/-
  NoGoals Meta — Typed Generators for SEO / Edge-Config Artifacts

  Sitemap, robots.txt, and Cloudflare Pages `_headers` are modeled as
  typed structures so that their properties (coverage, well-formedness,
  cross-file consistency) are checked by the Lean kernel, not by string
  inspection. Each renderer is a total function from the typed value to
  a String that the build driver writes to disk.

  URLs come from `Route.href` — the one path function — so the sitemap,
  the `<head>` alternates and the switcher are three views of one object.
-/

import NoGoals.IR.Route
import NoGoals.Render.Escape

namespace NoGoals.Meta

/-- OpenGraph locale tag of a language. -/
def _root_.NoGoals.Lang.ogLocale : Lang → String
  | .ja => "ja_JP"
  | .en => "en_US"

/-! ## hreflang alternates — shared by the sitemap and every page's `<head>` -/

/-- An hreflang tag: a language, or `x-default`. -/
inductive HreflangTag
  | lang (l : Lang)
  | xDefault
deriving DecidableEq, Repr

def HreflangTag.code : HreflangTag → String
  | .lang l => l.code
  | .xDefault => "x-default"

structure HreflangLink where
  tag : HreflangTag
  url : String
deriving Repr, DecidableEq

/-- The language switcher's target languages from a page in `lang`. -/
def switcherTargets (lang : Lang) : List Lang :=
  Lang.all.filter (· != lang)

/-- **Switcher symmetry**: the switcher on a page offers language `l'`
    exactly when the switcher on the `l'` twin offers the way back — you can
    never switch into a page you cannot switch out of. -/
theorem switcher_symmetric (l l' : Lang) :
    l' ∈ switcherTargets l ↔ l ∈ switcherTargets l' := by
  simp only [switcherTargets, List.mem_filter, Lang.mem_all, true_and, bne_iff_ne]
  exact ne_comm

/-- The alternate set of a slug: every language variant plus `x-default`
    pointing at the default-language variant. Exactly one definition —
    the sitemap and the chrome both call it, so they cannot disagree. -/
def alternatesFor (baseUrl : String) (d : Lang) (slug : Slug) : List HreflangLink :=
  Lang.all.map (fun l => ⟨.lang l, baseUrl ++ (Route.mk slug l).href d⟩) ++
  [⟨.xDefault, baseUrl ++ (Route.mk slug d).href d⟩]

/-- Every alternate set names both languages and `x-default`, in order. -/
theorem alternates_complete (baseUrl : String) (d : Lang) (slug : Slug) :
    (alternatesFor baseUrl d slug).map (·.tag) = [.lang .ja, .lang .en, .xDefault] := rfl

/-! ## Sitemap -/

structure SitemapEntry where
  route : Route
  loc : String
  alternates : List HreflangLink
deriving Repr

structure Sitemap where
  baseUrl : String
  entries : List SitemapEntry
deriving Repr

def entryFor (baseUrl : String) (d : Lang) (r : Route) : SitemapEntry :=
  ⟨r, baseUrl ++ r.href d, alternatesFor baseUrl d r.slug⟩

/-- One entry per route — the same route list the pages are generated from. -/
def sitemapOf (baseUrl : String) (d : Lang) (routes : List Route) : Sitemap :=
  ⟨baseUrl, routes.map (entryFor baseUrl d)⟩

/-! ### Sitemap theorems -/

/-- The sitemap has exactly one entry per route — no page is silently dropped. -/
theorem sitemap_entry_count (baseUrl : String) (d : Lang) (routes : List Route) :
    (sitemapOf baseUrl d routes).entries.length = routes.length := by
  simp [sitemapOf]

/-- **Coverage**: every route's URL is the `loc` of an entry that is a
    member of the generated sitemap. -/
theorem sitemap_covers (baseUrl : String) (d : Lang) (routes : List Route) :
    ∀ r ∈ routes, ∃ e ∈ (sitemapOf baseUrl d routes).entries, e.loc = baseUrl ++ r.href d := by
  intro r hr
  exact ⟨entryFor baseUrl d r, List.mem_map_of_mem hr, rfl⟩

/-- **hreflang symmetry**: every entry's alternate set is `alternatesFor`
    its slug, so the JA and EN entries of one slug carry the IDENTICAL set —
    the mutual-linking requirement (Google: "if page A links to page B, page
    B must link back") holds by construction, not by audit. -/
theorem hreflang_symmetric (baseUrl : String) (d : Lang) (routes : List Route) :
    ∀ e ∈ (sitemapOf baseUrl d routes).entries, e.alternates = alternatesFor baseUrl d e.route.slug := by
  intro e he
  simp only [sitemapOf, List.mem_map] at he
  obtain ⟨r, _, rfl⟩ := he
  rfl

/-! ### Sitemap XML renderer -/

/-- XML escaping for text/attribute content — the charwise `htmlEscape`,
    whose entities (`&amp; &lt; &gt; &quot; &#x27;`) are all valid XML
    character references. Sharing the definition means the escaping theorem
    is shared too, instead of a parallel `String.replace` chain with no
    proof. -/
def xmlEscape (s : String) : String := NoGoals.htmlEscape s

/-- For ANY input, no character of `xmlEscape s` is `< > " '` — element and
    attribute injection into the sitemap/feed XML is impossible. -/
theorem xmlEscape_no_specials (s : String) :
    ∀ x ∈ (xmlEscape s).toList, x ≠ '<' ∧ x ≠ '>' ∧ x ≠ '"' ∧ x ≠ '\'' :=
  NoGoals.htmlEscape_no_specials s

def renderHreflang (h : HreflangLink) : String :=
  s!"    <xhtml:link rel=\"alternate\" hreflang=\"{xmlEscape h.tag.code}\" href=\"{xmlEscape h.url}\" />"

def renderEntry (e : SitemapEntry) : String :=
  let alts := String.intercalate "\n" (e.alternates.map renderHreflang)
  s!"  <url>\n    <loc>{xmlEscape e.loc}</loc>\n{alts}\n  </url>"

def Sitemap.toXml (s : Sitemap) : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
  "<urlset xmlns=\"http://www.sitemaps.org/schemas/sitemap/0.9\"\n" ++
  "        xmlns:xhtml=\"http://www.w3.org/1999/xhtml\">\n" ++
  String.intercalate "\n" (s.entries.map renderEntry) ++
  "\n</urlset>\n"

/-! ## robots.txt -/

structure RobotsTxt where
  userAgent : String
  allow : List String
  disallow : List String
  sitemapUrl : Option String
deriving Repr

/-- Prod robots.txt: crawl everything, point at the sitemap. Derived from the
    same `baseUrl` that the sitemap uses, so the two can never drift. -/
def prodRobots (baseUrl : String) : RobotsTxt :=
  { userAgent := "*"
    allow := ["/"]
    disallow := []
    sitemapUrl := some (baseUrl ++ "/sitemap.xml") }

/-- Stage robots.txt: crawlers refused; no sitemap hint. -/
def stageRobots : RobotsTxt :=
  { userAgent := "*"
    allow := []
    disallow := ["/"]
    sitemapUrl := none }

def RobotsTxt.render (r : RobotsTxt) : String :=
  let ua := s!"User-agent: {r.userAgent}\n"
  let allows := r.allow.map (fun p => s!"Allow: {p}") |> String.intercalate "\n"
  let dis := r.disallow.map (fun p => s!"Disallow: {p}") |> String.intercalate "\n"
  let body := [ua, allows, dis].filter (· ≠ "") |> String.intercalate "\n"
  let sm := match r.sitemapUrl with
    | none => ""
    | some u => s!"\n\nSitemap: {u}"
  body ++ sm ++ "\n"

/-! ### Robots / sitemap consistency theorem -/

/-- The prod robots.txt's sitemap URL is consistent with the sitemap's base URL. -/
theorem prod_robots_sitemap_consistent (baseUrl : String) :
    (prodRobots baseUrl).sitemapUrl = some (baseUrl ++ "/sitemap.xml") := by
  rfl

/-! ## Cloudflare Pages _headers -/

structure HeaderDirective where
  name : String
  value : String
deriving Repr, DecidableEq

structure HeadersPolicy where
  scope : String
  directives : List HeaderDirective
deriving Repr

/-- The sources a site's pages load from beyond `'self'`, for the four
    directives the CSP gate can see in static HTML (`<script src>`,
    `<iframe src>`, `<img src/srcset>`, `<link rel=stylesheet>`). Empty (the
    default) is the strictest policy NoGoals ships: no inline styles or scripts
    anywhere, everything same-origin. Every entry is a decision the site
    makes in its spec, and the gate checks the emitted pages against exactly
    the policy these render to. -/
structure CspAllow where
  script : List String := []
  frame : List String := []
  img : List String := []
  style : List String := []
deriving Repr

/-- The production Content-Security-Policy. No `'unsafe-inline'` anywhere:
    zero inline styles or scripts ship (every declaration lives in the
    stylesheets; the audit's CSP gate fails on any element that would need an
    inline allowance). `frame-src` is emitted only when the site allows a
    frame origin; otherwise it falls back to `default-src 'self'`. -/
def cspOf (a : CspAllow) : String :=
  let src (name : String) (extra : List String) : String :=
    String.intercalate " " (name :: "'self'" :: extra)
  String.intercalate "; " (
    [ "default-src 'self'", src "style-src" a.style, src "img-src" a.img
    , src "script-src" a.script, "connect-src 'self'", "font-src 'self'" ] ++
    (if a.frame.isEmpty then [] else [String.intercalate " " ("frame-src" :: a.frame)]) ++
    [ "base-uri 'self'", "frame-ancestors 'none'", "form-action 'self'" ])

/-- Prod security headers, built from the typed policy above. -/
def prodHeaders (a : CspAllow) : HeadersPolicy :=
  { scope := "/*"
    directives := [
      ⟨"Content-Security-Policy", cspOf a⟩,
      ⟨"Strict-Transport-Security", "max-age=63072000; includeSubDomains; preload"⟩,
      ⟨"X-Content-Type-Options", "nosniff"⟩,
      ⟨"X-Frame-Options", "DENY"⟩,
      ⟨"Referrer-Policy", "strict-origin-when-cross-origin"⟩,
      ⟨"Permissions-Policy",
       "accelerometer=(), camera=(), geolocation=(), gyroscope=(), " ++
       "magnetometer=(), microphone=(), payment=(), usb=()"⟩
    ] }

/-- Stage headers: prod + an X-Robots-Tag prepended so crawlers never index staging. -/
def stageHeaders (a : CspAllow) : HeadersPolicy :=
  { prodHeaders a with
    directives := ⟨"X-Robots-Tag", "noindex, nofollow"⟩ :: (prodHeaders a).directives }

/-! ### Headers superset theorem -/

/-- Every prod directive is also present in stage — stage cannot weaken prod security. -/
theorem stage_headers_superset_prod (a : CspAllow) :
    ∀ d ∈ (prodHeaders a).directives, d ∈ (stageHeaders a).directives := by
  intro d hd
  simp [stageHeaders]
  exact Or.inr hd

/-- Stage has exactly one more directive than prod (the noindex tag). -/
theorem stage_headers_adds_one (a : CspAllow) :
    (stageHeaders a).directives.length = (prodHeaders a).directives.length + 1 := by
  simp [stageHeaders]

def HeadersPolicy.render (p : HeadersPolicy) : String :=
  let lines := p.directives.map (fun d => s!"  {d.name}: {d.value}")
  p.scope ++ "\n" ++ String.intercalate "\n" lines ++ "\n"

/-! ## Build Manifest (typed skeleton — hashes are populated in IO) -/

structure ManifestEntry where
  path : String
  sha256 : String
  size : Nat
deriving Repr

structure Manifest where
  generator : String
  generatedAt : String
  canonicalBaseUrl : String
  files : List ManifestEntry
deriving Repr

/-- JSON string escaping: backslash and quote, plus control characters as
    \uXXXX. Real escaping, not a docstring promise about the inputs. -/
def jsonEscape (s : String) : String :=
  s.toList.map (fun c =>
    if c == '\\' then "\\\\"
    else if c == '"' then "\\\""
    else if c == '\n' then "\\n"
    else if c == '\r' then "\\r"
    else if c == '\t' then "\\t"
    else if c.toNat < 0x20 then
      let hex := Nat.toDigits 16 c.toNat
      let pad := String.ofList (List.replicate (4 - hex.length) '0') ++ String.ofList hex
      "\\u" ++ pad
    else String.singleton c) |> String.join

/-- Simple JSON serialization for the manifest (no JSON dep for one file);
    every string field goes through `jsonEscape`. -/
def Manifest.toJson (m : Manifest) : String :=
  let str (s : String) : String := "\"" ++ jsonEscape s ++ "\""
  let renderEntry (e : ManifestEntry) : String :=
    "    {\"path\":" ++ str e.path ++
    ",\"sha256\":" ++ str e.sha256 ++
    ",\"size\":" ++ toString e.size ++ "}"
  let fileJson := m.files.map renderEntry |> String.intercalate ",\n"
  "{\n" ++
  "  \"generator\": " ++ str m.generator ++ ",\n" ++
  "  \"generatedAt\": " ++ str m.generatedAt ++ ",\n" ++
  "  \"canonicalBaseUrl\": " ++ str m.canonicalBaseUrl ++ ",\n" ++
  "  \"files\": [\n" ++ fileJson ++ "\n  ]\n" ++
  "}\n"

end NoGoals.Meta
