import NoGoals.Resolve.Refine
import NoGoals.Render.Plan
import NoGoals.Meta
import NoGoals.Verify.Permalinks
import NoGoals.Verify.SiteAudit
import NoGoals.Verify.HtmlFacts
import NoGoals.Verify.HtmlValidate

/-!
# Refinement + gate tests

Positive and negative controls for `refine`: a valid bilingual site
refines; a site with a broken link FAILS (fatally, with a located error and
a did-you-mean) instead of silently dropping the paragraph; every error on
every page is reported in one pass; links resolve in the source page's
language; heading anchors are emitted as ids and typed into links.

Then the runtime gates: link closure over parser facts, the bounded CSP
checker, the strict facts and html-validate decoders, and permalink
obligations including the three-release redirect regression.
-/

namespace NoGoals.Test.Refine

open NoGoals

/-! ## Fixtures -/

def emptyAssets : Assets 0 where
  name := fun i => i.elim0
  kind := fun i => i.elim0
  bytes := fun i => i.elim0
  unique := fun {i} => i.elim0

def indexJa : PageRaw :=
  { route := ⟨Slug.lit "index", .ja⟩, title := "Home"
    body := [.p [.text "hello", .a (.internal "/about#about") ⟨"about", by decide⟩],
             .heading ⟨.h1, .md, ⟨"Home Page", by decide⟩⟩] }

def aboutJa : PageRaw :=
  { route := ⟨Slug.lit "about", .ja⟩, title := "About"
    body := [.heading ⟨.h1, .md, ⟨"About", by decide⟩⟩] }

def indexEn : PageRaw :=
  { route := ⟨Slug.lit "index", .en⟩, title := "Home"
    body := [.p [.a (.internal "/about") ⟨"about", by decide⟩]] }

def aboutEn : PageRaw :=
  { route := ⟨Slug.lit "about", .en⟩, title := "About"
    body := [.heading ⟨.h1, .md, ⟨"About", by decide⟩⟩] }

def okSite : SiteRaw := { defaultLang := .ja, pages := [indexJa, aboutJa, indexEn, aboutEn] }

def withIndexBody (body : List BlockR) : SiteRaw :=
  { okSite with pages := [{ indexJa with body }, aboutJa, indexEn, aboutEn] }

def isOk {ε α : Type} : Except ε α → Bool
  | .ok _ => true | .error _ => false

def errorsOf {α : Type} : Except (List VError) α → List VError
  | .ok _ => [] | .error es => es

/-! ## Positive control: a valid site refines -/

#guard isOk (refine (nP := 4) (nA := 0) emptyAssets okSite)

/-! ## Negative controls: errors are fatal, located, complete -/

-- Broken link: fails (never silently drops the block) …
#guard !isOk (refine (nP := 4) (nA := 0) emptyAssets
  (withIndexBody [.p [.a (.internal "/abuot") ⟨"about", by decide⟩]]))

-- … the error is located (page index/ja, block 0, inline 0) with a did-you-mean.
#guard
  match refine (nP := 4) (nA := 0) emptyAssets
      (withIndexBody [.p [.a (.internal "/abuot") ⟨"about", by decide⟩]]) with
  | .error [.located ⟨_, .ja⟩ [0, 0] (.badLink "/abuot" ["about"])] => true
  | _ => false

-- TWO broken inlines → TWO errors, each with its own inline index.
#guard (errorsOf (refine (nP := 4) (nA := 0) emptyAssets
  (withIndexBody [.p [.a (.internal "/abuot") ⟨"a", by decide⟩, .text " ",
                      .a (.internal "/nope") ⟨"b", by decide⟩]]))).length = 2
#guard
  match refine (nP := 4) (nA := 0) emptyAssets
      (withIndexBody [.p [.a (.internal "/abuot") ⟨"a", by decide⟩, .text " ",
                          .a (.internal "/nope") ⟨"b", by decide⟩]]) with
  | .error [.located _ [0, 0] _, .located _ [0, 2] _] => true
  | _ => false

-- Nested location: a broken link inside a section's second child.
#guard
  match refine (nP := 4) (nA := 0) emptyAssets
      (withIndexBody [.section none [.p [.text "ok"], .p [.a (.internal "/nope") ⟨"b", by decide⟩]]]) with
  | .error [.located _ [0, 1, 0] (.badLink "/nope" _)] => true
  | _ => false

-- Missing anchor: the anchor must be in the target page's schema.
#guard
  match refine (nP := 4) (nA := 0) emptyAssets
      (withIndexBody [.p [.a (.internal "/about#team") ⟨"about", by decide⟩]]) with
  | .error [.located _ [0, 0] (.badAnchor "/about#team" "team" [a])] => a.s == "about"
  | _ => false

-- An anchor that is not a valid id is a syntax error, not a lookup miss.
#guard
  match refine (nP := 4) (nA := 0) emptyAssets
      (withIndexBody [.p [.a (.internal "/about#Team") ⟨"about", by decide⟩]]) with
  | .error [.located _ [0, 0] (.badAnchorSyntax "/about#Team" "Team")] => true
  | _ => false

-- Duplicate heading anchors on one page are rejected.
#guard
  match refine (nP := 4) (nA := 0) emptyAssets
      (withIndexBody [.heading ⟨.h1, .md, ⟨"Same", by decide⟩⟩, .heading ⟨.h2, .md, ⟨"same", by decide⟩⟩]) with
  | .error [.duplicateAnchor ⟨_, .ja⟩ a] => a.s == "same"
  | _ => false

-- Wrong page count is an error, not a truncation.
#guard !isOk (refine (nP := 3) (nA := 0) emptyAssets okSite)

-- A slug named after a language collides with that language's home page.
#guard
  match refine (nP := 4) (nA := 0) emptyAssets
      { okSite with pages := [{ indexJa with body := [] }, { aboutJa with route := ⟨Slug.lit "en", .ja⟩ },
                              { indexEn with body := [] }, { aboutEn with route := ⟨Slug.lit "en", .en⟩ }] } with
  | .error [.pathCollision _ _ "en/index.html"] => true
  | _ => false

-- A one-language raw site is incomplete, and the message names the missing variant.
#guard
  match refine (nP := 2) (nA := 0) emptyAssets { defaultLang := .ja, pages := [indexJa, aboutJa] } with
  | .error (.i18nMissing _ .en :: _) => true
  | _ => false

/-! ## Language-aware resolution and emitted ids -/

def okV : Option (SiteV 4 0 emptyAssets) := (refine emptyAssets okSite).toOption

-- The EN index's link lands on the EN about page.
#guard
  match okV with
  | some S =>
    match S.indexOf (Slug.lit "index") .en with
    | some i =>
      match (S.pages i).body with
      | [.p [.link p _ _]] => S.langOf p == .en && S.slugOf p == Slug.lit "about"
      | _ => false
    | none => false
  | none => false

-- The JA index's anchored link renders as `/about/#about`, and the JA about
-- page's tree declares `id="about"`.
#guard
  match okV with
  | some S =>
    match S.indexOf (Slug.lit "index") .ja, S.indexOf (Slug.lit "about") .ja with
    | some i, some j =>
      (match (S.pages i).body with
        | [.p [_, l], _] => renderInline S l == "<a href=\"/about/#about\">about</a>"
        | _ => false) &&
      (Render.Tree.idsList ((S.pages j).body.map (blockToHtml S))).contains "about"
    | _, _ => false
  | none => false

-- Heading ids come from `anchorOf`.
#guard (anchorOf "About Us").map (·.s) = some "about-us"
#guard (anchorOf "  Hello,   World!  ").map (·.s) = some "hello-world"
#guard (anchorOf "会社概要").isNone
#guard (anchorOf "Q3 2026").map (·.s) = some "q3-2026"

-- Kernel pages: the whole document is a well-formed tree.
#guard
  match okV with
  | some S => (List.finRange 4).all fun i => Render.Tree.wellFormed (pageTree S i)
  | none => false

/-! ## Href normalization -/

#guard normalizeHref "/about#team" = (.slug "about", some "team")
#guard normalizeHref "about#team" = (.slug "about", some "team")
#guard normalizeHref "/about/" = (.slug "about", none)
#guard normalizeHref "about" = (.slug "about", none)
#guard normalizeHref "/" = (.index, none)
#guard normalizeHref "" = (.samePage, none)
#guard normalizeHref "#team" = (.samePage, some "team")

/-! ## Did-you-mean -/

#guard editDistance "abuot" "about" = 2
#guard suggestSlugs ["about", "news", "contact"] "abuot" = ["about"]
#guard suggestSlugs ["about", "news", "contact"] "zzzzzz" = []

/-! ## Escaping (Meta renderers) -/

#guard Meta.xmlEscape "a&b<c>\"d'" = "a&amp;b&lt;c&gt;&quot;d&#x27;"
#guard Meta.jsonEscape "a\"b\\c\nd" = "a\\\"b\\\\c\\nd"

/-! ## Checked date literals -/

#guard (NoGoals.Verify.IsoDate.lit "2026-08-04").toString = "2026-08-04"
#guard (NoGoals.Verify.IsoDate.lit "2024-02-29").toString = "2024-02-29"  -- leap year

/-! ## Permalink obligations -/

section Permalinks
open NoGoals.Verify.Permalinks

  def obligations : List String := ["index.html", "about/index.html", "old/index.html"]
  def cur : List String := ["index.html", "about/index.html", "new/index.html", "_headers", "_redirects"]

  -- Losing a URL without a redirect fails, naming the URL.
  #guard !check obligations cur []
  #guard violations obligations cur [] = [.lost "old/index.html"]

  -- A redirect to a live public target passes.
  #guard check obligations cur [⟨"old/index.html", "new/index.html"⟩]

  -- Dangling, chained, self, duplicate, shadowing and config-file targets all fail.
  #guard !check obligations cur [⟨"old/index.html", "gone/index.html"⟩]
  #guard !check obligations cur [⟨"old/index.html", "index.html"⟩, ⟨"index.html", "about/index.html"⟩]
  #guard !check obligations cur [⟨"old/index.html", "old/index.html"⟩]
  #guard (violations obligations cur [⟨"old/index.html", "new/index.html"⟩, ⟨"old/index.html", "index.html"⟩]).contains
    (.duplicateSource "old/index.html")
  #guard (violations obligations cur [⟨"old/index.html", "new/index.html"⟩, ⟨"about/index.html", "index.html"⟩]).contains
    (.shadowsLiveFile ⟨"about/index.html", "index.html"⟩)
  #guard (violations obligations cur [⟨"old/index.html", "_headers"⟩]).contains
    (.danglingRedirect ⟨"old/index.html", "_headers"⟩)

  -- Three releases: A ships /old/; B replaces it with /new/ + redirect and
  -- the baseline written after B carries the redirect SOURCE; C drops the
  -- redirect → red. The obligation survives the file's disappearance.
  def baselineAfterB : String :=
    renderBaseline [("0000000000000000000000000000000000000000000000000000000000000000", "new/index.html")]
      ["old/index.html"]
  #guard
    match parseBaseline baselineAfterB with
    | .ok es => !check (obligationsOf es) ["new/index.html"] []
    | .error _ => false
  #guard
    match parseBaseline baselineAfterB with
    | .ok es => check (obligationsOf es) ["new/index.html"] [⟨"old/index.html", "new/index.html"⟩]
    | .error _ => false

  -- `_redirects` is rendered from the same map, as URLs — every public URL
  -- of a standalone .html file (the host also served it extensionless).
  #guard renderRedirects [⟨"old/index.html", "new/index.html"⟩, ⟨"a.html", "index.html"⟩] =
    "/old/ /new/ 301\n/a.html / 301\n/a / 301\n"

  -- Baseline parsing is strict.
  def goodSha := "06641eec2636a109fdf3f60a18bf1e7dbecebfd0eac62bd1bf56ed4a1557c4fa"
  def errs : Except (List BaselineParseError) (List BaselineEntry) → List BaselineParseError
    | .ok _ => [] | .error es => es
  #guard isOk (parseBaseline s!"{goodSha}  about/index.html\nredirect  old/index.html\n")
  #guard errs (parseBaseline "") = [.empty]
  #guard errs (parseBaseline "garbage") = [.malformedLine 1 "garbage"]
  #guard errs (parseBaseline "abc  about/index.html") = [.badHash 1 "abc"]
  #guard errs (parseBaseline s!"{goodSha}  ../escape") = [.badPath 1 "../escape"]
  #guard errs (parseBaseline s!"{goodSha}  /abs/index.html") = [.badPath 1 "/abs/index.html"]
  #guard errs (parseBaseline s!"{goodSha}  a/index.html\n{goodSha}  a/index.html\n") = [.duplicatePath "a/index.html"]
  -- Configuration files are hashed but are not obligations.
  #guard
    match parseBaseline s!"{goodSha}  _headers\n{goodSha}  index.html\n" with
    | .ok es => obligationsOf es == ["index.html"]
    | .error _ => false
end Permalinks

/-! ## Gates over parser facts -/

section Gates
open NoGoals.Verify.HtmlFacts NoGoals.Verify.SiteAudit

  def el (tag : String) (attrs : List (String × String)) (hasText := false) : Element :=
    { tag, attrs, hasText }

  def page (path : String) (elements : List Element) (ids : List String := []) (text := "") : FileFacts :=
    { path, elements, ids, text, attrText := [] }

  def inv : List String := ["index.html", "about/index.html", "en/index.html", "feed.xml",
    "assets/styles/site.css", "wagahai/index.html", "wagahai/privacy.html"]
  def site := "https://x.test"

  -- Closure: internal links must land on emitted files; fragments on ids.
  #guard (linkViolations site inv [] [page "index.html" [el "a" [("href", "/about/")]]]).isEmpty
  #guard !(linkViolations site inv [] [page "index.html" [el "a" [("href", "/missing/")]]]).isEmpty
  #guard !(linkViolations site inv [] [page "index.html" [el "a" [("href", "/missing/#x")]]]).isEmpty
  #guard (linkViolations site inv []
    [page "index.html" [el "a" [("href", "/about/#team")]], page "about/index.html" [] ["team"]]).isEmpty
  #guard !(linkViolations site inv []
    [page "index.html" [el "a" [("href", "/about/#team")]], page "about/index.html" [] ["other"]]).isEmpty
  -- same-page fragment
  #guard (linkViolations site inv [] [page "about/index.html" [el "a" [("href", "#team")]] ["team"]]).isEmpty
  #guard !(linkViolations site inv [] [page "about/index.html" [el "a" [("href", "#team")]] []]).isEmpty
  -- relative links from a nested static page
  #guard (linkViolations site inv [] [page "wagahai/index.html" [el "a" [("href", "privacy.html")]]]).isEmpty
  #guard !(linkViolations site inv [] [page "wagahai/index.html" [el "a" [("href", "terms.html")]]]).isEmpty
  -- external and mailto are not internal references
  #guard (linkViolations site inv [] [page "index.html" [el "a" [("href", "https://other.test/")], el "a" [("href", "mailto:a@b")]]]).isEmpty
  -- malformed is a violation, never silently external
  #guard !(linkViolations site inv [] [page "index.html" [el "a" [("href", "/../x/")]]]).isEmpty
  -- form actions: declared dynamic endpoint or emitted file
  #guard (linkViolations site inv ["/api/careers"] [page "index.html" [el "form" [("action", "/api/careers")]]]).isEmpty
  #guard !(linkViolations site inv [] [page "index.html" [el "form" [("action", "/api/careers")]]]).isEmpty
  -- srcset tokenization: commas inside URLs are not separators
  #guard srcsetUrls "/a.jpg 1x, /b.jpg 2x" = ["/a.jpg", "/b.jpg"]
  #guard srcsetUrls "data:image/png;base64,AAAA 1x, /b.jpg 2x" = ["data:image/png;base64,AAAA", "/b.jpg"]
  #guard srcsetUrls "/a.jpg,/b.jpg" = ["/a.jpg,/b.jpg"]   -- no whitespace: one URL, per the spec
  #guard srcsetUrls "  /a.jpg   100w ,  /b.jpg" = ["/a.jpg", "/b.jpg"]
  -- srcset candidates are references too
  #guard !(linkViolations site inv [] [page "index.html" [el "img" [("src", "/assets/styles/site.css"), ("srcset", "/assets/x.jpg 1x, /assets/y.jpg 2x")]]]).isEmpty

  -- Reachability with declared roots.
  def facts3 : Facts :=
    [page "index.html" [el "a" [("href", "/about/")]],
     page "about/index.html" [],
     page "wagahai/index.html" [el "a" [("href", "privacy.html")]],
     page "wagahai/privacy.html" [],
     page "en/index.html" []]
  #guard unreachableFrom site facts3 ["index.html", "wagahai/index.html"] [] = ["en/index.html"]
  #guard unreachableFrom site facts3 ["index.html", "wagahai/index.html"] ["en/index.html"] = []
  #guard unreachableFrom site facts3 ["index.html"] [] = ["wagahai/index.html", "wagahai/privacy.html", "en/index.html"]

  -- CSP: the bounded checker over a policy shaped like the consumer's.
  def policy : String :=
    Meta.cspOf { script := ["https://challenges.cloudflare.com"], frame := ["https://challenges.cloudflare.com"] }
  #guard (checkPageCsp policy site (page "index.html" [el "script" [("src", "/assets/js/a.js")]])).isEmpty
  #guard (checkPageCsp policy site (page "index.html" [el "script" [("src", "https://challenges.cloudflare.com/turnstile/v0/api.js")]])).isEmpty
  #guard !(checkPageCsp policy site (page "index.html" [el "script" [("src", "https://evil.test/x.js")]])).isEmpty
  #guard !(checkPageCsp policy site (page "index.html" [el "script" [] true])).isEmpty
  #guard (checkPageCsp policy site (page "index.html" [el "script" [] false])).isEmpty
  #guard !(checkPageCsp policy site (page "index.html" [el "div" [("style", "color:red")]])).isEmpty
  #guard !(checkPageCsp policy site (page "index.html" [el "style" [] true])).isEmpty
  #guard !(checkPageCsp policy site (page "index.html" [el "button" [("onclick", "go()")]])).isEmpty
  #guard !(checkPageCsp policy site (page "index.html" [el "a" [("href", "javascript:void(0)")]])).isEmpty
  #guard (checkPageCsp policy site (page "index.html" [el "link" [("rel", "stylesheet"), ("href", "/assets/styles/site.css")]])).isEmpty
  #guard !(checkPageCsp policy site (page "index.html" [el "link" [("rel", "stylesheet"), ("href", "https://cdn.test/x.css")]])).isEmpty
  -- `data:` is a source a site allows deliberately, never by default.
  #guard !(checkPageCsp policy site (page "index.html" [el "img" [("src", "data:image/png;base64,AA==")]])).isEmpty
  #guard (checkPageCsp (Meta.cspOf { img := ["data:"] }) site (page "index.html" [el "img" [("src", "data:image/png;base64,AA==")]])).isEmpty
  #guard (checkPageCsp policy site (page "index.html" [el "img" [("srcset", "/a.jpg 1x, /b.jpg 2x")]])).isEmpty
  #guard !(checkPageCsp policy site (page "index.html" [el "img" [("srcset", "/a.jpg 1x, https://cdn.test/b.jpg 2x")]])).isEmpty
  #guard (checkPageCsp policy site (page "index.html" [el "iframe" [("src", "https://challenges.cloudflare.com/x")]])).isEmpty
  #guard !(checkPageCsp policy site (page "index.html" [el "iframe" [("src", "https://evil.test/x")]])).isEmpty
  #guard (checkPageCsp policy site (page "index.html" [el "form" [("action", "/api/careers")]])).isEmpty
  #guard !(checkPageCsp policy site (page "index.html" [el "form" [("action", "https://forms.test/x")]])).isEmpty
  -- form-action does NOT fall back to default-src: without the directive it is unrestricted
  #guard (checkPageCsp "default-src 'self'" site (page "index.html" [el "form" [("action", "https://forms.test/x")]])).isEmpty
  -- unmodelled elements and policy features fail closed
  #guard !(checkPageCsp policy site (page "index.html" [el "base" [("href", "/")]])).isEmpty
  #guard !(checkPageCsp policy site (page "index.html" [el "video" [("src", "/v.mp4")]])).isEmpty
  #guard !(checkPageCsp "script-src 'nonce-abc'" site (page "index.html" [])).isEmpty
  -- same-origin absolute URLs are 'self'
  #guard (checkPageCsp policy site (page "index.html" [el "script" [("src", "https://x.test/a.js")]])).isEmpty
  -- stale allowances are reported, not failed
  #guard staleCspAllowances policy [page "index.html" [el "script" [("src", "/a.js")]]] = ["https://challenges.cloudflare.com"]
  #guard staleCspAllowances policy
    [page "index.html" [el "script" [("src", "https://challenges.cloudflare.com/x.js")]]] = []

  -- SEO coherence.
  def aboutRoute : Route := ⟨Slug.lit "about", .en⟩
  def goodHead : FileFacts := page "en/about/index.html" [
    el "html" [("lang", "en")],
    el "title" [],
    el "meta" [("name", "description"), ("content", "About us")],
    el "meta" [("property", "og:title"), ("content", "About")],
    el "meta" [("property", "og:description"), ("content", "About us")],
    el "meta" [("property", "og:type"), ("content", "website")],
    el "meta" [("property", "og:locale:alternate"), ("content", "ja_JP")],
    el "link" [("rel", "canonical"), ("href", "https://x.test/en/about/")],
    el "link" [("rel", "alternate"), ("hreflang", "ja"), ("href", "https://x.test/about/")],
    el "link" [("rel", "alternate"), ("hreflang", "en"), ("href", "https://x.test/en/about/")],
    el "link" [("rel", "alternate"), ("hreflang", "x-default"), ("href", "https://x.test/about/")],
    el "meta" [("property", "og:url"), ("content", "https://x.test/en/about/")],
    el "meta" [("property", "og:locale"), ("content", "en_US")]]
  #guard (seoViolations site .ja [(aboutRoute, "en/about/index.html")] [goodHead]).isEmpty
  #guard !(seoViolations site .ja [(aboutRoute, "en/about/index.html")]
    [{ goodHead with elements := goodHead.elements.filter fun e => e.attr "rel" != some "canonical" }]).isEmpty
  #guard !(seoViolations site .ja [(aboutRoute, "en/about/index.html")] []).isEmpty
  -- Metadata completeness: a missing description or a wrong document language fails.
  #guard (metadataViolations [(aboutRoute, "en/about/index.html")] [goodHead]).isEmpty
  #guard !(metadataViolations [(aboutRoute, "en/about/index.html")]
    [{ goodHead with elements := goodHead.elements.filter fun e => e.attr "name" != some "description" }]).isEmpty
  #guard !(metadataViolations [(aboutRoute, "en/about/index.html")]
    [{ goodHead with elements := el "html" [("lang", "ja")] :: goodHead.elements.drop 1 }]).isEmpty

  -- Text-level checks run over what the parser decoded.
  #guard cjkLeaks "Katayama 片山 Integrated" ["片山"] = []
  #guard cjkLeaks "Katayama 会社概要" ["片山"] = ["会社概要"]
  #guard doubleEscaped (page "x.html" [] [] "Tom &amp; Jerry") = ["&amp;"]
  #guard doubleEscaped (page "x.html" [] [] "Tom & Jerry") = []
  #guard classTokens (page "x.html" [el "div" [("class", "a b")], el "p" [("class", "b c")]]) = ["a", "b", "c"]
  #guard undefinedClasses ".a{} .b{}" [page "x.html" [el "div" [("class", "a b c")]]] = ["c"]
  #guard extractCssAssetRefs ".x{background:url('/assets/a.jpg')} .y{background:url(/assets/b.jpg)}" =
    ["assets/a.jpg", "assets/b.jpg"]

  -- Facts decoding is strict.
  def factsJson : String :=
    "{\"files\":[{\"path\":\"index.html\",\"elements\":[{\"tag\":\"a\",\"attrs\":{\"href\":\"/about/\"},\"hasText\":true}],\"ids\":[\"top\"],\"text\":\"hi\",\"attrText\":[]}]}"
  #guard isOk (parseFacts ["index.html"] factsJson)
  #guard !isOk (parseFacts ["index.html", "about/index.html"] factsJson)      -- missing file
  #guard !isOk (parseFacts [] factsJson)                                        -- unexpected file
  #guard !isOk (parseFacts ["index.html"] (factsJson.replace "\"hasText\":true" ""))  -- malformed
  #guard !isOk (parseFacts ["index.html"] (factsJson.replace "\"text\":\"hi\"," "\"text\":\"hi\",\"extra\":1,")) -- unknown key
  #guard !isOk (parseFacts ["index.html"] (factsJson.replace "\"ids\":[\"top\"]," ""))  -- missing key
  #guard !isOk (parseFacts ["index.html"] "not json")

  -- html-validate decoding is strict; clean files are omitted by the tool,
  -- so the canary's presence is what proves the inputs were processed.
  open NoGoals.Verify.HtmlValidate in
  def hvResult (file : String) (errorCount : Nat) (sev : Nat) : String :=
    s!"\{\"filePath\":\"{file}\",\"errorCount\":{errorCount},\"warningCount\":0,\"messages\":[\{\"line\":1,\"column\":2,\"ruleId\":\"x\",\"message\":\"m\",\"severity\":{sev}}]}"
  def canary := "/tmp/c/canary.html"
  def withCanary (xs : List String) : String := "[" ++ String.intercalate "," (xs ++ [hvResult canary 1 2]) ++ "]"
  open NoGoals.Verify.HtmlValidate in
  #guard isOk (parseOutput ["a.html"] canary (withCanary [hvResult "a.html" 1 2]))
  open NoGoals.Verify.HtmlValidate in
  #guard isOk (parseOutput ["a.html", "b.html"] canary (withCanary []))         -- clean files are omitted
  open NoGoals.Verify.HtmlValidate in
  #guard !isOk (parseOutput ["a.html"] canary ("[" ++ hvResult "a.html" 1 2 ++ "]"))   -- no canary: inputs skipped
  open NoGoals.Verify.HtmlValidate in
  #guard !isOk (parseOutput ["a.html"] canary ("[" ++ hvResult canary 0 1 ++ "]"))    -- canary reported clean
  open NoGoals.Verify.HtmlValidate in
  #guard !isOk (parseOutput ["a.html"] canary (withCanary [hvResult "a.html" 0 2]))   -- count mismatch
  open NoGoals.Verify.HtmlValidate in
  #guard !isOk (parseOutput ["a.html"] canary (withCanary [hvResult "a.html" 1 3]))   -- unknown severity
  open NoGoals.Verify.HtmlValidate in
  #guard !isOk (parseOutput [] canary (withCanary [hvResult "a.html" 1 2]))           -- unrequested result
  open NoGoals.Verify.HtmlValidate in
  #guard !isOk (parseOutput ["a.html"] canary (withCanary [hvResult "a.html" 1 2, hvResult "a.html" 1 2]))  -- duplicate
  open NoGoals.Verify.HtmlValidate in
  #guard !isOk (parseOutput ["a.html"] canary "{}")
end Gates

#check "Refine tests passed!"

end NoGoals.Test.Refine
