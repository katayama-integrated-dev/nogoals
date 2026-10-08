/-
  NoGoals Site Compilation

  Converts a `DSL.Site` to the emitted page set plus its verification
  report. One pipeline: `Site.routes` is the route set; `toSiteRaw` refines
  it through the verified IR (structure); `generateFiles` renders every
  route as ONE typed tree — kernel chrome around the page's own typed body
  slot — with no string surgery anywhere.
-/

import NoGoals.DSL
import NoGoals.IR.Atoms
import NoGoals.IR.Assets
import NoGoals.IR.HtmlRaw
import NoGoals.IR.HtmlVerified
import NoGoals.Resolve.Refine
import NoGoals.Render.Html
import NoGoals.Render.Plan
import NoGoals.Meta
import NoGoals.Compile.Evidence
import NoGoals.Compile.Report

namespace NoGoals.Compile

open NoGoals (urlToString)
open NoGoals.DSL
open NoGoals.Render.Tree (Html)

open NoGoals.Meta (switcherTargets)

/-! ## Type-Level Guarantees (always enforced) -/

/-- Facts about the verified IR renderer's vocabulary, true for any content
    routed through it, labelled `.kernel` where the consumer's page bodies do
    NOT yet route through it. The route/path facts are `.artifact`: every
    page and asset of THIS build has a typed route or asset path. -/
def typeLevelGuarantees : List Guarantee := [
  { category := "Type Safety"
    name := "Bilingual completeness for editorial content"
    description := "Every L leaf carries both JA and EN — enforced structurally by the L type; a page cannot ship with one language missing"
    status := .enforced "NoGoals.DSL.L (record with both ja and en fields)"
    location := some (toString ``NoGoals.DSL.L)
    scope := .artifact, id := "nogoals.bilingual-L" },
  { category := "Type Safety"
    name := "Dates are valid ISO calendar dates"
    description := "Every article and page date is an `IsoDate`; the `IsoDate.lit` literal is parsed during elaboration, so a malformed date is a compile error"
    status := .enforced "NoGoals.Verify.IsoDate.lit (elaboration-checked literal)"
    location := some (toString ``NoGoals.Verify.IsoDate.lit)
    scope := .artifact, id := "nogoals.iso-dates" },
  { category := "Type Safety"
    name := "Output paths cannot escape the root"
    description := "Every page path is derived from a Route whose slug is a list of validated [a-z0-9-] segments, and every asset path from validated [a-z0-9._-] segments that are never `.` or `..`; a name that could escape the output root or collide across case is unrepresentable — a compile error at the literal"
    status := .enforced "Segment / Slug / AssetPath types + Route.outputPath"
    location := some (toString ``NoGoals.Route.outputPath)
    scope := .artifact, id := "nogoals.safe-paths" },
  { category := "Type Safety"
    name := "Route closure: every internal href resolves to an emitted page (IR vocabulary)"
    description := "In the kernel IR, link targets are Fin nP (unrepresentable otherwise); rendered_link_resolves proves the emitted href, resolved as a browser and the host resolve it from any source page, is a file in the build plan. Body links of the shipped site are covered separately by the artifact-level link gate."
    status := .enforced "Fin nP + rendered_link_resolves"
    location := some (toString ``NoGoals.rendered_link_resolves)
    scope := .kernel, id := "nogoals.route-closure" },
  { category := "Type Safety"
    name := "Fragment closure: a link's #anchor is an id the target declares (IR vocabulary)"
    description := "A link's anchor is a member of the target page's anchor schema (AnchorIn); anchors_sound + body_ids_emitted prove the target's rendered tree carries that id"
    status := .enforced "AnchorIn subtype + rendered_fragment_declared"
    location := some (toString ``NoGoals.rendered_fragment_declared)
    scope := .kernel, id := "nogoals.fragment-closure" },
  { category := "Type Safety"
    name := "No missing assets (IR vocabulary)"
    description := "AssetId carries proof that asset exists with correct kind"
    status := .enforced "AssetId type witness"
    location := some (toString ``NoGoals.AssetId)
    scope := .kernel, id := "nogoals.asset-id" },
  { category := "Type Safety"
    name := "No asset type confusion (IR vocabulary)"
    description := "Cannot use JS file as image - kind is part of type"
    status := .enforced "AssetId n k A"
    location := some (toString ``NoGoals.AssetId)
    scope := .kernel, id := "nogoals.asset-kind" },
  { category := "Type Safety"
    name := "No empty alt text (IR vocabulary)"
    description := "Alt attributes require NonEmptyStr"
    status := .enforced "NonEmptyStr type"
    location := some (toString ``NoGoals.NonEmptyStr)
    scope := .kernel, id := "nogoals.alt-nonempty" },
  { category := "Type Safety"
    name := "No empty link labels (IR vocabulary)"
    description := "Link text requires NonEmptyStr"
    status := .enforced "NonEmptyStr type"
    location := some (toString ``NoGoals.NonEmptyStr)
    scope := .kernel, id := "nogoals.label-nonempty" },
  { category := "Type Safety"
    name := "Safe external URLs only (IR vocabulary)"
    description := "External URLs must be https/http/data URIs"
    status := .enforced "Url.Safe ADT"
    location := some (toString ``NoGoals.Url.Safe)
    scope := .kernel, id := "nogoals.url-safe" }
]

/-! ## Theorem-Proved Guarantees (verified by Lean kernel)

Every `location` is derived from a double-backtick name literal resolved by
the elaborator: renaming or deleting a cited theorem fails THIS module's
build. The report cannot cite a theorem that doesn't exist. -/

def theoremGuarantees : List Guarantee := [
  { category := "Theorems"
    name := "Slug/index round-trip (IR)"
    description := "indexOf (slug i) (lang i) = some i for all pages of a refined SiteV"
    status := .enforced "roundTrip₁ theorem"
    location := some (toString ``NoGoals.SiteV.roundTrip₁)
    scope := .kernel, id := "nogoals.roundtrip" },
  { category := "Theorems"
    name := "i18n completeness (IR)"
    description := "Every slug exists in every language, for a refined SiteV (the language set is closed: ja, en)"
    status := .enforced "i18nComplete theorem"
    location := some (toString ``NoGoals.SiteV.i18nComplete)
    scope := .kernel, id := "nogoals.i18n-complete" },
  { category := "Theorems"
    name := "No file collisions (IR plan)"
    description := "All output paths of a refined SiteV's build plan are unique - no overwrites"
    status := .enforced "unique_paths theorem"
    location := some (toString ``NoGoals.unique_paths)
    scope := .kernel, id := "nogoals.unique-paths" },
  { category := "Theorems"
    name := "Pages/assets path disjoint (IR)"
    description := "Page paths never collide with asset paths in a refined SiteV"
    status := .enforced "disjointAssets theorem"
    location := some (toString ``NoGoals.SiteV.disjointAssets)
    scope := .kernel, id := "nogoals.disjoint-assets" },
  { category := "Theorems"
    name := "Build covers all content (IR plan)"
    description := "Every page and asset of a refined SiteV appears in its build plan"
    status := .enforced "coverage theorem"
    location := some (toString ``NoGoals.coverage)
    scope := .kernel, id := "nogoals.coverage" },
  { category := "Theorems"
    name := "Asset path injectivity (IR)"
    description := "Different assets have different paths"
    status := .enforced "Assets.path_injective"
    location := some (toString ``NoGoals.Assets.path_injective)
    scope := .kernel, id := "nogoals.asset-injective" },
  { category := "Theorems"
    name := "Sitemap covers every route"
    description := "Every route of an indexed page (page × language) is the loc of an entry that is a member of the generated sitemap, and the sitemap has exactly one entry per such route — no page dropped, none invented"
    status := .enforced "sitemap_covers + sitemap_entry_count theorems"
    location := some (toString ``NoGoals.Meta.sitemap_covers)
    scope := .artifact, id := "nogoals.sitemap-coverage" },
  { category := "Theorems"
    name := "Stage headers ⊇ prod headers"
    description := "Staging security headers never weaken prod; stage only adds directives"
    status := .enforced "stage_headers_superset_prod theorem"
    location := some (toString ``NoGoals.Meta.stage_headers_superset_prod)
    scope := .artifact, id := "nogoals.stage-headers" },
  { category := "Theorems"
    name := "Robots/sitemap URL consistent"
    description := "Prod robots.txt Sitemap URL matches sitemap base URL — no drift"
    status := .enforced "prod_robots_sitemap_consistent theorem"
    location := some (toString ``NoGoals.Meta.prod_robots_sitemap_consistent)
    scope := .artifact, id := "nogoals.robots-sitemap" },
  { category := "Theorems"
    name := "Canonical, hreflang and sitemap from one route set"
    description := "The <head> canonical link, the <head> hreflang alternates, the sitemap alternates and the switcher are all Route.href of the same route set through one alternatesFor function: the JA and EN entries of a slug carry the identical alternate set (hreflang_symmetric) and every set names ja, en and x-default (alternates_complete)"
    status := .enforced "hreflang_symmetric + alternates_complete theorems"
    location := some (toString ``NoGoals.Meta.hreflang_symmetric)
    scope := .artifact, id := "nogoals.canonical-hreflang" , headline := true },
  { category := "Theorems"
    name := "Language switcher symmetric"
    description := "The switcher offers a language iff the twin page's switcher offers the way back — a page you can switch into can always switch out"
    status := .enforced "switcher_symmetric theorem"
    location := some (toString ``NoGoals.Meta.switcher_symmetric)
    scope := .chrome, id := "nogoals.switcher-symmetric" }
]

/-! ## Security Guarantees -/

def securityGuarantees : List Guarantee := [
  { category := "Security"
    name := "Escaping correct where applied (typed tree)"
    description := "Text and attribute content routed through the typed tree renderer is escaped; htmlEscape_no_specials proves the output contains no < > \" ' for ANY input. Raw slot content is NOT covered by this theorem — each raw node is a named trust obligation checked by the runtime validators."
    status := .enforced "htmlEscape_no_specials theorem"
    location := some (toString ``NoGoals.htmlEscape_no_specials)
    scope := .chrome, id := "nogoals.escaping" },
  { category := "Security"
    name := "CSP forbids inline styles and scripts (typed policy)"
    description := "The typed HeadersPolicy ships style-src 'self' and script-src without 'unsafe-inline'; the emitted _headers file is rendered from it. Whether the emitted PAGES honor the policy is the CSP audit gate's claim, reported separately from its actual run."
    status := .enforced "typed HeadersPolicy"
    location := some (toString ``NoGoals.Meta.prodHeaders)
    scope := .artifact, id := "nogoals.csp-policy" },
  { category := "Security"
    name := "XML injection impossible (sitemap/feeds)"
    description := "xmlEscape is the charwise htmlEscape; xmlEscape_no_specials proves sitemap and feed text/attribute content contains no < > \" ' for ANY input"
    status := .enforced "xmlEscape_no_specials theorem"
    location := some (toString ``NoGoals.Meta.xmlEscape_no_specials)
    scope := .artifact, id := "nogoals.xml-escape" , headline := true },
  { category := "Security"
    name := "Chrome structure well-formed (slots trusted)"
    description := "Every content page is one typed HTML tree: kernel chrome (head, nav, hero, footer) around the site's typed slots; chrome_tree_wellFormed proves the chrome adds no imbalance whenever the slot trees are well-formed, and render_wf_mod promotes that to the rendered bytes modulo the listed raw slots — the fragment grammar plus void/normal tag classes, not HTML element semantics (html-validate remains the authority for those). The report pages use their own constructors and are checked well-formed (no raw node) before they are written."
    status := .enforced "chrome_tree_wellFormed + render_wf_mod theorems"
    location := some (toString ``NoGoals.Render.Tree.render_wf_mod)
    scope := .chrome, id := "nogoals.chrome-wf" , headline := true },
  { category := "Security"
    name := "Well-formed markup (kernel renderer)"
    description := "The kernel renderer factors through a typed HTML tree; render_wf proves every raw-free tree renders to properly nested tags whose text and attribute values cannot open or close an element, with void elements never given children — balanced markup is a grammar theorem, not a validator's opinion"
    status := .enforced "render_wf grammar theorem"
    location := some (toString ``NoGoals.Render.Tree.render_wf)
    scope := .kernel, id := "nogoals.render-wf" }
]

/-! ## Runtime Checks — one entry per check, never one per item -/

def checkNavLinks (site : Site) : Guarantee :=
  let broken := site.validateNavLinks
  if broken.isEmpty then
    { category := "Runtime", name := "Navigation links resolve"
      description := s!"Every page link in the main and footer navigation names a page of this site"
      status := .checked, id := "site.nav-links" }
  else
    { category := "Runtime", name := "Navigation links resolve"
      description := "Every page link in the main and footer navigation names a page of this site"
      status := .failed (String.intercalate "; " broken), id := "site.nav-links" }

/-- "All N `what` are distinct" — one check shape for slugs, division ids
    and person ids. An empty list is `.notApplicable`. -/
def uniqueIds {α : Type} [BEq α] [ToString α] (id name what : String) (xs : List α) : Guarantee :=
  let ds := dupes xs
  { category := "Runtime", name
    description := s!"All {xs.length} {what} are distinct"
    status := if xs.isEmpty then .notApplicable
      else if ds.isEmpty then .checked
      else .failed s!"duplicate {what}: {String.intercalate ", " (ds.map toString)}"
    id }

def checkUniqueSlugs (site : Site) : Guarantee :=
  uniqueIds "site.unique-slugs" "Unique page slugs" "page slugs" (site.pages.map (·.slug))

def checkUniqueDivisions (site : Site) : Guarantee :=
  uniqueIds "site.unique-divisions" "Unique division IDs" "division IDs" (site.divisions.map (·.id))

def checkUniquePeople (site : Site) : Guarantee :=
  uniqueIds "site.unique-people" "Unique person IDs" "person IDs" (site.people.map (·.id))

def checkPeopleDivisions (site : Site) : Guarantee :=
  let divIds := site.divisions.map (·.id)
  let bad := site.people.filterMap fun p =>
    match p.division with
    | some d => if divIds.contains d then none else some s!"{p.id} → {d}"
    | none => none
  let refs := site.people.filterMap (·.division) |>.length
  { category := "Runtime", name := "People reference existing divisions"
    description := s!"Every division reference on a person record ({refs}) names a declared division"
    status := if site.people.isEmpty then .notApplicable
      else if bad.isEmpty then .checked
      else .failed s!"unknown divisions: {String.intercalate ", " bad}"
    id := "site.person-divisions" }

/-! ## Structural verification — the bridge to the verified IR

`compile` refines this site's route set through `NoGoals.refine`, so the `SiteV`
proof fields ((slug,lang) round-trip, i18n completeness, unique output
paths) are established for THIS build, not asserted. Bodies are the trusted
shell's concern (the typed body slot below); structure is the kernel's. -/

def noAssets : Assets 0 where
  name := fun i => i.elim0
  kind := fun i => i.elim0
  bytes := fun i => i.elim0
  unique := fun {i} => i.elim0

/-- The skeleton: every route, with the page's title and an empty kernel
    body. The ONLY derivation of the route set is `Site.routes`. -/
def toSiteRaw (site : Site) : SiteRaw :=
  { defaultLang := site.config.defaultLang
  , pages := site.routes.map fun (p, r) =>
      { route := r, title := p.title.get r.lang, body := [] } }

def structuralErrors (site : Site) : List VError :=
  let raw := toSiteRaw site
  match refine (nP := raw.pages.length) (nA := 0) noAssets raw with
  | .ok _ => []
  | .error es => es

/-! ## Typed chrome slots

Every injection point the shell needs is a named structural slot holding a
TYPED tree — there is no post-hoc `String.replace` on emitted HTML anywhere,
and no string slot: only a `raw` node inside a slot tree (the consumer's
`verbatimHtml`) is outside the grammar, and `compile` lists every one. -/

structure SiteChrome where
  /-- Extra `<head>` nodes (e.g. feed autodiscovery links). -/
  headExtra : List Html := []
  /-- Footer nodes rendered before the copyright line (e.g. a brand mark). -/
  footerPrelude : List Html := []
  /-- Footer nodes rendered between copyright and the verification badge. -/
  footerNav : List Html := []
  /-- Tooltip for the verification badge link (escaped at emission). -/
  badgeTitle : String := ""
  /-- Nodes inside the badge link, after the text span. -/
  badgeSuffix : List Html := []

/-! ## HTML generation (bilingual-native — one typed tree per route) -/

/-- `aria-current` on a nav link: `page` on the page itself, `true` on the
    section that contains it (a `news` item while reading `news/<id>`). -/
def currentAttr (target : Slug) : Option Slug → List (String × String)
  | some cur =>
      if target == cur then [("aria-current", "page")]
      else if target.segments.isPrefixOf cur.segments then [("aria-current", "true")]
      else []
  | none => []

def navLeafTree (site : Site) (lang : Lang) (current : Option Slug) : NavLeaf → Html
  | .page slug lbl =>
      .el "li" [] [.el "a" ([("href", (Route.mk slug lang).href site.config.defaultLang), ("class", "nav-link")] ++
        currentAttr slug current) [.text (lbl.get lang)]]
  | .external url lbl =>
      .el "li" [] [.el "a" [("href", urlToString url), ("class", "nav-link")] [.text (lbl.get lang)]]

def navItemTree (site : Site) (lang : Lang) (current : Option Slug) : NavItem → Html
  | .page slug label => navLeafTree site lang current (.page slug label)
  | .external url label =>
      .el "li" [] [.el "a" [("href", urlToString url), ("class", "nav-link"), ("rel", "external")]
        [.text (label.get lang)]]
  | .group label children =>
      -- One group level only — and that is all NavItem can express:
      -- `NavLeaf` makes a nested group unrepresentable, so nothing the
      -- validator accepts can be dropped here.
      .el "li" [] [.text (label.get lang), .el "ul" [] (children.map (navLeafTree site lang current))]

/-- Language switcher: one link per other language, pointing at the same
    slug in that language (`switcher_symmetric` is about the target set). -/
def switcherTree (site : Site) (slug : Slug) (lang : Lang) : List Html :=
  (switcherTargets lang).flatMap fun l =>
    [Html.el "a" [("href", (Route.mk slug l).href site.config.defaultLang), ("class", "language-link"),
        ("lang", l.code), ("hreflang", l.code)]
      [.text (site.config.langName l)],
     .text " "]

/-- `<link rel="alternate" hreflang=…>` for every alternate of the slug, and
    the canonical link — from the SAME `alternatesFor` the sitemap uses. -/
def alternateLinks (site : Site) (route : Route) : List Html :=
  alternateLinkTags site.config.canonicalBaseUrl site.config.defaultLang route.slug

def canonicalUrl (site : Site) (route : Route) : String :=
  canonicalUrlOf site.config.canonicalBaseUrl site.config.defaultLang route

/-- OpenGraph + Twitter card metadata from the same typed page data that
    renders the page — title/description cannot drift from what's on it. -/
def ogMetas (site : Site) (page : PageDef) (route : Route) : List Html :=
  let lang := route.lang
  [ogMeta "og:title" (page.title.get lang),
   ogMeta "og:description" (page.description.get lang),
   ogMeta "og:type" (if page.publishedAt.isSome then "article" else "website"),
   ogMeta "og:url" (canonicalUrl site route),
   ogMeta "og:image" (site.config.canonicalBaseUrl ++ page.socialImage.href),
   ogMeta "og:locale" (Lang.ogLocale lang)] ++
  (switcherTargets lang).map (fun l => ogMeta "og:locale:alternate" (Lang.ogLocale l)) ++
  page.publishedAt.toList.map (fun d => ogMeta "article:published_time" d.toString) ++
  [.void "meta" [("name", "twitter:card"), ("content", "summary_large_image")]]

def cssLinks (site : Site) : List Html :=
  (site.assets.filter (·.kind == .css)).map fun a =>
    .void "link" [("rel", "stylesheet"), ("href", a.path.href)]

def jsScripts (site : Site) : List Html :=
  (site.assets.filter (·.kind == .js)).map fun a =>
    .el "script" [("src", a.path.href), ("defer", "defer")] []

/-- The footer badge links to the report in the page's language. It is a
    label, not a count: the artifact gates run after the pages are emitted,
    so no number written into a page can equal the receipt's totals. -/
def badgeAttrs (site : Site) (lang : Lang) (chrome : SiteChrome) : List (String × String) :=
  [("href", (reportRoute lang).href site.config.defaultLang), ("class", "verification-badge-link")] ++
  (if chrome.badgeTitle.isEmpty then [] else [("title", chrome.badgeTitle)])

/-- The shell every HTML page shares, as one typed tree: the head essentials
    around the page's own head nodes, a skip link, the header (brand, nav
    with the current page marked, a `<details>` menu for narrow screens that
    needs no script, language switcher), `main` holding the page's nodes,
    the footer with the site's slots, and the scripts. `current` is the page
    the nav marks; the switcher links to `switchSlug` in the other language. -/
def shellTree (site : Site) (lang : Lang) (chrome : SiteChrome) (current : Option Slug)
    (switchSlug : Slug) (headNodes mainNodes : List Html) : Html :=
  let cfg := site.config
  let brandName := cfg.brand.get lang
  let homeHref := (Route.mk Slug.index lang).href cfg.defaultLang
  let badgeText := (⟨"検証レポート", "Verification report"⟩ : L).get lang
  let navItems := site.navigation.main.map (navItemTree site lang current)
  .el "html" [("lang", lang.code)] [
    .el "head" [] ([
      .void "meta" [("charset", "UTF-8")],
      .void "meta" [("name", "viewport"), ("content", "width=device-width, initial-scale=1.0")]] ++
      headNodes ++
      cssLinks site ++
      chrome.headExtra),
    .el "body" [("class", "site-body")] ([
      .el "a" [("href", "#main"), ("class", "skip-link")] [.text ((⟨"本文へ移動", "Skip to content"⟩ : L).get lang)],
      .el "header" [("class", "site-header")] [
        .el "nav" [("class", "container-wide nav-container")] [
          .el "a" [("href", homeHref), ("class", "nav-brand")] [
            .void "img" [("src", cfg.logoPath.href), ("alt", brandName), ("class", "brand-logo-image")],
            .el "span" [("class", "brand-name")] [.text brandName]],
          .el "ul" [("class", "nav-links")] navItems,
          .el "details" [("class", "nav-menu")] [
            .el "summary" [] [.text ((⟨"メニュー", "Menu"⟩ : L).get lang)],
            .el "ul" [("class", "nav-menu-list")] navItems],
          .el "div" [("class", "language-switcher")] (switcherTree site switchSlug lang)]],
      .el "main" [("id", "main")] mainNodes,
      .el "footer" [("class", "site-footer")] [
        .el "div" [("class", "container-wide")] (chrome.footerPrelude ++
          [Html.el "p" [] [.text s!"© {cfg.copyright.get lang}"]] ++
          chrome.footerNav ++
          [.el "p" [("class", "verification-badge")] [
            .el "a" (badgeAttrs site lang chrome) ([
              .el "span" [("class", "verification-badge-check"), ("aria-hidden", "true")] [.text "✓"],
              .el "span" [("class", "verification-badge-text")] [.text badgeText]] ++
              chrome.badgeSuffix)]])]] ++
      jsScripts site)]

/-- A route's head nodes: description, title, icon, canonical, hreflang
    alternates and OpenGraph — all from the page's typed data. -/
def pageHead (site : Site) (page : PageDef) (route : Route) : List Html :=
  let cfg := site.config
  let lang := route.lang
  -- Unless the page says otherwise — home page: the site's name alone;
  -- other pages: "Title | brand".
  let titleTag := match page.titleTag with
    | some t => t.get lang
    | none => if page.slug.isIndex then cfg.name.get lang else s!"{page.title.get lang} | {cfg.brand.get lang}"
  [.void "meta" [("name", "description"), ("content", page.description.get lang)],
   .el "title" [] [.text titleTag],
   .void "link" [("rel", "icon"), ("type", "image/png"), ("href", cfg.logoPath.href)],
   .void "link" [("rel", "canonical"), ("href", canonicalUrl site route)]] ++
  (if page.indexed then [] else [.void "meta" [("name", "robots"), ("content", "noindex")]]) ++
  alternateLinks site route ++
  ogMetas site page route

/-- The hero every route opens with: the page's title and lead over the
    page's `heroClass`. -/
def heroTree (page : PageDef) (lang : Lang) : Html :=
  .el "section" [("class", "hero hero-with-image " ++ page.heroClass)] [
    .el "div" [("class", "container-wide hero-inner")] [
      .el "div" [("class", "hero-copy")] (
        .el "h1" [] [.text (page.title.get lang)] ::
        page.lead.toList.map fun l => .el "p" [("class", "hero-lead")] [.text (l.get lang)])]]

/-- The full page as one typed tree: the shell around the route's head, its
    hero and the page's own body tree. -/
def generatePageTree (site : Site) (page : PageDef) (route : Route)
    (chrome : SiteChrome := {}) : Html :=
  shellTree site route.lang chrome (some page.slug) page.slug (pageHead site page route)
    (heroTree page route.lang :: page.body route.lang)

/-- A page tree as the bytes of its file. -/
def document (t : Html) : String :=
  "<!DOCTYPE html>\n" ++ Render.Tree.render t ++ "\n"

def generatePageHtml (site : Site) (page : PageDef) (route : Route)
    (chrome : SiteChrome := {}) : String :=
  document (generatePageTree site page route chrome)

/-! ### Not-found pages

One per language, outside the route set: no canonical, no alternates, not
in the sitemap. The host serves the nearest `404.html` up the requested
path, so `/en/…` misses get the English one. -/

def notFoundPath (d l : Lang) : String :=
  String.ofList (joinDirs ((Route.mk Slug.index l).dirSegments d) ++ "404.html".toList)

def notFoundTree (site : Site) (lang : Lang) (chrome : SiteChrome := {}) : Html :=
  let cfg := site.config
  let heading := (⟨"ページが見つかりません", "Page not found"⟩ : L).get lang
  let home := (⟨"トップページへ", "Go to the home page"⟩ : L).get lang
  shellTree site lang chrome none Slug.index
    [.el "title" [] [.text s!"{heading} | {cfg.brand.get lang}"],
     .void "link" [("rel", "icon"), ("type", "image/png"), ("href", cfg.logoPath.href)]]
    [.el "section" [("class", "section")] [
      .el "div" [("class", "container-wide")] [
        .el "h1" [("class", "section-heading")] [.text heading],
        .el "p" [] [.el "a" [("href", (Route.mk Slug.index lang).href cfg.defaultLang), ("class", "button")] [.text home]]]]]

def notFoundHtml (site : Site) (lang : Lang) (chrome : SiteChrome := {}) : String :=
  document (notFoundTree site lang chrome)

/-! ### The chrome cannot emit unbalanced markup -/

open Render.Tree in
theorem allWellFormedMod_map_of {α : Type} (l : List α) (f : α → Html)
    (h : ∀ x ∈ l, wellFormedMod (f x) = true) : allWellFormedMod (l.map f) = true := by
  rw [allWellFormedMod_iff]
  intro c hc
  simp only [List.mem_map] at hc
  obtain ⟨x, hx, rfl⟩ := hc
  exact h x hx

open Render.Tree in
theorem currentAttr_clean (target : Slug) (current : Option Slug) :
    (currentAttr target current).all (fun a => cleanToken a.1) = true := by
  unfold currentAttr
  split
  · split
    · decide
    · split <;> decide
  · decide

open Render.Tree in
theorem navLeafTree_wf (site : Site) (lang : Lang) (current : Option Slug) (leaf : NavLeaf) :
    wellFormedMod (navLeafTree site lang current leaf) = true := by
  cases leaf with
  | page slug lbl =>
    simp only [navLeafTree, wellFormedMod, allWellFormedMod, List.all_append, List.all_cons, List.all_nil,
      currentAttr_clean, Bool.and_true]; decide
  | external url lbl =>
    simp only [navLeafTree, wellFormedMod, allWellFormedMod, List.all_cons, List.all_nil, Bool.and_true]; decide

open Render.Tree in
theorem navItemTree_wf (site : Site) (lang : Lang) (current : Option Slug) (item : NavItem) :
    wellFormedMod (navItemTree site lang current item) = true := by
  cases item with
  | page slug label => exact navLeafTree_wf site lang current (.page slug label)
  | external url label => simp only [navItemTree, wellFormedMod, allWellFormedMod, List.all_cons, List.all_nil, Bool.and_true]; decide
  | group label children =>
    have hmap := allWellFormedMod_map_of children (navLeafTree site lang current)
      (fun l _ => navLeafTree_wf site lang current l)
    simp only [navItemTree, wellFormedMod, allWellFormedMod, hmap, Bool.and_true]
    decide

open Render.Tree in
theorem switcherTree_wf (site : Site) (slug : Slug) (lang : Lang) :
    allWellFormedMod (switcherTree site slug lang) = true := by
  rw [allWellFormedMod_iff]
  intro c hc
  simp only [switcherTree, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨l, _, hc⟩ := hc
  rcases hc with rfl | rfl
  · simp only [wellFormedMod, allWellFormedMod, List.all_cons, List.all_nil, Bool.and_true]; decide
  · rfl

open Render.Tree in
theorem alternateLinks_wf (site : Site) (route : Route) :
    allWellFormedMod (alternateLinks site route) = true := by
  simp only [alternateLinks, alternateLinkTags]
  exact allWellFormedMod_map_of _ _ (fun _ _ => by
    simp only [wellFormedMod, List.all_cons, List.all_nil, Bool.and_true]; decide)

open Render.Tree in
theorem ogMeta_wf (p v : String) : wellFormedMod (ogMeta p v) = true := by
  simp only [ogMeta, wellFormedMod, List.all_cons, List.all_nil, Bool.and_true]; decide

open Render.Tree in
theorem ogMetas_wf (site : Site) (page : PageDef) (route : Route) :
    allWellFormedMod (ogMetas site page route) = true := by
  have halt := allWellFormedMod_map_of (switcherTargets route.lang)
    (fun l => ogMeta "og:locale:alternate" (Lang.ogLocale l)) (fun _ _ => ogMeta_wf _ _)
  have hart := allWellFormedMod_map_of page.publishedAt.toList
    (fun d => ogMeta "article:published_time" d.toString) (fun _ _ => ogMeta_wf _ _)
  simp only [ogMetas, allWellFormedMod_append, allWellFormedMod, ogMeta_wf, halt, hart,
    Bool.and_true, Bool.true_and]
  simp only [wellFormedMod, List.all_cons, List.all_nil, Bool.and_true]
  decide

open Render.Tree in
theorem cssLinks_wf (site : Site) : allWellFormedMod (cssLinks site) = true :=
  allWellFormedMod_map_of _ _ (fun _ _ => by
    simp only [wellFormedMod, List.all_cons, List.all_nil, Bool.and_true]; decide)

open Render.Tree in
theorem jsScripts_wf (site : Site) : allWellFormedMod (jsScripts site) = true :=
  allWellFormedMod_map_of _ _ (fun _ _ => by
    simp only [wellFormedMod, allWellFormedMod, List.all_cons, List.all_nil, Bool.and_true]; decide)

open Render.Tree in
theorem badgeAttrs_clean (site : Site) (lang : Lang) (chrome : SiteChrome) :
    (badgeAttrs site lang chrome).all (fun a => cleanToken a.1) = true := by
  simp only [badgeAttrs]
  split <;> simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true] <;> decide

open Render.Tree in
/-- The shared shell adds no imbalance: it is well-formed whenever the page's
    head and main nodes and the site's slot trees are. -/
theorem shellTree_wf (site : Site) (lang : Lang) (chrome : SiteChrome) (current : Option Slug)
    (switchSlug : Slug) (headNodes mainNodes : List Html)
    (hheadNodes : allWellFormedMod headNodes = true)
    (hmain : allWellFormedMod mainNodes = true)
    (hhead : allWellFormedMod chrome.headExtra = true)
    (hpre : allWellFormedMod chrome.footerPrelude = true)
    (hnav : allWellFormedMod chrome.footerNav = true)
    (hsuf : allWellFormedMod chrome.badgeSuffix = true) :
    wellFormedMod (shellTree site lang chrome current switchSlug headNodes mainNodes) = true := by
  have hitems := allWellFormedMod_map_of site.navigation.main (navItemTree site lang current)
    (fun item _ => navItemTree_wf site lang current item)
  have hswitch := switcherTree_wf site switchSlug lang
  have hcss := cssLinks_wf site
  have hjs := jsScripts_wf site
  have hbadge := badgeAttrs_clean site lang chrome
  simp only [shellTree, wellFormedMod, allWellFormedMod, allWellFormedMod_append,
    List.cons_append, List.nil_append, List.all_cons, List.all_nil,
    hitems, hswitch, hcss, hjs, hbadge, hheadNodes, hmain, hhead, hpre, hnav, hsuf,
    Bool.and_true, Bool.true_and]
  decide

open Render.Tree in
theorem pageHead_wf (site : Site) (page : PageDef) (route : Route) :
    allWellFormedMod (pageHead site page route) = true := by
  have halt := alternateLinks_wf site route
  have hog := ogMetas_wf site page route
  unfold pageHead
  cases page.indexed <;>
    simp only [wellFormedMod, allWellFormedMod, allWellFormedMod_append, Bool.false_eq_true,
      if_true, if_false, List.cons_append, List.nil_append, List.all_cons, List.all_nil, halt, hog,
      Bool.and_true] <;>
    decide

open Render.Tree in
theorem heroTree_wf (page : PageDef) (lang : Lang) : wellFormedMod (heroTree page lang) = true := by
  unfold heroTree
  cases page.lead <;>
    simp only [Option.toList, List.map_cons, List.map_nil, wellFormedMod, allWellFormedMod,
      List.all_cons, List.all_nil, Bool.and_true] <;>
    decide

open Render.Tree in
/-- **The kernel chrome adds no imbalance**: for every site, page, route and
    chrome, the page tree is structurally well-formed whenever the site's
    slot trees and the page's body tree are. With
    `Render.Tree.render_wf_mod`, the rendered page is a well-formed fragment
    whenever the raw nodes inside those slots are. -/
theorem chrome_tree_wellFormed (site : Site) (page : PageDef) (route : Route)
    (chrome : SiteChrome)
    (hbody : allWellFormedMod (page.body route.lang) = true)
    (hhead : allWellFormedMod chrome.headExtra = true)
    (hpre : allWellFormedMod chrome.footerPrelude = true)
    (hnav : allWellFormedMod chrome.footerNav = true)
    (hsuf : allWellFormedMod chrome.badgeSuffix = true) :
    wellFormedMod (generatePageTree site page route chrome) = true :=
  shellTree_wf site route.lang chrome (some page.slug) page.slug _ _ (pageHead_wf site page route)
    (by simp only [allWellFormedMod, heroTree_wf, hbody, Bool.true_and]) hhead hpre hnav hsuf

open Render.Tree in
/-- The not-found pages are well-formed on the same terms as every route. -/
theorem notFoundTree_wellFormed (site : Site) (lang : Lang) (chrome : SiteChrome)
    (hhead : allWellFormedMod chrome.headExtra = true)
    (hpre : allWellFormedMod chrome.footerPrelude = true)
    (hnav : allWellFormedMod chrome.footerNav = true)
    (hsuf : allWellFormedMod chrome.badgeSuffix = true) :
    wellFormedMod (notFoundTree site lang chrome) = true :=
  shellTree_wf site lang chrome none Slug.index _ _
    (by simp only [allWellFormedMod, wellFormedMod, List.all_cons, List.all_nil, Bool.and_true]; decide)
    (by simp only [allWellFormedMod, wellFormedMod, List.all_cons, List.all_nil, Bool.and_true]; decide)
    hhead hpre hnav hsuf

structure OutputFile where
  path : String
  content : String
deriving Repr

/-- The full bilingual file set: every route, native paths, the page's own
    body in its slot. No post-processing step exists. -/
def generateFiles (site : Site) (chrome : Lang → SiteChrome) : List OutputFile :=
  site.routes.map fun (page, route) =>
    { path := route.outputPath site.config.defaultLang
    , content := generatePageHtml site page route (chrome route.lang) }

/-! ## Per-build checks on the trees themselves -/

/-! Does a fragment carry content a visitor can see or use? A non-blank text
    node, a raw slot with non-blank content, or a content-bearing element.
    Empty wrappers do not count. -/
mutual
def hasContent : Html → Bool
  | .text s => s.any (fun (c : Char) => !c.isWhitespace)
  | .raw s => s.any (fun (c : Char) => !c.isWhitespace)
  | .void tag _ => ["img", "input", "embed", "source"].contains tag
  | .el tag _ children =>
      ["img", "form", "video", "audio", "iframe", "canvas", "svg", "table", "textarea", "select", "button"].contains tag
        || anyContent children
def anyContent : List Html → Bool
  | [] => false
  | c :: rest => hasContent c || anyContent rest
end

/-- Every route's body slot has content (a blank page cannot ship). -/
def checkPageBodies (site : Site) : Guarantee :=
  let blank := site.routes.filterMap fun (p, r) =>
    if anyContent (p.body r.lang) then none else some (toString r)
  { category := "Structure", name := "Every page has a body"
    description := s!"All {site.routes.length} (page × language) body slots carry visible content — no blank page can ship"
    status := if blank.isEmpty then .checked else .failed s!"blank bodies: {String.intercalate ", " blank}"
    id := "site.page-bodies" }

/-- Every generated page tree is well-formed modulo its raw slots, and the
    raw slots are enumerated. -/
def checkPageTrees (site : Site) (chrome : Lang → SiteChrome) : Guarantee :=
  let trees := site.routes.map fun (p, r) => (r, generatePageTree site p r (chrome r.lang))
  let bad := trees.filterMap fun (r, t) =>
    if Render.Tree.wellFormedMod t then none else some (toString r)
  let raws := trees.map fun (r, t) => (r, (Render.Tree.raws t).length)
  let rawCount := (raws.map (·.2)).foldl (· + ·) 0
  let rawPages := (raws.filter (·.2 > 0)).map fun (r, _) => toString r
  { category := "Structure", name := "Page trees well-formed (modulo raw slots)"
    description := s!"All {trees.length} page trees are well-formed under the fragment grammar with void/normal tag classes; {rawCount} raw slot(s) on {rawPages.length} page(s) ({String.intercalate ", " rawPages}) are outside the grammar and covered by html-validate. render_wf_mod is conditional on those slots."
    status := if bad.isEmpty then .checked else .failed s!"ill-formed trees: {String.intercalate ", " bad}"
    location := some (toString ``NoGoals.Render.Tree.render_wf_mod)
    id := "site.page-trees" }

/-! ## Control Tests -/

def controlIndex : PageDef :=
  { slug := Slug.lit "index", title := ⟨"Home", "Home"⟩, description := ⟨"Home", "Home"⟩
    socialImage := AssetPath.lit "assets/images/hero.jpg", heroClass := "hero-img-hero"
    body := fun _ => [.el "p" [] [.text "home"]] }

def controlAbout : PageDef :=
  { slug := Slug.lit "about", title := ⟨"About", "About"⟩, description := ⟨"About", "About"⟩
    socialImage := AssetPath.lit "assets/images/hero.jpg", heroClass := "hero-img-hero"
    body := fun _ => [.el "p" [] [.text "about"]] }

def controlConfig : SiteConfig :=
  { name := ⟨"NoGoals Control", "NoGoals Control"⟩
    canonicalBaseUrl := "https://control.test"
    logoPath := AssetPath.lit "assets/images/logo.png" }

/-- Positive control: minimal valid site that should pass all checks -/
def positiveControlSite : Site := {
  config := controlConfig
  pages := [controlIndex, controlAbout]
  navigation := { main := [.page controlIndex.slug ⟨"Home", "Home"⟩, .page controlAbout.slug ⟨"About", "About"⟩] }
}

/-- Negative control: site with intentional errors that should fail specific checks -/
def negativeControlSite : Site := {
  config := controlConfig
  pages := [controlIndex, { controlIndex with title := ⟨"Dupe", "Dupe"⟩ }]  -- ERROR: duplicate slug
  navigation := {
    main := [
      .page controlIndex.slug ⟨"Home", "Home"⟩,
      .page (Slug.lit "nonexistent") ⟨"Broken", "Broken"⟩  -- ERROR: broken link
    ]
  }
  divisions := [{ id := Segment.lit "div1", name := ⟨"Div", "Div"⟩, summary := ⟨"S", "S"⟩, description := ⟨"D", "D"⟩ }]
  people := [
    { id := Segment.lit "person1", name := ⟨"P", "P"⟩, role := ⟨"R", "R"⟩, bio := ⟨"B", "B"⟩,
      division := some (Segment.lit "nonexistent-div") }  -- ERROR: invalid division ref
  ]
}

/-- Expected failures for negative control -/
def negativeControlExpectedFailures : List String := [
  "Unique page slugs",
  "Navigation links resolve",
  "People reference existing divisions"
]

def runtimeChecks (site : Site) : List Guarantee :=
  [checkNavLinks site, checkUniqueSlugs site, checkUniqueDivisions site,
   checkUniquePeople site, checkPeopleDivisions site]

/-- Run control tests -/
def runControlTests : List ControlResult :=
  let posFailures := (runtimeChecks positiveControlSite).filter (·.isFailed) |>.map (·.name)
  let posResult : ControlResult := {
    name := "Positive Control"
    description := "Valid site with all checks passing"
    expectedFailures := []
    actualFailures := posFailures
    passed := posFailures.isEmpty
  }
  let negFailures := (runtimeChecks negativeControlSite).filter (·.isFailed) |>.map (·.name)
  let negResult : ControlResult := {
    name := "Negative Control"
    description := "Invalid site - verification should detect errors"
    expectedFailures := negativeControlExpectedFailures
    actualFailures := negFailures
    passed := negativeControlExpectedFailures.all (negFailures.contains ·) &&
              negFailures.length == negativeControlExpectedFailures.length
  }
  [posResult, negResult]

/-! ## Build Result -/

structure BuildResult where
  files : List OutputFile
  report : VerificationReport
  controls : List ControlResult
deriving Repr

def BuildResult.controlsPassed (r : BuildResult) : Bool :=
  r.controls.all (·.passed)

def compile (site : Site) (timestamp : String := "unknown")
    (chrome : Lang → SiteChrome := fun _ => {})
    (extraGuarantees : List Guarantee := []) : BuildResult :=
  let staticGuarantees := typeLevelGuarantees ++ theoremGuarantees ++ securityGuarantees
  -- The bridge: refine this build's route set through the verified IR.
  -- The resulting entry is COMPUTED from the actual refine outcome.
  let structErrs := structuralErrors site
  let nVariants := site.routes.length
  let structuralG : Guarantee :=
    if structErrs.isEmpty then
      { category := "Theorems"
        name := "Structural invariants proven for this build"
        description := s!"NoGoals.refine constructed a verified SiteV for all {nVariants} (page × language) routes of this site's page SKELETON (slugs, languages, output paths — bodies are the trusted shell's): (slug,lang) round-trip, i18n completeness across both languages, unique output paths"
        status := .enforced "NoGoals.refine → SiteV proof fields, this build"
        location := some (toString ``NoGoals.refine)
        scope := .artifact, id := "site.structural", headline := true }
    else
      { category := "Theorems"
        name := "Structural invariants proven for this build"
        description := "NoGoals.refine REJECTED this site"
        status := .failed (String.intercalate "; " (structErrs.map (·.render)))
        location := some (toString ``NoGoals.refine)
        scope := .artifact, id := "site.structural" }
  let treeChecks := [checkPageBodies site, checkPageTrees site chrome]
  -- `extraGuarantees` are applied as UPDATES keyed by stable id: when the
  -- consumer restates a kernel-generic theorem as a proof about ITS build
  -- (the artifact-level bridge), the restatement replaces the kernel entry
  -- instead of duplicating it. Then dedupe defends against same-key
  -- entries arriving twice from any one source.
  let allGuarantees := dedupeGuarantees
    (updateGuarantees (staticGuarantees ++ [structuralG] ++ treeChecks ++ runtimeChecks site) extraGuarantees)
  let controls := runControlTests
  -- FAIL CLOSED: there is no input for which the build both reports a
  -- failure and produces output files.
  let files :=
    if allGuarantees.all (fun g => !g.isFailed) && controls.all (·.passed) then
      generateFiles site chrome
    else []
  let report : VerificationReport := {
    siteName := site.config.name.en
    timestamp := timestamp
    pageCount := site.pages.length
    assetCount := site.assets.length
    guarantees := allGuarantees
  }
  { files, report, controls }

end NoGoals.Compile
