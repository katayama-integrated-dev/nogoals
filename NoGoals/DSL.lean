/-
  NoGoals Site Definition DSL

  Ergonomic types for defining static site content. These are the "input"
  types — user-friendly, not yet link-resolved. They convert to NoGoals's
  verified IR types (SiteV, Assets, etc.).

  Identity is typed at the leaves: a page's `slug`, a person's or article's
  `id`, an asset's `path` are validated `Slug`/`Segment`/`AssetPath` values
  (`Slug.lit "about"`, `Segment.lit "zero-person-company"`,
  `AssetPath.lit "assets/images/logo.png"`), so a name that could escape the
  output root, collide across case, or fail as an `id=` is a compile error
  at the literal, and every route/href/output path is derived from one
  function (`NoGoals.Route`).
-/

import NoGoals.IR.Route
import NoGoals.IR.Atoms
import NoGoals.IR.Assets
import NoGoals.Render.Tree
import NoGoals.Verify.Date

namespace NoGoals.DSL

/-! ## Bilingual Content -/

/-- Bilingual text (Japanese + English) -/
structure L where
  ja : String
  en : String
deriving Repr, DecidableEq, Inhabited

/-- Shorthand constructor for bilingual text -/
def L.mk' (ja en : String) : L := ⟨ja, en⟩

/-- Deliberately language-neutral text (technical terms, proper nouns).
    This replaces the old silent `Coe String L` instance: "not translated
    yet" must be visible at the call site, and `grep L.same` enumerates
    every language-neutral string on the site. -/
def L.same (s : String) : L := ⟨s, s⟩

/-- Select language from bilingual content — total by cases on `Lang`. -/
def L.get (content : L) : Lang → String
  | .ja => content.ja
  | .en => content.en

/-! ## Page Definitions -/

/-- What the hero shows under the page title. -/
inductive HeroLead
  /-- The meta description (the default). -/
  | description
  /-- A tagline that differs from the meta description. -/
  | text (lead : L)
  /-- The title alone, for pages whose title already says it all. -/
  | omitted
deriving Repr

/-- A page: its route identity, its metadata, and its BODY as a typed HTML
    tree per language. The body lives here so that generating a page can
    never look a body up by name and miss — there is no registry to fall
    through. -/
structure PageDef where
  slug : Slug
  title : L
  description : L
  /-- The `<title>` text, when it is not the default (home page: the site's
      `name`; other pages: `title | brand`). A product's home page wants its
      tagline here without renaming the site. -/
  titleTag : Option L := none
  heroLead : HeroLead := .description
  /-- The image link previews show (`og:image`). The hero's own background
      is the stylesheet's business, through `heroClass`. -/
  socialImage : AssetPath
  /-- Stylesheet class carrying the hero background (`image-set()` etc.).
      The page declares it; the CSS-contract gate checks the stylesheet
      defines it. -/
  heroClass : String
  /-- The page is reached by a server redirect (a form's landing page), not
      by any click path — the reachability gate treats it as a declared
      exception instead of an orphan. -/
  reachedByRedirect : Bool := false
  /-- `false` keeps the page out of search: it is served as usual, with
      `<meta name="robots" content="noindex">` in its head and no sitemap
      entry (a form's receipt, say). -/
  indexed : Bool := true
  /-- Publication date, for article pages (`og:type article`). -/
  publishedAt : Option NoGoals.Verify.IsoDate := none
  /-- The page body per language — the trusted shell's typed trees, spliced
      into `<main>` after the hero. -/
  body : Lang → List NoGoals.Render.Tree.Html

def PageDef.lead (p : PageDef) : Option L :=
  match p.heroLead with
  | .description => some p.description
  | .text lead => some lead
  | .omitted => none

/-! ## Navigation -/

/-- A leaf navigation entry — the only content a nav group may hold.
    Nesting a group inside a group is unrepresentable on purpose: the
    chrome renders exactly one group level, so a deeper tree could only
    be validated-then-silently-dropped (an earlier version did exactly
    that — `checkNavLinks` accepted grandchildren the renderer discarded). -/
inductive NavLeaf
  | page (slug : Slug) (label : L)
  | external (url : Url.Safe) (label : L)
deriving Repr

/-- Navigation item. Page references are validated at compile time
    (`checkNavLinks`); external URLs must be `Url.Safe`, so `javascript:`
    is not even representable. -/
inductive NavItem
  | page (slug : Slug) (label : L)
  | external (url : Url.Safe) (label : L)
  | group (label : L) (children : List NavLeaf)
deriving Repr

/-- Navigation structure -/
structure Navigation where
  main : List NavItem
  footer : List NavItem := []
deriving Repr

/-! ## Division (Business Unit) -/

/-- A focus area within a division: a name and a one-sentence description. -/
structure FocusArea where
  name : L
  description : L
deriving Repr

structure Division where
  id : Segment
  name : L
  /-- One sentence, for a directory of divisions. -/
  summary : L
  description : L
  focusAreas : List FocusArea := []
deriving Repr

/-! ## Person -/

structure Person where
  id : Segment
  name : L
  role : L
  division : Option Segment := none
  bio : L
  photoPath : Option AssetPath := none
deriving Repr

/-! ## Product -/

inductive ProductStatus | research | development | preview | available
deriving Repr, DecidableEq

structure Product where
  id : Segment
  division : Segment
  name : L
  tagline : L
  description : L
  status : ProductStatus
  featured : Bool := false
deriving Repr

/-! ## News -/

structure NewsArticle where
  /-- The article's id — a validated segment, so `news/<id>` is a valid slug
      by construction and the id is a legal `id=` attribute. -/
  id : Segment
  /-- ISO calendar date; `IsoDate.lit` rejects a malformed literal at compile time. -/
  date : NoGoals.Verify.IsoDate
  title : L
  summary : L
  /-- Bilingual paragraphs. Each `L` is one paragraph in JA + EN. Fully type-checked
      for translation completeness. -/
  paragraphs : List L := []
  tags : List String := []
  author : Option L := none  -- Bilingual byline; signed essays carry an author
  division : Option Segment := none  -- Optional division id this article belongs to
  chips : List L := []  -- Bilingual category labels rendered as focus-chips
deriving Repr

/-- The slug of an article's own page: `news/<id>`. Total — both parts are
    validated segments. -/
def NewsArticle.slug (a : NewsArticle) : Slug :=
  ⟨[Segment.lit "news", a.id], by simp⟩

/-! ## Asset -/

structure AssetDef where
  path : AssetPath
  kind : AssetKind := .other
deriving Repr

/-! ## Site Configuration -/

structure SiteConfig where
  name : L
  /-- Absolute origin of the published site, e.g. `https://nogoals.org`.
      Every absolute URL (sitemap, canonical, feeds, OpenGraph) is
      `canonicalBaseUrl ++ Route.href`. -/
  canonicalBaseUrl : String
  defaultLang : Lang := .ja
  logoPath : AssetPath
  /-- Display name for the header brand mark, when it differs from `name`
      (the home page's `<title>` and the default copyright holder). -/
  brandName : Option L := none
  /-- Who the footer's © line names, when it is not `name` (a product site
      published by a company). -/
  copyrightHolder : Option L := none
  /-- Language-switcher labels: the `ja` field is the label of the Japanese
      variant, the `en` field that of the English one. -/
  langNames : L := ⟨"日本語", "EN"⟩
deriving Repr

def SiteConfig.brand (c : SiteConfig) : L := c.brandName.getD c.name

def SiteConfig.copyright (c : SiteConfig) : L := c.copyrightHolder.getD c.name

def SiteConfig.langName (c : SiteConfig) (lang : Lang) : String := c.langNames.get lang

/-! ## Complete Site Definition (Unverified) -/

/-- Site definition - the user-facing input type.
    This gets validated and converted to NoGoals.SiteV for verification. -/
structure Site where
  config : SiteConfig
  pages : List PageDef
  navigation : Navigation
  divisions : List Division := []
  people : List Person := []
  products : List Product := []
  news : List NewsArticle := []
  assets : List AssetDef := []

/-- **The route set**: every page in every language. This is the single
    derivation `toSiteRaw`, `generateFiles`, the sitemap and the feeds all
    consume — the emitted files, their URLs and their SEO metadata are views
    of this one list. -/
def Site.routes (site : Site) : List (PageDef × Route) :=
  Lang.all.flatMap fun lang => site.pages.map fun p => (p, ⟨p.slug, lang⟩)

/-! ## Validation -/

/-- Check that all navigation links point to existing pages -/
def Site.validateNavLinks (site : Site) : List String :=
  let pageSlugs := site.pages.map (·.slug)
  let checkLeaf : NavLeaf → List String
    | .page slug _ => if pageSlugs.contains slug then [] else [s!"broken nav link: {slug}"]
    | .external _ _ => []
  let checkItem : NavItem → List String
    | .page slug _ => if pageSlugs.contains slug then [] else [s!"broken nav link: {slug}"]
    | .external _ _ => []
    | .group _ children => children.flatMap checkLeaf
  site.navigation.main.flatMap checkItem ++ site.navigation.footer.flatMap checkItem

end NoGoals.DSL
