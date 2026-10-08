# The NoGoals model

## Three tiers, honestly labelled

Every claim in the verification report says which tier backs it:

- **Type-enforced.** Unrepresentable states: a link target is a `PageId`;
  a slug is a `Slug` (validated segments); an asset path is an `AssetPath`;
  a bilingual string is an `L` with both fields; a date is an `IsoDate.lit`.
- **Theorem-proved.** Facts about the kernel for ANY site (`unique_paths`,
  `coverage`, `resolve_href`, `render_wf`) and, through `NoGoals.Bridge`,
  instances of them for THIS site.
- **Runtime-checked.** What only the emitted bytes can show: HTML validity,
  CSP consistency, link closure, SEO coherence, permalinks. Fail closed:
  a red gate means no output.

The report's `scope` field says what a guarantee is ABOUT: `kernel` (the
IR renderer only — labelled as such on the report), `chrome`, `artifact`.

## The pipeline

```
Site (your Lean data)
  └─ Site.routes = pages × [ja, en]           one derivation of every route
       ├─ NoGoals.Compile.toSiteRaw → NoGoals.refine → SiteV   structure proved
       ├─ generatePageTree per route          ONE typed tree: kernel chrome
       │                                      around your body trees
       └─ sitemap / feeds / canonical / hreflang    all from Route.href
NoGoals.Build.run
  ├─ artifact list (pages, assets, feeds, sitemap, robots, _headers, _redirects, late files)
  ├─ stage → gates over parser facts → receipt → finalization pass
  └─ promote on green / quarantine on red
```

## Identity literals

| Literal | Accepts | Rejects |
|---|---|---|
| `Segment.lit` | `[a-z0-9-]+` | upper case, `.`, `/`, spaces |
| `Slug.lit` | segments joined by `/` (`news/my-post`) | `a//b`, `/a`, `a/` |
| `AssetPath.lit` | `[a-z0-9._-]+` segments (`assets/img/logo.png`) | upper case, `.`, `..` |
| `IsoDate.lit` | `YYYY-MM-DD`, real calendar date | `2026-13-01`, `2026-2-1` |

Lower-case only is deliberate: on a case-insensitive filesystem two
differently-cased names are one file.

## The chrome

NoGoals renders every page as one tree: `<head>` (charset, viewport,
description, title, icon, canonical, hreflang alternates incl. `x-default`,
OpenGraph, stylesheets, your `headExtra`), header with brand + nav +
language switcher, hero (`h1`, lead, background class), your body trees,
footer (your prelude, copyright, your nav, the verification badge with your
suffix), deferred scripts. You do not write this markup; you fill the
`SiteChrome` slots with trees.

## Articles and feeds

```lean
def articlePage (a : NewsArticle) : PageDef :=
  { slug := a.slug                      -- news/<id>, total: both parts are validated segments
    title := a.title, description := a.summary
    socialImage := AssetPath.lit "assets/images/hero.png", heroClass := "hero-img-default"
    publishedAt := some a.date          -- og:type article
    body := fun lang => [Render.renderArticle lang a] }

def pages : List PageDef := PageId.all.map staticPage ++ news.map articlePage

def feedFor (lang : Lang) : NoGoals.Render.Feed.AtomFeed :=
  { title := (⟨"ニュース", "News"⟩ : L).get lang
    baseUrl := config.canonicalBaseUrl, defaultLang := config.defaultLang, lang
    entries := news.map fun a =>
      { title := a.title.get lang, route := ⟨a.slug, lang⟩, date := a.date
        summary := a.summary.get lang, author := a.author.map (·.get lang) } }
-- Build.lean: feeds := [feedFor .ja, feedFor .en]
```

Links to an article from a body: `(Route.mk a.slug lang).href config.defaultLang`.
