---
name: NoGoals
description: Build and maintain a static website with NoGoals, the Lean 4 static site generator whose emitted site is machine-verified (links, assets, paths, bilingual completeness proved; CSP, HTML validity, SEO, redirects and permalinks gated fail-closed at build time). Use this whenever a user wants to create, scaffold, edit, audit, debug or deploy a NoGoals site, mentions NoGoals, `NoGoals.Build`, `SiteBuild`, `lake exe build-site`, a "verified" or "formally verified" website, or asks why a NoGoals build or audit went red — even if they only say "add a page", "fix the broken link", "the audit failed" or "make the site" inside a Lean project that depends on NoGoals.
---

# NoGoals — a website that cannot be broken

NoGoals is a Lean 4 library. A site is a Lean package that `require`s NoGoals, defines
its content as typed data, and runs `NoGoals.Build.run` as its build executable.
If the build succeeds, the site's links resolve, its assets exist, both
languages are complete, its output paths are unique, and every runtime gate
passed; if anything fails, no output is produced. That is the whole promise,
and it is why the workflow below is strict about a few things.

Read `references/model.md` first if you have not built a NoGoals site before; it
explains the three tiers (type-enforced, theorem-proved, runtime-checked)
and what each file in a site is for. Then use the section here that matches
the task.

## Scaffold a new site

1. Copy the contents of this skill's `assets/` directory into the new
   repository root. It is a complete, minimal site that audits green as-is:
   `lakefile.lean`, `lean-toolchain`, `Site/*.lean`, `Build.lean`,
   `package.json`, `.htmlvalidate.json`, `scripts/`, `.gitignore`, a
   stylesheet defining every class the chrome emits, placeholder images.
   Rename the namespace if the user wants (search and replace `MySite`).
2. Point the dependency at NoGoals. In `lakefile.lean` the template uses a path
   dependency (`require nogoals from ".." / "nogoals"`); for a published NoGoals use
   `require nogoals from git "<url>" @ "<tag>"`. **Never run `lake update`**
   afterwards: Lean and Mathlib are pinned by NoGoals, and re-resolving breaks the
   build. `lean-toolchain` must match NoGoals's.
3. `npm ci`. The gates need the two pinned node tools in `package.json`:
   `html-validate` and `parse5` (the lockfile pins their dependencies too).
   Node `^22.22.0 || >=24.8.0` — html-validate's range, which `package.json`
   declares.
4. Fill in `Site/Config.lean` (`canonicalBaseUrl` is the production origin —
   every absolute URL derives from it), then pages, navigation, assets.
5. First audit: `./scripts/build.sh --audit --offline --update-baseline`.
   The flag bootstraps the permalink baseline (a fresh site has no
   published URLs yet); once a baseline exists it prints a warning and
   leaves the file alone. From then on:
   `./scripts/build.sh` for a plain build, `--audit --offline` for every
   gate but the network one, `--audit` before a deploy. Read the receipt at
   `build/verification/receipt.json`: `totals.failed` must be 0, and
   `totals.skipped` 0 under a full audit. `lake exe build-site --help` lists
   the flags; an unknown flag is a usage error, never a quieter build.
6. Look at it: `./scripts/preview.sh` serves `build/` on localhost. Every
   URL NoGoals emits is root-absolute, so opening `build/index.html` from disk
   shows an unstyled page with dead links; that is the viewer, not the site.
7. Commit (including `deploy/permalink-baseline.txt`). Then
   `./scripts/test-fail-closed.sh` (needs `jq`) once to prove the
   transactional build works on this machine.

## The shape of a site (what goes where)

| File | What it holds | Why it is typed this way |
|---|---|---|
| `Site/Config.lean` | `SiteConfig`: names, `canonicalBaseUrl`, `defaultLang`, `logoPath` | One origin; one path function derives every URL from it |
| `Site/Blocks.lean` | a closed `inductive PageId` (+ `all`, `all_complete`) and the `Block` vocabulary | `pages` is BUILT from `PageId.all`, so a link to an unregistered page is unrepresentable |
| `Site/Bodies/*.lean` | `List Block` per page, bilingual `L` leaves | A page cannot ship with one language missing |
| `Site/Render.lean` | `Block → List Html` (typed tree), `slug`, `hrefP`, `siteChrome` | Escaping is the tree renderer's job; attribute names are `[a-z0-9-]` tokens; `Html.raw` is the one escape hatch and the report lists every use |
| `Site/Pages.lean` | `body`, `staticPage : PageId → PageDef`, `pages`, `navigation`, `site` | One route derivation feeds pages, sitemap, feeds |
| `Site/Assets.lean` | `AssetDef` list with `AssetPath.lit "…"` | Paths validated at the literal (lower-case, no `..`) |
| `Site/Verified.lean` | two `native_decide` theorems + `bridge` | Proves NoGoals accepts the site; the build stages exactly the paths of the proved `SiteV` |
| `Build.lean` | a `SiteBuild` spec around `bridge`, `main := NoGoals.Build.run spec` | Everything generic lives in NoGoals |

Every identifier the site reuses is a validated literal: `Slug.lit "about"`,
`Segment.lit "team"`, `AssetPath.lit "assets/images/logo.png"`,
`IsoDate.lit "2026-01-31"`. A bad literal is a compile error at the call
site. That is the intended experience: when the build says
`Segment.lit "About Us"` failed to prove `valid`, the fix is the literal
(`about-us`), not the checker.

## Add a page

1. Add a constructor to `PageId` in `Site/Blocks.lean` and to `PageId.all`;
   `all_complete`, `Render.slug`, `body` and `staticPage` then fail to
   compile until every arm exists — that is the registry doing its job.
2. Write the body in `Site/Bodies/<Page>.lean` as `List Block`, both
   languages per leaf.
3. Link to it from `navigation` in `Site/Pages.lean` or a `.cta .newPage`
   in another body. A page nothing links to fails the reachability gate; a
   page deliberately reached only by a server redirect declares
   `reachedByRedirect := true` in its `PageDef`; `indexed := false` keeps
   such a page (a form's receipt) out of the sitemap and search.
4. Build. If the page's stylesheet class (`heroClass`) does not exist in the
   CSS, the CSS-contract gate names it.

## Add an article (news / blog)

Articles are data: `NewsArticle` records (`id := Segment.lit "…"`,
`date := .lit "YYYY-MM-DD"`, bilingual title/summary/paragraphs) in
`site.news`, plus one `articlePage : NewsArticle → PageDef` mapped over that
list into `pages` and one `AtomFeed` per language built from the same list
(`references/model.md` shows both). Then an article's page, sitemap entry,
feed entry and permalink obligation all derive from one record. Keep the
list sorted newest-first (the news gate checks it) and never future-dated.

## Read a red build

The build prints one line per gate and quarantines the failed candidate in
`build.failed/` without touching `build/` (the last green output). Look at
the `✗` lines; each names the file and the exact reference, id, class or
URL. The receipt in `build.failed/verification/receipt.json` records the
failed gate under its stable id. `references/gates.md` lists every gate,
what it reads, and the usual cause of each failure. Do not "fix" a red gate
by widening an allowance (`cjkAllow`, `semanticClasses`,
`dynamicEndpoints`) unless the flagged thing is genuinely a decision the
site is making; those lists exist so decisions are written down, not so
failures disappear.

A build that fails BEFORE the gates (a Lean error) is a type error in site
data: an unregistered page, a missing language, an invalid literal, a body
referencing a person who does not exist. The message names the file and
line; fix the data.

## Ship

`./scripts/build.sh --audit` (full profile, network gate included) must be
green at a committed HEAD before any deploy; the receipt records both the
site's and NoGoals's commits and whether either tree was dirty, so a deploy
preflight can refuse anything else. Renaming a URL
requires a typed `Redirect` in the site's redirect list; the build renders
`_redirects` from it and the permanence gate proves every previously
published URL is still live or redirected. See `references/deploy.md`.

## What NoGoals does not do

- No markdown front-end: content is Lean data by design (that is where the
  proofs come from). Long prose can be authored in files and generated into
  Lean by a script the site owns.
- Bilingual Japanese/English only in this version (`L` has exactly `ja` and
  `en`; `Lang` is closed). A site with a different language set is a NoGoals
  change, not a site change.
- Host semantics are Cloudflare Pages (`/x/` ↦ `x/index.html`, `_headers`,
  `_redirects`). Other hosts serve the artifact but the deploy script is
  Pages-specific.
