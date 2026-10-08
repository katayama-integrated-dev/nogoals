# The gates

Run with `lake exe build-site --audit` (full) or `--audit --offline` (all but
the network gate). Each gate has a stable id; the receipt lists every gate
of the profile with `checked`, `failed`, or `skipped` plus the reason.

| id | Reads | Fails when | Usual fix |
|---|---|---|---|
| `gate.external` | HEAD of every http(s) URL in the emitted HTML | not 2xx (same-origin redirects followed) | URL moved: update it; cross-origin redirect: the URL is stale |
| `gate.html-validate` | pinned `html-validate` over every HTML file | any error | fix the markup; for a raw slot, fix the raw HTML |
| `gate.html-facts` | parse5 facts for every HTML file | producer failed or schema mismatch | `npm ci`; NoGoals and site versions out of sync |
| `gate.csp` | facts vs the typed CSP | inline `<script>`/`<style>`/`style=`/`on*=`, unlisted origin, unmodelled element | move styles to the stylesheet; add the origin to `spec.csp` (per directive) only if the site really loads from it |
| `gate.links` | every href/src/srcset/poster/action | no emitted file at the resolved path; fragment not an id on the target; malformed | fix the link; for a form posting to a function, add the exact path to `dynamicEndpoints` |
| `gate.seo` | route pages' canonical/hreflang/og:url/og:locale vs their route | a value differs from what the route predicts | the head is NoGoals's; a violation means a route or the default language changed under a page |
| `gate.metadata` | route pages' `<html lang>`, title, description, og:title/description/type, og:locale:alternate | missing, empty or duplicated | fill the page's `title`/`description`; the rest is NoGoals's head |
| `gate.i18n-cjk` | visible text of EN pages | Japanese characters not in `cjkAllow` | translate; add to `cjkAllow` only for deliberate Japanese (a brand mark) |
| `gate.assets` | `url(/assets/…)` in stylesheets | file missing from the artifact | declare the asset in `Assets.lean` or fix the CSS |
| `gate.news` | article dates | not newest-first, or future-dated | reorder; fix the date |
| `gate.feeds` | feed entry routes | an entry route is not emitted | feeds must be built from the same news list |
| `gate.css-contract` | class tokens vs stylesheets | a class no stylesheet defines | add the rule; `semanticClasses` only for classes that exist for JS or third-party hooks |
| `gate.escaping` | visible text | `&amp;` etc. in decoded text | you escaped twice — pass plain text to `Html.text` |
| `gate.reachability` | `<a href>` graph from `reachabilityRoots` | a page no click path reaches | link to it, or mark `reachedByRedirect` if a redirect lands there |
| `gate.permalinks` | `deploy/permalink-baseline.txt` vs emitted files + redirects | a previously published URL gone without a redirect; redirect chain/self/duplicate/shadowing; no baseline | add a `Redirect`; never delete a redirect whose source is an obligation |
| custom gates | whatever the site declares in `customGates` | its own rule | its own fix |

Compile-time checks that run before the gates and abort the build:
structural refinement (`site.structural`: route collisions, a slug named
after a language), `site.page-bodies` (a body that renders blank),
`site.page-trees` (an ill-formed tree — impossible from `Render.lean` unless
an attribute name is not a clean token).

## Receipt

`build/verification/receipt.json`: `profile.name` and `profile.required`
(every gate id the profile must have run), `source` (site and NoGoals commits +
dirty flags), `pins`, `evaluated.date` (the wall-clock date freshness checks
used), `redirects` (sources), `totals`, and one entry per guarantee with
`tier`, `scope` and theorem `anchor`. What a deploy preflight requires of it
is in `deploy.md`.
