# NoGoals — architecture

## Stack & pins

- **Lean:** `leanprover/lean4:v4.28.0` (pinned in `lean-toolchain`).
- **Mathlib:** pinned **by rev in `lakefile.lean`** (matching
  `lake-manifest.json` at `8f9d9cff6bd728b17a24e163c9402775d9e6a365 (tag v4.28.0)`, with aesop, batteries, plausible,
  proofwidgets, Qq, Cli locked alongside). The old `@ "master"` require — where
  a casual `lake update` silently re-resolved and broke the build — was
  retired on August 4, 2026. `lake update` runs only in a deliberate
  upgrade that also rebuilds katayama.dev, the first consumer.
- **Build:** `lake build` (the proofs check during the build),
  `lake script run test` (NoGoalsTest `#guard`s + integration),
  `./verify.sh` (the one honest counter: theorems, sorries, `#print axioms`
  audit; splices numbers into README, exits nonzero on drift).

## Architecture

**One pipeline; verified kernel + declared trusted shell.**

```
DSL.Site ──refine──▶ SiteV ──plan──▶ BuildPlan ──render(chrome, slots)──▶ files
   │           (Except: located     (unique_paths,      │
   │            VErrors, fatal)      coverage)          │
   └── runtime tier: config sanity, external links,     └── shell fills typed
       HTML validation, CSP↔content — all fail closed       slots (PageBlocks,
                                                            trusted, declared)
```

- **Kernel (verified):** `NoGoals/IR/Route` (validated `Segment`/`Slug`/
  `AssetPath`, closed `Lang`, `Route.href`/`outputPath` — THE path function —
  and `resolveUrl`, browser + Cloudflare Pages semantics, with `resolve_href`),
  `NoGoals/IR` (atoms, assets, verified HTML with typed anchors), `Resolve/Refine`
  (raw→verified; every error located by route + block path; links resolve in
  the source language), `Render/Plan` (+ `unique_paths`, `coverage`,
  `rendered_link_resolves`, `rendered_fragment_declared`), `Render/Html`
  (total; escaping and tree-grammar theorems, void/normal tag classes),
  `Meta` (sitemap/robots/headers over routes; `alternatesFor` shared with the
  chrome; `sitemap_covers` is a membership theorem).
- **Shell (trusted, declared):** every page is ONE typed tree: kernel chrome
  (head incl. canonical/hreflang/OG, nav, hero, footer) around
  `PageDef.body : Lang → List Html`, which the consumer's `PageBlocks`
  renderer builds (total, escaped by the tree). A site may declare `raw`
  nodes, e.g. a form it renders itself (`verbatimHtml`); the report counts
  them and names the pages that carry them. No string slot exists.
- **Runtime tier:** HTML facts from a pinned browser-grade parser
  (`tools/html-facts.mjs`, parse5) decoded strictly by `Verify/HtmlFacts`;
  gates over facts (`Verify/SiteAudit`: reference closure, bounded CSP, SEO
  coherence, CJK/escaping/CSS contract, reachability), html-validate with a
  canary (`Verify/HtmlValidate`), permalink obligations + `_redirects`
  (`Verify/Permalinks`), dates/attestations against the wall clock. Fail
  closed; a profile's skipped checks are visible in the receipt, and the
  deploy preflight requires every gate of the full-audit profile.
- **Report:** generated from term-level anchors (type/theorem tiers) and
  actual check results (runtime tier). It cannot drift by construction.

## The invariant system, honestly summarized

Three enforcement tiers; the distinction is load-bearing (DESIGN §3):

**Tier 1 — type-enforced.** `Segment`/`Slug`/`AssetPath` (paths cannot
escape the root or collide across case); closed `Lang`; `Fin n` link targets;
`{a // a ∈ Anc p}` fragments (AnchorIn, wired); `AssetId n k A` (existence +
kind witness); `NonEmptyStr`; `Url.Safe`; `L` (both languages or it doesn't
compile); a site's closed page-id type.

**Tier 2 — theorem-proved.** Over arbitrary `SiteV`/`BuildPlan`:
`unique_paths`, `coverage`, `i18nComplete`, `roundTrip₁`, `resolve_href` +
`rendered_link_resolves` (route closure), `rendered_fragment_declared`,
`render_wf`/`render_wf_mod` (tree grammar), `chrome_tree_wellFormed`,
`sitemap_covers`/`hreflang_symmetric`/`alternates_complete`,
`permalinks_sound`, BFS `reachableFrom_soundness`, srcset `widths_cover`,
`htmlEscape` correctness.

**Tier 3 — runtime-checked.** What the type system can't see from inside
Lean: files on disk, external URLs, html-validate, CSP↔content, manifest
diffs. All fail closed.

## The consumer contract (katayama.dev, the first consumer)

- Wiring: the consumer's `lakefile.lean` — `require nogoals from ".." / "nogoals"`.
  Sibling repos on disk; the path dependency is the deployment mechanism.
  NoGoals changes land in lockstep commits with the site's consuming change.
- Surface consumed: `DSL`, the compile/verify entry points, `Meta`,
  `Verify/*`, and the kernel render path with typed slots.
- Obligations: (1) NoGoals builds under the pinned toolchain; (2) the consumed
  surface doesn't change incompatibly without a lockstep site commit;
  (3) new theorems/features are driven by a site need.

## Locked

- **Pinned toolchain is the compatibility story.** Upgrades only as a
  deliberate change with the site rebuilt against it.
- **Path dependency stays.** Publishing adds a git URL for outsiders; the
  site keeps consuming by path.
- **`native_decide` is acceptable but disclosed** — the axiom audit reports
  `ofReduceBool` wherever it's used; it is never hidden behind "0 axioms."

## Resolved decisions

- **August 4, 2026:** Mathlib pinned by rev in the lakefile (was: manifest-only).
- **August 4, 2026:** License is MIT everywhere (docs/README's "TBD" retired with
  the file).
