/-
# NoGoals — the smallest static site generator that cannot emit a broken website

A formally verified static site generator in Lean 4. Pure functional core
with kernel-checked proofs; IO only at the boundaries.

## Modules (every one is consumed by the pipeline, the consumer, or the tests)
- DSL:      user-facing site definition (typed, bilingual `L` content)
- Compile:  DSL front-door — checks, chrome, verification report
- Bridge:   a site's two native_decide proofs → its SiteV, output list, report entries
- Build:    the publisher's build (`NoGoals.Build.run`): artifact, gates, receipt, promotion
- Meta:     typed sitemap / robots / headers / manifest generators
- IR:       the verified core types (Route, Atoms, Assets, HtmlRaw, HtmlVerified)
- Resolve:  raw → verified refinement (errors are fatal and located)
- Render:   HTML rendering and build plan (`unique_paths`, `coverage`)
- Images:   responsive srcset mathematics (proof showcase; see module doc)
- Nav:      BFS reachability with soundness proofs (proof showcase)
- Verify:   build-time checks — strings, dates, attestations,
            external links, permalinks, site audit over parser facts,
            html-validate
- CLI:      build entry points
-/

import NoGoals.DSL
import NoGoals.Compile
import NoGoals.Bridge
import NoGoals.Build
import NoGoals.Compile.Evidence
import NoGoals.Compile.Report
import NoGoals.Meta

import NoGoals.IR.Route
import NoGoals.IR.Atoms
import NoGoals.IR.Assets
import NoGoals.IR.HtmlRaw
import NoGoals.IR.HtmlVerified

import NoGoals.Resolve.Refine

import NoGoals.Render.Html
import NoGoals.Render.Plan
import NoGoals.Render.Feed

import NoGoals.Images.Srcset
import NoGoals.Nav.Reachability

import NoGoals.Verify.Strings
import NoGoals.Verify.Date
import NoGoals.Verify.Attestation
import NoGoals.Verify.External
import NoGoals.Verify.Permalinks
import NoGoals.Verify.SiteAudit
import NoGoals.Verify.Json
import NoGoals.Verify.HtmlFacts
import NoGoals.Verify.HtmlValidate

import NoGoals.CLI.Main
