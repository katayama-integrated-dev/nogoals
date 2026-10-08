# NoGoals — design

## Principles (the constitution)

1. **Invalid states are unrepresentable.** The types rule them out
   (`Fin n`, `AssetId`, `NonEmptyStr`, `Url.Safe`, `Ref`, `L`). Where a
   state can't be made unrepresentable, the check fails closed: there is
   no input for which the build both reports a failure and produces
   output.
2. **Every claim NoGoals makes about itself must be machine-checked.** No
   hand-written counts anywhere; report entries carry term-level anchors to
   the theorems they cite, so a renamed theorem breaks the report's build.
   A count typed by hand, a badge with a stub behind it, or a consumer
   hiding entries of NoGoals's own report would each make a claim
   unchecked, so the design leaves no place for any of them.
3. **Be honest about the enforcement tier.** Type-enforced, theorem-proved,
   runtime-checked — the report says which is which, and never claims a tier
   the build path doesn't exercise.
4. **One pipeline, boundary declared.** A verified kernel
   (IR → refine → plan → render) vouches for structure: links, assets, paths,
   i18n arity, escaping. A *declared trusted shell* (the consumer's
   presentational block vocabulary) fills typed slots. No post-hoc string
   surgery on emitted HTML; nothing bypasses the kernel. Design vocabulary
   (gradients, grids) is deliberately left unformalized, and the declared
   boundary says so.
5. **Verification is for the publisher first.** The build-time gates protect
   the person maintaining the site; the public verification page is a quiet
   secondary artifact. Demand drives theorems — NoGoals grows when
   katayama.dev needs a page shape or a guarantee, never from a roadmap.
6. **General tool, one motivating site.** NoGoals is open source for anyone
   building a static site. katayama.dev, the company's website, is the first
   consumer and the source of every feature request; the design reaches past
   it. Nothing site-specific lives in NoGoals (`NoGoals.Build.run` takes a
   `SiteBuild` spec; a site's own gates, chrome, feeds and proofs are its
   own), and the way in for others is the agent skill in `skills/nogoals/`
   rather than a second front-end. NoGoals grew out of Omega, an earlier
   internal effort to coordinate many parallel agents writing formally
   verifiable components; what held up was a narrower verification surface for
   one class of artifact, a website.

## The defining moments

**The publisher moment (primary).** A content edit on katayama.dev either
builds — in which case every link is an index into the site's pages, every
asset reference names a declared asset and the file is on disk, every text
field has both languages, no previously published URL broke — or fails with an
error naming the page, the block, and the nearest valid alternative. `cd site
&& ./scripts/build.sh --audit` (in a scaffold copy, the same script in the
copied directory) is one command, one exit code, run before every deploy.

**The publish moment (secondary).** A reader discovers a production website
whose correctness claims are machine-checked and can verify that in under a
minute: generated README numbers with CI enforcing them per commit, one click
to the real consumer wiring, a short quiet verification page whose entries
cannot drift by construction, and, from 1.0, the essay. **Failure mode
this must not have:** the reader spot-checks one number and finds it wrong — one drifted
count converts "machine-proven" into "asserted."

## Quality bar (checkable gates — 1 to 7 pass before any release; 8 before 1.0)

| # | Gate | Check |
|---|---|---|
| 1 | Counts generated, never hand-written | `verify.sh` computes theorem/sorry/axiom numbers and splices them into README; script exits nonzero on drift. |
| 2 | CI enforces the claim | Action runs build + tests + `verify.sh` per commit; fails on any sorry / undisclosed axiom; badge in README. |
| 3 | No false claim surfaces | No echo-checklist "verification," no stub-backed guarantee, no report entry without a term-level anchor or an actual runtime result behind it. |
| 4 | One pipeline | The deployed site is built through refine→SiteV→plan→render; no consumer needs a blocklist to hide entries of NoGoals's own report. |
| 5 | Fail closed | A failing check aborts the build. Demonstrated by negative-control tests. |
| 6 | Scratch swept | No abandoned proof scratch or session logs in the published tree. |
| 7 | Real URL + versioned tag | Install instructions point at the real repo; v0.1.0 is tagged; the path-dependency pattern documented. |
| 8 | The essay exists (1.0) | Not in v0.1.0. Including the honest two-pipelines arc: where proofs earned their keep, where a test would have done, where the boundary sits now. |

## Locked

- **Usability for outsiders is the agent skill.** No markdown front-end or
  second DSL; the usability layer is the agent skill
  (`skills/nogoals/SKILL.md`): an agent scaffolds and maintains a site against
  the one Lean API. Friendly errors and support posture are demand-driven.
- **A release waits for its claims.** Nothing is published until every claim
  it makes is true and machine-checked; scope does not shrink to meet a date,
  because one unchecked claim costs the credibility of all the others.
- **Publisher-first verification.** The public page is quiet; the gate suite
  is the product.
