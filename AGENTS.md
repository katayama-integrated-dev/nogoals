# NoGoals — conventions for contributors and agents

Read `OVERVIEW.md` first. It maps every document and resource in this
repository.

`PLAN.md` is the working plan and status ledger. It is kept in the private
working repository and is not part of releases.

## Build, test, verify

- Build: `lake build`. The proofs check during the build.
- Tests: `lake script run test` (the `#guard` suite, the kernel-level axiom
  audit, and the process-boundary tests).
- Claims: `./verify.sh`. It computes the theorem, sorry and axiom counts,
  writes them into both READMEs and `site/Site/Counts.lean` with `--write`,
  and exits nonzero when either has drifted.

## Toolchain

Lean v4.28.0 is pinned in `lean-toolchain`; Mathlib is pinned by commit in
`lakefile.lean` and `lake-manifest.json`. Do not run `lake update`. An
upgrade is its own change, and it rebuilds the first consumer as well.

## Consumers

NoGoals is a general tool with one motivating site.

- The first consumer is katayama.dev, the company's website. It lives in a
  separate repository, checked out next to this one, and requires NoGoals
  by path (`require nogoals from ".." / "nogoals"`). A change to the
  surface below lands together with the consumer's matching change.
- The second consumer is nogoals.org, built from `site/`.

The surface sites depend on: `DSL`, the compile and verify entry points,
`Meta`, `Verify/*`, the report renderer, and the values sites read
(`Guarantee`, `GuaranteeScope.render`, `GateDef`, `builtinGates`, the
guarantee lists in `Compile`). Do not break it.

After any surface change, the skill's scaffold (`skills/nogoals/assets/`)
and `site/` (`./scripts/build.sh --audit`) must still build and audit green.

## Rules

- Counts are generated. Never write a theorem, sorry or axiom count by hand
  anywhere; `./verify.sh --write` produces them.
- Fail closed. No check may report a failure while the build still produces
  output.
- Typed slots only. No `String.replace` post-processing of emitted HTML.
- Writing. Present tense. No session or operator narrative. Every claim is
  qualified to what the checks prove: type-enforced, theorem-proved, or
  runtime-gated under `--audit`. Dates are written as September 25, 2026.

## Releases

Releases are one-way exports from the private working repository. A script
there archives a tag, scrubs it against a denylist, builds and audits the
export on its own, and commits it into the public repository as one commit
and one annotated tag under the division's identity. The push is manual. The
site is then rebuilt from the public clone with `--audit`, scrubbed again,
and deployed; the permalink baseline that the deploy rewrites is committed
back to the private repository.
