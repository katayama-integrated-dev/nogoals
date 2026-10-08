# NoGoals — UX (consumer surfaces)

NoGoals is a library; its "UX" is the consumer's experience, in two personas —
now deliberately ranked publisher first (DESIGN principle 5).

## Persona 1: the publisher (the maintainer of katayama.dev, the first consumer)

The product is the edit-build-audit loop:

- **Authoring:** typed `DSL.Site` + `PageBlocks` content in Lean. Bilingual
  `L` fields mean a missing translation doesn't compile; `L.same` marks
  deliberately language-neutral strings and is greppable/auditable.
- **Errors are located.** A broken link or missing asset fails the build with
  page → block → offending reference and a did-you-mean from the slug map.
  (Lean-literate errors; making them friendly for non-Lean users stays
  locked out without demand.)
- **`cd site && ./scripts/build.sh --audit` before deploy** (in a scaffold
  copy, the same script in the copied directory): one command, one exit
  code — compile and refine the site, stage the build, run the gate suite
  (HTML validation, CSP↔content, links and reachability, SEO, assets,
  feeds, permalink permanence against the previous manifest, external links;
  `--offline` skips network), and promote to `build/` only on green. It does
  not run NoGoals's own test suite or `verify.sh`. Fail closed: no green, no
  deploy.
- **The class of surprise this kills:** silent ones. No paragraph silently
  dropped, no `String.replace` that silently stopped matching, no renamed
  slug that 404s old inbound links, no EN page shipping Japanese chrome.

## Persona 2: the reader (the publish target)

Surface: the GitHub repo + the site's quiet verification page; from 1.0,
the essay.

- **First screen:** README. Headline counts are script-generated with a CI
  badge enforcing them per commit.
- **The number that makes the case:** the sorry count in the README's
  generated count block, spliced in by `verify.sh` and enforced by CI; axioms
  audited and disclosed (`ofReduceBool` where `native_decide` is used).
- **Proof of reality:** one click to the consumer wiring of the scaffold in
  `skills/nogoals/assets/`.
- **The verification page:** short and quiet — the three-tier split, a few
  true statements whose type/theorem entries carry term-level anchors (they
  cannot drift), and the build command with the source identity
  (`cd site && ./scripts/build.sh --audit`). No badge walls.
- **Depth on demand:** the code; from 1.0, the essay for the argument
  (including the honest two-pipelines story).

## Voice & copy

The project speaks in checkable statements. Golden: the README's count block,
"N theorems, S sorries — counted by `verify.sh`, enforced by CI", where every
number was spliced in by the script.
Fail: any hand-typed number, any "enforced" badge without code behind it.
The difference: one survives a spot-check by a skeptic, the other converts
the pitch into theater.
