import Lake
open Lake DSL

-- NoGoals's own website, built with NoGoals: the second consumer, in the same repo.
-- `scripts/build.sh` links `.lake/packages` to NoGoals's, so Mathlib is fetched
-- and built once. Never run `lake update`: Lean and Mathlib are pinned by NoGoals.
package «nogoals-site» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require nogoals from ".."

@[default_target]
lean_lib «Site» where
  roots := #[`Site]

lean_exe «build-site» where
  root := `Build
  supportInterpreter := true
