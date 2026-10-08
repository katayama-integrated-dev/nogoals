import Lake
open Lake DSL

package «my-site» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

-- NoGoals as a path dependency (a sibling checkout). For a published NoGoals:
--   require nogoals from git "https://github.com/katayama-integrated-dev/nogoals" @ "v0.1.0"
-- (Build.lean's nogoalsDir and the fail-closed script assume the sibling
-- checkout; adjust both.)
-- Never run `lake update`: Lean and Mathlib are pinned by NoGoals.
require nogoals from ".." / "nogoals"

@[default_target]
lean_lib «Site» where
  roots := #[`Site]

lean_exe «build-site» where
  root := `Build
  supportInterpreter := true
