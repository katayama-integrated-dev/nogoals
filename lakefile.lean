import Lake
open Lake DSL
open System

package «nogoals» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib «NoGoals» where
  roots := #[`NoGoals]

-- Test library (build with: lake build NoGoalsTest); includes the axiom audit.
lean_lib «NoGoalsTest» where
  roots := #[`NoGoals.Test]
  globs := #[.submodules `NoGoals.Test]

lean_exe «nogoals» where
  root := `NoGoals.CLI.Main
  supportInterpreter := true

-- Process-boundary tests (fake executables): lake exe nogoals-test-io
lean_exe «nogoals-test-io» where
  root := `NoGoals.Test.HtmlValidateIO
  supportInterpreter := true

-- Run with: lake script run test
script test do
  IO.println "Running NoGoals tests (building NoGoalsTest runs all #guard assertions"
  IO.println "and the axiom audit)..."
  let exitCode ← IO.Process.spawn {
    cmd := "lake"
    args := #["build", "NoGoalsTest"]
  } >>= (·.wait)
  if exitCode != 0 then
    IO.println "❌ Tests failed."
    return 1
  IO.println "✅ NoGoalsTest built: all compile-time assertions hold."
  let ioCode ← IO.Process.spawn {
    cmd := "lake"
    args := #["exe", "nogoals-test-io"]
  } >>= (·.wait)
  if ioCode != 0 then
    IO.println "❌ Process-boundary tests failed."
    return 1
  return 0

-- Pinned by rev (matches lake-manifest.json). A bare "master" here would let any
-- `lake update` silently re-resolve against the pinned v4.28.0 toolchain and
-- break the build. An upgrade is a deliberate change of its own (see ARCHITECTURE.md).
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @
  "8f9d9cff6bd728b17a24e163c9402775d9e6a365"
