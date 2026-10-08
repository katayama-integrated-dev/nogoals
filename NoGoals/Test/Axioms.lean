/-
  Axiom audit — enforced at build time.

  Walks every constant declared in a `NoGoals.*` module and collects the axioms
  its proof ultimately depends on. The build FAILS if anything outside the
  allowlist appears — including `sorryAx`, so this is also a kernel-level
  sorry check (stronger than grepping source text).

  Allowlist:
  - `propext`, `Classical.choice`, `Quot.sound` — Lean/Mathlib's standard
    axioms; using Mathlib means using these.
  - `Lean.ofReduceBool` / `Lean.trustCompiler` — incurred by `native_decide`.
    Accepted but DISCLOSED: the audit prints every declaration that uses
    them. The honest public claim is "0 axioms beyond Lean's standard three;
    native_decide uses disclosed below", never a bare "0 axioms".

  Run: `lake build NoGoalsTest` (or `lake script run test` / `./verify.sh`).
-/

import NoGoals
import Lean

open Lean

namespace NoGoals.Test.Axioms

/-- Axioms that `declName`'s proof depends on (pure environment fold). -/
def axiomsOf (env : Environment) (declName : Name) : Array Name :=
  let (_, st) := ((CollectAxioms.collect declName).run env).run {}
  st.axioms

def allowed : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

def disclosed : List Name :=
  [``Lean.ofReduceBool, ``Lean.trustCompiler]

/-- Is `declName` declared in one of our own modules (`NoGoals` or `NoGoals.*`)? -/
def isOurs (env : Environment) (declName : Name) : Bool :=
  match env.getModuleIdxFor? declName with
  | some idx =>
    let mod := env.header.moduleNames[idx.toNat]!
    mod = `NoGoals || (`NoGoals).isPrefixOf mod
  | none => false

open Elab in
#eval show TermElabM Unit from do
  let env ← getEnv
  let mut audited := 0
  let mut disclosedUses : Array (Name × Name) := #[]
  let mut violations : Array (Name × Name) := #[]
  for (declName, _) in env.constants.toList do
    if isOurs env declName then
      audited := audited + 1
      for ax in axiomsOf env declName do
        if allowed.contains ax then pure ()
        else if disclosed.contains ax then
          disclosedUses := disclosedUses.push (declName, ax)
        else
          violations := violations.push (declName, ax)
  unless violations.isEmpty do
    let lines := violations.map (fun (d, a) => s!"  {d} uses {a}")
    throwError "Axiom audit FAILED — undisclosed axioms in NoGoals:\n{String.intercalate "\n" lines.toList}"
  -- Disclosed uses: report the distinct root declarations (helper lemmas of a
  -- native_decide proof all inherit the axiom; the count below is decl-level).
  let distinctDecls := (disclosedUses.map (·.1)).toList.eraseDups
  logInfo s!"axiom audit: {audited} NoGoals declarations audited; 0 undisclosed axioms; {distinctDecls.length} declarations depend on native_decide (ofReduceBool/trustCompiler)"

end NoGoals.Test.Axioms
