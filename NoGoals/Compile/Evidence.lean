/-
  Report evidence — what a guarantee IS, before anything renders it.

  A `Guarantee` carries its status (enforced / checked / failed / skipped /
  not-applicable), its SCOPE (what it is a fact about), a stable `id` for
  replacement-by-key, and an elaborator-resolved theorem anchor when one
  exists. The badge count, the failure count and the "skipped is never
  passed" rule are defined here, once, and every renderer reads them.
-/

namespace NoGoals.Compile

inductive GuaranteeStatus
  | enforced (mechanism : String)  -- Guaranteed by type system/theorems
  | checked                        -- Runtime check passed
  | failed (reason : String)       -- Runtime check failed
  | notApplicable                  -- Feature not used
  | skipped (reason : String)      -- Check exists but did NOT run this build
deriving Repr

/-- What a guarantee is actually *about*. The report must never present a
    fact about the kernel's IR renderer as a fact about the shipped site:
    scope is the field that keeps those claims apart.

    - `kernel`: the verified IR renderer (`refine → plan → render`). True of
      any content routed through it — which, today, does NOT include the
      consumer's page bodies.
    - `chrome`: the typed chrome tree every shipped page is wrapped in
      (head/nav/hero/footer); the body slot excluded.
    - `trustedShell`: the consumer's declared-trusted block renderer.
    - `artifact`: the concrete build artifact of THIS run — emitted files,
      generated sitemap/feeds/headers, runtime check results. -/
inductive GuaranteeScope
  | kernel
  | chrome
  | trustedShell
  | artifact
deriving Repr, DecidableEq

def GuaranteeScope.render : GuaranteeScope → String
  | .kernel => "kernel"
  | .chrome => "chrome"
  | .trustedShell => "trusted-shell"
  | .artifact => "artifact"

structure Guarantee where
  category : String
  name : String
  description : String
  status : GuaranteeStatus
  location : Option String := none
  scope : GuaranteeScope := .artifact
  /-- Stable identity for deduplication and for replacing a `.skipped`
      placeholder with the actual result of the same check. Empty means
      "identified by name" (fine for per-item runtime entries whose name
      IS the identity). -/
  id : String := ""
  /-- Shown on the quiet public verification page (set where the guarantee is
      defined, never selected by display name). -/
  headline : Bool := false
deriving Repr

/-- Dedup/replacement key: explicit id, else display name. -/
def Guarantee.key (g : Guarantee) : String :=
  if g.id.isEmpty then g.name else g.id

def Guarantee.isFailed (g : Guarantee) : Bool :=
  match g.status with | .failed _ => true | _ => false

def Guarantee.isPositive (g : Guarantee) : Bool :=
  match g.status with | .enforced _ => true | .checked => true | _ => false

/-- Keep the first occurrence of each key. -/
def dedupeGuarantees (gs : List Guarantee) : List Guarantee :=
  gs.foldl (fun acc g => if acc.any (·.key == g.key) then acc else acc ++ [g]) []

/-- Replace guarantees by key with updated results (e.g. a `.skipped`
    placeholder with the outcome of the check that actually ran). Keys in
    `updates` not present in `gs` are appended. -/
def updateGuarantees (gs updates : List Guarantee) : List Guarantee :=
  let replaced := gs.map (fun g =>
    match updates.find? (·.key == g.key) with
    | some u => u
    | none => g)
  let newOnes := updates.filter (fun u => !gs.any (·.key == u.key))
  replaced ++ newOnes

structure VerificationReport where
  siteName : String
  timestamp : String
  pageCount : Nat
  assetCount : Nat
  guarantees : List Guarantee
deriving Repr

def VerificationReport.failCount (r : VerificationReport) : Nat :=
  r.guarantees.filter (·.isFailed) |>.length

def VerificationReport.skippedCount (r : VerificationReport) : Nat :=
  r.guarantees.filter (fun g => match g.status with | .skipped _ => true | _ => false) |>.length

def VerificationReport.enforcedCount (r : VerificationReport) : Nat :=
  r.guarantees.filter (fun g => match g.status with | .enforced _ => true | _ => false) |>.length

def VerificationReport.checkedCount (r : VerificationReport) : Nat :=
  r.guarantees.filter (fun g => match g.status with | .checked => true | _ => false) |>.length

def VerificationReport.allPassed (r : VerificationReport) : Bool :=
  r.failCount == 0

end NoGoals.Compile
