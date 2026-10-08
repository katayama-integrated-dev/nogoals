/-
  Typed content attestations

  NoGoals sites commonly carry per-field attestation metadata in the source
  data (e.g. `data/news.json` has `verifiedBy/verifiedAt/method` blocks
  on every editorial leaf). This module promotes those blocks to typed
  Lean values and adds a freshness check.

  ## Rationale

  String-attached `verifiedAt` strings drift. After a year, every leaf
  claims to have been verified, but no human has looked at any of them
  in months. Lifting the timestamp to `IsoDate` lets us write:

  ```lean
  theorem all_news_fresh :
      ∀ a ∈ news, daysSince today a.titleAttest.verifiedAt ≤ 365 := by
    native_decide
  ```

  …which fails at the next build *after* a leaf goes stale, not silently.

  Sites supply a "today" date (typically read at compile time from a
  build-info constant or a stamped file). `daysSince today att = ...`
  uses `IsoDate.daysBetween`.

  ## Methods

  We track *how* each item was verified — distinguishing human review,
  automated decide, attestation-by-quote (citing a source), etc. — so the
  report can summarize trust levels.
-/

import NoGoals.Verify.Date

namespace NoGoals.Verify

inductive AttestationMethod where
  /-- A human reviewed the content and confirmed accuracy. -/
  | human
  /-- An automated check (decide / native_decide / fixed transform) confirmed
      the content. Trust is bounded by the check's correctness. -/
  | automated
  /-- The content cites an external source (URL, book, paper). Trust is
      bounded by source persistence and accuracy. -/
  | cited
  /-- Provenance unknown / legacy / placeholder. Use sparingly. -/
  | unknown
deriving Repr, DecidableEq, Inhabited

structure Attestation where
  /-- Who or what attested. Free-form (`"Founder"`, `"People Ops"`,
      `"build:native_decide"`, etc.). -/
  verifiedBy : String
  /-- When the attestation was made. Typed — must parse as a real date. -/
  verifiedAt : IsoDate
  /-- How verification was performed. -/
  method     : AttestationMethod
deriving Repr, Inhabited

namespace Attestation

/-- Build a fresh attestation pinned to today. Convenience for sites that
    stamp content as it's written. -/
def now (verifiedBy : String) (today : IsoDate) (method : AttestationMethod := .human) : Attestation :=
  { verifiedBy, verifiedAt := today, method }

/-- Days since the attestation. `today - verifiedAt`. -/
def daysSince (today : IsoDate) (att : Attestation) : Nat :=
  IsoDate.daysBetween today att.verifiedAt

/-- True iff the attestation was made on or before `today` AND is at most
    `maxAge` days old. The order premise matters: `daysBetween` is an
    absolute distance, so without it a *future-dated* attestation — which
    can only be a data error — would count as fresh. -/
def isFresh (today : IsoDate) (maxAge : Nat) (att : Attestation) : Bool :=
  IsoDate.le att.verifiedAt today && daysSince today att ≤ maxAge

/-! ## Bulk freshness check

    Sites typically have many attestations across news/people/products/etc.
    Collect them into a `List (String × Attestation)` (label + att) and run
    the check across the list. Discharged by `native_decide` in practice. -/

abbrev LabeledAttestation := String × Attestation

/-- True iff every attestation in `items` is at most `maxAge` days old
    relative to `today`. -/
def allFresh (today : IsoDate) (maxAge : Nat) (items : List LabeledAttestation) : Bool :=
  items.all (fun (_, att) => isFresh today maxAge att)

/-- Collect every (label, days-old) pair where the attestation is older
    than `maxAge`. Empty iff `allFresh = true`. -/
structure StaleEntry where
  label    : String
  daysOld  : Nat
  verifier : String
deriving Repr

def stale (today : IsoDate) (maxAge : Nat) (items : List LabeledAttestation) : List StaleEntry :=
  items.filterMap fun (label, att) =>
    let d := daysSince today att
    if d > maxAge then
      some { label, daysOld := d, verifier := att.verifiedBy }
    else none

/-- Pretty-print stale entries. -/
def formatStale (entries : List StaleEntry) : String :=
  if entries.isEmpty then "✓ all attestations fresh"
  else
    "✗ stale attestations detected:\n" ++
    String.intercalate "\n" (entries.map fun e =>
      s!"  • {e.label}: {e.daysOld} days old (verified by {e.verifier})")

end Attestation

end NoGoals.Verify
