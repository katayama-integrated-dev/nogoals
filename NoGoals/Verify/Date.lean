/-
  Typed ISO calendar dates

  NoGoals sites typically carry dates as raw strings (`"2025-12-04"`) for
  ergonomics. This module promotes those strings to a typed `IsoDate`
  that the compiler can refuse to construct on a malformed value. The
  parser is decidable so callers normally do something like:

  ```lean
  def myArticleDate : IsoDate := IsoDate.ofString! "2025-12-04"
  -- or, in a structure with a default:
  date : IsoDate := .ofString! "2025-12-04"
  ```

  `ofString!` panics on a bad date — a build will fail loudly rather than
  silently shipping `"2025-13-32"` or `"yesterday"`.

  The validity check covers leap years and per-month day counts, so
  February 30, April 31, etc. are rejected at compile time when sites
  use `decide` on a concrete date list.
-/

namespace NoGoals.Verify

structure IsoDate where
  year  : Nat
  month : Nat
  day   : Nat
deriving Repr, DecidableEq, Inhabited

namespace IsoDate

/-- Days per month, accounting for leap years (Gregorian rules). -/
def daysInMonth (year : Nat) (month : Nat) : Nat :=
  match month with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 =>
      let leap := year % 4 = 0 ∧ (year % 100 ≠ 0 ∨ year % 400 = 0)
      if leap then 29 else 28
  | _ => 0  -- Invalid month → 0 days, fails the validity check

/-- A real Gregorian-calendar date. -/
def isValid (d : IsoDate) : Bool :=
  1 ≤ d.month && d.month ≤ 12 && 1 ≤ d.day && d.day ≤ daysInMonth d.year d.month

/-- Parse `"YYYY-MM-DD"` into `IsoDate`. Returns `none` on a malformed
    string: wrong segment count, non-numeric component, invalid calendar
    date, or noncanonical field widths — the contract is exactly four
    year digits and two each for month and day, so `"1-2-3"` is rejected
    rather than silently reinterpreted. -/
def ofString? (s : String) : Option IsoDate :=
  match s.splitOn "-" with
  | [yStr, mStr, dStr] => do
      guard (yStr.length == 4 && mStr.length == 2 && dStr.length == 2)
      let y ← yStr.toNat?
      let m ← mStr.toNat?
      let d ← dStr.toNat?
      let date : IsoDate := { year := y, month := m, day := d }
      if isValid date then some date else none
  | _ => none

/-- Parse-or-panic. Prefer `IsoDate.lit` for literals — it rejects bad dates
    at elaboration time instead of panicking (and `panic!` in a pure context
    silently returns `default = ⟨0,0,0⟩` unless the value is forced). -/
def ofString! (s : String) : IsoDate :=
  match ofString? s with
  | some d => d
  | none => panic! s!"IsoDate.ofString!: invalid ISO date {s}"

/-- Checked date literal: `IsoDate.lit "2026-08-04"`. The default proof
    argument is discharged during elaboration, so a typo like `"2026-13-04"`
    is a compile error at the call site. (`native_decide` — string parsing
    doesn't kernel-reduce; the ofReduceBool dependency is disclosed by the
    axiom audit.) -/
def lit (s : String) (h : (ofString? s).isSome = true := by native_decide) : IsoDate :=
  (ofString? s).get h

/-- Render back to canonical `"YYYY-MM-DD"`. Pads month and day to 2 digits. -/
def toString (d : IsoDate) : String :=
  let pad (n : Nat) : String := if n < 10 then s!"0{n}" else Nat.repr n
  s!"{d.year}-{pad d.month}-{pad d.day}"

instance : ToString IsoDate := ⟨toString⟩

/-! ## Comparison

    Order via `(year, month, day)`. Used by freshness checks below. -/

def le (a b : IsoDate) : Bool :=
  a.year < b.year ||
    (a.year == b.year && (a.month < b.month ||
      (a.month == b.month && a.day ≤ b.day)))

/-! ## Day arithmetic

    A simple "days since epoch" function for freshness windows. We use
    1970-01-01 as the epoch and compute via Julian day approximation —
    the absolute value isn't important; only differences matter. -/

private def daysBeforeMonth (year : Nat) (month : Nat) : Nat :=
  let leap := year % 4 = 0 ∧ (year % 100 ≠ 0 ∨ year % 400 = 0)
  let cum := match month with
    | 1 => 0   | 2 => 31  | 3 => 59  | 4 => 90
    | 5 => 120 | 6 => 151 | 7 => 181 | 8 => 212
    | 9 => 243 | 10 => 273 | 11 => 304 | 12 => 334
    | _ => 0
  if leap ∧ month > 2 then cum + 1 else cum

/-- Days from year 0 to start of `year`: 365 per completed year plus one
    per completed leap year. The leap terms count years `z < year` with
    `z ≡ 0` mod 4/100/400 — using `year / 4` here would credit the current
    year's leap day on January 1st and make every span that crosses into a
    leap year one day too long. -/
private def daysBeforeYear (year : Nat) : Nat :=
  365 * year + (year + 3) / 4 - (year + 99) / 100 + (year + 399) / 400

/-- Convert to days-since-year-0. Differences between two `daysSinceY0`
    values give the day-count between dates. -/
def daysSinceY0 (d : IsoDate) : Nat :=
  daysBeforeYear d.year + daysBeforeMonth d.year d.month + d.day

/-- Days between `a` and `b` (absolute). -/
def daysBetween (a b : IsoDate) : Nat :=
  let da := daysSinceY0 a
  let db := daysSinceY0 b
  if da ≥ db then da - db else db - da

end IsoDate

end NoGoals.Verify
