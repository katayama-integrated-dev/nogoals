/-
  String-content verification

  A small generic module for "no forbidden substring appears in any rendered
  page." Common uses:

  • **Brand regression**: forbid retired brand names so a renamed product
    can't sneak back into copy. (e.g. forbid `"Light Gap"` after renaming to
    `"LightGap"`.)
  • **Public/private leak**: forbid the markers of internal-only sections so
    that content can never reach a public artifact. (e.g. forbid `"# Backstage"`
    or `"DO NOT INCLUDE IN PUBLIC OUTPUT"`.)
  • **Retired names**: forbid retired identifiers so old aliases stay
    retired. (e.g. a product's former code name.)

  The check is decidable on finite strings, so sites typically discharge it
  via `native_decide` at compile time.

  ## Usage

  ```lean
  import NoGoals.Verify.Strings

  def myForbidden : List NoGoals.Verify.ForbiddenString := [
    { pattern := "Old Brand", reason := "Renamed 2026-05; use 'New Brand'." },
    { pattern := "# Backstage", reason := "Backstage content must not ship." }
  ]

  -- Run checks against a precomputed list of (label, content) pairs.
  -- `label` shows up in the error message; `content` is the rendered text
  -- to scan. Sites usually pass `[(slug, renderedHtml)…]`.
  theorem no_forbidden_strings :
      NoGoals.Verify.Strings.allClean myForbidden myRenderedPages = true := by native_decide
  ```
-/

namespace NoGoals.Verify

/-- A pattern that must not appear anywhere in the rendered output, paired
    with a human-readable reason for the rule. The `reason` is reported when
    the check fails so reviewers know why the regression matters. -/
structure ForbiddenString where
  pattern : String
  reason  : String
deriving Repr, DecidableEq

end NoGoals.Verify

namespace NoGoals.Verify.Strings

open NoGoals.Verify

/-- True iff `p` (non-empty) appears as a substring of `s`. Implemented via
    `String.splitOn` — if the pattern is present, splitting on it yields at
    least two parts; if absent, exactly one. The empty pattern is treated as
    not-present (avoids vacuous matches). -/
def hasSubstr (s p : String) : Bool :=
  if p.isEmpty then false
  else (s.splitOn p).length > 1

/-- True iff none of the forbidden patterns appear in `s`. -/
def clean (s : String) (forbidden : List ForbiddenString) : Bool :=
  forbidden.all (fun fb => !hasSubstr s fb.pattern)

/-- A label/content pair: `label` identifies the source (e.g. a slug or file
    path) and `content` is the rendered text to scan. -/
abbrev LabeledContent := String × String

/-- True iff every labeled content string is `clean` against the rule list. -/
def allClean (forbidden : List ForbiddenString) (items : List LabeledContent) : Bool :=
  items.all (fun (_, content) => clean content forbidden)

/-- A single violation report: which item (label) contained which pattern. -/
structure Violation where
  label   : String
  pattern : String
  reason  : String
deriving Repr

/-- Collect every (label, pattern) pair that violates the rules. Empty list
    iff `allClean` is true. Useful for human-readable error reporting. -/
def violations (forbidden : List ForbiddenString) (items : List LabeledContent) : List Violation :=
  items.flatMap fun (label, content) =>
    forbidden.filterMap fun fb =>
      if hasSubstr content fb.pattern then
        some { label, pattern := fb.pattern, reason := fb.reason }
      else none

/-- Pretty-print a list of violations as a multi-line error message. -/
def formatViolations (vs : List Violation) : String :=
  if vs.isEmpty then "✓ no forbidden strings found"
  else
    "✗ forbidden strings detected:\n" ++
    String.intercalate "\n" (vs.map fun v =>
      s!"  • {v.label}: contains \"{v.pattern}\" ({v.reason})")

end NoGoals.Verify.Strings
