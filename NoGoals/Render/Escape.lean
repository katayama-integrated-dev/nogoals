/-
  Charwise HTML escaping, with its correctness theorems.

  Lives in its own module so both the typed HTML tree (`NoGoals.Render.Tree`)
  and the IR renderer (`NoGoals.Render.Html`) can import it without a cycle.
  Names are unchanged (`NoGoals.htmlEscape` etc.) — report anchors resolve as
  before.
-/

import Mathlib.Tactic.SplitIfs

namespace NoGoals

/-- Escape one character. Defined charwise (not via `String.replace` chains)
    so correctness is provable by induction. -/
def htmlEscapeChar (c : Char) : List Char :=
  if c = '&' then ['&', 'a', 'm', 'p', ';']
  else if c = '<' then ['&', 'l', 't', ';']
  else if c = '>' then ['&', 'g', 't', ';']
  else if c = '"' then ['&', 'q', 'u', 'o', 't', ';']
  else if c = '\'' then ['&', '#', 'x', '2', '7', ';']
  else [c]

def htmlEscapeList (cs : List Char) : List Char := cs.flatMap htmlEscapeChar

/-- HTML-escape text content. Escapes `& < > " '` — safe for both element
    text and double/single-quoted attribute values. Correctness is a theorem
    (`htmlEscape_no_specials`), not a promise. -/
def htmlEscape (s : String) : String := String.ofList (htmlEscapeList s.toList)

/-- No output character is `< > " '` — element/attribute injection is
    impossible for escaped content, for ALL inputs. -/
theorem htmlEscapeChar_no_specials (c : Char) :
    ∀ x ∈ htmlEscapeChar c, x ≠ '<' ∧ x ≠ '>' ∧ x ≠ '"' ∧ x ≠ '\'' := by
  intro x hx
  unfold htmlEscapeChar at hx
  split_ifs at hx with h1 h2 h3 h4 h5 <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  · rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
  · rcases hx with rfl | rfl | rfl | rfl <;> decide
  · rcases hx with rfl | rfl | rfl | rfl <;> decide
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · subst hx
    exact ⟨h2, h3, h4, h5⟩

theorem htmlEscapeList_no_specials (cs : List Char) :
    ∀ x ∈ htmlEscapeList cs, x ≠ '<' ∧ x ≠ '>' ∧ x ≠ '"' ∧ x ≠ '\'' := by
  intro x hx
  simp only [htmlEscapeList, List.mem_flatMap] at hx
  obtain ⟨c, _, hmem⟩ := hx
  exact htmlEscapeChar_no_specials c x hmem

/-- The end-to-end escaping theorem: for ANY input string, no character of
    `htmlEscape s` is `< > " '`. -/
theorem htmlEscape_no_specials (s : String) :
    ∀ x ∈ (htmlEscape s).toList, x ≠ '<' ∧ x ≠ '>' ∧ x ≠ '"' ∧ x ≠ '\'' := by
  simpa [htmlEscape, String.toList_ofList] using htmlEscapeList_no_specials s.toList

theorem htmlEscapeList_id_of_clean (cs : List Char)
    (h : ∀ c ∈ cs, c ≠ '&' ∧ c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\'') :
    htmlEscapeList cs = cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    have hc := h c (List.mem_cons_self ..)
    have hrest : ∀ x ∈ rest, x ≠ '&' ∧ x ≠ '<' ∧ x ≠ '>' ∧ x ≠ '"' ∧ x ≠ '\'' :=
      fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [htmlEscapeList, List.flatMap_cons] at *
    rw [ih hrest]
    unfold htmlEscapeChar
    simp [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2]

/-- Escaping is the identity on strings with nothing to escape. -/
theorem htmlEscape_id_of_clean (s : String)
    (h : ∀ c ∈ s.toList, c ≠ '&' ∧ c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\'') :
    htmlEscape s = s := by
  simp only [htmlEscape, htmlEscapeList_id_of_clean s.toList h, String.ofList_toList]

end NoGoals
