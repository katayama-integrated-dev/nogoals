import Mathlib.Data.Rat.Floor

/-!
# Responsive Images with Geometric Ladder

**Status: proof showcase.** This module contains the deepest mathematics in
NoGoals (geometric width ladders, a from-scratch Bernoulli inequality over ℚ,
fuel-bounded invariant proofs). It is consumed by the test suite and the
essay; the production pipeline does not construct srcsets from it yet —
wiring it into hero-image rendering is unified-plan item 4.5. Nothing in the
site's verification report cites these theorems until that lands.

The flagship theorem: prove that srcset selection has bounded waste.

## Theorems

1. **Coverage**: ∀ L,d within bounds, ∃ w ∈ widths, d·L ≤ w
2. **Bounded Waste**: ∀ w* selected, w* < (1+ε)·d·L
3. **Sorted Unique**: widths are in ascending order

These proofs guarantee that:
- Every viewport size has an appropriate image
- Images are never more than (1+ε) times larger than needed

-/

namespace NoGoals

/-! ## Floor Lemmas (proven using Mathlib.Data.Rat.Floor) -/

/-- Floor of non-negative rational is non-negative. -/
theorem Rat.floor_nonneg_of_nonneg (r : Rat) (h : r ≥ 0) : r.floor ≥ 0 :=
  Int.floor_nonneg.mpr h

/-- Floor is monotone: r ≥ s implies floor(r) ≥ floor(s). -/
theorem Rat.floor_mono (r s : Rat) (h : r ≥ s) : r.floor ≥ s.floor :=
  Int.floor_mono h

/-- Floor of a natural number cast to Rat is itself. -/
theorem Rat.floor_natCast (n : Nat) : (n : Rat).floor = n :=
  Int.floor_natCast (R := Rat) n

/-- Nat cast to Rat is non-negative. -/
theorem Rat.natCast_nonneg (n : Nat) : (0 : Rat) ≤ n :=
  Nat.cast_nonneg n

/-- Key derived property: floor(r).natAbs + 1 ≥ n when r ≥ n. -/
theorem floor_natAbs_add_one_ge (r : Rat) (n : Nat) (h : r ≥ n) :
    r.floor.natAbs + 1 ≥ n := by
  have h_floor_ge : r.floor ≥ (n : Rat).floor := Rat.floor_mono r n h
  rw [Rat.floor_natCast] at h_floor_ge
  have h_n_nonneg : (0 : Rat) ≤ n := Rat.natCast_nonneg n
  have h_r_nonneg : (0 : Rat) ≤ r := Rat.le_trans h_n_nonneg h
  have h_nonneg : r.floor ≥ 0 := Rat.floor_nonneg_of_nonneg r h_r_nonneg
  have h_abs : (r.floor.natAbs : Int) = r.floor := Int.natAbs_of_nonneg h_nonneg
  grind

/-! ## Slot Configuration -/

/-- Responsive slot parameters -/
structure SlotResp where
  Lmin    : Nat  -- Minimum layout width (px)
  Lmax    : Nat  -- Maximum layout width (px)
  dmax    : Nat  -- Maximum device pixel ratio
  epsNum  : Nat  -- Epsilon numerator (waste tolerance)
  epsDen  : Nat  -- Epsilon denominator
deriving Repr

/-- Compute epsilon (waste factor) -/
def epsilon (r : SlotResp) : Rat := Rat.divInt r.epsNum r.epsDen

/-! ## Epsilon Properties (Proven) -/

/-- Epsilon is non-negative when built from Nats. -/
theorem epsilon_nonneg (r : SlotResp) : epsilon r ≥ 0 := by
  unfold epsilon
  exact Rat.divInt_nonneg (Int.natCast_nonneg r.epsNum) (Int.natCast_nonneg r.epsDen)

/-- 1 + epsilon is at least 1. -/
theorem one_plus_eps_ge_one (r : SlotResp) : 1 + epsilon r ≥ 1 := by
  have h := epsilon_nonneg r; grind

/-- 1 + epsilon is positive. -/
theorem one_plus_eps_pos (r : SlotResp) : 1 + epsilon r > 0 := by
  have h := one_plus_eps_ge_one r; grind

/-! ## Geometric Ladder -/

/-- Helper for widths generation (lifted for easier reasoning) -/
def widthsGo (r : SlotResp) (acc : List Nat) (cur : Rat) (fuel : Nat) : List Nat :=
  let target : Rat := ↑(r.Lmax * r.dmax)
  if fuel = 0 then acc.reverse
  else if cur ≥ target then
    -- Reached max, add final width and stop
    let w := cur.floor.natAbs + 1
    (w :: acc).reverse
  else
    -- Add current width and continue
    let w := cur.floor.natAbs + 1
    let nxt := cur * (1 + epsilon r)
    widthsGo r (w :: acc) nxt (fuel - 1)
termination_by fuel

/-- Generate widths using geometric progression -/
def widths (r : SlotResp) : List Nat :=
  if r.Lmin = 0 ∨ r.dmax = 0 then
    []
  else
    widthsGo r [] (↑r.Lmin) 1000  -- Max 1000 widths

/-! ## Selection -/

/-- Select smallest width that satisfies target -/
def select (ws : List Nat) (target : Nat) : Option Nat :=
  let candidates := ws.filter (fun w => w ≥ target)
  candidates.head?  -- Assumes widths are sorted ascending

/-- Check if layout width and DPR are within slot bounds -/
def within (r : SlotResp) (L d : Nat) : Prop :=
  r.Lmin ≤ L ∧ L ≤ r.Lmax ∧ 1 ≤ d ∧ d ≤ r.dmax

/-- Valid slot configuration (required for coverage theorem) -/
def validSlot (r : SlotResp) : Prop :=
  0 < r.Lmin ∧ 0 < r.dmax

/-- Slot configuration where geometric series reaches target within 1000 steps.
    This holds for typical responsive image configs (e.g., ε = 0.25, ratio ≤ 18). -/
def validGeometric (r : SlotResp) : Prop :=
  (r.Lmax * r.dmax : Rat) ≤ (r.Lmin : Rat) * (1 + 999 * epsilon r)

/-- Slot configuration where geometric sequence is dense enough for bounded waste.
    Requires Lmin * ε > 1, which ensures the +1 floor error is absorbed.
    For ε = 0.25, this means Lmin > 4 (always true for web images with Lmin ≥ 320). -/
def validDensity (r : SlotResp) : Prop :=
  (r.Lmin : Rat) * epsilon r > 1

/-- Epsilon is positive when density condition holds. -/
theorem epsilon_pos_of_density (r : SlotResp) (h_valid : validSlot r) (h_dense : validDensity r) :
    epsilon r > 0 := by
  unfold validDensity at h_dense
  have h_lmin_pos : (r.Lmin : Rat) > 0 := by exact_mod_cast h_valid.1
  by_contra h_neg; push_neg at h_neg
  have : (r.Lmin : Rat) * epsilon r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt h_lmin_pos) h_neg
  grind

/-! ## Geometric Progression Theorems -/

/-- Bernoulli's inequality: (1+ε)^k ≥ 1 + k*ε for ε ≥ 0.
    This is the key tool for bounding geometric progressions. -/
theorem bernoulli (ε : Rat) (hε : ε ≥ 0) (k : Nat) : (1 + ε) ^ k ≥ 1 + k * ε := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hpos : 1 + ε ≥ 0 := by grind
    have h3 : (1 + ε) ^ n * (1 + ε) ≥ (1 + n * ε) * (1 + ε) := by
      have := mul_le_mul_of_nonneg_right ih hpos
      grind
    have h5 : (n : Rat) * ε * ε ≥ 0 := by
      have hn : (n : Rat) ≥ 0 := Nat.cast_nonneg n
      have hne : (n : Rat) * ε ≥ 0 := mul_nonneg hn hε
      exact mul_nonneg hne hε
    calc (1 + ε) ^ (n + 1)
        = (1 + ε) ^ n * (1 + ε) := by ring
      _ ≥ (1 + n * ε) * (1 + ε) := h3
      _ = 1 + (n + 1) * ε + n * ε * ε := by ring
      _ ≥ 1 + (n + 1) * ε := by grind
      _ = 1 + ((n : Rat) + 1) * ε := by ring
      _ = 1 + (↑(n + 1) : Rat) * ε := by norm_cast

/-- Geometric bound: Lmin * (1+ε)^k ≥ Lmin * (1 + k*ε) by Bernoulli. -/
theorem geometric_bound (r : SlotResp) (k : Nat) :
    (r.Lmin : Rat) * (1 + epsilon r) ^ k ≥ (r.Lmin : Rat) * (1 + k * epsilon r) := by
  have heps := epsilon_nonneg r
  have hbern := bernoulli (epsilon r) heps k
  have hlmin : (r.Lmin : Rat) ≥ 0 := Nat.cast_nonneg r.Lmin
  exact mul_le_mul_of_nonneg_left hbern hlmin

/-- Key lemma: widthsGo with fuel > 0 and cur ≥ target produces an element ≥ target -/
theorem widthsGo_has_large (r : SlotResp) (acc : List Nat) (cur : Rat) (fuel : Nat)
    (h_fuel : fuel > 0) (h_cur_ge : cur ≥ (r.Lmax * r.dmax : Nat)) :
    ∃ w ∈ widthsGo r acc cur fuel, w ≥ r.Lmax * r.dmax := by
  cases fuel with
  | zero => grind
  | succ n =>
    unfold widthsGo
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    -- cur ≥ target case: we know cur ≥ target so the first branch is taken
    have h_target : cur ≥ (↑(r.Lmax * r.dmax) : Rat) := h_cur_ge
    simp only [h_target, ↓reduceIte]
    -- We add w = floor(cur) + 1 and return (w :: acc).reverse
    refine ⟨cur.floor.natAbs + 1, ?_, ?_⟩
    · -- membership in reversed list
      simp only [List.mem_reverse, List.mem_cons, true_or]
    · -- w ≥ Lmax * dmax - use our derived floor lemma
      exact floor_natAbs_add_one_ge cur (r.Lmax * r.dmax) h_cur_ge

/-- The geometric ladder with factor (1+ε) eventually reaches any target from any start.
    Mathematically: for ε ≥ 0 and ratio bounded by 1 + 999ε, k = 999 works.
    For typical configs (ε = 0.25, ratio ≤ 18), this is easily satisfied. -/
theorem geometric_reaches_target (r : SlotResp) (h_geom : validGeometric r) :
    ∃ k < 1000, (r.Lmin : Rat) * (1 + epsilon r) ^ k ≥ r.Lmax * r.dmax := by
  use 999
  constructor
  · grind
  · calc (r.Lmin : Rat) * (1 + epsilon r) ^ 999
        ≥ (r.Lmin : Rat) * (1 + 999 * epsilon r) := geometric_bound r 999
      _ ≥ (r.Lmax * r.dmax : Rat) := by unfold validGeometric at h_geom; grind
      _ = ↑r.Lmax * ↑r.dmax := by norm_cast

/-- Key induction lemma: if geometric progression reaches target within fuel steps,
    then widthsGo produces a large element. Uses strong induction on k.
    Note: h_eps_nonneg is not used in the induction but kept for clarity. -/
theorem widthsGo_reaches_target (r : SlotResp) (cur : Rat) (fuel k : Nat)
    (h_fuel : k < fuel)
    (h_cur_pos : cur > 0)
    (_h_eps_nonneg : epsilon r ≥ 0)
    (h_reaches : cur * (1 + epsilon r) ^ k ≥ (r.Lmax : Rat) * (r.dmax : Rat)) :
    ∀ acc, ∃ w ∈ widthsGo r acc cur fuel, w ≥ r.Lmax * r.dmax := by
  induction k generalizing cur fuel with
  | zero =>
    intro acc
    simp at h_reaches
    have h_fuel_pos : fuel > 0 := by grind
    exact widthsGo_has_large r acc cur fuel h_fuel_pos
      (by simp only [Nat.cast_mul]; exact h_reaches)
  | succ k' ih =>
    intro acc
    cases fuel with
    | zero => grind
    | succ n =>
      unfold widthsGo
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      by_cases h_cur_target : cur ≥ ↑(r.Lmax * r.dmax)
      · -- Already at target
        simp only [h_cur_target, ↓reduceIte]
        refine ⟨cur.floor.natAbs + 1, ?_, ?_⟩
        · grind
        · exact floor_natAbs_add_one_ge cur (r.Lmax * r.dmax) h_cur_target
      · -- Not at target, recurse
        simp only [h_cur_target, ↓reduceIte]
        have h_k'_lt : k' < n := by grind
        have h_cur'_pos : cur * (1 + epsilon r) > 0 := mul_pos h_cur_pos (one_plus_eps_pos r)
        have h_reaches' : (cur * (1 + epsilon r)) * (1 + epsilon r) ^ k' ≥
            (r.Lmax : Rat) * (r.dmax : Rat) := by
          have h_eq : cur * (1 + epsilon r) ^ (k' + 1) =
              cur * (1 + epsilon r) * (1 + epsilon r) ^ k' := by rw [pow_succ]; ring
          rw [← h_eq]; exact h_reaches
        exact ih (cur * (1 + epsilon r)) n h_k'_lt h_cur'_pos h_reaches' ((cur.floor.natAbs + 1) :: acc)

/-- widthsGo from Lmin with fuel=1000 produces an element ≥ Lmax * dmax.
    This follows from: geometric_reaches_target provides k < 1000 such that
    Lmin * (1+ε)^k ≥ target, and widthsGo_reaches_target completes the proof. -/
theorem widthsGo_produces_large (r : SlotResp) (h_valid : validSlot r) (h_geom : validGeometric r) :
    ∃ w ∈ widthsGo r [] (↑r.Lmin) 1000, w ≥ r.Lmax * r.dmax := by
  obtain ⟨k, hk_lt, hk_ge⟩ := geometric_reaches_target r h_geom
  have h_lmin_pos : (r.Lmin : Rat) > 0 := by simp only [Nat.cast_pos]; exact h_valid.1
  have h_eps_nonneg := epsilon_nonneg r
  exact widthsGo_reaches_target r (↑r.Lmin) 1000 k hk_lt h_lmin_pos h_eps_nonneg hk_ge []

/-- Accumulator invariant: elements are in descending order (largest at head). -/
def accDescending (acc : List Nat) : Prop :=
  acc.Pairwise (· ≥ ·)

/-- Scaling by (1 + epsilon) is non-decreasing for non-negative cur -/
theorem cur_le_cur_mul_eps (r : SlotResp) (cur : Rat) (h_cur_nonneg : cur ≥ 0) :
    cur ≤ cur * (1 + epsilon r) := by
  have h_eps := one_plus_eps_ge_one r
  calc cur = cur * 1 := by ring
    _ ≤ cur * (1 + epsilon r) := mul_le_mul_of_nonneg_left h_eps h_cur_nonneg

/-- Helper: floor is monotone in Rat for non-negative inputs -/
theorem floor_mono_nat (r s : Rat) (hr : r ≥ 0) (h : r ≤ s) : r.floor.natAbs ≤ s.floor.natAbs := by
  have hr_floor : r.floor ≥ 0 := Int.floor_nonneg.mpr hr
  have hs_floor : s.floor ≥ 0 := Int.floor_nonneg.mpr (le_trans hr h)
  have hr_abs : (r.floor.natAbs : Int) = r.floor := Int.natAbs_of_nonneg hr_floor
  have hs_abs : (s.floor.natAbs : Int) = s.floor := Int.natAbs_of_nonneg hs_floor
  have h1 : r.floor ≤ s.floor := Int.floor_mono h
  grind

/-- Helper: prepending a larger element to a descending list preserves descending order -/
theorem cons_descending (w : Nat) (acc : List Nat) (h_acc : accDescending acc)
    (h_ge : ∀ x ∈ acc, w ≥ x) : accDescending (w :: acc) := by
  unfold accDescending at *
  rw [List.pairwise_cons]
  exact ⟨h_ge, h_acc⟩

/-- Helper: widthsGo preserves descending order of accumulator -/
theorem widthsGo_descending (r : SlotResp) (acc : List Nat) (cur : Rat) (fuel : Nat)
    (h_cur_pos : cur > 0) (h_acc_desc : accDescending acc)
    (h_acc_bound : ∀ x ∈ acc, cur.floor.natAbs + 1 ≥ x) :
    accDescending (widthsGo r acc cur fuel).reverse := by
  induction fuel generalizing acc cur with
  | zero =>
    unfold widthsGo
    simp only [↓reduceIte, List.reverse_reverse]
    exact h_acc_desc
  | succ n ih =>
    unfold widthsGo
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    split
    · -- cur ≥ target: terminal case
      simp only [List.reverse_reverse]
      exact cons_descending _ acc h_acc_desc h_acc_bound
    · -- cur < target: recursive case
      rename_i h_not_target
      apply ih
      · -- cur * (1 + epsilon r) > 0
        have h_eps := one_plus_eps_pos r
        exact mul_pos h_cur_pos h_eps
      · -- (w :: acc) is descending
        exact cons_descending _ acc h_acc_desc h_acc_bound
      · -- All elements in (w :: acc) are ≤ new width
        intro x hx
        have h_cur_nonneg : cur ≥ 0 := le_of_lt h_cur_pos
        have h_mono := cur_le_cur_mul_eps r cur h_cur_nonneg
        have h_floor := floor_mono_nat cur (cur * (1 + epsilon r)) h_cur_nonneg h_mono
        rw [List.mem_cons] at hx
        cases hx with
        | inl h_eq => subst h_eq; grind
        | inr h_mem => have h_old := h_acc_bound x h_mem; grind

/-- Widths list is sorted - consecutive widths are in non-decreasing order.
    Proof: widthsGo builds a descending accumulator, reverse makes it ascending. -/
theorem widths_sorted (r : SlotResp) : (widths r).Pairwise (· ≤ ·) := by
  unfold widths
  split
  · exact List.Pairwise.nil
  · -- Show widthsGo produces a descending list when reversed
    rename_i h_valid
    push_neg at h_valid
    have h_lmin_pos : (r.Lmin : Rat) > 0 := by simp only [Nat.cast_pos]; exact Nat.pos_of_ne_zero h_valid.1
    have h_desc := widthsGo_descending r [] (↑r.Lmin) 1000
      h_lmin_pos
      (by unfold accDescending; exact List.Pairwise.nil)
      (by simp)
    -- accDescending l.reverse means l is ascending
    unfold accDescending at h_desc
    -- Convert Pairwise (· ≥ ·) on reverse to Pairwise (· ≤ ·) on original
    rw [List.pairwise_reverse] at h_desc
    simp only [ge_iff_le] at h_desc
    exact h_desc

/-! ## Helper lemmas for select_bounded -/

/-- Width computed at a given cur value (same as in widthsGo) -/
private def widthAt (cur : Rat) : Nat := cur.floor.natAbs + 1

/-- widthAt upper bound: widthAt(cur) ≤ cur + 1 -/
private theorem widthAt_le (cur : Rat) (h : cur ≥ 0) : (widthAt cur : Rat) ≤ cur + 1 := by
  unfold widthAt
  have h_floor_nonneg : cur.floor ≥ 0 := Int.floor_nonneg.mpr h
  have h_floor_le : (cur.floor : Rat) ≤ cur := Int.floor_le cur
  have h_eq : (cur.floor.natAbs : Rat) = cur.floor := by
    simp only [Nat.cast_natAbs, abs_of_nonneg h_floor_nonneg]
  calc ((cur.floor.natAbs + 1 : Nat) : Rat)
      = (cur.floor.natAbs : Rat) + 1 := by norm_cast
    _ = cur.floor + 1 := by rw [h_eq]
    _ ≤ cur + 1 := by grind

/-- widthAt lower bound: widthAt(cur) > cur -/
private theorem widthAt_gt (cur : Rat) (h : cur ≥ 0) : (widthAt cur : Rat) > cur := by
  unfold widthAt
  have h_floor_nonneg : cur.floor ≥ 0 := Int.floor_nonneg.mpr h
  have h_eq : (cur.floor.natAbs : Rat) = cur.floor := by
    simp only [Nat.cast_natAbs, abs_of_nonneg h_floor_nonneg]
  have h_lt : cur < cur.floor + 1 := Int.lt_floor_add_one cur
  calc cur
      < cur.floor + 1 := h_lt
    _ = (cur.floor.natAbs : Rat) + 1 := by rw [h_eq]
    _ = ((cur.floor.natAbs + 1 : Nat) : Rat) := by norm_cast

/-- Cast subtraction for positive Nat -/
private theorem nat_sub_one_cast (n : Nat) (h : n > 0) : ((n - 1 : Nat) : Rat) = (n : Rat) - 1 := by
  cases n with
  | zero => grind
  | succ m => simp

/-- Key lemma: consecutive widths from geometric progression satisfy the bound.
    If prev_w = widthAt(cur) < target and next_w = widthAt(cur * (1+ε)) ≥ target,
    then next_w < target * (1+ε). -/
theorem consecutive_bound (cur : Rat) (target : Nat) (ε : Rat)
    (h_cur_pos : cur > 0) (h_eps_pos : ε > 0)
    (h_target_pos : target > 0)
    (h_prev_lt : widthAt cur < target) :
    (widthAt (cur * (1 + ε)) : Rat) < (target : Rat) * (1 + ε) := by
  have h_ratio_pos : 1 + ε > 0 := by grind
  have h_cur_nonneg : cur ≥ 0 := le_of_lt h_cur_pos
  -- Step 1: prev_w ≤ target - 1 (Nat inequality: a < b implies a ≤ b - 1)
  have h_prev_le : widthAt cur ≤ target - 1 := by grind
  -- Step 2: cur < prev_w
  have h_cur_lt_prev : cur < widthAt cur := widthAt_gt cur h_cur_nonneg
  -- Step 3: cur < target - 1
  have h_cur_lt_target_minus : cur < (target : Rat) - 1 := by
    have h1 : (widthAt cur : Rat) ≤ (target - 1 : Nat) := by exact_mod_cast h_prev_le
    have h2 : ((target - 1 : Nat) : Rat) = (target : Rat) - 1 := nat_sub_one_cast target h_target_pos
    calc cur < widthAt cur := h_cur_lt_prev
      _ ≤ (target - 1 : Nat) := h1
      _ = (target : Rat) - 1 := h2
  -- Step 4: next_w ≤ cur * (1+ε) + 1
  have h_next_le : (widthAt (cur * (1 + ε)) : Rat) ≤ cur * (1 + ε) + 1 := by
    apply widthAt_le
    apply mul_nonneg h_cur_nonneg
    grind
  -- Step 5: Combine to get next_w < (target - 1) * (1+ε) + 1 = target * (1+ε) - ε
  calc (widthAt (cur * (1 + ε)) : Rat)
      ≤ cur * (1 + ε) + 1 := h_next_le
    _ < ((target : Rat) - 1) * (1 + ε) + 1 := by
        have h := mul_lt_mul_of_pos_right h_cur_lt_target_minus h_ratio_pos
        grind
    _ = (target : Rat) * (1 + ε) - ε := by ring
    _ < (target : Rat) * (1 + ε) := by grind

/-- First width case: when first width is selected, need density condition.
    First width = Lmin + 1. For w < (1+ε) * target with w ≥ target,
    we need Lmin + 1 < (1+ε) * target, which holds when target ≥ Lmin and Lmin * ε > 1. -/
theorem first_width_bound (r : SlotResp) (target : Nat)
    (_h_valid : validSlot r) (h_dense : validDensity r)
    (h_target_ge : target ≥ r.Lmin) :
    (r.Lmin + 1 : Rat) < (1 + epsilon r) * (target : Rat) := by
  unfold validDensity at h_dense
  have h_target_ge_rat : (target : Rat) ≥ r.Lmin := by exact_mod_cast h_target_ge
  calc (r.Lmin + 1 : Rat)
      = r.Lmin + 1 := by norm_cast
    _ < r.Lmin + r.Lmin * epsilon r := by grind
    _ = r.Lmin * (1 + epsilon r) := by ring
    _ ≤ (target : Rat) * (1 + epsilon r) := by
        apply mul_le_mul_of_nonneg_right h_target_ge_rat
        have := epsilon_nonneg r
        grind
    _ = (1 + epsilon r) * (target : Rat) := by ring

/-! ## Helper lemmas for select_bounded proof -/

private theorem getElem?_some_lt {α : Type*} (l : List α) (i : Nat) (x : α)
    (h : l[i]? = some x) : i < l.length := by
  by_contra h_ge; simp only [not_lt] at h_ge
  rw [List.getElem?_eq_none_iff.mpr h_ge] at h
  exact nomatch h

private theorem getElem?_some_of_lt {α : Type*} (l : List α) (i : Nat)
    (h : i < l.length) : ∃ x, l[i]? = some x := by
  exact ⟨l[i], List.getElem?_eq_getElem h⟩

/-! ## Proof of widthsGo_geometric

    This theorem proves that widthsGo produces a geometric sequence.
    The element at index i equals floor(cur * (1+ε)^i) + 1.

    The proof uses an accumulator invariant (GeoInv) that tracks how each
    element relates to the starting cur value and its position in the sequence. -/

/-- Accumulator invariant: tracks geometric relationship -/
private def GeoInv (r : SlotResp) (acc : List Nat) (start cur : Rat) : Prop :=
  cur = start * (1 + epsilon r) ^ acc.length ∧
  ∀ j : Nat, j < acc.length → acc[j]? = some (widthAt (start * (1 + epsilon r) ^ (acc.length - 1 - j)))

/-- Result of widthsGo when fuel = 0 -/
private theorem widthsGo_zero (r : SlotResp) (acc : List Nat) (cur : Rat) :
    widthsGo r acc cur 0 = acc.reverse := by
  unfold widthsGo; simp only [↓reduceIte]

/-- Helper: extract element from reversed acc using GeoInv -/
private theorem geoInv_reverse_elem (r : SlotResp) (acc : List Nat) (start cur : Rat)
    (h_inv : GeoInv r acc start cur) (i : Nat) (hi : i < acc.length) :
    acc.reverse[i]? = some (widthAt (start * (1 + epsilon r) ^ i)) := by
  have h_rev := List.getElem?_reverse (l := acc) hi
  rw [h_rev]
  obtain ⟨_, h_acc⟩ := h_inv
  have h_idx : acc.length - 1 - i < acc.length := by grind
  have h_from_acc := h_acc (acc.length - 1 - i) h_idx
  have h_simp : acc.length - 1 - (acc.length - 1 - i) = i := by grind
  rw [h_simp] at h_from_acc
  exact h_from_acc

/-- Key lemma: The final result satisfies the geometric property -/
private theorem widthsGo_geo_from_inv (r : SlotResp) (acc : List Nat) (start cur : Rat) (fuel : Nat)
    (h_inv : GeoInv r acc start cur) :
    ∀ i : Nat, i < (widthsGo r acc cur fuel).length →
      (widthsGo r acc cur fuel)[i]? = some (widthAt (start * (1 + epsilon r) ^ i)) := by
  induction fuel generalizing acc cur with
  | zero =>
    intro i hi
    rw [widthsGo_zero] at hi ⊢
    simp only [List.length_reverse] at hi
    exact geoInv_reverse_elem r acc start cur h_inv i hi
  | succ n ih =>
    intro i hi
    unfold widthsGo at hi ⊢
    simp only [Nat.succ_ne_zero, ↓reduceIte] at hi ⊢
    split_ifs at hi ⊢ with hge
    · -- Terminal case: cur ≥ target, result is (widthAt cur :: acc).reverse
      rw [List.reverse_cons] at hi ⊢
      simp only [List.length_append, List.length_reverse, List.length_singleton] at hi
      by_cases hi_old : i < acc.length
      · -- i indexes into acc.reverse part
        rw [List.getElem?_append_left (by simp only [List.length_reverse]; exact hi_old)]
        exact geoInv_reverse_elem r acc start cur h_inv i hi_old
      · -- i = acc.length (the new element at the end)
        have hi_eq : i = acc.length := by grind
        subst hi_eq
        rw [List.getElem?_append_right (by simp only [List.length_reverse]; grind)]
        simp only [List.length_reverse, Nat.sub_self, List.getElem?_cons_zero]
        obtain ⟨h_cur_eq, _⟩ := h_inv
        unfold widthAt; congr 1; rw [h_cur_eq]
    · -- Recursive case: widthsGo r (widthAt cur :: acc) (cur * (1+ε)) n
      have h_inv' : GeoInv r (widthAt cur :: acc) start (cur * (1 + epsilon r)) := by
        obtain ⟨h_cur_eq, h_acc⟩ := h_inv
        constructor
        · simp only [List.length_cons]; rw [h_cur_eq]; ring_nf
        · intro j hj
          simp only [List.length_cons] at hj
          match j with
          | 0 =>
            simp only [List.getElem?_cons_zero, List.length_cons]
            have h_exp_eq : (acc.length + 1) - 1 - 0 = acc.length := by grind
            rw [h_exp_eq, ← h_cur_eq]
          | j' + 1 =>
            simp only [List.getElem?_cons_succ, List.length_cons]
            have hj' : j' < acc.length := by grind
            have h_from_acc := h_acc j' hj'
            have h_exp_eq : (acc.length + 1) - 1 - (j' + 1) = acc.length - 1 - j' := by grind
            rw [h_exp_eq]; exact h_from_acc
      exact ih (widthAt cur :: acc) (cur * (1 + epsilon r)) h_inv' i hi

/-- The widthsGo function produces a geometric sequence -/
theorem widthsGo_geometric (r : SlotResp) (cur : Rat) (fuel i : Nat)
    (_h_cur_pos : cur > 0)
    (h_i : i < (widthsGo r [] cur fuel).length) :
    (widthsGo r [] cur fuel)[i]? = some ((cur * (1 + epsilon r) ^ i).floor.natAbs + 1) := by
  have h_inv : GeoInv r [] cur cur := by
    constructor
    · simp only [List.length_nil, pow_zero, mul_one]
    · intro j hj; simp only [List.length_nil] at hj; grind
  have := widthsGo_geo_from_inv r [] cur cur fuel h_inv i h_i
  unfold widthAt at this
  exact this

/-- Helper: validSlot implies widths = widthsGo r [] r.Lmin 1000 -/
private theorem validSlot_widths_eq (r : SlotResp) (h_valid : validSlot r) :
    widths r = widthsGo r [] r.Lmin 1000 := by
  unfold widths
  have h : ¬(r.Lmin = 0 ∨ r.dmax = 0) := by
    push_neg; exact ⟨Nat.pos_iff_ne_zero.mp h_valid.1, Nat.pos_iff_ne_zero.mp h_valid.2⟩
  simp only [h, ↓reduceIte]

/-- Helper: Lmin cast to Rat is positive for valid slots -/
private theorem validSlot_Lmin_pos (r : SlotResp) (h_valid : validSlot r) :
    (r.Lmin : Rat) > 0 := by exact_mod_cast h_valid.1

/-- First element of widths list is Lmin + 1 -/
private theorem widths_first_elem (r : SlotResp) (h_valid : validSlot r)
    (h_nonempty : 0 < (widths r).length) :
    (widths r)[0]? = some (r.Lmin + 1) := by
  rw [validSlot_widths_eq r h_valid] at h_nonempty ⊢
  have h0 := widthsGo_geometric r r.Lmin 1000 0 (validSlot_Lmin_pos r h_valid) h_nonempty
  simp only [pow_zero, mul_one] at h0
  exact h0

/-- Consecutive widths come from geometric sequence -/
private theorem widths_consecutive (r : SlotResp) (h_valid : validSlot r) (i : Nat) (v w : Nat)
    (h_v : (widths r)[i]? = some v)
    (h_w : (widths r)[i + 1]? = some w) :
    ∃ cur : Rat, cur > 0 ∧
      v = cur.floor.natAbs + 1 ∧
      w = (cur * (1 + epsilon r)).floor.natAbs + 1 := by
  rw [validSlot_widths_eq r h_valid] at h_v h_w
  have h_cur_pos := validSlot_Lmin_pos r h_valid
  have h_len_v := getElem?_some_lt _ _ _ h_v
  have h_len_w := getElem?_some_lt _ _ _ h_w
  have hv' := widthsGo_geometric r r.Lmin 1000 i h_cur_pos h_len_v
  have hw' := widthsGo_geometric r r.Lmin 1000 (i + 1) h_cur_pos h_len_w
  rw [hv'] at h_v; rw [hw'] at h_w
  simp only [Option.some.injEq] at h_v h_w
  use r.Lmin * (1 + epsilon r) ^ i
  refine ⟨mul_pos h_cur_pos (pow_pos (one_plus_eps_pos r) i), h_v.symm, ?_⟩
  rw [← h_w]; ring_nf

/-- Find first position ≥ target in sorted list -/
private theorem exists_first_ge (l : List Nat) (target w : Nat)
    (h_sorted : l.Pairwise (· ≤ ·))
    (h_head : (l.filter (· ≥ target)).head? = some w) :
    ∃ k, l[k]? = some w ∧ (∀ j : Nat, j < k → ∀ v : Nat, l[j]? = some v → v < target) := by
  induction l with
  | nil => simp at h_head
  | cons a as ih =>
    simp only [List.filter_cons] at h_head
    by_cases ha : a ≥ target
    · simp only [ha, decide_true, ↓reduceIte, List.head?_cons, Option.some.injEq] at h_head
      use 0
      simp only [List.getElem?_cons_zero, h_head, true_and]
      intro j hj; grind
    · simp only [ha, decide_false, Bool.false_eq_true, ↓reduceIte] at h_head
      have h_sorted' : as.Pairwise (· ≤ ·) := List.Pairwise.tail h_sorted
      obtain ⟨k, hk, hk_prev⟩ := ih h_sorted' h_head
      use k + 1
      simp only [List.getElem?_cons_succ, hk, true_and]
      intro j hj v hv
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
        rw [← hv]
        grind
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hv
        exact hk_prev j' (by grind) v hv

/-- Select returns a width bounded by (1+ε) times the target.
    Requires validDensity to ensure the geometric sequence is dense enough
    to absorb the floor rounding error (+1).

    **Proof**:
    1. widthsGo produces widths w_i where w_i = floor(cur * (1+ε)^i) + 1
    2. Consecutive widths satisfy: if w_i < target ≤ w_{i+1}, then w_{i+1} < target * (1+ε)
    3. For the first width (i=0), validDensity ensures Lmin + 1 < (1+ε) * target -/
theorem select_bounded (r : SlotResp) (target : Nat)
    (h_valid : validSlot r) (h_dense : validDensity r) (h_target_pos : target > 0)
    (h_target_ge : target ≥ r.Lmin) :
    ∀ w, select (widths r) target = some w →
      (w : Rat) < (1 + epsilon r) * (target : Rat) := by
  intro w h_sel

  have h_sorted := widths_sorted r
  have h_head : ((widths r).filter (· ≥ target)).head? = some w := by
    unfold select at h_sel; exact h_sel

  obtain ⟨k, hk, hk_prev⟩ := exists_first_ge (widths r) target w h_sorted h_head

  have h_nonempty : 0 < (widths r).length := by
    have := getElem?_some_lt (widths r) k w hk
    grind

  by_cases hk0 : k = 0
  · -- w is first element
    subst hk0
    have h_first := widths_first_elem r h_valid h_nonempty
    rw [h_first] at hk
    simp only [Option.some.injEq] at hk
    rw [← hk]
    have := first_width_bound r target h_valid h_dense h_target_ge
    simp only [Nat.cast_add, Nat.cast_one]
    exact this

  · -- w has predecessor
    have h_k_pos : k > 0 := Nat.pos_of_ne_zero hk0
    have h_pred_idx : k - 1 < (widths r).length := by
      have := getElem?_some_lt (widths r) k w hk
      grind
    obtain ⟨v, hv⟩ := getElem?_some_of_lt (widths r) (k - 1) h_pred_idx

    have h_v_lt : v < target := hk_prev (k - 1) (by grind) v hv

    have h_succ : k - 1 + 1 = k := by grind
    rw [← h_succ] at hk
    obtain ⟨cur, h_cur_pos, hv_eq, hw_eq⟩ := widths_consecutive r h_valid (k - 1) v w hv hk

    have h_v_lt' : cur.floor.natAbs + 1 < target := by rw [← hv_eq]; exact h_v_lt
    have h_eps_pos := epsilon_pos_of_density r h_valid h_dense
    have h_bound := consecutive_bound cur target (epsilon r) h_cur_pos h_eps_pos h_target_pos h_v_lt'

    rw [hw_eq]
    calc (((cur * (1 + epsilon r)).floor.natAbs + 1 : Nat) : Rat)
        < (target : Rat) * (1 + epsilon r) := h_bound
      _ = (1 + epsilon r) * (target : Rat) := by ring

/-! ## Flagship Theorems -/

/-- Coverage: For any viewport in a valid slot, there exists a suitable width.
    Requires validGeometric to ensure the geometric series reaches the target. -/
theorem widths_cover (r : SlotResp) (L d : Nat)
    (h_valid : validSlot r) (h_geom : validGeometric r) (h : within r L d) :
    ∃ w, w ∈ widths r ∧ d * L ≤ w := by
  -- Strategy: Show widthsGo produces a final width ≥ Lmax * dmax
  -- Since L ≤ Lmax and d ≤ dmax, we have d * L ≤ Lmax * dmax
  unfold validSlot at h_valid
  obtain ⟨h_lmin_pos, h_dmax_pos⟩ := h_valid
  unfold within at h
  obtain ⟨h_lmin, h_lmax, h_d1, h_dmax⟩ := h
  unfold widths
  split
  · -- Invalid case: contradicts h_valid
    rename_i h_invalid
    rcases h_invalid with h0 | h0 <;> grind
  · -- Valid case: use widthsGo_produces_large
    have h_large := widthsGo_produces_large r ⟨h_lmin_pos, h_dmax_pos⟩ h_geom
    obtain ⟨w, hw_mem, hw_ge⟩ := h_large
    have h_bound : d * L ≤ r.Lmax * r.dmax := by
      have h1 := Nat.mul_le_mul_right L h_dmax
      have h2 := Nat.mul_le_mul_left r.dmax h_lmax
      have h3 := Nat.mul_comm r.dmax r.Lmax
      grind
    exact ⟨w, hw_mem, Nat.le_trans h_bound hw_ge⟩

/-- Bounded Waste: Selected width is at most (1+ε) times larger than needed.
    Requires validDensity (Lmin * ε > 1) to ensure geometric sequence is dense enough. -/
theorem widths_waste (r : SlotResp) (L d : Nat)
    (h_valid : validSlot r) (h_dense : validDensity r) (h_within : within r L d) :
    ∀ w_star, select (widths r) (d * L) = some w_star →
      (w_star : Rat) < (1 + epsilon r) * ((d : Rat) * (L : Rat)) := by
  intro w_star h_select
  -- Extract bounds from within
  unfold within at h_within
  obtain ⟨h_lmin, _, h_d1, _⟩ := h_within
  -- Target = d * L ≥ 1 * Lmin = Lmin
  have h_target_ge : d * L ≥ r.Lmin := by
    calc d * L ≥ 1 * L := Nat.mul_le_mul_right L h_d1
      _ = L := Nat.one_mul L
      _ ≥ r.Lmin := h_lmin
  -- Target > 0 since d ≥ 1 and L ≥ Lmin > 0
  have h_target_pos : d * L > 0 := by
    have h_L_pos : L > 0 := Nat.lt_of_lt_of_le h_valid.1 h_lmin
    exact Nat.mul_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one h_d1) h_L_pos
  have h := select_bounded r (d * L) h_valid h_dense h_target_pos h_target_ge w_star h_select
  -- Convert ↑(d * L) to ↑d * ↑L
  simp only [show ((d * L : Nat) : Rat) = (d : Rat) * (L : Rat) from by norm_cast] at h
  exact h

/-! ## Auxiliary Properties -/

/-- Helper: reversed cons list is non-empty -/
private theorem cons_reverse_ne_nil {α : Type*} (x : α) (xs : List α) :
    (x :: xs).reverse ≠ [] := by
  intro h; rw [List.reverse_eq_nil_iff] at h; exact List.cons_ne_nil _ _ h

/-- widthsGo with non-empty acc produces non-empty result -/
theorem widthsGo_acc_nonempty (r : SlotResp) (acc : List Nat) (cur : Rat) (fuel : Nat)
    (h_acc : acc ≠ []) : widthsGo r acc cur fuel ≠ [] := by
  induction fuel generalizing acc cur with
  | zero =>
    unfold widthsGo; simp only [↓reduceIte]
    exact List.reverse_ne_nil_iff.mpr h_acc
  | succ n ih =>
    unfold widthsGo; simp only [Nat.succ_ne_zero, ↓reduceIte]
    split
    · exact cons_reverse_ne_nil _ _
    · exact ih _ _ (List.cons_ne_nil _ _)

/-- widthsGo starting with empty acc and fuel > 0 produces non-empty result -/
theorem widthsGo_nonempty (r : SlotResp) (cur : Rat) (fuel : Nat) (h : fuel > 0) :
    widthsGo r [] cur fuel ≠ [] := by
  cases fuel with
  | zero => exact absurd rfl (Nat.ne_zero_of_lt h)
  | succ n =>
    unfold widthsGo; simp only [Nat.succ_ne_zero, ↓reduceIte]
    split
    · exact cons_reverse_ne_nil _ _
    · exact widthsGo_acc_nonempty r _ _ n (List.cons_ne_nil _ _)

/-- Widths are non-empty for valid slots -/
theorem widths_nonempty (r : SlotResp)
    (h_lmin : 0 < r.Lmin)
    (h_dmax : 0 < r.dmax) :
    widths r ≠ [] := by
  unfold widths
  split
  · -- Case Lmin = 0 or dmax = 0
    rename_i h
    rcases h with h1 | h2
    · rw [h1] at h_lmin; contradiction
    · rw [h2] at h_dmax; contradiction
  · -- Case valid: widthsGo r [] (↑r.Lmin) 1000
    exact widthsGo_nonempty r (↑r.Lmin) 1000 (by decide)

/-! ## Srcset Generation -/

/-- Generate srcset attribute string -/
def renderSrcset (baseUrl : String) (ws : List Nat) : String :=
  String.intercalate ", " <|
    ws.map fun w => s!"{baseUrl}-{w}w.jpg {w}w"

/-- Example slot configuration -/
def exampleSlot : SlotResp :=
  { Lmin := 320      -- Min: mobile
    Lmax := 1920     -- Max: desktop
    dmax := 3        -- Up to 3x displays (Retina)
    epsNum := 25     -- 25% waste tolerance
    epsDen := 100 }

-- Example widths computation: geometric series from 320 to 5760 (1920*3)
-- Run with: #eval! widths exampleSlot

/-! ## Integration with Site -/

/-- Generate responsive image HTML -/
def responsiveImg (slot : SlotResp) (src : String) (alt : String) : String :=
  let ws := widths slot
  let srcset := renderSrcset src ws
  s!"<img src=\"{src}-{slot.Lmin}w.jpg\" srcset=\"{srcset}\" sizes=\"100vw\" alt=\"{alt}\">"

end NoGoals
