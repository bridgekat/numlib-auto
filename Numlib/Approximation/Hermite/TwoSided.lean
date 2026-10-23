import Numlib.Approximation.Hermite.Global

/-!
# Polynomial intervals with two Taylor continuations

A polynomial on a finite nonnegative interval is continued on each side by
its actual endpoint Taylor polynomial. Matching jets give genuine finite
smoothness. Flat right jets yield bounded derivatives on the positive half-line.
-/

open Polynomial Set
namespace Hermite

/-- A polynomial interval with its actual order-p Taylor continuations on both sides. -/
noncomputable def twoSidedTaylor (p : ℕ) (Q : ℝ[X]) (s : ℝ) : ℝ → ℝ :=
  extendRight p (taylorTail p (fun j => iteratedDeriv j Q.eval 0) 0) Q 0 s

private theorem twoSidedTaylor_matching (p : ℕ) (Q : ℝ[X]) :
    ∀ j ≤ p, iteratedDeriv j
      (taylorTail p (fun i => iteratedDeriv i Q.eval 0) 0) 0 =
        iteratedDeriv j Q.eval 0 := by
  intro j hj
  exact taylorTail_jet p _ 0 hj

/-- The two Taylor continuations preserve actual finite differentiability. -/
theorem contDiff_twoSidedTaylor (p : ℕ) (Q : ℝ[X]) {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ p (twoSidedTaylor p Q s) :=
  extendRight_contDiff (taylorTail_contDiff p _ 0) hs (twoSidedTaylor_matching p Q)

/-- Actual derivatives on the negative half-line equal the initial Taylor tail. -/
theorem twoSidedTaylor_left (p : ℕ) (Q : ℝ[X]) {s u : ℝ} (hs : 0 ≤ s)
    {j : ℕ} (hj : j ≤ p) (hu : u ≤ 0) :
    iteratedDeriv j (twoSidedTaylor p Q s) u =
      iteratedDeriv j (taylorTail p (fun i => iteratedDeriv i Q.eval 0) 0) u :=
  extendRight_left (taylorTail_contDiff p _ 0) hs (twoSidedTaylor_matching p Q) hj hu

/-- Actual derivatives on the polynomial interval are unchanged, including joins. -/
theorem twoSidedTaylor_interval (p : ℕ) (Q : ℝ[X]) {s u : ℝ} (hs : 0 ≤ s)
    {j : ℕ} (hj : j ≤ p) (hu : u ∈ Icc 0 s) :
    iteratedDeriv j (twoSidedTaylor p Q s) u = iteratedDeriv j Q.eval u := by
  simpa only [twoSidedTaylor, sub_zero] using extendRight_interval (taylorTail_contDiff p _ 0)
    hs (twoSidedTaylor_matching p Q) hj hu

/-- Actual derivatives beyond a positive interval equal the final Taylor tail. -/
theorem twoSidedTaylor_right (p : ℕ) (Q : ℝ[X]) {s u : ℝ} (hs : 0 < s)
    {j : ℕ} (hj : j ≤ p) (hu : s ≤ u) :
    iteratedDeriv j (twoSidedTaylor p Q s) u =
      iteratedDeriv j (taylorTail p (fun i => iteratedDeriv i Q.eval s) s) u := by
  simpa only [twoSidedTaylor, sub_zero] using extendRight_tail (taylorTail_contDiff p _ 0)
    hs (twoSidedTaylor_matching p Q) hj hu

/-- Flat positive-order terminal jets make every right-side derivative constant. -/
theorem twoSidedTaylor_right_flat (p : ℕ) (Q : ℝ[X]) {s u : ℝ} (hs : 0 < s)
    (hflat : ∀ i, 1 ≤ i → i ≤ p → iteratedDeriv i Q.eval s = 0)
    {j : ℕ} (hj : j ≤ p) (hu : s ≤ u) :
    iteratedDeriv j (twoSidedTaylor p Q s) u = if j = 0 then Q.eval s else 0 := by
  rw [twoSidedTaylor_right p Q hs hj hu, taylorTail_of_flat hflat, iteratedDeriv_const]
  rfl

/-- A flat terminal jet gives a uniform actual derivative bound on the whole
positive half-line, chosen before the evaluation point and derivative order. -/
theorem twoSidedTaylor_bounded_nonneg (p : ℕ) (Q : ℝ[X]) {s : ℝ} (hs : 0 < s)
    (hflat : ∀ i, 1 ≤ i → i ≤ p → iteratedDeriv i Q.eval s = 0) :
    ∃ B > 0, ∀ j ≤ p, ∀ u : ℝ, 0 ≤ u →
      |iteratedDeriv j (twoSidedTaylor p Q s) u| ≤ B := by
  obtain ⟨B, hB, hb⟩ := polynomial_derivatives_bounded p Q s
  refine ⟨B, hB, ?_⟩
  intro j hj u hu
  by_cases hus : u ≤ s
  · rw [twoSidedTaylor_interval p Q hs.le hj ⟨hu, hus⟩]
    exact hb j hj u ⟨hu, hus⟩
  · rw [twoSidedTaylor_right_flat p Q hs hflat hj (lt_of_not_ge hus).le]
    split_ifs with hj0
    · simpa only [iteratedDeriv_zero] using hb 0 (Nat.zero_le _) s ⟨hs.le, le_rfl⟩
    · simpa only [abs_zero] using hB.le

/-- The second-order endpoint Taylor polynomial has its usual three actual jets. -/
theorem taylorTail_two (a : ℕ → ℝ) (b u : ℝ) :
    taylorTail 2 a b u = a 0 + a 1 * (u - b) + a 2 / 2 * (u - b) ^ 2 := by
  simp [taylorTail, initialPolynomial, jetPoly, Finset.sum_range_succ]

end Hermite
