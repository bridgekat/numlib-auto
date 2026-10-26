import Numlib.Analysis.Calculus.TaylorModel.Peano
import Numlib.Optimization.HighOrder.Criticality

/-!
# Strict minimality from quantitative Taylor growth

A uniform positive growth bound on the actual degree-j Taylor polynomial
survives its next homogeneous term and the genuine Peano remainder. Isolated
minimality alone need not provide this growth, so it is not used as a substitute.
-/

namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Quantitative growth of a genuine Taylor polynomial survives the next
actual derivative tensor on a sufficiently small displacement ball. -/
theorem exists_pos_eval_succ_growth (f : E → ℝ) (j : ℕ) (x : E)
    {c r : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hgrowth : ∀ s : E, ‖s‖ ≤ r → c * ‖s‖ ^ j ≤ eval f j x s - f x) :
    ∃ R > 0, ∀ s : E, ‖s‖ < R →
      c / 2 * ‖s‖ ^ j ≤ eval f (j + 1) x s - f x := by
  let A := ‖iteratedFDeriv ℝ (j + 1) f x‖
  have hA : 0 ≤ A := norm_nonneg _
  have hfac : (0 : ℝ) < (j + 1).factorial := by positivity
  let R := min r (c * (j + 1).factorial / (2 * (A + 1)))
  refine ⟨R, lt_min hr (div_pos (mul_pos hc hfac) (by positivity)), ?_⟩
  intro s hs
  have hs0 := norm_nonneg s
  have hs1 : ‖s‖ ≤ r := (hs.trans_le (min_le_left _ _)).le
  have hs2 : ‖s‖ < c * (j + 1).factorial / (2 * (A + 1)) :=
    hs.trans_le (min_le_right _ _)
  have hm := (lt_div_iff₀ (show 0 < 2 * (A + 1) by positivity)).mp hs2
  have hcoef : A * ‖s‖ / (j + 1).factorial ≤ c / 2 := by
    apply (div_le_iff₀ hfac).mpr
    nlinarith
  have hpow := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hs0 j)
  have he : A * ‖s‖ ^ (j + 1) / (j + 1).factorial =
      (A * ‖s‖ / (j + 1).factorial) * ‖s‖ ^ j := by rw [pow_succ]; ring
  have herr := norm_eval_succ_sub_eval_le f j x s
  rw [Real.norm_eq_abs] at herr
  change |eval f (j + 1) x s - eval f j x s| ≤
    A * ‖s‖ ^ (j + 1) / (j + 1).factorial at herr
  rw [he] at herr
  have hg := hgrowth s hs1
  linarith [(abs_le.mp herr).1]

/-- Finite smoothness derives the actual Peano error needed to preserve
positive Taylor growth in the objective itself. -/
theorem exists_pos_value_growth {f : E → ℝ} {j : ℕ} (hj : 0 < j)
    (hf : ContDiff ℝ j f) (x : E) {c r : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hgrowth : ∀ s : E, ‖s‖ ≤ r → c * ‖s‖ ^ j ≤ eval f j x s - f x) :
    ∃ R > 0, ∀ s : E, ‖s‖ < R → c / 2 * ‖s‖ ^ j ≤ f (x + s) - f x := by
  obtain ⟨R, hR, herr⟩ := exists_pos_abs_sub_eval_le hj hf x (half_pos hc)
  refine ⟨min r R, lt_min hr hR, ?_⟩
  intro s hs
  have hg := hgrowth s (hs.trans_le (min_le_left _ _)).le
  have he := (abs_le.mp (herr s (hs.trans_le (min_le_right _ _)))).1
  linarith

/-- A positive uniform Taylor growth bound gives strict isolated minima of
both the next Taylor polynomial and the actual objective on one common ball. -/
theorem strict_local_min_of_taylor_growth {f : E → ℝ} {j : ℕ} (hj : 0 < j)
    (hf : ContDiff ℝ j f) (x : E) {c r : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hgrowth : ∀ s : E, ‖s‖ ≤ r → c * ‖s‖ ^ j ≤ eval f j x s - f x) :
    ∃ R > 0, ∀ s : E, ‖s‖ < R → s ≠ 0 →
      f x < eval f (j + 1) x s ∧ f x < f (x + s) := by
  obtain ⟨R₁, hR₁, hmodel⟩ := exists_pos_eval_succ_growth f j x hc hr hgrowth
  obtain ⟨R₂, hR₂, hvalue⟩ := exists_pos_value_growth hj hf x hc hr hgrowth
  refine ⟨min R₁ R₂, lt_min hR₁ hR₂, ?_⟩
  intro s hs hs0
  have hpos := mul_pos (half_pos hc) (pow_pos (norm_pos_iff.mpr hs0) j)
  have h1 := hmodel s (hs.trans_le (min_le_left _ _))
  have h2 := hvalue s (hs.trans_le (min_le_right _ _))
  constructor <;> linarith

end TaylorModel
