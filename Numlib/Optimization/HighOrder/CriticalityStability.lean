import Numlib.Optimization.HighOrder.Criticality
import Numlib.Analysis.Calculus.TaylorModel.Holder

/-!
# Objective stability from approximate Taylor criticality

A bound on actual Taylor criticality bounds the possible objective decrease in a local
ball. A sharp Lipschitz Taylor remainder supplies the exact factorial and stability radius.
All regularity and Lipschitz assumptions are local; no extra derivative is required.
-/

namespace TaylorModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- Approximate Taylor criticality bounds true objective decrease up to the sharp
local Taylor error. The derivative Lipschitz bound is needed only on the radius ball. -/
theorem value_ge_of_criticality {f : E → ℝ} {j : ℕ} (hj : 0 < j)
    {D : Set E} (hD : IsOpen D) (hf : ContDiffOn ℝ j f D) (x : E)
    {δ ε L : ℝ} (hδ : 0 ≤ δ) (hball : Metric.closedBall x δ ⊆ D) (hL : 0 ≤ L)
    (hlip : ∀ u ∈ Metric.closedBall x δ, ∀ v ∈ Metric.closedBall x δ,
      ‖iteratedFDeriv ℝ j f u - iteratedFDeriv ℝ j f v‖ ≤ L * ‖u - v‖)
    (hcrit : criticality f j x δ ≤ ε * δ ^ j / j.factorial)
    {d : E} (hd : ‖d‖ ≤ δ) :
    f x - ε * δ ^ j / j.factorial - L * ‖d‖ ^ (j + 1) / (j + 1).factorial ≤ f (x + d) := by
  have hdec := (decrement_le_criticality f j x hd).trans hcrit
  rw [decrement_eq] at hdec
  have herr : |f (x + d) - eval f j x d| ≤ L * ‖d‖ ^ (j + 1) / (j + 1).factorial := by
    cases j with
    | zero => omega
    | succ p =>
      exact abs_sub_eval_le_lipschitz hD hball (convex_closedBall x δ) hf hL hlip
        (by simpa using hδ) (by simpa [dist_eq_norm] using hd)
  linarith [(abs_le.mp herr).1]

/-- A displacement whose Lipschitz error scale is at most `(j+1)ε` doubles at most
the objective-decrease tolerance supplied by approximate criticality. -/
theorem value_ge_sub_two_tolerance_of_criticality {f : E → ℝ} {j : ℕ} (hj : 0 < j)
    {D : Set E} (hD : IsOpen D) (hf : ContDiffOn ℝ j f D) (x : E)
    {δ ε L : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hball : Metric.closedBall x δ ⊆ D) (hL : 0 ≤ L)
    (hlip : ∀ u ∈ Metric.closedBall x δ, ∀ v ∈ Metric.closedBall x δ,
      ‖iteratedFDeriv ℝ j f u - iteratedFDeriv ℝ j f v‖ ≤ L * ‖u - v‖)
    (hcrit : criticality f j x δ ≤ ε * δ ^ j / j.factorial)
    {d : E} (hd : ‖d‖ ≤ δ) (hsmall : L * ‖d‖ ≤ (j + 1 : ℕ) * ε) :
    f x - 2 * ε * δ ^ j / j.factorial ≤ f (x + d) := by
  have hb := value_ge_of_criticality hj hD hf x hδ hball hL hlip hcrit hd
  have hpow : ‖d‖ ^ j ≤ δ ^ j := pow_le_pow_left₀ (norm_nonneg d) hd j
  have hnum : L * ‖d‖ ^ (j + 1) ≤ (j + 1 : ℕ) * ε * δ ^ j := by
    rw [pow_succ]
    nlinarith [mul_le_mul hsmall hpow (pow_nonneg (norm_nonneg d) j)
      (mul_nonneg (by positivity : (0 : ℝ) ≤ (j + 1 : ℕ)) hε)]
  have he : ((j + 1 : ℕ) : ℝ) * ε * δ ^ j / ((j + 1).factorial : ℝ) =
      ε * δ ^ j / j.factorial := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    field_simp
  have hr := (div_le_div_of_nonneg_right hnum
    (by positivity : (0 : ℝ) ≤ (j + 1).factorial)).trans_eq he
  calc f x - 2 * ε * δ ^ j / j.factorial =
      f x - ε * δ ^ j / j.factorial - ε * δ ^ j / j.factorial := by ring
    _ ≤ f x - ε * δ ^ j / j.factorial - L * ‖d‖ ^ (j + 1) / (j + 1).factorial := by
      linarith
    _ ≤ f (x + d) := hb

end TaylorModel
