import Numlib.Optimization.Regularization.Inexact.StepTwo
import Numlib.Optimization.TrustRegion.Inexact.Decrease

/-!
# Trial-length and request bounds from actual Step2 comparisons

A primitive positive reference-model decrease and a proved radius floor imply
a positive trial-length floor. Uniformly small requested accuracies therefore
pass every derivative request through the model degree, including under the
literal short-step guard. No trial-length conclusion is assumed in the trace.
-/

namespace InexactRegularization
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The uniform step threshold from the actual reference decrease and supplied
positive-order tensor bound. Its coefficient is independent of accuracies. -/
noncomputable def referenceStepThreshold (q : ℕ) (ζ κ D μ : ℝ) : ℝ :=
  ζ * κ ^ q / (8 * (q.factorial : ℝ) * D) * μ ^ (q + 1)

/-- Positive coefficients and accuracy give a strictly positive step threshold. -/
theorem referenceStepThreshold_pos (q : ℕ) {ζ κ D μ : ℝ}
    (hζ : 0 < ζ) (hκ : 0 < κ) (hD : 0 < D) (hμ : 0 < μ) :
    0 < referenceStepThreshold q ζ κ D μ := by
  unfold referenceStepThreshold
  positivity

/-- The sufficient step threshold is at most one on the normalized parameter
range, including zero relative factor, radius coefficient or accuracy. -/
theorem referenceStepThreshold_le_one (q : ℕ) {ζ κ D μ : ℝ}
    (hζ1 : ζ ≤ 1) (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hD : 1 ≤ D) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    referenceStepThreshold q ζ κ D μ ≤ 1 := by
  have hnum : ζ * κ ^ q * μ ^ (q + 1) ≤ 1 := by
    calc _ ≤ 1 * 1 * 1 := mul_le_mul
          (mul_le_mul hζ1 (pow_le_one₀ hκ hκ1) (pow_nonneg hκ _) zero_le_one)
          (pow_le_one₀ hμ hμ1) (pow_nonneg hμ _) (by norm_num)
      _ = 1 := by ring
  have hfac : (1 : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
  have hden : 1 ≤ 8 * (q.factorial : ℝ) * D := by nlinarith
  unfold referenceStepThreshold
  rw [div_mul_eq_mul_div]
  exact (div_le_one (by positivity : 0 < 8 * (q.factorial : ℝ) * D)).mpr
    (hnum.trans hden)

/-- Actual model decrease is bounded linearly by the trial length on the unit
ball; the nonnegative regularization penalty can only reduce this decrease. -/
theorem model_drop_le_two_mul_norm (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ)
    {σ D : ℝ} (hσ : 0 ≤ σ) (hD : 0 ≤ D) {s : E} (hs : ‖s‖ ≤ 1)
    (hA : ∀ i, 1 ≤ i → i ≤ p → ‖A i‖ ≤ D) :
    model A p σ 0 - model A p σ s ≤ 2 * D * ‖s‖ := by
  have hpen : 0 ≤ σ / ((p + 1).factorial : ℝ) * ‖s‖ ^ (p + 1) := by positivity
  have hdrop : model A p σ 0 - model A p σ s ≤ TaylorModel.jetDecrement A p s := by
    simp only [model, ModelDecrease.penalized_zero]
    unfold ModelDecrease.penalized TaylorModel.jetDecrement
    linarith
  exact hdrop.trans ((le_abs_self _).trans (norm_decrement_le_two_mul A p hD hs hA))

/-- A primitive reference-decrease test, the actual Step2 comparison and a
proved radius floor force a positive trial length for every permitted return. -/
theorem norm_step_ge_of_reference (A : FormalMultilinearSeries ℝ E ℝ)
    {p q j : ℕ} (hjq : j ≤ q) {σ δ ζ κ D μ : ℝ}
    (hσ : 0 ≤ σ) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hD : 1 ≤ D) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (hfloor : κ * μ ≤ δ)
    (reference s : E) (hA : ∀ i, 1 ≤ i → i ≤ p → ‖A i‖ ≤ D)
    (href : ζ / 4 * μ * δ ^ j / j.factorial ≤
      model A p σ 0 - model A p σ reference)
    (hcomp : model A p σ s ≤ model A p σ reference) :
    referenceStepThreshold q ζ κ D μ ≤ ‖s‖ := by
  by_cases hs : ‖s‖ ≤ 1
  · let b := κ * μ
    have hb : 0 ≤ b := mul_nonneg hκ hμ
    have hb1 : b ≤ 1 := (mul_le_of_le_one_left hμ hκ1).trans hμ1
    have hδ : 0 ≤ δ := hb.trans hfloor
    have hpow := pow_div_factorial_antitone hb hb1 hjq
    have hscale : ζ / 4 * μ * (b ^ q / q.factorial) ≤
        ζ / 4 * μ * δ ^ j / j.factorial := by
      calc _ ≤ ζ / 4 * μ * (b ^ j / j.factorial) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ ≤ ζ / 4 * μ * (δ ^ j / j.factorial) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
              (pow_le_pow_left₀ hb hfloor _) (Nat.cast_nonneg _)) (by positivity)
        _ = _ := by ring
    have hupper := model_drop_le_two_mul_norm A p hσ (zero_le_one.trans hD) hs hA
    have hh := hscale.trans (href.trans ((sub_le_sub_left hcomp _).trans hupper))
    have he : 2 * D * referenceStepThreshold q ζ κ D μ =
        ζ / 4 * μ * (b ^ q / q.factorial) := by
      unfold referenceStepThreshold
      dsimp only [b]
      rw [mul_pow, pow_succ μ]
      field_simp
      ring
    rw [← he] at hh
    exact (mul_le_mul_iff_right₀ (show 0 < 2 * D by positivity)).mp hh
  · exact (referenceStepThreshold_le_one q hζ1 hκ hκ1 hD hμ hμ1).trans (not_le.mp hs).le

/-- The explicit reference threshold makes every actual derivative request
through degree `p` pass; the index range is `1..p`, including when `q<p`. -/
theorem requests_of_reference (A : FormalMultilinearSeries ℝ E ℝ)
    {p q j : ℕ} (hjq : j ≤ q) {σ δ ζ κ D μ κs H : ℝ}
    (hσ : 0 ≤ σ) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hD : 1 ≤ D) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (hκs : 0 ≤ κs)
    (hfloor : κ * μ ≤ δ) (reference s : E)
    (hA : ∀ i, 1 ≤ i → i ≤ p → ‖A i‖ ≤ D)
    (href : ζ / 4 * μ * δ ^ j / j.factorial ≤
      model A p σ 0 - model A p σ reference)
    (hcomp : model A p σ s ≤ model A p σ reference)
    (hH : H ≤ κs * referenceStepThreshold q ζ κ D μ ^ p)
    (accuracy : ℕ → ℝ) (haccuracy : ∀ i, 1 ≤ i → i ≤ p → accuracy i ≤ H) :
    ∀ i, 1 ≤ i → i ≤ p → accuracy i ≤ κs * ‖s‖ ^ (p - i + 1) := by
  have hnonneg : 0 ≤ referenceStepThreshold q ζ κ D μ := by
    unfold referenceStepThreshold
    positivity
  exact requests_of_norm_floor hnonneg
    (referenceStepThreshold_le_one q hζ1 hκ hκ1 hD hμ hμ1) hκs hH accuracy haccuracy s
    (norm_step_ge_of_reference A hjq hσ hζ hζ1 hκ hκ1 hD hμ hμ1 hfloor reference s
      hA href hcomp)

end InexactRegularization
