import Numlib.Optimization.Quadratic.Optimality.TrustRegion
import Numlib.Optimization.Quadratic.Regularization.Stopping
import Numlib.Analysis.SpecialFunctions.Pow.Differences
import Mathlib.Tactic

/-!
# Global optimality for real-power regularized quadratic models

The actual first and second derivatives give stationarity and curvature at
zero. At a nonzero minimizer, sphere reflections give shifted semidefiniteness.
The squared-radius power tangent gives sufficiency and uniqueness.
-/

open scoped Topology
namespace QuadraticOptimality
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual quadratic plus the real norm-power penalty, with source exponent strictly above
two. -/
noncomputable def regularized (H : E →L[ℝ] E) (g : E) (σ r : ℝ) (s : E) : ℝ :=
  model H g s + σ / r * ‖s‖ ^ r

/-- The true first derivative of the quadratic norm-regularized model. -/
theorem hasFDerivAt_regularized {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric)
    (g : E) {r : ℝ} (hr : 2 < r) (σ : ℝ) (s : E) :
    HasFDerivAt (regularized H g σ r)
      (innerSL ℝ (g + H s) + (σ / r) • NormPower.first r s) s :=
  (hasFDerivAt_model hH g s).add
    ((NormPower.hasFDerivAt_normPower (by linarith : 1 < r) s).const_mul (σ / r))

/-- Every actual global minimizer satisfies radial stationarity with multiplier sigma times its
norm to the power r minus two. -/
theorem stationary_of_regularized_min {H : E →L[ℝ] E}
    (hH : H.toLinearMap.IsSymmetric) (g : E) {r : ℝ} (hr : 2 < r)
    (σ : ℝ) (s : E) (hmin : ∀ t, regularized H g σ r s ≤ regularized H g σ r t) :
    g + H s = -(σ * ‖s‖ ^ (r - 2)) • s := by
  have hm : IsLocalMin (regularized H g σ r) s := Filter.Eventually.of_forall hmin
  have he := hm.hasFDerivAt_eq_zero (hasFDerivAt_regularized hH g hr σ s)
  have hs (v : E) : inner ℝ (g + H s + (σ * ‖s‖ ^ (r - 2)) • s) v = 0 := by
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) he
    simp only [add_apply, innerSL_apply_apply, smul_apply, NormPower.first,
      smul_eq_mul, zero_apply] at hh
    rw [inner_add_left, real_inner_smul_left]
    have hr0 : r ≠ 0 := by linarith
    field_simp [hr0] at hh
    nlinarith
  have hz := inner_self_eq_zero.mp (hs (g + H s + (σ * ‖s‖ ^ (r - 2)) • s))
  simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hz

/-- At a zero global minimizer the original quadratic Hessian is positive semidefinite, using
the actual second derivative of the penalty at zero. -/
theorem psd_of_regularized_min_zero {H : E →L[ℝ] E}
    (hH : H.toLinearMap.IsSymmetric) (g : E) {r : ℝ} (hr : 2 < r)
    (σ : ℝ) (hmin : ∀ t, regularized H g σ r 0 ≤ regularized H g σ r t) :
    ∀ v, 0 ≤ inner ℝ (H v) v := by
  have hm : IsLocalMin (regularized H g σ r) 0 := Filter.Eventually.of_forall hmin
  let L : E → E →L[ℝ] ℝ := fun s =>
    innerSL ℝ (g + H s) + (σ / r) • NormPower.first r s
  have hfirst : HasFDerivAt (fun s => innerSL ℝ (g + H s)) ((innerSL ℝ).comp H) (0:E) := by
    convert (innerSL ℝ).hasFDerivAt.comp 0
      ((hasFDerivAt_const g (0:E)).add H.hasFDerivAt) using 1 <;> simp
    rfl
  have hd : HasFDerivAt L ((innerSL ℝ).comp H) 0 := by
    have hh := hfirst.add ((NormPower.hasFDerivAt_first_zero hr).const_smul (σ / r))
    convert! hh using 1
    simp only [smul_zero, add_zero]
  intro v
  exact Descent.nonneg_apply_apply_of_isLocalMin hm
    (Filter.Eventually.of_forall (hasFDerivAt_regularized hH g hr σ)) hd v

/-- Actual global minimality implies the exact radial multiplier equation and shifted positive
semidefiniteness, including a zero minimizer and every real exponent above two. -/
theorem necessary_regularized [CompleteSpace E] {H : E →L[ℝ] E}
    (hH : H.toLinearMap.IsSymmetric) (g s : E) {r : ℝ} (hr : 2 < r) (σ : ℝ)
    (hmin : ∀ t, regularized H g σ r s ≤ regularized H g σ r t) :
    g + H s = -(σ * ‖s‖ ^ (r - 2)) • s ∧
      ∀ v, 0 ≤ inner ℝ ((H + (σ * ‖s‖ ^ (r - 2)) • ContinuousLinearMap.id ℝ E) v) v := by
  have hstat := stationary_of_regularized_min hH g hr σ s hmin
  refine ⟨hstat, ?_⟩
  by_cases hs : s = 0
  · subst s
    have hp := psd_of_regularized_min_zero hH g hr σ hmin
    simpa only [norm_zero, Real.zero_rpow (by linarith : r - 2 ≠ 0), mul_zero,
      zero_smul, add_zero] using hp
  · apply shifted_psd_of_sphere_min hH g s hs hstat
    intro t ht
    have hn : ‖t‖ = ‖s‖ := (sq_eq_sq₀ (norm_nonneg t) (norm_nonneg s)).mp ht
    have hh := hmin t
    dsimp [regularized] at hh
    rw [hn] at hh
    linarith

omit [InnerProductSpace ℝ E] in
/-- The norm-power penalty lies above its squared-radius tangent for every pair of vectors,
including zero. -/
theorem penalty_gap_nonneg (s t : E) {r σ : ℝ} (hr : 2 < r) (hσ : 0 ≤ σ) :
    0 ≤ σ / r * (‖t‖ ^ r - ‖s‖ ^ r) - (σ * ‖s‖ ^ (r - 2)) / 2 * (‖t‖ ^ 2 - ‖s‖ ^ 2) := by
  have hh := Real.mul_rpow_sub_le_sub_rpow (sq_nonneg ‖s‖) (sq_nonneg ‖t‖) (by linarith : 1 ≤ r / 2)
  have he (s : E) (a : ℝ) : (‖s‖ ^ 2) ^ a = ‖s‖ ^ (2 * a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg s)]
    norm_num
  rw [he, he, he] at hh
  have h1 : 2 * (r / 2 - 1) = r - 2 := by ring
  have h2 : 2 * (r / 2) = r := by ring
  rw [h1, h2] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (div_nonneg hσ (by linarith : 0 ≤ r))
  have hr0 : r ≠ 0 := by linarith
  field_simp [hr0] at hh' ⊢
  nlinarith

/-- The actual radial multiplier equation and shifted semidefiniteness imply global minimality
of the norm-regularized quadratic. -/
theorem sufficient_regularized {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric)
    (g s : E) {r σ : ℝ} (hr : 2 < r) (hσ : 0 ≤ σ)
    (hsolve : g + H s = -(σ * ‖s‖ ^ (r - 2)) • s)
    (hPSD : ∀ v, 0 ≤ inner ℝ ((H + (σ * ‖s‖ ^ (r - 2)) • ContinuousLinearMap.id ℝ E) v) v) :
    ∀ t, regularized H g σ r s ≤ regularized H g σ r t := by
  intro t
  have hg := shifted_gap hH g s (t - s) hsolve
  rw [add_sub_cancel] at hg
  have hp := penalty_gap_nonneg s t hr hσ
  have hv := hPSD (t - s)
  dsimp [regularized]
  nlinarith


/-- Global minimality of the actual regularized quadratic is equivalent to radial stationarity
and shifted semidefiniteness. -/
theorem regularized_iff [CompleteSpace E] {H : E →L[ℝ] E}
    (hH : H.toLinearMap.IsSymmetric) (g s : E) {r σ : ℝ} (hr : 2 < r) (hσ : 0 ≤ σ) :
    (∀ t, regularized H g σ r s ≤ regularized H g σ r t) ↔
    g + H s = -(σ * ‖s‖ ^ (r - 2)) • s ∧
      ∀ v, 0 ≤ inner ℝ ((H + (σ * ‖s‖ ^ (r - 2)) • ContinuousLinearMap.id ℝ E) v) v := by
  exact ⟨necessary_regularized hH g s hr σ,
    fun ⟨hsolve, hPSD⟩ => sufficient_regularized hH g s hr hσ hsolve hPSD⟩

/-- A positive-definite shifted Hessian makes the actual global regularized minimizer unique. -/
theorem unique_regularized {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric)
    (g s : E) {r σ : ℝ} (hr : 2 < r) (hσ : 0 ≤ σ)
    (hsolve : g + H s = -(σ * ‖s‖ ^ (r - 2)) • s)
    (hPD : ∀ v, v ≠ 0 →
      0 < inner ℝ ((H + (σ * ‖s‖ ^ (r - 2)) • ContinuousLinearMap.id ℝ E) v) v) :
    ∀ t, regularized H g σ r t ≤ regularized H g σ r s → t = s := by
  intro t ht
  by_contra hne
  have hp := hPD (t - s) (sub_ne_zero.mpr hne)
  have hg := shifted_gap hH g s (t - s) hsolve
  rw [add_sub_cancel] at hg
  have hh := penalty_gap_nonneg s t hr hσ
  dsimp [regularized] at ht
  nlinarith

end QuadraticOptimality

