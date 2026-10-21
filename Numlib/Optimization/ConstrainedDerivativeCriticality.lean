import Numlib.Optimization.ConstrainedRegularization

/-!
# Perturbations of derivative gaps on unit directions

Tensor norm errors control directional derivative gaps on compact domains. The source and
comparison domains may differ, provided every tested source direction is a comparison direction.
-/

noncomputable section
namespace Optimization.ConstrainedRegularization
open TaylorCriticality
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {j : ℕ}

/-- A tensor perturbation transfers a negative diagonal bound on every unit direction. -/
theorem neg_diagonal_le_add_error
    (A B : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ) {d : E} {R T : ℝ}
    (hd : ‖d‖ ≤ 1) (hR : ‖A - B‖ ≤ R) (hT : -B (fun _ => d) ≤ T) :
    -A (fun _ => d) ≤ T + R := by
  have he := (abs_diagonal_sub_le_norm A B hd).trans hR
  have hh := (abs_le.mp he).1
  linarith

/-- A norm error bounds a derivative gap on a smaller unit-direction domain by the
comparison gap plus that error. Compactness is needed only for the comparison domain. -/
theorem gapOn_neg_diagonal_le_add_error
    (A B : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ)
    {D M : Set E} {R : ℝ} (hM : IsCompact M) (hD : D.Nonempty)
    (hDM : D ⊆ M) (hunit : ∀ d ∈ D, ‖d‖ ≤ 1) (hR : ‖A - B‖ ≤ R) :
    gapOn (fun d => -A (fun _ => d)) D ≤
      gapOn (fun d => -B (fun _ => d)) M + R := by
  apply gapOn_le hD
  intro d hd
  exact neg_diagonal_le_add_error A B (hunit d hd) hR
    (le_gapOn hM (B.cont.comp (continuous_pi fun _ => continuous_id)).neg.continuousOn
      (hDM hd))

end Optimization.ConstrainedRegularization

namespace Optimization.HigherOrderRegularization
/-- A strict positive-order step bound gives the strict real-power estimate. -/
theorem rpow_measure_lt_step_power {a C t : ℝ} {m r : ℕ}
    (ha : 0 ≤ a) (hC : 0 < C) (ht : 0 ≤ t) (hm : 0 < m) (hr : 0 < r)
    (h : a < C * t ^ m) :
    C⁻¹ ^ ((r : ℝ) / m) * a ^ ((r : ℝ) / m) < t ^ r := by
  have hdiv : C⁻¹ * a < t ^ m := by
    rw [← div_eq_inv_mul, div_lt_iff₀ hC]
    simpa [mul_comm] using h
  have hpow := Real.rpow_lt_rpow (mul_nonneg (inv_nonneg.mpr hC.le) ha) hdiv
    (by positivity : 0 < (r : ℝ) / m)
  rw [Real.mul_rpow (inv_nonneg.mpr hC.le) ha,
    ← Real.rpow_natCast t m, ← Real.rpow_mul ht] at hpow
  have he : (m : ℝ) * ((r : ℝ) / m) = r := by field_simp
  simpa [he, Real.rpow_natCast] using hpow
end Optimization.HigherOrderRegularization
