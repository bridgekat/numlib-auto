import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.IntervalCases

/-!
# SquaredNorm

SquaredNorm
-/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A Hilbert-valued C^j curve with zero value and zero first derivative has zero actual
squared-norm derivative at each j<=3. Derive from the genuine finite chain rule; no higher
derivative formula is assumed. -/
theorem iteratedDeriv_norm_sq_eq_zero_of_value_deriv_zero {r : ℝ → F} {j : ℕ} (hj : j ≤ 3)
    (hr : ContDiffAt ℝ j r 0) (h0 : r 0 = 0) (h1 : deriv r 0 = 0) :
    iteratedDeriv j (fun t => ‖r t‖ ^ 2) 0 = 0 := by
  have hg : ContDiff ℝ 3 (fun z : F => ‖z‖ ^ 2) := contDiff_id.norm_sq (𝕜 := ℝ)
  have hd : fderiv ℝ (fun z : F => ‖z‖ ^ 2) (r 0) = 0 := by
    rw [h0, fderiv_norm_sq_apply]
    simp
  interval_cases j
  · simp [h0]
  · rw [iteratedDeriv_one]
    have hh := ((hr.differentiableAt (by norm_num)).hasDerivAt.norm_sq).deriv
    simpa [h0] using hh
  · change iteratedDeriv 2 ((fun z : F => ‖z‖ ^ 2) ∘ r) 0 = 0
    rw [iteratedDeriv_vcomp_two (hg.of_le (by norm_num)).contDiffAt
      (hr.of_le (by norm_num)), h1, hd]
    rw [ContinuousMultilinearMap.map_coord_zero _ (0 : Fin 2) rfl]
    simp
  · change iteratedDeriv 3 ((fun z : F => ‖z‖ ^ 2) ∘ r) 0 = 0
    rw [iteratedDeriv_vcomp_three hg.contDiffAt hr, h1, hd]
    rw [ContinuousMultilinearMap.map_coord_zero _ (0 : Fin 3) rfl,
      ContinuousMultilinearMap.map_coord_zero _ (1 : Fin 2) (by simp),
      ContinuousMultilinearMap.map_coord_zero _ (0 : Fin 2) (by simp)]
    simp
