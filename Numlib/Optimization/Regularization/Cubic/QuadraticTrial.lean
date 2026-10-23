import Numlib.Optimization.Regularization.Cubic.LocalCountCounterexample

/-!
# A family of genuine stationary cubic trials on the quadratic objective

Every positive step scale gives a strictly improving model-stationary trial
with ratio one and all legal update rules.
-/

namespace CubicRegularization.QuadraticTrial
open HighOrderRegularization.ObstructionCounterexample LocalCountCounterexample
/-- The initialized point and exact accepted endpoint at a positive step scale. -/
noncomputable def point (u : ℝ) (k : ℕ) : ℝ := if k = 0 then u + u ^ 2 / 8 else u ^ 2 / 8

/-- The actual cubic model derivative vanishes at the negative scaled step. -/
theorem model_derivative_zero {u : ℝ} (hu : 0 < u) :
    fderiv ℝ (model objective (u + u ^ 2 / 8) (1 / 4)) (-u) = 0 := by
  rw [fderiv_model (by unfold objective; fun_prop)]
  apply ContinuousLinearMap.ext
  intro d
  simp only [TaylorModel.quadraticDerivative, add_apply, smul_apply, zero_apply,
    innerSL_apply_apply]
  have hf : fderiv ℝ objective (u + u ^ 2 / 8) d = (u + u ^ 2 / 8) * d := by
    rw [fderiv_eq_deriv_mul, deriv_objective]
  rw [hf]
  rw [show fderiv ℝ (fderiv ℝ objective) (u + u ^ 2 / 8) (-u) d = (-u) * d by
    have hh := second_formula (u + u ^ 2 / 8) ![-u, d]
    rw [iteratedFDeriv_two_apply] at hh
    exact hh]
  simp only [norm_neg, Real.norm_eq_abs, abs_of_pos hu, RCLike.inner_apply, conj_trivial]
  ring

/-- All model improvement, ratio and legal parameter rules hold for the trial. -/
theorem modelTrace {u : ℝ} (hu : 0 < u) : ModelTrace objective (point u) (fun _ => -u)
    (fun _ => 1 / 4) (fun _ => 1) (1 / 4) (3 / 4) (1 / 2) 2 3 (1 / 4) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    intro i hi
    norm_num
  · intro i hi
    have he : i = 0 := by omega
    subst i
    unfold model ModelDecrease.penalized
    rw [taylor_exact, taylor_exact]
    simp only [point, add_zero, norm_neg, Real.norm_eq_abs, abs_of_pos hu,
      Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one ]
    dsimp [objective]
    nlinarith [sq_pos_of_pos hu, mul_pos hu (sq_pos_of_pos hu)]
  · intro i hi
    have he : i = 0 := by omega
    subst i
    rw [taylor_exact, taylor_exact]
    simp only [point, add_zero]
    apply (div_self ?_).symm
    dsimp [objective]
    nlinarith [sq_pos_of_pos hu, mul_pos hu (sq_pos_of_pos hu)]

/-- Every positive accuracy below the initial gradient gives a genuine one-trial AR2 execution. -/
theorem run {u ε : ℝ} (hu : 0 < u) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfail : ε < u + u ^ 2 / 8) :
    FirstOrderRun objective (point u) (fun _ => -u) (fun _ => 1 / 4) (fun _ => 1)
      (1 / 4) (3 / 4) (1 / 2) 2 3 (1 / 4) (1 / 2) ε ⊤ 1 := by
  refine ⟨rfl, modelTrace hu, by norm_num, hε, hε1, ?_, ?_, ?_⟩
  · intro i hi
    have he : i = 0 := by omega
    subst i
    rw [← norm_deriv_eq_norm_fderiv, deriv_objective]
    simpa [point, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < u + u ^ 2 / 8)] using hfail
  · intro i hi
    have he : i = 0 := by omega
    subst i
    change ‖fderiv ℝ (model objective (u + u ^ 2 / 8) (1 / 4)) (-u)‖ ≤ _
    rw [model_derivative_zero hu, norm_zero]
    positivity
  · intro i hi
    have he : i = 0 := by omega
    subst i
    norm_num [point]
end CubicRegularization.QuadraticTrial
