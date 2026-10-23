import Numlib.Optimization.Regularization.Cubic.QuadraticTrial

/-!
# A phase-complexity endpoint with a negative local double logarithm

A genuine accepted cubic trial is required at epsilon=zeta/sqrt(2). The
printed local logarithm is minus one, canceling the final additive one. The
remaining exact global budget is below one at the fixed tiny initial scale,
although the initial point fails and the first accepted endpoint passes.
-/

namespace CubicRegularization.PhaseCountCounterexample
open HighOrderRegularization.ObstructionCounterexample LocalCountCounterexample
/-- A fixed positive step scale with a small objective gap. -/
noncomputable def u : ℝ := 1 / 2 ^ 40
/-- The exact initial gradient and chosen local threshold. -/
noncomputable def zeta : ℝ := u + u ^ 2 / 8
/-- The permitted requested tolerance at which the double logarithm is minus one. -/
noncomputable def epsilon : ℝ := zeta / Real.sqrt 2
/-- The exact printed AR2 successful-iteration coefficient for the fixed parameters. -/
noncomputable def kappa : ℝ := 6 * ((1 : ℝ) + 1 / 2 + 12) ^ (3 / 2 : ℝ) /
  ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 / 4) * (1 / 4))
/-- The local threshold is positive and uniformly tiny. -/
theorem zeta_bounds : 0 < zeta ∧ zeta ≤ 1 / 2 ^ 32 := by norm_num [zeta,u]
/-- The square-root factor is strictly between one and two. -/
theorem sqrt_two_bounds : 1 < Real.sqrt 2 ∧ Real.sqrt 2 ≤ 2 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]; norm_num
  · rw [Real.sqrt_le_iff]; norm_num
/-- The requested tolerance is legal and below the initial gradient. -/
theorem epsilon_bounds : 0 < epsilon ∧ epsilon < zeta ∧ epsilon ≤ 1 := by
  have hz := zeta_bounds
  have hs := sqrt_two_bounds
  refine ⟨div_pos hz.1 (by positivity), ?_, ?_⟩
  · exact (div_lt_self hz.1 hs.1)
  · exact (div_le_self hz.1.le hs.1.le).trans (by norm_num at hz ⊢; linarith)
/-- The exact printed global coefficient is positive and bounded. -/
theorem kappa_bounds : 0 < kappa ∧ kappa ≤ 20000 := by
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 1 + 1/2+12)
    (by norm_num : (3/2 : ℝ) ≤ 2)
  rw [Real.rpow_two] at hp
  have hb := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 3/2)
  have hd : 0 < (2 : ℝ) ^ (3/2 : ℝ) * (1/4) * (1/4) := by positivity
  constructor
  · unfold kappa; positivity
  · unfold kappa
    apply (div_le_iff₀ hd).mpr
    nlinarith
/-- The displayed local iteration contribution is exactly minus one. -/
theorem printed_double_log : Real.logb 2 (Real.logb 2 (zeta / epsilon)) = -1 := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (by positivity)
  have he : zeta / epsilon = Real.sqrt 2 := by
    unfold epsilon
    field_simp [zeta_bounds.1.ne']
  rw [he]
  have hl : Real.logb 2 (Real.sqrt 2) = (1/2 : ℝ) := by
    rw [Real.logb, Real.log_sqrt (by norm_num)]
    have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    field_simp
  rw [hl, show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.logb_inv]
  norm_num [Real.logb_self_eq_one]
/-- The complete printed global-plus-local iteration bound is strictly less than one. -/
theorem printed_bound_lt_one :
    kappa * (objective zeta - 0) / zeta ^ (3/2 : ℝ) +
      Real.logb 2 (Real.logb 2 (zeta / epsilon)) + 1 < 1 := by
  have hz := zeta_bounds
  have he : zeta ^ 2 / zeta ^ (3/2 : ℝ) = Real.sqrt zeta := by
    rw [←Real.rpow_natCast, ←Real.rpow_sub hz.1]
    norm_num
    rw [Real.sqrt_eq_rpow]
  have hs : Real.sqrt zeta ≤ (1 : ℝ) / 65536 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · norm_num at hz ⊢; linarith
  rw [printed_double_log]
  have hterm : kappa * (objective zeta - 0) / zeta ^ (3/2 : ℝ) =
      kappa / 2 * Real.sqrt zeta := by
    rw [←he]
    dsimp [objective]
    ring
  rw [hterm]
  have hk := kappa_bounds
  have hm := mul_le_mul hk.2 hs (Real.sqrt_nonneg zeta) (by norm_num : (0 : ℝ) ≤ 20000)
  nlinarith
end CubicRegularization.PhaseCountCounterexample

namespace CubicRegularization.PhaseCountCounterexample
open HighOrderRegularization.ObstructionCounterexample LocalCountCounterexample
/-- The exact quadratic trial is a genuine complete AR2 execution at the selected tolerance. -/
theorem actual_run : FirstOrderRun objective (QuadraticTrial.point u) (fun _ => -u)
    (fun _ => 1/4) (fun _ => 1) (1/4) (3/4) (1/2) 2 3 (1/4) (1/2) epsilon ⊤ 1 :=
  QuadraticTrial.run (by norm_num [u]) epsilon_bounds.1 epsilon_bounds.2.2 epsilon_bounds.2.1
/-- The actual zero model derivative satisfies the tightened minimum test. -/
theorem stricter_test :
    ‖fderiv ℝ (model objective (QuadraticTrial.point u 0) (1/4)) (-u)‖ ≤
      (1/2 : ℝ) * min ‖fderiv ℝ objective (QuadraticTrial.point u 0)‖
        ((1/2 : ℝ) * ‖-u‖ ^ 2) := by
  change ‖fderiv ℝ (model objective (u + u^2/8) (1/4)) (-u)‖ ≤ _
  rw [QuadraticTrial.model_derivative_zero (by norm_num [u]), norm_zero]
  positivity
/-- The initial point satisfies every literal local threshold, with all five terms finite. -/
theorem initial_region :
    ‖QuadraticTrial.point u 0‖ ≤ (1 : ℝ)/4 ∧
      ‖fderiv ℝ objective (QuadraticTrial.point u 0)‖ = zeta ∧
      zeta ≤ printedZeta 1 1 (1/2) (1/4) 12 (3/4) / 2 := by
  rw [printed_constants.2, ←norm_deriv_eq_norm_fderiv, deriv_objective]
  norm_num [QuadraticTrial.point, zeta, u]
/-- The whole specified point sequence lies inside the source neighborhood,
so the theorem's excluded outer-region configuration never occurs. -/
theorem never_excluded (k : ℕ) :
    ¬((1 : ℝ)/4 < ‖QuadraticTrial.point u k‖ ∧ epsilon <
      ‖fderiv ℝ objective (QuadraticTrial.point u k)‖ ∧
        ‖fderiv ℝ objective (QuadraticTrial.point u k)‖ ≤ zeta) := by
  have hn : ‖QuadraticTrial.point u k‖ ≤ (1 : ℝ)/4 := by
    unfold QuadraticTrial.point
    split_ifs <;> norm_num [u]
  intro hh
  exact (not_lt_of_ge hn) hh.1
/-- The initial point fails even the nonstrict accuracy test. -/
theorem initial_fails : epsilon < ‖fderiv ℝ objective (QuadraticTrial.point u 0)‖ := by
  rw [initial_region.2.1]
  exact epsilon_bounds.2.1
/-- The accepted endpoint meets the strict source accuracy test. -/
theorem terminal_passes : ‖fderiv ℝ objective (QuadraticTrial.point u 1)‖ < epsilon := by
  rw [←norm_deriv_eq_norm_fderiv, deriv_objective]
  have hs := sqrt_two_bounds
  have hz := zeta_bounds
  have he : zeta/2 ≤ epsilon := by
    unfold epsilon
    exact div_le_div_of_nonneg_left hz.1.le (by positivity) hs.2
  norm_num [QuadraticTrial.point, u, zeta] at he ⊢
  linarith
/-- The printed global-plus-local bound cannot contain a certifying iteration. -/
theorem count_fails : ¬∃ k : ℕ, (k : ℝ) ≤
    kappa * (objective zeta - 0) / zeta ^ (3/2 : ℝ) +
      Real.logb 2 (Real.logb 2 (zeta / epsilon)) + 1 ∧
    ‖fderiv ℝ objective (QuadraticTrial.point u k)‖ < epsilon := by
  rintro ⟨k,hk,hcert⟩
  have hk1 : (k : ℝ) < 1 := hk.trans_lt printed_bound_lt_one
  have hk0 : k = 0 := by exact_mod_cast (show (k : ℝ) = 0 by
    have hnat : k < 1 := by exact_mod_cast hk1
    have : k = 0 := by omega
    simp [this])
  subst k
  linarith [initial_fails]
end CubicRegularization.PhaseCountCounterexample
