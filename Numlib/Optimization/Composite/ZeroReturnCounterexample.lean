import Numlib.Optimization.Composite.SmoothReduction
import Numlib.Optimization.Composite.OuterReturn
import Numlib.Optimization.Regularization.ZeroReturnCounterexample

/-!
# A permitted composite zero exit without approximate optimality

The scalar quadratic, zero residual and nonzero absolute-value outer function
satisfy the global source regularity. At the initial point the true unit test
fails. The literal outer algorithm nevertheless permits step four, whose model
value equals its value at zero. It immediately exits at the initial point,
which fails the requested approximate optimality at every positive radius.
-/

noncomputable section
namespace Composite.ZeroReturnCounterexample
open RegularizationZeroReturn

/-- Fixed legal source settings, independent of any subsequent computation. -/
def settings : Settings 1 1 where
  order_pos := by norm_num
  order_le := by norm_num
  zeta := 1
  zeta_pos := by norm_num
  zeta_le_one := by norm_num
  theta := 1 / 2
  theta_pos := by norm_num
  theta_lt_one := by norm_num
  eta1 := 1 / 4
  eta2 := 3 / 4
  gamma1 := 1 / 2
  gamma2 := 2
  gamma3 := 3
  sigmaMin := 1
  sigmaInitial := 1
  eta1_pos := by norm_num
  eta1_le_eta2 := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_lt_one := by norm_num
  one_lt_gamma2 := by norm_num
  gamma2_lt_gamma3 := by norm_num
  sigmaMin_pos := by norm_num
  sigmaMin_le_initial := by norm_num

/-- Absolute value is nonzero and satisfies all Lipschitz, convexity and
subadditivity assumptions imposed on the outer function. -/
theorem outer_properties : LipschitzWith 1 (abs : ℝ → ℝ) ∧
    ConvexOn ℝ Set.univ (abs : ℝ → ℝ) ∧
    (∀ u v : ℝ, |u + v| ≤ |u| + |v|) ∧ |(0 : ℝ)| = 0 ∧ |(1 : ℝ)| ≠ 0 := by
  refine ⟨?_, ?_, abs_add_le, abs_zero, by norm_num⟩
  · apply lipschitzWith_iff_dist_le_mul.mpr
    intro u v
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using abs_abs_sub_abs_le_abs_sub u v
  · refine ⟨convex_univ, ?_⟩
    intro u hu v hv a b ha hb hab
    simp only [smul_eq_mul]
    calc |a * u + b * v| ≤ |a * u| + |b * v| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

/-- Actual composite Taylor decrements reduce to twice the trial direction. -/
theorem decrement_formula (d : ℝ) :
    decrement objective (fun _ : ℝ => (0 : ℝ)) abs 1 0 d = 2 * d := by
  rw [decrement_zero_residual objective abs_zero, RegularizationZeroReturn.decrement_formula]

/-- Actual composite criticality is twice every nonnegative radius. -/
theorem criticality_formula {δ : ℝ} (hδ : 0 ≤ δ) :
    criticality objective (fun _ : ℝ => (0 : ℝ)) abs 1 0 δ = 2 * δ := by
  rw [criticality_zero_residual objective abs_zero,
    RegularizationZeroReturn.criticality_formula hδ]

/-- The initial computed feasible direction exactly attains the criticality,
strictly fails the source check, and selects its sole order. -/
theorem initial_check : OptimalityCheck objective (fun _ : ℝ => (0 : ℝ)) abs
    settings.zeta (fun _ : Fin 1 => 1 / 2) (fun _ => 1) 0 (fun _ => 1) (some 0) := by
  constructor
  · intro a
    norm_num
  · intro a
    have ha : InexactTrustRegion.modelOrder a = 1 := by
      unfold InexactTrustRegion.modelOrder
      omega
    rw [ha, criticality_formula (by norm_num), decrement_formula]
    norm_num [settings]
  · intro hn
    contradiction
  · intro a ha
    have hj : InexactTrustRegion.modelOrder a = 1 := by
      unfold InexactTrustRegion.modelOrder
      omega
    rw [hj, decrement_formula]
    norm_num [settings]

/-- Step four satisfies the literal outer model-return contract. Its norm
exceeds one, so no model criticality test is required. -/
theorem outer_return : OuterStepReturn objective (fun _ : ℝ => (0 : ℝ)) abs 1
    settings.theta settings.zeta (fun _ : Fin 1 => 1 / 2) 0 4
      settings.sigmaInitial (fun _ => 1) (fun _ => 0) := by
  constructor
  · change regularizedModel objective (fun _ : ℝ => (0 : ℝ)) abs 1 0 1 4 ≤
      regularizedModel objective (fun _ : ℝ => (0 : ℝ)) abs 1 0 1 0
    rw [regularizedModel_zero_residual objective abs_zero,
      regularizedModel_zero_residual objective abs_zero, zero_improvement]
  · intro a
    norm_num
  · intro hs
    norm_num at hs

/-- A faithful initial check and permitted zero-return form an immediate outer
exit before any trial objective evaluation or parameter update. -/
theorem actual_exit : OuterZeroExit objective (fun _ : ℝ => (0 : ℝ)) abs settings
    (fun _ : Fin 1 => 1 / 2) 0 4 (fun _ => 1) (fun _ => 1)
      (fun _ => 1) (fun _ => 0) 0 := by
  refine ⟨by intro a; norm_num, by intro a; norm_num, initial_check, outer_return, ?_⟩
  change regularizedModel objective (fun _ : ℝ => (0 : ℝ)) abs 1 0 1 4 =
    regularizedModel objective (fun _ : ℝ => (0 : ℝ)) abs 1 0 1 0
  rw [regularizedModel_zero_residual objective abs_zero,
    regularizedModel_zero_residual objective abs_zero, zero_improvement]

/-- Global smoothness, actual derivative Lipschitz bounds, outer assumptions
and an objective lower bound all hold for the permitted immediate exit. -/
theorem source_regularity :
    ContDiff ℝ 1 objective ∧ ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ)) ∧
    (∀ x y, ‖iteratedFDeriv ℝ 1 objective x - iteratedFDeriv ℝ 1 objective y‖ ≤
      1 * ‖x - y‖) ∧
    (∀ x y, ‖iteratedFDeriv ℝ 1 (fun _ : ℝ => (0 : ℝ)) x -
      iteratedFDeriv ℝ 1 (fun _ : ℝ => (0 : ℝ)) y‖ ≤ 1 * ‖x - y‖) ∧
    (∀ x, 0 ≤ objective x + |(0 : ℝ)|) ∧
    LipschitzWith 1 (abs : ℝ → ℝ) ∧ ConvexOn ℝ Set.univ (abs : ℝ → ℝ) ∧
    (∀ u v : ℝ, |u + v| ≤ |u| + |v|) ∧ |(0 : ℝ)| = 0 := by
  refine ⟨smooth 1, contDiff_const, ?_, ?_, ?_, outer_properties.1,
    outer_properties.2.1, outer_properties.2.2.1, outer_properties.2.2.2.1⟩
  · intro x y
    simpa only [one_mul] using derivative_lipschitz x y
  · intro x y
    simp
  · intro x
    simpa only [abs_zero, add_zero] using nonneg x

/-- No positive radii certify the sole point produced by the immediate exit. -/
theorem no_produced_certificate : ¬∃ (z : ℝ) (δ : Fin 1 → ℝ),
    actual_exit.producedPoint z ∧
      OptimalityAt objective (fun _ : ℝ => (0 : ℝ)) abs (fun _ => 1 / 2) z δ := by
  rintro ⟨z, δ, hz, hδ, hc⟩
  rw [actual_exit.producedPoint_iff] at hz
  subst z
  have hh := hc 0
  have hpos := (hδ 0).1
  have hj : InexactTrustRegion.modelOrder (0 : Fin 1) = 1 := by rfl
  rw [hj, criticality_formula hpos.le] at hh
  norm_num at hh
  linarith

/-- The return permitted by the outer algorithm cannot satisfy any positive
fraction of the global model gap of the detailed solver. -/
theorem not_detailed_return : ¬∃ μ : ℝ, 0 < μ ∧
    ModelDecrease.ApproximateGlobalStep
      (regularizedModel objective (fun _ : ℝ => (0 : ℝ)) abs 1 0 1) μ 4 := by
  have he : regularizedModel objective (fun _ : ℝ => (0 : ℝ)) abs 1 0 1 =
      HighOrderRegularization.model objective 1 0 1 := by
    funext s
    exact regularizedModel_zero_residual objective abs_zero 1 0 1 s
  rw [he]
  exact not_positive_fraction

/-- The literal outer algorithm obeys every global problem assumption, uses
unit radii for its convex first-order case, and exits without producing any
point satisfying the requested approximate optimality.
-/
theorem verified_counterexample :
    ContDiff ℝ 1 objective ∧ ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ)) ∧
    (∀ x y, ‖iteratedFDeriv ℝ 1 objective x - iteratedFDeriv ℝ 1 objective y‖ ≤
      1 * ‖x - y‖) ∧
    (∀ x y, ‖iteratedFDeriv ℝ 1 (fun _ : ℝ => (0 : ℝ)) x -
      iteratedFDeriv ℝ 1 (fun _ : ℝ => (0 : ℝ)) y‖ ≤ 1 * ‖x - y‖) ∧
    (∀ x, 0 ≤ objective x + |(0 : ℝ)|) ∧
    LipschitzWith 1 (abs : ℝ → ℝ) ∧ ConvexOn ℝ Set.univ (abs : ℝ → ℝ) ∧
    (∀ u v : ℝ, |u + v| ≤ |u| + |v|) ∧ |(0 : ℝ)| = 0 ∧
    OuterZeroExit objective (fun _ : ℝ => (0 : ℝ)) abs settings
      (fun _ : Fin 1 => 1 / 2) 0 4 (fun _ => 1) (fun _ => 1)
        (fun _ => 1) (fun _ => 0) 0 ∧
    ¬∃ (z : ℝ) (δ : Fin 1 → ℝ), actual_exit.producedPoint z ∧
      OptimalityAt objective (fun _ : ℝ => (0 : ℝ)) abs (fun _ => 1 / 2) z δ := by
  rcases source_regularity with ⟨hf, hc, hLf, hLc, hlow, hh, hconv, hsub, hz⟩
  exact ⟨hf, hc, hLf, hLc, hlow, hh, hconv, hsub, hz, actual_exit,
    no_produced_certificate⟩

end Composite.ZeroReturnCounterexample
