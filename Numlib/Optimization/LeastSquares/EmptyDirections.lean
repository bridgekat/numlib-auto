import Numlib.Optimization.Regularization.HighOrder.EmptyDirections
import Numlib.Optimization.LeastSquares.Stopping
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# An admissible empty-direction obstruction for ARpLE

A globally C6 positive objective F realizes an initial linear jet and a flat
terminal jet. The positive smooth residual sqrt(2F) has actual power objective
Phi2=F. Its genuine AR6 trial has ratio two and empty inherited directions.
The residual stays above one; literal stopping fails at the flat endpoint,
where strict model improvement is impossible. The data p=6, ell=2 and i=3
satisfy the third-order exponent condition of Theorem 5.1.7.
-/

namespace LeastSquares.EmptyDirections
open Polynomial HighOrderRegularization
open HighOrderRegularization.EmptyDirections (jet point)

/-- A fixed sixth-order Hermite bound for the initial linear jet and flat terminal jet. -/
theorem jet_residual_six {k j : ℕ} (hk : k < 1) (hj : j ≤ 6) :
    |jet (k + 1) j - (derivative^[j] (Hermite.initialPolynomial 6 (jet k))).eval 1| ≤
      4 * (1 : ℝ) ^ (6 - j + 1) := by
  have hk0 : k = 0 := by omega
  subst k
  have hpoly : Hermite.initialPolynomial 6 (jet 0) = C 4 - C 2 * X := by
    norm_num [Hermite.initialPolynomial, Hermite.jetPoly, Finset.sum_range_succ, jet]
    ring
  rw [hpoly]
  interval_cases j <;> norm_num [jet, Function.iterate_succ_apply]

/-- The shifted interpolation jets have a positive constant terminal value. -/
def shiftedJet (c : ℝ) (k j : ℕ) : ℝ := if j = 0 then c + jet k 0 else jet k j

/-- A uniformly positive globally C6 objective realizes the shifted two-point
jets and has Lipschitz sixth derivative. -/
theorem exists_positive_objective :
    ∃ (f : ℝ → ℝ) (c L : ℝ), 1 < c ∧ 1 ≤ L ∧ ContDiff ℝ 6 f ∧
      (∀ x, 1 ≤ f x) ∧
      (∀ x y, ‖iteratedFDeriv ℝ 6 f x - iteratedFDeriv ℝ 6 f y‖ ≤ L * ‖x - y‖) ∧
      (∀ k : ℕ, k ≤ 1 → ∀ j ≤ 6, iteratedDeriv j f (k : ℝ) = shiftedJet c k j) := by
  obtain ⟨L,hL,B,hB,H⟩ := Hermite.exists_uniform_interpolant 6 4 (by norm_num)
  obtain ⟨f,hf,hLip,hjets,hbound⟩ := H 1 (by norm_num) (fun k => (k : ℝ)) jet
    (by intro i j hij _; exact_mod_cast hij)
    (by intro k hk j hj; simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left]
      using jet_residual_six hk hj)
  have hdata : ((∀ k < 1, ∀ j ≤ 6, |jet k j| ≤ 4) ∧
      ∀ k < 1, (k + 1 : ℕ) - (k : ℝ) ≤ 4) := by
    constructor
    · intro k hk j hj
      have hk0 : k = 0 := by omega
      subst k
      interval_cases j <;> norm_num [jet]
    · intro k _; simp
  refine ⟨fun x => (B + 1) + f x, B + 1, max 1 L, by linarith,
    le_max_left _ _, contDiff_const.add hf, ?_, ?_, ?_⟩
  · intro x
    have hb := hbound hdata 0 (by omega) x
    simp only [iteratedDeriv_zero] at hb
    linarith [(abs_le.mp hb).1]
  · intro x y
    rw [norm_iteratedFDeriv_sub_eq_norm_iteratedDeriv_sub,
      iteratedDeriv_const_add (by omega), iteratedDeriv_const_add (by omega)]
    exact (hLip.norm_sub_le x y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  · intro k hk j hj
    by_cases hj0 : j = 0
    · subst j
      simpa only [iteratedDeriv_zero, shiftedJet, ite_true] using
        congrArg (fun a : ℝ => B + 1 + a) (hjets k hk 0 (by omega))
    · rw [iteratedDeriv_const_add (by omega)]
      simpa only [shiftedJet, ite_eq_right hj0] using hjets k hk j hj

/-- A smooth positive scalar residual whose squared-norm objective is the prescribed positive f. -/
noncomputable def residual (f : ℝ → ℝ) (x : ℝ) : ℝ := Real.sqrt (2 * f x)

/-- The residual is C6 because its square-root argument stays strictly positive. -/
theorem contDiff_residual {f : ℝ → ℝ} (hf : ContDiff ℝ 6 f) (hpos : ∀ x, 0 < f x) :
    ContDiff ℝ 6 (residual f) := by
  exact (contDiff_const.mul hf).sqrt (fun x => ne_of_gt (mul_pos (by norm_num) (hpos x)))

/-- The actual residual-power objective is exactly the constructed positive objective. -/
theorem powerObjective_residual {f : ℝ → ℝ} (hpos : ∀ x, 0 ≤ f x) :
    powerObjective (residual f) 2 = f := by
  funext x
  rw [powerObjective_two, residual, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (mul_nonneg (by norm_num) (hpos x))]
  ring

/-- The actual sixth-order initial model is the linear Taylor model plus a seventh norm power. -/
theorem model_initial {f : ℝ → ℝ} {c : ℝ}
    (hj : ∀ j ≤ 6, iteratedDeriv j f 0 = shiftedJet c 0 j) (s : ℝ) :
    model f 6 0 1440 s = c + 4 - 2 * s + (2 / 7 : ℝ) * |s| ^ 7 := by
  rw [model_eq, TaylorModel.eval_eq_sum_iteratedDeriv]
  norm_num [Finset.sum_range_succ, hj, shiftedJet, jet]
  ring

/-- A polynomial representing the initial actual model locally at the unit step. -/
noncomputable def initialPolynomial (c : ℝ) : ℝ[X] :=
  C (c + 4) - C 2 * X + C (2 / 7) * X ^ 7

/-- Near the unit step, the actual seventh-norm-power model equals its polynomial expression. -/
theorem model_initial_eventuallyEq {f : ℝ → ℝ} {c : ℝ}
    (hj : ∀ j ≤ 6, iteratedDeriv j f 0 = shiftedJet c 0 j) :
    model f 6 0 1440 =ᶠ[nhds 1] (initialPolynomial c).eval := by
  filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) < 1)] with s hs
  rw [model_initial hj, abs_of_pos hs]
  simp [initialPolynomial]

/-- The actual model has zero first derivative and Hessian twelve at the unit step. -/
theorem model_derivatives {f : ℝ → ℝ} {c : ℝ}
    (hj : ∀ j ≤ 6, iteratedDeriv j f 0 = shiftedJet c 0 j) :
    iteratedDeriv 1 (model f 6 0 1440) 1 = 0 ∧
      iteratedDeriv 2 (model f 6 0 1440) 1 = 12 := by
  constructor
  · rw [(model_initial_eventuallyEq hj).iteratedDeriv_eq 1,
      Polynomial.iteratedDeriv_eval]
    norm_num [initialPolynomial, Function.iterate_succ_apply]
  · rw [(model_initial_eventuallyEq hj).iteratedDeriv_eq 2,
      Polynomial.iteratedDeriv_eval]
    norm_num [initialPolynomial, Function.iterate_succ_apply]

/-- The inherited actual small-model-curvature direction set is empty. -/
theorem smallModelDirections_empty {f : ℝ → ℝ} {c : ℝ}
    (hj : ∀ j ≤ 6, iteratedDeriv j f 0 = shiftedJet c 0 j) :
    smallModelDirections f 6 0 1 1440 1 = ∅ := by
  ext v
  simp only [mem_smallModelDirections_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hv,hsmall⟩
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, (model_derivatives hj).2] at hsmall
  have hv2 : v ^ 2 = 1 := by
    have hsq := congrArg (fun t : ℝ => t ^ 2) hv
    simpa only [Real.norm_eq_abs, sq_abs, one_pow] using hsq
  norm_num [Fin.prod_const, hv2] at hsmall

/-- All actual model stationarity conditions hold at the proposed unit step. -/
theorem stepConditions {f : ℝ → ℝ} {c : ℝ}
    (hj : ∀ j ≤ 6, iteratedDeriv j f 0 = shiftedJet c 0 j) :
    StepConditions f 6 0 1 1440 1 1 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [←norm_deriv_eq_norm_fderiv, ←iteratedDeriv_one, (model_derivatives hj).1]
    norm_num
  · intro v _
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, (model_derivatives hj).2]
    simp only [Fin.prod_const, smul_eq_mul]
    norm_num
    nlinarith [sq_nonneg v]
  · intro v hv
    rw [smallModelDirections_empty hj] at hv
    exact False.elim hv
end LeastSquares.EmptyDirections

namespace LeastSquares.EmptyDirections
open HighOrderRegularization
open HighOrderRegularization.EmptyDirections (jet point)

/-- The actual initial-to-terminal objective ratio is two, unaffected by the positive shift. -/
theorem actual_ratio {f : ℝ → ℝ} {c : ℝ}
    (hjets : ∀ k : ℕ, k ≤ 1 → ∀ j ≤ 6, iteratedDeriv j f (k : ℝ) = shiftedJet c k j) :
    ratio f 6 0 1 = 2 := by
  have hj0 : ∀ j ≤ 6, iteratedDeriv j f 0 = shiftedJet c 0 j := by
    simpa using hjets 0 (by omega)
  have h0 : f 0 = c + 4 := by simpa [shiftedJet, jet] using hjets 0 (by omega) 0 (by omega)
  have h1 : f 1 = c := by simpa [shiftedJet, jet] using hjets 1 le_rfl 0 (by omega)
  rw [ratio_eq, TaylorModel.decrement_eq, TaylorModel.eval_eq_sum_iteratedDeriv]
  norm_num [Finset.sum_range_succ, hj0, shiftedJet, jet, h0, h1]

/-- A genuine legal sixth-order accepted trial with the actual objective-based ratio. -/
theorem modelTrace {f : ℝ → ℝ} {c : ℝ}
    (hjets : ∀ k : ℕ, k ≤ 1 → ∀ j ≤ 6, iteratedDeriv j f (k : ℝ) = shiftedJet c k j) :
    ModelTrace f 6 point (fun _ => 1) (fun _ => 1440) (fun _ => 2)
      (1 / 4) (3 / 4) (1 / 2) 2 3 1440 1 := by
  have hj0 : ∀ j ≤ 6, iteratedDeriv j f 0 = shiftedJet c 0 j := by
    simpa using hjets 0 (by omega)
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, le_refl _, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    intro i _; norm_num
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    change model f 6 0 1440 1 < model f 6 0 1440 0
    rw [model_initial hj0, model_initial hj0]
    norm_num
    linarith
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    exact (actual_ratio hjets).symm
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    norm_num [point]

/-- A flat positive terminal jet admits no further strict model improvement. -/
theorem no_next_improvement {f : ℝ → ℝ} {c : ℝ}
    (hj : ∀ j ≤ 6, iteratedDeriv j f 1 = shiftedJet c 1 j) {σ : ℝ} (hσ : 0 ≤ σ) :
    ¬ ∃ s : ℝ, model f 6 1 σ s < model f 6 1 σ 0 := by
  rintro ⟨s,hs⟩
  rw [model_eq, model_eq, TaylorModel.eval_eq_sum_iteratedDeriv,
    TaylorModel.eval_eq_sum_iteratedDeriv] at hs
  norm_num [Finset.sum_range_succ, hj, shiftedJet, jet] at hs
  have hh : 0 ≤ σ / 5040 * |s| ^ 7 := by positivity
  linarith

/-- The residual stays above the global termination tolerance one everywhere. -/
theorem residual_norm_gt_one {f : ℝ → ℝ} (hpos : ∀ x, 1 ≤ f x) (x : ℝ) :
    1 < ‖residual f x‖ := by
  rw [residual, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hs := Real.sq_sqrt (show 0 ≤ 2 * f x by linarith [hpos x])
  nlinarith [Real.sqrt_nonneg (2 * f x), hpos x]

/-- The initial normalized gradient is positive and uses the actual residual-power objective. -/
theorem initial_measure_pos {f : ℝ → ℝ} {c : ℝ} (hpos : ∀ x, 1 ≤ f x)
    (hj : ∀ j ≤ 6, iteratedDeriv j f 0 = shiftedJet c 0 j) :
    0 < firstMeasure (residual f) 2 0 := by
  have hg : deriv f 0 = -2 := by
    simpa [shiftedJet, jet, iteratedDeriv_one] using hj 1 (by omega)
  rw [firstMeasure, powerObjective_residual (fun x => (hpos x).trans' zero_le_one),
    ← norm_deriv_eq_norm_fderiv, hg]
  apply div_pos (by norm_num)
  exact derivativeWeight_pos _ _ (by
    have hh := residual_norm_gt_one hpos 0
    exact norm_pos_iff.mp (by linarith))

/-- The order-six residual-power choice satisfies the third-order source admissibility rule. -/
theorem source_exponent_choice :
    1 < (2 : ℝ) ∧ (2 : ℝ) = (6 : ℝ) / 3 ∧ Real.logb 2 (6 - 2 : ℝ) < 3 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  apply (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) (by norm_num)).mpr
  norm_num

/-- A genuine positive smooth residual makes the literal ARpLE algorithm get stuck under
its admissible `p=6,ℓ=2,i=3` source settings. All actual model tests and ratios are derived;
the global residual test fails, the inherited direction set is empty, the literal terminal
guard fails, and no subsequent strict model improvement exists. -/
theorem exists_stuck_execution :
    ∃ (r : ℝ → ℝ) (L ε₁ : ℝ), 1 ≤ L ∧ 0 < ε₁ ∧ ε₁ ≤ 1 ∧
      ContDiff ℝ 6 r ∧ ContDiff ℝ 6 (powerObjective r 2) ∧
      (∀ x, 1 < ‖r x‖) ∧
      (∀ x y, ‖iteratedFDeriv ℝ 6 (powerObjective r 2) x -
        iteratedFDeriv ℝ 6 (powerObjective r 2) y‖ ≤ L * ‖x - y‖) ∧
      ModelTrace (powerObjective r 2) 6 point (fun _ => 1) (fun _ => 1440) (fun _ => 2)
        (1 / 4) (3 / 4) (1 / 2) 2 3 1440 1 ∧
      StepConditions (powerObjective r 2) 6 0 1 1440 1 1 1 ∧
      smallModelDirections (powerObjective r 2) 6 0 1 1440 1 = ∅ ∧
      (∀ (μ : ℝ) (M : Set ℝ), ¬ literalFiniteStop r 2 0 μ M 1 ε₁ 1 1) ∧
      ¬ literalFiniteStop r 2 1 0 ∅ 1 ε₁ 1 1 ∧
      finiteStop r 2 1 0 ∅ 1 ε₁ 1 1 ∧
      SecondOrderTrustRegion.IsLeastEigenpair (powerObjective r 2) 1 0 1 ∧
      (∀ σ : ℝ, 0 ≤ σ → ¬ ∃ s : ℝ,
        model (powerObjective r 2) 6 1 σ s < model (powerObjective r 2) 6 1 σ 0) := by
  obtain ⟨f,c,L,hc,hL,hf,hpos,hLip,hjets⟩ := exists_positive_objective
  have hj0 : ∀ j ≤ 6, iteratedDeriv j f 0 = shiftedJet c 0 j := by
    simpa using hjets 0 (by omega)
  have hj1 : ∀ j ≤ 6, iteratedDeriv j f 1 = shiftedJet c 1 j := by
    simpa using hjets 1 le_rfl
  have hpos0 : ∀ x, 0 ≤ f x := fun x => zero_le_one.trans (hpos x)
  have hobj := powerObjective_residual hpos0
  have hr : ∀ x, 1 < ‖residual f x‖ := residual_norm_gt_one hpos
  have hψ := initial_measure_pos hpos hj0
  let ε₁ := min 1 (firstMeasure (residual f) 2 0 / 2)
  have hε₁ : 0 < ε₁ := lt_min zero_lt_one (by linarith)
  have hε₁1 : ε₁ ≤ 1 := min_le_left _ _
  have hεψ : ε₁ < firstMeasure (residual f) 2 0 :=
    (min_le_right _ _).trans_lt (by linarith)
  have hgrad1 : deriv f 1 = 0 := by
    simpa [shiftedJet, jet, iteratedDeriv_one] using hj1 1 (by omega)
  have hhess1 : iteratedDeriv 2 f 1 = 0 := by
    simpa [shiftedJet, jet] using hj1 2 (by omega)
  refine ⟨residual f, L, ε₁, hL, hε₁, hε₁1,
    contDiff_residual hf (fun x => zero_lt_one.trans_le (hpos x)),
    hobj.symm ▸ hf, hr, hobj.symm ▸ hLip, hobj.symm ▸ modelTrace hjets,
    hobj.symm ▸ stepConditions hj0, hobj.symm ▸ smallModelDirections_empty hj0,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro μ M
    simp only [literalFiniteStop]
    rintro (hh | ⟨hh,_⟩)
    · exact (not_le.mpr (hr 0)) hh
    · exact (not_le.mpr hεψ) hh
  · rintro (hh | ⟨_, hh | ⟨_, hM, _⟩⟩)
    · exact (not_le.mpr (hr 1)) hh
    · norm_num [secondMeasure] at hh
    · exact Set.not_nonempty_empty hM
  · apply Or.inr
    refine ⟨?_, Or.inr ⟨?_, by simp⟩⟩
    · rw [firstMeasure, hobj, ←norm_deriv_eq_norm_fderiv, hgrad1]
      simpa using hε₁.le
    · simp [secondMeasure]
  · rw [hobj]
    simpa only [hhess1] using CurvatureSharpness.leastEigenpair f 1
  · intro σ hσ
    rw [hobj]
    exact no_next_improvement hj1 hσ
end LeastSquares.EmptyDirections
