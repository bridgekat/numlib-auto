import Numlib.Optimization.Regularization.HighOrder.CriticalityRun
import Numlib.Analysis.Calculus.TaylorModel.Scalar
import Numlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Numlib.Optimization.HighOrder.Criticality

/-!
# An actual nonterminating check after a true criticality certificate

The literal Step1 check uses a relative criticality direction and can select a
trial even after true epsilon-criticality holds. A tiny positive-fraction model
solve is allowed. Its actual finite execution refutes the printed implication
from nontermination to a uniform step-power obstruction.
-/

namespace HighOrderRegularization.ObstructionCounterexample
open InexactTrustRegion

/-- A globally bounded-below quadratic objective with unit Lipschitz derivative. -/
noncomputable def objective (x : ℝ) : ℝ := x ^ 2 / 2

/-- The actual scalar derivative of the quadratic objective. -/
theorem deriv_objective (x : ℝ) : deriv objective x = x := by
  have hh : HasDerivAt objective x x := by
    convert ((hasDerivAt_id x).pow 2).div_const 2 using 1 <;>
      (try funext y) <;> simp [objective]
  exact hh.deriv

/-- Every scalar first-order Taylor decrement is its actual derivative times
minus the displacement. -/
theorem decrement_one (f : ℝ → ℝ) (x s : ℝ) :
    TaylorModel.decrement f 1 x s = -(deriv f x) * s := by
  rw [TaylorModel.decrement_eq, TaylorModel.eval_eq_sum_iteratedDeriv]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDeriv_zero,
    iteratedDeriv_one]
  norm_num
  ring

/-- At a nonnegative scalar derivative, the unit Taylor criticality equals
that actual derivative and is attained by the direction minus one. -/
theorem criticality_one (f : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ deriv f x) :
    TaylorModel.criticality f 1 x 1 = deriv f x := by
  apply le_antisymm
  · obtain ⟨s, hs, he⟩ := TaylorModel.exists_decrement_eq_criticality f 1 x zero_le_one
    rw [←he, decrement_one]
    have hh : -(1 : ℝ) ≤ s := (abs_le.mp hs).1
    nlinarith
  · have hh := TaylorModel.decrement_le_criticality f 1 x
      (s := -1) (by norm_num : ‖(-1 : ℝ)‖ ≤ 1)
    simpa only [decrement_one, mul_neg_one, neg_neg] using hh

/-- The actual degree-one regularized model is a positive quadratic. -/
theorem model_formula (x s : ℝ) :
    model objective 1 x 1 s = objective x + x * s + s ^ 2 / 2 := by
  rw [model_eq]
  have he : TaylorModel.eval objective 1 x s = objective x + x * s := by
    have hh := decrement_one objective x s
    rw [TaylorModel.decrement_eq, deriv_objective] at hh
    linarith
  rw [he]
  norm_num [Real.norm_eq_abs, sq_abs]
  ring

/-- The actual scalar derivative of the current regularized model. -/
theorem deriv_model (x s : ℝ) : deriv (model objective 1 x 1) s = x + s := by
  have he : model objective 1 x 1 = fun u => objective x + x * u + u ^ 2 / 2 :=
    funext (model_formula x)
  rw [he]
  have hh : HasDerivAt (fun u : ℝ => objective x + x * u + u ^ 2 / 2) (x + s) s := by
    convert ((hasDerivAt_const s (objective x)).add
      ((hasDerivAt_id s).const_mul x)).add (((hasDerivAt_id s).pow 2).div_const 2) using 1 <;>
      (first | (funext y; rfl) | norm_num)
  exact hh.deriv

/-- The chosen tiny trial is a genuine positive-fraction approximate global
solve and satisfies every actual first-order unit-radius Step2 test. -/
theorem step_computation {x : ℝ} (hx : (7 : ℝ) / 10 ≤ x ∧ x ≤ 4 / 5) :
    ModelSolve.StepComputation (model objective 1 x 1) (modelOrder : Fin 1 → ℕ)
      (9 / 10) (1 / 2) (fun _ => 9 / 10) (-(1 : ℝ) / 1000000) (fun _ => 1) := by
  refine ⟨⟨1 / 1000000, by norm_num, by norm_num, ?_⟩, Or.inr ?_⟩
  · intro z
    simp only [model_formula]
    norm_num
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (z + x)]
  · refine ⟨by norm_num, (fun _ _ => -(1 : ℝ) / 1000000), (fun _ _ => 0),
      (fun _ => 0), (fun _ => -(1 : ℝ) / 2), ?_⟩
    intro a
    have ha : modelOrder a = 1 := by have := a.isLt; unfold modelOrder; omega
    refine ⟨fun _ ht => (Nat.not_lt_zero _ ht).elim,
      ⟨fun _ ht => (Nat.not_lt_zero _ ht).elim,
        fun _ ht => (Nat.not_lt_zero _ ht).elim,
        fun _ ht => (Nat.not_lt_zero _ ht).elim⟩, fun _ => rfl, by simp, by norm_num, ?_, ?_⟩
    · rw [ha, criticality_one _ _ (by rw [deriv_model]; linarith), decrement_one,
        deriv_model]
      norm_num
      nlinarith
    · rw [ha, decrement_one, deriv_model]
      norm_num
      linarith

/-- The fixed legal algorithm settings have a genuine positive stopping margin
between the relative objective test and the model test. -/
noncomputable def settings : HighOrderRegularization.Settings 1 1 where
  order_pos := by norm_num
  order_le := le_rfl
  zeta := 1 / 2
  zeta_pos := by norm_num
  zeta_le_one := by norm_num
  theta := 9 / 10
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
  sigmaMin_le_initial := le_rfl

/-- Three distinct consecutive points and the actual objective-based ratios
of two tiny successful trials; every literal objective check selects a trial. -/
noncomputable def data : HighOrderRegularization.ExecutionData ℝ 1 where
  point := fun k => 3 / 4 - (k : ℝ) / 1000000
  step := fun _ => -(1 : ℝ) / 1000000
  parameter := fun _ => 1
  ratio := fun k => ratio objective 1 (3 / 4 - (k : ℝ) / 1000000) (-(1 : ℝ) / 1000000)
  radius := fun _ _ => 1
  solvedRadius := fun _ _ => 1
  direction := fun _ _ => -1
  selected := fun _ => some 0

/-- Every point in the required finite prefix lies in the fixed positive interval. -/
theorem point_mem {k : ℕ} (hk : k ≤ 2) :
    (7 : ℝ) / 10 ≤ data.point k ∧ data.point k ≤ 4 / 5 := by
  have hkR : (k : ℝ) ≤ 2 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  dsimp [data]
  constructor <;> linarith

/-- Both tiny objective trials are actually very successful, using the true
quadratic objective values and their true linear Taylor predictions. -/
theorem ratio_lower {x : ℝ} (hx : (7 : ℝ) / 10 ≤ x ∧ x ≤ 4 / 5) :
    (3 : ℝ) / 4 ≤ ratio objective 1 x (-(1 : ℝ) / 1000000) := by
  rw [ratio, decrement_one, deriv_objective]
  have hd : 0 < -x * (-(1 : ℝ) / 1000000) := by linarith
  apply (le_div_iff₀ hd).mpr
  dsimp [objective]
  nlinarith

/-- The literal first-order objective check still selects a trial at every
point, despite all points already satisfying the true epsilon certificate. -/
theorem check {x : ℝ} (hx : (7 : ℝ) / 10 ≤ x ∧ x ≤ 4 / 5) :
    OptimalityCheck objective (1 / 2) (fun _ : Fin 1 => 9 / 10) (fun _ => 1)
      x (fun _ => -1) (some 0) := by
  have hd : 0 ≤ deriv objective x := by rw [deriv_objective]; linarith
  have ha : ∀ a : Fin 1, modelOrder a = 1 := by
    intro a
    have := a.isLt
    unfold modelOrder
    omega
  refine ⟨fun _ _ => by norm_num, ?_, ?_, ?_, ?_⟩
  · intro a _
    rw [ha a, criticality_one _ _ hd, decrement_one, deriv_objective]
    linarith
  · intro hn
    contradiction
  · intro a _
    rw [ha a, decrement_one, deriv_objective]
    norm_num
    linarith
  · intro a _ b hb
    have hae : a = 0 := Fin.eq_zero a
    have hbe : b = 0 := Fin.eq_zero b
    omega

/-- The actual model/ratio/parameter/point component of the finite counterexample. -/
theorem modelTrace : ModelTrace objective 1 data.point data.step data.parameter data.ratio
    settings.eta1 settings.eta2 settings.gamma1 settings.gamma2 settings.gamma3
      settings.sigmaMin 2 := by
  refine ⟨by norm_num, ?_, ?_, fun _ _ => rfl, ?_⟩
  · refine ⟨by norm_num [settings], by norm_num [settings, data], by norm_num [settings],
      by norm_num [settings], by norm_num [settings], by norm_num [settings],
      by norm_num [settings], by norm_num [settings], by norm_num [settings], ?_⟩
    intro k hk
    have hr := ratio_lower (point_mem hk.le)
    change settings.eta2 ≤ data.ratio k at hr
    rw [ite_eq_left hr]
    norm_num [settings, data]
  · intro k hk
    have hx := point_mem hk.le
    dsimp only [data] at hx ⊢
    rw [model_formula, model_formula]
    norm_num
    linarith
  · intro k hk
    have hr := ratio_lower (point_mem hk.le)
    change (3 : ℝ) / 4 ≤ data.ratio k at hr
    have ha : settings.eta1 ≤ data.ratio k := by change (1 : ℝ) / 4 ≤ _; linarith
    rw [ite_eq_left ha]
    dsimp only [data]
    push_cast
    ring

/-- All primitive fields of an actual exact ARqp execution hold through two
trials and the third nonterminating objective check. No step lower bound or
criticality failure is encoded in the execution. -/
theorem run : HighOrderRegularization.Run objective settings (fun _ => 9 / 10) data 2 where
  accuracy_pos := fun _ => by norm_num
  accuracy_le_one := fun _ => by norm_num
  initial_parameter := rfl
  initial_radii := fun _ => ⟨zero_lt_one, le_rfl⟩
  modelTrace := modelTrace
  check := fun k hk => check (point_mem hk)
  step_two := fun k hk _ => step_computation (point_mem hk)
  continues := fun _ _ => by simp only [data, ne_eq, reduceCtorEq, not_false_eq_true]
  radius_update := fun _ _ => by
    funext a
    norm_num [data, settings, ratio, decrement_one, deriv_objective, objective]

/-- The actual objective satisfies global finite smoothness, a unit Lipschitz
first derivative and a global lower bound. -/
theorem objective_regularity : ContDiff ℝ 1 objective ∧
    (∀ x y, ‖iteratedFDeriv ℝ 1 objective x - iteratedFDeriv ℝ 1 objective y‖ ≤
      (1 : ℝ) * ‖x - y‖) ∧ ∀ x, 0 ≤ objective x := by
  refine ⟨by unfold objective; fun_prop, ?_, fun x => div_nonneg (sq_nonneg x) (by norm_num)⟩
  intro x y
  rw [norm_iteratedFDeriv_sub_eq_norm_iteratedDeriv_sub]
  simp only [iteratedDeriv_one, deriv_objective, one_mul, le_refl]

/-- Both actual trials are successful and the next check is still selected;
the exact-zero model-decrease exit does not occur there either. -/
theorem successful_nontermination : settings.eta1 ≤ data.ratio 0 ∧
    data.selected 1 ≠ none ∧
      model objective 1 (data.point 1) (data.parameter 1) 0 ≠
        model objective 1 (data.point 1) (data.parameter 1) (data.step 1) := by
  have hr := ratio_lower (point_mem (k := 0) (by omega))
  have hs := modelTrace.improvement 1 (by omega)
  refine ⟨?_, by simp [data], hs.ne'⟩
  change (1 : ℝ) / 4 ≤ data.ratio 0
  change (3 : ℝ) / 4 ≤ data.ratio 0 at hr
  linarith

/-- The printed parameter upper bound is twelve, while the actual parameter
is one. The larger printed cap is retained in every counterexample comparison. -/
theorem printed_cap : max (data.parameter 0)
    (settings.gamma3 * (1 : ℝ) / (1 - settings.eta2)) = 12 := by
  norm_num [settings, data]

/-- The actual finite nonterminating run violates the full printed step-power
obstruction at iteration zero, even with its larger printed parameter cap. -/
theorem obstruction_fails :
    let S := max (data.parameter 0) (settings.gamma3 * (1 : ℝ) / (1 - settings.eta2))
    ¬∃ a : Fin 1, (1 - settings.theta) * (9 / 10 : ℝ) *
      data.radius 1 a ^ modelOrder a / (modelOrder a).factorial ≤
      (1 + S) * ∑ i ∈ Finset.range (modelOrder a),
        data.radius 1 a ^ (i + 1) * ‖data.step 0‖ ^ (1 - (i + 1) + 1) /
          (i + 1).factorial := by
  dsimp only
  rw [printed_cap]
  intro ⟨a, ha⟩
  have hae : modelOrder a = 1 := by have := a.isLt; unfold modelOrder; omega
  norm_num [hae, data, settings] at ha

/-- Nevertheless, the next iterate already satisfies true epsilon criticality.
This is the exact gap between a true certificate and the relative literal test. -/
theorem next_true_optimality : TaylorModel.criticality objective 1 (data.point 1) 1 ≤
    (9 : ℝ) / 10 := by
  rw [criticality_one _ _ (by rw [deriv_objective]; norm_num [data]), deriv_objective]
  norm_num [data]

/-- The low-order printed step bound also fails, with p=q=j=1, legal unit
radii and the exact printed parameter cap. -/
theorem step_bound_fails :
    let S := max (data.parameter 0) (settings.gamma3 * (1 : ℝ) / (1 - settings.eta2))
    ‖data.step 0‖ < (1 - settings.theta) / (2 * (1 + S)) * (9 / 10 : ℝ) := by
  dsimp only
  rw [printed_cap]
  norm_num [data, settings]

/-- The literal p=q=1 model and accepted-function decrease bounds both fail.
Their printed coefficient is sigma_min/2 times the squared step coefficient. -/
theorem decrease_bounds_fail :
    let S := max (data.parameter 0) (settings.gamma3 * (1 : ℝ) / (1 - settings.eta2))
    let κ := settings.sigmaMin / 2 * ((1 - settings.theta) / (2 * (1 + S))) ^ 2
    TaylorModel.decrement objective 1 (data.point 0) (data.step 0) <
        κ * (9 / 10 : ℝ) ^ 2 ∧
      objective (data.point 0) - objective (data.point 1) <
        settings.eta1 * κ * (9 / 10 : ℝ) ^ 2 := by
  dsimp only
  rw [printed_cap]
  rw [decrement_one, deriv_objective]
  norm_num [data, settings, objective]

end HighOrderRegularization.ObstructionCounterexample
