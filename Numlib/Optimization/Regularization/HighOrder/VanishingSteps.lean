import Numlib.Optimization.Regularization.HighOrder.ObstructionCounterexample
import Numlib.Optimization.HighOrder.ConstrainedCriticality
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# An infinite literal run with vanishing successful decreases

A fixed quadratic objective admits a single infinite primitive ARqp execution
whose successful decreases tend to zero. Every finite prefix uses actual
Taylor tests, positive-fraction global model solves, ratios and updates. Thus
no positive uniform per-success decrease holds after true epsilon criticality
has already been reached, although the computed relative check keeps failing.
-/

namespace HighOrderRegularization.VanishingSteps
open InexactTrustRegion ObstructionCounterexample

/-- A decreasing positive sequence of trial magnitudes. -/
noncomputable def magnitude (k : ℕ) : ℝ := (1 / 2000000) * (1 / 2 : ℝ) ^ k

/-- Every trial magnitude is positive and uniformly tiny. -/
theorem magnitude_mem (k : ℕ) : 0 < magnitude k ∧ magnitude k ≤ 1 / 1000000 := by
  have hpow : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  constructor
  · unfold magnitude; positivity
  · unfold magnitude; nlinarith

/-- A tiny model return satisfies all primitive model tests with a positive
fraction of global decrease; the fraction may depend on the call. -/
theorem step_computation {x h : ℝ} (hx : (7 : ℝ) / 10 ≤ x ∧ x ≤ 4 / 5)
    (hh : 0 < h ∧ h ≤ 1 / 1000000) :
    ModelSolve.StepComputation (model objective 1 x 1) (modelOrder : Fin 1 → ℕ)
      (9 / 10) (1 / 2) (fun _ => 9 / 10) (-h) (fun _ => 1) := by
  refine ⟨⟨h, hh.1, by linarith, ?_⟩, Or.inr ?_⟩
  · intro z
    simp only [model_formula]
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have hz : 0 ≤ (z + x) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hh.1.le hz, mul_nonneg hh.1.le (by linarith : 0 ≤ 1 - x ^ 2)]
  · refine ⟨by
      simpa only [Real.norm_eq_abs, abs_neg, abs_of_pos hh.1] using
        hh.2.trans (by norm_num : (1 : ℝ) / 1000000 ≤ 1), (fun _ _ => -h), (fun _ _ => 0),
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

/-- One infinite sequence of points with a finite total displacement. -/
noncomputable def point (k : ℕ) : ℝ :=
  3 / 4 - 1 / 1000000 + (1 / 1000000) * (1 / 2 : ℝ) ^ k

/-- All points stay strictly away from a passed literal objective test. -/
theorem point_mem (k : ℕ) : (7 : ℝ) / 10 ≤ point k ∧ point k ≤ 4 / 5 := by
  have hpow : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hp0 : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
  unfold point
  constructor <;> linarith

/-- The actual point increment is the selected negative trial. -/
theorem point_succ (k : ℕ) : point (k + 1) = point k + -magnitude k := by
  unfold point magnitude
  rw [pow_succ]
  ring

/-- The actual objective ratio remains very successful for every trial. -/
theorem ratio_lower {x h : ℝ} (hx : (7 : ℝ) / 10 ≤ x ∧ x ≤ 4 / 5)
    (hh : 0 < h ∧ h ≤ 1 / 1000000) :
    (3 : ℝ) / 4 ≤ ratio objective 1 x (-h) := by
  rw [ratio, decrement_one, deriv_objective]
  have hd : 0 < -x * -h := by nlinarith
  apply (le_div_iff₀ hd).mpr
  dsimp [objective]
  nlinarith [mul_nonneg hh.1.le (by linarith : 0 ≤ x / 4 - h / 2)]

/-- All primitive arrays of the fixed infinite execution. -/
noncomputable def data : HighOrderRegularization.ExecutionData ℝ 1 where
  point := point
  step := fun k => -magnitude k
  parameter := fun _ => 1
  ratio := fun k => ratio objective 1 (point k) (-magnitude k)
  radius := fun _ _ => 1
  solvedRadius := fun _ _ => 1
  direction := fun _ _ => -1
  selected := fun _ => some 0

/-- Every finite prefix satisfies the actual objective model, ratio, parameter
interval and accepted point update. -/
theorem modelTrace (N : ℕ) : ModelTrace objective 1 data.point data.step data.parameter
    data.ratio settings.eta1 settings.eta2 settings.gamma1 settings.gamma2 settings.gamma3
      settings.sigmaMin N := by
  refine ⟨by norm_num, ?_, ?_, fun _ _ => rfl, ?_⟩
  · refine ⟨by norm_num [settings], by norm_num [settings, data], by norm_num [settings],
      by norm_num [settings], by norm_num [settings], by norm_num [settings],
      by norm_num [settings], by norm_num [settings], by norm_num [settings], ?_⟩
    intro k hk
    have hr := ratio_lower (point_mem k) (magnitude_mem k)
    change settings.eta2 ≤ data.ratio k at hr
    rw [ite_eq_left hr]
    norm_num [settings, data]
  · intro k hk
    have hx := point_mem k
    have hh := magnitude_mem k
    change model objective 1 (point k) 1 (-magnitude k) < model objective 1 (point k) 1 0
    rw [model_formula, model_formula]
    norm_num
    nlinarith [mul_pos hh.1 (by linarith : 0 < point k - magnitude k / 2)]
  · intro k hk
    have hr := ratio_lower (point_mem k) (magnitude_mem k)
    change (3 : ℝ) / 4 ≤ data.ratio k at hr
    have ha : settings.eta1 ≤ data.ratio k := by
      change (1 : ℝ) / 4 ≤ _
      change (3 : ℝ) / 4 ≤ data.ratio k at hr
      linarith
    rw [ite_eq_left ha]
    exact point_succ k

/-- One fixed infinite computation has an actual ARqp prefix of every length.
All objective checks keep selecting a trial, and all model returns pass the
literal tests and even a positive-fraction approximate global solve. -/
theorem run (N : ℕ) : HighOrderRegularization.Run objective settings
    (fun _ => 9 / 10) data N where
  accuracy_pos := fun _ => by norm_num
  accuracy_le_one := fun _ => by norm_num
  initial_parameter := rfl
  initial_radii := fun _ => ⟨zero_lt_one, le_rfl⟩
  modelTrace := modelTrace N
  check := fun k _ => ObstructionCounterexample.check (point_mem k)
  step_two := fun k _ _ => step_computation (point_mem k) (magnitude_mem k)
  continues := fun _ _ => by simp only [data, ne_eq, reduceCtorEq, not_false_eq_true]
  radius_update := fun k _ => by
    have hr := ratio_lower (point_mem k) (magnitude_mem k)
    have ha : settings.eta1 ≤ data.ratio k := by
      change (1 : ℝ) / 4 ≤ _
      change (3 : ℝ) / 4 ≤ data.ratio k at hr
      linarith
    rw [ite_eq_left ha]
    rfl

/-- The objective satisfies the full level-set first-jet bound in addition to
its global smoothness, Lipschitz first derivative and lower bound. -/
theorem level_gradient_bound {x : ℝ} (hx : objective x ≤ objective (point 0)) :
    ‖iteratedFDeriv ℝ 1 objective x‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simp only [iteratedDeriv_one, deriv_objective, Real.norm_eq_abs]
  norm_num [objective, point] at hx
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]

/-- Every trial is successful. -/
theorem successful (k : ℕ) : settings.eta1 ≤ data.ratio k := by
  have hr := ratio_lower (point_mem k) (magnitude_mem k)
  change (1 : ℝ) / 4 ≤ _
  exact (by norm_num : (1 : ℝ) / 4 ≤ 3 / 4).trans hr

/-- The actual accepted objective decreases tend to zero along the fixed run. -/
theorem decrease_tendsto_zero : Filter.Tendsto
    (fun k => objective (data.point k) - objective (data.point (k + 1)))
      Filter.atTop (nhds 0) := by
  have hp : Filter.Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hx : Filter.Tendsto point Filter.atTop (nhds (3 / 4 - 1 / 1000000 : ℝ)) := by
    change Filter.Tendsto (fun k => 3 / 4 - 1 / 1000000 +
      (1 / 1000000) * (1 / 2 : ℝ) ^ k) Filter.atTop _
    simpa only [mul_zero, add_zero] using hp.const_mul (1 / 1000000) |>.const_add
      (3 / 4 - 1 / 1000000)
  have hf : Continuous objective := objective_regularity.1.continuous
  have hfx := hf.continuousAt.tendsto.comp hx
  have hfxs := hfx.comp (Filter.tendsto_add_atTop_nat 1)
  simpa only [data, Function.comp_apply, sub_self] using hfx.sub hfxs

/-- No positive coefficient, even one chosen after fixing the entire run,
can bound the decrease at all its successful iterations by epsilon squared. -/
theorem no_uniform_decrease : ¬∃ κ : ℝ, 0 < κ ∧ ∀ k : ℕ,
    settings.eta1 ≤ data.ratio k → κ * (9 / 10 : ℝ) ^ 2 ≤
      objective (data.point k) - objective (data.point (k + 1)) := by
  rintro ⟨κ, hκ, hbound⟩
  have he : 0 < κ * (9 / 10 : ℝ) ^ 2 := by positivity
  have hlt := (decrease_tendsto_zero.eventually (gt_mem_nhds he))
  obtain ⟨k, hk⟩ := hlt.exists
  exact (not_lt_of_ge (hbound k (successful k))) hk

end HighOrderRegularization.VanishingSteps
