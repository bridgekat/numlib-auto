import Numlib.Optimization.TrustRegion.HighOrder.Constrained
import Numlib.Optimization.TrustRegion.HighOrder.Complexity
import Numlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Accuracy dependence of additive trust-region iteration counts

The fixed objective `x ↦ x⁴ / 4` on a scalar box admits arbitrarily many
unsuccessful trials following one successful trial. The initial point, radius,
regularity constants and algorithm settings are fixed before the accuracy.
Thus a bound by a constant times the successful count plus a constant cannot
hold uniformly over all requested accuracies and legal model returns.
-/

noncomputable section

namespace HighOrderTrustRegion.CountingCounterexample
open Set

/-- A fixed nonnegative smooth objective. -/
def objective (x : ℝ) : ℝ := x ^ 4 / 4

/-- The fixed simple feasible box. -/
def feasible : Set ℝ := Icc (-2) 2

/-- A fixed open convex neighborhood of the feasible set. -/
def neighborhood : Set ℝ := Ioo (-3) 3

/-- The fixed objective is smooth to every finite order. -/
theorem smooth : ContDiff ℝ ⊤ objective := by unfold objective; fun_prop

/-- The actual scalar derivative of the quartic. -/
theorem hasDerivAt_objective (x : ℝ) : HasDerivAt objective (x ^ 3) x := by
  unfold objective
  convert (hasDerivAt_pow 4 x).div_const 4 using 1
  norm_num

/-- The genuine gradient is the cubic. -/
theorem gradient_objective (x : ℝ) : gradient objective x = x ^ 3 := by
  rw [gradient_eq_deriv', (hasDerivAt_objective x).deriv]

/-- The genuine first-order Taylor decrement. -/
theorem decrement (x s : ℝ) : TaylorModel.decrement objective 1 x s = -x ^ 3 * s := by
  rw [TaylorModel.decrement_one, gradient_objective]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  ring

/-- The actual unit-ball criticality at a positive scalar point. -/
theorem criticality {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) :
    TaylorModel.criticality objective 1 x δ = δ * x ^ 3 := by
  rw [TaylorModel.criticality_one objective x hδ, gradient_objective,
    Real.norm_eq_abs, abs_of_pos (pow_pos hx _)]

/-- The objective has a global lower bound independent of all accuracies. -/
theorem nonnegative (x : ℝ) : 0 ≤ objective x := by unfold objective; positivity

/-- All geometry is fixed before the accuracy request. -/
theorem geometry : IsClosed feasible ∧ feasible.Nonempty ∧ Convex ℝ feasible ∧
    IsOpen neighborhood ∧ Convex ℝ neighborhood ∧ feasible ⊆ neighborhood := by
  refine ⟨isClosed_Icc, ⟨0, by norm_num [feasible]⟩, convex_Icc _ _,
    isOpen_Ioo, convex_Ioo _ _, ?_⟩
  intro x hx
  simp only [feasible, mem_Icc] at hx
  simp only [neighborhood, mem_Ioo]
  constructor <;> linarith

/-- A small positive endpoint chosen after the requested rejection count. -/
def endpoint (m : ℕ) : ℝ := (1 / 2) ^ (m + 2)

/-- Every endpoint is positive and at most one quarter. -/
theorem endpoint_bounds (m : ℕ) : 0 < endpoint m ∧ endpoint m ≤ 1 / 4 := by
  refine ⟨by unfold endpoint; positivity, ?_⟩
  unfold endpoint
  rw [pow_add]
  have h := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := m)
  norm_num at *
  linarith

/-- Requested accuracy, smaller than the true endpoint gradient. -/
def accuracy (m : ℕ) : ℝ := endpoint m ^ 4

/-- Every request is positive, at most one, and strictly below the endpoint gradient. -/
theorem accuracy_bounds (m : ℕ) :
    0 < accuracy m ∧ accuracy m ≤ 1 ∧ accuracy m < endpoint m ^ 3 := by
  obtain ⟨ha, ha1⟩ := endpoint_bounds m
  have ha' : endpoint m < 1 := by linarith
  refine ⟨pow_pos ha _, pow_le_one₀ ha.le (by linarith), ?_⟩
  unfold accuracy
  calc endpoint m ^ 4 = endpoint m ^ 3 * endpoint m := by ring
    _ < endpoint m ^ 3 * 1 := mul_lt_mul_of_pos_left ha' (pow_pos ha _)
    _ = _ := mul_one _

/-- Accuracy-independent legal first-order trust-region settings. -/
def settings : Settings 1 where
  order_pos := by decide
  zeta := 1 / 2
  zeta_pos := by norm_num
  zeta_le_one := by norm_num
  theta := 1
  theta_pos := by norm_num
  theta_le_one := by norm_num
  eta1 := 1 / 10
  eta2 := 9 / 10
  gamma1 := 1 / 2
  gamma2 := 1 / 2
  gamma3 := 2
  radiusMax := 1
  eta1_pos := by norm_num
  eta1_le_eta2 := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_le_gamma2 := le_rfl
  gamma2_lt_one := by norm_num
  one_le_gamma3 := by norm_num

/-- Add the requested accuracy to the fixed settings. -/
def parameters (m : ℕ) : Parameters 1 := settings.withAccuracy
  (fun _ => accuracy m) (fun _ => (accuracy_bounds m).1)
  (fun _ => (accuracy_bounds m).2.1) ⟨0, (accuracy_bounds m).2.1⟩

/-- The actual iterates: the first accepted step reaches the small endpoint. -/
def point (m i : ℕ) : ℝ := if i = 0 then 1 else endpoint m

/-- The radius stays one on the first accepted step and then halves. -/
def radius (i : ℕ) : ℝ := (1 / 2) ^ (i - 1)

/-- A half-radius criticality computation, attaining exactly the required fraction. -/
def direction (i : ℕ) (_ : Fin 1) : ℝ := -radius i / 2

/-- The first step reaches the endpoint; subsequent steps use the whole radius. -/
def step (m i : ℕ) : ℝ := if i = 0 then endpoint m - 1 else -radius i

/-- Every trial selects the first-order model. -/
def order (_ : ℕ) : Fin 1 := 0

/-- The actual objective-to-Taylor-decrease ratio. -/
noncomputable def ratio (m i : ℕ) : ℝ :=
  (objective (point m i) - objective (point m i + step m i)) /
    TaylorModel.decrement objective 1 (point m i) (step m i)

/-- All radii are positive and at most one. -/
theorem radius_bounds (i : ℕ) : 0 < radius i ∧ radius i ≤ 1 :=
  ⟨by unfold radius; positivity,
    pow_le_one₀ (by norm_num) (by norm_num)⟩

/-- Every later radius is exactly half its predecessor. -/
theorem radius_succ {i : ℕ} (hi : 0 < i) : radius (i + 1) = radius i / 2 := by
  have he : i = i - 1 + 1 := by omega
  simp only [radius, Nat.add_sub_cancel]
  conv_lhs => rw [he, pow_succ]
  ring

/-- Every rejected-prefix radius is at least four times the endpoint. -/
theorem radius_lower {m i : ℕ} (hi : i ≤ m) : 4 * endpoint m ≤ radius i := by
  have hh := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) (show i - 1 ≤ m by omega)
  have he : 4 * endpoint m = (1 / 2 : ℝ) ^ m := by
    unfold endpoint
    rw [pow_add]
    norm_num
    ring
  rw [he]
  exact hh

/-- All current points are positive and at most one. -/
theorem point_bounds (m i : ℕ) : 0 < point m i ∧ point m i ≤ 1 := by
  unfold point
  split_ifs
  · norm_num
  · obtain ⟨h, h'⟩ := endpoint_bounds m
    exact ⟨h, h'.trans (by norm_num)⟩

/-- Every unit testing ball is feasible at all actual current points. -/
theorem testing_ball (m i : ℕ) {d : ℝ} (hd : ‖d‖ ≤ 1) : point m i + d ∈ feasible := by
  obtain ⟨hx, hx1⟩ := point_bounds m i
  rw [Real.norm_eq_abs, abs_le] at hd
  simp only [feasible, mem_Icc]
  constructor <;> linarith

/-- The first trial's true ratio is an explicit finite geometric sum. -/
theorem ratio_zero (m : ℕ) :
    ratio m 0 = (1 + endpoint m + endpoint m ^ 2 + endpoint m ^ 3) / 4 := by
  have ha := (endpoint_bounds m).2
  have hn : endpoint m - 1 ≠ 0 := by linarith
  unfold ratio
  simp only [point, step, ite_true, decrement]
  unfold objective
  field_simp [hn]
  ring

/-- The first trial is accepted but is not very successful. -/
theorem ratio_zero_bounds (m : ℕ) : 1 / 10 ≤ ratio m 0 ∧ ratio m 0 < 9 / 10 := by
  obtain ⟨ha, ha1⟩ := endpoint_bounds m
  rw [ratio_zero]
  have h2 : endpoint m ^ 2 ≤ 1 / 16 := by nlinarith
  have h3 : endpoint m ^ 3 ≤ 1 / 64 := by
    nlinarith [mul_le_mul ha1 h2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  constructor <;> nlinarith [sq_nonneg (endpoint m), pow_pos ha 3]

/-- Each subsequent trial in the requested prefix increases the actual objective. -/
theorem trial_increases {m i : ℕ} (hi : 0 < i) (him : i ≤ m) :
    objective (point m i) < objective (point m i + step m i) := by
  have hr := radius_lower him
  have ha := (endpoint_bounds m).1
  have hlt : endpoint m < radius i - endpoint m := by linarith
  have hp := pow_lt_pow_left₀ hlt ha.le (by decide : 4 ≠ 0)
  simp only [point, step, ite_eq_right (by omega : i ≠ 0), objective]
  have he : (endpoint m + -radius i) ^ 4 = (radius i - endpoint m) ^ 4 := by ring
  rw [he]
  linarith

/-- Every later prefix ratio is strictly negative and hence unsuccessful. -/
theorem ratio_negative {m i : ℕ} (hi : 0 < i) (him : i ≤ m) : ratio m i < 0 := by
  have hh := trial_increases hi him
  have hden : 0 < TaylorModel.decrement objective 1 (point m i) (step m i) := by
    simp only [point, step, ite_eq_right (by omega : i ≠ 0), decrement, neg_mul_neg]
    exact mul_pos (pow_pos (endpoint_bounds m).1 _) (radius_bounds i).1
  exact div_neg_of_neg_of_pos (sub_neg.mpr hh) hden

/-- Every actual point has a gradient strictly larger than the requested accuracy. -/
theorem point_gradient_gt (m i : ℕ) : accuracy m < point m i ^ 3 := by
  by_cases hi : i = 0
  · simp only [point, ite_eq_left hi, one_pow]
    exact (accuracy_bounds m).2.2.trans_le
      (pow_le_one₀ (endpoint_bounds m).1.le
        ((endpoint_bounds m).2.trans (by norm_num)))
  · simpa only [point, ite_eq_right hi] using (accuracy_bounds m).2.2

/-- The selected actual step is within its trust-region ball. -/
theorem step_norm (m i : ℕ) : ‖step m i‖ ≤ radius i := by
  by_cases hi : i = 0
  · subst i
    have h := endpoint_bounds m
    simp only [step, ite_true, radius, Nat.zero_sub, pow_zero, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  · simp only [step, ite_eq_right hi, norm_neg, Real.norm_eq_abs,
      abs_of_pos (radius_bounds i).1]
    exact le_rfl

/-- Every trial in the prescribed prefix satisfies all actual unrestricted
trust-region tests, including a genuine approximate criticality computation. -/
theorem actual_trial (m i : ℕ) (hi : i < m + 1) :
    Trial objective (parameters m) (point m i) (radius i) (direction i) (order i)
      (step m i) (point m (i + 1)) (radius (i + 1)) (ratio m i) := by
  have hr := radius_bounds i
  have hx := point_bounds m i
  have hδ : optimalityRadius (parameters m) (radius i) = radius i := by
    apply optimalityRadius_eq_radius
    exact hr.2
  have ho (a : Fin 1) : modelOrder a = 1 := by
    have he : a = 0 := Fin.eq_zero a
    rw [he]
    rfl
  have hd : TaylorModel.decrement objective 1 (point m i) (direction i 0) =
      point m i ^ 3 * radius i / 2 := by rw [decrement]; unfold direction; ring
  refine ⟨hr.1, ?_, ?_, ?_, ?_, step_norm m i, ?_, rfl, ?_, ?_⟩
  · intro a _
    rw [hδ]
    simp only [direction, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_pos hr.1, show |(2 : ℝ)| = 2 by norm_num]
    linarith
  · intro a _
    rw [ho, hδ, criticality hx.1 hr.1]
    have he : a = 0 := Fin.eq_zero a
    rw [he, hd]
    change 1 / 2 * (radius i * point m i ^ 3) ≤ _
    ring_nf
    rfl
  · intro a ha
    have he : a = order i := Subsingleton.elim _ _
    exact False.elim ((lt_irrefl _ (he ▸ ha)))
  · rw [ho, hδ]
    have he : order i = 0 := rfl
    rw [he, hd]
    simp only [parameters, Settings.withAccuracy, settings, Nat.factorial_one,
      Nat.cast_one, pow_one, div_one]
    have hh := mul_lt_mul_of_pos_right (point_gradient_gt m i) hr.1
    nlinarith
  · rw [ho, show order i = 0 by rfl, hd, decrement]
    by_cases hi0 : i = 0
    · subst i
      simp only [point, step, ite_true, radius, Nat.zero_sub, pow_zero]
      have ha := (endpoint_bounds m).2
      norm_num
      linarith
    · simp only [step, ite_eq_right hi0]
      nlinarith [mul_pos (pow_pos hx.1 3) hr.1]
  · by_cases hi0 : i = 0
    · subst i
      have hs := (ratio_zero_bounds m).1
      change point m 1 = if (1 / 10 : ℝ) ≤ ratio m 0 then _ else _
      rw [ite_eq_left hs]
      simp [point, step]
    · have hs : ¬(1 / 10 : ℝ) ≤ ratio m i := by
        have hh := ratio_negative (Nat.pos_of_ne_zero hi0) (by omega : i ≤ m)
        linarith
      change point m (i + 1) = if (1 / 10 : ℝ) ≤ ratio m i then _ else _
      rw [ite_eq_right hs]
      simp only [point, ite_eq_right hi0, ite_eq_right (by omega : i + 1 ≠ 0)]
  · change if (9 / 10 : ℝ) ≤ ratio m i then
        radius (i + 1) ∈ Icc (radius i) (min 1 (2 * radius i))
      else if (1 / 10 : ℝ) ≤ ratio m i then
        radius (i + 1) ∈ Icc (1 / 2 * radius i) (radius i)
      else radius (i + 1) ∈ Icc (1 / 2 * radius i) (1 / 2 * radius i)
    by_cases hi0 : i = 0
    · subst i
      obtain ⟨ha, hb⟩ := ratio_zero_bounds m
      rw [ite_eq_right (not_le.mpr hb), ite_eq_left ha]
      norm_num [radius]
    · have hh := ratio_negative (Nat.pos_of_ne_zero hi0) (by omega : i ≤ m)
      rw [ite_eq_right (show ¬(9 / 10 : ℝ) ≤ ratio m i by linarith),
        ite_eq_right (show ¬(1 / 10 : ℝ) ≤ ratio m i by linarith),
        radius_succ (Nat.pos_of_ne_zero hi0)]
      exact ⟨by linarith, by linarith⟩

/-- The same actual trials satisfy the simple-constraint algorithm: every
testing ball and selected trial point lies in the fixed feasible box. -/
theorem constrained_trial (m i : ℕ) (hi : i < m + 1) :
    ConstrainedTrial objective feasible (parameters m) (point m i) (radius i)
      (direction i) (order i) (step m i) (point m (i + 1))
        (radius (i + 1)) (ratio m i) := by
  apply (actual_trial m i hi).constrained_of_ball
  · simpa using testing_ball m i (d := 0) (by norm_num)
  · intro d hd
    apply testing_ball m i
    exact hd.trans ((optimalityRadius_le_radius _ _).trans (radius_bounds i).2)
  · exact testing_ball m i ((step_norm m i).trans (radius_bounds i).2)

/-- A genuine constrained run of arbitrary prescribed prefix length, starting
at the fixed point one with fixed initial radius one. -/
theorem actual_run (m : ℕ) : ConstrainedRun objective feasible (parameters m)
    (point m) (step m) direction order radius (ratio m) (m + 1) := by
  refine ⟨by norm_num [radius], by norm_num [radius, parameters,
    Settings.withAccuracy, settings], constrained_trial m⟩

/-- The genuine first jet is bounded by twenty-seven on the fixed neighborhood. -/
theorem derivative_bound {x : ℝ} (hx : x ∈ neighborhood) :
    ‖iteratedFDeriv ℝ 1 objective x‖ ≤ 27 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one,
    (hasDerivAt_objective x).deriv, Real.norm_eq_abs, abs_pow]
  have hh : |x| ≤ 3 := by
    simp only [neighborhood, mem_Ioo] at hx
    rw [abs_le]
    constructor <;> linarith
  have hp := pow_le_pow_left₀ (abs_nonneg x) hh 3
  norm_num at hp
  exact hp

/-- The actual first derivative is Lipschitz on the same fixed neighborhood. -/
theorem derivative_lipschitz {x y : ℝ}
    (hx : x ∈ neighborhood) (hy : y ∈ neighborhood) :
    ‖iteratedFDeriv ℝ 1 objective x - iteratedFDeriv ℝ 1 objective y‖ ≤
      27 * ‖x - y‖ := by
  have hx' : |x| ≤ 3 := by
    simp only [neighborhood, mem_Ioo] at hx
    rw [abs_le]
    constructor <;> linarith
  have hy' : |y| ≤ 3 := by
    simp only [neighborhood, mem_Ioo] at hy
    rw [abs_le]
    constructor <;> linarith
  have hx2 : |x ^ 2| ≤ 9 := by
    rw [abs_pow]
    nlinarith [abs_nonneg x]
  have hy2 : |y ^ 2| ≤ 9 := by
    rw [abs_pow]
    nlinarith [abs_nonneg y]
  have hxy : |x * y| ≤ 9 := by
    rw [abs_mul]
    nlinarith [abs_nonneg x, abs_nonneg y]
  have hs : |x ^ 2 + x * y + y ^ 2| ≤ 27 := calc
    _ ≤ |x ^ 2 + x * y| + |y ^ 2| := abs_add_le _ _
    _ ≤ (|x ^ 2| + |x * y|) + |y ^ 2| := by
      linarith [abs_add_le (x ^ 2) (x * y)]
    _ ≤ 27 := by linarith
  rw [norm_iteratedFDeriv_sub_eq_norm_iteratedDeriv_sub, iteratedDeriv_one,
    (hasDerivAt_objective x).deriv, (hasDerivAt_objective y).deriv]
  have he : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring
  rw [he, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg (x - y))]

/-- All first-order anchored regularity assumptions hold with fixed constants
before the accuracy, including bounds on the entire feasible sublevel set. -/
theorem source_regularity : ContDiffOn ℝ 1 objective neighborhood ∧
    (∀ x ∈ feasible, objective x ≤ objective 1 →
      ‖iteratedFDeriv ℝ 1 objective x‖ ≤ 27 ∧
        ∀ y ∈ neighborhood,
          ‖iteratedFDeriv ℝ 1 objective x - iteratedFDeriv ℝ 1 objective y‖ ≤
            27 * ‖x - y‖) := by
  refine ⟨(smooth.of_le (by simp)).contDiffOn, ?_⟩
  intro x hx _
  have hx' := geometry.2.2.2.2.2 hx
  exact ⟨derivative_bound hx', fun y hy => derivative_lipschitz hx' hy⟩

/-- Exactly the first trial is successful in every requested prefix. The
half-open prefix of length `m+1` is the source's inclusive prefix `0,...,m`. -/
theorem successful_prefix (m : ℕ) :
    EvaluationComplexity.successfulIterations
      {i | (parameters m).eta1 ≤ ratio m i} (m + 1) = {0} := by
  classical
  ext i
  simp only [EvaluationComplexity.mem_successfulIterations, Set.mem_ofPred_eq,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hi, hs⟩
    by_contra hn
    have hh := ratio_negative (Nat.pos_of_ne_zero hn) (by omega : i ≤ m)
    change (1 / 10 : ℝ) ≤ ratio m i at hs
    linarith
  · intro hi
    subst i
    exact ⟨by omega, (ratio_zero_bounds m).1⟩

/-- Every actual current point, including the final rejected-prefix endpoint,
fails the requested true constrained criticality test at unit radius. -/
theorem not_critical (m i : ℕ) :
    accuracy m < TaylorModel.constrainedCriticality objective 1 feasible (point m i) 1 := by
  rw [TaylorModel.constrainedCriticality_one_eq_norm_of_ball (by norm_num)
    (fun d hd => testing_ball m i hd), gradient_objective, Real.norm_eq_abs,
    abs_of_pos (pow_pos (point_bounds m i).1 3), one_mul]
  exact point_gradient_gt m i

/-- No two accuracy-independent real constants bound every inclusive trial
index by a multiple of the successful count plus an additive constant. The
objective, feasible set, initial point and all settings remain fixed. -/
theorem no_uniform_count : ¬∃ A B : ℝ, ∀ m : ℕ,
    (m : ℝ) ≤ A * (EvaluationComplexity.successfulIterations
      {i | (parameters m).eta1 ≤ ratio m i} (m + 1)).card + B := by
  rintro ⟨A, B, h⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (A + B)
  have hh := h m
  rw [successful_prefix, Finset.card_singleton] at hh
  norm_num at hh
  linarith

/-- Complete fixed-data counterexample: genuine constrained executions for
every requested rejection count, all true criticality tests fail, all source
regularity assumptions hold, and the inclusive count has no uniform constants. -/
theorem verified_counterexample :
    IsClosed feasible ∧ feasible.Nonempty ∧ Convex ℝ feasible ∧
    IsOpen neighborhood ∧ Convex ℝ neighborhood ∧ feasible ⊆ neighborhood ∧
    ContDiffOn ℝ 1 objective neighborhood ∧
    (∀ x, 0 ≤ objective x) ∧
    (∀ x ∈ feasible, objective x ≤ objective 1 →
      ‖iteratedFDeriv ℝ 1 objective x‖ ≤ 27 ∧ ∀ y ∈ neighborhood,
        ‖iteratedFDeriv ℝ 1 objective x - iteratedFDeriv ℝ 1 objective y‖ ≤
          27 * ‖x - y‖) ∧
    (∀ m, point m 0 = 1 ∧ radius 0 = 1 ∧
      ConstrainedRun objective feasible (parameters m) (point m) (step m)
        direction order radius (ratio m) (m + 1) ∧
      ∀ i, accuracy m <
        TaylorModel.constrainedCriticality objective 1 feasible (point m i) 1) ∧
    ¬∃ A B : ℝ, ∀ m : ℕ, (m : ℝ) ≤
      A * (EvaluationComplexity.successfulIterations
        {i | (parameters m).eta1 ≤ ratio m i} (m + 1)).card + B := by
  obtain ⟨hc, hne, hcv, ho, hocv, hsub⟩ := geometry
  exact ⟨hc, hne, hcv, ho, hocv, hsub, source_regularity.1,
    nonnegative, source_regularity.2,
    fun m => ⟨by simp [point], by norm_num [radius], actual_run m, not_critical m⟩,
    no_uniform_count⟩

end HighOrderTrustRegion.CountingCounterexample
