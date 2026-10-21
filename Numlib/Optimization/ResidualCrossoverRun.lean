import Numlib.Optimization.ResidualCrossoverArithmetic
import Numlib.Optimization.ResidualCrossoverJets
import Numlib.Optimization.HigherOrderApproximateRegularization
import Numlib.Optimization.TaylorCriticalityLocalMinimum

/-!
# A complete two-call residual wrapper with paid regularization queries

The selected nonspecific INNER method computes exact global cubic-model minimizers and
obeys very-successful parameter updates. It performs a fixed number of actual repeated
queries at the nonterminal incoming point before computing each step. Every output query
and derivative test is also charged. This is an explicitly extended regularization-type
method, rather than the cached query schedule of a particular earlier algorithm.
-/

noncomputable section
open Set Metric
namespace Optimization.ResidualCrossover
open ResidualLeastSquares ConstrainedTaylorCriticality TaylorCriticality
open ResidualCrossoverJets
open scoped Nat

/-- Fixed update controls for the two exact regularization steps. -/
def controls : ParameterUpdates.RegularizationParameters where
  eta1 := 1 / 10
  eta2 := 1 / 5
  gamma1 := 1 / 100
  gamma2 := 2
  gamma3 := 3
  sigmaMin := 1 / 1000
  eta1_pos := by norm_num
  eta_le := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_lt_one := by norm_num
  one_lt_gamma2 := by norm_num
  gamma2_lt_gamma3 := by norm_num
  sigmaMin_pos := by norm_num

/-- Exact scalar form of the first actual cubic Taylor model. -/
theorem first_model (d : Line) :
    HigherOrderRegularization.model objective 2 (point 0) 1 d =
      objective (point 0) + firstCubic (d 0) := by
  have ht := taylorDecrement_eq objective 2 (point 0) d
  rw [taylorDecrement_two_zero] at ht
  unfold HigherOrderRegularization.model
  rw [norm_eq_abs_coord]
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one]
  unfold firstCubic
  linarith

/-- Exact scalar form of the second actual model at its retained warm-start parameter. -/
theorem second_model (d : Line) :
    HigherOrderRegularization.model objective 2 (point 1) (middleGradient / 2) d =
      objective (point 1) + secondCubic (d 0) := by
  have ht := taylorDecrement_eq objective 2 (point 1) d
  rw [taylorDecrement_two_one] at ht
  unfold HigherOrderRegularization.model
  rw [norm_eq_abs_coord]
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one]
  unfold secondCubic
  have hg : slope = middleGradient := rfl
  rw [hg] at ht
  linarith

/-- The first executed step is a true global minimizer of the actual model. -/
theorem first_model_min (d : Line) :
    HigherOrderRegularization.model objective 2 (point 0) 1 (point 1) ≤
      HigherOrderRegularization.model objective 2 (point 0) 1 d := by
  rw [first_model, first_model]
  exact add_le_add le_rfl (firstCubic_min (d 0))

/-- The second executed step is a true global minimizer of the actual model. -/
theorem second_model_min (d : Line) :
    HigherOrderRegularization.model objective 2 (point 1) (middleGradient / 2) (point (-2)) ≤
      HigherOrderRegularization.model objective 2 (point 1) (middleGradient / 2) d := by
  rw [second_model, second_model]
  exact add_le_add le_rfl (secondCubic_min (d 0))

/-- Both actual models strictly decrease at their chosen steps. -/
theorem model_decreases :
    HigherOrderRegularization.model objective 2 (point 0) 1 (point 1) < objective (point 0) ∧
    HigherOrderRegularization.model objective 2 (point 1) (middleGradient / 2) (point (-2)) <
      objective (point 1) := by
  rw [first_model, second_model]
  norm_num [firstCubic, secondCubic, middleGradient, point]

/-- Both exact model minimizers pass all first- and second-order unit-radius model tests. -/
theorem model_gaps_zero {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ 2) :
    gapOn (taylorDecrement (HigherOrderRegularization.model objective 2 (point 0) 1)
      j (point 1)) (closedBall 0 1) = 0 ∧
    gapOn (taylorDecrement
      (HigherOrderRegularization.model objective 2 (point 1) (middleGradient / 2))
      j (point (-2))) (closedBall 0 1) = 0 := by
  have he : j = 1 ∨ j = 2 := by omega
  constructor
  · exact gapOn_taylorDecrement_eq_zero_of_isLocalMin he
      ((HigherOrderApproximateRegularization.contDiff_model objective 2 (point 0) 1).of_le
        (by exact_mod_cast hjq))
      (show IsLocalMin _ (point 1) from Filter.Eventually.of_forall first_model_min)
      (by norm_num)
  · exact gapOn_taylorDecrement_eq_zero_of_isLocalMin he
      ((HigherOrderApproximateRegularization.contDiff_model objective 2 (point 1)
        (middleGradient / 2)).of_le (by exact_mod_cast hjq))
      (show IsLocalMin _ (point (-2)) from Filter.Eventually.of_forall second_model_min)
      (by norm_num)

/-- The first actual ratio uses the unregularized prediction three quarters. -/
theorem first_ratio : HigherOrderRegularization.ratio objective 2 (point 0) (point 1) =
    (1 / 2 - middleResidual ^ 2 / 2) / (3 / 4) := by
  have hn : point (1 : ℝ) ≠ 0 := by
    intro h
    have := congrArg (fun x : Line => x 0) h
    norm_num [point] at this
  unfold HigherOrderRegularization.ratio
  rw [ite_eq_right hn, ← taylorDecrement, taylorDecrement_two_zero]
  have he : point 0 + point 1 = point 1 := by simp
  rw [he, objective_point_zero, objective_point_one]
  norm_num [point, middleResidual]

/-- The second actual ratio uses the unregularized prediction twice the incoming slope. -/
theorem second_ratio :
    HigherOrderRegularization.ratio objective 2 (point 1) (point (-2)) =
      (middleResidual ^ 2 / 2 - finalResidual ^ 2 / 2) / (2 * middleGradient) := by
  have hn : point (-2 : ℝ) ≠ 0 := by
    intro h
    have := congrArg (fun x : Line => x 0) h
    norm_num [point] at this
  unfold HigherOrderRegularization.ratio
  rw [ite_eq_right hn, ← taylorDecrement, taylorDecrement_two_one]
  have he : point 1 + point (-2) = point (-1) := by rw [← point_add]; norm_num
  rw [he, objective_point_one, objective_point_neg_one]
  norm_num [point, middleResidual, finalResidual, middleGradient, ResidualCrossoverJets.slope]

/-- The initial actual first-order constrained gap is one. -/
theorem first_gap : taylorGap objective feasible 1 (point 0) 1 = 1 := by
  have he : taylorDecrement objective 1 (point 0) =
      fun d : Line => -(-EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) d := by
    funext d
    rw [taylorDecrement_one_zero]
    simp
  unfold taylorGap
  rw [feasibleBall_eq (by norm_num : |(0 : ℝ)| ≤ 2), he,
    gapOn_norm_linear _ (by norm_num), norm_neg, norm_coordinate]
  norm_num


/-- An actual oracle query identifies its evaluation point and derivative order.
Order zero is a value query; orders one and two are separate derivative queries. -/
structure RawQuery where
  point : Line
  order : ℕ

/-- The response is the actual objective tensor, including the value at order zero. -/
def RawQuery.reply (q : RawQuery) :
    ContinuousMultilinearMap ℝ (fun _ : Fin q.order => Line) ℝ :=
  iteratedFDeriv ℝ q.order objective q.point

/-- The value response is precisely the actual objective value. -/
@[simp] theorem RawQuery.value_reply (x : Line) :
    (RawQuery.mk x 0).reply (fun i => Fin.elim0 i) = objective x := by
  simp [RawQuery.reply]

/-- The event channel counts actual values and individual positive-order derivative calls. -/
def RawQuery.kind (q : RawQuery) : EvaluationKind :=
  if q.order = 0 then .function else .derivative

attribute [local instance] Classical.propDecidable

/-- A single fixed query policy for both calls, selected at the incoming point. -/
def callCount (x : Line) : ℕ := if x = point 0 then 794 else 2461

/-- Incoming derivatives are computed and actual value queries are repeated before the
step is calculated. No repeated query is replaced by a free cache lookup. -/
def incomingQueries (x : Line) : List RawQuery :=
  [⟨x, 1⟩, ⟨x, 2⟩] ++ List.replicate (callCount x - 1) ⟨x, 0⟩

/-- The returned value and both actual terminal derivative tests are paid once. -/
def outputQueries (x : Line) : List RawQuery := [⟨x, 0⟩, ⟨x, 1⟩, ⟨x, 2⟩]

/-- Outer points of the complete two-call execution, with a terminal constant continuation. -/
def outerPoint : ℕ → Line
  | 0 => point 0
  | 1 => point 1
  | _ => point (-1)

/-- The exact regularization parameter is retained as warm-start solver state. -/
def outerSigma : ℕ → ℝ
  | 0 => 1
  | _ => middleGradient / 2

/-- The real query lists at each inner stage, including its terminal stage. -/
def rawQueries (k i : ℕ) : List RawQuery :=
  if i = 0 then incomingQueries (outerPoint k) else outputQueries (outerPoint (k + 1))

/-- Each INNER call contains one genuine regularization transition and a paid terminal test. -/
def innerTrace (k : ℕ) : InnerTrace Line ℝ where
  point := fun i => if i = 0 then outerPoint k else outerPoint (k + 1)
  state := fun i => if i = 0 then outerSigma k else outerSigma (k + 1)
  length := 1
  queries := fun i => (rawQueries k i).map RawQuery.kind

/-- The complete wrapper shares its actual points, warm-start state and inner traces. -/
def trace : Trace Line ℝ where
  point := outerPoint
  radius := fun k _ => if k = 0 then 0 else 1
  state := outerSigma
  inner := innerTrace

/-- Incoming stage events, retaining their actual point and tensor-order interpretation. -/
def incomingEvents (x : Line) : List EvaluationKind := (incomingQueries x).map RawQuery.kind

/-- Terminal stage events, with all three real output queries. -/
def outputEvents (x : Line) : List EvaluationKind := (outputQueries x).map RawQuery.kind

/-- The selected generic INNER transition takes a global cubic-model minimizer, pays its
actual incoming query list, and makes a very-successful accepted parameter update. Its
incoming first-order test must fail; the output test is separately executed and charged. -/
def innerStep (τ : ℕ → ℝ) (a b : Line × ℝ) (events : List EvaluationKind) : Prop :=
  let s := b.1 - a.1
  τ 1 < taylorGap objective feasible 1 a.1 1 ∧
    (∀ d, HigherOrderRegularization.model objective 2 a.1 a.2 s ≤
      HigherOrderRegularization.model objective 2 a.1 a.2 d) ∧
    HigherOrderRegularization.model objective 2 a.1 a.2 s < objective a.1 ∧
    controls.eta2 ≤ HigherOrderRegularization.ratio objective 2 a.1 s ∧
    max controls.sigmaMin (controls.gamma1 * a.2) ≤ b.2 ∧ b.2 ≤ a.2 ∧
    events = incomingEvents a.1

/-- The selected terminal rule performs the actual two-order objective test with unit
radii and pays the actual terminal value and derivative events. -/
def innerTerminal (τ : ℕ → ℝ) (a : Line × ℝ) (events : List EvaluationKind) : Prop :=
  (∀ j ∈ Finset.Icc 1 2,
    taylorGap objective feasible j a.1 1 ≤ τ j / (j ! : ℝ)) ∧ events = outputEvents a.1

/-- The exact query policy uses different fixed call counts at the two nonterminal inputs. -/
theorem call_counts : callCount (point 0) = 794 ∧ callCount (point 1) = 2461 := by
  have hn : point (1 : ℝ) ≠ 0 := by
    intro h
    have := congrArg (fun x : Line => x 0) h
    norm_num [point] at this
  simp [callCount, hn]

/-- The incoming log counts every actual repeated value call and both tensor orders. -/
theorem incomingEvents_count (x : Line) (a : EvaluationKind) :
    (incomingEvents x).count a = if a = .function then callCount x - 1 else 2 := by
  cases a <;> simp [incomingEvents, incomingQueries, RawQuery.kind, List.count_replicate]

/-- The terminal log contains one value call and two separate derivative calls. -/
theorem outputEvents_count (x : Line) (a : EvaluationKind) :
    (outputEvents x).count a = if a = .function then 1 else 2 := by
  cases a <;> simp [outputEvents, outputQueries, RawQuery.kind]

/-- The two stages of one call include both its incoming and terminal query lists. -/
theorem inner_evaluations_eq (k : ℕ) (a : EvaluationKind) :
    (innerTrace k).evaluations a =
      (incomingEvents (outerPoint k)).count a +
        (outputEvents (outerPoint (k + 1))).count a := by
  simp [InnerTrace.evaluations, innerTrace, rawQueries, incomingEvents, outputEvents,
    Finset.sum_range_succ]

/-- Every visited oracle invocation is counted, including both output derivative orders. -/
theorem inner_evaluations (a : EvaluationKind) :
    (innerTrace 0).evaluations a = (if a = .function then 794 else 4) ∧
      (innerTrace 1).evaluations a = (if a = .function then 2461 else 4) := by
  rw [inner_evaluations_eq, inner_evaluations_eq, incomingEvents_count, incomingEvents_count,
    outputEvents_count, outputEvents_count]
  have hz : callCount (0 : Line) = 794 := by simp [callCount]
  cases a <;> simp [outerPoint, hz, call_counts.2]

/-- Both actual executed transitions obey the same fixed regularization-type INNER rule. -/
theorem inner_steps :
    innerStep (inputTolerance 1) (point 0, 1) (point 1, middleGradient / 2)
      (incomingEvents (point 0)) ∧
    innerStep (inputTolerance middleResidual) (point 1, middleGradient / 2)
      (point (-1), middleGradient / 2) (incomingEvents (point 1)) := by
  have hstep0 : point 1 - point 0 = point 1 := by simp
  have hstep1 : point (-1) - point 1 = point (-2) := by rw [← point_sub]; norm_num
  have hg : slope = middleGradient := rfl
  constructor
  · simp only [innerStep, hstep0, first_gap]
    exact ⟨starting_tests_fail.1, first_model_min, model_decreases.1,
      by simpa only [controls, first_ratio] using acceptance_and_updates.1,
      by simpa only [controls, mul_one] using acceptance_and_updates.2.2.1,
      acceptance_and_updates.2.2.2.1, trivial⟩
  · simp only [innerStep, hstep1, taylorGap_one 1 le_rfl (by norm_num), hg]
    refine ⟨starting_tests_fail.2, second_model_min, model_decreases.2,
      by simpa only [controls, second_ratio] using acceptance_and_updates.2.1, ?_, le_rfl, trivial⟩
    norm_num [controls, middleGradient]

/-- Both returned points pass every actual input-tolerance objective test. -/
theorem inner_terminals :
    innerTerminal (inputTolerance 1) (point 1, middleGradient / 2) (outputEvents (point 1)) ∧
    innerTerminal (inputTolerance middleResidual) (point (-1), middleGradient / 2)
      (outputEvents (point (-1))) := by
  have hg : slope = middleGradient := rfl
  constructor
  · refine ⟨?_, rfl⟩
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    rw [taylorGap_one j hj1 hj2, hg]
    interval_cases j
    · simpa using middle_gap_bounds.2.1
    · simpa using middle_gap_bounds.2.2
  · refine ⟨?_, rfl⟩
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    rw [taylorGap_neg_one j hj1 hj2]
    exact div_nonneg (input_tolerance_bounds (Or.inr rfl) (Finset.mem_Icc.mpr ⟨hj1, hj2⟩)).1.le
      (by positivity)


/-- The two actual incoming residuals determine the input tolerance vectors. -/
def inputResidual (k : ℕ) : ℝ := if k = 0 then 1 else middleResidual

/-- Each complete executed call satisfies the same source INNER contract, with fixed
coefficients one and exponents four and twenty. No cost or output certificate is postulated. -/
theorem inner_contract (k : ℕ) (hk : k < 2) :
    InnerContract feasible objective 0 2 (inputTolerance (inputResidual k)) (fun _ => 1)
      exponent (fun _ => 1) innerStep innerTerminal (innerTrace k) := by
  refine {
    feasible := ?_
    legal := ?_
    checked := ?_
    final_value := ?_
    objective_nonincrease := ?_
    lower_bound := ?_
    tolerance := ?_
    radius := ?_
    exponent := ?_
    gap := ?_
    coefficient := ?_
    cost := ?_ }
  · intro i hi
    change i ≤ 1 at hi
    interval_cases k <;> interval_cases i <;>
      norm_num [innerTrace, outerPoint, feasible, Metric.mem_closedBall, dist_zero_right]
  · intro i hi
    change i < 1 at hi
    have hi0 : i = 0 := by omega
    subst i
    interval_cases k
    · simpa [innerTrace, outerPoint, outerSigma, rawQueries, inputResidual, incomingEvents]
        using inner_steps.1
    · simpa [innerTrace, outerPoint, outerSigma, rawQueries, inputResidual, incomingEvents]
        using inner_steps.2
  · interval_cases k
    · simpa [innerTrace, outerPoint, outerSigma, rawQueries, outputEvents, inputResidual]
        using inner_terminals.1
    · simpa [innerTrace, outerPoint, outerSigma, rawQueries, outputEvents, inputResidual]
        using inner_terminals.2
  · change 1 ≤ (outputEvents (outerPoint (k + 1))).count .function
    rw [outputEvents_count]
    norm_num
  · interval_cases k
    · change objective (point 1) ≤ objective (point 0)
      rw [objective_point_one, objective_point_zero]
      norm_num
    · change objective (point (-1)) ≤ objective (point 1)
      rw [objective_point_neg_one, objective_point_one]
      norm_num
  · intro x _
    rw [objective_eq_half_norm_sq]
    positivity
  · intro j hj
    apply (input_tolerance_bounds (j := j) ?_ hj).imp_right (fun h => h.le)
    interval_cases k <;> simp [inputResidual]
  · intro j _
    norm_num
  · intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    interval_cases j <;> norm_num [exponent]
  · intro j hj
    change taylorGap objective feasible j ((innerTrace k).point 1) 1 ≤
      inputTolerance (inputResidual k) j * 1 ^ j / (j ! : ℝ)
    simp only [one_pow, mul_one]
    interval_cases k
    · exact inner_terminals.1.1 j hj
    · exact inner_terminals.2.1 j hj
  · intro a
    norm_num
  · intro a
    simp only [one_mul]
    interval_cases k
    · change ((innerTrace 0).evaluations a : ℝ) ≤
        (objective (point 0) - 0) * toleranceWeight 2 (inputTolerance 1) exponent
      rw [objective_point_zero, sub_zero]
      have hc : ((innerTrace 0).evaluations a : ℝ) ≤ 794 := by
        rw [(inner_evaluations a).1]
        split_ifs <;> norm_num
      exact hc.trans first_cost_le
    · change ((innerTrace 1).evaluations a : ℝ) ≤
        (objective (point 1) - 0) * toleranceWeight 2 (inputTolerance middleResidual) exponent
      rw [objective_eq_half_norm_sq, residual_norm_one, sub_zero]
      have hc : ((innerTrace 1).evaluations a : ℝ) ≤ 2461 := by
        rw [(inner_evaluations a).2]
        split_ifs <;> norm_num
      exact hc.trans second_cost_le

/-- The initial residual-only stopping test fails. -/
theorem not_stops_zero : ¬Stops feasible residual 2 primal epsilon trace 0 := by
  rintro (hr | ⟨hk, _⟩)
  · change ‖residual (point 0)‖ ≤ primal at hr
    rw [residual_norm_zero] at hr
    norm_num [primal] at hr
  · omega

/-- The intermediate point fails the actual outer first-order gap test despite passing
both input-tolerance INNER tests; its residual is still above the primal tolerance. -/
theorem not_stops_one : ¬Stops feasible residual 2 primal epsilon trace 1 := by
  have hr : primal < ‖residual (trace.point 1)‖ := by
    change primal < ‖residual (point 1)‖
    rw [residual_norm_one]
    norm_num [primal]
  rintro (hsmall | ⟨_, hc⟩)
  · exact (not_le.mpr hr) hsmall
  · have hg := hc.gap hr (by norm_num : 1 ∈ Finset.Icc 1 2)
    change 0 < 1 ∧ taylorGap objective feasible 1 (point 1) 1 ≤
      epsilon 1 * ‖residual (point 1)‖ * 1 ^ 1 / (1 ! : ℝ) at hg
    rw [taylorGap_one 1 le_rfl (by norm_num), residual_norm_one] at hg
    have hh := middle_gap_bounds.1
    have he : ResidualCrossoverJets.slope = middleGradient := rfl
    rw [he] at hg
    norm_num only [Nat.factorial_one, Nat.cast_one, pow_one, mul_one, div_one] at hg
    have hR : (7999 / 10000 : ℝ) = middleResidual := rfl
    rw [hR, mul_comm] at hg
    linarith [hg.2]

/-- Every index from two onwards uses the residual-small terminal point. -/
theorem stops_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    Stops feasible residual 2 primal epsilon trace k := by
  left
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero => omega
    | succ k =>
      change ‖residual (point (-1))‖ ≤ primal
      rw [residual_norm_neg_one]
      norm_num [primal]

/-- The complete two-call execution satisfies all literal wrapper rules. The arrays after
the first stop are harmless continuations; no extra INNER contract is assumed there. -/
theorem execution : Execution feasible residual 2 primal beta epsilon exponent
    (fun _ => 1) innerStep innerTerminal trace := by
  refine {
    order_pos := by norm_num
    initial_feasible := ?_
    primal := ?_
    dual := ?_
    factor := ?_
    initial_scaling := ?_
    initial_radius := ?_
    start := ?_
    finish := ?_
    state_start := ?_
    state_finish := ?_
    coefficient := ?_
    solve := ?_ }
  · change point 0 ∈ feasible
    rw [point_mem_feasible]
    norm_num
  · norm_num [primal]
  · intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    interval_cases j <;> norm_num [epsilon]
  · norm_num [beta]
  · intro _
    change beta < (‖residual (point 0)‖)⁻¹
    rw [residual_norm_zero]
    norm_num [beta]
  · intro j
    rfl
  · intro k
    rfl
  · intro k
    rfl
  · intro k
    rfl
  · intro k
    rfl
  · intro a
    norm_num
  · intro k hn
    have hk : k < 2 := by
      by_contra h
      exact hn (stops_of_two_le (by omega))
    interval_cases k
    · change InnerContract feasible objective 0 2 (inputTolerance ‖residual (point 0)‖)
        (fun _ => 1) exponent (fun _ => 1) innerStep innerTerminal (innerTrace 0)
      rw [residual_norm_zero]
      exact inner_contract 0 (by norm_num)
    · change InnerContract feasible objective 0 2 (inputTolerance ‖residual (point 1)‖)
        (fun _ => 1) exponent (fun _ => 1) innerStep innerTerminal (innerTrace 1)
      rw [residual_norm_one]
      exact inner_contract 1 (by norm_num)

/-- The first actual stopping index is exactly two. -/
theorem first_stop : Stops feasible residual 2 primal epsilon trace 2 ∧
    ∀ k < 2, ¬Stops feasible residual 2 primal epsilon trace k := by
  refine ⟨stops_of_two_le le_rfl, ?_⟩
  intro k hk
  interval_cases k
  · exact not_stops_zero
  · exact not_stops_one

/-- The actual two-call value-query count already exceeds the printed bound, before the
initial residual query. No rounding or initialization convention causes the violation. -/
theorem inner_cost_violation : printedBound < (evaluations trace .function 2 : ℝ) := by
  have hc : evaluations trace .function 2 = 794 + 2461 := by
    simp only [evaluations, trace, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      (inner_evaluations .function).1, (inner_evaluations .function).2, ite_true]
  rw [hc]
  exact_mod_cast printedBound_lt_inner_cost

/-- Including the actual initial residual query only strengthens the strict violation. -/
theorem total_cost_violation : printedBound < (totalEvaluations trace .function 2 : ℝ) := by
  have hc : evaluations trace .function 2 ≤ totalEvaluations trace .function 2 := by
    simp [totalEvaluations]
  exact inner_cost_violation.trans_le (by exact_mod_cast hc)

end Optimization.ResidualCrossover
