import Numlib.Optimization.ExplicitRegularization

/-!
# A single regularization trial with its actual value calls

`TrialData` packages one inspected trial and the next inspection, including initialization.
Its finite execution retains the selected inner run, common endpoint request, cache and ratio.
This constructor is useful when extending a concrete trial to a certified-error execution.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Optimization.ExplicitRegularization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Complete operational data for one trial, with both the initial and next inspections.
No true optimality, decrease estimate or parameter upper bound is assumed. -/
structure TrialData (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  parameters : Parameters
  objective : E → ℝ
  oracle : Oracle objective parameters.p
  initial : State E
  inspection : Inspection parameters oracle.derivative initial
  failed : inspection.order ≤ parameters.q
  inner : InexactRegularization.InnerResult parameters.toImplicitParameters 0
    (oracle.derivative initial.point initial.request) initial.sigma inspection.radii
    (inspection.direction failed)
  accurate : InexactRegularization.StepAccurate parameters.toImplicitParameters parameters.q
    initial.request inner.step
  values : ValueTrial parameters oracle initial inner.step
  nextSigma : ℝ
  update : HigherOrderApproximateRegularization.ParameterUpdate
    parameters.toImplicitParameters.toParameters values.ratio initial.sigma nextSigma
  terminalInspection : Inspection parameters oracle.derivative
    (trialState initial inspection failed inner values nextSigma)
  initial_fresh : initial.fresh = true
  initial_cache : initial.valueCache = none
  initial_sigma : parameters.sigmaMin ≤ initial.sigma
  initial_radii : HigherOrderApproximateRegularization.ValidRadii
    parameters.toImplicitParameters.toParameters initial.radii
  initial_tolerance : ∀ j, 1 ≤ j → j ≤ parameters.q → parameters.epsilon j ≤ initial.radii j
  initial_request : ∀ i ∈ Finset.Icc 1 parameters.p, 0 < initial.request i
  initial_request_le : ∀ i ∈ Finset.Icc 1 parameters.p, initial.request i ≤ parameters.kappaInitial

/-- The chosen trial gives a complete finite execution with its actual value-query log. -/
def TrialData.execution (d : TrialData E) : Execution d.parameters d.oracle 1 where
  state := fun k => if k = 0 then d.initial else
    trialState d.initial d.inspection d.failed d.inner d.values d.nextSigma
  inspection := fun k => by
    by_cases hk : k = 0
    · subst k; exact d.inspection
    · simpa only [ite_eq_right hk] using d.terminalInspection
  trial := fun _ => true
  accepted := fun _ => decide (d.parameters.eta1 ≤ d.values.ratio)
  queries := fun _ => d.values.queries
  initial_fresh := d.initial_fresh
  initial_cache := d.initial_cache
  initial_sigma := d.initial_sigma
  initial_radii := d.initial_radii
  initial_tolerance := d.initial_tolerance
  initial_request := d.initial_request
  initial_request_le := d.initial_request_le
  transition := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    exact Transition.trial d.failed d.inner d.accurate d.values d.nextSigma d.update

/-- The execution starts at the supplied initialized state. -/
@[simp] theorem TrialData.execution_state_zero (d : TrialData E) :
    d.execution.state 0 = d.initial := rfl

/-- The next state retains the source acceptance and cache update. -/
@[simp] theorem TrialData.execution_state_one (d : TrialData E) :
    d.execution.state 1 =
      trialState d.initial d.inspection d.failed d.inner d.values d.nextSigma := rfl

/-- The sole operation is the supplied trial. -/
@[simp] theorem TrialData.execution_trial (d : TrialData E) (k : ℕ) :
    d.execution.trial k = true := rfl

/-- Trial acceptance uses the actual endpoint-value ratio. -/
@[simp] theorem TrialData.execution_accepted (d : TrialData E) (k : ℕ) :
    d.execution.accepted k = decide (d.parameters.eta1 ≤ d.values.ratio) := rfl

/-- The finite execution logs exactly the supplied endpoint requests. -/
@[simp] theorem TrialData.execution_queries (d : TrialData E) (k : ℕ) :
    d.execution.queries k = d.values.queries := rfl

end Optimization.ExplicitRegularization
