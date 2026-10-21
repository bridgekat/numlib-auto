import Numlib.Optimization.ExplicitTrustRegion
import Numlib.Optimization.InexactRegularizationAccuracy

/-!
# Regularization with observable absolute-error certification

Actual inspections and inner executions use the supplied tensors. The polynomial constant
is zero because every model test uses a decrement; no objective value is needed until a trial.
A value cache stores its original positive request. A trial may reuse that value only when
its error bound meets the new shared endpoint budget. The query log includes both endpoints
of the first trial and every subsequent recomputation, with no initialization value query.
-/

noncomputable section
open scoped Nat
attribute [local instance] Classical.propDecidable
namespace Optimization.ExplicitRegularization
open InexactTaylorModels TaylorCriticality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Absolute-error oracles are shared with the trust-region interface. -/
abbrev Oracle := @ExplicitTrustRegion.Oracle

/-- Regularization parameters with the two endpoint-error allowances. -/
structure Parameters extends toImplicitParameters : InexactRegularization.Parameters where
  step_acceptance : kappaStep ≤ eta1 / 4
  step_success : kappaStep ≤ (1 - eta2) / 4

/-- The cached scalar records the request at which its value was actually obtained.
The point is the current state point. `none` means that no value is available yet. -/
structure State (E : Type*) extends toImplicitState : InexactRegularization.State E where
  valueCache : Option ℝ

/-- The actual radius searches require no approximate scalar constant. -/
abbrev Inspection (P : Parameters) (oracle : E → (ℕ → ℝ) → InexactRegularization.Coefficients E)
    (a : State E) :=
  InexactRegularization.Inspection P.toImplicitParameters 0
    (oracle a.point a.request) a.sigma a.radii

variable {oracle : E → (ℕ → ℝ) → InexactRegularization.Coefficients E}

/-- The literal observable error sum is checked independently at every active order. -/
def ErrorCheck (P : Parameters) (a : State E) (I : Inspection P oracle a) : Prop :=
  ∀ j, 1 ≤ j → j ≤ P.q →
    ∑ i ∈ Finset.Icc 1 j, a.request i * I.radii j ^ i / (i ! : ℝ) ≤
      P.fraction * P.epsilon j * I.radii j ^ j / (2 * (j ! : ℝ))

/-- Stopping uses the actual completed inspection and its known tensor-error sums. -/
def Certified (P : Parameters) (a : State E) (I : Inspection P oracle a) : Prop :=
  I.order = P.q + 1 ∧ ErrorCheck P a I

/-- The two observable clauses characterize a stopping certificate. -/
@[simp] theorem certified_iff (P : Parameters) (a : State E) (I : Inspection P oracle a) :
    Certified P a I ↔ I.order = P.q + 1 ∧ ErrorCheck P a I := Iff.rfl

/-- One trial chooses a common endpoint error allowance. Its current value either comes
from a fresh call at that allowance or from an explicitly compatible cached request. -/
structure ValueTrial {f : E → ℝ} (P : Parameters) (O : Oracle f P.p)
    (a : State E) (s : E) where
  request : ℝ
  request_pos : 0 < request
  budget : request ≤ P.kappaStep * decrement (O.derivative a.point a.request) P.p s
  currentRequest : ℝ
  current_pos : 0 < currentRequest
  current_le : currentRequest ≤ request
  recompute : Bool
  fresh_request : recompute = true → currentRequest = request
  cached_request : recompute = false → a.valueCache = some currentRequest

/-- The ratio uses the two values actually requested, with no exact objective access. -/
def ValueTrial.ratio {f : E → ℝ} {P : Parameters} {O : Oracle f P.p}
    {a : State E} {s : E} (v : ValueTrial P O a s) : ℝ :=
  (O.value a.point v.currentRequest - O.value (a.point + s) v.request) /
    decrement (O.derivative a.point a.request) P.p s

/-- A trial always queries its candidate endpoint and optionally recomputes the old endpoint. -/
def ValueTrial.queries {f : E → ℝ} {P : Parameters} {O : Oracle f P.p}
    {a : State E} {s : E} (v : ValueTrial P O a s) : List (E × ℝ) :=
  (if v.recompute then [(a.point, v.request)] else []) ++ [(a.point + s, v.request)]

/-- A trial makes precisely one or two actual value calls. -/
@[simp] theorem ValueTrial.queries_length {f : E → ℝ} {P : Parameters} {O : Oracle f P.p}
    {a : State E} {s : E} (v : ValueTrial P O a s) :
    v.queries.length = if v.recompute then 2 else 1 := by
  cases h : v.recompute <;> simp [ValueTrial.queries, h]

/-- Accuracy refinement restores incoming radii and preserves the compatible value cache. -/
def refine (P : Parameters) (a : State E) : State E :=
  ⟨InexactRegularization.refine P.toImplicitParameters a.toImplicitState, a.valueCache⟩

/-- Trial state updates preserve the actual endpoint cache and the source radius choices. -/
def trialState {f : E → ℝ} {P : Parameters} {O : Oracle f P.p}
    (a : State E) (I : Inspection P O.derivative a) (hq : I.order ≤ P.q)
    (s : InexactRegularization.InnerResult P.toImplicitParameters 0
        (O.derivative a.point a.request)
      a.sigma I.radii (I.direction hq)) (v : ValueTrial P O a s.step) (next : ℝ) : State E :=
  if P.eta1 ≤ v.ratio then
    ⟨⟨a.point + s.step, next, s.radii, a.request, true⟩, some v.request⟩ else
    ⟨⟨a.point, next, I.radii, a.request, false⟩, some v.currentRequest⟩

/-- The three nonterminal branches preserve actual search and inner witnesses. An all-pass
inspection refines only when the observable error check fails. The short-step tensor test
checks through `q`, exactly as in the literal source algorithm. -/
inductive Transition {f : E → ℝ} (P : Parameters) (O : Oracle f P.p)
    (a : State E) (I : Inspection P O.derivative a) :
    State E → Bool → Bool → List (E × ℝ) → Prop where
  | refineInspection (hall : I.order = P.q + 1) (herr : ¬ErrorCheck P a I) :
      Transition P O a I (refine P a) false false []
  | refineStep (hq : I.order ≤ P.q)
      (s : InexactRegularization.InnerResult P.toImplicitParameters 0
        (O.derivative a.point a.request)
        a.sigma I.radii (I.direction hq))
      (hinaccurate : ¬InexactRegularization.StepAccurate P.toImplicitParameters P.q
        a.request s.step) :
      Transition P O a I (refine P a) false false []
  | trial (hq : I.order ≤ P.q)
      (s : InexactRegularization.InnerResult P.toImplicitParameters 0
        (O.derivative a.point a.request)
        a.sigma I.radii (I.direction hq))
      (haccurate : InexactRegularization.StepAccurate P.toImplicitParameters P.q
        a.request s.step)
      (v : ValueTrial P O a s.step) (next : ℝ)
      (hupdate : HigherOrderApproximateRegularization.ParameterUpdate
        P.toImplicitParameters.toParameters
        v.ratio a.sigma next) :
      Transition P O a I (trialState a I hq s v next) true
        (decide (P.eta1 ≤ v.ratio)) v.queries

/-- Finite executions stop at the actual inspection certificate; no true-quality, parameter
upper bound, evaluation count, or future success is assumed. All cache keys are operational. -/
structure Execution {f : E → ℝ} (P : Parameters) (O : Oracle f P.p) (N : ℕ) where
  state : ℕ → State E
  inspection : ∀ k, Inspection P O.derivative (state k)
  trial : ℕ → Bool
  accepted : ℕ → Bool
  queries : ℕ → List (E × ℝ)
  initial_fresh : (state 0).fresh = true
  initial_cache : (state 0).valueCache = none
  initial_sigma : P.sigmaMin ≤ (state 0).sigma
  initial_radii : HigherOrderApproximateRegularization.ValidRadii
    P.toImplicitParameters.toParameters
    (state 0).radii
  initial_tolerance : ∀ j, 1 ≤ j → j ≤ P.q → P.epsilon j ≤ (state 0).radii j
  initial_request : ∀ i ∈ Finset.Icc 1 P.p, 0 < (state 0).request i
  initial_request_le : ∀ i ∈ Finset.Icc 1 P.p, (state 0).request i ≤ P.kappaInitial
  transition : ∀ k, k < N → Transition P O (state k) (inspection k) (state (k + 1))
    (trial k) (accepted k) (queries k)

/-- A full run obeys the operational transitions until its first observable certificate. -/
def IsExecution {f : E → ℝ} (P : Parameters) (O : Oracle f P.p)
    (state : ℕ → State E) (inspection : ∀ k, Inspection P O.derivative (state k))
    (trial accepted : ℕ → Bool) (queries : ℕ → List (E × ℝ)) : Prop :=
  ∀ N, (∀ k < N, ¬Certified P (state k) (inspection k)) →
    ∃ r : Execution P O N, r.state = state ∧ HEq r.inspection inspection ∧
      r.trial = trial ∧ r.accepted = accepted ∧ r.queries = queries

/-- Actual value requests concatenate the executed trial logs; initialization adds no call. -/
def Execution.functionQueries {f : E → ℝ} {P : Parameters} {O : Oracle f P.p} {N : ℕ}
    (r : Execution P O N) : List (E × ℝ) :=
  ((List.range N).map r.queries).flatten

/-- Full tensor batches are requested initially and after accepted steps or refinements,
including the final inspected state. Rejected trials retain their exact point/request key. -/
def Execution.derivativeQueries {f : E → ℝ} {P : Parameters} {O : Oracle f P.p} {N : ℕ}
    (r : Execution P O N) : List (E × (ℕ → ℝ)) :=
  (((Finset.range (N + 1)).filter fun k => (r.state k).fresh).sort (· ≤ ·)).map
    fun k => ((r.state k).point, (r.state k).request)

end Optimization.ExplicitRegularization
