import Numlib.Optimization.ConstrainedRegularizationOperations

/-!
# Explicit-accuracy regularization with feasible model operations

The outer branches use actual constrained inspections and returned inner executions.
All-space embeddings keep the whole state, requests, cache, query lists and branch labels.
Feasibility of all-space directions is internal set membership, with no added oracle call.
These definitions assert neither general constrained solver existence nor complexity.
-/

noncomputable section
open Set
open scoped Nat
namespace Optimization.ConstrainedExplicitRegularization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An actual completed constrained inspection at the current point and supplied tensors. -/
abbrev Inspection (X : Set E) (P : ExplicitRegularization.Parameters)
    (oracle : E → (ℕ → ℝ) → InexactRegularization.Coefficients E) (a :
      ExplicitRegularization.State E) :=
  ConstrainedRegularizationOperations.Inspection X a.point P.toImplicitParameters 0
    (oracle a.point a.request) a.sigma a.radii

/-- The source observable error sum uses every actual constrained inspected radius. -/
def ErrorCheck {X : Set E} (P : ExplicitRegularization.Parameters) {oracle : E → (ℕ → ℝ) →
  InexactRegularization.Coefficients E}
    (a : ExplicitRegularization.State E) (I : Inspection X P oracle a) : Prop :=
  ∀ j, 1 ≤ j → j ≤ P.q →
    ∑ i ∈ Finset.Icc 1 j, a.request i * I.radii j ^ i / (i ! : ℝ) ≤
      P.fraction * P.epsilon j * I.radii j ^ j / (2 * (j ! : ℝ))

/-- Computed stopping requires the actual all-order inspection and its observable error test. -/
def Certified {X : Set E} (P : ExplicitRegularization.Parameters)
    {oracle : E → (ℕ → ℝ) → InexactRegularization.Coefficients E}
    (a : ExplicitRegularization.State E) (I : Inspection X P oracle a) : Prop :=
  I.order = P.q + 1 ∧ ErrorCheck P a I

/-- The all-space error check is literally the original check, even after radius halvings. -/
theorem errorCheck_ofUnconstrained_iff (P : ExplicitRegularization.Parameters)
    {oracle : E → (ℕ → ℝ) → InexactRegularization.Coefficients E} (a :
      ExplicitRegularization.State E)
    (I : ExplicitRegularization.Inspection P oracle a) :
    ErrorCheck P a (ConstrainedRegularizationOperations.Inspection.ofUnconstrained a.point I) ↔
      ExplicitRegularization.ErrorCheck P a I := Iff.rfl

/-- The all-space certificate is exactly the original actual certificate. -/
theorem certified_ofUnconstrained_iff (P : ExplicitRegularization.Parameters)
    {oracle : E → (ℕ → ℝ) → InexactRegularization.Coefficients E} (a :
      ExplicitRegularization.State E)
    (I : ExplicitRegularization.Inspection P oracle a) :
    Certified P a (ConstrainedRegularizationOperations.Inspection.ofUnconstrained a.point I) ↔
      ExplicitRegularization.Certified P a I := Iff.rfl

/-- Trial updates retain the actual returned radii and the compatible value cache. -/
def trialState {X : Set E} {f : E → ℝ} {P : ExplicitRegularization.Parameters} {O :
  ExplicitRegularization.Oracle f P.p}
    (a : ExplicitRegularization.State E) (I : Inspection X P O.derivative a) (hq : I.order ≤ P.q)
    (s : ConstrainedRegularizationOperations.InnerResult X a.point P.toImplicitParameters 0
      (O.derivative a.point a.request) a.sigma I.radii (I.direction hq))
    (v : ExplicitRegularization.ValueTrial P O a s.step) (next : ℝ) :
      ExplicitRegularization.State E :=
  if P.eta1 ≤ v.ratio then
    ⟨⟨a.point + s.step, next, s.radii, a.request, true⟩, some v.request⟩ else
    ⟨⟨a.point, next, I.radii, a.request, false⟩, some v.currentRequest⟩

/-- Literal constrained outer branches retain all selected searches and inner calls. -/
inductive Transition (X : Set E) {f : E → ℝ} (P : ExplicitRegularization.Parameters) (O :
  ExplicitRegularization.Oracle f P.p)
    (a : ExplicitRegularization.State E) (I : Inspection X P O.derivative a) :
    ExplicitRegularization.State E → Bool → Bool → List (E × ℝ) → Prop where
  | refineInspection (hall : I.order = P.q + 1) (herr : ¬ErrorCheck P a I) :
      Transition X P O a I (ExplicitRegularization.refine P a) false false []
  | refineStep (hq : I.order ≤ P.q)
      (s : ConstrainedRegularizationOperations.InnerResult X a.point P.toImplicitParameters 0
        (O.derivative a.point a.request) a.sigma I.radii (I.direction hq))
      (hinaccurate : ¬InexactRegularization.StepAccurate P.toImplicitParameters P.q a.request
        s.step) :
      Transition X P O a I (ExplicitRegularization.refine P a) false false []
  | trial (hq : I.order ≤ P.q)
      (s : ConstrainedRegularizationOperations.InnerResult X a.point P.toImplicitParameters 0
        (O.derivative a.point a.request) a.sigma I.radii (I.direction hq))
      (haccurate : InexactRegularization.StepAccurate P.toImplicitParameters P.q a.request s.step)
      (v : ExplicitRegularization.ValueTrial P O a s.step) (next : ℝ)
      (hupdate : HigherOrderApproximateRegularization.ParameterUpdate
        P.toImplicitParameters.toParameters v.ratio a.sigma next) :
      Transition X P O a I (trialState a I hq s v next) true
        (decide (P.eta1 ≤ v.ratio)) v.queries

/-- Every literal original outer branch embeds with identical successor, events and queries.
The actual completed search and every inner state are transformed by the earlier embeddings. -/
theorem Transition.ofUnconstrained {f : E → ℝ} {P : ExplicitRegularization.Parameters}
    {O : ExplicitRegularization.Oracle f P.p} {a b : ExplicitRegularization.State E} {I :
      ExplicitRegularization.Inspection P O.derivative a}
    {t ac : Bool} {qs : List (E × ℝ)} (h : ExplicitRegularization.Transition P O a I b t ac qs) :
    Transition univ P O a (ConstrainedRegularizationOperations.Inspection.ofUnconstrained a.point
      I) b t ac qs := by
  cases h with
  | refineInspection hall herr => exact .refineInspection hall herr
  | refineStep hq s hi =>
    exact .refineStep hq
      (ConstrainedRegularizationOperations.InnerResult.ofUnconstrained a.point s) hi
  | trial hq s ha v next hu =>
    exact Transition.trial (P := P) (O := O) (I :=
      ConstrainedRegularizationOperations.Inspection.ofUnconstrained a.point I) hq
      (ConstrainedRegularizationOperations.InnerResult.ofUnconstrained a.point s)
      ha v next hu

/-- Every actual outer branch preserves feasibility of the current point. -/
theorem Transition.feasible {X : Set E} {f : E → ℝ} {P : ExplicitRegularization.Parameters}
    {O : ExplicitRegularization.Oracle f P.p} {a b : ExplicitRegularization.State E}
    {I : Inspection X P O.derivative a} {t ac : Bool} {qs : List (E × ℝ)}
    (h : Transition X P O a I b t ac qs) (ha : a.point ∈ X) : b.point ∈ X := by
  cases h with
  | refineInspection => exact ha
  | refineStep => exact ha
  | trial hq s ha v next hu =>
    unfold trialState
    split_ifs
    · exact s.feasible
    · exact ‹a.point ∈ X›

/-- Initialized finite constrained runs retain actual oracle and cache operations. -/
structure Execution (X : Set E) {f : E → ℝ} (P : ExplicitRegularization.Parameters) (O :
  ExplicitRegularization.Oracle f P.p)
    (N : ℕ) where
  state : ℕ → ExplicitRegularization.State E
  inspection : ∀ k, Inspection X P O.derivative (state k)
  trial : ℕ → Bool
  accepted : ℕ → Bool
  queries : ℕ → List (E × ℝ)
  initial_feasible : (state 0).point ∈ X
  initial_fresh : (state 0).fresh = true
  initial_cache : (state 0).valueCache = none
  initial_sigma : P.sigmaMin ≤ (state 0).sigma
  initial_radii : HigherOrderApproximateRegularization.ValidRadii
    P.toImplicitParameters.toParameters (state 0).radii
  initial_tolerance : ∀ j, 1 ≤ j → j ≤ P.q → P.epsilon j ≤ (state 0).radii j
  initial_request : ∀ i ∈ Finset.Icc 1 P.p, 0 < (state 0).request i
  initial_request_le : ∀ i ∈ Finset.Icc 1 P.p, (state 0).request i ≤ P.kappaInitial
  transition : ∀ k, k < N → Transition X P O (state k) (inspection k) (state (k + 1))
    (trial k) (accepted k) (queries k)

/-- Every point in an executed constrained prefix is feasible by the literal branch laws. -/
theorem Execution.feasible {X : Set E} {f : E → ℝ}
    {P : ExplicitRegularization.Parameters} {O : ExplicitRegularization.Oracle f P.p} {N : ℕ}
    (r : Execution X P O N) {k : ℕ} (hk : k ≤ N) : (r.state k).point ∈ X := by
  induction k with
  | zero => exact r.initial_feasible
  | succ k ih => exact (r.transition k (by omega)).feasible (ih (by omega))

/-- An actual original finite execution embeds with every data field unchanged. -/
def Execution.ofUnconstrained {f : E → ℝ} {P : ExplicitRegularization.Parameters} {O :
  ExplicitRegularization.Oracle f P.p}
    {N : ℕ} (r : ExplicitRegularization.Execution P O N) : Execution univ P O N where
  state := r.state
  inspection k := ConstrainedRegularizationOperations.Inspection.ofUnconstrained (r.state
    k).point (r.inspection k)
  trial := r.trial
  accepted := r.accepted
  queries := r.queries
  initial_feasible := mem_univ _
  initial_fresh := r.initial_fresh
  initial_cache := r.initial_cache
  initial_sigma := r.initial_sigma
  initial_radii := r.initial_radii
  initial_tolerance := r.initial_tolerance
  initial_request := r.initial_request
  initial_request_le := r.initial_request_le
  transition k hk := Transition.ofUnconstrained (r.transition k hk)

/-- The actual value log is the concatenation of the stored executed trial requests. -/
def Execution.functionQueries {X : Set E} {f : E → ℝ}
    {P : ExplicitRegularization.Parameters} {O : ExplicitRegularization.Oracle f P.p} {N : ℕ}
    (r : Execution X P O N) : List (E × ℝ) :=
  ((List.range N).map r.queries).flatten

/-- The tensor log uses exactly the fresh states, including the final inspected state. -/
def Execution.derivativeQueries {X : Set E} {f : E → ℝ}
    {P : ExplicitRegularization.Parameters} {O : ExplicitRegularization.Oracle f P.p} {N : ℕ}
    (r : Execution X P O N) : List (E × (ℕ → ℝ)) :=
  (((Finset.range (N + 1)).filter fun k => (r.state k).fresh).sort (· ≤ ·)).map
    fun k => ((r.state k).point, (r.state k).request)

/-- All-space transport adds no actual value query and preserves the exact request list. -/
@[simp] theorem Execution.ofUnconstrained_functionQueries {f : E → ℝ}
    {P : ExplicitRegularization.Parameters} {O : ExplicitRegularization.Oracle f P.p} {N : ℕ}
    (r : ExplicitRegularization.Execution P O N) :
    (Execution.ofUnconstrained r).functionQueries = r.functionQueries := rfl

/-- All-space transport adds no tensor batch and preserves its exact point/request keys. -/
@[simp] theorem Execution.ofUnconstrained_derivativeQueries {f : E → ℝ}
    {P : ExplicitRegularization.Parameters} {O : ExplicitRegularization.Oracle f P.p} {N : ℕ}
    (r : ExplicitRegularization.Execution P O N) :
    (Execution.ofUnconstrained r).derivativeQueries = r.derivativeQueries := rfl

/-- Full constrained runs obey actual operations through every pre-certificate prefix. -/
def IsExecution (X : Set E) {f : E → ℝ} (P : ExplicitRegularization.Parameters) (O :
  ExplicitRegularization.Oracle f P.p)
    (state : ℕ → ExplicitRegularization.State E) (inspection : ∀ k, Inspection X P O.derivative
      (state k))
    (trial accepted : ℕ → Bool) (queries : ℕ → List (E × ℝ)) : Prop :=
  ∀ N, (∀ k < N, ¬Certified P (state k) (inspection k)) →
    ∃ r : Execution X P O N, r.state = state ∧ HEq r.inspection inspection ∧
      r.trial = trial ∧ r.accepted = accepted ∧ r.queries = queries

/-- Every actual original full run is a source-constrained full run on all space.
All actual states, request/cache data, event labels and oracle-query lists are identical. -/
theorem isExecution_of_unconstrained {f : E → ℝ} {P : ExplicitRegularization.Parameters} {O :
  ExplicitRegularization.Oracle f P.p}
    {state : ℕ → ExplicitRegularization.State E} {inspection : ∀ k,
      ExplicitRegularization.Inspection P O.derivative (state k)}
    {trial accepted : ℕ → Bool} {queries : ℕ → List (E × ℝ)}
    (h : ExplicitRegularization.IsExecution P O state inspection trial accepted queries) :
    IsExecution univ P O state
      (fun k => ConstrainedRegularizationOperations.Inspection.ofUnconstrained (state k).point
        (inspection k)) trial accepted queries := by
  intro N hn
  obtain ⟨r, hr, hi, ht, ha, hq⟩ := h N hn
  subst state
  have hi' : r.inspection = inspection := eq_of_heq hi
  subst inspection
  exact ⟨Execution.ofUnconstrained r, rfl, HEq.rfl, ht, ha, hq⟩

end Optimization.ConstrainedExplicitRegularization
