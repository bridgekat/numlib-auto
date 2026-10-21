import Numlib.Optimization.ConstrainedExplicitRegularization
import NumlibSurface.CartisGouldToint.Chapter13.Section03.ARqpEDACertificationCounterexample
import NumlibSurface.CartisGouldToint.Chapter14.Section02

/-!
# The all-space ARqpEDA-SC leaf and a fixed-data certification counterexample

The source modifications (14.2.2)–(14.2.5) use actual constrained polynomial searches,
model witnesses and feasible detailed inner executions. Their all-space embeddings retain
all selected operations and oracle logs. Unit incoming and actual returned radii satisfy
the source Step 2 policy; the selected outer inspection radii still record literal halvings.
Global anchored and bounded jets hold on the full initial feasible sublevel. One fixed
family refutes the observable termination/function-count row of Theorem 14.2.4.
-/

noncomputable section
open Set Optimization
namespace CartisGouldToint.Chapter14.Section02.ARqpEDAUniv
open TransverseObjective ExplicitRegularization TransverseRegularizationContinuation
open TransverseQualifiedContinuation TransverseCertificationRates

/-- The explicit all-space leaf of ARqpEDA-SC uses genuine constrained operations.
No assertion concerning a solver or its complexity on a general feasible set is made. -/
abbrev algorithm {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} (P : Parameters)
    (O : Oracle f P.p) (state : ℕ → State (EuclideanSpace ℝ (Fin n)))
    (inspection : ∀ k, ConstrainedExplicitRegularization.Inspection univ P O.derivative (state k))
    (trial accepted : ℕ → Bool) (queries : ℕ → List (EuclideanSpace ℝ (Fin n) × ℝ)) : Prop :=
  ConstrainedExplicitRegularization.IsExecution univ P O state inspection trial accepted queries

/-- Every original full run embeds with the same whole states, cache, requests and queries. -/
theorem algorithm_of_unconstrained {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : Parameters} {O : Oracle f P.p} {state : ℕ → State (EuclideanSpace ℝ (Fin n))}
    {inspection : ∀ k, Inspection P O.derivative (state k)} {trial accepted : ℕ → Bool}
    {queries : ℕ → List (EuclideanSpace ℝ (Fin n) × ℝ)}
    (h : Chapter13.Section03.ARqpEDA.algorithm P O state inspection trial accepted queries) :
    algorithm P O state
      (fun k => ConstrainedRegularizationOperations.Inspection.ofUnconstrained
        (state k).point (inspection k)) trial accepted queries :=
  ConstrainedExplicitRegularization.isExecution_of_unconstrained h

/-- All-space constraints are simple: their actual translated subproblems and attained
model minima coincide with the internal unconstrained problems using the same coefficients.
No constraint oracle or extra objective/tensor access occurs in these identities. -/
theorem univ_internal_subproblems {n : ℕ} :
    (∀ (x : EuclideanSpace ℝ (Fin n)) (δ : ℝ),
      feasibleDisplacements univ x ∩ Metric.closedBall 0 δ = Metric.closedBall 0 δ) ∧
    (∀ (x : EuclideanSpace ℝ (Fin n)) (A : InexactRegularization.Coefficients _)
      (j : ℕ) (δ : ℝ),
      ConstrainedRegularizationOperations.coefficientGap univ x A j δ =
        TaylorCriticality.gapOn (InexactTaylorModels.decrement A j) (Metric.closedBall 0 δ)) ∧
    (∀ (x z : EuclideanSpace ℝ (Fin n)) (m : EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ t, x + t ∈ (univ : Set _) → m z ≤ m t) ↔ ∀ t, m z ≤ m t) := by
  refine ⟨?_, ConstrainedRegularizationOperations.coefficientGap_univ, ?_⟩
  · intros
    simp [feasibleDisplacements, ConstrainedTaylorCriticality.feasibleDisplacements]
  · intros
    simp

/-- Every outer control is fixed before the tolerance vector is replaced, as an equality
of entire parameter records, with the same objective, oracle and initial state. -/
theorem transverse_fixed_controls {ε₀ ε : ℝ}
    (h₀ : 0 < ε₀) (h₀1 : ε₀ < 1) (hε : 0 < ε) (hε1 : ε < 1) :
    (parameters ε₀ h₀ h₀1).withTolerances (fun _ => ε)
      (fun _ _ _ => hε) (fun _ _ _ => hε1) = parameters ε hε hε1 :=
  parameters_withTolerances h₀ h₀1 hε hε1

/-- The favorable ARqpEDA-SC row is exactly the three-halves exponent for p=2,q=1. -/
theorem transverse_table_exponent :
    simpleConstraintExponent .arEDA 2 1 1 (univ : Set Plane)
      (fun _ : EuclideanSpace ℝ (Fin 0) => 0) = 3 / 2 := by
  norm_num [simpleConstraintExponent, convex_univ]

/-- The fixed initial point fails the true constrained unit-radius first-order test. -/
theorem transverse_initial_not_optimal {ε : ℝ} (hsmall : ε ≤ 1 / 65536) :
    ε < constrainedTaylorGap objective univ 1 initialState.point 1 := by
  rw [constrainedTaylorGap_univ]
  exact Chapter13.Section03.transverse_arqpeda_initial_not_optimal hsmall

/-- The actual positive jets are globally bounded: differentiate the globally Lipschitz
jet of one lower order, using the norm-preserving currying identity. -/
theorem transverse_bounded_positive_jets (j : ℕ) (hj : 1 ≤ j) (hjp : j ≤ 2) (x : Plane) :
    ‖iteratedFDeriv ℝ j objective x‖ ≤ 4 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  rw [← norm_fderiv_iteratedFDeriv]
  exact norm_fderiv_le_of_lipschitz ℝ (lipschitz_jets i (by omega))

/-- The source f.D0pLaB.X holds on the full initial feasible sublevel, with one fixed
open convex ambient set and fixed constants, independently of every tolerance. -/
theorem transverse_source_smoothness :
    SmoothBoundedJetsOnLevelSet objective univ initialState.point 2 true univ
      (fun _ => 4) (fun _ => 4) where
  isOpen := isOpen_univ
  convex := convex_univ
  centers_subset := subset_univ _
  contDiffOn := contDiff_objective.contDiffOn
  lipschitz_nonneg := by intros; norm_num
  bound_nonneg := by intros; norm_num
  bound j hj hjp x _ d := by
    have h := (iteratedFDeriv ℝ j objective x).le_opNorm (fun _ => d)
    have hb := transverse_bounded_positive_jets j hj hjp x
    simpa using h.trans
      (mul_le_mul_of_nonneg_right hb (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  lipschitz j _ hjp x _ y _ d := by
    have h := (lipschitz_jets j hjp).norm_sub_le y x
    have hh := (iteratedFDeriv ℝ j objective y - iteratedFDeriv ℝ j objective x).le_opNorm
      (fun _ => d)
    simpa using hh.trans
      (mul_le_mul_of_nonneg_right h (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  initial_feasible := mem_univ _
  feasible_subset := subset_refl _
  lipschitz_one_le := by intros; norm_num
  bound_one_le := by intros; norm_num

/-- The objective lies between zero and one on the entire fixed initial feasible sublevel. -/
theorem transverse_sublevel_value_bound (x : Plane)
    (hx : x ∈ feasibleSublevelSet objective univ initialState.point) :
    0 ≤ objective x ∧ |objective x| ≤ 1 := by
  have hinit : objective initialState.point = 1 := objective_initial
  have hu : objective x ≤ 1 := by simpa only [hinit] using hx.2
  exact ⟨objective_nonneg x, by simpa only [abs_of_nonneg (objective_nonneg x)] using hu⟩

/-- One fixed family supplies actual all-space source executions from the same whole state. -/
theorem transverse_algorithm {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hsmall : ε ≤ 1 / 65536) :
    let s := chosenRun hε hε1 hsmall
    (s.node 0).state = initialState ∧
      algorithm (parameters ε hε hε1) exactOracle
        (fun k => (s.node k).state)
        (fun k => ConstrainedRegularizationOperations.Inspection.ofUnconstrained
          (s.node k).state.point (s.node k).inspection) s.trial s.accepted s.queries :=
  ⟨chosenRun_initial hε hε1 hsmall,
    algorithm_of_unconstrained (chosenRun_isExecution hε hε1 hsmall)⟩

/-- Every actual incoming outer radius equals one. The all-space inspection embedding
preserves its selected dyadic radii and does not replace them by incoming unit radii. -/
theorem transverse_incoming_radii {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hsmall : ε ≤ 1 / 65536) (k j : ℕ) :
    ((chosenRun hε hε1 hsmall).node k).state.radii j = 1 ∧
    (ConstrainedRegularizationOperations.Inspection.ofUnconstrained
      ((chosenRun hε hε1 hsmall).node k).state.point
      ((chosenRun hε hε1 hsmall).node k).inspection).radii j =
        ((chosenRun hε hε1 hsmall).node k).inspection.radii j := by
  exact ⟨congrFun ((chosenRun hε hε1 hsmall).node k).valid.2.2.2.2.2.1 j, rfl⟩

/-- Every actual converted inner call has unit returned radii and the fixed initialization
fraction, including a call discarded by outer request refinement. All inner states persist. -/
theorem transverse_return_policy {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hsmall : ε ≤ 1 / 65536) :
    let s := chosenRun hε hε1 hsmall
    ∀ (k : ℕ)
      (hn : ¬Certified (parameters ε hε hε1) (s.node k).state (s.node k).inspection)
      (hq : (s.node k).inspection.order ≤ (parameters ε hε hε1).q)
      (R : Returned (s.node k).inspection hq),
      (s.branch k hn).innerCall = some ⟨hq, R⟩ →
        let C := ConstrainedRegularizationOperations.InnerResult.ofUnconstrained
          (s.node k).state.point R.result
        (∀ j, C.radii j = 1) ∧ C.execution.state = R.result.execution.state ∧
          (C.execution.state 0).mu = ‖fderiv ℝ objective (s.node k).state.point‖ ^ 2 / 100 := by
  dsimp only
  intro k hn hq R hcall
  exact ⟨fun j => Branch.innerCall_radii _ hcall j, rfl, Branch.innerCall_mu _ hcall⟩

/-- Every proposed corrected bound fails at arbitrarily small tolerances on the already
fixed actual constrained family, before any eventual certificate can occur. -/
theorem exists_rate_violating_run (A C : ℝ) (M : ℕ) :
    ∃ (m : ℕ) (hm : max 3 M ≤ m),
      let h3 := (le_max_left 3 M).trans hm
      let ε := TransverseDyadicRates.epsilon m
      let hε := TransverseDyadicRates.epsilon_pos m
      let hε1 := dyadic_epsilon_lt_one h3
      let hsmall := TransverseDyadicRates.epsilon_le h3
      let s := chosenRun hε hε1 hsmall
      ∀ k, ConstrainedExplicitRegularization.Certified (parameters ε hε hε1)
        (s.node k).state
        (ConstrainedRegularizationOperations.Inspection.ofUnconstrained
          (s.node k).state.point (s.node k).inspection) →
        A * ε ^ (-(3 / 2 : ℝ)) + C < (functionQueries s k).length :=
  TransverseCertificationRates.exists_rate_violating_run A C M

/-- There is no eventually uniform corrected three-halves function-count bound.
The two coefficients and the minimum dyadic index precede the tolerance choice. -/
theorem no_uniform_certification_bound :
    ¬∃ (A C : ℝ) (M : ℕ), ∀ (m : ℕ) (hm : max 3 M ≤ m),
      let h3 := (le_max_left 3 M).trans hm
      let ε := TransverseDyadicRates.epsilon m
      let hε := TransverseDyadicRates.epsilon_pos m
      let hε1 := dyadic_epsilon_lt_one h3
      let hsmall := TransverseDyadicRates.epsilon_le h3
      let s := chosenRun hε hε1 hsmall
      ∃ k, ConstrainedExplicitRegularization.Certified (parameters ε hε hε1)
        (s.node k).state
        (ConstrainedRegularizationOperations.Inspection.ofUnconstrained
          (s.node k).state.point (s.node k).inspection) ∧
        (functionQueries s k).length ≤ A * ε ^ (-(3 / 2 : ℝ)) + C := by
  rintro ⟨A, C, M, hbound⟩
  obtain ⟨m, hm, hviol⟩ := exists_rate_violating_run A C M
  obtain ⟨k, hc, hq⟩ := hbound m hm
  exact (not_lt_of_ge hq) (hviol k hc)

/-- The ARqpEDA-SC row of Theorem 14.2.4 fails for one closed, nonempty convex simple
all-space feasible set, one globally regular bounded-below objective and one fixed actual
execution family. Its full initial state and all controls precede all tolerances and rate
coefficients. The actual returned-radius policy is proved by `transverse_return_policy`;
its selected inspection radii, complete searches and all oracle logs remain unchanged. -/
theorem literal_arqpeda_sc_uniform_certification_counterexample :
    IsClosed (univ : Set Plane) ∧ (univ : Set Plane).Nonempty ∧
    Convex ℝ (univ : Set Plane) ∧
    (∀ (x : Plane) (δ : ℝ), feasibleDisplacements univ x ∩ Metric.closedBall 0 δ =
      Metric.closedBall 0 δ) ∧
    SmoothBoundedJetsOnLevelSet objective univ initialState.point 2 true univ
      (fun _ => 4) (fun _ => 4) ∧
    (∀ x, 0 ≤ objective x) ∧ objective initialState.point = 1 ∧
    (∀ (ε₀ ε : ℝ) (h₀ : 0 < ε₀) (h₀1 : ε₀ < 1) (hε : 0 < ε) (hε1 : ε < 1),
      (parameters ε₀ h₀ h₀1).withTolerances (fun _ => ε)
        (fun _ _ _ => hε) (fun _ _ _ => hε1) = parameters ε hε hε1) ∧
    (∀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hsmall : ε ≤ 1 / 65536),
      let s := chosenRun hε hε1 hsmall
      (s.node 0).state = initialState ∧
      algorithm (parameters ε hε hε1) exactOracle (fun k => (s.node k).state)
        (fun k => ConstrainedRegularizationOperations.Inspection.ofUnconstrained
          (s.node k).state.point (s.node k).inspection) s.trial s.accepted s.queries ∧
      (∀ k j, (s.node k).state.radii j = 1) ∧
      ∀ (k : ℕ)
        (hn : ¬Certified (parameters ε hε hε1) (s.node k).state (s.node k).inspection)
        (hq : (s.node k).inspection.order ≤ (parameters ε hε hε1).q)
        (R : Returned (s.node k).inspection hq),
        (s.branch k hn).innerCall = some ⟨hq, R⟩ →
          let C := ConstrainedRegularizationOperations.InnerResult.ofUnconstrained
            (s.node k).state.point R.result
          (∀ j, C.radii j = 1) ∧ C.execution.state = R.result.execution.state ∧
            (C.execution.state 0).mu =
              ‖fderiv ℝ objective (s.node k).state.point‖ ^ 2 / 100) ∧
    ¬∃ (A C : ℝ) (M : ℕ), ∀ (m : ℕ) (hm : max 3 M ≤ m),
      let h3 := (le_max_left 3 M).trans hm
      let ε := TransverseDyadicRates.epsilon m
      let hε := TransverseDyadicRates.epsilon_pos m
      let hε1 := dyadic_epsilon_lt_one h3
      let hsmall := TransverseDyadicRates.epsilon_le h3
      let s := chosenRun hε hε1 hsmall
      ∃ k, ConstrainedExplicitRegularization.Certified (parameters ε hε hε1)
        (s.node k).state
        (ConstrainedRegularizationOperations.Inspection.ofUnconstrained
          (s.node k).state.point (s.node k).inspection) ∧
        (functionQueries s k).length ≤ A * ε ^ (-(3 / 2 : ℝ)) + C := by
  refine ⟨isClosed_univ, ⟨0, mem_univ _⟩, convex_univ, univ_internal_subproblems.1,
    transverse_source_smoothness,
    objective_nonneg, objective_initial,
    (fun _ _ h₀ h₀1 hε hε1 => transverse_fixed_controls h₀ h₀1 hε hε1),
    ?_, no_uniform_certification_bound⟩
  intro ε hε hε1 hsmall
  exact ⟨(transverse_algorithm hε hε1 hsmall).1,
    (transverse_algorithm hε hε1 hsmall).2,
    (fun k j => (transverse_incoming_radii hε hε1 hsmall k j).1),
    transverse_return_policy hε hε1 hsmall⟩

end CartisGouldToint.Chapter14.Section02.ARqpEDAUniv
