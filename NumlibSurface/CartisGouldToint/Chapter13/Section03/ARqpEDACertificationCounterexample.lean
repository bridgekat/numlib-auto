import NumlibSurface.CartisGouldToint.Chapter13.Section03.ARqpEDA
import Numlib.Optimization.TransverseCertificationRates

/-!
# A fixed-data certification-rate counterexample to Theorem 13.3.8

One globally smooth bounded-below Euclidean objective and one exact known-error oracle
have a fixed initialization and fixed outer controls. Actual returned low-order radii equal
one, and every inner call uses the same squared-gradient fraction rule. The selected full
execution family defeats every tolerance-independent corrected three-halves function bound
for the algorithm's observable certification. Its initial point fails true first-order quality.
-/

noncomputable section
namespace CartisGouldToint.Chapter13.Section03
open Optimization ExplicitRegularization TransverseObjective
open TransverseRegularizationContinuation TransverseQualifiedContinuation
open TransverseCertificationRates

/-- The fixed initial point fails the true first-order unit-ball criterion throughout the
small-tolerance family; the example does not start at an already approximate minimizer. -/
theorem transverse_arqpeda_initial_not_optimal {ε : ℝ} (hsmall : ε ≤ 1 / 65536) :
    ε < TaylorCriticality.gapOn
      (TaylorCriticality.taylorDecrement objective 1 initialState.point)
      (Metric.closedBall 0 1) := by
  change ε < TaylorCriticality.gapOn
    (TaylorCriticality.taylorDecrement objective 1 (point 0 1)) (Metric.closedBall 0 1)
  rw [first_gap_initial]
  linarith

/-- Every selected family member is an actual full Algorithm 13.3.2 execution, with the
same entire initial state, including all unit requests, freshness and empty cache. -/
theorem transverse_arqpeda_algorithm {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hsmall : ε ≤ 1 / 65536) :
    let s := chosenRun hε hε1 hsmall
    (s.node 0).state = initialState ∧
      ARqpEDA.algorithm (parameters ε hε hε1) exactOracle
        (fun k => (s.node k).state) (fun k => (s.node k).inspection)
        s.trial s.accepted s.queries :=
  ⟨chosenRun_initial hε hε1 hsmall, chosenRun_isExecution hε hε1 hsmall⟩

/-- Every actual returned inner call, including one discarded by accuracy refinement,
satisfies (13.1.69) and retains the fixed squared-gradient initialization rule. -/
theorem transverse_arqpeda_return_policy {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hsmall : ε ≤ 1 / 65536) :
    let s := chosenRun hε hε1 hsmall
    ∀ (k : ℕ)
      (hn : ¬Certified (parameters ε hε hε1) (s.node k).state (s.node k).inspection)
      (hq : (s.node k).inspection.order ≤ (parameters ε hε hε1).q)
      (R : Returned (s.node k).inspection hq),
      (s.branch k hn).innerCall = some ⟨hq, R⟩ →
        (∀ j, R.result.radii j = 1) ∧
        (R.result.execution.state 0).mu =
          ‖fderiv ℝ objective (s.node k).state.point‖ ^ 2 / 100 := by
  dsimp only
  intro k hn hq R hcall
  exact ⟨fun j => Branch.innerCall_radii _ hcall j, Branch.innerCall_mu _ hcall⟩

/-- Source inequality (13.1.70) has no active order in this q=1 family. -/
theorem transverse_arqpeda_higher_radius_policy {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (j : ℕ) :
    ¬(3 ≤ j ∧ j ≤ (parameters ε hε hε1).q) :=
  higher_radius_policy_vacuous hε hε1 j

/-- All outer controls are fixed before tolerances: only their requested tolerance vector
is replaced, including neither the initialization nor any endpoint-accuracy control. -/
theorem transverse_arqpeda_fixed_controls {ε₀ ε : ℝ}
    (h₀ : 0 < ε₀) (h₀1 : ε₀ < 1) (hε : 0 < ε) (hε1 : ε < 1) :
    (parameters ε₀ h₀ h₀1).withTolerances (fun _ => ε)
      (fun _ _ _ => hε) (fun _ _ _ => hε1) = parameters ε hε hε1 :=
  parameters_withTolerances h₀ h₀1 hε hε1

/-- Theorem 13.3.8's actual-certification function bound is false even with arbitrary
corrected positive constants. This single fixed Euclidean objective satisfies f.D0pL and
f.Bb with initial gap one, has the actual source algorithm and radius policies above, and
has no tolerance-independent pair of coefficients guaranteeing certified termination. -/
theorem literal_arqpeda_uniform_certification_counterexample :
    ContDiff ℝ 2 objective ∧
    (∀ j, j ≤ 2 → LipschitzWith 4 (iteratedFDeriv ℝ j objective)) ∧
    (∀ x, 0 ≤ objective x) ∧ objective initialState.point = 1 ∧
    ¬∃ A C : ℝ, ∀ (m : ℕ) (hm : 3 ≤ m),
      let ε := TransverseDyadicRates.epsilon m
      let hε := TransverseDyadicRates.epsilon_pos m
      let hε1 := dyadic_epsilon_lt_one hm
      let hsmall := TransverseDyadicRates.epsilon_le hm
      let s := chosenRun hε hε1 hsmall
      ∃ k, Certified (parameters ε hε hε1) (s.node k).state (s.node k).inspection ∧
        (functionQueries s k).length ≤ A * ε ^ (-(3 / 2 : ℝ)) + C :=
  ⟨contDiff_objective, lipschitz_jets, objective_nonneg, objective_initial,
    no_uniform_certification_bound⟩

end CartisGouldToint.Chapter13.Section03
