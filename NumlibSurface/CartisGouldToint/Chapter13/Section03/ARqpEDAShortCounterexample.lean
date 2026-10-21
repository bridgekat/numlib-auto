import NumlibSurface.CartisGouldToint.Chapter13.Section03.ARqpEDA
import NumlibSurface.CartisGouldToint.Chapter13.Section01.ARqpIDAShortCounterexample

/-!
# A short-step counterexample to the literal ARqpEDA decrease bounds

The reusable tiny linear-model trial from Section 13.1 has a known-error oracle valid
at every positive request and exact scalar values. The stricter accuracy constant
`kappa_s=1/16` satisfies (13.3.13). Both actual endpoint calls share the positive request
`2⁻²⁶`, satisfying (13.3.18), and the actual ratio accepts the step `2⁻²⁰`.
The objective satisfies f.D0pL with unit constants; its true gradient remains one.
Both printed decrease bounds in Lemma 13.3.7 fail. Boundedness below is not assumed
in that lemma, and no claim about Theorem 13.3.8 follows from this example.
-/

noncomputable section
open scoped Nat
namespace CartisGouldToint.Chapter13.Section03
open Optimization InexactTaylorModels

/-- A complete legal literal ARqpEDA trial refutes both decrease bounds in Lemma 13.3.7.
All global Lipschitz constants and known tensor-error multipliers equal one. The actual
inner minimizer has norm `2⁻²⁰`; twenty actual first-search halvings retain it. Both
endpoint values are exact, the source common request is positive, and both calls are
logged. True approximate optimality fails at both states, and the prescribed model
radius conditions hold. -/
theorem literal_arqpeda_tiny_step_decrease_counterexample :
    ∃ (P : ARqpEDAParameters) (f : EuclideanSpace ℝ (Fin 1) → ℝ)
      (O : ExplicitAccuracyOracle f P.p) (r : algorithm_13_3_2 P O 1),
    P.p = 2 ∧ P.q = 1 ∧ Section01.ImplicitSmoothness f P.p ∧
    (∀ i ≤ P.p, ∀ x y,
      ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ 1 * ‖x - y‖) ∧
    (∀ x h, O.value x h = f x) ∧
    r.trial 0 = true ∧ r.accepted 0 = true ∧ (r.queries 0).length = 2 ∧
    (∀ j ≤ 2, (r.state 1).radii j = 1) ∧
    (∀ j, 3 ≤ j → j ≤ P.q →
      P.fraction * P.theta / (24 * max (1 + P.kappaInitial) (r.state 0).sigma) *
        P.epsilon j ≤ (r.state 1).radii j) ∧
    (∀ k ≤ 1, ¬HigherOrderApproximateRegularization.SatisfiesCriteria
      P.toImplicitParameters.toParameters f (r.state k).point (r.state k).radii) ∧
    let σmax := max (r.state 0).sigma
      (P.gamma3 * ((2 * (1 : ℝ) + 4 * ((P.p + 1)! : ℝ) * P.kappaStep) /
        (1 - P.eta2)))
    let κ := P.sigmaMin / ((P.p + 1)! : ℝ) *
      ((1 - P.theta) / (2 * (P.q ! : ℝ) *
        (1 + σmax + 3 * P.kappaStep))) ^
        (((P.p + 1 : ℕ) : ℝ) / (P.p - P.q + 1 : ℕ))
    decrement (O.derivative (r.state 0).point (r.state 0).request) P.p
        ((r.state 1).point - (r.state 0).point) <
      κ * P.epsilon 1 ^ (((P.p + 1 : ℕ) : ℝ) / (P.p - 1 + 1 : ℕ)) ∧
    f (r.state 0).point - f (r.state 1).point <
      P.eta1 / 2 * κ * P.epsilon 1 ^
        (((P.p + 1 : ℕ) : ℝ) / (P.p - 1 + 1 : ℕ)) := by
  let d := Section01.TinyStep.explicitTrial
  exact ⟨d.parameters, d.objective, d.oracle, d.execution,
    Section01.TinyStep.explicitTrial_properties⟩

end CartisGouldToint.Chapter13.Section03
