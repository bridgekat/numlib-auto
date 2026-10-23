import Numlib.Optimization.Constrained.LagrangianStability
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Equality constraints and local Lagrangian stability

The restricted criticality is the supremum of actual Lagrangian Taylor decrements
on the specified allowed displacements. The augmented multiplier norm is exactly
the Euclidean norm of `(1,y)`. Local smoothness is required on an open set containing
the radius ball; this resolves the source's ambiguous use of “diameter”. The final
constraint equalities refer to the same displacement `d` as the conclusion.
When both Lipschitz constants vanish, the entire radius ball is allowed, as in footnote 111.
-/

namespace CartisGouldToint

/-- **Theorem 14.3.2.** Actual approximate Lagrangian Taylor criticality implies
both printed objective stability bounds, with the exact feasibility loss, factorial,
augmented multiplier factor and square-root-two stability radius. All assumptions
are local, and the allowed displacement set need not be closed or convex. -/
theorem theorem_14_3_2 {n m j : ℕ} (hj : 1 ≤ j) (_hj3 : j ≤ 3)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (X D V : Set (EuclideanSpace ℝ (Fin n))) (_hX : IsClosed X) (_hXne : X.Nonempty)
    (x : EuclideanSpace ℝ (Fin n)) (_hx : x ∈ X) (hD : IsOpen D)
    (_hV : V ⊆ TaylorModel.feasibleDisplacements X x)
    (hf : ContDiffOn ℝ j f D) (hc : ContDiffOn ℝ j c D)
    (y : EuclideanSpace ℝ (Fin m)) {δ ε₀ ε η Lf Lc : ℝ}
    (hδ : 0 < δ) (hε : 0 ≤ ε) (_hη : 0 ≤ η) (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hball : Metric.closedBall x δ ⊆ D)
    (hlf : ∀ u ∈ Metric.closedBall x δ, ∀ v ∈ Metric.closedBall x δ,
      ‖iteratedFDeriv ℝ j f u - iteratedFDeriv ℝ j f v‖ ≤ Lf * ‖u - v‖)
    (hlc : ∀ u ∈ Metric.closedBall x δ, ∀ v ∈ Metric.closedBall x δ,
      ‖iteratedFDeriv ℝ j c u - iteratedFDeriv ℝ j c v‖ ≤ Lc * ‖u - v‖)
    (hfeas : ‖c x‖ ≤ ε₀)
    (hcrit : TaylorModel.restrictedCriticality (Constrained.vectorLagrangian f c y) j V x δ ≤
      ε * Constrained.multiplierNorm y * δ ^ j / j.factorial + η) :
    ∀ d : EuclideanSpace ℝ (Fin n), d ∈ V → ‖c (x + d)‖ ≤ ε₀ →
      (‖d‖ ≤ δ ∧ (max Lf Lc = 0 ∨
        ‖d‖ ≤ (j + 1 : ℕ) * ε / (Real.sqrt 2 * max Lf Lc))) →
      (f x - 2 * ε₀ * ‖y‖ - 2 * ε * Constrained.multiplierNorm y * δ ^ j / j.factorial - η ≤
        f (x + d)) ∧
      ((c (x + d) = 0 ∧ inner ℝ y (c x) ≤ 0) ∨ c (x + d) = c x →
        f x - 2 * ε * Constrained.multiplierNorm y * δ ^ j / j.factorial - η ≤ f (x + d)) := by
  intro d hdV hcd hd
  have hL := Constrained.value_ge_of_lagrangian_criticality hj hD hf hc x y hδ.le
    hε hLf hLc hball hlf hlc hcrit hdV hd
  let b := 2 * ε * Constrained.multiplierNorm y * δ ^ j / (j.factorial : ℝ) + η
  have hb : Constrained.vectorLagrangian f c y x - b ≤
      Constrained.vectorLagrangian f c y (x + d) := by
    dsimp [b]
    linarith only [hL]
  constructor
  · have hh := Constrained.objective_bound_of_lagrangian_bound f c x d y hfeas hcd hb
    dsimp [b] at hh
    linarith only [hh]
  · intro he
    have hh := Constrained.objective_bound_of_lagrangian_bound_no_loss f c x d y hb he
    dsimp [b] at hh
    linarith only [hh]
end CartisGouldToint
