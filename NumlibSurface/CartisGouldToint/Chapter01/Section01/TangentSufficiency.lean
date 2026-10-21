import Numlib.Optimization.ConstrainedSecondOrder
import NumlibSurface.CartisGouldToint.Chapter01.Section01

/-!
# Tangent-cone correction to the convex-set sufficient condition

The converse in the supplied transcription of Theorem 1.1.2 uses radial feasible
displacements. Its valid correction tests the positive tangent critical cone, which also
contains limits of normalized feasible displacements. The sufficient condition below holds
for arbitrary feasible sets, so in particular for the closed convex sets in the theorem.
The original radial converse remains separately marked wrong in its plan.
-/

namespace CartisGouldToint.Chapter01.Section01

/-- Corrected strict sufficiency for Theorem 1.1.2: the Hessian must be positive on every
nonzero direction in the positive tangent critical cone. The feasible set may be arbitrary;
closedness and convexity are unnecessary for this sufficient condition. -/
theorem theorem_1_1_2_corrected {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {C U : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    (hU : IsOpen U) (hxU : x ∈ U) (_hx : x ∈ C) (hf : ContDiffOn ℝ 2 f U)
    (hfirst : ∀ y ∈ C, 0 ≤ fderiv ℝ f x (y - x))
    (hpos : ∀ d ∈ Constrained.tangentCriticalCone C x (fderiv ℝ f x), d ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ f) x d d) :
    ∃ δ > 0, ∀ y ∈ C, dist y x < δ → y ≠ x → f x < f y :=
  Constrained.isStrictLocalMinOn_of_contDiffOn_posDef_tangentCriticalCone
    hU hxU hf hfirst hpos

end CartisGouldToint.Chapter01.Section01
