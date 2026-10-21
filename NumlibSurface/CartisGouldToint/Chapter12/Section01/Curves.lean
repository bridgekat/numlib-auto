import NumlibSurface.CartisGouldToint.Chapter12.Section01
import Numlib.Analysis.Calculus.CurveTaylorExpansion

/-!
# Curve-based necessary optimality conditions

A function that is locally `C^q` at a local unconstrained minimum satisfies every curve
coefficient sign test through order `q`, using the actual positive-composition coefficients.
-/

noncomputable section
namespace CartisGouldToint.Chapter12.Section01
variable {n : ℕ}

/-- Theorem 12.1.1: if `f` is `C^q` near a local unconstrained minimum, then for every
`1 ≤ j ≤ q` and every jet with nonzero active directions, the actual composition coefficient
(12.1.6) is nonnegative whenever all preceding coefficients (12.1.7) vanish. -/
theorem theorem_12_1_1 {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {q : ℕ}
    (hf : ContDiffAt ℝ q f x) (hmin : IsLocalMin f x) : IsCurveOrderMinimizer f x q :=
  isCurveOrderMinimizer_of_canonical (CurveTaylor.isOrderMinimizer_of_isLocalMin hf hmin)

end CartisGouldToint.Chapter12.Section01
