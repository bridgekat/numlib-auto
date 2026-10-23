import Numlib.Optimization.Quadratic.Secular
import NumlibSurface.CartisGouldToint.Chapter08.Section01

/-!
# The actual secular function and its interior root

The generalized eigenbasis contains actual vectors and operator eigenrelations;
the spectral expression is proved from the actual shifted linear system.
The source endpoint inequality means a strictly positive right-hand limit of
`π−τ`, including an infinite limit. No inverse is evaluated at a singular edge.
-/

open Filter
open scoped Topology
namespace CartisGouldToint

/-- The actual weighted squared shifted-inverse norm (8.2.4). -/
noncomputable abbrev secularFunction {n : ℕ}
    (H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (z : ℝ) : ℝ :=
  QuadraticSecular.secular H M g z

/-- Lemma 8.2.1. The continuous nonzero nonnegative nondecreasing comparison
function has exactly one root above the left spectral endpoint. The endpoint
inequality uses a positive finite or infinite right limit, including singular
pencils. Existence and uniqueness are derived from the actual shifted inverse. -/
theorem lemma_8_2_1 {n : ℕ} [NeZero n]
    {H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (B : QuadraticSecular.PencilBasis (ι := Fin n) H M)
    (g : EuclideanSpace ℝ (Fin n)) (τ : ℝ → ℝ)
    (hτc : ContinuousOn τ (Set.Ioi B.edge))
    (hτm : MonotoneOn τ (Set.Ioi B.edge))
    (hτn : ∀ z ∈ Set.Ioi B.edge, 0 ≤ τ z)
    (hτp : ∃ z ∈ Set.Ioi B.edge, 0 < τ z)
    (hleft : Tendsto (fun z => secularFunction H M g z - τ z)
        (𝓝[Set.Ioi B.edge] B.edge) atTop ∨
      ∃ l : ℝ, 0 < l ∧ Tendsto (fun z => secularFunction H M g z - τ z)
        (𝓝[Set.Ioi B.edge] B.edge) (𝓝 l)) :
    ∃! z, z ∈ Set.Ioi B.edge ∧ secularFunction H M g z = τ z :=
  B.existsUnique_secular_root g τ hτc hτm hτn hτp hleft

end CartisGouldToint
