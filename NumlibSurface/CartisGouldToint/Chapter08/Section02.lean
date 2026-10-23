import Numlib.Optimization.Quadratic.Secular.Transform
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

namespace CartisGouldToint

/-- The actual Taylor approximation (8.2.12) of the shifted-inverse secular
function, evaluated at displacement `δ`. Coefficients are its actual derivatives. -/
noncomputable abbrev secularTaylorPolynomial {n : ℕ}
    (H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (z δ : ℝ) : ℝ :=
  QuadraticSecular.PencilBasis.actualTaylor H M g k z δ

/-- Theorem 8.2.2, both displacement signs and all strictness clauses.
For positive displacements, even Taylor orders give upper bounds and odd orders
lower bounds. For negative displacements within the spectral domain, successive
Taylor orders give increasing lower bounds. Every inequality is strict when
`g≠0`. The result also holds at order zero. -/
theorem theorem_8_2_2 {n : ℕ} [NeZero n]
    {H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (B : QuadraticSecular.PencilBasis (ι := Fin n) H M)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    {z δ : ℝ} (hz : B.edge < z) :
    (0 < δ →
      (Even k → secularFunction H M g (z + δ) ≤ secularTaylorPolynomial H M g k z δ ∧
        (g ≠ 0 → secularFunction H M g (z + δ) < secularTaylorPolynomial H M g k z δ)) ∧
      (Odd k → secularTaylorPolynomial H M g k z δ ≤ secularFunction H M g (z + δ) ∧
        (g ≠ 0 → secularTaylorPolynomial H M g k z δ < secularFunction H M g (z + δ)))) ∧
    (B.edge - z < δ → δ < 0 →
      secularTaylorPolynomial H M g k z δ ≤ secularTaylorPolynomial H M g (k + 1) z δ ∧
      secularTaylorPolynomial H M g (k + 1) z δ ≤ secularFunction H M g (z + δ) ∧
      (g ≠ 0 →
        secularTaylorPolynomial H M g k z δ < secularTaylorPolynomial H M g (k + 1) z δ ∧
        secularTaylorPolynomial H M g (k + 1) z δ < secularFunction H M g (z + δ))) :=
  B.actualTaylor_bounds g k hz

end CartisGouldToint

namespace CartisGouldToint

/-- The actual transformed secular function (8.2.17), `π(z)^β`. Negative
exponents are used on its positive-base domain, supplied by a nonzero gradient. -/
noncomputable abbrev transformedSecularFunction {n : ℕ}
    (H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (β z : ℝ) : ℝ :=
  QuadraticSecular.PencilBasis.transformed H M g β z

/-- Lemma 8.2.3, with the strictness correction at `β=−1/2`. Both derivative
signs are strict for positive exponents and nonzero gradient. For negative
exponents the first derivative is positive, and the second is nonpositive on
`[−1/2,0)`. It is strictly negative on `(−1/2,0)` and also at the endpoint when
two distinct generalized eigenvalues are active. With one active eigenvalue,
the endpoint transform can be affine, so its weak inequality is essential. -/
theorem lemma_8_2_3 {n : ℕ} [NeZero n]
    {H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (B : QuadraticSecular.PencilBasis (ι := Fin n) H M)
    (g : EuclideanSpace ℝ (Fin n)) (β : ℝ)
    {z : ℝ} (hz : B.edge < z) :
    (0 < β → deriv (transformedSecularFunction H M g β) z ≤ 0 ∧
      0 ≤ iteratedDeriv 2 (transformedSecularFunction H M g β) z ∧
      (g ≠ 0 → deriv (transformedSecularFunction H M g β) z < 0 ∧
        0 < iteratedDeriv 2 (transformedSecularFunction H M g β) z)) ∧
    (β < 0 → g ≠ 0 → 0 < deriv (transformedSecularFunction H M g β) z ∧
      (-(1 / 2 : ℝ) ≤ β → iteratedDeriv 2 (transformedSecularFunction H M g β) z ≤ 0 ∧
        (-(1 / 2 : ℝ) < β → iteratedDeriv 2 (transformedSecularFunction H M g β) z < 0) ∧
        ((∃ i j, inner ℝ g (B.basis i) ≠ 0 ∧ inner ℝ g (B.basis j) ≠ 0 ∧
          B.eigenvalue i ≠ B.eigenvalue j) →
          iteratedDeriv 2 (transformedSecularFunction H M g β) z < 0))) :=
  B.transformed_derivative_signs g β hz

end CartisGouldToint
