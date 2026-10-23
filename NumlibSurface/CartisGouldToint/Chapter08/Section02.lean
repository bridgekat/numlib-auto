import Numlib.Optimization.Quadratic.Secular.Vector
import Numlib.Optimization.Quadratic.Secular.FirstTaylor
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

namespace CartisGouldToint

/-- Corollary 8.2.4, with the necessary nonzero-gradient hypothesis. Positive
powers are strictly decreasing to zero and strictly convex; powers in `[−1/2,0)`
are strictly increasing to infinity and concave. Lower-endpoint values mean the
extended-real right-hand limits asserted here, including a singular pencil. -/
theorem corollary_8_2_4 {n : ℕ} [NeZero n]
    {H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (B : QuadraticSecular.PencilBasis (ι := Fin n) H M)
    {g : EuclideanSpace ℝ (Fin n)} (hg : g ≠ 0) (β : ℝ) :
    (β ≠ 0 → ∃ l : EReal,
      Tendsto (fun z => (transformedSecularFunction H M g β z : EReal))
        (𝓝[Set.Ioi B.edge] B.edge) (𝓝 l)) ∧
    (0 < β → StrictAntiOn (transformedSecularFunction H M g β) (Set.Ioi B.edge) ∧
      StrictConvexOn ℝ (Set.Ioi B.edge) (transformedSecularFunction H M g β) ∧
      Tendsto (transformedSecularFunction H M g β) atTop (𝓝 0)) ∧
    (-(1 / 2 : ℝ) ≤ β → β < 0 →
      StrictMonoOn (transformedSecularFunction H M g β) (Set.Ioi B.edge) ∧
      ConcaveOn ℝ (Set.Ioi B.edge) (transformedSecularFunction H M g β) ∧
      Tendsto (transformedSecularFunction H M g β) atTop atTop) :=
  ⟨fun hβ => B.transformed_right_limit hg hβ,
    fun hβ => ⟨B.strictAntiOn_transformed hg hβ, B.strictConvexOn_transformed hg hβ,
      B.transformed_tendsto_zero g hβ⟩,
    fun hβlow hβ => ⟨B.strictMonoOn_transformed hg hβ, B.concaveOn_transformed hg hβ hβlow,
      B.transformed_tendsto_atTop hg hβ⟩⟩

end CartisGouldToint

namespace CartisGouldToint

/-- The actual first-order Taylor approximation used in (8.2.20)–(8.2.21). -/
noncomputable abbrev transformedFirstTaylorPolynomial {n : ℕ}
    (H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (β z δ : ℝ) : ℝ :=
  QuadraticSecular.PencilBasis.firstTaylor H M g β z δ

/-- Theorem 8.2.5, with both necessary strictness corrections. Both displacement
signs are included. A zero displacement gives equality. At exponent `−1/2`,
strictness additionally requires two distinct active eigenvalues; an interior
negative exponent already suffices. Positive exponents include the constant
zero-gradient case, while negative powers require the positive-base domain. -/
theorem theorem_8_2_5 {n : ℕ} [NeZero n]
    {H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (B : QuadraticSecular.PencilBasis (ι := Fin n) H M)
    (g : EuclideanSpace ℝ (Fin n)) (β : ℝ)
    {z δ : ℝ} (hz : B.edge < z) (hzδ : B.edge < z + δ) :
    (0 < β → transformedFirstTaylorPolynomial H M g β z δ ≤
        transformedSecularFunction H M g β (z + δ) ∧
      (g ≠ 0 → δ ≠ 0 → transformedFirstTaylorPolynomial H M g β z δ <
        transformedSecularFunction H M g β (z + δ))) ∧
    (β < 0 → -(1 / 2 : ℝ) ≤ β → g ≠ 0 →
      transformedSecularFunction H M g β (z + δ) ≤
        transformedFirstTaylorPolynomial H M g β z δ ∧
      (δ ≠ 0 → (-(1 / 2 : ℝ) < β ∨
        ∃ i j, inner ℝ g (B.basis i) ≠ 0 ∧ inner ℝ g (B.basis j) ≠ 0 ∧
          B.eigenvalue i ≠ B.eigenvalue j) →
        transformedSecularFunction H M g β (z + δ) <
          transformedFirstTaylorPolynomial H M g β z δ)) :=
  ⟨fun hβ => B.firstTaylor_lower_pos_exponent g hβ hz hzδ,
    fun hβ hβlow hg => B.firstTaylor_upper_neg_exponent hg hβ hβlow hz hzδ⟩

end CartisGouldToint

namespace CartisGouldToint

/-- Theorem 8.2.6: the actual shifted-inverse solution has the differentiated
linear-system recurrence, while its squared metric norm has the exact odd/even
contractions and coefficient recurrence. All orders are genuine iterated derivatives.
Positive definiteness admits a zero shift whenever the original Hessian is positive definite. -/
theorem theorem_8_2_6 {n : ℕ}
    {H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (B : QuadraticSecular.PencilBasis (ι := Fin n) H M)
    (g : EuclideanSpace ℝ (Fin n)) {z : ℝ}
    (hpos : ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      0 < inner ℝ ((H + z • M) v) v) :
    iteratedDeriv 0 (QuadraticSecular.solution H M g) z = QuadraticSecular.solution H M g z ∧
      QuadraticSecular.derivativeCoefficient 0 = 1 ∧
      ∀ k : ℕ,
        (H + z • M) (iteratedDeriv (k + 1) (QuadraticSecular.solution H M g) z) =
          -(k + 1 : ℝ) • M (iteratedDeriv k (QuadraticSecular.solution H M g) z) ∧
        QuadraticSecular.derivativeCoefficient (k + 1) =
          2 * ((2 * k + 3 : ℝ) / (k + 1)) * QuadraticSecular.derivativeCoefficient k ∧
        iteratedDeriv (2 * k + 1) (secularFunction H M g) z =
          2 * QuadraticSecular.derivativeCoefficient k *
            inner ℝ (iteratedDeriv k (QuadraticSecular.solution H M g) z)
              (M (iteratedDeriv (k + 1) (QuadraticSecular.solution H M g) z)) ∧
        iteratedDeriv (2 * k + 2) (secularFunction H M g) z =
          QuadraticSecular.derivativeCoefficient (k + 1) *
            inner ℝ (iteratedDeriv (k + 1) (QuadraticSecular.solution H M g) z)
              (M (iteratedDeriv (k + 1) (QuadraticSecular.solution H M g) z)) := by
  have hz := fun i => ne_of_gt (B.denominator_pos_of_positive hpos i)
  refine ⟨rfl, QuadraticSecular.derivativeCoefficient_zero, fun k => ?_⟩
  exact ⟨B.shifted_iteratedDeriv_succ g k hz, QuadraticSecular.derivativeCoefficient_succ k,
    B.iteratedDeriv_secular_odd g k hz, B.iteratedDeriv_secular_even g k hz⟩

end CartisGouldToint
