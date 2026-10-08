import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation
import Numlib.Analysis.Sobolev.Triangulation
import Numlib.Approximation.NodalInterpolation
import Numlib.FiniteElement.Interpolation

/-!
# Atkinson–Han §10.2: affine-equivalent finite elements

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §10.2.

The section builds the finite element machinery on a polygon: triangulations, the local spaces
`ℙ_k` on a triangle, barycentric coordinates, and the affine map (10.2.25)
`F_K(x̂) = T_K x̂ + b_K` carrying the reference element `K̂` onto an element `K`. The triangulation
axioms (1)–(4) are the backbone's `Triangulation` (`Numlib/Geometry/Triangulation.lean`), and the
linear element space on a triangulation, Example 10.2.3, is `example_10_2_3` at the end of this
file. The model boundary value problem in `H¹(Ω)` is out of scope — not for want of the space,
which is `Chapter07.definition_7_2_2_multiIndex`, but for the trace on the boundary of §7.3 that
its Neumann data need; **the rest of the section is not**, and it is what this file holds.

Lemma 10.2.2's proof uses only two facts about the sets involved: a ball of diameter `ρ̂` sits
inside `K̂`, and `K` has diameter `h_K`. No triangle, no polynomial space and no Sobolev norm. The
nodal representation formulas (10.2.23), Exercise 10.2.1 and Exercise 10.2.3 are finite algebraic
identities on the reference element.

The book's matrix norm is the spectral norm, the operator norm induced by the Euclidean vector
norm, so `T_K` is read as a continuous linear equivalence of `EuclideanSpace ℝ (Fin d)` and
`‖T_K‖`, `‖T_K⁻¹‖` are the operator norms of `T_K` and of its inverse.

The quantities `ρ̂` and `ρ_K` — the diameters of the largest inscribed balls — enter the statement
only through the containment of *one* inscribed ball, so the hypothesis is
`Metric.closedBall ĉ (ρ̂ / 2) ⊆ K̂` rather than a definition of the inradius, which Mathlib does not
have. The bound for the largest inscribed ball follows by taking `ρ̂` as large as the containment
allows.

## Main definitions

* `refBary` — the barycentric coordinates `λ̂₁, λ̂₂, λ̂₃` of the reference triangle.
* `quadraticNode` and `quadraticShape` — the six nodes of (10.2.23), three vertices and three side
  mid-points, and the six shape functions `λ̂ᵢ(2λ̂ᵢ − 1)` and `4λ̂ᵢλ̂ⱼ` dual to them.
* `cubicNode` and `cubicShape` — the ten points of the principal lattice `N̂₃` and the ten shape
  functions of Exercise 10.2.1.
* `bilinearNode` and `bilinearShape` — the four vertices of the reference square and the four
  products `(1 ∓ x̂₁)(1 ∓ x̂₂)` of Exercise 10.2.3.

## Main results

* `lemma_10_2_2` — the bounds `‖T_K‖ ≤ h_K / ρ̂` and `‖T_K⁻¹‖ ≤ ĥ / ρ_K` for the affine map of an
  affine-equivalent family: the backbone's `FiniteElement.opNorm_le_diam_div_of_image`.
* `quadraticShape_isNodalBasis`, `cubicShape_isNodalBasis`, `bilinearShape_isNodalBasis` — each
  family of shape functions is dual to its nodes. For the quadratic element this is exactly the pair
  of observations (1) and (2) from which the book derives (10.2.23).
* `equation_10_2_23`, `exercise_10_2_1`, `exercise_10_2_3` — the nodal representations themselves:
  interpolation at those nodes with those shape functions reproduces every polynomial of the space.
* `proposition_10_2_1` — unisolvence of `ℙ_k` on the principal lattice `N̂_k`, for every `k ≥ 1`:
  the backbone's `LagrangeElement.bijective_latticeEval`.
* `example_10_2_3` — the linear element space on a triangulation: the representation (10.2.28)
  in barycentric coordinates, the conformity across the edges, and the global continuity and
  `H¹`-membership of the glued piecewise linear function.

The `ℙ_k` Lagrange element on the principal lattice, on `EuclideanSpace ℝ (Fin 2)` — nodal,
reproducing `ℙ_k`, and conforming on every triangulation (the book's remark after Example 10.2.3,
and Exercise 10.2.4 at `k = 2`) — is the backbone's `LagrangeElement.node`,
`LagrangeElement.shape`, `LagrangeElement.isConformingElement`
(`Numlib/FiniteElement/LagrangeElement.lean`).

## Deviations from the book

The nodal representations are stated on `ℝ × ℝ`, the book's `ℝ²`, rather than on
`EuclideanSpace ℝ (Fin 2)`: they are affine-algebraic identities in which no norm, inner product or
measure appears, and the product type is what `ring` reads. The reference triangle is the one with
vertices `(0,0)`, `(1,0)`, `(0,1)`, so that `λ̂₁ = 1 − x̂₁ − x̂₂`, `λ̂₂ = x̂₁` and `λ̂₃ = x̂₂`; the
reference square is `[0,1]²`, as in §10.3.

The book quantifies (10.2.23) over `v̂ ∈ X̂₂`, the space of `ℙ₂(K̂)` functions "determined by" their
values at the six nodes. `ℙ₂(K̂)` *is* the set of `c₀ + c₁x + c₂y + c₃x² + c₄xy + c₅y²`, so the
statement is a universally quantified identity in the six coefficients; likewise for the cubic and
the bilinear case. Stating it so is what makes it independent of Proposition 10.2.1: the
representation is proved rather than deduced from unisolvence, and unisolvence over the space then
follows from it.

## Not formalized here

The model Neumann problem (10.2.4)–(10.2.12), whose boundary term needs the trace on `Γ`;
Exercise 10.2.5, the `H(div)`-conformity of a piecewise `H¹` vector field (Exercise 10.2.4, the
`H¹`-conformity of the quadratic element, is the case `k = 2` of the backbone's
`LagrangeElement.isConformingElement`).
The `H¹`-conformity of a continuous piecewise-`C¹` function, on which Example 10.2.3 rests, is
the backbone's `Triangulation.memSobolev_of_piecewise`
(`Numlib/Analysis/Sobolev/Triangulation.lean`).
Proposition 10.2.1, the unisolvence of `ℙ_k` on the principal lattice for *every* `k`, is proved in
the backbone (`LagrangeElement.bijective_latticeEval`). It was planned as the hard item of the
chapter, on the ground that the classical induction needs the divisibility of a polynomial vanishing
on a line by the affine form of that line; the proof there uses no divisibility and no induction,
only the explicit nodal basis and a dimension count. Its cases `k = 2` and `k = 3` are
`equation_10_2_23` and `exercise_10_2_1`, proved independently of it.
-/

namespace AtkinsonHan.Chapter10

variable {d : ℕ}

/-- **Lemma 10.2.2.**  Let `F_K x̂ = T_K x̂ + b_K` be the affine bijection (10.2.25) of the
reference element `K̂` onto the element `K`, let a ball of diameter `ρ̂` lie in `K̂` and a ball of
diameter `ρ_K` in `K`, and write `h_K = diam K`, `ĥ = diam K̂`. Then

  `‖T_K‖ ≤ h_K / ρ̂`  and  `‖T_K⁻¹‖ ≤ ĥ / ρ_K`.

The two halves are the same statement with the roles of `K̂` and `K` exchanged, the second applied
to the inverse map `y ↦ T_K⁻¹ y - T_K⁻¹ b_K`, which is the affine map carrying `K` onto `K̂`.

Both elements are assumed bounded, as the book's elements — closed triangles — are: `Metric.diam`
of an unbounded set is `0`, and the bounds would then be false rather than vacuous. -/
theorem lemma_10_2_2 {Kref K : Set (EuclideanSpace ℝ (Fin d))}
    {T : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d)}
    {b cref c : EuclideanSpace ℝ (Fin d)} {ρref ρK : ℝ} (hρref : 0 < ρref) (hρK : 0 < ρK)
    (hKrefb : Bornology.IsBounded Kref) (hKb : Bornology.IsBounded K)
    (hballref : Metric.closedBall cref (ρref / 2) ⊆ Kref)
    (hballK : Metric.closedBall c (ρK / 2) ⊆ K)
    (hF : (fun x => T x + b) '' Kref = K) :
    ‖(T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖ ≤ Metric.diam K / ρref ∧
      ‖(T.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖
        ≤ Metric.diam Kref / ρK :=
  FiniteElement.opNorm_le_diam_div_of_image hρref hρK hKrefb hKb hballref hballK hF

/-! ### Nodal representations on the reference element -/

/-- **The barycentric coordinates of the reference triangle** with vertices `â₁ = (0,0)`,
`â₂ = (1,0)` and `â₃ = (0,1)`: `λ̂₁ = 1 − x̂₁ − x̂₂`, `λ̂₂ = x̂₁`, `λ̂₃ = x̂₂`. They sum to `1`, are
affine, and `λ̂ᵢ(âⱼ) = δᵢⱼ`, which is what makes them the shape functions of the linear element
(`AtkinsonHan.Chapter10.example_10_3_2` states the last property for a general simplex, through
`AffineBasis.coord`). -/
noncomputable def refBary : Fin 3 → ℝ × ℝ → ℝ :=
  ![fun p => 1 - p.1 - p.2, fun p => p.1, fun p => p.2]

/-- **The six nodes of the quadratic element**: the three vertices `âᵢ` of the reference triangle
followed by the three side mid-points `âᵢⱼ = (âᵢ + âⱼ)/2`, in the order `â₁₂`, `â₁₃`, `â₂₃`. -/
noncomputable def quadraticNode : Fin 6 → ℝ × ℝ :=
  ![(0, 0), (1, 0), (0, 1), (1 / 2, 0), (0, 1 / 2), (1 / 2, 1 / 2)]

/-- **The six shape functions of (10.2.23)**: `λ̂ᵢ(2λ̂ᵢ − 1)` at the vertices and `4λ̂ᵢλ̂ⱼ` at the
side mid-points, in the order of `quadraticNode`. -/
noncomputable def quadraticShape : Fin 6 → ℝ × ℝ → ℝ :=
  ![fun p => refBary 0 p * (2 * refBary 0 p - 1),
    fun p => refBary 1 p * (2 * refBary 1 p - 1),
    fun p => refBary 2 p * (2 * refBary 2 p - 1),
    fun p => 4 * refBary 0 p * refBary 1 p,
    fun p => 4 * refBary 0 p * refBary 2 p,
    fun p => 4 * refBary 1 p * refBary 2 p]

/-- **The two observations the book derives (10.2.23) from**: `λ̂ᵢ(2λ̂ᵢ − 1)` takes the value `1` at
`âᵢ` and `0` at the other vertices and at every side mid-point, and `4λ̂ᵢλ̂ⱼ` takes the value `1` at
`âᵢⱼ` and `0` at every other node. Together they say that the six shape functions are dual to the
six nodes. -/
theorem quadraticShape_isNodalBasis : Approximation.IsNodalBasis quadraticNode quadraticShape where
  eval_self i := by
    fin_cases i <;> simp [quadraticNode, quadraticShape, refBary] <;> norm_num
  eval_of_ne i j hij := by
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | (simp [quadraticNode, quadraticShape, refBary] <;> norm_num)

/-- **(10.2.23)**, the nodal representation of a quadratic on the reference triangle:

  `v̂ = Σᵢ v̂(âᵢ) λ̂ᵢ (2λ̂ᵢ − 1) + Σ_{i<j} 4 v̂(âᵢⱼ) λ̂ᵢ λ̂ⱼ`.

A quadratic is a `v̂(x̂) = c₀ + c₁x̂₁ + c₂x̂₂ + c₃x̂₁² + c₄x̂₁x̂₂ + c₅x̂₂²`, so the claim is an
identity between polynomials in `x̂` with the six coefficients free — the `k = 2` case of
Proposition 10.2.1, proved without it. -/
theorem equation_10_2_23 (c₀ c₁ c₂ c₃ c₄ c₅ : ℝ) :
    Approximation.nodalInterp quadraticNode quadraticShape
        (fun p : ℝ × ℝ => c₀ + c₁ * p.1 + c₂ * p.2 + c₃ * p.1 ^ 2 + c₄ * p.1 * p.2 + c₅ * p.2 ^ 2)
      = fun p : ℝ × ℝ =>
        c₀ + c₁ * p.1 + c₂ * p.2 + c₃ * p.1 ^ 2 + c₄ * p.1 * p.2 + c₅ * p.2 ^ 2 := by
  funext p
  simp [Approximation.nodalInterp_apply, Fin.sum_univ_succ, quadraticNode, quadraticShape, refBary]
  ring

/-- **The ten points of the principal lattice `N̂₃`** (10.2.24) for `k = 3`: the three vertices, the
six points dividing the sides in thirds — the point with barycentric coordinates `2/3` at `âᵢ` and
`1/3` at `âⱼ`, for the ordered pairs `(1,2), (2,1), (1,3), (3,1), (2,3), (3,2)` — and the
centroid. -/
noncomputable def cubicNode : Fin 10 → ℝ × ℝ :=
  ![(0, 0), (1, 0), (0, 1), (1 / 3, 0), (2 / 3, 0), (0, 1 / 3), (0, 2 / 3), (2 / 3, 1 / 3),
    (1 / 3, 2 / 3), (1 / 3, 1 / 3)]

/-- **The ten cubic shape functions** dual to `cubicNode`: `λ̂ᵢ(3λ̂ᵢ − 1)(3λ̂ᵢ − 2)/2` at the
vertices, `9 λ̂ᵢ λ̂ⱼ (3λ̂ᵢ − 1)/2` at the side points, and `27 λ̂₁λ̂₂λ̂₃` at the centroid. -/
noncomputable def cubicShape : Fin 10 → ℝ × ℝ → ℝ :=
  ![fun p => refBary 0 p * (3 * refBary 0 p - 1) * (3 * refBary 0 p - 2) / 2,
    fun p => refBary 1 p * (3 * refBary 1 p - 1) * (3 * refBary 1 p - 2) / 2,
    fun p => refBary 2 p * (3 * refBary 2 p - 1) * (3 * refBary 2 p - 2) / 2,
    fun p => 9 * refBary 0 p * refBary 1 p * (3 * refBary 0 p - 1) / 2,
    fun p => 9 * refBary 0 p * refBary 1 p * (3 * refBary 1 p - 1) / 2,
    fun p => 9 * refBary 0 p * refBary 2 p * (3 * refBary 0 p - 1) / 2,
    fun p => 9 * refBary 0 p * refBary 2 p * (3 * refBary 2 p - 1) / 2,
    fun p => 9 * refBary 1 p * refBary 2 p * (3 * refBary 1 p - 1) / 2,
    fun p => 9 * refBary 1 p * refBary 2 p * (3 * refBary 2 p - 1) / 2,
    fun p => 27 * refBary 0 p * refBary 1 p * refBary 2 p]

set_option maxHeartbeats 1000000 in
-- the duality is a hundred numeric evaluations, one for each ordered pair of the ten nodes
/-- The ten cubic shape functions are dual to the ten points of `N̂₃`. -/
theorem cubicShape_isNodalBasis : Approximation.IsNodalBasis cubicNode cubicShape where
  eval_self i := by
    fin_cases i <;> simp [cubicNode, cubicShape, refBary] <;> norm_num
  eval_of_ne i j hij := by
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | (simp [cubicNode, cubicShape, refBary] <;> norm_num)

set_option maxHeartbeats 1000000 in
-- `ring` on a cubic identity in two variables with ten free coefficients
/-- **Exercise 10.2.1.**  A cubic on the reference triangle is represented by its values at the ten
points of the principal lattice `N̂₃`, through the shape functions `cubicShape`. It is (10.2.23) one
degree higher, and the `k = 3` case of Proposition 10.2.1. -/
theorem exercise_10_2_1 (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℝ) :
    Approximation.nodalInterp cubicNode cubicShape
        (fun p : ℝ × ℝ => c₀ + c₁ * p.1 + c₂ * p.2 + c₃ * p.1 ^ 2 + c₄ * p.1 * p.2 + c₅ * p.2 ^ 2
          + c₆ * p.1 ^ 3 + c₇ * p.1 ^ 2 * p.2 + c₈ * p.1 * p.2 ^ 2 + c₉ * p.2 ^ 3)
      = fun p : ℝ × ℝ => c₀ + c₁ * p.1 + c₂ * p.2 + c₃ * p.1 ^ 2 + c₄ * p.1 * p.2 + c₅ * p.2 ^ 2
          + c₆ * p.1 ^ 3 + c₇ * p.1 ^ 2 * p.2 + c₈ * p.1 * p.2 ^ 2 + c₉ * p.2 ^ 3 := by
  funext p
  simp [Approximation.nodalInterp_apply, Fin.sum_univ_succ, cubicNode, cubicShape, refBary]
  ring

/-- **The four vertices of the reference square** `[0,1]²`. -/
noncomputable def bilinearNode : Fin 4 → ℝ × ℝ := ![(0, 0), (1, 0), (0, 1), (1, 1)]

/-- **The bilinear nodal basis of `ℚ_{1,1}`** on the reference square: the four products
`(1 − x̂₁)(1 − x̂₂)`, `x̂₁(1 − x̂₂)`, `(1 − x̂₁)x̂₂`, `x̂₁x̂₂`, in the order of `bilinearNode`. -/
noncomputable def bilinearShape : Fin 4 → ℝ × ℝ → ℝ :=
  ![fun p => (1 - p.1) * (1 - p.2), fun p => p.1 * (1 - p.2), fun p => (1 - p.1) * p.2,
    fun p => p.1 * p.2]

/-- The four bilinear shape functions are dual to the four vertices of the reference square. -/
theorem bilinearShape_isNodalBasis : Approximation.IsNodalBasis bilinearNode bilinearShape where
  eval_self i := by fin_cases i <;> simp [bilinearNode, bilinearShape]
  eval_of_ne i j hij := by
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | simp [bilinearNode, bilinearShape]

/-- **Exercise 10.2.3.**  The nodes and parameters of `ℚ_{1,1}(K̂)` on the reference square are its
four vertices and the values there, and a bilinear function is represented by

  `v̂ = Σ v̂(âᵢ) φ̂ᵢ`

with the `φ̂ᵢ` of `bilinearShape`. The quadrilateral counterpart of (10.2.23); the book keeps it
apart from the triangular case because the reference map of a general quadrilateral is bilinear
rather than affine. -/
theorem exercise_10_2_3 (a₀ a₁ a₂ a₃ : ℝ) :
    Approximation.nodalInterp bilinearNode bilinearShape
        (fun p : ℝ × ℝ => a₀ + a₁ * p.1 + a₂ * p.2 + a₃ * p.1 * p.2)
      = fun p : ℝ × ℝ => a₀ + a₁ * p.1 + a₂ * p.2 + a₃ * p.1 * p.2 := by
  funext p
  simp [Approximation.nodalInterp_apply, Fin.sum_univ_succ, bilinearNode, bilinearShape]
  ring

/-! ### Proposition 10.2.1: unisolvence of `ℙ_k` on the principal lattice -/

/-- **Proposition 10.2.1**: a polynomial of total degree at most `k` on a triangle is uniquely
determined by its values at the `(k+1)(k+2)/2` points of the principal lattice `N̂_k` — that is,
the interpolation map `p ↦ (p(x̂))_{x̂ ∈ N̂_k}` on `ℙ_k` (`LagrangeElement.latticeEval`) is
bijective. The book quotes the proposition without proof; the backbone's
`LagrangeElement.bijective_latticeEval` proves it through Silvester's explicit nodal basis and a
dimension count. -/
theorem proposition_10_2_1 {k : ℕ} (hk : 0 < k) :
    Function.Bijective (LagrangeElement.latticeEval k) :=
  LagrangeElement.bijective_latticeEval hk

/-! ### Example 10.2.3: the linear element space on a triangulation

The triangulation is `Triangulation Ω` (`Numlib/Geometry/Triangulation.lean`, the book's
properties 1–4 of §10.2), the local space `X_K = ℙ₁(K)` is spanned by the barycentric coordinates
`λᵢ = λ̂ᵢ ∘ F_K⁻¹` of the element, and the local finite element function determined by the values
at the three vertices is `Triangulation.localInterp` at the vertices of the reference triangle with
the shape functions `EuclideanSpace.baryCoord` (the `λ̂ᵢ` of `refBary`, on
`EuclideanSpace ℝ (Fin 2)`). -/

section Example1023

open MeasureTheory TopologicalSpace EuclideanSpace

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- **Example 10.2.3** (the linear element space). Let `𝒯_h` be a triangulation of a plane
domain `Ω` and let the local function on each element `K` be the `ℙ₁(K)` function determined by
the values of `v` at the three vertices `aⱼ`. Then

* (10.2.28): on `K` it is `∑ᵢ v(aᵢ) λᵢ` with `λᵢ = λ̂ᵢ ∘ F_K⁻¹` the barycentric coordinates of
  `K`;
* the element is conforming — the local functions of two elements agree at every point of
  their common closed elements (the condition (10.2.6)): at a common vertex both take the value
  of `v` there, and along a common edge the difference is a linear function of one variable
  vanishing at the two end points;
* so the piecewise linear function `v_h` glued from them (`Triangulation.globalInterp`) is
  globally continuous, `v_h ∈ C(Ω̄)`, and lies in `H¹(Ω)` (§10.2.3: `X_h ⊆ H¹(Ω)` because
  `X_h ⊆ C(Ω̄)`).

The local space `X_K` "consists of `ℙ₁(K)` functions determined by their values at the three
vertices": `nodalInterp_coord_affineMap` (§10.3) says that the interpolant reproduces every
affine function, and `LagrangeElement.latticeShape` at `k = 1` are the shape functions of the
reference element. The book adds that `ℙ_k` on the nodal set `N_k(K)` of (10.2.29) is conforming
as well: that is the backbone's `LagrangeElement.isConformingElement`. -/
theorem example_10_2_3 {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (v : 𝔼₂ → ℝ) :
    (∀ (T : 𝒯.elems) (x : 𝔼₂), 𝒯.localInterp referenceTriangleVertex baryCoord T v x
      = ∑ i, v (T.1 i) * baryCoord i ((𝒯.linearPart T).symm (x - T.1 0))) ∧
    𝒯.IsConformingElement referenceTriangleVertex baryCoord ∧
    ContinuousOn (𝒯.globalInterp referenceTriangleVertex baryCoord v) (closure (Ω : Set 𝔼₂)) ∧
    MemSobolev (𝒯.globalInterp referenceTriangleVertex baryCoord v) 1 2 Ω volume := by
  refine ⟨fun T x ↦ ?_, 𝒯.isConformingElement_linear, ?_, ?_⟩
  · rw [Triangulation.localInterp_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [𝒯.affine_referenceTriangleVertex T i, mul_comm]
  · exact 𝒯.continuousOn_globalInterp _ _ 𝒯.isConformingElement_linear
      (fun i ↦ (contDiff_baryCoord i).continuous) v
  · exact 𝒯.memSobolev_globalInterp _ _ 𝒯.isConformingElement_linear
      (fun i ↦ (contDiff_baryCoord i).of_le (by simp)) v 2

end Example1023

end AtkinsonHan.Chapter10
