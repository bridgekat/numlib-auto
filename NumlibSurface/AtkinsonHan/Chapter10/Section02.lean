import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation
import Numlib.Analysis.Normed.Operator.Scaling
import Numlib.Approximation.MvPolynomial
import Numlib.Approximation.NodalInterpolation

/-!
# Atkinson–Han §10.2: affine-equivalent finite elements

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §10.2.

The section builds the finite element machinery on a polygon: triangulations, the local spaces
`ℙ_k` on a triangle, barycentric coordinates, and the affine map (10.2.25)
`F_K(x̂) = T_K x̂ + b_K` carrying the reference element `K̂` onto an element `K`. The model boundary
value problem in `H¹(Ω)` is out of scope — not for want of the space, which is
`Chapter07.definition_7_2_2_multiIndex`, but for the trace and the Poincaré inequality of §7.3 —
and with it the finite element space and the triangulation axioms; **the rest of the section is
not**, and it is what this file holds.

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
* `latticePoint`, `latticeShape` and `latticeEval` — the principal lattice `N̂_k` for a general `k`,
  Silvester's nodal shape functions on it, and the interpolation map of Proposition 10.2.1.

## Main results

* `lemma_10_2_2` — the bounds `‖T_K‖ ≤ h_K / ρ̂` and `‖T_K⁻¹‖ ≤ ĥ / ρ_K` for the affine map of an
  affine-equivalent family. It specializes the backbone's
  `ContinuousLinearMap.opNorm_le_diam_div`.
* `quadraticShape_isNodalBasis`, `cubicShape_isNodalBasis`, `bilinearShape_isNodalBasis` — each
  family of shape functions is dual to its nodes. For the quadratic element this is exactly the pair
  of observations (1) and (2) from which the book derives (10.2.23).
* `equation_10_2_23`, `exercise_10_2_1`, `exercise_10_2_3` — the nodal representations themselves:
  interpolation at those nodes with those shape functions reproduces every polynomial of the space.
* `proposition_10_2_1` — unisolvence of `ℙ_k` on the principal lattice `N̂_k`, for every `k ≥ 1`,
  with `eq_zero_of_eval_latticePoint` for the uniqueness half alone.

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

The triangulation axioms (1)–(4) and the model Neumann problem (10.2.4)–(10.2.12), whose space is
`H¹(Ω)` on a polygon; Example 10.2.3 and Exercises 10.2.4, 10.2.5, which characterize `H¹`- and
`H(div)`-conformity of a piecewise polynomial space and need the weak derivative of a
piecewise-smooth function.
Proposition 10.2.1, the unisolvence of `ℙ_k` on the principal lattice for *every* `k`, is proved
below. It was planned as the hard item of the chapter, on the ground that the classical induction
needs the divisibility of a polynomial vanishing on a line by the affine form of that line; the
proof here uses no divisibility and no induction, only the explicit nodal basis and a dimension
count. Its cases `k = 2` and `k = 3` are `equation_10_2_23` and `exercise_10_2_1`, proved
independently of it.
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
        ≤ Metric.diam Kref / ρK := by
  constructor
  · have h := ContinuousLinearMap.opNorm_le_diam_div
      (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (b := b) (S := Kref) (D := K)
      (by positivity) hKb hballref (fun x hx => hF ▸ Set.mem_image_of_mem _ hx)
    rwa [show 2 * (ρref / 2) = ρref by ring] at h
  · -- the inverse of `x ↦ T x + b` is `y ↦ T⁻¹ y - T⁻¹ b`, and it carries `K` onto `K̂`
    have hmaps : ∀ y ∈ K, (T.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) y
        + (-T.symm b) ∈ Kref := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ : ∃ x ∈ Kref, T x + b = y := by
        rw [← hF] at hy
        obtain ⟨x, hx, hxy⟩ := hy
        exact ⟨x, hx, hxy⟩
      have : (T.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (T x + b)
          + (-T.symm b) = x := by
        simp [ContinuousLinearEquiv.coe_coe, map_add]
      rw [this]
      exact hx
    have h := ContinuousLinearMap.opNorm_le_diam_div
      (T.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (b := -T.symm b)
      (S := K) (D := Kref) (by positivity) hKrefb hballK hmaps
    rwa [show 2 * (ρK / 2) = ρK by ring] at h

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

/-! ### Proposition 10.2.1: unisolvence of `ℙ_k` on the principal lattice

The statement is about `ℙ_k` on the plane, so this section works with
`MvPolynomial (Fin 2) ℝ` and the subspace `MvPolynomial.restrictTotalDegree (Fin 2) ℝ k`, rather
than with the `ℝ × ℝ` functions of the low-degree cases above: what is at stake here is the
*degree* of a polynomial, and that is a property of the polynomial and not of the function.

The proof exhibits the nodal basis explicitly. For a lattice point with barycentric multi-index
`α = (α₁, α₂, α₃)`, `Σ αᵢ = k`, the shape function is Silvester's product

  `L_α = ∏_c ∏_{r < α_c} (k λ_c − r) / (α_c − r)`,

of total degree `Σ_c α_c = k`. At the lattice point with multi-index `β` the scaled barycentric
coordinate `k λ_c` takes the value `β_c`, so `L_α` there is `∏_c ∏_{r < α_c} (β_c − r)/(α_c − r)`:
it is `1` at `β = α`, and at any other `β` some `β_c < α_c` — because the two multi-indices have the
same sum — so the factor `r = β_c` vanishes. That makes the evaluation map onto the lattice
*surjective*, and since `ℙ_k` and the lattice have the same finite cardinality `C(k+2, 2)`,
surjective forces bijective.

No divisibility of a multivariate polynomial by an affine form is needed, and neither is the
induction on `k` that the classical argument runs.
-/

section PrincipalLattice

open Finset Module MvPolynomial

/-- The **Lagrange factor** `∏_{r < a} (ℓ − r)/(a − r)` of an affine form `ℓ`: it is `1` where
`ℓ = a` and `0` where `ℓ` takes a natural value smaller than `a`, and its total degree is at
most `a`. -/
noncomputable def lagFactor (ℓ : MvPolynomial (Fin 2) ℝ) (a : ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∏ r ∈ Finset.range a, C ((a : ℝ) - r)⁻¹ * (ℓ - C (r : ℝ))

theorem totalDegree_lagFactor_le {ℓ : MvPolynomial (Fin 2) ℝ} (hℓ : ℓ.totalDegree ≤ 1) (a : ℕ) :
    (lagFactor ℓ a).totalDegree ≤ a := by
  refine le_trans (totalDegree_finsetProd _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ => 1) fun r _ => ?_) (by simp)
  refine le_trans (totalDegree_mul _ _) ?_
  rw [totalDegree_C, zero_add]
  exact le_trans (totalDegree_sub_C_le _ _) hℓ

theorem eval_lagFactor (x : Fin 2 → ℝ) (ℓ : MvPolynomial (Fin 2) ℝ) (a : ℕ) :
    eval x (lagFactor ℓ a) = ∏ r ∈ Finset.range a, ((a : ℝ) - r)⁻¹ * (eval x ℓ - r) := by
  simp [lagFactor]

/-- The Lagrange factor is `1` where its form takes the value `a`: every factor is `(a − r)/(a − r)`
and `r < a`. -/
theorem eval_lagFactor_self {x : Fin 2 → ℝ} {ℓ : MvPolynomial (Fin 2) ℝ} {a : ℕ}
    (h : eval x ℓ = (a : ℝ)) : eval x (lagFactor ℓ a) = 1 := by
  rw [eval_lagFactor, h]
  refine Finset.prod_eq_one fun r hr => ?_
  have hne : ((a : ℝ) - r) ≠ 0 := by
    have : (r : ℝ) < a := by exact_mod_cast Finset.mem_range.mp hr
    linarith
  field_simp

/-- The Lagrange factor vanishes where its form takes a natural value below `a`: the factor with
`r = b` is zero. -/
theorem eval_lagFactor_of_lt {x : Fin 2 → ℝ} {ℓ : MvPolynomial (Fin 2) ℝ} {a b : ℕ} (hb : b < a)
    (h : eval x ℓ = (b : ℝ)) : eval x (lagFactor ℓ a) = 0 := by
  rw [eval_lagFactor, h]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hb) (by simp)

/-- The three barycentric coordinates `λ̂₁ = 1 − x̂₁ − x̂₂`, `λ̂₂ = x̂₁` and `λ̂₃ = x̂₂` of the
reference triangle, scaled by `k`, so that each takes an integer value at every point of
`N̂_k`. -/
noncomputable def scaledBary (k : ℕ) : Fin 3 → MvPolynomial (Fin 2) ℝ :=
  ![C (k : ℝ) * (1 - X 0 - X 1), C (k : ℝ) * X 0, C (k : ℝ) * X 1]

theorem totalDegree_scaledBary_le (k : ℕ) (c : Fin 3) : (scaledBary k c).totalDegree ≤ 1 := by
  have hX : ∀ i : Fin 2, (X i : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 := fun i =>
    le_of_eq (totalDegree_X i)
  have hmul : ∀ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ 1 →
      (C (k : ℝ) * q).totalDegree ≤ 1 := fun q hq =>
    le_trans (totalDegree_mul _ _) (by rw [totalDegree_C, zero_add]; exact hq)
  fin_cases c
  · exact hmul _ (le_trans (totalDegree_sub _ _)
      (max_le (le_trans (totalDegree_sub _ _) (max_le (by simp) (hX 0))) (hX 1)))
  · exact hmul _ (hX 0)
  · exact hmul _ (hX 1)

/-- The point `(m₁/k, m₂/k)` of the **principal lattice** `N̂_k` of the reference triangle. As `m`
ranges over the exponent vectors with `m₁ + m₂ ≤ k` this is exactly the book's
`N̂_k = {Σ tᵢ âᵢ : Σ tᵢ = 1, tᵢ ∈ {0, 1/k, …, 1}}`. -/
noncomputable def latticePoint (k : ℕ) (m : Fin 2 →₀ ℕ) (i : Fin 2) : ℝ := (m i : ℝ) / k

/-- The barycentric multi-index `(k − m₁ − m₂, m₁, m₂)` of a lattice point: the values of the
scaled barycentric coordinates there. -/
def latticeMulti (k : ℕ) (m : Fin 2 →₀ ℕ) : Fin 3 → ℕ := ![k - m 0 - m 1, m 0, m 1]

theorem sum_latticeMulti {k : ℕ} {m : Fin 2 →₀ ℕ} (hm : m 0 + m 1 ≤ k) :
    ∑ c, latticeMulti k m c = k := by
  simp only [Fin.sum_univ_three, latticeMulti, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  omega

/-- At a lattice point the scaled barycentric coordinates take the values of its multi-index. -/
theorem eval_scaledBary {k : ℕ} (hk : 0 < k) {m : Fin 2 →₀ ℕ} (hm : m 0 + m 1 ≤ k) (c : Fin 3) :
    eval (latticePoint k m) (scaledBary k c) = (latticeMulti k m c : ℝ) := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hcast : ((k - m 0 - m 1 : ℕ) : ℝ) = (k : ℝ) - m 0 - m 1 := by
    have h1 : m 0 ≤ k := by omega
    have h2 : m 1 ≤ k - m 0 := by omega
    rw [Nat.cast_sub h2, Nat.cast_sub h1]
  fin_cases c
  · change eval (latticePoint k m) (C (k : ℝ) * (1 - X 0 - X 1)) = ((k - m 0 - m 1 : ℕ) : ℝ)
    rw [hcast]
    simp only [map_mul, map_sub, map_one, eval_C, eval_X, latticePoint]
    field_simp
  · change eval (latticePoint k m) (C (k : ℝ) * X 0) = ((m 0 : ℕ) : ℝ)
    simp only [map_mul, eval_C, eval_X, latticePoint]
    field_simp
  · change eval (latticePoint k m) (C (k : ℝ) * X 1) = ((m 1 : ℕ) : ℝ)
    simp only [map_mul, eval_C, eval_X, latticePoint]
    field_simp

/-- **Silvester's shape function** of the principal lattice at the point with exponent vector `m`:
the product over the three barycentric coordinates of the Lagrange factors of their multi-index
entries. -/
noncomputable def latticeShape (k : ℕ) (m : Fin 2 →₀ ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∏ c, lagFactor (scaledBary k c) (latticeMulti k m c)

/-- The shape functions lie in `ℙ_k`: the three multi-index entries sum to `k`. -/
theorem totalDegree_latticeShape_le {k : ℕ} {m : Fin 2 →₀ ℕ} (hm : m 0 + m 1 ≤ k) :
    (latticeShape k m).totalDegree ≤ k := by
  refine le_trans (totalDegree_finsetProd _ _) ?_
  refine le_trans (Finset.sum_le_sum fun c _ =>
    totalDegree_lagFactor_le (totalDegree_scaledBary_le k c) _) ?_
  exact le_of_eq (sum_latticeMulti hm)

/-- Two distinct lattice points have multi-indices of the same sum, so one entry of the second is
strictly below the corresponding entry of the first. This is what makes a shape function vanish at
every node but its own. -/
theorem exists_latticeMulti_lt {k : ℕ} {m m' : Fin 2 →₀ ℕ} (hm : m 0 + m 1 ≤ k)
    (hm' : m' 0 + m' 1 ≤ k) (hne : m ≠ m') :
    ∃ c, latticeMulti k m' c < latticeMulti k m c := by
  have hcoord : m 0 ≠ m' 0 ∨ m 1 ≠ m' 1 := by
    by_contra hcon
    have h0 : m 0 = m' 0 := not_not.mp fun hh => hcon (Or.inl hh)
    have h1 : m 1 = m' 1 := not_not.mp fun hh => hcon (Or.inr hh)
    refine hne (Finsupp.ext fun i => ?_)
    fin_cases i
    · exact h0
    · exact h1
  rcases lt_or_ge (m' 0) (m 0) with h0 | h0
  · exact ⟨1, by simpa [latticeMulti] using h0⟩
  · rcases lt_or_ge (m' 1) (m 1) with h1 | h1
    · exact ⟨2, by simpa [latticeMulti] using h1⟩
    · refine ⟨0, ?_⟩
      simp only [latticeMulti, Matrix.cons_val_zero]
      omega

/-- **The shape functions are dual to the lattice points**: `L_m(x_{m'}) = δ_{m m'}`. -/
theorem eval_latticeShape {k : ℕ} (hk : 0 < k) {m m' : Fin 2 →₀ ℕ} (hm : m 0 + m 1 ≤ k)
    (hm' : m' 0 + m' 1 ≤ k) :
    eval (latticePoint k m') (latticeShape k m) = if m = m' then 1 else 0 := by
  rw [latticeShape, map_prod]
  split_ifs with h
  · subst h
    exact Finset.prod_eq_one fun c _ => eval_lagFactor_self (eval_scaledBary hk hm c)
  · obtain ⟨c, hc⟩ := exists_latticeMulti_lt hm hm' (Ne.symm fun hh => h hh.symm)
    exact Finset.prod_eq_zero (Finset.mem_univ c)
      (eval_lagFactor_of_lt hc (eval_scaledBary hk hm' c))

/-- The index set of the principal lattice `N̂_k`, which is also the index set of the monomial basis
of `ℙ_k`: the exponent vectors of total degree at most `k`. Indexing the nodes and the monomials by
one type is what makes the two cardinalities agree without a separate count. -/
def latticeIndex (k : ℕ) : Set (Fin 2 →₀ ℕ) := {m | (m.sum fun _ e => e) ≤ k}

theorem mem_latticeIndex_iff {k : ℕ} {m : Fin 2 →₀ ℕ} :
    m ∈ latticeIndex k ↔ m 0 + m 1 ≤ k := by
  change (m.sum fun _ e => e) ≤ k ↔ _
  rw [Finsupp.sum_fintype _ _ fun _ => rfl, Fin.sum_univ_two]

/-- The interpolation map of Proposition 10.2.1: evaluation of a polynomial of total degree at most
`k` at the points of the principal lattice `N̂_k`. -/
noncomputable def latticeEval (k : ℕ) :
    (MvPolynomial.restrictTotalDegree (Fin 2) ℝ k) →ₗ[ℝ] (latticeIndex k → ℝ) where
  toFun p m := eval (latticePoint k (m : Fin 2 →₀ ℕ)) (p : MvPolynomial (Fin 2) ℝ)
  map_add' p q := by ext m; simp
  map_smul' a p := by ext m; simp

@[simp]
theorem latticeEval_apply (k : ℕ) (p : MvPolynomial.restrictTotalDegree (Fin 2) ℝ k)
    (m : latticeIndex k) :
    latticeEval k p m = eval (latticePoint k (m : Fin 2 →₀ ℕ)) (p : MvPolynomial (Fin 2) ℝ) := rfl

/-- **Proposition 10.2.1**: a polynomial of total degree at most `k` on a triangle is uniquely
determined by its values at the `(k+1)(k+2)/2` points of the principal lattice `N̂_k` — that is,
the interpolation problem there is unisolvent.

The surjectivity is Silvester's shape functions `latticeShape`, which are dual to the nodes by
`eval_latticeShape`; the injectivity then follows because `ℙ_k` and the lattice both have
`C(k + 2, 2)` elements, the lattice by construction, since it is indexed by the very exponent
vectors that index the monomial basis. The book quotes the proposition without proof. -/
theorem proposition_10_2_1 {k : ℕ} (hk : 0 < k) : Function.Bijective (latticeEval k) := by
  classical
  have hfin : Fintype (latticeIndex k) := by
    change Fintype ↑{m : Fin 2 →₀ ℕ | (m.sum fun _ e => e) ≤ k}
    exact Fintype.ofEquiv _ (MvPolynomial.slackEquiv (Fin 2) k).symm
  have hshape : ∀ m : latticeIndex k,
      latticeShape k (m : Fin 2 →₀ ℕ) ∈ MvPolynomial.restrictTotalDegree (Fin 2) ℝ k := fun m => by
    rw [mem_restrictTotalDegree]
    exact totalDegree_latticeShape_le (mem_latticeIndex_iff.mp m.2)
  have hsurj : Function.Surjective (latticeEval k) := by
    intro b
    refine ⟨∑ m : latticeIndex k, b m • ⟨latticeShape k (m : Fin 2 →₀ ℕ), hshape m⟩, ?_⟩
    ext m'
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single m']
    · have h := eval_latticeShape hk (mem_latticeIndex_iff.mp m'.2) (mem_latticeIndex_iff.mp m'.2)
      change b m' * eval (latticePoint k (m' : Fin 2 →₀ ℕ))
        (latticeShape k (m' : Fin 2 →₀ ℕ)) = b m'
      rw [h]
      simp
    · intro m _ hmm
      have h := eval_latticeShape hk (mem_latticeIndex_iff.mp m.2) (mem_latticeIndex_iff.mp m'.2)
      change b m * eval (latticePoint k (m' : Fin 2 →₀ ℕ)) (latticeShape k (m : Fin 2 →₀ ℕ)) = 0
      have hne2 : ¬ ((m : Fin 2 →₀ ℕ) = (m' : Fin 2 →₀ ℕ)) := fun hh => hmm (Subtype.ext hh)
      rw [h]
      simp [hne2]
    · intro h; exact absurd (Finset.mem_univ m') h
  have hcardIdx : Fintype.card (latticeIndex k) = (k + 2).choose k := by
    rw [← Nat.card_eq_fintype_card]
    exact (MvPolynomial.card_setOf_sum_le (Fin 2) k).trans (by simp)
  have hdim : finrank ℝ (MvPolynomial.restrictTotalDegree (Fin 2) ℝ k)
      = finrank ℝ (latticeIndex k → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card, hcardIdx,
      MvPolynomial.finrank_restrictTotalDegree (Fin 2) k ℝ]
    simp only [Fintype.card_fin]
    rw [← Nat.choose_symm (by omega : k ≤ k + 2)]
    congr 1
    omega
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩

/-- **Proposition 10.2.1**, in the form the book's proofs use it: a polynomial of total degree at
most `k` vanishing at every point of the principal lattice is the zero polynomial. -/
theorem eq_zero_of_eval_latticePoint {k : ℕ} (hk : 0 < k) {p : MvPolynomial (Fin 2) ℝ}
    (hp : p.totalDegree ≤ k)
    (h : ∀ m : Fin 2 →₀ ℕ, m 0 + m 1 ≤ k → eval (latticePoint k m) p = 0) : p = 0 := by
  have hmem : p ∈ MvPolynomial.restrictTotalDegree (Fin 2) ℝ k := by
    rw [mem_restrictTotalDegree]; exact hp
  have hzero := (proposition_10_2_1 hk).1 (a₁ := ⟨p, hmem⟩) (a₂ := 0) ?_
  · exact congrArg Subtype.val hzero
  · ext m
    rw [latticeEval_apply, latticeEval_apply]
    simpa using h (m : Fin 2 →₀ ℕ) (mem_latticeIndex_iff.mp m.2)

end PrincipalLattice

end AtkinsonHan.Chapter10
