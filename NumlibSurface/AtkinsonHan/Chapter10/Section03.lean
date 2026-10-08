import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Numlib.Analysis.Sobolev.Affine
import Numlib.Analysis.Sobolev.SeminormCompare
import Numlib.Analysis.Sobolev.Simplex
import Numlib.Analysis.Sobolev.Triangulation
import Numlib.Approximation.NodalInterpolation
import Numlib.Geometry.Euclidean.TriangleShape
import NumlibSurface.AtkinsonHan.Chapter07.Section03
import NumlibSurface.AtkinsonHan.Chapter10.Section02
import Numlib.FiniteElement.Interpolation

/-!
# Atkinson–Han §10.3: local interpolation and regular families

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §10.3.

The section estimates the finite element interpolation error on an element by transporting the
problem to the reference element, and then sums over the elements of a triangulation. The general
theory is the backbone's `Numlib/FiniteElement/Interpolation.lean`; the numbered results here
restate it in the book's terms and are proved by delegation. Everything
is here: Theorem 10.3.1 (the transport of the interpolant), Theorem 10.3.3 (the estimate on
the reference element), Theorem 10.3.4 (the affine change of variables in `H^m`), Theorem 10.3.5
(the local estimate), Definition 10.3.6 and Corollary 10.3.7 (regular families), Example
10.3.8 (the linear element on triangles, and its `Q₁` analogue on the unit square), and Theorem
10.3.9 (the global estimate on a triangulation). Two of these are not Sobolev statements at all:

* **Theorem 10.3.1**, that nodal interpolation commutes with the affine pullback, is an algebraic
  identity between two finite sums. It is the backbone's `Approximation.nodalInterp_comp`, and the
  book's `Π̂` and `Π_K` of (10.3.1) and (10.3.2) are `Approximation.nodalInterp` at the reference
  nodes and at their images under `F_K`.
* **Definition 10.3.6**, the regularity of a family of partitions, needs only the diameter of an
  element and a ball inscribed in it.

## Main definitions

* `meshSize` — the mesh parameter (10.3.9), `h = max_{K ∈ 𝒯_h} h_K`, written as a supremum of
  diameters so that it is defined for any collection of elements; `diam_le_meshSize` is the
  maximum property for a finite one.
* `IsRegularFamily` — Definition 10.3.6: a family of partitions is regular when the ratios
  `h_K / ρ_K` are bounded uniformly and the mesh parameter tends to `0` along the family.
* `q1Node`, `q1Shape` — the `Q₁` element on the unit square: the four vertices and the bilinear
  shape functions of Exercise 10.2.3, on `EuclideanSpace ℝ (Fin 2)`.

## Main results

* `theorem_10_3_1` — `Π̂ (v ∘ F_K) = (Π_K v) ∘ F_K`.
* `theorem_10_3_3` — `|v̂ − Π̂ v̂|_{m,K̂} ≤ c |v̂|_{k+1,K̂}` on a reference element `K̂` that is a
  bounded connected Sobolev extension domain (for every exponent), with `m ≤ k + 1`,
  `k + 1 > d/2`, shape functions in `H^m(K̂)` and the polynomial invariance `ℙ_k(K̂) ⊆ X̂`: the
  book's argument through the embedding `H^{k+1}(K̂) ↪ C(K̂̄)` and Corollary 7.3.18.
* `theorem_10_3_4` — the affine change of variables in `H^m`: `v ∈ H^m(K)` iff `v ∘ F_K ∈ H^m(K̂)`,
  with the seminorm bounds (10.3.5)–(10.3.6); the general lemmas are
  `Numlib/Analysis/Sobolev/Affine.lean`.
* `theorem_10_3_5` — `|v − Π_K v|_{m,K} ≤ c h_K^{k+1} ρ_K^{−m} |v|_{k+1,K}` on every affine image
  `K = F_K(K̂)`, with `c` depending on `K̂` and `Π̂` only.
* `corollary_10_3_7` — `‖v − Π_K v‖_{m,K} ≤ c h_K^{k+1−m} |v|_{k+1,K}` on a regular family whose
  elements have diameter at most `H`.
* `example_10_3_8` — the book's example: Corollary 10.3.7 for the linear element (`P₁`, the
  barycentric coordinates as shape functions) on the affine images of the reference triangle,
  `m ≤ 2`: `‖v − Π_K v‖_{m,K} ≤ c h_K^{2−m} |v|_{2,K}`, (10.3.11).
* `example_10_3_8_square` — the same for the `Q₁` element on the affine images of the unit
  square.
* `theorem_10_3_9` — the global estimate `‖v − Π_h v‖_{m,Ω} ≤ c h^{k+1−m} |v|_{k+1,Ω}`, `m = 0, 1`,
  on a regular family of triangulations (`Triangulation`, `Numlib/Geometry/Triangulation.lean`)
  for a conforming element type, and `theorem_10_3_9_linear`, `theorem_10_3_9_lattice`, its
  instances for the linear element and for the `ℙ_k` Lagrange element on the principal lattice.
* `example_10_3_2` — the linear element: the barycentric coordinates of a simplex are nodal for its
  vertices, so `Π_K` is the interpolant through the vertex values, and
  `nodalInterp_coord_affineMap` says that it reproduces affine functions.

## Deviations from the book

The book's reference element is a triangle, a Lipschitz domain, and its Theorem 10.3.3 rests on
Corollary 7.3.18 (Bramble–Hilbert) and the embedding `H^{k+1}(K̂) ↪ C(K̂)` on it. The backbone
proves both on Sobolev extension domains (`IsSobolevExtensionDomainAll`,
`Numlib/Analysis/Sobolev/{EmbeddingDomain,DenyLions}.lean`); no general Lipschitz extension
operator is formalized, so the estimates are stated for a reference element that is an extension
domain *as a hypothesis*. The reference triangle satisfies it
(`isSobolevExtensionDomainAll_referenceTriangle`, `Numlib/Analysis/Sobolev/Simplex.lean`: two
reflections across its legs reach the diamond `|x̂₁| + |x̂₂| < 1`, an affine image of the unit
square, and being an extension domain is affine-invariant), as does the unit square
(`isSobolevExtensionDomainAll_unitSquare`, Brezis's Remark 9), so every estimate of the section
applies to the book's triangles verbatim: `example_10_3_8` is the book's example and
`example_10_3_8_square` its `Q₁` counterpart. The dimension is general and the hypothesis
`k + 1 > d/2` is carried explicitly (the book's `k > 0` is its case `d = 2`).

`H^m(K)` is `Chapter07.definition_7_2_2 m 2 K` (`MemSobolev v m 2 K volume`), and the seminorm
`|·|_{m,K}` and norm `‖·‖_{m,K}` are the backbone's tensor `sobolevSeminorm` and `sobolevNorm`,
equivalent to the book's multi-index ones with constants depending on `d` and `m` only
(`Numlib/Analysis/Sobolev/SeminormCompare.lean` carries the comparison, used inside
`theorem_10_3_3`). A function of `H^{k+1}(K)` is read on its continuous representative up to the
boundary (`ContinuousOn v (closure K)`), which every element has by Theorem 7.3.7 (c); the nodal
values at vertices, which lie on the boundary of the open element, are then meaningful.

Corollary 10.3.7 carries a bound `h_K ≤ H` on the diameters of the elements of the family, which
the book leaves implicit: its constant depends on such a bound through the seminorms of order
`j < m` (the top-order estimate of Theorem 10.3.5 needs none).

The book's `ρ_K` is the diameter of the *largest* ball inscribed in `K`, a supremum Mathlib has no
name for and which need not be attained for a general set. Condition (a) of Definition 10.3.6 uses
it only through the inequality `h_K ≤ σ ρ_K`, so `IsRegularFamily` asks instead for *some* inscribed
ball with `h_K ≤ σ · (2 r)`. For a `K` whose largest inscribed ball exists — the book's triangles —
the two readings agree, and in either reading the condition says the elements do not degenerate.

`𝒯_h` is read as a collection of elements, `Set (Set (EuclideanSpace ℝ (Fin d)))`, and the family is
indexed by an arbitrary type with a filter along which the mesh parameter tends to zero: the book
indexes by `h` itself and lets `h → 0`. The partition axioms (1)–(4) of §10.2 — that the elements
are triangles covering `Ω̄` with disjoint interiors and matching faces — play no part in Definition
10.3.6 and are not formalized; that is why the definition is stated for a family of collections and
not for a family of triangulations, and why Corollary 10.3.7 quantifies over the elements `K` of the
family together with the affine map `F_K` carrying the reference element onto each.

## Not formalized here

Exercises 10.3.1, 10.3.2, 10.3.4 and 10.3.7 are not nodes; Exercise 10.3.3
(`h_K / ρ_K` bounded if and only if the minimal angles are bounded below) is Sobolev-free, and is
`exercise_10_3_3` below. The remark after Theorem 10.3.9 on the interpolation of discontinuous
functions by local `L²` projections is a pointer to the literature.
-/

open Filter Metric Topology

open scoped Real

namespace AtkinsonHan.Chapter10

variable {d : ℕ}

/-- **Theorem 10.3.1.**  Let `F_K` be an affine bijection of the reference element onto `K`, let
`x̂ᵢ` be the nodal points of the reference element and `φ̂ᵢ` the associated basis functions, and put
`xᵢᴷ = F_K(x̂ᵢ)` and `φᵢᴷ = φ̂ᵢ ∘ F_K⁻¹` as in (10.2.27). Then the interpolation operators (10.3.1)
`Π̂ v̂ = Σ v̂(x̂ᵢ) φ̂ᵢ` and (10.3.2) `Π_K v = Σ v(xᵢᴷ) φᵢᴷ` satisfy

  `Π̂ (v ∘ F_K) = (Π_K v) ∘ F_K`.

The proof is the definition read twice: `v(xᵢᴷ) = v̂(x̂ᵢ)` and `φᵢᴷ ∘ F_K = φ̂ᵢ`. Neither the
affinity of `F_K` nor the duality `φ̂ᵢ(x̂ⱼ) = δᵢⱼ` is used — only that `F_K` is invertible — so this
is the backbone's `Approximation.nodalInterp_comp` for the equivalence `F_K`. The nodal property
survives the transport (`Approximation.IsNodalBasis.comp`), which is the book's display
`φᵢᴷ(xⱼᴷ) = δᵢⱼ`. -/
theorem theorem_10_3_1 {I : ℕ} (F : EuclideanSpace ℝ (Fin d) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin d))
    (x : Fin I → EuclideanSpace ℝ (Fin d)) (φ : Fin I → EuclideanSpace ℝ (Fin d) → ℝ)
    (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    Approximation.nodalInterp x φ (v ∘ F) =
      Approximation.nodalInterp (F ∘ x) (fun i => φ i ∘ F.symm) v ∘ F :=
  (Approximation.nodalInterp_comp x φ v (F := F) (G := F.symm) F.symm_apply_apply).symm

/-- **Example 10.3.2, the linear element.**  On a simplex with vertices `b i` the shape functions of
the linear element are the barycentric coordinates `λᵢ`, and they are nodal for the vertices:
`λᵢ(bⱼ) = δᵢⱼ`. So `Approximation.nodalInterp b (fun i => λᵢ)` *is* the operator `Π_K` of (10.3.2)
for that element — the function agreeing with `v` at each vertex — and Theorem 10.3.1 applies to it,
the transported shape functions `λᵢ ∘ F_K⁻¹` being the barycentric coordinates of the image simplex.

The book writes the reference element as a triangle in the plane; nothing here needs the dimension
or the number of vertices, and the coordinates are Mathlib's `AffineBasis.coord`. -/
theorem example_10_3_2 {ι : Type*} (b : AffineBasis ι ℝ (EuclideanSpace ℝ (Fin d))) :
    Approximation.IsNodalBasis (b : ι → EuclideanSpace ℝ (Fin d))
      (fun i => (b.coord i : EuclideanSpace ℝ (Fin d) → ℝ)) where
  eval_self _ := b.coord_apply_eq _
  eval_of_ne _ _ hij := b.coord_apply_ne hij

/-- **The linear element is exact on affine functions**: `Π_K f = f` for an affine `f`. It is the
`k = 1` case of the reproduction property that makes the interpolation error estimates of §10.3
worth having, and it is the identity `f(y) = Σᵢ λᵢ(y) f(bᵢ)`, which is the affine map applied to the
barycentric representation `y = Σᵢ λᵢ(y) bᵢ`. -/
theorem nodalInterp_coord_affineMap {ι : Type*} [Fintype ι]
    (b : AffineBasis ι ℝ (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ) :
    Approximation.nodalInterp (b : ι → EuclideanSpace ℝ (Fin d))
      (fun i => (b.coord i : EuclideanSpace ℝ (Fin d) → ℝ)) f = f := by
  funext y
  rw [Approximation.nodalInterp_apply]
  have hw : ∑ i, b.coord i y = 1 := b.sum_coord_apply_eq_one y
  have h := Finset.univ.map_affineCombination (b : ι → EuclideanSpace ℝ (Fin d))
    (fun i => b.coord i y) hw f
  rw [b.affineCombination_coord_eq_self y] at h
  rw [h, Finset.univ.affineCombination_eq_linear_combination _ _ hw]
  rfl

/-- **The mesh parameter (10.3.9)**, `h = max_{K ∈ 𝒯_h} h_K`, of a collection of elements: the
supremum of their diameters. For a finite collection — the book's partitions are finite — the
supremum is the maximum, which is `diam_le_meshSize`. -/
noncomputable def meshSize (T : Set (Set (EuclideanSpace ℝ (Fin d)))) : ℝ :=
  sSup (Metric.diam '' T)

/-- Every element of a finite collection has diameter at most the mesh parameter. -/
theorem diam_le_meshSize {T : Set (Set (EuclideanSpace ℝ (Fin d)))} (hT : T.Finite)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : K ∈ T) : Metric.diam K ≤ meshSize T :=
  le_csSup (hT.image _).bddAbove (Set.mem_image_of_mem _ hK)

/-- **Definition 10.3.6.**  A family `{𝒯_h}` of finite element partitions is **regular** if

* (a) there is a `σ` with `h_K / ρ_K ≤ σ` for every element `K` of every member of the family, and
* (b) the mesh parameter `h` tends to `0` along the family.

Here `h_K = diam K` and `ρ_K` is the diameter of the largest ball inscribed in `K`; condition (a) is
written as the existence of an inscribed ball of radius `r` with `h_K ≤ σ (2 r)`, which is what the
inequality `h_K ≤ σ ρ_K` says whenever the largest inscribed ball exists. Condition (b) is a limit
along a filter `l` on the index type, the book's `h → 0`.

Regularity is what turns the element-wise estimate (10.3.7), whose right-hand side carries both
`h_K` and `ρ_K`, into a bound in `h_K` alone (Corollary 10.3.7). -/
def IsRegularFamily {ι : Type*} (l : Filter ι)
    (T : ι → Set (Set (EuclideanSpace ℝ (Fin d)))) : Prop :=
  (∃ σ : ℝ, ∀ i, ∀ K ∈ T i, ∃ (c : EuclideanSpace ℝ (Fin d)) (r : ℝ),
      0 < r ∧ Metric.closedBall c r ⊆ K ∧ Metric.diam K ≤ σ * (2 * r)) ∧
    Tendsto (fun i => meshSize (T i)) l (𝓝 0)

/-- The book's regularity of a family is the backbone's `FiniteElement.IsRegularFamily`: the mesh
parameter `meshSize` is the supremum of the diameters that the backbone writes inline. -/
theorem isRegularFamily_iff_isRegularFamily {ι : Type*} {l : Filter ι}
    {T : ι → Set (Set (EuclideanSpace ℝ (Fin d)))} :
    IsRegularFamily l T ↔ FiniteElement.IsRegularFamily l T :=
  Iff.rfl

/-! ### Exercise 10.3.3: regularity against the minimal angle

The exercise is about triangles, and `ρ_K` is the diameter `2 ρ` of the inscribed circle, which for
a triangle is `Affine.Simplex.inradius`. The statement below is therefore condition (a) of
Definition 10.3.6 read on a family of triangles with the *actual* inradius, rather than through the
weaker "some inscribed ball" form that `IsRegularFamily` uses for a family of arbitrary sets. The
geometry is `Numlib.Geometry.Euclidean.TriangleShape`. -/

/-- **Exercise 10.3.3.** For a family of triangles, condition (a) of Definition 10.3.6 — the ratios
`h_K / ρ_K` are bounded — holds if and only if the angles of the triangles are bounded away from
zero.

Both directions are quantitative: a bound `h_K ≤ σ ρ_K` gives every angle at least
`arcsin (1 / (2 σ))`, and a bound `α ≤ θ` on all the angles gives `h_K ≤ (3 / sin² α) ρ_K`. -/
theorem exercise_10_3_3 {ι : Type*}
    (T : ι → Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2) :
    (∃ σ : ℝ, ∀ t, Metric.diam (Set.range (T t).points) ≤ σ * (2 * (T t).inradius))
      ↔ ∃ α : ℝ, 0 < α ∧ ∀ t i, α ≤ (T t).triangleAngle i := by
  constructor
  · rintro ⟨σ, hσ⟩
    have hσ' : ∀ t, Metric.diam (Set.range (T t).points) ≤ max σ 1 * (2 * (T t).inradius) := by
      intro t
      refine (hσ t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
      linarith [(T t).inradius_pos]
    set τ := max σ 1 with hτ
    have hτpos : (0 : ℝ) < τ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hle1 : 1 / (2 * τ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [le_max_right σ 1]
    refine ⟨Real.arcsin (1 / (2 * τ)), Real.arcsin_pos.2 (by positivity), fun t i => ?_⟩
    have hD := (T t).diam_pos
    have hr := (T t).inradius_pos
    have hsin : 1 / (2 * τ) ≤ Real.sin ((T t).triangleAngle i) := by
      have h1 := (T t).inradius_le_diam_mul_sin_triangleAngle i
      have h2 := hσ' t
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(T t).sin_triangleAngle_nonneg i]
    calc Real.arcsin (1 / (2 * τ)) ≤ Real.arcsin (Real.sin ((T t).triangleAngle i)) :=
          Real.arcsin_le_arcsin hsin
      _ ≤ (T t).triangleAngle i := by
          rcases le_total ((T t).triangleAngle i) (π / 2) with h | h
          · rw [Real.arcsin_sin (by linarith [(T t).triangleAngle_nonneg i, Real.pi_pos]) h]
          · exact (Real.arcsin_le_pi_div_two _).trans h
  · rintro ⟨α, hαpos, hα⟩
    set β := min α (π / 2) with hβ
    have hβpos : 0 < β := lt_min hαpos (by linarith [Real.pi_pos])
    have hβle : β ≤ π / 2 := min_le_right _ _
    have hsinβ : 0 < Real.sin β :=
      Real.sin_pos_of_pos_of_lt_pi hβpos (by linarith [Real.pi_pos])
    refine ⟨3 / (2 * Real.sin β ^ 2), fun t => ?_⟩
    have h := (T t).diam_mul_sin_sq_le hβpos hβle
      (fun i => le_trans (min_le_left _ _) (hα t i))
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [h, (T t).inradius_pos]

/-! ### Theorem 10.3.4 -/

section Theorem1034

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- **Theorem 10.3.4** (affine change of variables in `H^m`). Let `x = T x̂ + b` be a bijection of
the reference element `K̂` onto the element `K`, both open subsets of `ℝ^d`, and let
`v̂ = v ∘ F`, `F x̂ = T x̂ + b`. Then `v ∈ H^m(K)` if and only if `v̂ ∈ H^m(K̂)`, and the estimates
(10.3.5) `|v̂|_{m,K̂} ≤ ‖T‖^m |det T|^{-1/2} |v|_{m,K}` and (10.3.6)
`|v|_{m,K} ≤ ‖T⁻¹‖^m |det T|^{1/2} |v̂|_{m,K̂}` hold.

`H^m(K)` is `Chapter07.definition_7_2_2 m 2 K` (the bundled reading of Definition 7.2.2), and the
seminorm `|·|_{m,K}` is the backbone's `sobolevSeminorm · m 2 K volume`, the `L²(K)` norm of the
operator norm of the derivative tensor of order `m`. That seminorm is equivalent to the book's
`(∑_{|α| = m} ‖∂^α v‖²_{L²(K)})^{1/2}` with constants depending on `d` and `m` only (the book's
`c`, which it does not specify); for the tensor seminorm the constant is exactly `1`, and this is
what is proved: `∂^m v̂ (x̂) = ∂^m v (F x̂) ∘ (T, …, T)` has operator norm at most
`‖T‖^m ‖∂^m v (F x̂)‖`, and the change of variables `x = F x̂` in the `L²` integral contributes
`|det T|^{-1/2}` (`sobolevSeminorm_comp_affine_le`, `eLpNorm_comp_affine`); (10.3.6) is (10.3.5)
for `F⁻¹`. The membership equivalence is `memSobolev_comp_affine_iff`, from the backbone's
`HasWeakIteratedFDerivOn.comp_affineEquiv`. `‖T‖` is the operator norm of `T` on Euclidean
`ℝ^d` and `det T` the determinant of its linear map. -/
theorem theorem_10_3_4 (T : 𝔼 ≃L[ℝ] 𝔼) (b : 𝔼) (Khat K : Opens 𝔼)
    (hK : (fun x ↦ T x + b) '' Khat = K) (m : ℕ) (v : 𝔼 → ℝ) :
    (Chapter07.definition_7_2_2 m 2 K v ↔
      Chapter07.definition_7_2_2 m 2 Khat (fun x ↦ v (T x + b))) ∧
    (Chapter07.definition_7_2_2 m 2 K v →
      sobolevSeminorm (fun x ↦ v (T x + b)) m 2 Khat volume
        ≤ ENNReal.ofReal (‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ m * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ)))
          * sobolevSeminorm v m 2 K volume) ∧
    (Chapter07.definition_7_2_2 m 2 K v →
      sobolevSeminorm v m 2 K volume
        ≤ ENNReal.ofReal
            (‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ))
          * sobolevSeminorm (fun x ↦ v (T x + b)) m 2 Khat volume) := by
  have hKhat : Khat = affinePreimage T b K := (affinePreimage_eq_of_image_eq T b hK).symm
  refine ⟨?_, sobolevSeminorm_comp_affine_le_of_image T b hK,
    sobolevSeminorm_le_comp_affine_of_image T b hK⟩
  subst hKhat
  exact memSobolev_comp_affine_iff T b

end Theorem1034

/-! ### Theorem 10.3.3: the interpolation error on the reference element -/

section Theorem1033

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

variable {d : ℕ}

/-- **Theorem 10.3.3** (the interpolation error estimate on the reference element). Let `K̂ ⊆ ℝ^d`
be a bounded connected open reference element which is a Sobolev extension domain for every
exponent, let `k, m` be nonnegative integers with `m ≤ k + 1` and `k + 1 > d/2` (the book's
`k > 0`, which is this condition for `d = 2`, and the condition the book names for general `d`),
let `x̂ᵢ ∈ K̂̄` be the nodes and `φ̂ᵢ ∈ H^m(K̂)` the shape functions of the interpolation operator
`Π̂` of (10.3.1), and assume the polynomial invariance (10.3.4), `Π̂ q = q` on `K̂` for every
polynomial `q` of degree at most `k` — the hypothesis `ℙ_k(K̂) ⊆ X̂`. Then there is a constant `c`
with (10.3.3), `|v̂ − Π̂ v̂|_{m,K̂} ≤ c |v̂|_{k+1,K̂}` for every `v̂ ∈ H^{k+1}(K̂)`.
`H^{k+1}(K̂)` is `Chapter07.definition_7_2_2 (k + 1) 2 K̂`, i.e. `MemSobolev v (k + 1) 2 K̂ volume`,
and `v̂` is read on its continuous representative up to the boundary
(`ContinuousOn v (closure K̂)`), which every element has by the embedding `H^{k+1}(K̂) ↪ C(K̂̄)`
(Theorem 7.3.7 (c), `SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order`); the
nodal values `v̂(x̂ᵢ)` are then meaningful even at nodes on the boundary. The seminorms are the
tensor seminorms `sobolevSeminorm` of Theorem 10.3.4. The proof is the book's: `Π̂` is bounded from
`H^{k+1}(K̂)` to `H^m(K̂)` through the embedding
(`FiniteElement.sobolevSeminorm_sum_apply_smul_le`), it fixes `ℙ_k(K̂)`
(`FiniteElement.sum_apply_smul_ae_eq_fn_of_mem_polynomialSubmodule`), so
`|v̂ − Π̂ v̂|_{m,K̂} ≤ c inf_{q ∈ ℙ_k} ‖v̂ + q‖_{k+1,K̂}`, and Corollary 7.3.18
(`SobolevEuclidean.exists_ciInf_norm_add_le_mul_topSeminorm`) bounds the infimum by `|v̂|_{k+1,K̂}`;
the passage between the tensor seminorm and the book's multi-index seminorm is
`SobolevMultiIndex.sobolevSeminorm_fn_le` and
`SobolevMultiIndex.topSeminorm_le_mul_toReal_sobolevSeminorm`.

The book's reference element is a triangle, a Lipschitz domain, which the backbone does not
know to be an extension domain (no Lipschitz extension operator is formalized); the unit
square is one (`SobolevEuclidean.exists_extensionL_unitSquare`), so the theorem applies to `Q_k`
elements on rectangles now and to simplicial elements once a simplex extension operator
exists. -/
theorem theorem_10_3_3 {Khat : Opens (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsSobolevExtensionDomainAll d Khat)
    (hb : Bornology.IsBounded (Khat : Set (EuclideanSpace ℝ (Fin d))))
    (hc : IsPreconnected (Khat : Set (EuclideanSpace ℝ (Fin d))))
    {k m : ℕ} (hm : m ≤ k + 1) (hkd : (d : ℝ) / 2 < k + 1)
    {I : ℕ} (xhat : Fin I → EuclideanSpace ℝ (Fin d))
    (φhat : Fin I → EuclideanSpace ℝ (Fin d) → ℝ)
    (hx : ∀ i, xhat i ∈ closure (Khat : Set (EuclideanSpace ℝ (Fin d))))
    (hφ : ∀ i, MemSobolev (φhat i) m 2 Khat volume)
    (hP : ∀ q : MvPolynomial (Fin d) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ Khat, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ v : EuclideanSpace ℝ (Fin d) → ℝ, MemSobolev v (k + 1) 2 Khat volume →
      ContinuousOn v (closure (Khat : Set (EuclideanSpace ℝ (Fin d)))) →
      sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 2 Khat volume
        ≤ ENNReal.ofReal c * sobolevSeminorm v (k + 1) 2 Khat volume :=
  FiniteElement.sobolevSeminorm_sub_nodalInterp_le hΩ hb hc hm hkd xhat φhat hx hφ hP

end Theorem1033

/-! ### Theorem 10.3.5: the local interpolation error -/

section Theorem1035

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- **Theorem 10.3.5** (the local interpolation error estimate, (10.3.7)). Under the hypotheses
of Theorem 10.3.3 on the reference element `K̂` — a bounded connected extension domain with an
inscribed ball of diameter `ρ̂`, nodes `x̂ᵢ ∈ K̂̄`, shape functions `φ̂ᵢ ∈ H^m(K̂)`, the polynomial
invariance `ℙ_k(K̂) ⊆ X̂`, `m ≤ k + 1` and `k + 1 > d/2` — there is a constant `c`, depending only
on `K̂` and `Π̂`, such that for every element `K = F_K(K̂)`, `F_K x̂ = T_K x̂ + b_K`, with an
inscribed ball of diameter `ρ_K`, the interpolation operator `Π_K` of (10.3.2) — nodes
`F_K(x̂ᵢ)`, shape functions `φ̂ᵢ ∘ F_K⁻¹` — satisfies

  `|v − Π_K v|_{m,K} ≤ c h_K^{k+1} ρ_K^{−m} |v|_{k+1,K}`  for every `v ∈ H^{k+1}(K)`,

with `h_K = diam K`. The proof is the book's: Theorem 10.3.1 (`Approximation.nodalInterp_comp`)
gives `(v − Π_K v) ∘ F_K = v̂ − Π̂ v̂`, (10.3.6) of Theorem 10.3.4 transports the left-hand side to
`K̂`, Theorem 10.3.3 bounds it there by `|v̂|_{k+1,K̂}`, (10.3.5) brings that back to `K`, and
Lemma 10.2.2 bounds `‖T_K‖ ≤ h_K/ρ̂` and `‖T_K⁻¹‖ ≤ ĥ/ρ_K`; the constant is
`c = c₀ ĥ^m / ρ̂^{k+1}` with the `c₀` of (10.3.3). As in Theorem 10.3.3, `v` is read on its
continuous representative up to the boundary, `H^{k+1}(K)` is `MemSobolev v (k + 1) 2 K volume`
and the seminorms are the tensor ones; the extension-domain hypothesis on `K̂` is the backbone's
stand-in for the book's Lipschitz reference element (the unit square qualifies, the reference
triangle waits for a Lipschitz extension operator). -/
theorem theorem_10_3_5 {Khat : Opens 𝔼} (hΩ : IsSobolevExtensionDomainAll d Khat)
    (hb : Bornology.IsBounded (Khat : Set 𝔼)) (hc : IsPreconnected (Khat : Set 𝔼))
    {chat : 𝔼} {ρhat : ℝ} (hρhat : 0 < ρhat)
    (hballhat : Metric.closedBall chat (ρhat / 2) ⊆ Khat)
    {k m : ℕ} (hm : m ≤ k + 1) (hkd : (d : ℝ) / 2 < k + 1)
    {I : ℕ} (xhat : Fin I → 𝔼) (φhat : Fin I → 𝔼 → ℝ)
    (hx : ∀ i, xhat i ∈ closure (Khat : Set 𝔼))
    (hφ : ∀ i, MemSobolev (φhat i) m 2 Khat volume)
    (hP : ∀ q : MvPolynomial (Fin d) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ Khat, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (T : 𝔼 ≃L[ℝ] 𝔼) (b : 𝔼) (K : Opens 𝔼),
      (fun x ↦ T x + b) '' Khat = K →
      ∀ {cK : 𝔼} {ρK : ℝ}, 0 < ρK → Metric.closedBall cK (ρK / 2) ⊆ K →
      ∀ v : 𝔼 → ℝ, MemSobolev v (k + 1) 2 K volume → ContinuousOn v (closure (K : Set 𝔼)) →
      sobolevSeminorm (v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ xhat)
          (fun i ↦ φhat i ∘ fun y ↦ T.symm (y - b)) v) m 2 K volume
        ≤ ENNReal.ofReal (c * Metric.diam (K : Set 𝔼) ^ (k + 1) / ρK ^ m)
          * sobolevSeminorm v (k + 1) 2 K volume :=
  FiniteElement.sobolevSeminorm_sub_nodalInterp_comp_affine_le hΩ hb hc hρhat hballhat hm hkd xhat
    φhat hx hφ hP

end Theorem1035

/-! ### Corollary 10.3.7: the estimate on a regular family -/

section Corollary1037

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- **Corollary 10.3.7** (the interpolation error on a regular family, (10.3.10)). Under the
hypotheses of Theorem 10.3.5 on the reference element `K̂` (a bounded connected extension domain
with an inscribed ball of diameter `ρ̂`, nodes `x̂ᵢ ∈ K̂̄`, shape functions `φ̂ᵢ ∈ H^m(K̂)`, the
polynomial invariance `ℙ_k(K̂) ⊆ X̂`, `m ≤ k + 1`, `k + 1 > d/2`), let `{𝒯_h}` be a regular family
of partitions (Definition 10.3.6, `IsRegularFamily`) whose elements have diameter at most `H`.
Then there is a constant `c` such that for every element `K` of every `𝒯_h`, read as the open set
`K` which is the affine image `F_K(K̂)` of the reference element,

  `‖v − Π_K v‖_{m,K} ≤ c h_K^{k+1−m} |v|_{k+1,K}`  for every `v ∈ H^{k+1}(K)`.

Regularity gives `ρ_K ≥ h_K/σ`, which turns the `h_K^{k+1} ρ_K^{−m}` of (10.3.7) into
`σ^m h_K^{k+1−m}`; the norm `‖·‖_{m,K}` (`sobolevNorm`, the tensor norm of Definition 7.2.2)
is at most the sum of the seminorms of orders `j ≤ m`
(`MemSobolev.sobolevNorm_le_sum_sobolevSeminorm`), each bounded by Theorem 10.3.5 at order `j`
with `h_K^{k+1−j} = h_K^{m−j} h_K^{k+1−m} ≤ H^{m−j} h_K^{k+1−m}`. The bound `h_K ≤ H` on the
elements is left implicit by the book — its `c` depends on it through the lower-order seminorms
(for the top seminorm `j = m` alone no such bound is needed, Theorem 10.3.5); it holds for any
family with `h → 0` once the finitely many
coarse meshes are accounted for. `v` is read on its continuous representative up to the boundary,
as in Theorems 10.3.3 and 10.3.5, and `K` is the open element with `closure K` the book's closed
one. -/
theorem corollary_10_3_7 {Khat : Opens 𝔼} (hΩ : IsSobolevExtensionDomainAll d Khat)
    (hb : Bornology.IsBounded (Khat : Set 𝔼)) (hc : IsPreconnected (Khat : Set 𝔼))
    {chat : 𝔼} {ρhat : ℝ} (hρhat : 0 < ρhat)
    (hballhat : Metric.closedBall chat (ρhat / 2) ⊆ Khat)
    {k m : ℕ} (hm : m ≤ k + 1) (hkd : (d : ℝ) / 2 < k + 1)
    {I : ℕ} (xhat : Fin I → 𝔼) (φhat : Fin I → 𝔼 → ℝ)
    (hx : ∀ i, xhat i ∈ closure (Khat : Set 𝔼))
    (hφ : ∀ i, MemSobolev (φhat i) m 2 Khat volume)
    (hP : ∀ q : MvPolynomial (Fin d) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ Khat, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q)
    {ι : Type*} {l : Filter ι} {𝒯 : ι → Set (Set 𝔼)} (hreg : IsRegularFamily l 𝒯)
    {H : ℝ} (hH : ∀ i, ∀ K ∈ 𝒯 i, Metric.diam K ≤ H) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ∀ K ∈ 𝒯 i, ∀ Kop : Opens 𝔼, (Kop : Set 𝔼) = K →
      ∀ (T : 𝔼 ≃L[ℝ] 𝔼) (b : 𝔼), (fun x ↦ T x + b) '' Khat = Kop →
      ∀ v : 𝔼 → ℝ, MemSobolev v (k + 1) 2 Kop volume → ContinuousOn v (closure (Kop : Set 𝔼)) →
      sobolevNorm (v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ xhat)
          (fun i ↦ φhat i ∘ fun y ↦ T.symm (y - b)) v) m 2 Kop volume
        ≤ ENNReal.ofReal (c * Metric.diam K ^ (k + 1 - m))
          * sobolevSeminorm v (k + 1) 2 Kop volume :=
  FiniteElement.sobolevNorm_sub_nodalInterp_comp_affine_le hΩ hb hc hρhat hballhat hm hkd xhat φhat
    hx hφ hP hreg hH

end Corollary1037

/-! ### Example 10.3.8 on the unit square: `Q₁` elements on parallelograms

The book's Example 10.3.8 is the linear element on a *triangle* (`example_10_3_8` below). The
unit square is an extension domain as well (Brezis's Remark 9,
`SobolevEuclidean.exists_extensionL_unitSquare`, `isSobolevExtensionDomainAll_unitSquare`), so
the estimate is instantiated here also for the `Q₁` element on it: nodes the four vertices, shape
functions the bilinear `(1 ∓ x̂₁)(1 ∓ x̂₂)` of Exercise 10.2.3 (`bilinearShape`, here on
`EuclideanSpace ℝ (Fin 2)`), local space `Q₁ ⊇ ℙ₁`, and the elements the affine images of the
square — parallelograms, of which the book's rectangles are the case of a diagonal `T_K`. -/

section Example1038Square

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- The unit square is bounded. -/
theorem isBounded_unitSquare : Bornology.IsBounded (EuclideanSpace.rect 0 1 0 1 : Set 𝔼₂) :=
  Metric.isBounded_closedBall.subset (EuclideanSpace.rect_subset_closedBall 0 1 0 1)

/-- A rectangle is convex: it is the intersection of the preimages of two open intervals under
the coordinate projections. -/
theorem convex_rect (a₁ b₁ a₂ b₂ : ℝ) :
    Convex ℝ (EuclideanSpace.rect a₁ b₁ a₂ b₂ : Set 𝔼₂) := by
  have h0 := (convex_Ioo a₁ b₁).linear_preimage
    ((EuclideanSpace.proj (0 : Fin 2) : 𝔼₂ →L[ℝ] ℝ) : 𝔼₂ →ₗ[ℝ] ℝ)
  have h1 := (convex_Ioo a₂ b₂).linear_preimage
    ((EuclideanSpace.proj (1 : Fin 2) : 𝔼₂ →L[ℝ] ℝ) : 𝔼₂ →ₗ[ℝ] ℝ)
  convert h0.inter h1 using 1
  ext x
  rw [EuclideanSpace.mem_rect]
  simp [and_assoc]

/-- **The closed rectangle lies in the closure of the open one**: a point with
`a₁ ≤ x₁ ≤ b₁`, `a₂ ≤ x₂ ≤ b₂` is the limit of the points `x + t (c − x)`, `t → 0⁺`, with `c`
the centre. -/
theorem mem_closure_rect {a₁ b₁ a₂ b₂ : ℝ} (h1 : a₁ < b₁) (h2 : a₂ < b₂) {x : 𝔼₂}
    (hx : a₁ ≤ x 0 ∧ x 0 ≤ b₁ ∧ a₂ ≤ x 1 ∧ x 1 ≤ b₂) :
    x ∈ closure (EuclideanSpace.rect a₁ b₁ a₂ b₂ : Set 𝔼₂) := by
  obtain ⟨c, hc⟩ : ∃ c : 𝔼₂, c = !₂[(a₁ + b₁) / 2, (a₂ + b₂) / 2] := ⟨_, rfl⟩
  have hc0 : c 0 = (a₁ + b₁) / 2 := by rw [hc]; rfl
  have hc1 : c 1 = (a₂ + b₂) / 2 := by rw [hc]; rfl
  have hlim : Filter.Tendsto (fun t : ℝ ↦ x + t • (c - x)) (𝓝[>] 0) (𝓝 x) := by
    have h : Filter.Tendsto (fun t : ℝ ↦ x + t • (c - x)) (𝓝 0) (𝓝 (x + (0 : ℝ) • (c - x))) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  rw [EuclideanSpace.mem_rect]
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hc0, hc1]
  obtain ⟨hx0, hx0', hx1, hx1'⟩ := hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.2 ht.2.le) (sub_nonneg.2 hx0),
      mul_pos ht.1 (by linarith : (0 : ℝ) < (a₁ + b₁) / 2 - a₁)]
  · nlinarith [mul_nonneg (sub_nonneg.2 ht.2.le) (sub_nonneg.2 hx0'),
      mul_pos ht.1 (by linarith : (0 : ℝ) < b₁ - (a₁ + b₁) / 2)]
  · nlinarith [mul_nonneg (sub_nonneg.2 ht.2.le) (sub_nonneg.2 hx1),
      mul_pos ht.1 (by linarith : (0 : ℝ) < (a₂ + b₂) / 2 - a₂)]
  · nlinarith [mul_nonneg (sub_nonneg.2 ht.2.le) (sub_nonneg.2 hx1'),
      mul_pos ht.1 (by linarith : (0 : ℝ) < b₂ - (a₂ + b₂) / 2)]

/-- The closed ball of radius `1/4` about the centre of the unit square lies in the square: an
inscribed ball of diameter `ρ̂ = 1/2`. -/
theorem closedBall_subset_unitSquare :
    Metric.closedBall (!₂[(1 : ℝ) / 2, 1 / 2] : 𝔼₂) ((1 / 2 : ℝ) / 2)
      ⊆ (EuclideanSpace.rect 0 1 0 1 : Set 𝔼₂) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  have h0 := (PiLp.norm_apply_le (x - !₂[(1 : ℝ) / 2, 1 / 2]) 0).trans hx
  have h1 := (PiLp.norm_apply_le (x - !₂[(1 : ℝ) / 2, 1 / 2]) 1).trans hx
  simp only [PiLp.sub_apply, Real.norm_eq_abs, Matrix.cons_val_zero, Matrix.cons_val_one,
    abs_le] at h0 h1
  rw [EuclideanSpace.mem_rect]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h0.1, h0.2, h1.1, h1.2]

/-- **The four vertices of the unit square**, the nodes of the `Q₁` element, in the order of
`bilinearNode`. -/
noncomputable def q1Node : Fin 4 → 𝔼₂ := ![!₂[0, 0], !₂[1, 0], !₂[0, 1], !₂[1, 1]]

/-- **The bilinear shape functions** `(1 − x̂₁)(1 − x̂₂)`, `x̂₁(1 − x̂₂)`, `(1 − x̂₁)x̂₂`, `x̂₁x̂₂`
of the `Q₁` element on the unit square (`bilinearShape` of Exercise 10.2.3, on `ℝ²` as a
Euclidean space). -/
noncomputable def q1Shape : Fin 4 → 𝔼₂ → ℝ :=
  ![fun x ↦ (1 - x 0) * (1 - x 1), fun x ↦ x 0 * (1 - x 1), fun x ↦ (1 - x 0) * x 1,
    fun x ↦ x 0 * x 1]

/-- The bilinear shape functions are dual to the vertices. -/
theorem q1Shape_isNodalBasis : Approximation.IsNodalBasis q1Node q1Shape where
  eval_self i := by fin_cases i <;> simp [q1Node, q1Shape]
  eval_of_ne i j hij := by
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | simp [q1Node, q1Shape]

/-- The vertices lie in the closure of the unit square. -/
theorem q1Node_mem_closure (i : Fin 4) :
    q1Node i ∈ closure (EuclideanSpace.rect 0 1 0 1 : Set 𝔼₂) := by
  refine mem_closure_rect zero_lt_one zero_lt_one ?_
  fin_cases i <;> simp [q1Node]

/-- The bilinear shape functions are smooth. -/
theorem contDiff_q1Shape (i : Fin 4) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (q1Shape i) := by
  have h0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : 𝔼₂ ↦ x 0 :=
    (EuclideanSpace.proj (0 : Fin 2) : 𝔼₂ →L[ℝ] ℝ).contDiff
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : 𝔼₂ ↦ x 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : 𝔼₂ →L[ℝ] ℝ).contDiff
  fin_cases i
  · exact (contDiff_const.sub h0).mul (contDiff_const.sub h1)
  · exact h0.mul (contDiff_const.sub h1)
  · exact (contDiff_const.sub h0).mul h1
  · exact h0.mul h1

/-- The bilinear shape functions lie in `H^m` of the unit square for every `m`. -/
theorem memSobolev_q1Shape (m : ℕ) (i : Fin 4) :
    MemSobolev (q1Shape i) m 2 (EuclideanSpace.rect 0 1 0 1) volume :=
  ((contDiff_q1Shape i).of_le (by simp)).memSobolev_of_isBounded isBounded_unitSquare 2

/-- **`Q₁` interpolation reproduces `ℙ₁`**: the polynomial invariance (10.3.4) of the `Q₁`
element at `k = 1`. A polynomial of total degree at most `1` is `c₀ + c₁ x̂₁ + c₂ x̂₂`, and the
bilinear interpolant reproduces `1`, `x̂₁` and `x̂₂`, everywhere. -/
theorem nodalInterp_q1_eval (q : MvPolynomial (Fin 2) ℝ) (hq : q.totalDegree ≤ 1) (x : 𝔼₂) :
    Approximation.nodalInterp q1Node q1Shape (fun y : 𝔼₂ ↦ MvPolynomial.eval (fun i ↦ y i) q) x
      = MvPolynomial.eval (fun i ↦ x i) q := by
  have key : ∀ d ∈ q.support,
      ∑ i, q1Shape i x * (q.coeff d * ∏ j, q1Node i j ^ d j)
        = q.coeff d * ∏ j, x j ^ d j := by
    intro d hd
    have hdeg : d 0 + d 1 ≤ 1 := by
      have h := (MvPolynomial.le_totalDegree hd).trans hq
      rwa [Finsupp.sum_fintype _ _ fun _ ↦ rfl, Fin.sum_univ_two] at h
    simp only [Fin.prod_univ_two, Fin.sum_univ_four]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (le_trans (Nat.le_add_right _ _) hdeg) with h0 | h0
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (le_trans (Nat.le_add_left _ _) hdeg) with h1 | h1
      · simp [q1Node, q1Shape, h0, h1]
        ring
      · simp [q1Node, q1Shape, h0, h1]
        ring
    · have h1 : d 1 = 0 := by omega
      simp [q1Node, q1Shape, h0, h1]
      ring
  calc Approximation.nodalInterp q1Node q1Shape
        (fun y : 𝔼₂ ↦ MvPolynomial.eval (fun i ↦ y i) q) x
      = ∑ i, q1Shape i x * ∑ d ∈ q.support,
          q.coeff d * ∏ j, q1Node i j ^ d j := by
        simp only [Approximation.nodalInterp_apply, smul_eq_mul, MvPolynomial.eval_eq']
    _ = ∑ d ∈ q.support, ∑ i, q1Shape i x * (q.coeff d * ∏ j, q1Node i j ^ d j) := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ d ∈ q.support, q.coeff d * ∏ j, x j ^ d j := Finset.sum_congr rfl key
    _ = MvPolynomial.eval (fun i ↦ x i) q := (MvPolynomial.eval_eq' _ _).symm

/-- **Example 10.3.8 on the unit square: the `Q₁` element on a regular family of
parallelograms.** For a regular family `{𝒯_h}` (Definition 10.3.6) of elements of diameter at
most `H`, each the affine image `K = F_K(K̂)` of the unit square `K̂ = (0,1)²`, with the four
vertices `F_K(x̂ᵢ)` as nodes and the transported bilinear shape functions
`φ̂ᵢ ∘ F_K⁻¹` — the local space `Q₁(K̂) ⊇ ℙ₁(K̂)` of the remark after Theorem 10.3.5 — the
estimate (10.3.11) holds for `m = 0, 1, 2`:

  `‖v − Π_K v‖_{m,K} ≤ c h_K^{2−m} |v|_{2,K}`  for every `v ∈ H²(K)`.

This is Corollary 10.3.7 at `k = 1`, `d = 2` (so `k + 1 = 2 > d/2 = 1`), the reference element
being an extension domain (`isSobolevExtensionDomainAll_unitSquare`), bounded, convex, with the
ball of radius `1/4` about its centre inscribed, the vertices in its closure, the shape
functions smooth, and `Q₁ ⊇ ℙ₁` (`nodalInterp_q1_eval`). The book's example is the linear
element on triangles, `example_10_3_8`. -/
theorem example_10_3_8_square {m : ℕ} (hm : m ≤ 2) {ι : Type*} {l : Filter ι}
    {𝒯 : ι → Set (Set 𝔼₂)} (hreg : IsRegularFamily l 𝒯) {H : ℝ}
    (hH : ∀ i, ∀ K ∈ 𝒯 i, Metric.diam K ≤ H) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ∀ K ∈ 𝒯 i, ∀ Kop : Opens 𝔼₂, (Kop : Set 𝔼₂) = K →
      ∀ (T : 𝔼₂ ≃L[ℝ] 𝔼₂) (b : 𝔼₂), (fun x ↦ T x + b) '' EuclideanSpace.rect 0 1 0 1 = Kop →
      ∀ v : 𝔼₂ → ℝ, MemSobolev v 2 2 Kop volume → ContinuousOn v (closure (Kop : Set 𝔼₂)) →
      sobolevNorm (v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ q1Node)
          (fun i ↦ q1Shape i ∘ fun y ↦ T.symm (y - b)) v) m 2 Kop volume
        ≤ ENNReal.ofReal (c * Metric.diam K ^ (2 - m)) * sobolevSeminorm v 2 2 Kop volume :=
  corollary_10_3_7 (k := 1) isSobolevExtensionDomainAll_unitSquare isBounded_unitSquare
    (convex_rect 0 1 0 1).isPreconnected one_half_pos closedBall_subset_unitSquare hm
    (by norm_num) q1Node q1Shape q1Node_mem_closure (memSobolev_q1Shape m)
    (fun q hq x _ ↦ nodalInterp_q1_eval q hq x) hreg hH

end Example1038Square

/-! ### Example 10.3.8: the linear element on triangles

The book's example: the reference element is the reference triangle
`K̂ = {x̂₁, x̂₂ > 0, x̂₁ + x̂₂ < 1}` (`EuclideanSpace.referenceTriangle`), the nodes its three
vertices, the shape functions the barycentric coordinates `1 − x̂₁ − x̂₂, x̂₁, x̂₂` (Example
10.3.2, `EuclideanSpace.baryCoord`), the local space `X̂ = ℙ₁(K̂)`, and the elements the affine
images of `K̂` — every nondegenerate triangle. The reference triangle is a Sobolev extension
domain for every exponent (`isSobolevExtensionDomainAll_referenceTriangle`,
`Numlib/Analysis/Sobolev/Simplex.lean`: two reflections and an affine change of variables to the
unit square), so Corollary 10.3.7 applies to it verbatim. -/

section Example1038

open MeasureTheory Set TopologicalSpace EuclideanSpace
open scoped ENNReal NNReal Topology

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- **The barycentric coordinates are nodal for the vertices of the reference triangle**: the
`P₁` element, Example 10.3.2 with the explicit coordinates of `EuclideanSpace.baryCoord`
(the backbone's `EuclideanSpace.isNodalBasis_baryCoord`). -/
theorem baryCoord_isNodalBasis :
    Approximation.IsNodalBasis referenceTriangleVertex baryCoord :=
  isNodalBasis_baryCoord

/-- The barycentric coordinates lie in `H^m` of the reference triangle for every `m`. -/
theorem memSobolev_baryCoord (m : ℕ) (i : Fin 3) :
    MemSobolev (baryCoord i) m 2 referenceTriangle volume :=
  ((contDiff_baryCoord i).of_le (by simp)).memSobolev_of_isBounded isBounded_referenceTriangle 2

/-- **`P₁` interpolation reproduces `ℙ₁`**: the polynomial invariance (10.3.4) of the linear
element at `k = 1`. A polynomial of total degree at most `1` is `c₀ + c₁ x̂₁ + c₂ x̂₂`, and the
barycentric interpolant reproduces `1`, `x̂₁` and `x̂₂`, everywhere — the explicit form of
`nodalInterp_coord_affineMap` on the reference triangle. -/
theorem nodalInterp_baryCoord_eval (q : MvPolynomial (Fin 2) ℝ) (hq : q.totalDegree ≤ 1)
    (x : 𝔼₂) :
    Approximation.nodalInterp referenceTriangleVertex baryCoord
      (fun y : 𝔼₂ ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q := by
  have key : ∀ d ∈ q.support,
      ∑ i, baryCoord i x * (q.coeff d * ∏ j, referenceTriangleVertex i j ^ d j)
        = q.coeff d * ∏ j, x j ^ d j := by
    intro d hd
    have hdeg : d 0 + d 1 ≤ 1 := by
      have h := (MvPolynomial.le_totalDegree hd).trans hq
      rwa [Finsupp.sum_fintype _ _ fun _ ↦ rfl, Fin.sum_univ_two] at h
    simp only [Fin.prod_univ_two, Fin.sum_univ_three]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (le_trans (Nat.le_add_right _ _) hdeg) with h0 | h0
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (le_trans (Nat.le_add_left _ _) hdeg) with h1 | h1
      · simp [referenceTriangleVertex, baryCoord, h0, h1]
        ring
      · simp [referenceTriangleVertex, baryCoord, h0, h1]
        ring
    · have h1 : d 1 = 0 := by omega
      simp [referenceTriangleVertex, baryCoord, h0, h1]
      ring
  calc Approximation.nodalInterp referenceTriangleVertex baryCoord
        (fun y : 𝔼₂ ↦ MvPolynomial.eval (fun i ↦ y i) q) x
      = ∑ i, baryCoord i x * ∑ d ∈ q.support,
          q.coeff d * ∏ j, referenceTriangleVertex i j ^ d j := by
        simp only [Approximation.nodalInterp_apply, smul_eq_mul, MvPolynomial.eval_eq']
    _ = ∑ d ∈ q.support, ∑ i, baryCoord i x * (q.coeff d * ∏ j,
          referenceTriangleVertex i j ^ d j) := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ d ∈ q.support, q.coeff d * ∏ j, x j ^ d j := Finset.sum_congr rfl key
    _ = MvPolynomial.eval (fun i ↦ x i) q := (MvPolynomial.eval_eq' _ _).symm

/-- **Example 10.3.8: the linear element on a regular family of triangles.** Let `K` be a
triangle in a regular family of affine finite elements (Definition 10.3.6, `IsRegularFamily`,
with the elements of diameter at most `H`), each the affine image `K = F_K(K̂)` of the reference
triangle `K̂`, with the three vertices `F_K(x̂ᵢ)` as nodes, the transported barycentric coordinates
`λ̂ᵢ ∘ F_K⁻¹` as shape functions and the local space `X_K = ℙ₁(K)`. Then for every `v ∈ H²(K)`
the estimate (10.3.11) holds,

  `‖v − Π_K v‖_{m,K} ≤ c h_K^{2−m} |v|_{2,K}`,

for `m = 0, 1` (and `m = 2`). This is Corollary 10.3.7 (the estimate (10.3.10)) at `k = 1`,
`d = 2` (so `k + 1 = 2 > d/2 = 1`), the reference triangle being a Sobolev extension domain
(`isSobolevExtensionDomainAll_referenceTriangle`, the backbone's reading of "Lipschitz"), bounded,
convex, with the ball of radius `1/8` about `(1/4, 1/4)` inscribed, the vertices in its closure,
the barycentric coordinates smooth and nodal (Example 10.3.2), and `ℙ₁(K̂) ⊆ X̂`
(`nodalInterp_baryCoord_eval`). `v` is read on its continuous representative up to the boundary
and `K` is the open element, as in Corollary 10.3.7. -/
theorem example_10_3_8 {m : ℕ} (hm : m ≤ 2) {ι : Type*} {l : Filter ι}
    {𝒯 : ι → Set (Set 𝔼₂)} (hreg : IsRegularFamily l 𝒯) {H : ℝ}
    (hH : ∀ i, ∀ K ∈ 𝒯 i, Metric.diam K ≤ H) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ∀ K ∈ 𝒯 i, ∀ Kop : Opens 𝔼₂, (Kop : Set 𝔼₂) = K →
      ∀ (T : 𝔼₂ ≃L[ℝ] 𝔼₂) (b : 𝔼₂), (fun x ↦ T x + b) '' referenceTriangle = Kop →
      ∀ v : 𝔼₂ → ℝ, MemSobolev v 2 2 Kop volume → ContinuousOn v (closure (Kop : Set 𝔼₂)) →
      sobolevNorm (v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ referenceTriangleVertex)
          (fun i ↦ baryCoord i ∘ fun y ↦ T.symm (y - b)) v) m 2 Kop volume
        ≤ ENNReal.ofReal (c * Metric.diam K ^ (2 - m)) * sobolevSeminorm v 2 2 Kop volume :=
  corollary_10_3_7 (k := 1) isSobolevExtensionDomainAll_referenceTriangle
    isBounded_referenceTriangle convex_referenceTriangle.isPreconnected
    (by norm_num : (0 : ℝ) < 1 / 4) closedBall_subset_referenceTriangle hm (by norm_num)
    referenceTriangleVertex baryCoord referenceTriangleVertex_mem_closure (memSobolev_baryCoord m)
    (fun q hq x _ ↦ nodalInterp_baryCoord_eval q hq x) hreg hH

end Example1038

/-! ### Theorem 10.3.9: the global interpolation error on a triangulation

The triangulation is `Triangulation Ω` (`Numlib/Geometry/Triangulation.lean`): a finite set of
nondegenerate triangles with disjoint interiors, whose closures cover `Ω`, meeting edge to
edge. Its elements are the affine images `F_K(K̂)` of the reference triangle
(`Triangulation.image_referenceTriangle`), the local interpolant `Π_K v` is
`Triangulation.localInterp` ((10.3.2), with the transported nodes and shape functions of
Corollary 10.3.7) and the global interpolant `Π_h v` is `Triangulation.globalInterp`, glued
from the local ones (§10.3.4, `Π_h v|_K = Π_K v`). The element type is assumed *conforming*
(`Triangulation.IsConformingElement`: the local interpolants agree on the common edges, the
book's standing assumption `X_h ⊆ C(Ω̄)` of §10.2.3, which Example 10.2.3 verifies for the
linear element); then `Π_h v` is continuous on `Ω̄` and lies in `H¹(Ω)`
(`Triangulation.memSobolev_globalInterp`, through the weak derivative of a continuous
piecewise-`C¹` function, `Numlib/Analysis/Sobolev/Triangulation.lean`). -/

section Theorem1039

open MeasureTheory Set TopologicalSpace EuclideanSpace
open scoped ENNReal NNReal Topology

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- The mesh parameter of a triangulation, read as a collection of elements, is its
`Triangulation.meshSize`. -/
theorem meshSize_range_K {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) :
    meshSize (Set.range 𝒯.K) = 𝒯.meshSize :=
  𝒯.meshSize_eq_sSup_image.symm

/-- **Definition 10.3.6 for a family of triangulations**: the family is regular exactly when
(a) some `σ` bounds `h_K / ρ_K` for every element of every triangulation — every element
contains a ball of radius `r` with `h_K ≤ σ (2 r)` — and (b) the mesh parameters
`Triangulation.meshSize` tend to `0`. -/
theorem isRegularFamily_iff {Ω : Opens 𝔼₂} {ι : Type*} (l : Filter ι) (𝒯 : ι → Triangulation Ω) :
    IsRegularFamily l (fun i ↦ Set.range (𝒯 i).K) ↔
      (∃ σ : ℝ, ∀ i, ∀ T : (𝒯 i).elems, ∃ (c : 𝔼₂) (r : ℝ), 0 < r ∧
        Metric.closedBall c r ⊆ (𝒯 i).K T ∧ Metric.diam ((𝒯 i).K T) ≤ σ * (2 * r)) ∧
      Tendsto (fun i ↦ (𝒯 i).meshSize) l (𝓝 0) :=
  FiniteElement.isRegularFamily_range_K_iff l 𝒯

/-- **Theorem 10.3.9** (the global interpolation error, (10.3.13)). Let `{𝒯_h}` be a regular
family of triangulations of a plane domain `Ω` (Definition 10.3.6, `IsRegularFamily`, with mesh
parameters at most `H`), and let the reference element be the reference triangle with nodes
`x̂ᵢ ∈ K̂̄`, `C¹` shape functions `φ̂ᵢ` and the polynomial invariance `ℙ_k(K̂) ⊆ X̂`, `k ≥ 1`, the
element being conforming on every triangulation of the family. Then there is a constant `c`,
independent of `h`, such that for every `v ∈ H^{k+1}(Ω)` (read on its continuous representative
up to the boundary, as in Corollary 10.3.7) and `m = 0, 1`,

  `‖v − Π_h v‖_{m,Ω} ≤ c h^{k+1−m} |v|_{k+1,Ω}`.

The proof is the book's: `‖v − Π_h v‖²_{m,Ω} = ∑_K ‖v − Π_K v‖²_{m,K}`
(`Triangulation.sobolevNorm_rpow_eq_sum`, the additivity of the tensor norm over the elements,
which needs `v − Π_h v ∈ H^m(Ω)` — for `m = 1` the conformity), each term is bounded by
Corollary 10.3.7 with `h_K ≤ h`, and `∑_K |v|²_{k+1,K} = |v|²_{k+1,Ω}`. The hypothesis
`k + 1 > d/2` of Corollary 10.3.7 is `k ≥ 1` in the plane. -/
theorem theorem_10_3_9 {k m : ℕ} (hm : m ≤ 1) (hk : 1 ≤ k)
    {I : ℕ} (xhat : Fin I → 𝔼₂) (φhat : Fin I → 𝔼₂ → ℝ)
    (hx : ∀ i, xhat i ∈ closure (referenceTriangle : Set 𝔼₂))
    (hφ : ∀ i, ContDiff ℝ 1 (φhat i))
    (hP : ∀ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ referenceTriangle, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q)
    {Ω : Opens 𝔼₂} {ι : Type*} {l : Filter ι} {𝒯 : ι → Triangulation Ω}
    (hreg : IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H)
    (hconf : ∀ i, (𝒯 i).IsConformingElement xhat φhat) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ∀ v : 𝔼₂ → ℝ, MemSobolev v (k + 1) 2 Ω volume →
      ContinuousOn v (closure (Ω : Set 𝔼₂)) →
      sobolevNorm (v - (𝒯 i).globalInterp xhat φhat v) m 2 Ω volume
        ≤ ENNReal.ofReal (c * (𝒯 i).meshSize ^ (k + 1 - m))
          * sobolevSeminorm v (k + 1) 2 Ω volume :=
  Triangulation.sobolevNorm_sub_globalInterp_le hm hk xhat φhat hx hφ hP hreg hH hconf

/-- **Theorem 10.3.9 for the linear element** of Example 10.3.8: on a regular family of
triangulations with mesh parameters at most `H`, the continuous piecewise linear interpolant
`Π_h v` at the vertices satisfies `‖v − Π_h v‖_{m,Ω} ≤ c h^{2−m} |v|_{2,Ω}` for every
`v ∈ H²(Ω)` and `m = 0, 1`. The linear element is conforming on every triangulation
(`Triangulation.isConformingElement_linear`, Example 10.2.3), and `ℙ₁(K̂) ⊆ X̂`
(`nodalInterp_baryCoord_eval`). -/
theorem theorem_10_3_9_linear {m : ℕ} (hm : m ≤ 1) {Ω : Opens 𝔼₂} {ι : Type*} {l : Filter ι}
    {𝒯 : ι → Triangulation Ω} (hreg : IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ∀ v : 𝔼₂ → ℝ, MemSobolev v 2 2 Ω volume →
      ContinuousOn v (closure (Ω : Set 𝔼₂)) →
      sobolevNorm (v - (𝒯 i).globalInterp referenceTriangleVertex baryCoord v) m 2 Ω volume
        ≤ ENNReal.ofReal (c * (𝒯 i).meshSize ^ (2 - m)) * sobolevSeminorm v 2 2 Ω volume :=
  theorem_10_3_9 (k := 1) hm le_rfl referenceTriangleVertex baryCoord
    referenceTriangleVertex_mem_closure (fun i ↦ (contDiff_baryCoord i).of_le (by simp))
    (fun q hq x _ ↦ nodalInterp_baryCoord_eval q hq x) hreg hH
    fun i ↦ (𝒯 i).isConformingElement_linear

/-- **Theorem 10.3.9 for the `ℙ_k` Lagrange element** on the principal lattice `N̂_k` (10.2.24) —
the book's "affine-equivalent finite element spaces of piecewise polynomials of degree at most
`k`": on a regular family of triangulations with mesh parameters at most `H`, the continuous
piecewise-`ℙ_k` interpolant `Π_h v` at the lattice nodes satisfies
`‖v − Π_h v‖_{m,Ω} ≤ c h^{k+1−m} |v|_{k+1,Ω}` for every `v ∈ H^{k+1}(Ω)`, `k ≥ 1`, `m = 0, 1`.
The element is the backbone's `LagrangeElement.node`, `LagrangeElement.shape`, conforming on every
triangulation and reproducing `ℙ_k` (Proposition 10.2.1); the estimate is
`LagrangeElement.sobolevNorm_sub_globalInterp_le`. -/
theorem theorem_10_3_9_lattice {k m : ℕ} (hm : m ≤ 1) (hk : 1 ≤ k) {Ω : Opens 𝔼₂} {ι : Type*}
    {l : Filter ι} {𝒯 : ι → Triangulation Ω} (hreg : IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ∀ v : 𝔼₂ → ℝ, MemSobolev v (k + 1) 2 Ω volume →
      ContinuousOn v (closure (Ω : Set 𝔼₂)) →
      sobolevNorm (v - (𝒯 i).globalInterp (LagrangeElement.node k) (LagrangeElement.shape k) v)
          m 2 Ω volume
        ≤ ENNReal.ofReal (c * (𝒯 i).meshSize ^ (k + 1 - m))
          * sobolevSeminorm v (k + 1) 2 Ω volume :=
  LagrangeElement.sobolevNorm_sub_globalInterp_le hm hk hreg hH

end Theorem1039

end AtkinsonHan.Chapter10
