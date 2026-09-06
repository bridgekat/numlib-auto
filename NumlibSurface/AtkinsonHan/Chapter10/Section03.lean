import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Numlib.Approximation.NodalInterpolation

/-!
# Atkinson–Han §10.3: local interpolation and regular families

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §10.3.

The section estimates the finite element interpolation error on an element by transporting the
problem to the reference element. The estimates themselves are Sobolev statements and are out of
reach, but the two results this file holds are not:

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

## Main results

* `theorem_10_3_1` — `Π̂ (v ∘ F_K) = (Π_K v) ∘ F_K`.
* `example_10_3_2` — the linear element: the barycentric coordinates of a simplex are nodal for its
  vertices, so `Π_K` is the interpolant through the vertex values, and
  `nodalInterp_coord_affineMap` says that it reproduces affine functions.

## Deviations from the book

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
not for a family of triangulations.

## Not formalized here

Theorems 10.3.3, 10.3.4, 10.3.5, Corollary 10.3.7 and Theorem 10.3.9, the interpolation error
estimates: they are inequalities between `H^m` seminorms and rest on the Deny–Lions estimate
(the Bramble–Hilbert lemma, Exercises 10.3.5 and 10.3.6), on the transformation of a Sobolev
seminorm under an affine map, and — for the global bound — on the additivity of the `H^m` norm over
a triangulation. Mathlib has no weak derivative on an open set of `ℝᵈ`, hence no `H^m(K)`. The same
obstruction rules out Exercises 10.3.1, 10.3.2, 10.3.4 and 10.3.7. Exercise 10.3.3 (`h_K / ρ_K`
bounded if and only if the minimal angles are bounded below) is Sobolev-free — it is plane geometry
relating the diameter of a triangle, the diameter of its inscribed circle and its smallest angle —
and is planned but not written: Mathlib has a circumradius for a simplex but no inradius, so the
inscribed circle has to be built first.
-/

open Filter Metric Topology

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

end AtkinsonHan.Chapter10
