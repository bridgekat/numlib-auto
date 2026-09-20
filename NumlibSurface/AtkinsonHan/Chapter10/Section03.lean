import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Numlib.Analysis.Sobolev.Affine
import Numlib.Analysis.Sobolev.SeminormCompare
import Numlib.Approximation.NodalInterpolation
import Numlib.Geometry.Euclidean.TriangleShape
import NumlibSurface.AtkinsonHan.Chapter07.Section03
import NumlibSurface.AtkinsonHan.Chapter10.Section02

/-!
# Atkinson–Han §10.3: local interpolation and regular families

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §10.3.

The section estimates the finite element interpolation error on an element by transporting the
problem to the reference element. Everything is here except the global estimate over a
triangulation: Theorem 10.3.1 (the transport of the interpolant), Theorem 10.3.3 (the estimate on
the reference element), Theorem 10.3.4 (the affine change of variables in `H^m`), Theorem 10.3.5
(the local estimate), Definition 10.3.6 and Corollary 10.3.7 (regular families), and Example
10.3.8 in its unit-square form. Two of these are not Sobolev statements at all:

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
* `example_10_3_8_square` — Corollary 10.3.7 for the `Q₁` element on the affine images of the
  unit square, `m ≤ 2`: `‖v − Π_K v‖_{m,K} ≤ c h_K^{2−m} |v|_{2,K}`.
* `example_10_3_2` — the linear element: the barycentric coordinates of a simplex are nodal for its
  vertices, so `Π_K` is the interpolant through the vertex values, and
  `nodalInterp_coord_affineMap` says that it reproduces affine functions.

## Deviations from the book

The book's reference element is a triangle, a Lipschitz domain, and its Theorem 10.3.3 rests on
Corollary 7.3.18 (Bramble–Hilbert) and the embedding `H^{k+1}(K̂) ↪ C(K̂)` on it. The backbone
proves both on Sobolev extension domains (`IsSobolevExtensionDomainAll`,
`Numlib/Analysis/Sobolev/{EmbeddingDomain,DenyLions}.lean`), whose instances are the `C¹` chart
domains and the unit square (`SobolevEuclidean.exists_extensionL_unitSquare`); no Lipschitz
extension operator is formalized, so the reference simplex is not known to be one. The
estimates are therefore stated for a reference element that is an extension domain *as a
hypothesis*, which the unit square satisfies (`isSobolevExtensionDomainAll_unitSquare`) and the
reference triangle will once a simplex extension operator exists; Example 10.3.8 on triangles
stays open, its `Q₁` counterpart on the square is `example_10_3_8_square`. The dimension is
general and the hypothesis `k + 1 > d/2` is carried explicitly (the book's `k > 0` is its case
`d = 2`).

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

Theorem 10.3.9, the global estimate `‖v − Π_h v‖_{m,Ω} ≤ c h^{k+1−m} |v|_{k+1,Ω}`: it is Corollary
10.3.7 summed over the elements of a triangulation of `Ω`, and needs the triangulation scaffold —
a finite family of elements with disjoint interiors covering `Ω̄`, the global interpolant `Π_h`
glued from the `Π_K`, and the additivity `‖w‖²_{m,Ω} = ∑_K ‖w‖²_{m,K}` of the tensor norm over
the elements — which does not exist (`notes/frontier.md`, blocker 11). Example 10.3.8 on
triangles (see above). Exercises 10.3.1, 10.3.2, 10.3.4 and 10.3.7 are not nodes; Exercise 10.3.3
(`h_K / ρ_K` bounded if and only if the minimal angles are bounded below) is Sobolev-free, and is
`exercise_10_3_3` below.
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

/-- The constants of (10.3.5)–(10.3.6) in `ℝ≥0∞`: `ofReal (a^m) * ofReal |x| ^ (1/2)` is
`ofReal (a^m |x|^{1/2})`. -/
theorem ofReal_pow_mul_ofReal_abs_rpow {a : ℝ} (ha : 0 ≤ a) (m : ℕ) (x : ℝ) :
    ENNReal.ofReal (a ^ m) * ENNReal.ofReal |x| ^ (1 / (2 : ℝ≥0∞)).toReal
      = ENNReal.ofReal (a ^ m * |x| ^ (1 / 2 : ℝ)) := by
  have h2 : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by norm_num
  rw [h2, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
    ← ENNReal.ofReal_mul (pow_nonneg ha m)]

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
  -- `K̂` is the preimage of `K`
  have hKhat : Khat = affinePreimage T b K := (affinePreimage_eq_of_image_eq T b hK).symm
  subst hKhat
  refine ⟨memSobolev_comp_affine_iff T b, fun h ↦ ?_, fun h ↦ ?_⟩
  · refine (sobolevSeminorm_comp_affine_le T b h).trans (le_of_eq ?_)
    rw [← mul_assoc, ofReal_pow_mul_ofReal_abs_rpow (norm_nonneg _), abs_inv,
      Real.inv_rpow (abs_nonneg _), ← Real.rpow_neg (abs_nonneg _)]
  · have h' : MemSobolev (fun x ↦ v (T x + b)) m 2 (affinePreimage T b K) volume :=
      memSobolev_comp_affine T b h
    have key := sobolevSeminorm_comp_affine_le T.symm (-T.symm b) h'
    rw [affinePreimage_symm] at key
    have hfun : (fun y ↦ v (T (T.symm y + -T.symm b) + b)) = v := by
      funext y
      simp
    rw [hfun] at key
    refine key.trans (le_of_eq ?_)
    rw [← mul_assoc, ofReal_pow_mul_ofReal_abs_rpow (norm_nonneg _),
      ContinuousLinearEquiv.det_symm_eq_inv, inv_inv]

end Theorem1034

/-! ### Theorem 10.3.3: the interpolation error on the reference element -/

section Theorem1033

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

variable {d : ℕ}

/-- (General.) A function continuous on `closure Ω` that agrees almost everywhere on the open set
`Ω` with a continuous function agrees with it on `closure Ω`. -/
theorem eqOn_closure_of_ae_eq_of_continuousOn {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [TopologicalSpace Y] [T2Space Y]
    {μ : Measure X} [μ.IsOpenPosMeasure] {Ω : Opens X} {v u : X → Y}
    (h : v =ᵐ[μ.restrict (Ω : Set X)] u) (hv : ContinuousOn v (closure (Ω : Set X)))
    (hu : Continuous u) : EqOn v u (closure (Ω : Set X)) :=
  (Measure.eqOn_open_of_ae_eq h Ω.isOpen (hv.mono subset_closure) hu.continuousOn).of_subset_closure
    hv hu.continuousOn subset_closure subset_rfl

/-- The nodal interpolant (10.3.1) as a linear combination of the shape functions:
`Π̂ v̂ = ∑ᵢ v̂(x̂ᵢ) φ̂ᵢ`. -/
theorem nodalInterp_eq_sum_smul {I : ℕ} {α : Type*} (x : Fin I → α) (φ : Fin I → α → ℝ)
    (v : α → ℝ) : Approximation.nodalInterp x φ v = ∑ i, v (x i) • φ i := by
  funext y
  simp [Approximation.nodalInterp_apply, Finset.sum_apply, mul_comm]

variable {Ω : Opens (EuclideanSpace ℝ (Fin d))}

/-- The nodal interpolant of any function lies in `W^{m,p}(Ω)` when the shape functions do. -/
theorem memSobolev_nodalInterp {I : ℕ} {x : Fin I → EuclideanSpace ℝ (Fin d)}
    {φ : Fin I → EuclideanSpace ℝ (Fin d) → ℝ} {m : ℕ} {p : ℝ≥0∞}
    (hφ : ∀ i, MemSobolev (φ i) m p Ω volume) (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    MemSobolev (Approximation.nodalInterp x φ v) m p Ω volume := by
  rw [nodalInterp_eq_sum_smul]
  exact MemSobolev.finsetSum fun i _ ↦ (hφ i).const_smul _

/-- The Sobolev seminorm of a nodal interpolant is bounded by the nodal values times the
seminorms of the shape functions: `|Π̂ v̂|_{m,K̂} ≤ ∑ᵢ |v̂(x̂ᵢ)| |φ̂ᵢ|_{m,K̂}`. -/
theorem sobolevSeminorm_nodalInterp_le {I : ℕ} {x : Fin I → EuclideanSpace ℝ (Fin d)}
    {φ : Fin I → EuclideanSpace ℝ (Fin d) → ℝ} {m : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hφ : ∀ i, MemSobolev (φ i) m p Ω volume) (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    sobolevSeminorm (Approximation.nodalInterp x φ v) m p Ω volume
      ≤ ∑ i, ‖v (x i)‖ₑ * sobolevSeminorm (φ i) m p Ω volume := by
  rw [nodalInterp_eq_sum_smul]
  exact sobolevSeminorm_sum_smul_le hp (fun i _ ↦ hφ i) _

/-- **The interpolation operator is bounded**, the first display of the proof of Theorem 10.3.3:
for a bounded linear `ι : V → C(K)` and nodes `yᵢ ∈ K`,
`|∑ᵢ (ι w)(yᵢ) φᵢ|_{m,Ω} ≤ ‖ι‖ ‖w‖ ∑ᵢ |φᵢ|_{m,Ω}`. -/
theorem sobolevSeminorm_sum_apply_smul_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K] (ι : V →L[ℝ] C(K, ℝ)) {I : ℕ}
    (y : Fin I → K) {φ : Fin I → EuclideanSpace ℝ (Fin d) → ℝ} {m : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hφ : ∀ i, MemSobolev (φ i) m p Ω volume) (w : V) :
    sobolevSeminorm (∑ i, (ι w (y i)) • φ i) m p Ω volume
      ≤ ENNReal.ofReal (‖ι‖ * ‖w‖ * ∑ i, (sobolevSeminorm (φ i) m p Ω volume).toReal) := by
  refine (sobolevSeminorm_sum_smul_le hp (fun i _ ↦ hφ i) _).trans ?_
  calc ∑ i, ‖ι w (y i)‖ₑ * sobolevSeminorm (φ i) m p Ω volume
      ≤ ∑ i, ENNReal.ofReal (‖ι‖ * ‖w‖) * sobolevSeminorm (φ i) m p Ω volume := by
        gcongr with i
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal
          ((ContinuousMap.norm_coe_le_norm _ _).trans (ι.le_opNorm w))
    _ = ENNReal.ofReal (‖ι‖ * ‖w‖) * ∑ i, sobolevSeminorm (φ i) m p Ω volume := by
        rw [Finset.mul_sum]
    _ = _ := by
        rw [ENNReal.ofReal_mul (p := ‖ι‖ * ‖w‖) (by positivity),
          ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ ENNReal.toReal_nonneg]
        congr 1
        exact Finset.sum_congr rfl fun i _ ↦
          (ENNReal.ofReal_toReal (hφ i).sobolevSeminorm_ne_top).symm

/-- The polynomial function `x ↦ q(x)` on `ℝ^d` is continuous. -/
theorem continuous_eval_coords (q : MvPolynomial (Fin d) ℝ) :
    Continuous fun x : EuclideanSpace ℝ (Fin d) ↦ MvPolynomial.eval (fun i ↦ x i) q := by
  have : (fun x : EuclideanSpace ℝ (Fin d) ↦ MvPolynomial.eval (fun i ↦ x i) q)
      = MvPolynomial.evalBasis (EuclideanSpace.basisFun (Fin d) ℝ).toBasis q := by
    funext x
    exact (MvPolynomial.evalBasis_basisFun q x).symm
  rw [this]
  exact (MvPolynomial.contDiff_evalBasis _ q).continuous

local notation "𝟚" => ((2 : ℝ≥0) : ℝ≥0∞)

/-- **The polynomial invariance (10.3.4) on `ℙ_k(K̂) ⊆ H^{k+1}(K̂)`**: if the nodal interpolation
`Π̂` reproduces every polynomial of degree at most `k` on `K̂`, and `ι : H^{k+1}(K̂) → C(K)` sends
each element to (the restriction to `K ⊇ K̂` of) a continuous representative, then for
`q ∈ ℙ_k(K̂)` the interpolant `∑ᵢ (ι q)(x̂ᵢ) φ̂ᵢ` of that representative is `q` almost everywhere
on `K̂`. The nodes may lie on the boundary of `K̂`, which is why the representative is read on
`K ⊇ closure K̂`. -/
theorem sum_apply_smul_ae_eq_fn_of_mem_polynomialSubmodule
    {Khat : Opens (EuclideanSpace ℝ (Fin d))}
    (hb : Bornology.IsBounded (Khat : Set (EuclideanSpace ℝ (Fin d)))) {k : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
    (ι : SobolevEuclidean d (k + 1) 𝟚 Khat →L[ℝ] C(K, ℝ))
    (hι : ∀ u, ∃ ut : EuclideanSpace ℝ (Fin d) → ℝ, Continuous ut ∧
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Khat : Set (EuclideanSpace ℝ (Fin d)))] ut ∧
      ∀ x : K, ι u x = ut x)
    {I : ℕ} (xhat : Fin I → EuclideanSpace ℝ (Fin d))
    (φhat : Fin I → EuclideanSpace ℝ (Fin d) → ℝ) (hx : ∀ i, xhat i ∈ K)
    (hxc : ∀ i, xhat i ∈ closure (Khat : Set (EuclideanSpace ℝ (Fin d))))
    (hP : ∀ q : MvPolynomial (Fin d) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ Khat, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q)
    {q : SobolevEuclidean d (k + 1) 𝟚 Khat}
    (hq : q ∈ SobolevEuclidean.polynomialSubmodule (k := k) (p := 𝟚) hb) :
    (∑ i, (ι q ⟨xhat i, hx i⟩) • φhat i)
      =ᵐ[volume.restrict (Khat : Set (EuclideanSpace ℝ (Fin d)))] SobolevMultiIndex.fn q := by
  obtain ⟨r, hr, hqr⟩ := (SobolevEuclidean.mem_polynomialSubmodule_iff hb).1 hq
  have hrep := hι q
  obtain ⟨qt, hqtc, hqtae, hqtι⟩ := hrep
  have hpq : EqOn (fun x : EuclideanSpace ℝ (Fin d) ↦ MvPolynomial.eval (fun i ↦ x i) r) qt
      (closure (Khat : Set (EuclideanSpace ℝ (Fin d)))) :=
    eqOn_closure_of_ae_eq_of_continuousOn (hqr.symm.trans hqtae)
      (continuous_eval_coords r).continuousOn hqtc
  have hIq : (∑ i, (ι q ⟨xhat i, hx i⟩) • φhat i) = Approximation.nodalInterp xhat φhat
      (fun x : EuclideanSpace ℝ (Fin d) ↦ MvPolynomial.eval (fun i ↦ x i) r) := by
    rw [nodalInterp_eq_sum_smul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hqtι, ← hpq (hxc i)]
  rw [hIq]
  refine Filter.EventuallyEq.trans ?_ hqr.symm
  exact ae_restrict_of_forall_mem Khat.isOpen.measurableSet fun x hx' ↦
    hP r ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 hr) x hx'

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
`H^{k+1}(K̂)` to `H^m(K̂)` through the embedding (`sobolevSeminorm_sum_apply_smul_le`), it fixes
`ℙ_k(K̂)` (`sum_apply_smul_ae_eq_fn_of_mem_polynomialSubmodule`), so
`|v̂ − Π̂ v̂|_{m,K̂} ≤ c inf_{q ∈ ℙ_k} ‖v̂ + q‖_{k+1,K̂}`, and Corollary 7.3.18
(`SobolevEuclidean.exists_ciInf_norm_add_le_mul_topSeminorm`) bounds the infimum by
`|v̂|_{k+1,K̂}`; the passage between the tensor seminorm and the book's multi-index seminorm is
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
        ≤ ENNReal.ofReal c * sobolevSeminorm v (k + 1) 2 Khat volume := by
  classical
  -- the exponent in the backbone's form, `2 = ((2 : ℝ≥0) : ℝ≥0∞)` definitionally
  replace hφ : ∀ i, MemSobolev (φhat i) m 𝟚 Khat volume := hφ
  have : CompactSpace (closure (Khat : Set (EuclideanSpace ℝ (Fin d)))) :=
    isCompact_iff_compactSpace.1 hb.isCompact_closure
  -- the embedding `H^{k+1}(K̂) ↪ C(K̂̄)`
  have hkd' : (d : ℝ) / ((2 : ℝ≥0) : ℝ) < ((k + 1 : ℕ) : ℝ) := by
    rw [NNReal.coe_ofNat]
    push_cast
    exact hkd
  have hemb := SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order (N := d) k hΩ
    (Or.inr (by norm_num)) hkd' (K := closure (Khat : Set (EuclideanSpace ℝ (Fin d))))
    subset_closure
  obtain ⟨ι, hι, -⟩ := hemb
  -- Corollary 7.3.18: the quotient norm is bounded by the top seminorm
  have hBH := SobolevEuclidean.exists_ciInf_norm_add_le_mul_topSeminorm (N := d) (k := k)
    (p := 2) (hΩ _) hb hc
  obtain ⟨C₁, hC₁, hBH⟩ := hBH
  -- the constants
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = ∑ m' : Fin m → Fin d,
      ‖basisCoordProd (EuclideanSpace.basisFun (Fin d) ℝ).toBasis m'‖ := ⟨_, rfl⟩
  obtain ⟨Ck, hCk⟩ : ∃ Ck : ℝ, Ck = ∑ α : MultiIndexEq (Fin d) (k + 1), ∏ j,
      ‖multiIndexTuple ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis :
        Fin d → EuclideanSpace ℝ (Fin d)) α.1.1 j‖ := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ i, (sobolevSeminorm (φhat i) m 𝟚 Khat volume).toReal :=
    ⟨_, rfl⟩
  have hCm0 : 0 ≤ Cm := by rw [hCm]; positivity
  have hCk0 : 0 ≤ Ck := by rw [hCk]; positivity
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hA0 : 0 ≤ Cm + ‖ι‖ * S := add_nonneg hCm0 (mul_nonneg (norm_nonneg _) hS0)
  have hc0 : 0 ≤ (Cm + ‖ι‖ * S) * C₁ * Ck := mul_nonneg (mul_nonneg hA0 hC₁.le) hCk0
  refine ⟨(Cm + ‖ι‖ * S) * C₁ * Ck, hc0, fun v hv hvc ↦ ?_⟩
  replace hv : MemSobolev v (k + 1) 𝟚 Khat volume := hv
  suffices key : sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat volume
      ≤ ENNReal.ofReal ((Cm + ‖ι‖ * S) * C₁ * Ck) * sobolevSeminorm v (k + 1) 𝟚 Khat volume from
    key
  -- the typed element of `H^{k+1}(K̂)` carrying `v`
  have hv' : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin d) ℝ).toBasis v (k + 1) 𝟚 Khat
      volume := hv.memSobolevMultiIndex
  have hu := hv'.exists_sobolevMultiIndex
  obtain ⟨u, hu⟩ := hu
  -- its continuous representative is `v` on the closure
  have hrep := hι u
  obtain ⟨ut, hutc, hutae, hutι⟩ := hrep
  have hvut : EqOn v ut (closure (Khat : Set (EuclideanSpace ℝ (Fin d)))) :=
    eqOn_closure_of_ae_eq_of_continuousOn (hu.symm.trans hutae) hvc hutc
  have hnode : ∀ i, v (xhat i) = ι u ⟨xhat i, hx i⟩ := fun i ↦ by rw [hvut (hx i), hutι]
  -- the interpolation operator on the typed space
  obtain ⟨Ip, hIp⟩ : ∃ Ip : SobolevEuclidean d (k + 1) 𝟚 Khat → EuclideanSpace ℝ (Fin d) → ℝ,
      ∀ w, Ip w = ∑ i, (ι w ⟨xhat i, hx i⟩) • φhat i := ⟨_, fun _ ↦ rfl⟩
  have hIpu : Approximation.nodalInterp xhat φhat v = Ip u := by
    rw [nodalInterp_eq_sum_smul, hIp]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hnode i]
  have hIpadd : ∀ w₁ w₂, Ip (w₁ + w₂) = Ip w₁ + Ip w₂ := fun w₁ w₂ ↦ by
    rw [hIp, hIp, hIp, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_add, ContinuousMap.add_apply, add_smul]
  have hIpmem : ∀ w, MemSobolev (Ip w) m 𝟚 Khat volume := fun w ↦ by
    rw [hIp]
    exact MemSobolev.finsetSum fun i _ ↦ (hφ i).const_smul _
  have hIpbound : ∀ w, sobolevSeminorm (Ip w) m 𝟚 Khat volume
      ≤ ENNReal.ofReal (‖ι‖ * ‖w‖ * S) := fun w ↦ by
    rw [hIp, hS]
    exact sobolevSeminorm_sum_apply_smul_le ι (fun i ↦ ⟨xhat i, hx i⟩) (by norm_num) hφ w
  -- the estimate against `‖u + q‖` for every `q ∈ ℙ_k(K̂)`
  have hvm : MemSobolev v m 𝟚 Khat volume := hv.mono_order (by exact_mod_cast hm)
  have hmain : ∀ q : SobolevEuclidean.polynomialSubmodule (k := k) (p := 𝟚) hb,
      (sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat volume).toReal
        ≤ (Cm + ‖ι‖ * S) * ‖u + q.1‖ := by
    intro q
    have hfnq : MemSobolev (SobolevMultiIndex.fn q.1) (k + 1) 𝟚 Khat volume :=
      SobolevMultiIndex.memSobolev_fn q.1
    have hpoly := sum_apply_smul_ae_eq_fn_of_mem_polynomialSubmodule hb ι hι xhat φhat hx hx hP
      q.2
    rw [← hIp] at hpoly
    have hae : v - Approximation.nodalInterp xhat φhat v
        =ᵐ[volume.restrict (Khat : Set (EuclideanSpace ℝ (Fin d)))]
          (v + SobolevMultiIndex.fn q.1) - Ip (u + q.1) := by
      rw [hIpu, hIpadd]
      filter_upwards [hpoly] with x hx'
      simp only [Pi.sub_apply, Pi.add_apply, hx']
      ring
    rw [sobolevSeminorm_congr_ae hae]
    have h1 : sobolevSeminorm ((v + SobolevMultiIndex.fn q.1) - Ip (u + q.1)) m 𝟚 Khat volume
        ≤ sobolevSeminorm (v + SobolevMultiIndex.fn q.1) m 𝟚 Khat volume
          + sobolevSeminorm (Ip (u + q.1)) m 𝟚 Khat volume :=
      sobolevSeminorm_sub_le (by norm_num) (hvm.add (hfnq.mono_order (by exact_mod_cast hm)))
        (hIpmem _)
    have h2 : sobolevSeminorm (v + SobolevMultiIndex.fn q.1) m 𝟚 Khat volume
        ≤ ENNReal.ofReal (Cm * ‖u + q.1‖) := by
      have hae2 : v + SobolevMultiIndex.fn q.1
          =ᵐ[volume.restrict (Khat : Set (EuclideanSpace ℝ (Fin d)))]
            SobolevMultiIndex.fn (u + q.1) := by
        filter_upwards [hu, SobolevMultiIndex.fn_add u q.1] with x h1 h2
        rw [h2]
        change v x + _ = SobolevMultiIndex.fn u x + _
        rw [h1]
      rw [sobolevSeminorm_congr_ae hae2, ENNReal.ofReal_mul hCm0, hCm]
      exact SobolevMultiIndex.sobolevSeminorm_fn_le (u + q.1) hm
    have h3 := hIpbound (u + q.1)
    have htot : sobolevSeminorm ((v + SobolevMultiIndex.fn q.1) - Ip (u + q.1)) m 𝟚 Khat volume
        ≤ ENNReal.ofReal ((Cm + ‖ι‖ * S) * ‖u + q.1‖) := by
      refine h1.trans ((add_le_add h2 h3).trans (le_of_eq ?_))
      rw [← ENNReal.ofReal_add (mul_nonneg hCm0 (norm_nonneg _))
        (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hS0)]
      congr 1
      ring
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hA0 (norm_nonneg _)) htot
  -- pass to the infimum, apply Corollary 7.3.18 and compare the seminorms
  have hinf : (sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat volume).toReal
      ≤ (Cm + ‖ι‖ * S) * ⨅ q : SobolevEuclidean.polynomialSubmodule (k := k) (p := 𝟚) hb,
        ‖u + q‖ := by
    rw [Real.mul_iInf_of_nonneg hA0]
    exact le_ciInf hmain
  have hBHu := hBH u
  have hcmp := SobolevMultiIndex.topSeminorm_le_mul_toReal_sobolevSeminorm u
  rw [← hCk] at hcmp
  have hsv : sobolevSeminorm v (k + 1) 𝟚 Khat volume
      = sobolevSeminorm (SobolevMultiIndex.fn u) (k + 1) 𝟚 Khat volume :=
    sobolevSeminorm_congr_ae hu.symm
  have hfinal : (sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat
      volume).toReal
        ≤ (Cm + ‖ι‖ * S) * C₁ * Ck * (sobolevSeminorm v (k + 1) 𝟚 Khat volume).toReal := by
    rw [hsv]
    refine hinf.trans ?_
    refine (mul_le_mul_of_nonneg_left hBHu hA0).trans ?_
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcmp hC₁.le) hA0).trans
      (le_of_eq ?_)
    ring
  have hlhs : sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat volume ≠ ⊤ :=
    (hvm.sub (memSobolev_nodalInterp hφ v)).sobolevSeminorm_ne_top
  calc sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat volume
      = ENNReal.ofReal (sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat
          volume).toReal := (ENNReal.ofReal_toReal hlhs).symm
    _ ≤ ENNReal.ofReal ((Cm + ‖ι‖ * S) * C₁ * Ck
          * (sobolevSeminorm v (k + 1) 𝟚 Khat volume).toReal) := ENNReal.ofReal_le_ofReal hfinal
    _ = ENNReal.ofReal ((Cm + ‖ι‖ * S) * C₁ * Ck) * sobolevSeminorm v (k + 1) 𝟚 Khat volume := by
          rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_toReal hv.sobolevSeminorm_ne_top]

end Theorem1033

/-! ### Theorem 10.3.5: the local interpolation error -/

section Theorem1035

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The inverse of the affine map `F x = T x + b` is a left inverse. -/
theorem affine_leftInverse (T : 𝔼 ≃L[ℝ] 𝔼) (b : 𝔼) :
    Function.LeftInverse (fun y ↦ T.symm (y - b)) (fun x ↦ T x + b) := fun x ↦ by simp

/-- The image of a bounded set under the affine map `F x = T x + b` is bounded. -/
theorem isBounded_image_affine (T : 𝔼 ≃L[ℝ] 𝔼) (b : 𝔼) {s : Set 𝔼} (hs : Bornology.IsBounded s) :
    Bornology.IsBounded ((fun x ↦ T x + b) '' s) :=
  ((isometry_add_right b).lipschitzWith.comp (T : 𝔼 →L[ℝ] 𝔼).lipschitzWith).isBounded_image hs

/-- **The transported shape functions lie in `H^m(K)`**: if `φ̂ ∈ W^{m,p}(K̂)` and
`K = F_K(K̂)` for `F_K x = T x + b`, then `φ̂ ∘ F_K⁻¹ ∈ W^{m,p}(K)`, the affine change of
variables `memSobolev_comp_affine` for the inverse map `y ↦ T⁻¹(y − b)`. -/
theorem memSobolev_comp_affine_inv (T : 𝔼 ≃L[ℝ] 𝔼) (b : 𝔼) {Khat K : Opens 𝔼}
    (hK : (fun x ↦ T x + b) '' Khat = K) {φ : 𝔼 → ℝ} {m : ℕ∞} {p : ℝ≥0∞}
    (hφ : MemSobolev φ m p Khat volume) :
    MemSobolev (φ ∘ fun y ↦ T.symm (y - b)) m p K volume := by
  have hKhat : Khat = affinePreimage T b K := (affinePreimage_eq_of_image_eq T b hK).symm
  have h := memSobolev_comp_affine T.symm (-T.symm b) hφ
  rw [hKhat, affinePreimage_symm] at h
  refine h.congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp [sub_eq_add_neg]

/-- `|det T|^{1/2} · |det T|^{-1/2} = 1` for an invertible `T`. -/
theorem abs_det_rpow_half_mul_rpow_neg_half (T : 𝔼 ≃L[ℝ] 𝔼) :
    |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ)
      * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ)) = 1 := by
  have hdet : 0 < |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| :=
    abs_pos.2 (LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero
  rw [Real.rpow_neg hdet.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hdet _).ne']

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
          * sobolevSeminorm v (k + 1) 2 K volume := by
  obtain ⟨c₀, hc₀0, hc₀⟩ := theorem_10_3_3 hΩ hb hc hm hkd xhat φhat hx hφ hP
  refine ⟨c₀ * Metric.diam (Khat : Set 𝔼) ^ m / ρhat ^ (k + 1), by positivity, ?_⟩
  intro T b K hK cK ρK hρK hballK v hv hvc
  have hKb : Bornology.IsBounded (K : Set 𝔼) := hK ▸ isBounded_image_affine T b hb
  -- Lemma 10.2.2
  obtain ⟨hT, hT'⟩ := lemma_10_2_2 hρhat hρK hb hKb hballhat hballK hK
  -- the change of variables `F_K`
  have hKhat : Khat = affinePreimage T b K := (affinePreimage_eq_of_image_eq T b hK).symm
  have hG : Function.LeftInverse (fun y ↦ T.symm (y - b)) (fun x ↦ T x + b) :=
    affine_leftInverse T b
  -- the transported shape functions lie in `H^m(K)`
  have hφK : ∀ i, MemSobolev (φhat i ∘ fun y ↦ T.symm (y - b)) m 2 K volume := fun i ↦
    memSobolev_comp_affine_inv T b hK (hφ i)
  -- `w = v − Π_K v` and its transport `w ∘ F_K = v̂ − Π̂ v̂` (Theorem 10.3.1)
  obtain ⟨w, hw⟩ : ∃ w : 𝔼 → ℝ, w = v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ xhat)
      (fun i ↦ φhat i ∘ fun y ↦ T.symm (y - b)) v := ⟨_, rfl⟩
  have hwmem : MemSobolev w m 2 K volume := by
    rw [hw]
    exact (hv.mono_order (by exact_mod_cast hm)).sub (memSobolev_nodalInterp hφK v)
  have hwF : (fun x ↦ w (T x + b))
      = (fun x ↦ v (T x + b)) - Approximation.nodalInterp xhat φhat (fun x ↦ v (T x + b)) := by
    funext x
    have h := congrFun (Approximation.nodalInterp_comp xhat φhat v hG) x
    change w (T x + b)
      = v (T x + b) - Approximation.nodalInterp xhat φhat (v ∘ fun x ↦ T x + b) x
    rw [← h, hw]
    rfl
  rw [← hw]
  -- (10.3.6), Theorem 10.3.3 on `K̂`, and (10.3.5) at order `k + 1`
  have h6 := (theorem_10_3_4 T b Khat K hK m w).2.2 hwmem
  have hvF : MemSobolev (fun x ↦ v (T x + b)) (k + 1) 2 Khat volume :=
    (theorem_10_3_4 T b Khat K hK (k + 1) v).1.1 hv
  have hvFc : ContinuousOn (fun x ↦ v (T x + b)) (closure (Khat : Set 𝔼)) := by
    rw [hKhat]
    exact hvc.comp_affine_closure T b
  have h3 := hc₀ _ hvF hvFc
  rw [← hwF] at h3
  have h5 := (theorem_10_3_4 T b Khat K hK (k + 1) v).2.1 hv
  -- assemble the constants
  have hdet : |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ)
      * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ)) = 1 :=
    abs_det_rpow_half_mul_rpow_neg_half T
  have hA0 : 0 ≤ ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ) := by
    positivity
  have hB0 : 0 ≤ ‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1)
      * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ)) := by
    positivity
  have hreal : ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ)
      * (c₀ * (‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1) * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ))))
      ≤ c₀ * Metric.diam (Khat : Set 𝔼) ^ m / ρhat ^ (k + 1) * Metric.diam (K : Set 𝔼) ^ (k + 1)
        / ρK ^ m := by
    have e : ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ)
        * (c₀ * (‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1) * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ))))
        = c₀ * ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * ‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1)
          * (|LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ)
            * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ))) := by ring
    rw [e, hdet, mul_one]
    have h1 : ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m ≤ (Metric.diam (Khat : Set 𝔼) / ρK) ^ m :=
      pow_le_pow_left₀ (norm_nonneg _) hT' m
    have h2 : ‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1) ≤ (Metric.diam (K : Set 𝔼) / ρhat) ^ (k + 1) :=
      pow_le_pow_left₀ (norm_nonneg _) hT (k + 1)
    calc c₀ * ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * ‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1)
        ≤ c₀ * (Metric.diam (Khat : Set 𝔼) / ρK) ^ m
            * (Metric.diam (K : Set 𝔼) / ρhat) ^ (k + 1) := by
          gcongr
      _ = c₀ * Metric.diam (Khat : Set 𝔼) ^ m / ρhat ^ (k + 1) * Metric.diam (K : Set 𝔼) ^ (k + 1)
            / ρK ^ m := by
          rw [div_pow, div_pow]
          field_simp
  calc sobolevSeminorm w m 2 K volume
      ≤ ENNReal.ofReal (‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ))
          * (ENNReal.ofReal c₀ * (ENNReal.ofReal (‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1)
            * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ)))
            * sobolevSeminorm v (k + 1) 2 K volume)) := by
        refine h6.trans ?_
        gcongr
        exact h3.trans (by gcongr)
    _ = ENNReal.ofReal (‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ)
          * (c₀ * (‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1) * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ)))))
          * sobolevSeminorm v (k + 1) 2 K volume := by
        rw [ENNReal.ofReal_mul hA0, ENNReal.ofReal_mul hc₀0, mul_assoc, mul_assoc]
    _ ≤ _ := by gcongr

end Theorem1035

/-! ### Corollary 10.3.7: the estimate on a regular family -/

section Corollary1037

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The arithmetic of Corollary 10.3.7: for `0 ≤ h ≤ σ ρ`, `ρ > 0` and `h ≤ H`, and orders
`j ≤ m ≤ k + 1`, `h^{k+1} / ρ^j ≤ σ^j H^{m−j} h^{k+1−m}`. -/
theorem pow_div_pow_le_of_le_mul {h ρ σ H : ℝ} (hh : 0 ≤ h) (hρ : 0 < ρ) (hσ : 0 ≤ σ)
    (hhσ : h ≤ σ * ρ) (hhH : h ≤ H) {j m k : ℕ} (hjm : j ≤ m) (hmk : m ≤ k + 1) :
    h ^ (k + 1) / ρ ^ j ≤ σ ^ j * H ^ (m - j) * h ^ (k + 1 - m) := by
  obtain ⟨a, rfl⟩ : ∃ a, m = j + a := ⟨m - j, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, k + 1 = j + a + e := ⟨k + 1 - (j + a), by omega⟩
  rw [he, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, pow_add, pow_add,
    div_le_iff₀ (by positivity)]
  have h1 : h ^ j ≤ (σ * ρ) ^ j := pow_le_pow_left₀ hh hhσ j
  have h2 : h ^ a ≤ H ^ a := pow_le_pow_left₀ hh hhH a
  calc h ^ j * h ^ a * h ^ e ≤ (σ * ρ) ^ j * H ^ a * h ^ e := by gcongr
    _ = σ ^ j * H ^ a * h ^ e * ρ ^ j := by ring

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
          * sobolevSeminorm v (k + 1) 2 Kop volume := by
  obtain ⟨σ, hσ⟩ := hreg.1
  -- Theorem 10.3.5 at every order `j ≤ m`
  have h5 : ∀ j : Fin (m + 1), ∃ c : ℝ, 0 ≤ c ∧ ∀ (T : 𝔼 ≃L[ℝ] 𝔼) (b : 𝔼) (K : Opens 𝔼),
      (fun x ↦ T x + b) '' Khat = K →
      ∀ {cK : 𝔼} {ρK : ℝ}, 0 < ρK → Metric.closedBall cK (ρK / 2) ⊆ K →
      ∀ v : 𝔼 → ℝ, MemSobolev v (k + 1) 2 K volume → ContinuousOn v (closure (K : Set 𝔼)) →
      sobolevSeminorm (v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ xhat)
          (fun i ↦ φhat i ∘ fun y ↦ T.symm (y - b)) v) j 2 K volume
        ≤ ENNReal.ofReal (c * Metric.diam (K : Set 𝔼) ^ (k + 1) / ρK ^ (j : ℕ))
          * sobolevSeminorm v (k + 1) 2 K volume := fun j ↦
    theorem_10_3_5 hΩ hb hc hρhat hballhat ((Nat.lt_succ_iff.1 j.2).trans hm) hkd xhat φhat hx
      (fun i ↦ (hφ i).mono_order (by exact_mod_cast Nat.lt_succ_iff.1 j.2)) hP
  choose cj hcj0 hcj using h5
  obtain ⟨σ', hσ'⟩ : ∃ σ' : ℝ, σ' = max σ 0 := ⟨_, rfl⟩
  obtain ⟨H', hH'⟩ : ∃ H' : ℝ, H' = max H 0 := ⟨_, rfl⟩
  have hσ'0 : 0 ≤ σ' := hσ' ▸ le_max_right _ _
  have hH'0 : 0 ≤ H' := hH' ▸ le_max_right _ _
  refine ⟨∑ j : Fin (m + 1), cj j * σ' ^ (j : ℕ) * H' ^ (m - j),
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (mul_nonneg (hcj0 j) (by positivity)) (by positivity),
    ?_⟩
  intro i K hK Kop hKop T b hF v hv hvc
  obtain ⟨cK, r, hr, hball, hdiam⟩ := hσ i K hK
  have hball' : Metric.closedBall cK (2 * r / 2) ⊆ Kop := by
    rw [hKop, mul_div_cancel_left₀ _ (two_ne_zero' ℝ)]
    exact hball
  have hdiamK : Metric.diam (Kop : Set 𝔼) = Metric.diam K := by rw [hKop]
  have hw : MemSobolev (v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ xhat)
      (fun i ↦ φhat i ∘ fun y ↦ T.symm (y - b)) v) m 2 Kop volume :=
    (hv.mono_order (by exact_mod_cast hm)).sub
      (memSobolev_nodalInterp (fun i ↦ memSobolev_comp_affine_inv T b hF (hφ i)) v)
  refine (hw.sobolevNorm_le_sum_sobolevSeminorm (by norm_num)).trans ?_
  -- the real inequality of each order
  have hreal : ∀ j : Fin (m + 1), cj j * Metric.diam (Kop : Set 𝔼) ^ (k + 1) / (2 * r) ^ (j : ℕ)
      ≤ cj j * σ' ^ (j : ℕ) * H' ^ (m - j) * Metric.diam K ^ (k + 1 - m) := by
    intro j
    rw [hdiamK, mul_div_assoc, mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hcj0 j)
    rw [← mul_assoc]
    refine pow_div_pow_le_of_le_mul Metric.diam_nonneg (by positivity) hσ'0 ?_ ?_
      (Nat.lt_succ_iff.1 j.2) hm
    · exact hdiam.trans (mul_le_mul_of_nonneg_right (hσ' ▸ le_max_left _ _) (by positivity))
    · exact (hH i K hK).trans (hH' ▸ le_max_left _ _)
  calc ∑ j : Fin (m + 1), sobolevSeminorm (v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ xhat)
        (fun i ↦ φhat i ∘ fun y ↦ T.symm (y - b)) v) j 2 Kop volume
      ≤ ∑ j : Fin (m + 1), ENNReal.ofReal (cj j * σ' ^ (j : ℕ) * H' ^ (m - j)
          * Metric.diam K ^ (k + 1 - m)) * sobolevSeminorm v (k + 1) 2 Kop volume := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        refine (hcj j T b Kop hF (by positivity) hball' v hv hvc).trans ?_
        gcongr
        exact hreal j
    _ = ENNReal.ofReal (∑ j : Fin (m + 1), cj j * σ' ^ (j : ℕ) * H' ^ (m - j)
          * Metric.diam K ^ (k + 1 - m)) * sobolevSeminorm v (k + 1) 2 Kop volume := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun j _ ↦
          mul_nonneg (mul_nonneg (mul_nonneg (hcj0 j) (by positivity)) (by positivity))
            (by positivity)]
    _ = _ := by rw [Finset.sum_mul]

end Corollary1037

/-! ### Example 10.3.8 on the unit square: `Q₁` elements on parallelograms

The book's Example 10.3.8 is the linear element on a *triangle*, whose reference element, the
reference simplex, is a Lipschitz domain that the backbone does not know to be a Sobolev extension
domain; it stays open (`example_10_3_8`). The unit square is an extension domain (Brezis's
Remark 9, `SobolevEuclidean.exists_extensionL_unitSquare`), so the estimate is instantiated here
for the `Q₁` element on it: nodes the four vertices, shape functions the bilinear
`(1 ∓ x̂₁)(1 ∓ x̂₂)` of Exercise 10.2.3 (`bilinearShape`, here on `EuclideanSpace ℝ (Fin 2)`),
local space `Q₁ ⊇ ℙ₁`, and the elements the affine images of the square — parallelograms, of
which the book's rectangles are the case of a diagonal `T_K`. -/

section Example1038Square

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- **The unit square is a Sobolev extension domain for every exponent**: Brezis's Remark 9
(`SobolevEuclidean.exists_extensionL_unitSquare`), read as the backbone's hypothesis. -/
theorem isSobolevExtensionDomainAll_unitSquare :
    IsSobolevExtensionDomainAll 2 (EuclideanSpace.rect 0 1 0 1) := by
  intro q _
  obtain ⟨P, C, hP⟩ := SobolevEuclidean.exists_extensionL_unitSquare (p := q)
  exact ⟨P.comp (Submodule.subtypeL ⊤), fun u ↦ (hP u.1).1⟩

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

/-- A smooth function lies in `H^m(Ω)` for every `m` on a bounded open `Ω ⊆ ℝ^N`
(`SobolevEuclidean.exists_fn_ae_eq_of_contDiff`). -/
theorem memSobolev_of_contDiff {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    {φ : EuclideanSpace ℝ (Fin N) → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (m : ℕ) :
    MemSobolev φ m 2 Ω volume := by
  obtain ⟨u, hu⟩ := SobolevEuclidean.exists_fn_ae_eq_of_contDiff (k := m) (p := 2) hb hφ
  exact (SobolevMultiIndex.memSobolev_fn u).congr_ae hu

/-- The bilinear shape functions lie in `H^m` of the unit square for every `m`. -/
theorem memSobolev_q1Shape (m : ℕ) (i : Fin 4) :
    MemSobolev (q1Shape i) m 2 (EuclideanSpace.rect 0 1 0 1) volume :=
  memSobolev_of_contDiff isBounded_unitSquare (contDiff_q1Shape i) m

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
element on triangles, `example_10_3_8`, which waits for a simplex extension operator. -/
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

end AtkinsonHan.Chapter10
