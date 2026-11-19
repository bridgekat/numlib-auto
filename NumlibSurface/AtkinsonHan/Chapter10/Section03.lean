/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
# Atkinson and Han, Section 10.3: Interpolation error estimates

This module formalizes Section 10.3 of [han2009theoretical]. The section estimates the error of
finite element interpolation on one element $K = F_K(\hat K)$, the image of a reference element
$\hat K$ under an affine bijection $F_K(\hat x) = T_K \hat x + b_K$. Interpolation commutes with the
change of variables (Theorem 10.3.1), the error on $\hat K$ is bounded by $c |\hat v|_{k+1,\hat K}$
when the local space contains the polynomials of degree at most $k$ (Theorem 10.3.3), and the affine
change of variables in $H^m$ (Theorem 10.3.4) carries this bound to the local estimate $|v - \Pi_K
v|_{m,K} \le c h_K^{k+1} \rho_K^{-m} |v|_{k+1,K}$ (Theorem 10.3.5). Here $h_K$ is the diameter of
$K$ and $\rho_K$ the diameter of a ball inscribed in $K$. On a regular family of partitions
(Definition 10.3.6) the ratio $h_K / \rho_K$ is bounded, and the estimate becomes $\|v - \Pi_K
v\|_{m,K} \le c h_K^{k+1-m} |v|_{k+1,K}$ (Corollary 10.3.7). Example 10.3.8 applies this to the
linear element on triangles, and Theorem 10.3.9 sums the local estimates over a triangulation.

The general theory is in `Numlib.FiniteElement.Interpolation`, and the results here specialize it.
The Sobolev spaces come from `Numlib.Analysis.Sobolev`, the nodal interpolation operator from
`Numlib.Approximation.NodalInterpolation`, the triangulations from `Numlib.Geometry.Triangulation`,
and the geometry of a triangle from `Numlib.Geometry.Euclidean.TriangleShape`.

## Main definitions

* Equation (10.3.9), `AtkinsonHan.Chapter10.meshSize`: the mesh parameter
  $h = \max_{K \in \mathcal{T}_h} h_K$, as the supremum of the diameters of the elements.
* Definition 10.3.6, `AtkinsonHan.Chapter10.IsRegularFamily`: a family of partitions is regular if
  the ratios $h_K / \rho_K$ are bounded uniformly and the mesh parameter tends to $0$.

## Main results

* Theorem 10.3.1, `AtkinsonHan.Chapter10.theorem_10_3_1`:
  $\hat\Pi (v \circ F_K) = (\Pi_K v) \circ F_K$.
* Example 10.3.2, `AtkinsonHan.Chapter10.example_10_3_2`: the barycentric coordinates of a simplex
  are nodal for its vertices.
* Example 10.3.2, `AtkinsonHan.Chapter10.nodalInterp_coord_affineMap`: the linear element reproduces
  affine functions.
* Theorem 10.3.3, `AtkinsonHan.Chapter10.theorem_10_3_3`: $|\hat v - \hat\Pi \hat v|_{m,\hat K} \le
  c |\hat v|_{k+1,\hat K}$ on the reference element, if $\hat\Pi$ reproduces the polynomials of
  degree at most $k$.
* Theorem 10.3.4, `AtkinsonHan.Chapter10.theorem_10_3_4`: $v \in H^m(K)$ if and only if
  $v \circ F_K \in H^m(\hat K)$, with the seminorm bounds (10.3.5) and (10.3.6).
* Theorem 10.3.5, `AtkinsonHan.Chapter10.theorem_10_3_5`: $|v - \Pi_K v|_{m,K} \le c h_K^{k+1}
  \rho_K^{-m} |v|_{k+1,K}$ on every affine image $K$ of $\hat K$.
* Corollary 10.3.7, `AtkinsonHan.Chapter10.corollary_10_3_7`: $\|v - \Pi_K v\|_{m,K} \le c
  h_K^{k+1-m} |v|_{k+1,K}$ on a regular family.
* Example 10.3.8, `AtkinsonHan.Chapter10.example_10_3_8`: $\|v - \Pi_K v\|_{m,K} \le c h_K^{2-m}
  |v|_{2,K}$ for the linear element on a regular family of triangles.
* Example 10.3.8, `AtkinsonHan.Chapter10.example_10_3_8_square`: the same estimate for the $Q_1$
  element on a regular family of parallelograms.
* Theorem 10.3.9, `AtkinsonHan.Chapter10.theorem_10_3_9`: $\|v - \Pi_h v\|_{m,\Omega} \le c
  h^{k+1-m} |v|_{k+1,\Omega}$ for $m = 0, 1$ on a regular family of triangulations.
* Theorem 10.3.9, `AtkinsonHan.Chapter10.theorem_10_3_9_linear`: the global estimate for the linear
  element.
* Theorem 10.3.9, `AtkinsonHan.Chapter10.theorem_10_3_9_lattice`: the global estimate for the
  $\mathbb{P}_k$ Lagrange element on the principal lattice.
* Exercise 10.3.3, `AtkinsonHan.Chapter10.exercise_10_3_3`: for a family of triangles,
  $h_K / \rho_K$ is bounded if and only if the angles are bounded away from $0$.

## Implementation notes

* $H^m(K)$ is `AtkinsonHan.Chapter07.definition_7_2_2 m 2 K`, that is `MemSobolev v m 2 K volume`.
  The seminorm $|\cdot|_{m,K}$ is `sobolevSeminorm v m 2 K volume`, the $L^2(K)$ norm of the
  operator norm of the tensor of weak derivatives of order $m$, and the norm $\|\cdot\|_{m,K}$ is
  `sobolevNorm`. Both take values in $[0, \infty]$. They are equivalent to the multi-index seminorm
  and norm of the source, with constants that depend on $d$ and $m$ only
  (`Numlib.Analysis.Sobolev.SeminormCompare`).
* An element is an open set (`TopologicalSpace.Opens`), and the closed element of the source is its
  closure. An element $K = F_K(\hat K)$ is given by $T_K$ as a continuous linear equivalence and
  $b_K$ as a vector, with the hypothesis that the image of $\hat K$ under
  $\hat x \mapsto T_K \hat x + b_K$ is $K$.
* The interpolation operators $\hat\Pi$ of (10.3.1) and $\Pi_K$ of (10.3.2) are
  `Approximation.nodalInterp`, at the nodes $\hat x_i$ with the shape functions $\hat\varphi_i$, and
  at the nodes $F_K(\hat x_i)$ with the shape functions $\hat\varphi_i \circ F_K^{-1}$.
* The polynomial invariance (10.3.4), $\mathbb{P}_k(\hat K) \subseteq \hat X$, is the hypothesis
  that $\hat\Pi q = q$ on $\hat K$ for every `MvPolynomial` $q$ of total degree at most $k$.
* The $Q_1$ element on the unit square $(0, 1)^2$, `EuclideanSpace.rect 0 1 0 1`, has the nodes
  `AtkinsonHan.Chapter10.q1Node` and the shape functions `AtkinsonHan.Chapter10.q1Shape`. These are
  `AtkinsonHan.Chapter10.bilinearNode` and `AtkinsonHan.Chapter10.bilinearShape` of Exercise 10.2.3,
  on `EuclideanSpace ℝ (Fin 2)` in place of `ℝ × ℝ`.
* The reference triangle is `EuclideanSpace.referenceTriangle`, with the vertices
  `EuclideanSpace.referenceTriangleVertex` and the barycentric coordinates
  `EuclideanSpace.baryCoord`. A triangulation is a `Triangulation`, and the global interpolant
  $\Pi_h v$ is `Triangulation.globalInterp`.

## Deviations from the source

* **Theorem 10.3.1** (generalization). The identity holds for any shape functions; the nodal
  property $\hat\varphi_i(\hat x_j) = \delta_{ij}$ is not assumed. See
  `AtkinsonHan.Chapter10.theorem_10_3_1`.
* **Example 10.3.2** (generalization). The source takes a triangle in the plane; the statement holds
  for the barycentric coordinates of any simplex in $\mathbb{R}^d$. See
  `AtkinsonHan.Chapter10.example_10_3_2`.
* **Theorems 10.3.3 and 10.3.5, Corollary 10.3.7** (generalization). The source takes a triangle
  with $k > 0$. The library takes a bounded connected open set in $\mathbb{R}^d$ that is a Sobolev
  extension domain for every exponent, with $k + 1 > d/2$. The reference triangle and the unit
  square satisfy this hypothesis. See `AtkinsonHan.Chapter10.theorem_10_3_3`.
* **Theorem 10.3.4** (reading). The bounds (10.3.5) and (10.3.6) use the Sobolev seminorm formed
  with the tensor operator norm. This gives constant $1$ in place of the unspecified constant
  for the book's multi-index seminorm.
* **Theorems 10.3.3, 10.3.5 and 10.3.9, Corollary 10.3.7, Example 10.3.8** (reading). A function of
  $H^{k+1}$ is taken on its representative that is continuous up to the boundary, so that its values
  at the nodes are defined. See `AtkinsonHan.Chapter10.theorem_10_3_3`.
* **Theorem 10.3.5, Definition 10.3.6** (reading). The source takes $\rho_K$ to be the diameter of
  the largest ball inscribed in $K$. The library uses the diameter of any inscribed closed ball. See
  `AtkinsonHan.Chapter10.IsRegularFamily`.
* **Equation (10.3.9)** (generalization). Mesh size is defined by a real supremum for arbitrary
  collections. This gives the book's maximum for a nonempty finite mesh.
* **Definition 10.3.6** (reading). The source indexes the family by $h \to 0$. The library indexes
  it by any type, with a filter along which the mesh parameter tends to $0$, and a partition is a
  collection of sets. See `AtkinsonHan.Chapter10.IsRegularFamily`.
* **Corollary 10.3.7, Example 10.3.8, Theorem 10.3.9** (reading). The source leaves implicit a bound
  $h_K \le H$ on the diameters of the elements, on which its constant depends. The library makes it
  a hypothesis. See `AtkinsonHan.Chapter10.corollary_10_3_7`.
* **Example 10.3.8** (generalization). The estimate (10.3.11) is also proved for $m = 2$ and for
  the bilinear element on affine images of the reference square. See
  `AtkinsonHan.Chapter10.example_10_3_8` and `AtkinsonHan.Chapter10.example_10_3_8_square`.
* **Theorem 10.3.9** (restriction). The statement uses plane triangulations and $C^1$ shape
  functions on the reference triangle. The source takes the reference element of Corollary
  10.3.7. Conformity on each triangulation supplies the source's standing continuity assumption
  $X_h \subseteq C(\overline\Omega)$. See `AtkinsonHan.Chapter10.theorem_10_3_9`.

## Not formalized

* **Exercises 10.3.1, 10.3.2, 10.3.4 and 10.3.7.**
* **The remark after Theorem 10.3.9** on the interpolation of discontinuous functions by local $L^2$
  projections. It refers to the literature and states no result.
-/

open Filter Metric Topology

open scoped Real

namespace AtkinsonHan.Chapter10

variable {d : ℕ}

/-- **Theorem 10.3.1** of [han2009theoretical]. Let $F_K$ be an affine bijection of $\mathbb{R}^d$,
let $\hat x_1, \dots, \hat x_I \in \mathbb{R}^d$ be nodes and
$\hat\varphi_1, \dots, \hat\varphi_I$ functions on $\mathbb{R}^d$, and put
$x_i^K = F_K(\hat x_i)$ and $\varphi_i^K = \hat\varphi_i \circ F_K^{-1}$ as in (10.2.27). Then
for every function $v$ on $\mathbb{R}^d$ the interpolation operators $\hat\Pi \hat v = \sum_i
\hat v(\hat x_i) \hat\varphi_i$ of (10.3.1) and $\Pi_K v = \sum_i v(x_i^K) \varphi_i^K$ of
(10.3.2) satisfy
$$\hat\Pi (v \circ F_K) = (\Pi_K v) \circ F_K.$$

**Generalization.** The source assumes that the $\hat\varphi_i$ are nodal,
$\hat\varphi_i(\hat x_j) = \delta_{ij}$. The identity does not need this, because
$v(x_i^K) = (v \circ F_K)(\hat x_i)$ and $\varphi_i^K \circ F_K = \hat\varphi_i$.

The statement is `Approximation.nodalInterp_comp` for the bijection $F_K$. That lemma holds for
any map with a left inverse, so the affinity of $F_K$ is not used. The nodal property is
preserved by the transport (`Approximation.IsNodalBasis.comp`), which is the display
$\varphi_i^K(x_j^K) = \delta_{ij}$ of the source. -/
theorem theorem_10_3_1 {I : ℕ} (F : EuclideanSpace ℝ (Fin d) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin d))
    (x : Fin I → EuclideanSpace ℝ (Fin d)) (φ : Fin I → EuclideanSpace ℝ (Fin d) → ℝ)
    (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    Approximation.nodalInterp x φ (v ∘ F) =
      Approximation.nodalInterp (F ∘ x) (fun i => φ i ∘ F.symm) v ∘ F :=
  (Approximation.nodalInterp_comp x φ v (F := F) (G := F.symm) F.symm_apply_apply).symm

/-- **Example 10.3.2** of [han2009theoretical], the linear element. Let $b_0, \dots, b_d$ be an
affine basis of $\mathbb{R}^d$, the vertices of a simplex, and let $\lambda_i$ be the
barycentric coordinates with respect to it. Then $\lambda_i(b_j) = \delta_{ij}$, so the
$\lambda_i$ are nodal for the vertices.

**Generalization.** The source takes a triangle in the plane. The statement holds in any
dimension and for any index set of the vertices.

The barycentric coordinates are `AffineBasis.coord`. So `Approximation.nodalInterp b (fun i =>
b.coord i)` is the operator $\Pi_K$ of (10.3.2) for the linear element, the function that agrees
with $v$ at each vertex. -/
theorem example_10_3_2 {ι : Type*} (b : AffineBasis ι ℝ (EuclideanSpace ℝ (Fin d))) :
    Approximation.IsNodalBasis (b : ι → EuclideanSpace ℝ (Fin d))
      (fun i => (b.coord i : EuclideanSpace ℝ (Fin d) → ℝ)) where
  eval_self _ := b.coord_apply_eq _
  eval_of_ne _ _ hij := b.coord_apply_ne hij

/-- The linear element reproduces affine functions. Let $b_0, \dots, b_d$ be an affine basis of
$\mathbb{R}^d$ with barycentric coordinates $\lambda_i$, and let
$f : \mathbb{R}^d \to \mathbb{R}$ be affine. Then
$$\sum_i \lambda_i(y) f(b_i) = f(y) \qquad \text{for all } y \in \mathbb{R}^d,$$
that is, $\Pi_K f = f$.

This is the case $k = 1$ of the polynomial invariance (10.3.4) for the linear element of Example
10.3.2. It is $f$ applied to the barycentric representation $y = \sum_i \lambda_i(y) b_i$.

**Reading.** Affine reproduction on any simplex in place of a plane triangle.
-/
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

/-- **Equation (10.3.9)** of [han2009theoretical]. The **mesh parameter** of a collection
$\mathcal{T}_h$ of subsets of $\mathbb{R}^d$ is
$$h = \sup_{K \in \mathcal{T}_h} \operatorname{diam} K.$$

The source writes a maximum over a finite partition; for a finite collection the supremum is the
maximum (`AtkinsonHan.Chapter10.diam_le_meshSize`). The value is `sSup` of the set of diameters,
so it is $0$ for an empty collection and for a collection whose diameters are unbounded.

**Reading.** The supremum accepts arbitrary collections and gives the book's maximum on nonempty
finite collections.
-/
noncomputable def meshSize (T : Set (Set (EuclideanSpace ℝ (Fin d)))) : ℝ :=
  sSup (Metric.diam '' T)

/-- Let $\mathcal{T}_h$ be a finite collection of subsets of $\mathbb{R}^d$. Every
$K \in \mathcal{T}_h$ satisfies $\operatorname{diam} K \le h$, where $h$ is the mesh parameter
`AtkinsonHan.Chapter10.meshSize`. -/
theorem diam_le_meshSize {T : Set (Set (EuclideanSpace ℝ (Fin d)))} (hT : T.Finite)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : K ∈ T) : Metric.diam K ≤ meshSize T :=
  le_csSup (hT.image _).bddAbove (Set.mem_image_of_mem _ hK)

/-- **Definition 10.3.6** of [han2009theoretical]. Let $\{\mathcal{T}_i\}$ be a family of
collections of subsets of $\mathbb{R}^d$, indexed by a type with a filter $l$. The family is
**regular** if

* (a) there is a $\sigma \in \mathbb{R}$ such that every element $K$ of every $\mathcal{T}_i$
  contains a closed ball of some radius $r > 0$ with
  $\operatorname{diam} K \le \sigma \cdot 2r$, and
* (b) the mesh parameter of $\mathcal{T}_i$ (`AtkinsonHan.Chapter10.meshSize`) tends to $0$
  along $l$.

**Reading.** The source states (a) as $h_K / \rho_K \le \sigma$, where
$h_K = \operatorname{diam} K$ and $\rho_K$ is the diameter of the largest ball inscribed in $K$.
The largest inscribed ball need not exist for a general set, and (a) uses $\rho_K$ only through
$h_K \le \sigma \rho_K$; so the definition asks for some inscribed ball of diameter $2r$. When
the largest inscribed ball exists, as for a triangle, the two readings agree. The source indexes
the family by $h$ and lets $h \to 0$; here the index type and the filter are arbitrary.

The partition axioms of Section 10.2 (the elements cover $\overline\Omega$, have disjoint
interiors and meet face to face) play no part in the definition, so a member of the family is
any collection of sets. Regularity turns the local estimate (10.3.7), which has both $h_K$ and
$\rho_K$, into a bound in $h_K$ alone (Corollary 10.3.7). -/
def IsRegularFamily {ι : Type*} (l : Filter ι)
    (T : ι → Set (Set (EuclideanSpace ℝ (Fin d)))) : Prop :=
  (∃ σ : ℝ, ∀ i, ∀ K ∈ T i, ∃ (c : EuclideanSpace ℝ (Fin d)) (r : ℝ),
      0 < r ∧ Metric.closedBall c r ⊆ K ∧ Metric.diam K ≤ σ * (2 * r)) ∧
    Tendsto (fun i => meshSize (T i)) l (𝓝 0)

/-- A family is regular in the sense of `AtkinsonHan.Chapter10.IsRegularFamily` if and only if it is
regular in the sense of the backbone, `FiniteElement.IsRegularFamily`. The two definitions
agree, since `AtkinsonHan.Chapter10.meshSize` is the supremum of the diameters that the backbone
writes out. -/
theorem isRegularFamily_iff_isRegularFamily {ι : Type*} {l : Filter ι}
    {T : ι → Set (Set (EuclideanSpace ℝ (Fin d)))} :
    IsRegularFamily l T ↔ FiniteElement.IsRegularFamily l T :=
  Iff.rfl

/-!
### Exercise 10.3.3: regularity and the minimal angle

The exercise is about triangles. For a triangle, $\rho_K$ is the diameter $2\rho$ of the inscribed
circle, where $\rho$ is `Affine.Simplex.inradius`. The statement below is therefore condition (a) of
Definition 10.3.6 for a family of triangles with the actual inradius, in place of the weaker form
with some inscribed ball that `AtkinsonHan.Chapter10.IsRegularFamily` uses for arbitrary sets.
-/

/-- **Exercise 10.3.3** of [han2009theoretical]. Let $\{K_t\}$ be a family of triangles in
$\mathbb{R}^2$, with diameter $h_K$ and inradius $\rho$. There is a $\sigma$ with
$h_K \le \sigma \cdot 2\rho$ for every triangle of the family if and only if there is an
$\alpha > 0$ such that every angle of every triangle of the family is at least $\alpha$.

Both directions are quantitative: a bound $h_K \le \sigma \rho_K$ gives every angle at least
$\arcsin(1 / (2\sigma))$, and a lower bound $\alpha$ on all angles gives
$h_K \le (3 / \sin^2 \alpha) \rho_K$. A triangle is an
`Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2`, its diameter is the diameter of its vertex set,
and its angles are `Affine.Simplex.triangleAngle`. -/
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

/-! ### Theorem 10.3.4: the affine change of variables -/

section Theorem1034

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- **Theorem 10.3.4** of [han2009theoretical] (affine change of variables in $H^m$). Let
$\hat K, K \subseteq \mathbb{R}^d$ be open, let $T$ be an invertible linear map of
$\mathbb{R}^d$ and $b \in \mathbb{R}^d$, and let $F(\hat x) = T\hat x + b$ map $\hat K$ onto
$K$. Let $m \ge 0$, let $v$ be a function on $\mathbb{R}^d$, and put $\hat v = v \circ F$. Then
$v \in H^m(K)$ if and only if $\hat v \in H^m(\hat K)$, and if $v \in H^m(K)$, then
$$|\hat v|_{m,\hat K} \le \|T\|^m |\det T|^{-1/2} |v|_{m,K}, \qquad (10.3.5)$$
$$|v|_{m,K} \le \|T^{-1}\|^m |\det T|^{1/2} |\hat v|_{m,\hat K}. \qquad (10.3.6)$$

The source has a constant $c$ in both bounds, which it does not specify, for its seminorm built
from multi-indices. For the tensor seminorm `sobolevSeminorm` the constant is $1$, and this is
what is proved. The seminorm is the $L^2$ norm of the operator norm of $\partial^m v$, and
$\partial^m \hat v(\hat x) = \partial^m v(F\hat x) \circ (T, \dots, T)$ has operator norm at
most $\|T\|^m \|\partial^m v(F\hat x)\|$; the change of variables $x = F\hat x$ in the integral
gives the factor $|\det T|^{-1/2}$. The bound (10.3.6) is (10.3.5) for $F^{-1}$.

$H^m(K)$ is `AtkinsonHan.Chapter07.definition_7_2_2 m 2 K`. $\|T\|$ is the operator norm on
Euclidean $\mathbb{R}^d$, and $\det T$ is `LinearMap.det`. The proof uses
`memSobolev_comp_affine_iff`, `sobolevSeminorm_comp_affine_le_of_image` and
`sobolevSeminorm_le_comp_affine_of_image`.

**Reading.** Tensor operator seminorm gives exact factor 1 rather than the unspecified multi-index
constant.
-/
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

/-- **Theorem 10.3.3** of [han2009theoretical] (the interpolation error on the reference element).
Let $\hat K \subseteq \mathbb{R}^d$ be a bounded, connected open set that is a Sobolev extension
domain for every exponent. Let $k, m \ge 0$ be integers with $m \le k + 1$ and $k + 1 > d/2$.
Let $\hat x_1, \dots, \hat x_I \in \overline{\hat K}$ be nodes and $\hat\varphi_1, \dots,
\hat\varphi_I \in H^m(\hat K)$ shape functions, and let $\hat\Pi$ be the interpolation operator
(10.3.1). Assume the polynomial invariance (10.3.4): $\hat\Pi q = q$ on $\hat K$ for every
polynomial $q$ of degree at most $k$. Then there is a constant $c \ge 0$ such that
$$|\hat v - \hat\Pi \hat v|_{m,\hat K} \le c |\hat v|_{k+1,\hat K} \qquad (10.3.3)$$
for every $\hat v \in H^{k+1}(\hat K)$ that is continuous on $\overline{\hat K}$.

**Generalization.** The source takes a triangle as the reference element, with $k > 0$, which is
the condition $k + 1 > d/2$ for $d = 2$. The library proves the estimate on any bounded
connected Sobolev extension domain in $\mathbb{R}^d$, because no extension operator for a
general Lipschitz domain is formalized. The reference triangle is one
(`isSobolevExtensionDomainAll_referenceTriangle`), and so is the unit square
(`isSobolevExtensionDomainAll_unitSquare`).

**Reading.** The values $\hat v(\hat x_i)$ at nodes on the boundary are defined for the
representative of $\hat v$ that is continuous up to the boundary. Every element of
$H^{k+1}(\hat K)$ has one, by the embedding $H^{k+1}(\hat K) \hookrightarrow C(\overline{\hat
K})$ of Theorem 7.3.7 (c)
(`SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order`). The statement takes
this representative, as the hypothesis `ContinuousOn v (closure Khat)`.

The seminorms are the tensor seminorms `sobolevSeminorm`, as in Theorem 10.3.4. The proof is
that of the source: $\hat\Pi$ is bounded from $H^{k+1}(\hat K)$ to $H^m(\hat K)$ through the
embedding and fixes $\mathbb{P}_k$, so $|\hat v - \hat\Pi \hat v|_{m,\hat K} \le c \inf_{q \in
\mathbb{P}_k} \|\hat v + q\|_{k+1,\hat K}$, and Corollary 7.3.18
(`SobolevEuclidean.exists_ciInf_norm_add_le_mul_topSeminorm`) bounds the infimum by
$|\hat v|_{k+1,\hat K}$. The statement is `FiniteElement.sobolevSeminorm_sub_nodalInterp_le`. -/
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

/-- **Theorem 10.3.5** of [han2009theoretical] (the local interpolation error estimate (10.3.7)).
Let the reference element $\hat K$, the integers $k$ and $m$, the nodes $\hat x_i$ and the shape
functions $\hat\varphi_i$ satisfy the hypotheses of Theorem 10.3.3, and let $\hat K$ contain a
closed ball of diameter $\hat\rho > 0$. Then there is a constant $c \ge 0$ with the following
property. Let $K \subseteq \mathbb{R}^d$ be open, let $F_K(\hat x) = T_K \hat x + b_K$ with
$T_K$ invertible map $\hat K$ onto $K$, and let $K$ contain a closed ball of diameter
$\rho_K > 0$. Let $\Pi_K$ be the interpolation operator (10.3.2) with the nodes $F_K(\hat x_i)$
and the shape functions $\hat\varphi_i \circ F_K^{-1}$. Then
$$|v - \Pi_K v|_{m,K} \le c \, \frac{h_K^{k+1}}{\rho_K^m} \, |v|_{k+1,K}$$
for every $v \in H^{k+1}(K)$ that is continuous on $\overline K$, where
$h_K = \operatorname{diam} K$.

**Reading.** In the source, $\rho_K$ is the diameter of the largest ball inscribed in $K$. Here
it is the diameter of any inscribed closed ball, which gives the bound for the largest one when
it exists. As in Theorem 10.3.3, $v$ is taken on its representative that is continuous up to the
boundary.

The constant $c$ depends only on $\hat K$, $\hat\rho$ and $\hat\Pi$. The proof is that of the
source: Theorem 10.3.1 gives $(v - \Pi_K v) \circ F_K = \hat v - \hat\Pi \hat v$, the bound
(10.3.6) carries the left-hand side to $\hat K$, Theorem 10.3.3 bounds it there, (10.3.5)
carries $|\hat v|_{k+1,\hat K}$ back to $K$, and Lemma 10.2.2 gives $\|T_K\| \le h_K / \hat\rho$
and $\|T_K^{-1}\| \le \hat h / \rho_K$. The constant is $c = c_0 \hat h^m / \hat\rho^{k+1}$ with
the $c_0$ of (10.3.3). The statement is
`FiniteElement.sobolevSeminorm_sub_nodalInterp_comp_affine_le`. -/
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

/-- **Corollary 10.3.7** of [han2009theoretical] (the interpolation error on a regular family,
(10.3.10)). Let the reference element $\hat K$, the integers $k$ and $m$, the nodes $\hat x_i$
and the shape functions $\hat\varphi_i$ satisfy the hypotheses of Theorem 10.3.5, with an
inscribed closed ball of diameter $\hat\rho > 0$. Let $\{\mathcal{T}_h\}$ be a regular family of
partitions (Definition 10.3.6) whose elements have diameter at most $H$. Then there is a
constant $c \ge 0$ with the following property. Let $K$ be an element of some $\mathcal{T}_h$
that is open and is the image of $\hat K$ under $F_K(\hat x) = T_K \hat x + b_K$, with $T_K$
invertible, and let $\Pi_K$ be the interpolation operator with the nodes $F_K(\hat x_i)$ and the
shape functions $\hat\varphi_i \circ F_K^{-1}$. Then
$$\|v - \Pi_K v\|_{m,K} \le c \, h_K^{k+1-m} \, |v|_{k+1,K}$$
for every $v \in H^{k+1}(K)$ that is continuous on $\overline K$.

**Reading.** The source leaves the bound $h_K \le H$ implicit. Its constant depends on such a
bound through the seminorms of order $j < m$; the estimate for the seminorm of order $m$ alone
(Theorem 10.3.5) needs none. Every family with $h \to 0$ has such a bound once finitely many
coarse meshes are left out. As in Theorem 10.3.3, $v$ is taken on its representative that is
continuous up to the boundary.

Regularity gives $\rho_K \ge h_K / \sigma$, which turns the factor $h_K^{k+1} \rho_K^{-m}$ of
(10.3.7) into $\sigma^m h_K^{k+1-m}$. The norm $\|\cdot\|_{m,K}$ (`sobolevNorm`) is at most the
sum of the seminorms of orders $j \le m$ (`MemSobolev.sobolevNorm_le_sum_sobolevSeminorm`), and
Theorem 10.3.5 at order $j$ bounds each, with $h_K^{k+1-j} \le H^{m-j} h_K^{k+1-m}$. The
statement is `FiniteElement.sobolevNorm_sub_nodalInterp_comp_affine_le`. -/
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

/-!
### Example 10.3.8 on the unit square: the $Q_1$ element on parallelograms

Example 10.3.8 of the source is the linear element on triangles
(`AtkinsonHan.Chapter10.example_10_3_8` below). The unit square $(0, 1)^2$ is a Sobolev extension
domain as well (Remark 9 in Chapter 9 of [brezis2011functional],
`SobolevEuclidean.exists_extensionL_unitSquare`, `isSobolevExtensionDomainAll_unitSquare`), so the
estimate also holds for the $Q_1$ element on it. The nodes are the four vertices, the shape
functions are the bilinear functions $(1 \mp \hat x_1)(1 \mp \hat x_2)$ of Exercise 10.2.3, the
local space is $Q_1 \supseteq \mathbb{P}_1$, and the elements are the affine images of the square.
These are parallelograms; the rectangles are the case of a diagonal $T_K$.
-/

section Example1038Square

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- The unit square $(0, 1)^2$ is bounded. -/
theorem isBounded_unitSquare : Bornology.IsBounded (EuclideanSpace.rect 0 1 0 1 : Set 𝔼₂) :=
  Metric.isBounded_closedBall.subset (EuclideanSpace.rect_subset_closedBall 0 1 0 1)

/-- The open rectangle $(a_1, b_1) \times (a_2, b_2) \subseteq \mathbb{R}^2$ is convex.

It is the intersection of the preimages of two open intervals under the coordinate projections. -/
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

/-- Let $a_1 < b_1$ and $a_2 < b_2$. Every point $x \in \mathbb{R}^2$ with $a_1 \le x_1 \le b_1$ and
$a_2 \le x_2 \le b_2$ lies in the closure of the open rectangle $(a_1, b_1) \times (a_2, b_2)$.

The point $x$ is the limit of $x + t(c - x)$ as $t \to 0^+$, where $c$ is the centre of the
rectangle. -/
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

/-- The closed ball of radius $1/4$ about the centre $(1/2, 1/2)$ lies in the unit square
$(0, 1)^2$. It is an inscribed ball of diameter $\hat\rho = 1/2$. -/
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

/-- The four vertices $(0, 0)$, $(1, 0)$, $(0, 1)$ and $(1, 1)$ of the unit square, the **nodes of
the $Q_1$ element**, in the order of `AtkinsonHan.Chapter10.bilinearNode`. -/
noncomputable def q1Node : Fin 4 → 𝔼₂ := ![!₂[0, 0], !₂[1, 0], !₂[0, 1], !₂[1, 1]]

/-- The **shape functions of the $Q_1$ element** on the unit square: the bilinear functions
$(1 - \hat x_1)(1 - \hat x_2)$, $\hat x_1 (1 - \hat x_2)$, $(1 - \hat x_1) \hat x_2$ and
$\hat x_1 \hat x_2$.

These are `AtkinsonHan.Chapter10.bilinearShape` of Exercise 10.2.3, on
`EuclideanSpace ℝ (Fin 2)` in place of `ℝ × ℝ`. -/
noncomputable def q1Shape : Fin 4 → 𝔼₂ → ℝ :=
  ![fun x ↦ (1 - x 0) * (1 - x 1), fun x ↦ x 0 * (1 - x 1), fun x ↦ (1 - x 0) * x 1,
    fun x ↦ x 0 * x 1]

/-- The bilinear shape functions `AtkinsonHan.Chapter10.q1Shape` are nodal for the vertices
`AtkinsonHan.Chapter10.q1Node`: the $i$-th shape function is $1$ at the $i$-th vertex and $0$ at
the other three. -/
theorem q1Shape_isNodalBasis : Approximation.IsNodalBasis q1Node q1Shape where
  eval_self i := by fin_cases i <;> simp [q1Node, q1Shape]
  eval_of_ne i j hij := by
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | simp [q1Node, q1Shape]

/-- Each vertex `AtkinsonHan.Chapter10.q1Node i` lies in the closure of the unit square $(0, 1)^2$.
-/
theorem q1Node_mem_closure (i : Fin 4) :
    q1Node i ∈ closure (EuclideanSpace.rect 0 1 0 1 : Set 𝔼₂) := by
  refine mem_closure_rect zero_lt_one zero_lt_one ?_
  fin_cases i <;> simp [q1Node]

/-- Each bilinear shape function `AtkinsonHan.Chapter10.q1Shape i` is $C^\infty$ on $\mathbb{R}^2$.
-/
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

/-- Each bilinear shape function `AtkinsonHan.Chapter10.q1Shape i` lies in $H^m((0, 1)^2)$ for every
$m \ge 0$. -/
theorem memSobolev_q1Shape (m : ℕ) (i : Fin 4) :
    MemSobolev (q1Shape i) m 2 (EuclideanSpace.rect 0 1 0 1) volume :=
  ((contDiff_q1Shape i).of_le (by simp)).memSobolev_of_isBounded isBounded_unitSquare 2

/-- The $Q_1$ interpolant reproduces $\mathbb{P}_1$. Let $q$ be a polynomial in two variables of
total degree at most $1$, and let $\hat\Pi$ be nodal interpolation at the vertices
`AtkinsonHan.Chapter10.q1Node` with the shape functions `AtkinsonHan.Chapter10.q1Shape`. Then
$\hat\Pi q (x) = q(x)$ for every $x \in \mathbb{R}^2$.

This is the polynomial invariance (10.3.4) of the $Q_1$ element with $k = 1$. A polynomial of
degree at most $1$ is $c_0 + c_1 \hat x_1 + c_2 \hat x_2$, and the interpolant reproduces $1$,
$\hat x_1$ and $\hat x_2$. -/
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

/-- **Example 10.3.8** of [han2009theoretical], the $Q_1$ element on parallelograms. Let $m \le 2$,
and let $\{\mathcal{T}_h\}$ be a regular family (Definition 10.3.6) of collections of subsets of
$\mathbb{R}^2$ whose elements have diameter at most $H$. Then there is a constant $c \ge 0$ with
the following property. Let $K$ be an element of some $\mathcal{T}_h$ that is open and is the
image of the unit square $\hat K = (0, 1)^2$ under $F_K(\hat x) = T_K \hat x + b_K$, with $T_K$
invertible, and let $\Pi_K$ be the interpolation operator with the nodes $F_K(\hat x_i)$ at the
four transported vertices and the transported bilinear shape functions
$\hat\varphi_i \circ F_K^{-1}$. Then
$$\|v - \Pi_K v\|_{m,K} \le c \, h_K^{2-m} \, |v|_{2,K} \qquad (10.3.11)$$
for every $v \in H^2(K)$ that is continuous on $\overline K$.

The source states Example 10.3.8 for the linear element on triangles
(`AtkinsonHan.Chapter10.example_10_3_8`). This declaration is the same estimate for the local
space $Q_1(\hat K) \supseteq \mathbb{P}_1(\hat K)$ of the remark after Theorem 10.3.5.

This is Corollary 10.3.7 with $k = 1$ and $d = 2$, so that $k + 1 = 2 > d/2$. The unit square is
a Sobolev extension domain (`isSobolevExtensionDomainAll_unitSquare`), bounded and convex, and
contains the closed ball of radius $1/4$ about its centre. The vertices lie in its closure, the
shape functions are smooth, and the interpolant reproduces $\mathbb{P}_1$
(`AtkinsonHan.Chapter10.nodalInterp_q1_eval`).

**Reading.** Uses affine square images and Q₁ instead of triangles, continuous representative, m up
to 2 and explicit mesh bound.
-/
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

/-!
### Example 10.3.8: the linear element on triangles

The reference element is the reference triangle $\hat K = \{\hat x : \hat x_1 > 0, \hat x_2 > 0,
\hat x_1 + \hat x_2 < 1\}$ (`EuclideanSpace.referenceTriangle`). The nodes are its three vertices,
the shape functions are the barycentric coordinates $1 - \hat x_1 - \hat x_2$, $\hat x_1$,
$\hat x_2$ of Example 10.3.2 (`EuclideanSpace.baryCoord`), the local space is
$\hat X = \mathbb{P}_1(\hat K)$, and the elements are the affine images of $\hat K$, which are the
nondegenerate triangles. The reference triangle is a Sobolev extension domain for every exponent
(`isSobolevExtensionDomainAll_referenceTriangle`): two reflections and an affine change of variables
carry it to the unit square. So Corollary 10.3.7 applies to it.
-/

section Example1038

open MeasureTheory Set TopologicalSpace EuclideanSpace
open scoped ENNReal NNReal Topology

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- The barycentric coordinates `EuclideanSpace.baryCoord` are nodal for the vertices
`EuclideanSpace.referenceTriangleVertex` of the reference triangle: the $i$-th coordinate is $1$
at the $i$-th vertex and $0$ at the other two.

This is Example 10.3.2 for the reference triangle, with the explicit coordinates
$1 - \hat x_1 - \hat x_2$, $\hat x_1$, $\hat x_2$. It is
`EuclideanSpace.isNodalBasis_baryCoord`. -/
theorem baryCoord_isNodalBasis :
    Approximation.IsNodalBasis referenceTriangleVertex baryCoord :=
  isNodalBasis_baryCoord

/-- Each barycentric coordinate `EuclideanSpace.baryCoord i` lies in $H^m(\hat K)$ of the reference
triangle $\hat K$ for every $m \ge 0$. -/
theorem memSobolev_baryCoord (m : ℕ) (i : Fin 3) :
    MemSobolev (baryCoord i) m 2 referenceTriangle volume :=
  ((contDiff_baryCoord i).of_le (by simp)).memSobolev_of_isBounded isBounded_referenceTriangle 2

/-- The linear interpolant reproduces $\mathbb{P}_1$. Let $q$ be a polynomial in two variables of
total degree at most $1$, and let $\hat\Pi$ be nodal interpolation at the vertices of the
reference triangle with the barycentric coordinates as shape functions. Then
$\hat\Pi q (x) = q(x)$ for every $x \in \mathbb{R}^2$.

This is the polynomial invariance (10.3.4) of the linear element with $k = 1$, and the explicit
form of `AtkinsonHan.Chapter10.nodalInterp_coord_affineMap` on the reference triangle. -/
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

/-- **Example 10.3.8** of [han2009theoretical], the linear element on triangles. Let $m \le 2$, and
let $\{\mathcal{T}_h\}$ be a regular family (Definition 10.3.6) of collections of subsets of
$\mathbb{R}^2$ whose elements have diameter at most $H$. Then there is a constant $c \ge 0$ with
the following property. Let $K$ be an element of some $\mathcal{T}_h$ that is open and is the
image of the reference triangle $\hat K$ under $F_K(\hat x) = T_K \hat x + b_K$, with $T_K$
invertible, and let $\Pi_K$ be the interpolation operator with the three vertices
$F_K(\hat x_i)$ as nodes and the transported barycentric coordinates
$\hat\lambda_i \circ F_K^{-1}$ as shape functions, so that $X_K = \mathbb{P}_1(K)$. Then
$$\|v - \Pi_K v\|_{m,K} \le c \, h_K^{2-m} \, |v|_{2,K} \qquad (10.3.11)$$
for every $v \in H^2(K)$ that is continuous on $\overline K$.

**Generalization.** The source states (10.3.11) for $m = 0, 1$. The declaration also covers
$m = 2$.

**Reading.** As in Corollary 10.3.7, $v$ is taken on its representative that is continuous up to
the boundary, and the bound $h_K \le H$ on the diameters of the elements is a hypothesis.

This is Corollary 10.3.7 with $k = 1$ and $d = 2$, so that $k + 1 = 2 > d/2$. The reference
triangle is a Sobolev extension domain (`isSobolevExtensionDomainAll_referenceTriangle`),
bounded and convex, and contains the closed ball of radius $1/8$ about $(1/4, 1/4)$. The
vertices lie in its closure, the barycentric coordinates are smooth and nodal (Example 10.3.2),
and the interpolant reproduces $\mathbb{P}_1$
(`AtkinsonHan.Chapter10.nodalInterp_baryCoord_eval`). -/
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

/-!
### Theorem 10.3.9: the global interpolation error on a triangulation

A triangulation of a plane domain $\Omega$ is a `Triangulation Ω`: a finite set of nondegenerate
triangles with disjoint interiors, whose closures cover $\Omega$, and which meet edge to edge. Its
elements are the affine images $F_K(\hat K)$ of the reference triangle
(`Triangulation.image_referenceTriangle`). The local interpolant $\Pi_K v$ of (10.3.2) is
`Triangulation.localInterp`, with the transported nodes and shape functions of Corollary 10.3.7, and
the global interpolant $\Pi_h v$ with $\Pi_h v|_K = \Pi_K v$ is `Triangulation.globalInterp`, glued
from the local ones. The element is assumed to be conforming (`Triangulation.IsConformingElement`):
the local interpolants agree on common edges. This is the standing assumption
$X_h \subseteq C(\overline\Omega)$ of Section 10.2.3, which Example 10.2.3 verifies for the linear
element. Then $\Pi_h v$ is continuous on $\overline\Omega$ and lies in $H^1(\Omega)$
(`Triangulation.memSobolev_globalInterp`).
-/

section Theorem1039

open MeasureTheory Set TopologicalSpace EuclideanSpace
open scoped ENNReal NNReal Topology

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- For a triangulation $\mathcal{T}$ of $\Omega$, the mesh parameter
`AtkinsonHan.Chapter10.meshSize` of the collection of its open elements equals
`Triangulation.meshSize`. -/
theorem meshSize_range_K {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) :
    meshSize (Set.range 𝒯.K) = 𝒯.meshSize :=
  𝒯.meshSize_eq_sSup_image.symm

/-- Definition 10.3.6 for a family of triangulations. A family $\{\mathcal{T}_i\}$ of triangulations
of $\Omega \subseteq \mathbb{R}^2$, indexed by a type with a filter $l$, is regular
(`AtkinsonHan.Chapter10.IsRegularFamily` for the collections of open elements) if and only if

* (a) there is a $\sigma \in \mathbb{R}$ such that every element $K$ of every $\mathcal{T}_i$
  contains a closed ball of some radius $r > 0$ with
  $\operatorname{diam} K \le \sigma \cdot 2r$, and
* (b) the mesh parameters `Triangulation.meshSize` of the $\mathcal{T}_i$ tend to $0$ along $l$.

**Reading.** Mesh-family clause uses filter limits and closed-ball shape witnesses.
-/
theorem isRegularFamily_iff {Ω : Opens 𝔼₂} {ι : Type*} (l : Filter ι) (𝒯 : ι → Triangulation Ω) :
    IsRegularFamily l (fun i ↦ Set.range (𝒯 i).K) ↔
      (∃ σ : ℝ, ∀ i, ∀ T : (𝒯 i).elems, ∃ (c : 𝔼₂) (r : ℝ), 0 < r ∧
        Metric.closedBall c r ⊆ (𝒯 i).K T ∧ Metric.diam ((𝒯 i).K T) ≤ σ * (2 * r)) ∧
      Tendsto (fun i ↦ (𝒯 i).meshSize) l (𝓝 0) :=
  FiniteElement.isRegularFamily_range_K_iff l 𝒯

/-- **Theorem 10.3.9** of [han2009theoretical] (the global interpolation error (10.3.13)). Let
$\Omega \subseteq \mathbb{R}^2$ be open, let $k \ge 1$ and $m \le 1$, and let
$\{\mathcal{T}_h\}$ be a regular family of triangulations of $\Omega$ (Definition 10.3.6) with
mesh parameters at most $H$. Let the reference element be the reference triangle $\hat K$, with
nodes $\hat x_i \in \overline{\hat K}$ and $C^1$ shape functions $\hat\varphi_i$, and assume the
polynomial invariance $\hat\Pi q = q$ on $\hat K$ for every polynomial $q$ of degree at most
$k$. Let the element be conforming on every triangulation of the family. Then there is a
constant $c \ge 0$ such that
$$\|v - \Pi_h v\|_{m,\Omega} \le c \, h^{k+1-m} \, |v|_{k+1,\Omega}$$
for every triangulation of the family, with mesh parameter $h$, and every
$v \in H^{k+1}(\Omega)$ that is continuous on $\overline\Omega$.

**Reading.** The source assumes $X_h \subseteq C(\overline\Omega)$; here this is the hypothesis
that the element is conforming (`Triangulation.IsConformingElement`). As in Corollary 10.3.7,
$v$ is taken on its representative that is continuous up to the boundary, and the bound
$h \le H$ is a hypothesis.

The proof is that of the source: $\|v - \Pi_h v\|_{m,\Omega}^2 = \sum_K \|v - \Pi_K v\|_{m,K}^2$
(`Triangulation.sobolevNorm_rpow_eq_sum`), which needs $v - \Pi_h v \in H^m(\Omega)$ and hence
conformity for $m = 1$. Corollary 10.3.7 with $h_K \le h$ bounds each term, and
$\sum_K |v|_{k+1,K}^2 = |v|_{k+1,\Omega}^2$. The hypothesis $k + 1 > d/2$ of Corollary 10.3.7 is
$k \ge 1$ in the plane. The statement is `Triangulation.sobolevNorm_sub_globalInterp_le`. -/
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

/-- **Theorem 10.3.9** of [han2009theoretical] for the linear element of Example 10.3.8. Let
$\Omega \subseteq \mathbb{R}^2$ be open, let $m \le 1$, and let $\{\mathcal{T}_h\}$ be a regular
family of triangulations of $\Omega$ with mesh parameters at most $H$. Let $\Pi_h v$ be the
continuous piecewise linear interpolant of $v$ at the vertices. Then there is a constant
$c \ge 0$ such that
$$\|v - \Pi_h v\|_{m,\Omega} \le c \, h^{2-m} \, |v|_{2,\Omega}$$
for every triangulation of the family, with mesh parameter $h$, and every $v \in H^2(\Omega)$
that is continuous on $\overline\Omega$.

The linear element is conforming on every triangulation
(`Triangulation.isConformingElement_linear`, Example 10.2.3), and it reproduces $\mathbb{P}_1$
(`AtkinsonHan.Chapter10.nodalInterp_baryCoord_eval`), so this is
`AtkinsonHan.Chapter10.theorem_10_3_9` with $k = 1$.

**Reading.** Linear plane-triangle specialization with explicit mesh bound and continuous
representative.
-/
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

/-- **Theorem 10.3.9** of [han2009theoretical] for the $\mathbb{P}_k$ Lagrange element on the
principal lattice $\hat N_k$ of (10.2.24), the affine-equivalent finite element spaces of
piecewise polynomials of degree at most $k$ in the source. Let $\Omega \subseteq \mathbb{R}^2$
be open, let $k \ge 1$ and $m \le 1$, and let $\{\mathcal{T}_h\}$ be a regular family of
triangulations of $\Omega$ with mesh parameters at most $H$. Let $\Pi_h v$ be the continuous
piecewise $\mathbb{P}_k$ interpolant of $v$ at the lattice nodes. Then there is a constant
$c \ge 0$ such that
$$\|v - \Pi_h v\|_{m,\Omega} \le c \, h^{k+1-m} \, |v|_{k+1,\Omega}$$
for every triangulation of the family, with mesh parameter $h$, and every
$v \in H^{k+1}(\Omega)$ that is continuous on $\overline\Omega$.

The element is `LagrangeElement.node` and `LagrangeElement.shape`. It is conforming on every
triangulation and reproduces $\mathbb{P}_k$ (Proposition 10.2.1). The statement is
`LagrangeElement.sobolevNorm_sub_globalInterp_le`.

**Reading.** Plane-triangle principal-lattice specialization with explicit mesh bound and continuous
representative.
-/
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
