/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Measure
import Numlib.Analysis.Sobolev.Simplex
import Numlib.Approximation.NodalInterpolation

/-!
# Triangulations of a plane domain

Let $\Omega \subseteq \mathbb{R}^2$ be open. A **triangulation** of $\Omega$ in the sense of the
finite element method ([han2009theoretical], §10.2) is a finite family $\mathcal{T}_h = \{K\}$ of
nondegenerate triangles, the elements, such that (1) the closed elements cover $\overline{\Omega}$,
that is $\overline{\Omega} = \bigcup_{K \in \mathcal{T}_h} \overline{K}$; (2) each element is a
triangle; (3) distinct elements have disjoint interiors; and (4) two distinct closed elements meet
in the empty set, in a common vertex, or in a common side. Condition (4) is the regularity
condition: it says that the mesh is conforming. Every element $K$ with vertices $a_0, a_1, a_2$ is
the image of the reference triangle $\hat{K} = \{(x, y) : x > 0,\ y > 0,\ x + y < 1\}$ under the
affine map $F_K(\hat{x}) = T_K \hat{x} + b_K$, where $T_K \hat{x} = \hat{x}_0 (a_1 - a_0) +
\hat{x}_1 (a_2 - a_0)$ and $b_K = a_0$.

This module defines triangulations, the mesh parameter $h = \max_K \operatorname{diam} K$, the
vertex set, and the skeleton (the union of the boundaries of the elements). It shows that the open
elements fill $\Omega$ up to a null set, and that functions given element by element and compatible
on the overlaps glue to a function continuous on $\overline{\Omega}$. For a reference element with
nodes $\hat{x}_i$ and shape functions $\hat{\varphi}_i$, it defines the local interpolant $\Pi_K v =
\sum_i v(F_K \hat{x}_i)\, \hat{\varphi}_i \circ F_K^{-1}$ and the global interpolant $\Pi_h v$ with
$\Pi_h v|_K = \Pi_K v$. It proves that the linear element is conforming, and that on a polygonal
domain the global interpolant of a function that vanishes on $\partial\Omega$ vanishes on
$\partial\Omega$.

## Main definitions

* `EuclideanSpace.closedTriangle`: the closed triangle $\{A + s (B - A) + t (C - A) : s, t \ge 0,\
  s + t \le 1\}$.
* `EuclideanSpace.IsEdgeUnisolvent`: a reference element is edge unisolvent if an interpolant that
  vanishes at the nodes on a reference edge vanishes on that whole edge.
* `Triangulation`: a triangulation of an open set $\Omega \subseteq \mathbb{R}^2$.
* `Triangulation.K` and `Triangulation.closedK`: the open and the closed element with a given vertex
  triple.
* `Triangulation.linearPart`: the linear part $T_K$ of the affine map $F_K$.
* `Triangulation.meshSize`: the mesh parameter $h = \max_K \operatorname{diam} K$.
* `Triangulation.skeleton`: the union of the boundaries of the elements.
* `Triangulation.vertices`: the set of all vertices of the elements, the nodes of the linear
  element.
* `Triangulation.Compatible` and `Triangulation.glue`: a family of functions, one per element, that
  agree on the overlaps of the closed elements, and the function glued from them.
* `Triangulation.localInterp` and `Triangulation.globalInterp`: the local interpolant $\Pi_K$ and
  the global interpolant $\Pi_h$.
* `Triangulation.IsConformingElement`: the local interpolants of every function are compatible.
* `Triangulation.FrontierSubsetEdges`: $\partial\Omega$ is a union of edges of elements.

## Main results

* `EuclideanSpace.closure_openTriangle`: the closure of the open triangle is the closed triangle.
* `EuclideanSpace.frontier_openTriangle_subset`: the boundary of a nondegenerate triangle lies on
  its three edges.
* `Triangulation.closure_eq_iUnion_closedK`: $\overline{\Omega} = \bigcup_K \overline{K}$.
* `Triangulation.image_referenceTriangle`: $K = F_K(\hat{K})$.
* `Triangulation.skeleton_subset_iUnion_segment` and `Triangulation.volume_skeleton`: the skeleton
  lies on finitely many segments and is a null set.
* `Triangulation.exists_mem_K_of_notMem_skeleton`: every point of $\Omega$ off the skeleton lies in
  an open element.
* `Triangulation.ae_eq_iUnion_K`: the union of the open elements equals $\Omega$ up to a null set.
* `Triangulation.continuousOn_glue`: a compatible family of functions, each continuous on its closed
  element, glues to a function continuous on $\overline{\Omega}$.
* `Triangulation.localInterp_eq_nodalInterp_comp`: $\Pi_K v = \hat{\Pi}(v \circ F_K) \circ
  F_K^{-1}$.
* `Triangulation.continuousOn_globalInterp`: for a conforming element with continuous shape
  functions, $\Pi_h v$ is continuous on $\overline{\Omega}$.
* `Triangulation.globalInterp_eqOn_frontier`: if $\partial\Omega$ is a union of edges and the
  element is conforming and edge unisolvent, then $\Pi_h v = 0$ on $\partial\Omega$ whenever $v = 0$
  on $\partial\Omega$.
* `Triangulation.isConformingElement_linear`: the linear element is conforming.

## Implementation notes

* The elements are a `Finset` of vertex triples $T$ with values in `EuclideanSpace ℝ (Fin 2)`, not
  an indexed family. A family of triangulations `ι → Triangulation Ω` (a regular family of meshes
  with $h \to 0$) then needs no dependent index types. The type of elements is the subtype
  `𝒯.elems`, which is a `Fintype`. Two distinct triples that describe the same triangle are excluded
  by the disjointness of the open elements.
* The fields of `Triangulation` are the four conditions above, in a modified form. Condition (1) is
  split into "each open element lies in $\Omega$" and "$\Omega$ is covered by the closed elements".
  Together these give $\overline{\Omega} = \bigcup_K \overline{K}$
  (`Triangulation.closure_eq_iUnion_closedK`).
* Condition (4) is stated pointwise: every point common to two distinct closed elements is a common
  vertex or lies on an edge whose two ends are vertices of both elements. For nondegenerate
  triangles this is the trichotomy of the source. It is stated pointwise because that is the form in
  which it is used: the continuity across an edge of a piecewise polynomial whose pieces agree at
  the nodes of that edge.
* The open element is `EuclideanSpace.openTriangle` of `Numlib.Analysis.Sobolev.Simplex`. Every
  element is therefore a Sobolev extension domain, and the affine map $F_K$ is
  `EuclideanSpace.triangleEquiv` followed by a translation.
* The boundedness of $\Omega$ is not assumed. It follows from the existence of a triangulation
  (`Triangulation.isBounded`).
* The sums over the elements in `Numlib.Analysis.Sobolev.Triangulation` (the additivity of the
  Sobolev norm) rest on `Triangulation.ae_eq_iUnion_K` and `Triangulation.pairwise_disjoint_K`. The
  weak derivative of a piecewise $C^1$ function rests on
  `Triangulation.skeleton_subset_iUnion_segment`.
* `Triangulation.FrontierSubsetEdges` does not follow from the four conditions; its doc comment
  gives a counterexample. It is an extra hypothesis of `Triangulation.globalInterp_eqOn_frontier`.
-/

open EuclideanSpace Function Set Topology MeasureTheory TopologicalSpace

noncomputable section

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-! ### Closed triangles -/

namespace EuclideanSpace

/-- The **closed reference triangle** $\{(x, y) \in \mathbb{R}^2 : x \ge 0,\ y \ge 0,\ x + y \le
1\}$, the closure of the reference triangle `EuclideanSpace.referenceTriangle`. -/
def closedReferenceTriangle : Set 𝔼₂ := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}

/-- The closure of the reference triangle $\hat{K}$ is the closed reference triangle. -/
theorem closure_referenceTriangle_eq :
    closure (referenceTriangle : Set 𝔼₂) = closedReferenceTriangle :=
  closure_referenceTriangle

/-- The closed reference triangle is compact. -/
theorem isCompact_closedReferenceTriangle : IsCompact closedReferenceTriangle := by
  rw [← closure_referenceTriangle_eq]
  exact isBounded_referenceTriangle.isCompact_closure

/-- The **affine map** $x \mapsto A + x_0 (B - A) + x_1 (C - A)$ of $\mathbb{R}^2$, which carries
the reference triangle onto the triangle with vertices $A, B, C$. -/
def triangleAffine (A B C : 𝔼₂) : 𝔼₂ → 𝔼₂ := fun x ↦ A + x 0 • (B - A) + x 1 • (C - A)

/-- For all $A, B, C \in \mathbb{R}^2$, the open triangle with vertices $A, B, C$ is the image of
the reference triangle under the map $x \mapsto A + x_0 (B - A) + x_1 (C - A)$. -/
theorem openTriangle_eq_image_triangleAffine (A B C : 𝔼₂) :
    openTriangle A B C = triangleAffine A B C '' referenceTriangle :=
  rfl

/-- The map $x \mapsto A + x_0 (B - A) + x_1 (C - A)$ sends the vertices $(0, 0)$, $(1, 0)$,
$(0, 1)$ of the reference triangle to $A$, $B$, $C$. -/
theorem triangleAffine_referenceTriangleVertex (A B C : 𝔼₂) (a : Fin 3) :
    triangleAffine A B C (referenceTriangleVertex a) = ![A, B, C] a := by
  fin_cases a <;> simp [triangleAffine, referenceTriangleVertex]

/-- If $B - A$ and $C - A$ are linearly independent, then the map
$x \mapsto A + x_0 (B - A) + x_1 (C - A)$ is $x \mapsto L x + A$, where $L$ is the linear
equivalence `EuclideanSpace.triangleEquiv A B C h`. -/
theorem triangleAffine_eq (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) :
    triangleAffine A B C = fun x ↦ triangleEquiv A B C h x + A := by
  funext x
  rw [triangleAffine, triangleEquiv_apply]
  abel

/-- The map $x \mapsto A + x_0 (B - A) + x_1 (C - A)$ is continuous. -/
theorem continuous_triangleAffine (A B C : 𝔼₂) : Continuous (triangleAffine A B C) := by
  unfold triangleAffine
  fun_prop

/-- The map $F(x) = A + x_0 (B - A) + x_1 (C - A)$ preserves affine combinations: for all
$P, Q \in \mathbb{R}^2$ and $s \in \mathbb{R}$,
$$F(P + s (Q - P)) = F(P) + s (F(Q) - F(P)).$$
-/
theorem triangleAffine_lineMap (A B C : 𝔼₂) (P Q : 𝔼₂) (s : ℝ) :
    triangleAffine A B C (P + s • (Q - P))
      = triangleAffine A B C P + s • (triangleAffine A B C Q - triangleAffine A B C P) := by
  simp only [triangleAffine, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  module

/-- The **closed triangle** with vertices $A, B, C \in \mathbb{R}^2$:
$$\{A + s (B - A) + t (C - A) : s \ge 0,\ t \ge 0,\ s + t \le 1\}.$$

It is defined as the image of the closed reference triangle under the map
$x \mapsto A + x_0 (B - A) + x_1 (C - A)$. -/
def closedTriangle (A B C : 𝔼₂) : Set 𝔼₂ := triangleAffine A B C '' closedReferenceTriangle

/-- A point $x$ lies in the closed triangle with vertices $A, B, C$ if and only if
$x = A + s (B - A) + t (C - A)$ for some $s, t \ge 0$ with $s + t \le 1$. -/
theorem mem_closedTriangle {A B C x : 𝔼₂} :
    x ∈ closedTriangle A B C ↔
      ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t ≤ 1 ∧ x = A + s • (B - A) + t • (C - A) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y 0, y 1, hy.1, hy.2.1, hy.2.2, rfl⟩
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨!₂[s, t], ⟨hs, ht, hst⟩, rfl⟩

/-- The open triangle with vertices $A, B, C$ lies in the closed triangle with the same vertices. -/
theorem openTriangle_subset_closedTriangle (A B C : 𝔼₂) :
    openTriangle A B C ⊆ closedTriangle A B C := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, ⟨hy.1.le, hy.2.1.le, hy.2.2.le⟩, rfl⟩

/-- The closed triangle is compact. -/
theorem isCompact_closedTriangle (A B C : 𝔼₂) : IsCompact (closedTriangle A B C) :=
  isCompact_closedReferenceTriangle.image (continuous_triangleAffine A B C)

/-- The closed triangle is closed. -/
theorem isClosed_closedTriangle (A B C : 𝔼₂) : IsClosed (closedTriangle A B C) :=
  (isCompact_closedTriangle A B C).isClosed

/-- The closed triangle is bounded. -/
theorem isBounded_closedTriangle (A B C : 𝔼₂) : Bornology.IsBounded (closedTriangle A B C) :=
  (isCompact_closedTriangle A B C).isBounded

/-- The open triangle is bounded. -/
theorem isBounded_openTriangle (A B C : 𝔼₂) : Bornology.IsBounded (openTriangle A B C) :=
  (isBounded_closedTriangle A B C).subset (openTriangle_subset_closedTriangle A B C)

/-- **The closure of the open triangle is the closed triangle.** This holds for all
$A, B, C \in \mathbb{R}^2$, also when the three points are collinear. -/
theorem closure_openTriangle (A B C : 𝔼₂) :
    closure (openTriangle A B C) = closedTriangle A B C := by
  refine Subset.antisymm (closure_minimal (openTriangle_subset_closedTriangle A B C)
    (isClosed_closedTriangle A B C)) ?_
  rw [closedTriangle, ← closure_referenceTriangle_eq, openTriangle_eq_image_triangleAffine]
  exact image_closure_subset_closure_image (continuous_triangleAffine A B C)

/-- The vertices $A$, $B$ and $C$ lie in the closed triangle with vertices $A, B, C$. -/
theorem vertex_mem_closedTriangle (A B C : 𝔼₂) (a : Fin 3) :
    ![A, B, C] a ∈ closedTriangle A B C := by
  rw [← triangleAffine_referenceTriangleVertex]
  refine mem_image_of_mem _ ?_
  fin_cases a <;> simp [closedReferenceTriangle, referenceTriangleVertex]

/-- The open triangle is convex. -/
theorem convex_openTriangle (A B C : 𝔼₂) : Convex ℝ (openTriangle A B C) := by
  rw [openTriangle_eq_image_triangleAffine]
  have hlin : IsLinearMap ℝ fun x : 𝔼₂ ↦ x 0 • (B - A) + x 1 • (C - A) :=
    ⟨fun x y ↦ by simp only [PiLp.add_apply]; module,
      fun c x ↦ by simp only [PiLp.smul_apply, smul_eq_mul]; module⟩
  have : triangleAffine A B C = (fun y ↦ A + y) ∘ fun x : 𝔼₂ ↦ x 0 • (B - A) + x 1 • (C - A) := by
    funext x
    simp only [triangleAffine, Function.comp_apply]
    abel
  rw [this, image_comp]
  exact (convex_referenceTriangle.is_linear_image hlin).translate A

/-- **The boundary of the open triangle lies on its three edges.** If $B - A$ and $C - A$ are
linearly independent, then
$$\partial\,\triangle ABC \subseteq [A, B] \cup [B, C] \cup [C, A],$$
where $\triangle ABC$ is the open triangle and $[P, Q]$ is the closed segment from $P$ to $Q$. -/
theorem frontier_openTriangle_subset (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) :
    frontier (openTriangle A B C) ⊆ segment ℝ A B ∪ segment ℝ B C ∪ segment ℝ C A := by
  rw [(isOpen_openTriangle A B C h).frontier_eq, closure_openTriangle]
  rintro x ⟨hx, hx'⟩
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := mem_closedTriangle.1 hx
  have hnot : ¬ (0 < s ∧ 0 < t ∧ s + t < 1) := fun h' ↦
    hx' (mem_openTriangle.2 ⟨s, t, h'.1, h'.2.1, h'.2.2, rfl⟩)
  rcases hs.eq_or_lt with hs0 | hs0
  · -- `s = 0`: on the edge `CA`
    refine Or.inr ?_
    rw [segment_symm, segment_eq_image']
    exact ⟨t, ⟨ht, by linarith⟩, by rw [← hs0]; simp⟩
  rcases ht.eq_or_lt with ht0 | ht0
  · -- `t = 0`: on the edge `AB`
    refine Or.inl (Or.inl ?_)
    rw [segment_eq_image']
    exact ⟨s, ⟨hs, by linarith⟩, by rw [← ht0]; simp⟩
  · -- `s + t = 1`: on the edge `BC`
    have h1 : s + t = 1 := by
      by_contra h'
      exact hnot ⟨hs0, ht0, lt_of_le_of_ne hst h'⟩
    refine Or.inl (Or.inr ?_)
    rw [segment_eq_image']
    refine ⟨t, ⟨ht, by linarith⟩, ?_⟩
    have hs' : s = 1 - t := by linarith
    rw [hs']
    module

/-- The boundary of an open triangle has Lebesgue measure zero, as the boundary of every convex set
in $\mathbb{R}^2$ has. -/
theorem volume_frontier_openTriangle (A B C : 𝔼₂) :
    volume (frontier (openTriangle A B C)) = 0 :=
  Convex.addHaar_frontier volume (convex_openTriangle A B C)

/-- **Edge unisolvence** of a reference element. Let $\hat{x}_i$ be nodes and $\hat{\varphi}_i$ be
shape functions on the reference triangle, and let $\hat{\Pi} v = \sum_i v(\hat{x}_i)\,
\hat{\varphi}_i$ be the interpolant. The element is **edge unisolvent** if, for each edge
$[\hat{a}_j, \hat{a}_k]$ between two distinct vertices of the reference triangle and each
function $v$ that vanishes at the nodes on that edge, $\hat{\Pi} v$ vanishes on the whole edge.

This property makes the interpolant of a function that vanishes on the boundary of a polygon
vanish on that boundary (`Triangulation.globalInterp_eqOn_frontier`). The Lagrange elements are
edge unisolvent, by unisolvence in one variable along the edge ([han2009theoretical], Example
10.2.3). The interpolant is `Approximation.nodalInterp`. -/
def IsEdgeUnisolvent {I : ℕ} (xhat : Fin I → 𝔼₂) (φhat : Fin I → 𝔼₂ → ℝ) : Prop :=
  ∀ a b : Fin 3, a ≠ b → ∀ v : 𝔼₂ → ℝ,
    (∀ i, xhat i ∈ segment ℝ (referenceTriangleVertex a) (referenceTriangleVertex b) →
      v (xhat i) = 0) →
    ∀ y ∈ segment ℝ (referenceTriangleVertex a) (referenceTriangleVertex b),
      Approximation.nodalInterp xhat φhat v y = 0

end EuclideanSpace

/-! ### Triangulations -/

/-- A **triangulation** of an open set $\Omega \subseteq \mathbb{R}^2$ ([han2009theoretical],
§10.2). It consists of a finite set of nondegenerate triangles, each given by its three
vertices, such that the open triangles lie in $\Omega$ and are pairwise disjoint, the closed
triangles cover $\Omega$, and the triangles meet edge to edge: every point common to two
distinct closed triangles is a common vertex or lies on a common edge, that is, an edge whose
two ends are vertices of both triangles. -/
structure Triangulation (Ω : Opens 𝔼₂) where
  /-- The elements, each given by its vertex triple $(a_0, a_1, a_2)$. -/
  elems : Finset (Fin 3 → 𝔼₂)
  /-- Every element is nondegenerate: $a_1 - a_0$ and $a_2 - a_0$ are linearly independent. -/
  linearIndependent : ∀ T ∈ elems, LinearIndependent ℝ ![T 1 - T 0, T 2 - T 0]
  /-- Every open element lies in $\Omega$. -/
  openTriangle_subset : ∀ T ∈ elems, openTriangle (T 0) (T 1) (T 2) ⊆ Ω
  /-- The closed elements cover $\Omega$. -/
  subset_iUnion : (Ω : Set 𝔼₂) ⊆ ⋃ T ∈ elems, closedTriangle (T 0) (T 1) (T 2)
  /-- Distinct elements have disjoint open triangles. -/
  disjoint : ∀ T ∈ elems, ∀ T' ∈ elems, T ≠ T' →
    Disjoint (openTriangle (T 0) (T 1) (T 2)) (openTriangle (T' 0) (T' 1) (T' 2))
  /-- Conformity: if a point lies in the closed triangles of two distinct elements $T \ne T'$, then
  it is a vertex of $T$ that is also a vertex of $T'$, or it lies on a segment $[T_a, T_b]$ with
  $a \ne b$ whose two ends are vertices of $T'$. -/
  conforming : ∀ T ∈ elems, ∀ T' ∈ elems, T ≠ T' →
    ∀ x, x ∈ closedTriangle (T 0) (T 1) (T 2) → x ∈ closedTriangle (T' 0) (T' 1) (T' 2) →
      (∃ a b : Fin 3, x = T a ∧ T a = T' b) ∨
      (∃ a b a' b' : Fin 3, a ≠ b ∧ T a = T' a' ∧ T b = T' b' ∧ x ∈ segment ℝ (T a) (T b))

namespace Triangulation

variable {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω)

/-! ### Elements -/

/-- The **open element** $K$ with vertex triple $T = (a_0, a_1, a_2)$: the open triangle with
vertices $a_0, a_1, a_2$. -/
def K (T : 𝒯.elems) : Set 𝔼₂ := openTriangle (T.1 0) (T.1 1) (T.1 2)

/-- The **closed element** $\overline{K}$ with vertex triple $T = (a_0, a_1, a_2)$: the closed
triangle with vertices $a_0, a_1, a_2$. -/
def closedK (T : 𝒯.elems) : Set 𝔼₂ := closedTriangle (T.1 0) (T.1 1) (T.1 2)

/-- The vertices $a_0, a_1, a_2$ of an element are not collinear: $a_1 - a_0$ and $a_2 - a_0$ are
linearly independent. -/
theorem li (T : 𝒯.elems) : LinearIndependent ℝ ![T.1 1 - T.1 0, T.1 2 - T.1 0] :=
  𝒯.linearIndependent T.1 T.2

/-- The open element $K$, as an element of `TopologicalSpace.Opens`. -/
def Kopens (T : 𝒯.elems) : Opens 𝔼₂ := openTriangleOpens (T.1 0) (T.1 1) (T.1 2) (𝒯.li T)

/-- The underlying set of `Triangulation.Kopens` is the open element $K$. -/
@[simp]
theorem coe_Kopens (T : 𝒯.elems) : (𝒯.Kopens T : Set 𝔼₂) = 𝒯.K T := rfl

/-- The open element $K$ is open. -/
theorem isOpen_K (T : 𝒯.elems) : IsOpen (𝒯.K T) := (𝒯.Kopens T).isOpen

/-- The closure of the open element $K$ is the closed element $\overline{K}$. -/
theorem closure_K (T : 𝒯.elems) : closure (𝒯.K T) = 𝒯.closedK T :=
  closure_openTriangle _ _ _

/-- The closed element is closed. -/
theorem isClosed_closedK (T : 𝒯.elems) : IsClosed (𝒯.closedK T) := isClosed_closedTriangle _ _ _

/-- The closed element is compact. -/
theorem isCompact_closedK (T : 𝒯.elems) : IsCompact (𝒯.closedK T) :=
  isCompact_closedTriangle _ _ _

/-- The open element $K$ lies in the closed element $\overline{K}$. -/
theorem K_subset_closedK (T : 𝒯.elems) : 𝒯.K T ⊆ 𝒯.closedK T :=
  openTriangle_subset_closedTriangle _ _ _

/-- The open element is convex. -/
theorem convex_K (T : 𝒯.elems) : Convex ℝ (𝒯.K T) := convex_openTriangle _ _ _

/-- The open element is bounded. -/
theorem isBounded_K (T : 𝒯.elems) : Bornology.IsBounded (𝒯.K T) := isBounded_openTriangle _ _ _

/-- The open element lies in $\Omega$. -/
theorem K_subset (T : 𝒯.elems) : 𝒯.K T ⊆ Ω := 𝒯.openTriangle_subset T.1 T.2

/-- The open element, as an open set, lies in $\Omega$. -/
theorem Kopens_le (T : 𝒯.elems) : 𝒯.Kopens T ≤ Ω := 𝒯.K_subset T

/-- The closed element lies in $\overline{\Omega}$. -/
theorem closedK_subset_closure (T : 𝒯.elems) : 𝒯.closedK T ⊆ closure (Ω : Set 𝔼₂) := by
  rw [← 𝒯.closure_K]
  exact closure_mono (𝒯.K_subset T)

/-- The vertices $a_0, a_1, a_2$ of an element lie in its closed element. -/
theorem vertex_mem_closedK (T : 𝒯.elems) (a : Fin 3) : T.1 a ∈ 𝒯.closedK T := by
  have := vertex_mem_closedTriangle (T.1 0) (T.1 1) (T.1 2) a
  rwa [show ![T.1 0, T.1 1, T.1 2] a = T.1 a by fin_cases a <;> rfl] at this

/-- The closed elements cover $\Omega$: $\Omega \subseteq \bigcup_K \overline{K}$. -/
theorem subset_iUnion_closedK : (Ω : Set 𝔼₂) ⊆ ⋃ T, 𝒯.closedK T := fun x hx ↦ by
  obtain ⟨T, hT, hxT⟩ := mem_iUnion₂.1 (𝒯.subset_iUnion hx)
  exact mem_iUnion.2 ⟨⟨T, hT⟩, hxT⟩

/-- **The closure of the domain is the union of the closed elements:**
$$\overline{\Omega} = \bigcup_{K \in \mathcal{T}_h} \overline{K}.$$

This is condition (1) of the definition of a triangulation in [han2009theoretical], §10.2. -/
theorem closure_eq_iUnion_closedK : closure (Ω : Set 𝔼₂) = ⋃ T, 𝒯.closedK T :=
  Subset.antisymm (closure_minimal 𝒯.subset_iUnion_closedK
      (isClosed_iUnion_of_finite fun T ↦ 𝒯.isClosed_closedK T))
    (iUnion_subset fun T ↦ 𝒯.closedK_subset_closure T)

include 𝒯 in
/-- If $\Omega$ has a triangulation, then $\Omega$ is bounded. -/
theorem isBounded : Bornology.IsBounded (Ω : Set 𝔼₂) := by
  refine Bornology.IsBounded.subset ?_ 𝒯.subset_iUnion_closedK
  exact (Bornology.isBounded_iUnion (s := 𝒯.closedK)).2 fun T ↦ isBounded_closedTriangle _ _ _

include 𝒯 in
/-- If $\Omega$ has a triangulation, then $\overline{\Omega}$ is compact. -/
theorem isCompact_closure : IsCompact (closure (Ω : Set 𝔼₂)) :=
  𝒯.isBounded.isCompact_closure

/-- The open elements of distinct elements are disjoint. -/
theorem pairwise_disjoint_K : Pairwise (Disjoint on 𝒯.K) := fun T T' hTT' ↦
  𝒯.disjoint T.1 T.2 T'.1 T'.2 fun h ↦ hTT' (Subtype.ext h)

/-- The conformity condition, for elements $T \ne T'$ of the element type: a point $x$ in both
closed elements is a vertex of $T$ that is also a vertex of $T'$, or lies on a segment
$[T_a, T_b]$ with $a \ne b$ whose two ends are vertices of $T'$. -/
theorem conforming' {T T' : 𝒯.elems} (hTT' : T ≠ T') {x : 𝔼₂} (hx : x ∈ 𝒯.closedK T)
    (hx' : x ∈ 𝒯.closedK T') :
    (∃ a b : Fin 3, x = T.1 a ∧ T.1 a = T'.1 b) ∨
      (∃ a b a' b' : Fin 3, a ≠ b ∧ T.1 a = T'.1 a' ∧ T.1 b = T'.1 b' ∧
        x ∈ segment ℝ (T.1 a) (T.1 b)) :=
  𝒯.conforming T.1 T.2 T'.1 T'.2 (fun h ↦ hTT' (Subtype.ext h)) x hx hx'

/-! ### The affine map from the reference triangle -/

/-- The **linear part** $T_K \hat{x} = \hat{x}_0 (a_1 - a_0) + \hat{x}_1 (a_2 - a_0)$ of the affine
map that carries the reference triangle onto the element with vertices $a_0, a_1, a_2$, as a
continuous linear equivalence of $\mathbb{R}^2$. -/
def linearPart (T : 𝒯.elems) : 𝔼₂ ≃L[ℝ] 𝔼₂ :=
  triangleEquiv (T.1 0) (T.1 1) (T.1 2) (𝒯.li T)

/-- **The element is the affine image of the reference triangle.** Let $K$ be an element with
vertices $a_0, a_1, a_2$, let $T_K$ be its linear part and let $b_K = a_0$. Then
$K = F_K(\hat{K})$ for the affine map $F_K(\hat{x}) = T_K \hat{x} + b_K$.

This is the form in which the interpolation estimates of [han2009theoretical], §10.3, use the
element. The open element is written as `Triangulation.Kopens`. -/
theorem image_referenceTriangle (T : 𝒯.elems) :
    (fun x ↦ 𝒯.linearPart T x + T.1 0) '' referenceTriangle = 𝒯.Kopens T :=
  (openTriangle_eq_image _ _ _ (𝒯.li T)).symm

/-- The affine map $F_K(\hat{x}) = T_K \hat{x} + a_0$ of an element with vertices $a_0, a_1, a_2$ is
the map $\hat{x} \mapsto a_0 + \hat{x}_0 (a_1 - a_0) + \hat{x}_1 (a_2 - a_0)$. -/
theorem affine_eq_triangleAffine (T : 𝒯.elems) :
    (fun x ↦ 𝒯.linearPart T x + T.1 0) = triangleAffine (T.1 0) (T.1 1) (T.1 2) :=
  (triangleAffine_eq _ _ _ (𝒯.li T)).symm

/-- The affine map $F_K$ sends the vertices $(0, 0)$, $(1, 0)$, $(0, 1)$ of the reference triangle
to the vertices $a_0$, $a_1$, $a_2$ of the element. -/
theorem affine_referenceTriangleVertex (T : 𝒯.elems) (a : Fin 3) :
    𝒯.linearPart T (referenceTriangleVertex a) + T.1 0 = T.1 a := by
  rw [show 𝒯.linearPart T (referenceTriangleVertex a) + T.1 0
      = triangleAffine (T.1 0) (T.1 1) (T.1 2) (referenceTriangleVertex a) from
    congrFun (𝒯.affine_eq_triangleAffine T) _, triangleAffine_referenceTriangleVertex]
  fin_cases a <;> rfl

/-- The affine map $F_K$ maps the segment between two vertices $\hat{a}_j$ and $\hat{a}_k$ of the
reference triangle onto the edge between the vertices $a_j$ and $a_k$ of the element, with the
same parameter: for every $t \in \mathbb{R}$,
$$F_K(\hat{a}_j + t (\hat{a}_k - \hat{a}_j)) = a_j + t (a_k - a_j).$$
-/
theorem affine_vertex_lineMap (T : 𝒯.elems) (a b : Fin 3) (t : ℝ) :
    𝒯.linearPart T (referenceTriangleVertex a
      + t • (referenceTriangleVertex b - referenceTriangleVertex a)) + T.1 0
      = T.1 a + t • (T.1 b - T.1 a) := by
  rw [← 𝒯.affine_referenceTriangleVertex T a, ← 𝒯.affine_referenceTriangleVertex T b]
  simp only [map_add, map_smul, map_sub]
  module

/-- The map $y \mapsto T_K^{-1}(y - b_K)$ inverts the affine map $F_K$: $T_K^{-1}(F_K(x) - b_K) = x$
for every $x \in \mathbb{R}^2$. -/
theorem affine_symm (T : 𝒯.elems) (x : 𝔼₂) :
    (𝒯.linearPart T).symm (𝒯.linearPart T x + T.1 0 - T.1 0) = x := by simp

/-- The affine map $F_K$ maps the closed reference triangle onto the closed element $\overline{K}$.
-/
theorem image_closedReferenceTriangle (T : 𝒯.elems) :
    (fun x ↦ 𝒯.linearPart T x + T.1 0) '' closedReferenceTriangle = 𝒯.closedK T := by
  rw [affine_eq_triangleAffine]
  rfl

/-! ### The mesh parameter -/

/-- The **mesh parameter** $h = \max_{K \in \mathcal{T}_h} \operatorname{diam} K$
([han2009theoretical], (10.3.9)), the largest diameter of an element.

It is the supremum of the diameters of the open elements, so $h = 0$ when there are no elements. -/
def meshSize : ℝ := sSup (Set.range fun T ↦ Metric.diam (𝒯.K T))

/-- Every element has diameter at most the mesh parameter: $\operatorname{diam} K \le h$. -/
theorem diam_le_meshSize (T : 𝒯.elems) : Metric.diam (𝒯.K T) ≤ 𝒯.meshSize :=
  le_csSup (Set.finite_range _).bddAbove ⟨T, rfl⟩

/-- The mesh parameter is nonnegative: $h \ge 0$. -/
theorem meshSize_nonneg : 0 ≤ 𝒯.meshSize := by
  by_cases h : Nonempty 𝒯.elems
  · obtain ⟨T⟩ := h
    exact Metric.diam_nonneg.trans (𝒯.diam_le_meshSize T)
  · rw [not_nonempty_iff] at h
    rw [meshSize, Set.range_eq_empty, Real.sSup_empty]

/-- The mesh parameter is the supremum of $\operatorname{diam} S$ over the set
$\{K : K \in \mathcal{T}_h\}$ of the open elements, taken as a set of subsets of $\mathbb{R}^2$. -/
theorem meshSize_eq_sSup_image :
    𝒯.meshSize = sSup (Metric.diam '' Set.range 𝒯.K) := by
  rw [meshSize, ← Set.range_comp]
  rfl

/-! ### The skeleton -/

/-- The **skeleton** of the triangulation: the union $\bigcup_K \partial K$ of the boundaries of the
open elements. -/
def skeleton : Set 𝔼₂ := ⋃ T, frontier (𝒯.K T)

/-- The skeleton lies on the edges of the elements: it is contained in the union, over all elements
with vertices $a_0, a_1, a_2$ and all $j \in \{0, 1, 2\}$, of the segments $[a_j, a_{j+1}]$,
with the indices read modulo $3$. -/
theorem skeleton_subset_iUnion_segment :
    𝒯.skeleton ⊆ ⋃ p : 𝒯.elems × Fin 3, segment ℝ (p.1.1 p.2) (p.1.1 (p.2 + 1)) := by
  refine iUnion_subset fun T ↦ (frontier_openTriangle_subset _ _ _ (𝒯.li T)).trans ?_
  intro x hx
  rw [mem_iUnion]
  rcases hx with (hx | hx) | hx
  · exact ⟨(T, 0), hx⟩
  · exact ⟨(T, 1), hx⟩
  · exact ⟨(T, 2), hx⟩

/-- The skeleton has Lebesgue measure zero. -/
theorem volume_skeleton : volume 𝒯.skeleton = 0 :=
  measure_iUnion_null fun _ ↦ volume_frontier_openTriangle _ _ _

/-- The skeleton is closed. -/
theorem isClosed_skeleton : IsClosed 𝒯.skeleton :=
  isClosed_iUnion_of_finite fun _ ↦ isClosed_frontier

/-- **Off the skeleton, every point of the domain lies in an open element.** If $x \in \Omega$ and
$x$ is not in the skeleton, then $x \in K$ for some element $K$. -/
theorem exists_mem_K_of_notMem_skeleton {x : 𝔼₂} (hx : x ∈ Ω) (hS : x ∉ 𝒯.skeleton) :
    ∃ T, x ∈ 𝒯.K T := by
  obtain ⟨T, hT⟩ := mem_iUnion.1 (𝒯.subset_iUnion_closedK hx)
  refine ⟨T, ?_⟩
  by_contra hxK
  apply hS
  rw [skeleton, mem_iUnion]
  exact ⟨T, by rw [(𝒯.isOpen_K T).frontier_eq, closure_K]; exact ⟨hT, hxK⟩⟩

/-- The set $\Omega \setminus \bigcup_K K$ of the points of the domain outside every open element
has Lebesgue measure zero. -/
theorem volume_diff_iUnion_K : volume ((Ω : Set 𝔼₂) \ ⋃ T, 𝒯.K T) = 0 := by
  refine measure_mono_null (fun x hx ↦ ?_) 𝒯.volume_skeleton
  by_contra hS
  obtain ⟨T, hT⟩ := 𝒯.exists_mem_K_of_notMem_skeleton hx.1 hS
  exact hx.2 (mem_iUnion.2 ⟨T, hT⟩)

/-- **The open elements fill the domain up to a null set:** $\bigcup_K K$ and $\Omega$ are equal
almost everywhere for the Lebesgue measure. -/
theorem ae_eq_iUnion_K : (⋃ T, 𝒯.K T : Set 𝔼₂) =ᵐ[volume] (Ω : Set 𝔼₂) := by
  refine ae_eq_set.2 ⟨?_, 𝒯.volume_diff_iUnion_K⟩
  rw [sdiff_eq_empty.2 (iUnion_subset fun T ↦ 𝒯.K_subset T), measure_empty]

/-! ### The global nodes of the linear element -/

open Classical in
/-- The **vertex set** of the triangulation: the set of all vertices of all elements. These are the
nodes $x_i$ of the space of linear elements ([han2009theoretical], §10.2.1). -/
def vertices : Finset 𝔼₂ := 𝒯.elems.biUnion fun T ↦ Finset.univ.image T

/-- Every vertex of every element is in the vertex set. -/
theorem vertex_mem_vertices (T : 𝒯.elems) (a : Fin 3) : T.1 a ∈ 𝒯.vertices := by
  classical
  simp only [vertices, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨T.1, T.2, a, rfl⟩

/-- Every point of the vertex set is a vertex of some element. -/
theorem exists_vertex_of_mem_vertices {x : 𝔼₂} (hx : x ∈ 𝒯.vertices) :
    ∃ (T : 𝒯.elems) (a : Fin 3), T.1 a = x := by
  classical
  simp only [vertices, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and] at hx
  obtain ⟨T, hT, a, ha⟩ := hx
  exact ⟨⟨T, hT⟩, a, ha⟩

/-- The vertex set lies in $\overline{\Omega}$. -/
theorem vertices_subset_closure : (𝒯.vertices : Set 𝔼₂) ⊆ closure (Ω : Set 𝔼₂) := fun x hx ↦ by
  obtain ⟨T, a, rfl⟩ := 𝒯.exists_vertex_of_mem_vertices hx
  exact 𝒯.closedK_subset_closure T (𝒯.vertex_mem_closedK T a)

/-! ### Gluing functions defined element by element -/

/-- A family of functions $g_K \colon \mathbb{R}^2 \to \mathbb{R}$, one per element, is
**compatible** if $g_K(x) = g_{K'}(x)$ for all elements $K, K'$ and every
$x \in \overline{K} \cap \overline{K'}$.

The local interpolants of a conforming finite element are compatible: this is the content of the
continuity of the global interpolant ([han2009theoretical], Example 10.2.3). -/
def Compatible (g : 𝒯.elems → 𝔼₂ → ℝ) : Prop :=
  ∀ T T' : 𝒯.elems, ∀ x, x ∈ 𝒯.closedK T → x ∈ 𝒯.closedK T' → g T x = g T' x

open Classical in
/-- The **function glued from the pieces** $g_K$: at a point $x$ of some closed element
$\overline{K}$ its value is $g_K(x)$, and outside all closed elements its value is $0$.

When $x$ lies in several closed elements, the element is chosen by `Classical.choose`. For a
compatible family the choice does not matter (`Triangulation.glue_eq_of_mem_closedK`). -/
def glue (g : 𝒯.elems → 𝔼₂ → ℝ) : 𝔼₂ → ℝ := fun x ↦
  if h : ∃ T, x ∈ 𝒯.closedK T then g h.choose x else 0

/-- For a compatible family $(g_K)$, the glued function equals $g_K$ on each closed element
$\overline{K}$. -/
theorem glue_eq_of_mem_closedK {g : 𝒯.elems → 𝔼₂ → ℝ} (hg : 𝒯.Compatible g) (T : 𝒯.elems)
    {x : 𝔼₂} (hx : x ∈ 𝒯.closedK T) : 𝒯.glue g x = g T x := by
  have h : ∃ T, x ∈ 𝒯.closedK T := ⟨T, hx⟩
  rw [glue, dite_eq_left h]
  exact hg _ _ x h.choose_spec hx

/-- For a compatible family $(g_K)$, the glued function equals $g_K$ on each open element $K$. -/
theorem glue_eq_of_mem_K {g : 𝒯.elems → 𝔼₂ → ℝ} (hg : 𝒯.Compatible g) (T : 𝒯.elems)
    {x : 𝔼₂} (hx : x ∈ 𝒯.K T) : 𝒯.glue g x = g T x :=
  𝒯.glue_eq_of_mem_closedK hg T (𝒯.K_subset_closedK T hx)

/-- The glued function vanishes outside $\overline{\Omega}$. -/
theorem glue_eq_zero_of_notMem_closure {g : 𝒯.elems → 𝔼₂ → ℝ} {x : 𝔼₂}
    (hx : x ∉ closure (Ω : Set 𝔼₂)) : 𝒯.glue g x = 0 := by
  rw [glue, dite_eq_right]
  rintro ⟨T, hT⟩
  exact hx (𝒯.closedK_subset_closure T hT)

/-- **The glued function is continuous on the closure of the domain.** If the family $(g_K)$ is
compatible and each $g_K$ is continuous on its closed element $\overline{K}$, then the glued
function is continuous on $\overline{\Omega}$.

The proof is the pasting lemma for the finite closed cover
$\overline{\Omega} = \bigcup_K \overline{K}$. -/
theorem continuousOn_glue {g : 𝒯.elems → 𝔼₂ → ℝ} (hg : 𝒯.Compatible g)
    (hc : ∀ T, ContinuousOn (g T) (𝒯.closedK T)) :
    ContinuousOn (𝒯.glue g) (closure (Ω : Set 𝔼₂)) := by
  rw [𝒯.closure_eq_iUnion_closedK]
  refine (locallyFinite_of_finite _).continuousOn_iUnion (fun T ↦ 𝒯.isClosed_closedK T)
    fun T ↦ (hc T).congr fun x hx ↦ ?_
  exact 𝒯.glue_eq_of_mem_closedK hg T hx

/-! ### The global nodal interpolant -/

section Interpolant

variable {I : ℕ} (xhat : Fin I → 𝔼₂) (φhat : Fin I → 𝔼₂ → ℝ)

/-- The **local interpolation operator** $\Pi_K$ of an element $K$ ([han2009theoretical], (10.3.2)).
Let $\hat{x}_i$ be nodes and $\hat{\varphi}_i$ be shape functions on the reference triangle, and
let $F_K(\hat{x}) = T_K \hat{x} + b_K$ carry the reference triangle onto $K$, with $T_K$ the
linear part and $b_K$ the first vertex. Then $\Pi_K v$ is the nodal interpolant of $v$ at the
nodes $x_i^K = F_K(\hat{x}_i)$ with the shape functions
$\varphi_i^K = \hat{\varphi}_i \circ F_K^{-1}$:
$$\Pi_K v = \sum_i v(x_i^K)\, \varphi_i^K.$$
-/
def localInterp (T : 𝒯.elems) (v : 𝔼₂ → ℝ) : 𝔼₂ → ℝ :=
  Approximation.nodalInterp ((fun x ↦ 𝒯.linearPart T x + T.1 0) ∘ xhat)
    (fun i ↦ φhat i ∘ fun y ↦ (𝒯.linearPart T).symm (y - T.1 0)) v

/-- The local interpolant at a point $x$:
$$\Pi_K v(x) = \sum_i \hat{\varphi}_i(F_K^{-1} x)\, v(F_K \hat{x}_i).$$
-/
theorem localInterp_apply (T : 𝒯.elems) (v : 𝔼₂ → ℝ) (x : 𝔼₂) :
    𝒯.localInterp xhat φhat T v x
      = ∑ i, φhat i ((𝒯.linearPart T).symm (x - T.1 0)) * v (𝒯.linearPart T (xhat i) + T.1 0) := by
  simp [localInterp, Approximation.nodalInterp_apply]

/-- If the shape functions $\hat{\varphi}_i$ are nodal for the nodes $\hat{x}_i$, then on every
element the shape functions $\varphi_i^K = \hat{\varphi}_i \circ F_K^{-1}$ are nodal for the
nodes $x_i^K = F_K(\hat{x}_i)$, that is, $\varphi_i^K(x_j^K) = \delta_{ij}$
([han2009theoretical], §10.2.2). -/
theorem isNodalBasis_local (h : Approximation.IsNodalBasis xhat φhat) (T : 𝒯.elems) :
    Approximation.IsNodalBasis ((fun x ↦ 𝒯.linearPart T x + T.1 0) ∘ xhat)
      (fun i ↦ φhat i ∘ fun y ↦ (𝒯.linearPart T).symm (y - T.1 0)) :=
  h.comp fun x ↦ by simp

/-- If the shape functions $\hat{\varphi}_i$ are nodal for the nodes $\hat{x}_i$, then the local
interpolant reproduces the values at the nodes of the element: $\Pi_K v(x_i^K) = v(x_i^K)$ for
every $i$. -/
theorem localInterp_apply_node (h : Approximation.IsNodalBasis xhat φhat) (T : 𝒯.elems)
    (v : 𝔼₂ → ℝ) (i : Fin I) :
    𝒯.localInterp xhat φhat T v (𝒯.linearPart T (xhat i) + T.1 0)
      = v (𝒯.linearPart T (xhat i) + T.1 0) :=
  (𝒯.isNodalBasis_local xhat φhat h T).nodalInterp_apply_node v i

/-- If every shape function $\hat{\varphi}_i$ is of class $C^n$ on $\mathbb{R}^2$, where $n$ is a
natural number, $\infty$ or $\omega$, then for every function $v$ the local interpolant
$\Pi_K v$ is of class $C^n$ on $\mathbb{R}^2$. -/
theorem contDiff_localInterp {n : WithTop ℕ∞} (hφ : ∀ i, ContDiff ℝ n (φhat i)) (T : 𝒯.elems)
    (v : 𝔼₂ → ℝ) : ContDiff ℝ n (𝒯.localInterp xhat φhat T v) := by
  unfold localInterp Approximation.nodalInterp
  refine ContDiff.sum fun i _ ↦ ?_
  exact ((hφ i).comp ((𝒯.linearPart T).symm.contDiff.comp (contDiff_id.sub contDiff_const)))
    |>.smul contDiff_const

/-- Suppose that every shape function $\hat{\varphi}_i$ is affine along lines: $\hat{\varphi}_i(P +
s (Q - P)) = \hat{\varphi}_i(P) + s (\hat{\varphi}_i(Q) - \hat{\varphi}_i(P))$ for all
$P, Q \in \mathbb{R}^2$ and $s \in \mathbb{R}$. Then for every element $K$ and every function
$v$, the local interpolant $\Pi_K v$ is affine along lines in the same sense. -/
theorem localInterp_lineMap
    (hφ : ∀ i (P Q : 𝔼₂) (s : ℝ), φhat i (P + s • (Q - P)) = φhat i P + s * (φhat i Q - φhat i P))
    (T : 𝒯.elems) (v : 𝔼₂ → ℝ) (P Q : 𝔼₂) (s : ℝ) :
    𝒯.localInterp xhat φhat T v (P + s • (Q - P))
      = 𝒯.localInterp xhat φhat T v P
        + s * (𝒯.localInterp xhat φhat T v Q - 𝒯.localInterp xhat φhat T v P) := by
  have hF : (𝒯.linearPart T).symm (P + s • (Q - P) - T.1 0)
      = (𝒯.linearPart T).symm (P - T.1 0)
        + s • ((𝒯.linearPart T).symm (Q - T.1 0) - (𝒯.linearPart T).symm (P - T.1 0)) := by
    simp only [map_add, map_sub, map_smul]
    module
  simp only [localInterp_apply, hF, hφ, add_mul, sub_mul, mul_assoc, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- A **conforming element**: the reference element with nodes $\hat{x}_i$ and shape functions
$\hat{\varphi}_i$ is conforming on the triangulation if, for every function $v$, the local
interpolants $\Pi_K v$ form a compatible family, that is, they agree at every point common to
two closed elements.

Then the local interpolants glue to a function that is continuous on $\overline{\Omega}$. This
is the condition (10.2.6) of [han2009theoretical], §10.2.3. -/
def IsConformingElement : Prop :=
  ∀ v : 𝔼₂ → ℝ, 𝒯.Compatible fun T ↦ 𝒯.localInterp xhat φhat T v

/-- The **global interpolant** $\Pi_h v$ ([han2009theoretical], §10.3.4): the function glued from
the local interpolants $\Pi_K v$, so that $\Pi_h v|_K = \Pi_K v$ for a conforming element. -/
def globalInterp (v : 𝔼₂ → ℝ) : 𝔼₂ → ℝ :=
  𝒯.glue fun T ↦ 𝒯.localInterp xhat φhat T v

/-- For a conforming element, the global interpolant equals the local one on each closed element:
$\Pi_h v(x) = \Pi_K v(x)$ for $x \in \overline{K}$. -/
theorem globalInterp_eq_of_mem_closedK (h : 𝒯.IsConformingElement xhat φhat) (T : 𝒯.elems)
    (v : 𝔼₂ → ℝ) {x : 𝔼₂} (hx : x ∈ 𝒯.closedK T) :
    𝒯.globalInterp xhat φhat v x = 𝒯.localInterp xhat φhat T v x :=
  𝒯.glue_eq_of_mem_closedK (h v) T hx

/-- For a conforming element, the global interpolant equals the local one on each open element:
$\Pi_h v(x) = \Pi_K v(x)$ for $x \in K$. -/
theorem globalInterp_eq_of_mem_K (h : 𝒯.IsConformingElement xhat φhat) (T : 𝒯.elems)
    (v : 𝔼₂ → ℝ) {x : 𝔼₂} (hx : x ∈ 𝒯.K T) :
    𝒯.globalInterp xhat φhat v x = 𝒯.localInterp xhat φhat T v x :=
  𝒯.glue_eq_of_mem_K (h v) T hx

/-- **The global interpolant of a conforming element with continuous shape functions is continuous
on the closure of the domain.** If the element is conforming and every $\hat{\varphi}_i$ is
continuous, then $\Pi_h v$ is continuous on $\overline{\Omega}$ for every function $v$. -/
theorem continuousOn_globalInterp (h : 𝒯.IsConformingElement xhat φhat)
    (hφ : ∀ i, Continuous (φhat i)) (v : 𝔼₂ → ℝ) :
    ContinuousOn (𝒯.globalInterp xhat φhat v) (closure (Ω : Set 𝔼₂)) :=
  𝒯.continuousOn_glue (h v) fun T ↦ by
    unfold localInterp Approximation.nodalInterp
    refine (continuous_finsetSum _ fun i _ ↦ ?_).continuousOn
    exact ((hφ i).comp ((𝒯.linearPart T).symm.continuous.comp
      (continuous_id.sub continuous_const))).smul continuous_const

end Interpolant

/-! ### Edges, the boundary and edge unisolvence -/

section Edges

variable {I : ℕ} (xhat : Fin I → 𝔼₂) (φhat : Fin I → 𝔼₂ → ℝ)

/-- The segment between two vertices $a_j$ and $a_k$ of an element lies in its closed element. -/
theorem segment_subset_closedK (T : 𝒯.elems) (a b : Fin 3) :
    segment ℝ (T.1 a) (T.1 b) ⊆ 𝒯.closedK T := by
  have hc : Convex ℝ (𝒯.closedK T) := by
    rw [← 𝒯.closure_K]
    exact (𝒯.convex_K T).closure
  exact hc.segment_subset (𝒯.vertex_mem_closedK T a) (𝒯.vertex_mem_closedK T b)

/-- **The boundary of the domain is a union of element edges:** every point $x \in \partial\Omega$
lies on a segment $[a_j, a_k]$ between two distinct vertices of some element, and this whole
segment lies in $\partial\Omega$.

This is what "$\Omega$ is a polygonal domain triangulated by $\mathcal{T}_h$" means in
[han2009theoretical], §10.2. It is a hypothesis, not a consequence of the four conditions of
`Triangulation`. For a counterexample, take a triangulation of the closed square and a closed
segment $S$ that lies strictly inside an interior edge $[P, Q]$. The open square minus $S$
satisfies all four conditions, because the open elements do not meet $S$. But
$S \subseteq \partial\Omega$, and $S$ lies on no edge that is contained in $\partial\Omega$. The
property makes a piecewise polynomial that vanishes at the boundary nodes vanish on
$\partial\Omega$ (`Triangulation.globalInterp_eqOn_frontier`). -/
def FrontierSubsetEdges : Prop :=
  ∀ x ∈ frontier (Ω : Set 𝔼₂), ∃ (T : 𝒯.elems) (a b : Fin 3), a ≠ b ∧
    x ∈ segment ℝ (T.1 a) (T.1 b) ∧ segment ℝ (T.1 a) (T.1 b) ⊆ frontier (Ω : Set 𝔼₂)

/-- If every node $\hat{x}_i$ lies in the closed reference triangle, then every transported node
$F_K(\hat{x}_i)$ lies in the closed element $\overline{K}$. -/
theorem node_mem_closedK (hx : ∀ i, xhat i ∈ closure (referenceTriangle : Set 𝔼₂)) (T : 𝒯.elems)
    (i : Fin I) : 𝒯.linearPart T (xhat i) + T.1 0 ∈ 𝒯.closedK T := by
  rw [← 𝒯.image_closedReferenceTriangle, ← closure_referenceTriangle_eq]
  exact ⟨xhat i, hx i, rfl⟩

/-- **The local interpolant is the reference interpolant read through $F_K$:** for every function
$v$ and every $x \in \mathbb{R}^2$,
$$\Pi_K v(x) = \hat{\Pi}(v \circ F_K)(F_K^{-1} x),$$
where $\hat{\Pi}$ is the interpolant on the reference triangle. This is the relation $\Pi_K v =
\hat{\Pi}(v \circ F_K) \circ F_K^{-1}$ of [han2009theoretical], Theorem 10.3.1. -/
theorem localInterp_eq_nodalInterp_comp (T : 𝒯.elems) (v : 𝔼₂ → ℝ) (x : 𝔼₂) :
    𝒯.localInterp xhat φhat T v x
      = Approximation.nodalInterp xhat φhat (fun y ↦ v (𝒯.linearPart T y + T.1 0))
        ((𝒯.linearPart T).symm (x - T.1 0)) := by
  simp [localInterp_apply, Approximation.nodalInterp_apply]

/-- The global interpolant depends only on the values at the nodes of the elements: if
$v(F_K \hat{x}_i) = w(F_K \hat{x}_i)$ for every element $K$ and every $i$, then
$\Pi_h v = \Pi_h w$. -/
theorem globalInterp_congr {v w : 𝔼₂ → ℝ}
    (h : ∀ (T : 𝒯.elems) (i : Fin I),
      v (𝒯.linearPart T (xhat i) + T.1 0) = w (𝒯.linearPart T (xhat i) + T.1 0)) :
    𝒯.globalInterp xhat φhat v = 𝒯.globalInterp xhat φhat w := by
  unfold globalInterp
  congr 1
  funext T x
  simp only [localInterp_apply, h]

/-- The global interpolant of the zero function is zero: $\Pi_h 0 = 0$. -/
theorem globalInterp_zero : 𝒯.globalInterp xhat φhat 0 = 0 := by
  funext x
  simp only [globalInterp, glue, localInterp_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  split_ifs <;> rfl

/-- **Edge unisolvence along an element edge.** Suppose that the reference element is edge
unisolvent. Let $a_j$ and $a_k$ be two distinct vertices of an element $K$, and let $v$ vanish
on the segment $[a_j, a_k]$. Then $\Pi_K v$ vanishes on $[a_j, a_k]$.

The edge $[a_j, a_k]$ is the image under $F_K$ of the reference edge $[\hat{a}_j, \hat{a}_k]$,
with the same parameter (`Triangulation.affine_vertex_lineMap`). So the nodes on the edge are
the images of the reference nodes on the reference edge. -/
theorem localInterp_eq_zero_of_mem_segment (hunis : IsEdgeUnisolvent xhat φhat) (T : 𝒯.elems)
    {a b : Fin 3} (hab : a ≠ b) {v : 𝔼₂ → ℝ} (hv : ∀ x ∈ segment ℝ (T.1 a) (T.1 b), v x = 0)
    {x : 𝔼₂} (hx : x ∈ segment ℝ (T.1 a) (T.1 b)) : 𝒯.localInterp xhat φhat T v x = 0 := by
  rw [localInterp_eq_nodalInterp_comp]
  rw [segment_eq_image'] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  have hF : (𝒯.linearPart T).symm (T.1 a + s • (T.1 b - T.1 a) - T.1 0)
      = referenceTriangleVertex a
        + s • (referenceTriangleVertex b - referenceTriangleVertex a) := by
    rw [← 𝒯.affine_vertex_lineMap T a b s, 𝒯.affine_symm]
  rw [hF]
  refine hunis a b hab _ (fun i hi ↦ ?_) _ ?_
  · rw [segment_eq_image'] at hi
    obtain ⟨t, ht, hti⟩ := hi
    rw [← hti, 𝒯.affine_vertex_lineMap]
    refine hv _ ?_
    rw [segment_eq_image']
    exact ⟨t, ht, rfl⟩
  · rw [segment_eq_image']
    exact ⟨s, hs, rfl⟩

/-- **A piecewise polynomial that vanishes at the boundary nodes vanishes on the boundary.** Suppose
that $\partial\Omega$ is a union of element edges (`Triangulation.FrontierSubsetEdges`), and
that the reference element is conforming and edge unisolvent. If $v = 0$ on $\partial\Omega$,
then $\Pi_h v = 0$ on $\partial\Omega$.

A boundary point lies on an edge contained in $\partial\Omega$. On that edge the global
interpolant is the local one, and the nodes on the edge are boundary points, where $v$ vanishes.
This is the boundary half of the inclusion $V_h \subseteq H_0^1(\Omega)$ ([han2009theoretical],
Example 10.4.2; [quarteroni2000numerical], (12.94)). -/
theorem globalInterp_eqOn_frontier (hedge : 𝒯.FrontierSubsetEdges)
    (hconf : 𝒯.IsConformingElement xhat φhat) (hunis : IsEdgeUnisolvent xhat φhat) {v : 𝔼₂ → ℝ}
    (hv : EqOn v 0 (frontier (Ω : Set 𝔼₂))) :
    EqOn (𝒯.globalInterp xhat φhat v) 0 (frontier (Ω : Set 𝔼₂)) := by
  intro x hx
  obtain ⟨T, a, b, hab, hxs, hseg⟩ := hedge x hx
  rw [𝒯.globalInterp_eq_of_mem_closedK xhat φhat hconf T v (𝒯.segment_subset_closedK T a b hxs),
    Pi.zero_apply]
  exact 𝒯.localInterp_eq_zero_of_mem_segment xhat φhat hunis T hab (fun y hy ↦ hv (hseg hy)) hxs

end Edges

/-! ### The linear element -/

section Linear

/-- The barycentric coordinates $\lambda_0 = 1 - x - y$, $\lambda_1 = x$, $\lambda_2 = y$ of the
reference triangle are nodal for its vertices $(0, 0)$, $(1, 0)$, $(0, 1)$:
$\lambda_i(\hat{a}_j) = \delta_{ij}$. -/
theorem _root_.EuclideanSpace.isNodalBasis_baryCoord :
    Approximation.IsNodalBasis referenceTriangleVertex baryCoord where
  eval_self i := by rw [baryCoord_apply_vertex, ite_eq_left rfl]
  eval_of_ne i j hij := by rw [baryCoord_apply_vertex, ite_eq_right hij]

/-- The barycentric coordinates of the reference triangle are affine along lines: $\lambda_i(P + s
(Q - P)) = \lambda_i(P) + s (\lambda_i(Q) - \lambda_i(P))$ for all $P, Q \in \mathbb{R}^2$ and
$s \in \mathbb{R}$. -/
theorem _root_.EuclideanSpace.baryCoord_lineMap (i : Fin 3) (P Q : 𝔼₂) (s : ℝ) :
    baryCoord i (P + s • (Q - P)) = baryCoord i P + s * (baryCoord i Q - baryCoord i P) := by
  fin_cases i
  · simp [baryCoord]; ring
  · simp [baryCoord]
  · simp [baryCoord]

/-- The local interpolant of the linear element reproduces the values at the vertices:
$\Pi_K v(a_j) = v(a_j)$ for every vertex $a_j$ of $K$. -/
theorem localInterp_linear_vertex (T : 𝒯.elems) (v : 𝔼₂ → ℝ) (a : Fin 3) :
    𝒯.localInterp referenceTriangleVertex baryCoord T v (T.1 a) = v (T.1 a) := by
  have := 𝒯.localInterp_apply_node referenceTriangleVertex baryCoord isNodalBasis_baryCoord T v a
  rwa [𝒯.affine_referenceTriangleVertex T a] at this

/-- **The linear element is conforming** ([han2009theoretical], Example 10.2.3): the reference
element with the vertices of the reference triangle as nodes and the barycentric coordinates as
shape functions is conforming on every triangulation. That is, its local interpolants agree at
every point common to two closed elements.

At a common vertex both interpolants take the value of $v$ there. Along a common edge both are
affine functions of one variable that agree at the two ends of the edge, so they are equal. -/
theorem isConformingElement_linear :
    𝒯.IsConformingElement referenceTriangleVertex baryCoord := by
  intro v T T' x hx hx'
  dsimp only
  by_cases hTT' : T = T'
  · subst hTT'; rfl
  rcases 𝒯.conforming' hTT' hx hx' with ⟨a, b, rfl, hab⟩ | ⟨a, b, a', b', -, ha, hb, hseg⟩
  · rw [𝒯.localInterp_linear_vertex, hab, 𝒯.localInterp_linear_vertex]
  · rw [segment_eq_image'] at hseg
    obtain ⟨s, -, rfl⟩ := hseg
    rw [𝒯.localInterp_lineMap _ _ baryCoord_lineMap, 𝒯.localInterp_lineMap _ _ baryCoord_lineMap,
      𝒯.localInterp_linear_vertex, 𝒯.localInterp_linear_vertex, ha, hb,
      𝒯.localInterp_linear_vertex, 𝒯.localInterp_linear_vertex]

end Linear

end Triangulation

end
