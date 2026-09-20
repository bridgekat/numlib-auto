import Mathlib.Analysis.Convex.Measure
import Numlib.Analysis.Sobolev.Simplex
import Numlib.Approximation.NodalInterpolation

/-!
# Triangulations of a plane domain

A **triangulation** of a bounded open set `Ω ⊆ ℝ²` in the sense of the finite element method
([han2009theoretical] §10.2): a finite family `𝒯_h = {K}` of nondegenerate triangles such that

1. the closed elements cover `Ω̄` (`Ω̄ = ⋃_{K ∈ 𝒯_h} K`),
2. each element is a triangle,
3. distinct elements have disjoint interiors,
4. two distinct closed elements meet in the empty set, a common vertex, or a common side
   ("the regularity condition", the mesh is *conforming*).

`Triangulation Ω` records the elements as a finite set of vertex triples `T : Fin 3 → ℝ²`, and
its fields are the four properties, with (1) split into "each open element lies in `Ω`" and
"`Ω` is covered by the closed elements" (the two together give `Ω̄ = ⋃ K̄`,
`Triangulation.closure_eq_iUnion_closedK`), and (4) read pointwise: every point of the
intersection of two closed elements is a common vertex or lies on a common edge, which for
nondegenerate triangles is the book's trichotomy. The open element is
`EuclideanSpace.openTriangle` of `Numlib/Analysis/Sobolev/Simplex.lean`, so every element is a
Sobolev extension domain and the affine map `F_K` of the reference element technique is
`EuclideanSpace.triangleEquiv` followed by a translation (`Triangulation.image_referenceTriangle`).

## Main definitions

* `EuclideanSpace.closedTriangle A B C` — the closed triangle
  `{A + s (B − A) + t (C − A) : s, t ≥ 0, s + t ≤ 1}`, the closure of the open one
  (`closure_openTriangle`), whose frontier lies on the three edges
  (`frontier_openTriangle_subset`).
* `Triangulation Ω` — the structure above; `𝒯.K T` and `𝒯.closedK T` are the open and closed
  elements, `𝒯.Kopens T` the open element as an `Opens`, `𝒯.linearPart T` the linear part of the
  affine map carrying the reference triangle onto `K`, `𝒯.meshSize` the mesh parameter
  `h = max_K diam K` (10.3.9), `𝒯.vertices` the global vertex set, the nodes of the linear
  element.
* `𝒯.skeleton` — the union of the frontiers of the elements, a finite union of segments
  (`skeleton_subset_iUnion_segment`) and a null set (`volume_skeleton`); off it every point of
  `Ω` lies in an open element (`exists_mem_K_of_notMem_skeleton`), so the open elements
  partition `Ω` up to a null set (`ae_eq_iUnion_K`).
* `𝒯.glue g` — the function equal to `g T` on each closed element, for a family
  `g : 𝒯.elems → ℝ² → ℝ` that is `Compatible` (the `g T` agree on the overlaps of the closed
  elements); it is continuous on `Ω̄` when each `g T` is continuous on its closed element
  (`continuousOn_glue`), by the pasting lemma over the finite closed cover.
* `𝒯.FrontierSubsetEdges` — the polygonal-domain hypothesis: `∂Ω` is a union of element edges.
  It does not follow from the four axioms (see its doc comment) and it is what makes a piecewise
  polynomial vanishing at the boundary nodes vanish on `∂Ω` (`globalInterp_eqOn_frontier`), for
  an `IsEdgeUnisolvent` reference element — one whose interpolant vanishes along a reference
  edge as soon as it vanishes at the nodes of that edge, as the Lagrange elements do.

## Implementation notes

The elements are a `Finset` of vertex triples rather than an indexed family, so that a family
of triangulations `ι → Triangulation Ω` (a regular family of meshes, `h → 0`) needs no dependent
index types; the element type is the subtype `𝒯.elems`, which is a `Fintype`. Two distinct
triples describing the same triangle are excluded by the disjointness of the open elements.

The conformity condition is stated pointwise because that is the form its consumer uses: the
continuity across an edge of a piecewise polynomial whose pieces agree at the nodes of that
edge. The sums over the elements in `Numlib/Analysis/Sobolev/Triangulation.lean` (the
additivity of the Sobolev norm) rest on `ae_eq_iUnion_K` and `pairwise_disjoint_K`; the weak
derivative of a piecewise-`C¹` function rests on `skeleton_subset_iUnion_segment`.
-/

open EuclideanSpace Function Set Topology MeasureTheory TopologicalSpace

noncomputable section

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-! ### Closed triangles -/

namespace EuclideanSpace

/-- **The closed reference triangle** `{(x, y) : x ≥ 0, y ≥ 0, x + y ≤ 1}`, the closure of
`referenceTriangle`. -/
def closedReferenceTriangle : Set 𝔼₂ := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}

/-- The closure of the reference triangle is the closed reference triangle. -/
theorem closure_referenceTriangle_eq :
    closure (referenceTriangle : Set 𝔼₂) = closedReferenceTriangle :=
  closure_referenceTriangle

/-- The closed reference triangle is compact. -/
theorem isCompact_closedReferenceTriangle : IsCompact closedReferenceTriangle := by
  rw [← closure_referenceTriangle_eq]
  exact isBounded_referenceTriangle.isCompact_closure

/-- **The affine map `x ↦ A + x₀ (B − A) + x₁ (C − A)`** carrying the reference triangle onto
the triangle with vertices `A, B, C`. -/
def triangleAffine (A B C : 𝔼₂) : 𝔼₂ → 𝔼₂ := fun x ↦ A + x 0 • (B - A) + x 1 • (C - A)

/-- The open triangle is the image of the reference triangle under `triangleAffine`. -/
theorem openTriangle_eq_image_triangleAffine (A B C : 𝔼₂) :
    openTriangle A B C = triangleAffine A B C '' referenceTriangle :=
  rfl

/-- `triangleAffine A B C` sends the vertices of the reference triangle to `A, B, C`. -/
theorem triangleAffine_referenceTriangleVertex (A B C : 𝔼₂) (a : Fin 3) :
    triangleAffine A B C (referenceTriangleVertex a) = ![A, B, C] a := by
  fin_cases a <;> simp [triangleAffine, referenceTriangleVertex]

/-- `triangleAffine A B C` is `x ↦ triangleEquiv A B C h x + A`. -/
theorem triangleAffine_eq (A B C : 𝔼₂) (h : LinearIndependent ℝ ![B - A, C - A]) :
    triangleAffine A B C = fun x ↦ triangleEquiv A B C h x + A := by
  funext x
  rw [triangleAffine, triangleEquiv_apply]
  abel

/-- `triangleAffine` is continuous. -/
theorem continuous_triangleAffine (A B C : 𝔼₂) : Continuous (triangleAffine A B C) := by
  unfold triangleAffine
  fun_prop

/-- `triangleAffine A B C` maps affine combinations to affine combinations. -/
theorem triangleAffine_lineMap (A B C : 𝔼₂) (P Q : 𝔼₂) (s : ℝ) :
    triangleAffine A B C (P + s • (Q - P))
      = triangleAffine A B C P + s • (triangleAffine A B C Q - triangleAffine A B C P) := by
  simp only [triangleAffine, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  module

/-- **The closed triangle with vertices `A, B, C`**,
`{A + s (B − A) + t (C − A) : s ≥ 0, t ≥ 0, s + t ≤ 1}`: the image of the closed reference
triangle under `triangleAffine A B C`. -/
def closedTriangle (A B C : 𝔼₂) : Set 𝔼₂ := triangleAffine A B C '' closedReferenceTriangle

/-- Membership of the closed triangle: the barycentric description with nonnegative weights. -/
theorem mem_closedTriangle {A B C x : 𝔼₂} :
    x ∈ closedTriangle A B C ↔
      ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t ≤ 1 ∧ x = A + s • (B - A) + t • (C - A) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y 0, y 1, hy.1, hy.2.1, hy.2.2, rfl⟩
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨!₂[s, t], ⟨hs, ht, hst⟩, rfl⟩

/-- The open triangle lies in the closed one. -/
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

/-- **The closure of the open triangle is the closed triangle.** -/
theorem closure_openTriangle (A B C : 𝔼₂) :
    closure (openTriangle A B C) = closedTriangle A B C := by
  refine Subset.antisymm (closure_minimal (openTriangle_subset_closedTriangle A B C)
    (isClosed_closedTriangle A B C)) ?_
  rw [closedTriangle, ← closure_referenceTriangle_eq, openTriangle_eq_image_triangleAffine]
  exact image_closure_subset_closure_image (continuous_triangleAffine A B C)

/-- The vertices lie in the closed triangle. -/
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

/-- **The frontier of the open triangle lies on its three edges.** -/
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

/-- The frontier of a triangle is a null set (the frontier of a convex set). -/
theorem volume_frontier_openTriangle (A B C : 𝔼₂) :
    volume (frontier (openTriangle A B C)) = 0 :=
  Convex.addHaar_frontier volume (convex_openTriangle A B C)

/-- **Edge unisolvence of a reference element**: the nodes `x̂ᵢ` and shape functions `φ̂ᵢ` on the
reference triangle are *edge unisolvent* when, on each edge `[x̂_a, x̂_b]` of the reference
triangle, the interpolant `Π̂ v = ∑ᵢ v(x̂ᵢ) φ̂ᵢ` of a function vanishing at the nodes lying on that
edge vanishes on the whole edge. It is what makes the interpolant of a function vanishing on the
boundary of a polygon vanish on that boundary (`Triangulation.globalInterp_eqOn_frontier`), the
Lagrange elements being edge unisolvent by one-variable unisolvence along the edge
([han2009theoretical] Example 10.2.3). -/
def IsEdgeUnisolvent {I : ℕ} (xhat : Fin I → 𝔼₂) (φhat : Fin I → 𝔼₂ → ℝ) : Prop :=
  ∀ a b : Fin 3, a ≠ b → ∀ v : 𝔼₂ → ℝ,
    (∀ i, xhat i ∈ segment ℝ (referenceTriangleVertex a) (referenceTriangleVertex b) →
      v (xhat i) = 0) →
    ∀ y ∈ segment ℝ (referenceTriangleVertex a) (referenceTriangleVertex b),
      Approximation.nodalInterp xhat φhat v y = 0

end EuclideanSpace

/-! ### Triangulations -/

/-- **A triangulation of a plane domain** `Ω ⊆ ℝ²` ([han2009theoretical] §10.2): a finite set
of nondegenerate triangles, given by their vertex triples, whose open elements lie in `Ω` and
are pairwise disjoint, whose closed elements cover `Ω`, and which meet edge to edge: every
point common to two distinct closed elements is a common vertex or lies on a common edge (an
edge whose two ends are vertices of both). -/
structure Triangulation (Ω : Opens 𝔼₂) where
  /-- The elements, each given by its three vertices. -/
  elems : Finset (Fin 3 → 𝔼₂)
  /-- Every element is a nondegenerate triangle. -/
  linearIndependent : ∀ T ∈ elems, LinearIndependent ℝ ![T 1 - T 0, T 2 - T 0]
  /-- Every open element lies in the domain. -/
  openTriangle_subset : ∀ T ∈ elems, openTriangle (T 0) (T 1) (T 2) ⊆ Ω
  /-- The closed elements cover the domain. -/
  subset_iUnion : (Ω : Set 𝔼₂) ⊆ ⋃ T ∈ elems, closedTriangle (T 0) (T 1) (T 2)
  /-- Distinct elements have disjoint interiors. -/
  disjoint : ∀ T ∈ elems, ∀ T' ∈ elems, T ≠ T' →
    Disjoint (openTriangle (T 0) (T 1) (T 2)) (openTriangle (T' 0) (T' 1) (T' 2))
  /-- Conformity: two distinct closed elements meet only at common vertices and along common
  edges. -/
  conforming : ∀ T ∈ elems, ∀ T' ∈ elems, T ≠ T' →
    ∀ x, x ∈ closedTriangle (T 0) (T 1) (T 2) → x ∈ closedTriangle (T' 0) (T' 1) (T' 2) →
      (∃ a b : Fin 3, x = T a ∧ T a = T' b) ∨
      (∃ a b a' b' : Fin 3, a ≠ b ∧ T a = T' a' ∧ T b = T' b' ∧ x ∈ segment ℝ (T a) (T b))

namespace Triangulation

variable {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω)

/-! #### Elements -/

/-- The open element with vertex triple `T`. -/
def K (T : 𝒯.elems) : Set 𝔼₂ := openTriangle (T.1 0) (T.1 1) (T.1 2)

/-- The closed element with vertex triple `T`. -/
def closedK (T : 𝒯.elems) : Set 𝔼₂ := closedTriangle (T.1 0) (T.1 1) (T.1 2)

/-- The vertices of an element are not collinear. -/
theorem li (T : 𝒯.elems) : LinearIndependent ℝ ![T.1 1 - T.1 0, T.1 2 - T.1 0] :=
  𝒯.linearIndependent T.1 T.2

/-- The open element, as an open set. -/
def Kopens (T : 𝒯.elems) : Opens 𝔼₂ := openTriangleOpens (T.1 0) (T.1 1) (T.1 2) (𝒯.li T)

/-- The underlying set of the open element, as an open set, is the open element. -/
@[simp]
theorem coe_Kopens (T : 𝒯.elems) : (𝒯.Kopens T : Set 𝔼₂) = 𝒯.K T := rfl

/-- The open element is open. -/
theorem isOpen_K (T : 𝒯.elems) : IsOpen (𝒯.K T) := (𝒯.Kopens T).isOpen

/-- The closure of an open element is the closed element. -/
theorem closure_K (T : 𝒯.elems) : closure (𝒯.K T) = 𝒯.closedK T :=
  closure_openTriangle _ _ _

/-- The closed element is closed. -/
theorem isClosed_closedK (T : 𝒯.elems) : IsClosed (𝒯.closedK T) := isClosed_closedTriangle _ _ _

/-- The closed element is compact. -/
theorem isCompact_closedK (T : 𝒯.elems) : IsCompact (𝒯.closedK T) :=
  isCompact_closedTriangle _ _ _

/-- The open element lies in the closed one. -/
theorem K_subset_closedK (T : 𝒯.elems) : 𝒯.K T ⊆ 𝒯.closedK T :=
  openTriangle_subset_closedTriangle _ _ _

/-- The open element is convex. -/
theorem convex_K (T : 𝒯.elems) : Convex ℝ (𝒯.K T) := convex_openTriangle _ _ _

/-- The open element is bounded. -/
theorem isBounded_K (T : 𝒯.elems) : Bornology.IsBounded (𝒯.K T) := isBounded_openTriangle _ _ _

/-- The open element lies in the domain. -/
theorem K_subset (T : 𝒯.elems) : 𝒯.K T ⊆ Ω := 𝒯.openTriangle_subset T.1 T.2

/-- The open element lies in the domain. -/
theorem Kopens_le (T : 𝒯.elems) : 𝒯.Kopens T ≤ Ω := 𝒯.K_subset T

/-- The closed element lies in the closure of the domain. -/
theorem closedK_subset_closure (T : 𝒯.elems) : 𝒯.closedK T ⊆ closure (Ω : Set 𝔼₂) := by
  rw [← 𝒯.closure_K]
  exact closure_mono (𝒯.K_subset T)

/-- The vertices of an element lie in its closed element. -/
theorem vertex_mem_closedK (T : 𝒯.elems) (a : Fin 3) : T.1 a ∈ 𝒯.closedK T := by
  have := vertex_mem_closedTriangle (T.1 0) (T.1 1) (T.1 2) a
  rwa [show ![T.1 0, T.1 1, T.1 2] a = T.1 a by fin_cases a <;> rfl] at this

/-- The domain is covered by the closed elements. -/
theorem subset_iUnion_closedK : (Ω : Set 𝔼₂) ⊆ ⋃ T, 𝒯.closedK T := fun x hx ↦ by
  obtain ⟨T, hT, hxT⟩ := mem_iUnion₂.1 (𝒯.subset_iUnion hx)
  exact mem_iUnion.2 ⟨⟨T, hT⟩, hxT⟩

/-- **The closure of the domain is the union of the closed elements** — axiom (1) of the
book's definition. -/
theorem closure_eq_iUnion_closedK : closure (Ω : Set 𝔼₂) = ⋃ T, 𝒯.closedK T :=
  Subset.antisymm (closure_minimal 𝒯.subset_iUnion_closedK
      (isClosed_iUnion_of_finite fun T ↦ 𝒯.isClosed_closedK T))
    (iUnion_subset fun T ↦ 𝒯.closedK_subset_closure T)

include 𝒯 in
/-- The domain is bounded. -/
theorem isBounded : Bornology.IsBounded (Ω : Set 𝔼₂) := by
  refine Bornology.IsBounded.subset ?_ 𝒯.subset_iUnion_closedK
  exact (Bornology.isBounded_iUnion (s := 𝒯.closedK)).2 fun T ↦ isBounded_closedTriangle _ _ _

include 𝒯 in
/-- The closure of the domain is compact. -/
theorem isCompact_closure : IsCompact (closure (Ω : Set 𝔼₂)) :=
  𝒯.isBounded.isCompact_closure

/-- Distinct open elements are disjoint. -/
theorem pairwise_disjoint_K : Pairwise (Disjoint on 𝒯.K) := fun T T' hTT' ↦
  𝒯.disjoint T.1 T.2 T'.1 T'.2 fun h ↦ hTT' (Subtype.ext h)

/-- The conformity condition, on the element type. -/
theorem conforming' {T T' : 𝒯.elems} (hTT' : T ≠ T') {x : 𝔼₂} (hx : x ∈ 𝒯.closedK T)
    (hx' : x ∈ 𝒯.closedK T') :
    (∃ a b : Fin 3, x = T.1 a ∧ T.1 a = T'.1 b) ∨
      (∃ a b a' b' : Fin 3, a ≠ b ∧ T.1 a = T'.1 a' ∧ T.1 b = T'.1 b' ∧
        x ∈ segment ℝ (T.1 a) (T.1 b)) :=
  𝒯.conforming T.1 T.2 T'.1 T'.2 (fun h ↦ hTT' (Subtype.ext h)) x hx hx'

/-! #### The affine map to the reference triangle -/

/-- The linear part `x ↦ x₀ (B − A) + x₁ (C − A)` of the affine map carrying the reference
triangle onto the element with vertices `A, B, C`. -/
def linearPart (T : 𝒯.elems) : 𝔼₂ ≃L[ℝ] 𝔼₂ :=
  triangleEquiv (T.1 0) (T.1 1) (T.1 2) (𝒯.li T)

/-- **The element is the affine image of the reference triangle** under
`F_K x̂ = T_K x̂ + b_K`, with `T_K = 𝒯.linearPart T` and `b_K` the first vertex — in the form
the interpolation estimates of Atkinson–Han §10.3 take it. -/
theorem image_referenceTriangle (T : 𝒯.elems) :
    (fun x ↦ 𝒯.linearPart T x + T.1 0) '' referenceTriangle = 𝒯.Kopens T :=
  (openTriangle_eq_image _ _ _ (𝒯.li T)).symm

/-- The affine map `F_K` is `triangleAffine` of the vertices. -/
theorem affine_eq_triangleAffine (T : 𝒯.elems) :
    (fun x ↦ 𝒯.linearPart T x + T.1 0) = triangleAffine (T.1 0) (T.1 1) (T.1 2) :=
  (triangleAffine_eq _ _ _ (𝒯.li T)).symm

/-- `F_K` sends the vertices of the reference triangle to the vertices of the element. -/
theorem affine_referenceTriangleVertex (T : 𝒯.elems) (a : Fin 3) :
    𝒯.linearPart T (referenceTriangleVertex a) + T.1 0 = T.1 a := by
  rw [show 𝒯.linearPart T (referenceTriangleVertex a) + T.1 0
      = triangleAffine (T.1 0) (T.1 1) (T.1 2) (referenceTriangleVertex a) from
    congrFun (𝒯.affine_eq_triangleAffine T) _, triangleAffine_referenceTriangleVertex]
  fin_cases a <;> rfl

/-- `F_K` maps the segment from the vertex `a` to the vertex `b` of the reference triangle onto
the edge from the vertex `a` to the vertex `b` of the element, parameter by parameter. -/
theorem affine_vertex_lineMap (T : 𝒯.elems) (a b : Fin 3) (t : ℝ) :
    𝒯.linearPart T (referenceTriangleVertex a
      + t • (referenceTriangleVertex b - referenceTriangleVertex a)) + T.1 0
      = T.1 a + t • (T.1 b - T.1 a) := by
  rw [← 𝒯.affine_referenceTriangleVertex T a, ← 𝒯.affine_referenceTriangleVertex T b]
  simp only [map_add, map_smul, map_sub]
  module

/-- The inverse `F_K⁻¹ y = T_K⁻¹ (y − b_K)` of the affine map. -/
theorem affine_symm (T : 𝒯.elems) (x : 𝔼₂) :
    (𝒯.linearPart T).symm (𝒯.linearPart T x + T.1 0 - T.1 0) = x := by simp

/-- `F_K` maps the closed reference triangle onto the closed element. -/
theorem image_closedReferenceTriangle (T : 𝒯.elems) :
    (fun x ↦ 𝒯.linearPart T x + T.1 0) '' closedReferenceTriangle = 𝒯.closedK T := by
  rw [affine_eq_triangleAffine]
  rfl

/-! #### The mesh parameter -/

/-- **The mesh parameter** `h = max_{K ∈ 𝒯_h} h_K` ([han2009theoretical] (10.3.9)), the largest
diameter of an element, as the supremum of the diameters. -/
def meshSize : ℝ := sSup (Set.range fun T ↦ Metric.diam (𝒯.K T))

/-- Every element has diameter at most the mesh parameter. -/
theorem diam_le_meshSize (T : 𝒯.elems) : Metric.diam (𝒯.K T) ≤ 𝒯.meshSize :=
  le_csSup (Set.finite_range _).bddAbove ⟨T, rfl⟩

/-- The mesh parameter is nonnegative. -/
theorem meshSize_nonneg : 0 ≤ 𝒯.meshSize := by
  by_cases h : Nonempty 𝒯.elems
  · obtain ⟨T⟩ := h
    exact Metric.diam_nonneg.trans (𝒯.diam_le_meshSize T)
  · rw [not_nonempty_iff] at h
    rw [meshSize, Set.range_eq_empty, Real.sSup_empty]

/-- The mesh parameter is the mesh parameter of the collection of the elements, as a set of
sets. -/
theorem meshSize_eq_sSup_image :
    𝒯.meshSize = sSup (Metric.diam '' Set.range 𝒯.K) := by
  rw [meshSize, ← Set.range_comp]
  rfl

/-! #### The skeleton -/

/-- **The skeleton** of the triangulation: the union of the frontiers of the elements, the
edges. -/
def skeleton : Set 𝔼₂ := ⋃ T, frontier (𝒯.K T)

/-- The skeleton lies on the edges of the elements: the segments from the vertex `a` to the
vertex `a + 1` of each element, indexed by the pairs `(T, a)`. -/
theorem skeleton_subset_iUnion_segment :
    𝒯.skeleton ⊆ ⋃ p : 𝒯.elems × Fin 3, segment ℝ (p.1.1 p.2) (p.1.1 (p.2 + 1)) := by
  refine iUnion_subset fun T ↦ (frontier_openTriangle_subset _ _ _ (𝒯.li T)).trans ?_
  intro x hx
  rw [mem_iUnion]
  rcases hx with (hx | hx) | hx
  · exact ⟨(T, 0), hx⟩
  · exact ⟨(T, 1), hx⟩
  · exact ⟨(T, 2), hx⟩

/-- The skeleton is a null set. -/
theorem volume_skeleton : volume 𝒯.skeleton = 0 :=
  measure_iUnion_null fun _ ↦ volume_frontier_openTriangle _ _ _

/-- The skeleton is closed. -/
theorem isClosed_skeleton : IsClosed 𝒯.skeleton :=
  isClosed_iUnion_of_finite fun _ ↦ isClosed_frontier

/-- **Off the skeleton, every point of the domain lies in an open element.** -/
theorem exists_mem_K_of_notMem_skeleton {x : 𝔼₂} (hx : x ∈ Ω) (hS : x ∉ 𝒯.skeleton) :
    ∃ T, x ∈ 𝒯.K T := by
  obtain ⟨T, hT⟩ := mem_iUnion.1 (𝒯.subset_iUnion_closedK hx)
  refine ⟨T, ?_⟩
  by_contra hxK
  apply hS
  rw [skeleton, mem_iUnion]
  exact ⟨T, by rw [(𝒯.isOpen_K T).frontier_eq, closure_K]; exact ⟨hT, hxK⟩⟩

/-- The domain and the union of the open elements differ by a null set. -/
theorem volume_diff_iUnion_K : volume ((Ω : Set 𝔼₂) \ ⋃ T, 𝒯.K T) = 0 := by
  refine measure_mono_null (fun x hx ↦ ?_) 𝒯.volume_skeleton
  by_contra hS
  obtain ⟨T, hT⟩ := 𝒯.exists_mem_K_of_notMem_skeleton hx.1 hS
  exact hx.2 (mem_iUnion.2 ⟨T, hT⟩)

/-- **The open elements partition the domain up to a null set.** -/
theorem ae_eq_iUnion_K : (⋃ T, 𝒯.K T : Set 𝔼₂) =ᵐ[volume] (Ω : Set 𝔼₂) := by
  refine ae_eq_set.2 ⟨?_, 𝒯.volume_diff_iUnion_K⟩
  rw [sdiff_eq_empty.2 (iUnion_subset fun T ↦ 𝒯.K_subset T), measure_empty]

/-! #### The global nodes of the linear element -/

open Classical in
/-- **The vertex set** of the triangulation: the nodes `{xᵢ}` of the linear element space
([han2009theoretical] §10.2.1). -/
def vertices : Finset 𝔼₂ := 𝒯.elems.biUnion fun T ↦ Finset.univ.image T

/-- Every vertex of every element is a global node. -/
theorem vertex_mem_vertices (T : 𝒯.elems) (a : Fin 3) : T.1 a ∈ 𝒯.vertices := by
  classical
  simp only [vertices, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨T.1, T.2, a, rfl⟩

/-- Every global node is a vertex of some element. -/
theorem exists_vertex_of_mem_vertices {x : 𝔼₂} (hx : x ∈ 𝒯.vertices) :
    ∃ (T : 𝒯.elems) (a : Fin 3), T.1 a = x := by
  classical
  simp only [vertices, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and] at hx
  obtain ⟨T, hT, a, ha⟩ := hx
  exact ⟨⟨T, hT⟩, a, ha⟩

/-- The global nodes lie in the closure of the domain. -/
theorem vertices_subset_closure : (𝒯.vertices : Set 𝔼₂) ⊆ closure (Ω : Set 𝔼₂) := fun x hx ↦ by
  obtain ⟨T, a, rfl⟩ := 𝒯.exists_vertex_of_mem_vertices hx
  exact 𝒯.closedK_subset_closure T (𝒯.vertex_mem_closedK T a)

/-! #### Gluing functions defined element by element -/

/-- A family of functions, one per element, is **compatible** when any two agree at every
point common to their closed elements. The elementwise interpolants of a conforming finite
element are compatible: that is the content of the continuity of the global interpolant
([han2009theoretical] Example 10.2.3). -/
def Compatible (g : 𝒯.elems → 𝔼₂ → ℝ) : Prop :=
  ∀ T T' : 𝒯.elems, ∀ x, x ∈ 𝒯.closedK T → x ∈ 𝒯.closedK T' → g T x = g T' x

open Classical in
/-- **The function glued from the pieces** `g T`: on each closed element it is `g T` (when the
family is compatible), and `0` outside the closure of the domain. -/
def glue (g : 𝒯.elems → 𝔼₂ → ℝ) : 𝔼₂ → ℝ := fun x ↦
  if h : ∃ T, x ∈ 𝒯.closedK T then g h.choose x else 0

/-- On each closed element the glued function is the piece there. -/
theorem glue_eq_of_mem_closedK {g : 𝒯.elems → 𝔼₂ → ℝ} (hg : 𝒯.Compatible g) (T : 𝒯.elems)
    {x : 𝔼₂} (hx : x ∈ 𝒯.closedK T) : 𝒯.glue g x = g T x := by
  have h : ∃ T, x ∈ 𝒯.closedK T := ⟨T, hx⟩
  rw [glue, dite_eq_left h]
  exact hg _ _ x h.choose_spec hx

/-- On each open element the glued function is the piece there. -/
theorem glue_eq_of_mem_K {g : 𝒯.elems → 𝔼₂ → ℝ} (hg : 𝒯.Compatible g) (T : 𝒯.elems)
    {x : 𝔼₂} (hx : x ∈ 𝒯.K T) : 𝒯.glue g x = g T x :=
  𝒯.glue_eq_of_mem_closedK hg T (𝒯.K_subset_closedK T hx)

/-- The glued function vanishes outside the closure of the domain. -/
theorem glue_eq_zero_of_notMem_closure {g : 𝒯.elems → 𝔼₂ → ℝ} {x : 𝔼₂}
    (hx : x ∉ closure (Ω : Set 𝔼₂)) : 𝒯.glue g x = 0 := by
  rw [glue, dite_eq_right]
  rintro ⟨T, hT⟩
  exact hx (𝒯.closedK_subset_closure T hT)

/-- **The glued function is continuous on the closure of the domain** when the pieces are
compatible and each is continuous on its closed element: the pasting lemma over the finite
closed cover `Ω̄ = ⋃ K̄`. -/
theorem continuousOn_glue {g : 𝒯.elems → 𝔼₂ → ℝ} (hg : 𝒯.Compatible g)
    (hc : ∀ T, ContinuousOn (g T) (𝒯.closedK T)) :
    ContinuousOn (𝒯.glue g) (closure (Ω : Set 𝔼₂)) := by
  rw [𝒯.closure_eq_iUnion_closedK]
  refine (locallyFinite_of_finite _).continuousOn_iUnion (fun T ↦ 𝒯.isClosed_closedK T)
    fun T ↦ (hc T).congr fun x hx ↦ ?_
  exact 𝒯.glue_eq_of_mem_closedK hg T hx

/-! #### The global nodal interpolant -/

section Interpolant

variable {I : ℕ} (xhat : Fin I → 𝔼₂) (φhat : Fin I → 𝔼₂ → ℝ)

/-- **The local interpolation operator `Π_K`** of an element ([han2009theoretical] (10.3.2)):
nodal interpolation at the transported nodes `xᵢᴷ = F_K(x̂ᵢ)` with the transported shape
functions `φᵢᴷ = φ̂ᵢ ∘ F_K⁻¹`, where `F_K x̂ = T_K x̂ + b_K` carries the reference triangle onto
the element, `T_K = 𝒯.linearPart T` and `b_K` the first vertex. -/
def localInterp (T : 𝒯.elems) (v : 𝔼₂ → ℝ) : 𝔼₂ → ℝ :=
  Approximation.nodalInterp ((fun x ↦ 𝒯.linearPart T x + T.1 0) ∘ xhat)
    (fun i ↦ φhat i ∘ fun y ↦ (𝒯.linearPart T).symm (y - T.1 0)) v

/-- The local interpolant, unfolded: `Π_K v (x) = ∑ᵢ φ̂ᵢ(F_K⁻¹ x) v(F_K x̂ᵢ)`. -/
theorem localInterp_apply (T : 𝒯.elems) (v : 𝔼₂ → ℝ) (x : 𝔼₂) :
    𝒯.localInterp xhat φhat T v x
      = ∑ i, φhat i ((𝒯.linearPart T).symm (x - T.1 0)) * v (𝒯.linearPart T (xhat i) + T.1 0) := by
  simp [localInterp, Approximation.nodalInterp_apply]

/-- The transported shape functions are nodal for the transported nodes ([han2009theoretical]
§10.2.2, `φᵢᴷ(xⱼᴷ) = δᵢⱼ`). -/
theorem isNodalBasis_local (h : Approximation.IsNodalBasis xhat φhat) (T : 𝒯.elems) :
    Approximation.IsNodalBasis ((fun x ↦ 𝒯.linearPart T x + T.1 0) ∘ xhat)
      (fun i ↦ φhat i ∘ fun y ↦ (𝒯.linearPart T).symm (y - T.1 0)) :=
  h.comp fun x ↦ by simp

/-- The local interpolant reproduces the values at the nodes of the element. -/
theorem localInterp_apply_node (h : Approximation.IsNodalBasis xhat φhat) (T : 𝒯.elems)
    (v : 𝔼₂ → ℝ) (i : Fin I) :
    𝒯.localInterp xhat φhat T v (𝒯.linearPart T (xhat i) + T.1 0)
      = v (𝒯.linearPart T (xhat i) + T.1 0) :=
  (𝒯.isNodalBasis_local xhat φhat h T).nodalInterp_apply_node v i

/-- The local interpolant of `C^n` shape functions is `C^n`. -/
theorem contDiff_localInterp {n : WithTop ℕ∞} (hφ : ∀ i, ContDiff ℝ n (φhat i)) (T : 𝒯.elems)
    (v : 𝔼₂ → ℝ) : ContDiff ℝ n (𝒯.localInterp xhat φhat T v) := by
  unfold localInterp Approximation.nodalInterp
  refine ContDiff.sum fun i _ ↦ ?_
  exact ((hφ i).comp ((𝒯.linearPart T).symm.contDiff.comp (contDiff_id.sub contDiff_const)))
    |>.smul contDiff_const

/-- Affine shape functions give affine local interpolants: the interpolant of `v` on an
element maps the point `P + s (Q − P)` to `Π_K v (P) + s (Π_K v (Q) − Π_K v (P))`. -/
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

/-- **A conforming element type**: the shape functions `φ̂ᵢ` at the nodes `x̂ᵢ` make a conforming
finite element on the triangulation when the local interpolants of every function are
compatible — agree at every point common to two closed elements — so that they glue into a
function continuous on `Ω̄` ([han2009theoretical] §10.2.3, the condition (10.2.6)). -/
def IsConformingElement : Prop :=
  ∀ v : 𝔼₂ → ℝ, 𝒯.Compatible fun T ↦ 𝒯.localInterp xhat φhat T v

/-- **The global interpolant `Π_h v`** ([han2009theoretical] §10.3.4, `Π_h v|_K = Π_K v`): the
function glued from the local interpolants. -/
def globalInterp (v : 𝔼₂ → ℝ) : 𝔼₂ → ℝ :=
  𝒯.glue fun T ↦ 𝒯.localInterp xhat φhat T v

/-- For a conforming element the global interpolant is the local one on each closed element. -/
theorem globalInterp_eq_of_mem_closedK (h : 𝒯.IsConformingElement xhat φhat) (T : 𝒯.elems)
    (v : 𝔼₂ → ℝ) {x : 𝔼₂} (hx : x ∈ 𝒯.closedK T) :
    𝒯.globalInterp xhat φhat v x = 𝒯.localInterp xhat φhat T v x :=
  𝒯.glue_eq_of_mem_closedK (h v) T hx

/-- For a conforming element the global interpolant is the local one on each open element. -/
theorem globalInterp_eq_of_mem_K (h : 𝒯.IsConformingElement xhat φhat) (T : 𝒯.elems)
    (v : 𝔼₂ → ℝ) {x : 𝔼₂} (hx : x ∈ 𝒯.K T) :
    𝒯.globalInterp xhat φhat v x = 𝒯.localInterp xhat φhat T v x :=
  𝒯.glue_eq_of_mem_K (h v) T hx

/-- **The global interpolant of a conforming element with continuous shape functions is
continuous on `Ω̄`.** -/
theorem continuousOn_globalInterp (h : 𝒯.IsConformingElement xhat φhat)
    (hφ : ∀ i, Continuous (φhat i)) (v : 𝔼₂ → ℝ) :
    ContinuousOn (𝒯.globalInterp xhat φhat v) (closure (Ω : Set 𝔼₂)) :=
  𝒯.continuousOn_glue (h v) fun T ↦ by
    unfold localInterp Approximation.nodalInterp
    refine (continuous_finsetSum _ fun i _ ↦ ?_).continuousOn
    exact ((hφ i).comp ((𝒯.linearPart T).symm.continuous.comp
      (continuous_id.sub continuous_const))).smul continuous_const

end Interpolant

/-! #### Edges, the boundary and edge unisolvence -/

section Edges

variable {I : ℕ} (xhat : Fin I → 𝔼₂) (φhat : Fin I → 𝔼₂ → ℝ)

/-- The segment between two vertices of an element lies in the closed element. -/
theorem segment_subset_closedK (T : 𝒯.elems) (a b : Fin 3) :
    segment ℝ (T.1 a) (T.1 b) ⊆ 𝒯.closedK T := by
  have hc : Convex ℝ (𝒯.closedK T) := by
    rw [← 𝒯.closure_K]
    exact (𝒯.convex_K T).closure
  exact hc.segment_subset (𝒯.vertex_mem_closedK T a) (𝒯.vertex_mem_closedK T b)

/-- **The boundary of the domain is a union of element edges**: every point of `∂Ω` lies on an
edge `[T_a, T_b]` of some element, and that whole edge lies in `∂Ω`. This is what
"`Ω` is a polygonal domain triangulated by `𝒯`" means ([han2009theoretical] §10.2), and it is a
hypothesis rather than a consequence of the four axioms of `Triangulation`: the open square
minus a closed segment `S` lying strictly inside an interior edge `[P, Q]` of a triangulation of
the closed square satisfies all four (the open elements miss `S`), while `S ⊆ ∂Ω` lies on no edge
contained in `∂Ω`. It is what makes a piecewise polynomial vanishing at the boundary nodes vanish
on `∂Ω` (`Triangulation.globalInterp_eqOn_frontier`). -/
def FrontierSubsetEdges : Prop :=
  ∀ x ∈ frontier (Ω : Set 𝔼₂), ∃ (T : 𝒯.elems) (a b : Fin 3), a ≠ b ∧
    x ∈ segment ℝ (T.1 a) (T.1 b) ∧ segment ℝ (T.1 a) (T.1 b) ⊆ frontier (Ω : Set 𝔼₂)

/-- The transported node `F_K x̂ᵢ` lies in the closed element when `x̂ᵢ` lies in the closed
reference triangle. -/
theorem node_mem_closedK (hx : ∀ i, xhat i ∈ closure (referenceTriangle : Set 𝔼₂)) (T : 𝒯.elems)
    (i : Fin I) : 𝒯.linearPart T (xhat i) + T.1 0 ∈ 𝒯.closedK T := by
  rw [← 𝒯.image_closedReferenceTriangle, ← closure_referenceTriangle_eq]
  exact ⟨xhat i, hx i, rfl⟩

/-- **The local interpolant is the reference interpolant read through `F_K`**
([han2009theoretical] Theorem 10.3.1, `Π_K v = (Π̂ (v ∘ F_K)) ∘ F_K⁻¹`). -/
theorem localInterp_eq_nodalInterp_comp (T : 𝒯.elems) (v : 𝔼₂ → ℝ) (x : 𝔼₂) :
    𝒯.localInterp xhat φhat T v x
      = Approximation.nodalInterp xhat φhat (fun y ↦ v (𝒯.linearPart T y + T.1 0))
        ((𝒯.linearPart T).symm (x - T.1 0)) := by
  simp [localInterp_apply, Approximation.nodalInterp_apply]

/-- The global interpolant depends only on the values at the nodes of the elements. -/
theorem globalInterp_congr {v w : 𝔼₂ → ℝ}
    (h : ∀ (T : 𝒯.elems) (i : Fin I),
      v (𝒯.linearPart T (xhat i) + T.1 0) = w (𝒯.linearPart T (xhat i) + T.1 0)) :
    𝒯.globalInterp xhat φhat v = 𝒯.globalInterp xhat φhat w := by
  unfold globalInterp
  congr 1
  funext T x
  simp only [localInterp_apply, h]

/-- The global interpolant of the zero function is zero. -/
theorem globalInterp_zero : 𝒯.globalInterp xhat φhat 0 = 0 := by
  funext x
  simp only [globalInterp, glue, localInterp_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  split_ifs <;> rfl

/-- **Edge unisolvence along an element edge**: for an edge-unisolvent reference element, the
local interpolant of a function vanishing on the edge `[T_a, T_b]` vanishes on that edge. The
edge is the image under `F_K` of the reference edge `[x̂_a, x̂_b]` parameter by parameter
(`Triangulation.affine_vertex_lineMap`), so the nodes on it are the images of the reference
nodes on the reference edge. -/
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

/-- **A piecewise polynomial vanishing at the boundary nodes vanishes on the boundary.** For a
conforming, edge-unisolvent element on a triangulation whose boundary is a union of element
edges, the global interpolant of a function vanishing on `∂Ω` vanishes on `∂Ω`: a boundary
point lies on an edge contained in `∂Ω`, where the interpolant is the local one, and the nodes of
that edge are boundary points, where the function vanishes. This is the boundary-condition half
of "`V_h ⊆ H¹₀(Ω)`" ([han2009theoretical] Example 10.4.2, [quarteroni2000numerical] (12.94)). -/
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

/-! #### The linear element -/

section Linear

/-- The barycentric coordinates of the reference triangle are nodal for its vertices. -/
theorem _root_.EuclideanSpace.isNodalBasis_baryCoord :
    Approximation.IsNodalBasis referenceTriangleVertex baryCoord where
  eval_self i := by rw [baryCoord_apply_vertex, ite_eq_left rfl]
  eval_of_ne i j hij := by rw [baryCoord_apply_vertex, ite_eq_right hij]

/-- The barycentric coordinates of the reference triangle are affine. -/
theorem _root_.EuclideanSpace.baryCoord_lineMap (i : Fin 3) (P Q : 𝔼₂) (s : ℝ) :
    baryCoord i (P + s • (Q - P)) = baryCoord i P + s * (baryCoord i Q - baryCoord i P) := by
  fin_cases i
  · simp [baryCoord]; ring
  · simp [baryCoord]
  · simp [baryCoord]

/-- The local interpolant of the linear element reproduces the values at the vertices. -/
theorem localInterp_linear_vertex (T : 𝒯.elems) (v : 𝔼₂ → ℝ) (a : Fin 3) :
    𝒯.localInterp referenceTriangleVertex baryCoord T v (T.1 a) = v (T.1 a) := by
  have := 𝒯.localInterp_apply_node referenceTriangleVertex baryCoord isNodalBasis_baryCoord T v a
  rwa [𝒯.affine_referenceTriangleVertex T a] at this

/-- **The linear element is conforming** ([han2009theoretical] Example 10.2.3): the local
interpolants at the vertices, with the barycentric coordinates as shape functions, agree at
every point common to two closed elements. At a common vertex both take the value of `v`
there; along a common edge both are affine functions of one variable agreeing at its two
ends, hence equal. -/
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
