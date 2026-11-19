/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Exposed
import Numlib.Analysis.Convex.Face
import Numlib.Analysis.Convex.Representation
import Numlib.Analysis.Convex.Tangent
import NumlibSurface.Rockafellar.Chapter02.Section06

/-!
# Rockafellar, Section 18: Extreme points and faces of convex sets

This module formalizes §18 of [rockafellar1970convex]: the faces of a convex set $C$ in
$\mathbb{R}^n$, its extreme and exposed points and directions, the internal representations
$C = \operatorname{conv} S$ and $C = \operatorname{cl}(\operatorname{conv} S)$ by extreme and by
exposed points and directions, and the external representation of $C$ by its tangent half-spaces.
All sixteen numbered results are formalized: Theorems 18.1–18.8 and Corollaries 18.1.1–18.1.3,
18.3.1, 18.5.1–18.5.3 and 18.7.1. The proofs specialize `Numlib.Analysis.Convex.Face`,
`Numlib.Analysis.Convex.Exposed`, `Numlib.Analysis.Convex.Representation` and
`Numlib.Analysis.Convex.Tangent`.

A face of $C$ is a convex subset $C'$ of $C$ such that every closed segment in $C$ with a relative
interior point in $C'$ has both endpoints in $C'$. An extreme point is a face with one point, and an
extreme direction is the direction of a half-line face. The relative interiors of the faces
partition $C$ (Theorem 18.2). A closed convex set without lines is the convex hull of its extreme
points and extreme directions (Theorem 18.5), and the closure of the convex hull of its exposed
points and exposed directions (Theorem 18.7). The module also proves the extension of Theorem 18.5
to closed convex sets with a non-trivial lineality space, which the source states in words on page
166 without proof.

## Main definitions

* Definition of an extreme ray, `Rockafellar.IsExtremeRay`: a face of a convex cone that is a
  half-line from the origin.
* Definition of an exposed ray, `Rockafellar.IsExposedRay`: an exposed face of a convex cone that is
  a half-line from the origin.
* The correspondence of faces on page 166, `Rockafellar.facesEquivFacesInterOrthogonal`: a bijection
  between the faces of $C$ and the faces of $C \cap L^\perp$, where $L$ is the lineality space of
  $C$.
* Definition of a tangent hyperplane, `Rockafellar.IsTangentHyperplaneAt`: the unique supporting
  hyperplane to $C$ at a point.

## Main results

* Definitions of faces and extreme points, `Rockafellar.isFace_iff`, `Rockafellar.isFace_mono`,
  `Rockafellar.isFace_singleton_iff`, `Rockafellar.mem_extremePoints_iff`: the definitions of §18 in
  the words of the source.
* The lattice of faces, `Rockafellar.faces_isGLB`, `Rockafellar.faces_isLUB`: the faces of a convex
  set form a complete lattice under inclusion.
* Theorem 18.1, `Rockafellar.theorem_18_1`: a subset of $C$ with a relative interior point in a face
  $C'$ lies in $C'$.
* Corollary 18.1.1, `Rockafellar.corollary_18_1_1`, `Rockafellar.corollary_18_1_1_isClosed`: a face
  satisfies $C' = C \cap \operatorname{cl} C'$, and a face of a closed convex set is closed.
* Corollary 18.1.2, `Rockafellar.corollary_18_1_2`: two faces whose relative interiors meet are
  equal.
* Corollary 18.1.3, `Rockafellar.corollary_18_1_3`, `Rockafellar.corollary_18_1_3_dim`: a face other
  than $C$ lies in the relative boundary of $C$ and, if non-empty, has smaller dimension.
* Theorem 18.2, `Rockafellar.theorem_18_2_union`, `Rockafellar.theorem_18_2_disjoint`,
  `Rockafellar.theorem_18_2_subset`, `Rockafellar.theorem_18_2_maximal`: the relative interiors of
  the faces partition $C$, and they are the maximal relatively open convex subsets of $C$.
* Theorem 18.3, `Rockafellar.theorem_18_3`: a face of $\operatorname{conv} S$ is the convex hull of
  the points and directions of $S$ that belong to it.
* Corollary 18.3.1, `Rockafellar.corollary_18_3_1_points`,
  `Rockafellar.corollary_18_3_1_directions`, `Rockafellar.corollary_18_3_1_directions_of_isBounded`:
  the extreme points of $\operatorname{conv} S$ are points of $S$, and under a boundedness condition
  its extreme directions are directions of $S$.
* Theorem 18.4, `Rockafellar.theorem_18_4`: in a closed convex set that is neither an affine set nor
  a closed half of an affine set, each relative interior point lies on a segment between two
  relative boundary points.
* Theorem 18.5, `Rockafellar.theorem_18_5`, `Rockafellar.theorem_18_5_lineality`: a closed convex
  set without lines is the convex hull of its extreme points and extreme directions, and the
  extension to arbitrary lineality.
* Corollary 18.5.1, `Rockafellar.corollary_18_5_1` (Minkowski's theorem): a closed bounded convex
  set is the convex hull of its extreme points.
* Corollary 18.5.2, `Rockafellar.corollary_18_5_2`: a closed convex cone without lines is generated
  by any subset that generates its extreme rays.
* Corollary 18.5.3, `Rockafellar.corollary_18_5_3`: a non-empty closed convex set without lines has
  an extreme point.
* Theorem 18.6, `Rockafellar.theorem_18_6`, `Rockafellar.theorem_18_6_closure` (Straszewicz's
  theorem): the exposed points of a closed convex set are dense in its extreme points.
* Theorem 18.7, `Rockafellar.theorem_18_7`: a closed convex set without lines is the closure of the
  convex hull of its exposed points and exposed directions.
* Corollary 18.7.1, `Rockafellar.corollary_18_7_1`: a closed convex cone without lines is the
  closure of the cone generated by any subset that generates its exposed rays.
* Theorem 18.8, `Rockafellar.theorem_18_8`: an $n$-dimensional closed convex set in $\mathbb{R}^n$
  is the intersection of its tangent closed half-spaces.

## Implementation notes

* A face is `ConvexAnalysis.IsFace`, the definition of the source. An extreme point is a point of
  `Set.extremePoints ℝ` of Mathlib, and an exposed point is a point of `Set.exposedPoints ℝ`.
* A direction is represented by a vector that generates it, not by an element of a quotient. So
  `ConvexAnalysis.extremeDirections C` and `ConvexAnalysis.exposedDirections C` are closed under
  multiplication by positive scalars. For a set $S$ of points `P` and directions `D`,
  $\operatorname{conv} S$ is `ConvexAnalysis.convexHullPD P D`.
* The two exceptional cases of Theorem 18.4 are one predicate, `ConvexAnalysis.IsAffineHalf`: a
  linear functional equal to $0$ makes an affine set the degenerate case of a closed half of an
  affine set.

## Deviations from the source

* **Section 18, faces and extreme points** (generalization). The face definition and
  the extreme-point characterizations also admit nonconvex ambient sets. The face intersection
  and transitivity statements and the intermediate-set property have the same extension.
* **Theorem 18.1 and Corollaries 18.1.2 and 18.1.3** (generalization). The face containment,
  equality and relative-boundary results apply without convexity of the ambient set. The
  containment result also admits nonconvex $D$.
* **Theorem 18.2**, covering and disjointness (generalization). The union also applies to
  $C = \emptyset$, and disjointness of the relative interiors requires only that the faces
  be distinct, even for a nonconvex ambient set.
* **Theorem 18.3** (generalization). The source assumes the face $C'$ non-empty; this is not needed.
  See `Rockafellar.theorem_18_3`.
* **Section 18, orthogonal reduction of faces** (generalization). The formulas for faces
  and their orthogonal cross-sections apply to arbitrary ambient sets. See
  `Rockafellar.eq_add_inter_orthogonal_of_isFace` and `Rockafellar.facesEquivFacesInterOrthogonal`.
* **Section 18, extreme and exposed rays** (generalization). The ray predicates are defined
  for arbitrary sets. The equivalence with directions uses closure under nonnegative scaling
  without requiring convexity. This represents cones that contain the origin.
* **Corollary 18.5.2** (generalization). The source assumes that the cone contains more than the
  origin; this is not needed. See `Rockafellar.corollary_18_5_2`.
* **Section 18, exposed faces and points** (reading). The empty set is always exposed.
  For an exposed point, the maximizer condition also allows the zero functional on a
  singleton, including in dimension zero.
* **Corollary 18.7.1** (generalization). The source assumes that the cone contains more than the
  origin; this is not needed. See `Rockafellar.corollary_18_7_1`.
* **Section 18, tangency** (reading). `Rockafellar.IsTangentHyperplaneAt` requires uniqueness
  of the supporting half-space, which is equivalent to uniqueness of the hyperplane
  for the full-dimensional sets in Theorem 18.8.

## Not formalized

* **Corollary 18.1.3, dimension inequality for the empty proper face.**
  `Rockafellar.corollary_18_1_3_dim` assumes the face is nonempty.
* **Section 18, the meet of an empty family of faces.** `Rockafellar.faces_isGLB` uses the
  ambient intersection for a nonempty family. The relative meet of the empty family is $C$.
-/

open Set

namespace Rockafellar

open ConvexAnalysis
open scoped Pointwise

variable {n : ℕ} {C C' C₁ C₂ D : Set (Rn n)}

/-! ### Faces (page 162) -/

/-- **Section 18** of [rockafellar1970convex] (page 162), definition of a face. A set $C'$ is a
**face** of $C \subseteq \mathbb{R}^n$ if and only if $C'$ is convex, $C' \subseteq C$, and
every closed segment in $C$ with a relative interior point in $C'$ has both endpoints in $C'$.

Convexity of $C'$ is a real requirement: $\{0, 1\}$ satisfies the segment condition in $[0, 1]$
but is not a face of it.

**Generalization.** The book defines faces of convex sets. The Lean condition applies to
arbitrary ambient sets. -/
theorem isFace_iff : IsFace C C' ↔ Convex ℝ C' ∧ C' ⊆ C ∧
    ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C', z ∈ openSegment ℝ x y → x ∈ C' ∧ y ∈ C' :=
  ⟨fun h => ⟨h.convex, h.subset, fun _ hx _ hy _ hz hseg =>
      ⟨h.toIsExtreme.left_mem_of_mem_openSegment hx hy hz hseg,
        h.toIsExtreme.right_mem_of_mem_openSegment hx hy hz hseg⟩⟩,
    fun h => ⟨⟨h.2.1, fun _ hx _ hy _ hz hseg => (h.2.2 _ hx _ hy _ hz hseg).1⟩, h.1⟩⟩

/-- A convex set is a face of itself. -/
theorem isFace_self (hC : Convex ℝ C) : IsFace C C := Convex.isFace_self hC

/-- The empty set is a face of every set.

**Generalization.** The book states this for convex ambient sets. -/
theorem isFace_empty : IsFace C (∅ : Set (Rn n)) := IsFace.empty

/-- A face of a face of $C$ is a face of $C$.

**Generalization.** The ambient set $C$ may be nonconvex. -/
theorem isFace_trans (h₁ : IsFace C C') (h₂ : IsFace C' C₁) : IsFace C C₁ := h₁.trans h₂

/-- **Section 18** of [rockafellar1970convex] (page 163). If $C'$ is a face of $C$ and
$C' \subseteq D \subseteq C$, then $C'$ is a face of $D$.

**Generalization.** The book assumes $C$ and $D$ convex. The Lean statement admits
arbitrary ambient and intermediate sets. -/
theorem isFace_mono (h : IsFace C C') (hDC : D ⊆ C) (hC'D : C' ⊆ D) : IsFace D C' :=
  h.mono hDC hC'D

/-- **Section 18** of [rockafellar1970convex] (page 162). A point $x$ is an **extreme point** of $C$
if and only if $\{x\}$ is a face of $C$: the extreme points are the zero-dimensional faces.

**Generalization.** The characterization holds for nonconvex $C$ as well. -/
theorem isFace_singleton_iff {x : Rn n} : IsFace C {x} ↔ x ∈ C.extremePoints ℝ :=
  isFace_singleton

/-- **Section 18** of [rockafellar1970convex] (page 162), definition of an extreme point. A point
$x$ is an extreme point of $C \subseteq \mathbb{R}^n$ if and only if $x \in C$ and, whenever
$x = (1 - \lambda) y + \lambda z$ with $y, z \in C$ and $0 < \lambda < 1$, then $y = z = x$.

**Generalization.** The condition also defines extreme points of nonconvex sets. -/
theorem mem_extremePoints_iff {x : Rn n} :
    x ∈ C.extremePoints ℝ ↔ x ∈ C ∧ ∀ y ∈ C, ∀ z ∈ C, ∀ l : ℝ, 0 < l → l < 1 →
      x = (1 - l) • y + l • z → y = x ∧ z = x := by
  rw [mem_extremePoints]
  refine and_congr_right fun _ => ⟨fun h y hy z hz l hl0 hl1 heq => ?_, fun h y hy z hz hseg => ?_⟩
  · exact h y hy z hz ⟨1 - l, l, by linarith, hl0, by ring, heq.symm⟩
  · obtain ⟨a, b, ha, hb, hab, hval⟩ := hseg
    exact h y hy z hz b hb (by linarith) (by rw [← hval, show (1 : ℝ) - b = a by linarith])

/-! ### The lattice of faces (page 164) -/

/-- **Section 18** of [rockafellar1970convex] (page 164). The intersection of a non-empty collection
of faces of $C$ is a face of $C$, and it is the greatest lower bound of the collection.

**Generalization.** The nonempty-family assertion also applies when the ambient set is
nonconvex. The empty family in the book's face lattice has relative meet $C$. -/
theorem faces_isGLB {F : Set (Set (Rn n))} (hF : F.Nonempty) (h : ∀ B ∈ F, IsFace C B) :
    IsFace C (⋂₀ F) ∧ IsGLB F (⋂₀ F) :=
  ⟨isFace_sInter hF h,
    ⟨fun _ hB => sInter_subset_of_mem hB, fun _ hB => subset_sInter fun _ hC' => hB hC'⟩⟩

/-- **Section 18** of [rockafellar1970convex] (page 164). Let $C$ be convex. Every collection of
faces of $C$ has a least upper bound among the faces of $C$: a face that contains every member
of the collection and is contained in every other such face. With `Rockafellar.faces_isGLB`,
this makes the faces of $C$ a complete lattice under inclusion. -/
theorem faces_isLUB (hC : Convex ℝ C) (F : Set (Set (Rn n))) (h : ∀ B ∈ F, IsFace C B) :
    ∃ G, IsFace C G ∧ (∀ B ∈ F, B ⊆ G) ∧ ∀ G', IsFace C G' → (∀ B ∈ F, B ⊆ G') → G ⊆ G' :=
  ⟨⋂₀ {H | IsFace C H ∧ ∀ B ∈ F, B ⊆ H},
    isFace_sInter ⟨C, Convex.isFace_self hC, fun B hB => (h B hB).subset⟩ fun _ hH => hH.1,
    fun _ hB _ hx => mem_sInter.2 fun _ hH => hH.2 _ hB hx,
    fun _ hG' hsub => sInter_subset_of_mem ⟨hG', hsub⟩⟩

/-! ### Theorem 18.1 and its corollaries -/

/-- **Theorem 18.1** of [rockafellar1970convex]. Let $C'$ be a face of $C \subseteq \mathbb{R}^n$,
and let $D \subseteq C$ be a set such that $\operatorname{ri} D$ meets $C'$. Then
$D \subseteq C'$.

**Generalization.** The source assumes both $C$ and $D$ convex. The Lean result uses the face
property and the prolongation property of $\operatorname{ri} D$. -/
theorem theorem_18_1 (hface : IsFace C C') (hDC : D ⊆ C) (h : (ri D ∩ C').Nonempty) : D ⊆ C' :=
  hface.subset_of_relint_inter_nonempty hDC h

/-- **Corollary 18.1.1** of [rockafellar1970convex]. Let $C$ be convex and let $C'$ be a face of
$C$. Then $C' = C \cap \operatorname{cl} C'$. -/
theorem corollary_18_1_1 (hC : Convex ℝ C) (hface : IsFace C C') : C' = C ∩ closure C' :=
  hface.eq_inter_closure hC

/-- **Corollary 18.1.1** of [rockafellar1970convex], second sentence. A face of a closed convex set
is closed. -/
theorem corollary_18_1_1_isClosed (hC : Convex ℝ C) (hCcl : IsClosed C) (hface : IsFace C C') :
    IsClosed C' :=
  hface.isClosed hC hCcl

/-- **Corollary 18.1.2** of [rockafellar1970convex]. If $C_1$ and $C_2$ are faces of $C$ and
$\operatorname{ri} C_1 \cap \operatorname{ri} C_2 \neq \emptyset$, then $C_1 = C_2$.

**Generalization.** The ambient set may be nonconvex. -/
theorem corollary_18_1_2 (h₁ : IsFace C C₁) (h₂ : IsFace C C₂) (h : (ri C₁ ∩ ri C₂).Nonempty) :
    C₁ = C₂ :=
  h₁.eq_of_relint_inter_nonempty h₂ h

/-- **Corollary 18.1.3** of [rockafellar1970convex]. If $C'$ is a face of $C$ and $C' \neq C$, then
$C'$ is contained in the relative boundary $\operatorname{cl} C \setminus \operatorname{ri} C$
of $C$.

**Generalization.** The ambient set may be nonconvex. -/
theorem corollary_18_1_3 (hface : IsFace C C') (hne : C' ≠ C) : C' ⊆ relbd C := by
  rw [relbd_eq_intrinsicFrontier]
  exact hface.subset_intrinsicFrontier hne

/-- **Corollary 18.1.3** of [rockafellar1970convex], dimension. Let $C$ be convex, and let $C'$ be a
non-empty face of $C$ with $C' \neq C$. Then $\dim C' < \dim C$.

The book also permits the empty proper face, whose dimension is $-1$.

**Reading.** Omits the empty proper face, whose dimension is minus one.
-/
theorem corollary_18_1_3_dim (hC : Convex ℝ C) (hface : IsFace C C') (hne' : C'.Nonempty)
    (hne : C' ≠ C) : dim C' < dim C :=
  corollary_6_3_3 hface.convex hC (hne'.mono hface.subset) (corollary_18_1_3 hface hne)

/-! ### Theorem 18.2: the relative interiors of the faces partition $C$ -/

/-- **Theorem 18.2** of [rockafellar1970convex], covering. Let $C$ be convex. Then
$$C = \bigcup \{\operatorname{ri} C' \mid C' \text{ a face of } C\}.$$

**Generalization.** The book assumes $C$ nonempty and indexes the union by nonempty faces.
Including the empty face contributes nothing, and the identity also holds for $C = \emptyset$.
-/
theorem theorem_18_2_union (hC : Convex ℝ C) : C = ⋃ C' ∈ {B : Set (Rn n) | IsFace C B}, ri C' :=
  eq_iUnion_relint_isFace hC

/-- **Theorem 18.2** of [rockafellar1970convex], disjointness. If $C_1$ and $C_2$ are distinct faces
of $C$, then $\operatorname{ri} C_1$ and $\operatorname{ri} C_2$ are disjoint. With
`Rockafellar.theorem_18_2_union`, the relative interiors of the faces partition $C$.

**Generalization.** Disjointness also holds for distinct faces of a nonconvex set, and
the empty face has empty relative interior. -/
theorem theorem_18_2_disjoint (h₁ : IsFace C C₁) (h₂ : IsFace C C₂) (hne : C₁ ≠ C₂) :
    Disjoint (ri C₁) (ri C₂) :=
  h₁.relint_pairwise_disjoint h₂ hne

/-- **Theorem 18.2** of [rockafellar1970convex], containment. Let $C$ be convex, and let
$D \subseteq C$ be a non-empty, convex and relatively open set. Then
$D \subseteq \operatorname{ri} C'$ for some face $C'$ of $C$. -/
theorem theorem_18_2_subset (hC : Convex ℝ C) (hD : Convex ℝ D) (hDC : D ⊆ C) (hne : D.Nonempty)
    (hopen : IsRelativelyOpen D) : ∃ C', IsFace C C' ∧ D ⊆ ri C' :=
  exists_isFace_subset_relint hC hD hDC hne hopen

/-- **Theorem 18.2** of [rockafellar1970convex], maximality. Let $C$ be convex and let $C'$ be a
non-empty face of $C$. If $D$ is a convex, relatively open set with
$\operatorname{ri} C' \subseteq D \subseteq C$, then $D = \operatorname{ri} C'$. So the relative
interiors of the non-empty faces are maximal among the relatively open convex subsets of $C$. -/
theorem theorem_18_2_maximal (hC : Convex ℝ C) (hface : IsFace C C') (hne' : C'.Nonempty)
    (hD : Convex ℝ D) (hopen : IsRelativelyOpen D) (hsub : ri C' ⊆ D) (hDC : D ⊆ C) :
    D = ri C' :=
  hface.relint_maximal hC hne' hD hopen hsub hDC

/-! ### Theorem 18.3: the faces of a hull of points and directions -/

/-- **Theorem 18.3** of [rockafellar1970convex]. Let $C = \operatorname{conv} S$ for a set $S$ of
points $P$ and directions $D$ in $\mathbb{R}^n$, and let $C'$ be a face of $C$. Then
$C' = \operatorname{conv} S'$, where $S'$ consists of the points of $S$ that lie in $C'$ and the
directions of $S$ in which $C'$ recedes:
$$C' = \operatorname{conv}\bigl((P \cap C') \cup \{y \in D \mid y \in 0^+ C'\}\bigr).$$

**Generalization.** The source assumes $C'$ non-empty. This hypothesis is not needed. -/
theorem theorem_18_3 {P D : Set (Rn n)} (hface : IsFace (convexHullPD P D) C') :
    C' = convexHullPD (P ∩ C') {y ∈ D | y ∈ recessionCone C'} :=
  hface.eq_convexHullPD

/-- **Corollary 18.3.1** of [rockafellar1970convex], extreme points. Every extreme point of
$\operatorname{conv} S$, for a set $S$ of points $P$ and directions $D$, is a point of $S$, that
is, it belongs to $P$. -/
theorem corollary_18_3_1_points (P D : Set (Rn n)) :
    (convexHullPD P D).extremePoints ℝ ⊆ P :=
  extremePoints_convexHullPD_subset P D

/-- **Corollary 18.3.1** of [rockafellar1970convex], extreme directions. Let $S$ be a set of points
$P$ and directions $D$ in $\mathbb{R}^n$ such that no half-line contains an unbounded set of
points of $S$. Then every extreme direction of $\operatorname{conv} S$ is a direction of $S$:
each vector $y$ that generates an extreme direction is a positive multiple of a vector of $D$. -/
theorem corollary_18_3_1_directions (P D : Set (Rn n))
    (hP : ∀ x z : Rn n, Bornology.IsBounded (P ∩ halfLine x z)) {y : Rn n}
    (hy : y ∈ extremeDirections (convexHullPD P D)) : ∃ z ∈ D, ∃ a : ℝ, 0 < a ∧ y = a • z :=
  exists_mem_eq_smul_of_mem_extremeDirections P D hP hy

/-- **Corollary 18.3.1** of [rockafellar1970convex], extreme directions, in the case that the set
$P$ of points of $S$ is bounded. Then every vector that generates an extreme direction of
$\operatorname{conv} S$ is a positive multiple of a vector of $D$. -/
theorem corollary_18_3_1_directions_of_isBounded (P D : Set (Rn n))
    (hP : Bornology.IsBounded P) {y : Rn n}
    (hy : y ∈ extremeDirections (convexHullPD P D)) : ∃ z ∈ D, ∃ a : ℝ, 0 < a ∧ y = a • z :=
  exists_mem_eq_smul_of_mem_extremeDirections_of_isBounded P D hP hy

/-! ### Theorem 18.4: a closed convex set is the hull of its relative boundary -/

/-- **Theorem 18.4** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^n$ be a closed convex
set that is neither an affine set nor a closed half of an affine set. Then every point
$x \in \operatorname{ri} C$ lies on a closed segment $[a, b]$ with $a$ and $b$ in the relative
boundary of $C$.

The two exceptional cases of the source are the single predicate `ConvexAnalysis.IsAffineHalf`:
$C$ is the intersection of its affine hull with a closed half-space
$\{x \mid \varphi(x) \le \alpha\}$. The choice $\varphi = 0$ gives the affine sets. -/
theorem theorem_18_4 (hC : Convex ℝ C) (hCcl : IsClosed C) (hhalf : ¬ IsAffineHalf C) {x : Rn n}
    (hx : x ∈ ri C) : ∃ a ∈ relbd C, ∃ b ∈ relbd C, x ∈ segment ℝ a b := by
  obtain ⟨a, haC, b, hbC, hari, hbri, hseg⟩ :=
    exists_notMem_relint_mem_segment_of_not_isAffineHalf hC hCcl hhalf hx
  exact ⟨a, ⟨subset_closure haC, hari⟩, b, ⟨subset_closure hbC, hbri⟩, hseg⟩

/-! ### Theorem 18.5: the fundamental internal representation -/

/-- **Theorem 18.5** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^n$ be a closed convex
set that contains no lines, and let $S$ be the set of its extreme points and extreme directions.
Then $C = \operatorname{conv} S$.

"Contains no lines" is `ConvexAnalysis.ContainsNoLine`, which also holds for $C = \emptyset$. -/
theorem theorem_18_5 (hC : Convex ℝ C) (hCcl : IsClosed C) (hnl : ContainsNoLine C) :
    convexHullPD (C.extremePoints ℝ) (extremeDirections C) = C :=
  convexHullPD_extremePoints_extremeDirections hC hCcl hnl

/-- **Section 18** of [rockafellar1970convex] (page 166), Theorem 18.5 for a closed convex set of
arbitrary lineality. Let $C \subseteq \mathbb{R}^n$ be closed and convex, let $L$ be its
lineality space, and let $C_0 = C \cap L^\perp$. Then
$$C = L + \operatorname{conv} S_0,$$
where $S_0$ is the set of extreme points and extreme directions of $C_0$.

The source states this "obvious extension" in words and does not prove it. The set $C_0$
contains no lines, because the direction of such a line would lie in both $L$ and $L^\perp$. The
lineality space is `ConvexAnalysis.linealitySubmodule C`. -/
theorem theorem_18_5_lineality (hC : Convex ℝ C) (hCcl : IsClosed C) :
    C = (linealitySubmodule C : Set (Rn n)) +
      convexHullPD ((C ∩ ((linealitySubmodule C)ᗮ : Set (Rn n))).extremePoints ℝ)
        (extremeDirections (C ∩ ((linealitySubmodule C)ᗮ : Set (Rn n)))) := by
  set L : Submodule ℝ (Rn n) := linealitySubmodule C with hL
  set C₀ : Set (Rn n) := C ∩ ((Lᗮ : Submodule ℝ (Rn n)) : Set (Rn n)) with hC₀
  have hcompl : IsCompl L Lᗮ := Submodule.isCompl_orthogonal L
  have hC₀conv : Convex ℝ C₀ := hC.inter (Lᗮ : Submodule ℝ (Rn n)).convex
  have hC₀cl : IsClosed C₀ :=
    hCcl.inter (Lᗮ : Submodule ℝ (Rn n)).closed_of_finiteDimensional
  have hC₀nl : ContainsNoLine C₀ := by
    intro x y hy
    by_contra hall
    push Not at hall
    have hyL : y ∈ L := by
      rw [hL, mem_linealitySubmodule]
      exact mem_linealitySpace_of_forall_add_smul_mem hC hCcl fun t => (hall t).1
    have hxL : x ∈ (Lᗮ : Submodule ℝ (Rn n)) := by
      have h0 := (hall 0).2
      simpa using h0
    have hx1L : x + (1 : ℝ) • y ∈ (Lᗮ : Submodule ℝ (Rn n)) := (hall 1).2
    have hyL' : y ∈ (Lᗮ : Submodule ℝ (Rn n)) := by
      have hsub := (Lᗮ : Submodule ℝ (Rn n)).sub_mem hx1L hxL
      simpa using hsub
    have hbot : y ∈ L ⊓ Lᗮ := Submodule.mem_inf.2 ⟨hyL, hyL'⟩
    rw [hcompl.inf_eq_bot] at hbot
    exact hy (Submodule.mem_bot ℝ |>.1 hbot)
  rw [theorem_18_5 hC₀conv hC₀cl hC₀nl]
  exact eq_add_inter_of_isCompl hcompl

/-- **Section 18** of [rockafellar1970convex] (page 166). Let $C'$ be a face of $C$ and let $L$ be
the lineality space of $C$. Then $C' = (C' \cap L^\perp) + L$: a face is invariant under
translation by $L$.

**Generalization.** The book assumes $C$ convex. This decomposition applies to faces
of arbitrary sets. -/
theorem eq_add_inter_orthogonal_of_isFace (h : IsFace C C') :
    C' = (linealitySubmodule C : Set (Rn n)) +
      (C' ∩ ((linealitySubmodule C)ᗮ : Set (Rn n))) :=
  h.eq_add_inter_of_isCompl_of_le (coe_linealitySubmodule C).subset
    (Submodule.isCompl_orthogonal _)

/-- **Section 18** of [rockafellar1970convex] (page 166). Let $L$ be the lineality space of $C$ and
$C_0 = C \cap L^\perp$. The faces $C'$ of $C$ correspond one-to-one to the faces $C_0'$ of
$C_0$, by $C_0' = C' \cap L^\perp$ and $C' = L + C_0'$.

**Generalization.** The book states the correspondence for convex $C$. The Lean correspondence
applies to arbitrary $C$ by using $L^\perp$ as a complement of $L$. -/
noncomputable def facesEquivFacesInterOrthogonal (A : Set (Rn n)) :
    {C' : Set (Rn n) // IsFace A C'} ≃
      {C₀ : Set (Rn n) // IsFace (A ∩ ((linealitySubmodule A)ᗮ : Set (Rn n))) C₀} :=
  isFaceEquivInter (coe_linealitySubmodule A).subset (Submodule.isCompl_orthogonal _)

/-- **Corollary 18.5.1** of [rockafellar1970convex] (Minkowski's theorem). A closed bounded convex
set $C \subseteq \mathbb{R}^n$ is the convex hull of its extreme points. -/
theorem corollary_18_5_1 (hC : Convex ℝ C) (hCcl : IsClosed C) (hbdd : Bornology.IsBounded C) :
    convexHull ℝ (C.extremePoints ℝ) = C :=
  convexHull_extremePoints (Metric.isCompact_of_isClosed_isBounded hCcl hbdd) hC

/-- **Corollary 18.5.3** of [rockafellar1970convex]. A non-empty closed convex set
$C \subseteq \mathbb{R}^n$ that contains no lines has at least one extreme point. -/
theorem corollary_18_5_3 (hC : Convex ℝ C) (hCcl : IsClosed C) (hnl : ContainsNoLine C)
    (hne : C.Nonempty) : (C.extremePoints ℝ).Nonempty :=
  extremePoints_nonempty_of_containsNoLine hC hCcl hnl hne

/-!
### Rays of a convex cone (page 162)

For a cone the useful zero-dimensional object is not an extreme point, since the origin is the only
candidate, but an extreme ray: a face that is a half-line from the origin.
-/

/-- **Section 18** of [rockafellar1970convex] (page 162), definition of an extreme ray. A vector
$y \in \mathbb{R}^n$ generates an **extreme ray** of $K$ if $y \neq 0$ and the
half-line $\{\lambda y \mid \lambda \ge 0\}$ is a face of $K$.

**Generalization.** The book defines this for convex cones. The predicate admits arbitrary $K$.
-/
def IsExtremeRay (K : Set (Rn n)) (y : Rn n) : Prop := y ≠ 0 ∧ IsFace K (halfLine 0 y)

/-- **Section 18** of [rockafellar1970convex] (page 162), definition of an exposed ray. A vector
$y \in \mathbb{R}^n$ generates an **exposed ray** of $K$ if $y \neq 0$ and the
half-line $\{\lambda y \mid \lambda \ge 0\}$ is an exposed face of $K$.

**Generalization.** The book defines this for convex cones. The predicate admits arbitrary $K$.
-/
def IsExposedRay (K : Set (Rn n)) (y : Rn n) : Prop := y ≠ 0 ∧ IsExposed ℝ K (halfLine 0 y)

/-- Let $K \subseteq \mathbb{R}^n$ be non-empty and closed under multiplication by non-negative
scalars, and let $y \neq 0$. If the half-line $\{x + \lambda y \mid \lambda \ge 0\}$ is an
extreme subset of $K$, then $x = 0$. This is used for
`Rockafellar.isExtremeRay_iff_isExtremeDirection`. -/
theorem eq_zero_of_isExtreme_halfLine {K : Set (Rn n)} (hne : K.Nonempty)
    (hcone : ∀ x ∈ K, ∀ a : ℝ, 0 ≤ a → a • x ∈ K) {x y : Rn n} (hy : y ≠ 0)
    (h : IsExtreme ℝ K (halfLine x y)) : x = 0 := by
  have h0 : (0 : Rn n) ∈ K := zero_mem_of_forall_smul_mem hne hcone
  have hxC' : x ∈ halfLine x y := left_mem_halfLine x y
  have h2x : (2 : ℝ) • x ∈ K := hcone x (h.subset hxC') 2 (by norm_num)
  have hopen : x ∈ openSegment ℝ (0 : Rn n) ((2 : ℝ) • x) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
  obtain ⟨b, hb, hbeq⟩ :=
    mem_halfLine.1 (h.left_mem_of_mem_openSegment h0 h2x hxC' hopen)
  obtain ⟨a, ha, haeq⟩ :=
    mem_halfLine.1 (h.right_mem_of_mem_openSegment h0 h2x hxC' hopen)
  have hxa : x = a • y := by
    have hstep : x + x = x + a • y := by rw [← haeq]; module
    exact add_left_cancel hstep
  have hsum : (a + b) • y = 0 := by
    rw [add_smul, ← hxa]
    exact hbeq.symm
  have hab : a + b = 0 := by
    rcases smul_eq_zero.1 hsum with hab | hy0
    · exact hab
    · exact absurd hy0 hy
  have ha0 : a = 0 := by linarith
  rw [hxa, ha0, zero_smul]

/-- **Section 18** of [rockafellar1970convex] (page 162). Let $K \subseteq \mathbb{R}^n$ be
non-empty and closed under multiplication by non-negative scalars. Then $y$ generates an extreme
ray of $K$ if and only if $y$ generates an extreme direction of $K$.

**Generalization.** The book states this for convex cones. The Lean criterion does not require
convexity and assumes the scaling property at zero as well as positive scalars. -/
theorem isExtremeRay_iff_isExtremeDirection {K : Set (Rn n)} (hne : K.Nonempty)
    (hcone : ∀ x ∈ K, ∀ a : ℝ, 0 ≤ a → a • x ∈ K) {y : Rn n} :
    IsExtremeRay K y ↔ IsExtremeDirection K y := by
  refine ⟨fun h => ⟨h.1, 0, h.2⟩, fun h => ⟨h.1, ?_⟩⟩
  obtain ⟨x, hface⟩ := h.2
  rwa [eq_zero_of_isExtreme_halfLine hne hcone h.1 hface.toIsExtreme] at hface

/-- Let $K \subseteq \mathbb{R}^n$ be non-empty and closed under multiplication by non-negative
scalars. Then $y$ generates an exposed ray of $K$ if and only if $y$ generates an exposed
direction of $K$.

The same argument as for extreme rays applies to the exposed rays defined in the book. -/
theorem isExposedRay_iff_isExposedDirection {K : Set (Rn n)} (hne : K.Nonempty)
    (hcone : ∀ x ∈ K, ∀ a : ℝ, 0 ≤ a → a • x ∈ K) {y : Rn n} :
    IsExposedRay K y ↔ IsExposedDirection K y := by
  refine ⟨fun h => ⟨h.1, 0, h.2⟩, fun h => ⟨h.1, ?_⟩⟩
  obtain ⟨x, hexp⟩ := h.2
  rwa [eq_zero_of_isExtreme_halfLine hne hcone h.1 hexp.isExtreme] at hexp

/-- A closed set $K \subseteq \mathbb{R}^n$ that is closed under multiplication by positive scalars
(a cone in the sense of the source) is also closed under multiplication by non-negative scalars.
This is the form that the backbone theorems on cones use. -/
theorem forall_smul_mem_of_isCone {K : Set (Rn n)} (hK : IsCone K) (hKcl : IsClosed K) :
    ∀ x ∈ K, ∀ a : ℝ, 0 ≤ a → a • x ∈ K := by
  intro x hx a ha
  rcases ha.lt_or_eq with hpos | h0
  · exact hK a hpos x hx
  · have hlim : Filter.Tendsto (fun t : ℝ => t • x) (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((0 : ℝ) • x)) :=
      ((continuous_id.smul continuous_const).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have hmem : (0 : Rn n) ∈ K := by
      have h := hKcl.mem_of_tendsto hlim
        (Filter.Eventually.mono self_mem_nhdsWithin fun t ht => hK t ht x hx)
      rwa [zero_smul] at h
    rw [← h0, zero_smul]
    exact hmem

/-- **Corollary 18.5.2** of [rockafellar1970convex]. Let $K \subseteq \mathbb{R}^n$ be a non-empty
closed convex cone that contains no lines, and let $T \subseteq K$ be a set such that every
extreme ray of $K$ is generated by some $x \in T$. Then $K$ is the convex cone generated by $T$,
that is, the set of non-negative combinations of vectors of $T$.

**Generalization.** The source assumes that $K$ contains more than the origin. This is not
needed: the cone $\{0\}$ has no extreme rays, so the hypothesis on $T$ is vacuous, and both
sides are $\{0\}$.

A cone is `Rockafellar.IsCone`, a set closed under multiplication by positive scalars. -/
theorem corollary_18_5_2 {K T : Set (Rn n)} (hK : Convex ℝ K) (hKcl : IsClosed K)
    (hcone : IsCone K) (hne : K.Nonempty) (hnl : ContainsNoLine K) (hTK : T ⊆ K)
    (hgen : ∀ y, IsExtremeRay K y → ∃ x ∈ T, ∃ a : ℝ, 0 < a ∧ y = a • x) :
    (PointedCone.hull ℝ T : Set (Rn n)) = K := by
  have hsmul := forall_smul_mem_of_isCone hcone hKcl
  exact coneHull_of_forall_extremeDirection hK hKcl hne hsmul hnl hTK fun y hy =>
    hgen y ((isExtremeRay_iff_isExtremeDirection hne hsmul).2 hy)

/-!
### Directions at infinity pass to the recession cone (page 163)

If $C'$ is a half-line face of a closed convex set $C$ with endpoint $x$, then
$C' \subseteq x + 0^+ C \subseteq C$ by Theorem 8.3, so $C' - x$ is an extreme ray of $0^+ C$. The
converse fails: a parabolic set in $\mathbb{R}^2$ has no half-line face, while its recession cone is
a ray.
-/

/-- **Section 18** of [rockafellar1970convex] (page 163). Every extreme direction of a closed convex
set $C$ is an extreme direction of its recession cone $0^+ C$. This is sharper than Theorem 8.3,
which gives only that it is a direction of recession. -/
theorem subset_extremeDirections_recessionCone (hC : Convex ℝ C) (hCcl : IsClosed C) :
    extremeDirections C ⊆ extremeDirections (recessionCone C) :=
  extremeDirections_subset_extremeDirections_recessionCone hC hCcl

/-- **Section 18** of [rockafellar1970convex] (page 163). Every exposed direction of a closed convex
set $C$ is an exposed direction of its recession cone $0^+ C$. -/
theorem subset_exposedDirections_recessionCone (hC : Convex ℝ C) (hCcl : IsClosed C) :
    exposedDirections C ⊆ exposedDirections (recessionCone C) :=
  exposedDirections_subset_exposedDirections_recessionCone hC hCcl

/-- **Section 18** of [rockafellar1970convex] (page 163). Let $C$ be closed and convex. If $y$
generates an extreme direction of $C$, then $y$ generates an extreme ray of the cone $0^+ C$. In
the words of the source: if $C'$ is a half-line face of $C$ with endpoint $x$, then $C' - x$ is
an extreme ray of $0^+ C$. -/
theorem isExtremeRay_recessionCone {y : Rn n} (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hy : IsExtremeDirection C y) : IsExtremeRay (recessionCone C) y :=
  (isExtremeRay_iff_isExtremeDirection ⟨0, zero_mem_recessionCone C⟩
    fun _ hx _ ha => smul_mem_recessionCone ha hx).2
    (subset_extremeDirections_recessionCone hC hCcl hy)

/-- Let $C$ be closed and convex. If $y$ generates an exposed direction of $C$, then $y$ generates
an exposed ray of the cone $0^+ C$. -/
theorem isExposedRay_recessionCone {y : Rn n} (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hy : IsExposedDirection C y) : IsExposedRay (recessionCone C) y :=
  (isExposedRay_iff_isExposedDirection ⟨0, zero_mem_recessionCone C⟩
    fun _ hx _ ha => smul_mem_recessionCone ha hx).2
    (subset_exposedDirections_recessionCone hC hCcl hy)

/-! ### Theorem 18.6: Straszewicz's theorem -/

/-- **Theorem 18.6** of [rockafellar1970convex] (Straszewicz's theorem). Let
$C \subseteq \mathbb{R}^n$ be closed and convex. Every extreme point of $C$ is the limit of a
sequence of exposed points of $C$.

The statement is that the set of extreme points lies in the closure of the set of exposed
points. -/
theorem theorem_18_6 (hC : Convex ℝ C) (hCcl : IsClosed C) :
    C.extremePoints ℝ ⊆ closure (C.exposedPoints ℝ) :=
  extremePoints_subset_closure_exposedPoints hC hCcl

/-- **Theorem 18.6** of [rockafellar1970convex], in the words of the source. Let
$C \subseteq \mathbb{R}^n$ be closed and convex. The exposed points of $C$ are extreme points,
and they form a dense subset of the extreme points: the two sets have the same closure. -/
theorem theorem_18_6_closure (hC : Convex ℝ C) (hCcl : IsClosed C) :
    C.exposedPoints ℝ ⊆ C.extremePoints ℝ ∧
      closure (C.exposedPoints ℝ) = closure (C.extremePoints ℝ) :=
  ⟨exposedPoints_subset_extremePoints, closure_exposedPoints_eq_closure_extremePoints hC hCcl⟩

/-! ### Exposed faces and exposed points (page 162) -/

/-- **Section 18** of [rockafellar1970convex] (page 162), definition of an exposed face. A set $C'$
is an exposed face of $C \subseteq \mathbb{R}^n$ if and only if $C'$ is empty or there is a
vector $b$ such that $C'$ is the set of points of $C$ at which the linear function
$\langle \cdot, b \rangle$ attains its maximum over $C$.

The source quantifies over vectors $b$, and Mathlib over continuous linear functionals; in
$\mathbb{R}^n$ the two are the same.

**Reading.** The book allows the empty set when it arises as a maximizer set. The Lean
predicate treats the empty set as exposed for every $C$, and allows nonconvex $C$. -/
theorem isExposed_iff_exists_vector :
    IsExposed ℝ C C' ↔ (C'.Nonempty →
      ∃ b : Rn n, C' = {x | x ∈ C ∧ ∀ y ∈ C, pairing n y b ≤ pairing n x b}) := by
  constructor
  · intro h hne
    obtain ⟨l, hl⟩ := h hne
    obtain ⟨b, rfl⟩ := exists_linFn l
    exact ⟨b, by simpa using hl⟩
  · intro h hne
    obtain ⟨b, hb⟩ := h hne
    exact ⟨linFn b, by simpa using hb⟩

/-- **Section 18** of [rockafellar1970convex] (page 162), definition of an exposed point. A point
$x$ is an exposed point of $C \subseteq \mathbb{R}^n$ if and only if $x \in C$ and there is a
vector $b$ such that $\langle y, b \rangle \le \langle x, b \rangle$ for all $y \in C$, with
equality only for $y = x$.

**Reading.** For nonsingleton $C$ the maximizing vector is nonzero, so its supporting
hyperplane meets $C$ only at $x$. For a singleton the maximizer condition also accepts
the zero functional, including in dimension zero. The condition permits nonconvex $C$. -/
theorem mem_exposedPoints_iff {x : Rn n} :
    x ∈ C.exposedPoints ℝ ↔ x ∈ C ∧ ∃ b : Rn n, (∀ y ∈ C, pairing n y b ≤ pairing n x b) ∧
      ∀ y ∈ C, pairing n x b ≤ pairing n y b → y = x := by
  rw [exposed_point_def]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨l, hl⟩ := h
    obtain ⟨b, rfl⟩ := exists_linFn l
    exact ⟨b, fun y hy => by simpa using (hl y hy).1,
      fun y hy hle => (hl y hy).2 (by simpa using hle)⟩
  · obtain ⟨b, hmax, huniq⟩ := h
    exact ⟨linFn b, fun y hy =>
      ⟨by simpa using hmax y hy, fun hle => huniq y hy (by simpa using hle)⟩⟩

/-! ### Theorem 18.7: the exposed representation -/

/-- **Theorem 18.7** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^n$ be a closed convex
set that contains no lines, and let $S$ be the set of its exposed points and exposed directions.
Then $C = \operatorname{cl}(\operatorname{conv} S)$.

Unlike in Theorem 18.5, the closure cannot be omitted: the set of exposed points of a closed
convex set need not be closed. -/
theorem theorem_18_7 (hC : Convex ℝ C) (hCcl : IsClosed C) (hnl : ContainsNoLine C) :
    closure (convexHullPD (C.exposedPoints ℝ) (exposedDirections C)) = C :=
  closure_convexHullPD_exposedPoints_exposedDirections hC hCcl hnl

/-- **Corollary 18.7.1** of [rockafellar1970convex]. Let $K \subseteq \mathbb{R}^n$ be a non-empty
closed convex cone that contains no lines, and let $T \subseteq K$ be a set such that every
exposed ray of $K$ is generated by some $x \in T$. Then $K$ is the closure of the convex cone
generated by $T$.

**Generalization.** The source assumes that $K$ contains more than the origin. This is not
needed.

The source prints this corollary without a proof. The proof follows Corollary 18.5.2 with
Theorem 18.7 in place of Theorem 18.5: $K = \operatorname{cl}(\operatorname{conv} S)$ for $S$
the set of exposed points and exposed directions of $K$; the origin is the only exposed point,
since it is the only extreme point of a cone without lines; and the convex hull of the origin
and a set of directions is the cone that the directions generate. -/
theorem corollary_18_7_1 {K T : Set (Rn n)} (hK : Convex ℝ K) (hKcl : IsClosed K)
    (hcone : IsCone K) (hne : K.Nonempty) (hnl : ContainsNoLine K) (hTK : T ⊆ K)
    (hgen : ∀ y, IsExposedRay K y → ∃ x ∈ T, ∃ a : ℝ, 0 < a ∧ y = a • x) :
    closure (PointedCone.hull ℝ T : Set (Rn n)) = K := by
  have hsmul := forall_smul_mem_of_isCone hcone hKcl
  exact closure_coneHull_of_forall_exposedDirection hK hKcl hne hsmul hnl hTK fun y hy =>
    hgen y ((isExposedRay_iff_isExposedDirection hne hsmul).2 hy)

/-! ### Theorem 18.8: the tangent representation -/

/-- **Section 18** of [rockafellar1970convex] (page 168), definition of a tangent hyperplane. For a
vector $b \in \mathbb{R}^n$ and a point $x$, the hyperplane $\{z \mid \langle z, b \rangle =
\langle x, b \rangle\}$ is **tangent** to $C$ at $x$ if it is the unique supporting hyperplane
to $C$ at $x$: $b \neq 0$, $x \in C$, $\langle z, b \rangle \le \langle x, b \rangle$ for all
$z \in C$, and every non-zero linear function that attains its maximum over $C$ at $x$ is a
positive multiple of $\langle \cdot, b \rangle$. The corresponding tangent half-space is $\{z
\mid \langle z, b \rangle \le \langle x, b \rangle\}$.

The definition is `ConvexAnalysis.IsTangentAt` for the linear function `Rockafellar.linFn b`.

**Reading.** The book uses uniqueness of the supporting hyperplane of a closed convex set.
The Lean predicate requires uniqueness of its supporting half-space orientation and admits
arbitrary sets. These uniqueness conditions agree for sets with nonempty interior. For
$C = \{0\} \subseteq \mathbb{R}$, the unique supporting hyperplane has two supporting
orientations, so the Lean predicate fails there. -/
def IsTangentHyperplaneAt (C : Set (Rn n)) (b : Rn n) (x : Rn n) : Prop :=
  IsTangentAt C (linFn b) x

/-- **Theorem 18.8** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^n$ be an
$n$-dimensional closed convex set. Then $C$ is the intersection of the closed half-spaces
tangent to $C$:
$$C = \bigcap \{\{z \mid \langle z, b \rangle \le \langle x, b \rangle\} \mid \text{the
  hyperplane } \langle z, b \rangle = \langle x, b \rangle \text{ is tangent to } C \text{ at }
  x\}.$$

The condition that $C$ is $n$-dimensional in $\mathbb{R}^n$ is stated as
$\operatorname{int} C \neq \emptyset$. -/
theorem theorem_18_8 (hC : Convex ℝ C) (hCcl : IsClosed C) (hint : (interior C).Nonempty) :
    ⋂ (b : Rn n) (x : Rn n) (_ : IsTangentHyperplaneAt C b x),
      {z : Rn n | pairing n z b ≤ pairing n x b} = C := by
  refine subset_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · simp only [mem_iInter, mem_ofPred_eq] at hz
    rw [← eq_iInter_tangent_halfSpaces hC hCcl hint]
    simp only [mem_iInter, mem_ofPred_eq]
    intro f y hty
    obtain ⟨b, rfl⟩ := exists_linFn f
    simpa using hz b y hty
  · simp only [mem_iInter, mem_ofPred_eq]
    intro b y hty
    simpa using IsTangentAt.subset_halfSpace hty hz

end Rockafellar
