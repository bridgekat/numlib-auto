/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Exposed
import Numlib.Analysis.Convex.RelativeInterior

/-!
# Faces of a convex set

A **face** of a convex set $C$ is a convex subset $C' \subseteq C$ such that every closed line
segment in $C$ with a relative interior point in $C'$ has both endpoints in $C'$. All results of
this module rest on one strengthening of this definition: a face contains every convex subset of $C$
whose relative interior it meets ([rockafellar1970convex], Theorem 18.1). From it follow the
partition of $C$ by the relative interiors of its nonempty faces ([rockafellar1970convex], Theorem
18.2) and, for compact $C$, Minkowski's theorem: $C$ is the convex hull of its extreme points. The
presentation follows [rockafellar1970convex], §18.

This module treats the bounded case, which the polyhedral theory and the corollaries of the
Krein–Milman theorem use. The representation of an unbounded closed convex set needs hulls of points
and directions (`ConvexAnalysis.convexHullPD` in `Numlib.Analysis.Convex.HullDirections`) and is in
`Numlib.Analysis.Convex.Representation`. The representation by exposed points is in
`Numlib.Analysis.Convex.Exposed` and `Numlib.Analysis.Convex.Tangent`.

## Main definitions

* `ConvexAnalysis.IsFace`: a face in the sense of Rockafellar, as Mathlib's `IsExtreme ℝ C C'`
  together with the convexity of $C'$.

## Main results

* `ConvexAnalysis.IsFace.subset_of_relint_inter_nonempty`: a face contains every subset
  $D \subseteq C$ whose relative interior it meets.
* `ConvexAnalysis.IsFace.eq_inter_closure`: $C' = C \cap \operatorname{cl} C'$, so a face of a
  closed convex set is closed.
* `ConvexAnalysis.IsFace.eq_of_relint_inter_nonempty`: two faces whose relative interiors meet are
  equal.
* `ConvexAnalysis.IsFace.disjoint_relint`, `ConvexAnalysis.IsFace.subset_intrinsicFrontier`,
  `ConvexAnalysis.IsFace.finrank_vectorSpan_lt`: a face other than $C$ lies in the relative boundary
  of $C$ and, if nonempty, has strictly smaller dimension.
* `ConvexAnalysis.exists_isFace_subset_relint`: every nonempty relatively open convex subset of $C$
  lies in the relative interior of a face of $C$.
* `ConvexAnalysis.exists_isFace_mem_relint`, `ConvexAnalysis.eq_iUnion_relint_isFace`,
  `ConvexAnalysis.IsFace.relint_pairwise_disjoint`, `ConvexAnalysis.IsFace.relint_maximal`: the
  relative interiors of the faces partition $C$, and those of the nonempty faces are maximal
  relatively open convex subsets of $C$.
* `ConvexAnalysis.exists_notMem_relint_mem_segment_of_isBounded`: if the line through a relative
  interior point $x$ of a closed set $C$, in a direction of its affine hull, meets $C$ in a bounded
  set, then $x$ lies on a segment that joins two points of $C$ outside $\operatorname{ri} C$.
* `ConvexAnalysis.exists_notMem_relint_mem_segment`: in a compact set of positive dimension, every
  relative interior point lies on such a segment.
* `ConvexAnalysis.convexHull_extremePoints`: **Minkowski's theorem**, a compact convex set is the
  convex hull of its extreme points.

## Notation

* `ri`: the relative interior, `intrinsicInterior ℝ`, from
  `Numlib.Analysis.Convex.RelativeInterior`.

## Implementation notes

* Extreme points and exposed faces are Mathlib's `Set.extremePoints` and `IsExposed`.
  `ConvexAnalysis.isFace_singleton` and `ConvexAnalysis.IsExposed.isFace` connect them to
  `ConvexAnalysis.IsFace`.
* Mathlib's `IsCompact.extremePoints_nonempty` gives the existence of an extreme point of a nonempty
  compact convex set.
-/

open Set

namespace ConvexAnalysis

/-! ### The definition and its elementary properties -/

section Defs

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C C' C'' D : Set E}

/-- A **face** of $C$ in the sense of Rockafellar: a convex subset $C' \subseteq C$ such that
whenever an open segment between two points $x_1, x_2 \in C$ meets $C'$, both endpoints $x_1$
and $x_2$ lie in $C'$.

The segment condition is Mathlib's `IsExtreme ℝ C C'`. The convexity of $C'$ is an additional
requirement: $\{0, 1\}$ is an extreme subset of $[0, 1]$ but not a face of it. Rockafellar
defines faces of convex sets only. The definition here does not require $C$ to be convex, and
the results that need this assume it. -/
structure IsFace (C C' : Set E) : Prop extends IsExtreme ℝ C C' where
  /-- The face is a convex set. -/
  convex : Convex ℝ C'

/-- Every convex set is a face of itself. It is the greatest element of the lattice of faces. -/
protected theorem _root_.Convex.isFace_self (hC : Convex ℝ C) : IsFace C C :=
  ⟨IsExtreme.rfl, hC⟩

/-- The empty set is a face of every set. It is the least element of the lattice of faces. -/
protected theorem IsFace.empty : IsFace C (∅ : Set E) :=
  ⟨⟨empty_subset _, fun _ _ _ _ z hz _ => absurd hz (notMem_empty z)⟩, convex_empty⟩

/-- A face of a face is a face: if $C'$ is a face of $C$ and $C''$ is a face of $C'$, then $C''$ is
a face of $C$. -/
protected theorem IsFace.trans (h₁ : IsFace C C') (h₂ : IsFace C' C'') : IsFace C C'' :=
  ⟨h₁.toIsExtreme.trans h₂.toIsExtreme, h₂.convex⟩

/-- If $C''$ is a face of $C$ and $C'' \subseteq D \subseteq C$, then $C''$ is a face of $D$. -/
protected theorem IsFace.mono (h : IsFace C C'') (hDC : D ⊆ C) (hC''D : C'' ⊆ D) : IsFace D C'' :=
  ⟨h.toIsExtreme.mono hDC hC''D, h.convex⟩

/-- The intersection of two faces of $C$ is a face of $C$. -/
protected theorem IsFace.inter (h₁ : IsFace C C') (h₂ : IsFace C C'') : IsFace C (C' ∩ C'') :=
  ⟨h₁.toIsExtreme.inter h₂.toIsExtreme, h₁.convex.inter h₂.convex⟩

/-- **Cutting a face and its ambient set by the same convex set leaves a face.** If $C'$ is a face
of $C$ and $D$ is convex, then $C' \cap D$ is a face of $C \cap D$.

The set $D$ is cut out of both sets, so this is not `ConvexAnalysis.IsFace.inter`, which
intersects two faces of one set. -/
theorem IsFace.inter_convex (h : IsFace C C') (hD : Convex ℝ D) : IsFace (C ∩ D) (C' ∩ D) :=
  ⟨⟨inter_subset_inter_left D h.subset, fun _ hu _ hv _ hz hseg =>
      ⟨h.left_mem_of_mem_openSegment hu.1 hv.1 hz.1 hseg, hu.2⟩⟩,
    h.convex.inter hD⟩

/-- The intersection of a nonempty family of faces of $C$ is a face of $C$. Together with
`Convex.isFace_self` and `ConvexAnalysis.IsFace.empty`, this makes the faces of a convex set $C$
a complete lattice under inclusion. -/
theorem isFace_sInter {F : Set (Set E)} (hF : F.Nonempty) (h : ∀ B ∈ F, IsFace C B) :
    IsFace C (⋂₀ F) :=
  ⟨isExtreme_sInter hF fun B hB => (h B hB).toIsExtreme,
    convex_sInter fun B hB => (h B hB).convex⟩

/-- The **extreme points** of Rockafellar are the zero-dimensional faces: $\{x\}$ is a face of $C$
if and only if $x$ is an extreme point of $C$ in the sense of Mathlib's `Set.extremePoints`. -/
@[simp]
theorem isFace_singleton {x : E} : IsFace C {x} ↔ x ∈ C.extremePoints ℝ :=
  ⟨fun h => isExtreme_singleton.1 h.toIsExtreme,
    fun h => ⟨isExtreme_singleton.2 h, convex_singleton x⟩⟩

/-- **Exposed faces are faces.** Let $C$ be convex, let $g$ be a linear functional and let
$\alpha \in \mathbb{R}$ with $g(y) \le \alpha$ for all $y \in C$. Then
$C \cap \{w \mid g(w) = \alpha\}$ is a face of $C$.

This is the only source of faces that the partition theorem below uses. -/
theorem _root_.Convex.isFace_inter_setOf_eq (hC : Convex ℝ C) {g : E →ₗ[ℝ] ℝ} {α : ℝ}
    (hmax : ∀ y ∈ C, g y ≤ α) : IsFace C (C ∩ {w | g w = α}) := by
  refine ⟨⟨inter_subset_left, ?_⟩, hC.inter (convex_hyperplane g.isLinear α)⟩
  rintro x hx y hy z ⟨_, hz⟩ ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨hx, ?_⟩
  have hz' : a * g x + b * g y = α := by
    rw [← show g (a • x + b • y) = α from hz, map_add, map_smul, map_smul, smul_eq_mul,
      smul_eq_mul]
  change g x = α
  by_contra hne
  have hlt : g x < α := lt_of_le_of_ne (hmax x hx) hne
  have h1 : a * g x < a * α := mul_lt_mul_of_pos_left hlt ha
  have h2 : b * g y ≤ b * α := mul_le_mul_of_nonneg_left (hmax y hy) hb.le
  have h3 : a * α + b * α = α := by rw [← add_mul, hab, one_mul]
  linarith

end Defs

section Exposed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C C' : Set E}

/-- In a real normed space, an exposed subset of a convex set $C$, in the sense of Mathlib's
`IsExposed`, is a face of $C$. -/
protected theorem IsExposed.isFace (h : IsExposed ℝ C C') (hC : Convex ℝ C) : IsFace C C' :=
  ⟨h.isExtreme, h.convex hC⟩

end Exposed

/-! ### Faces contain the subsets whose relative interior they meet -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C C' C₁ C₂ D : Set E}

omit [FiniteDimensional ℝ E] in
/-- **A face contains every subset of $C$ whose relative interior it meets.** Let $E$ be a real
normed space, let $C'$ be a face of $C$, and let $D \subseteq C$. If
$\operatorname{ri} D \cap C' \neq \emptyset$, then $D \subseteq C'$.

This strengthens the defining segment property from segments to arbitrary sets, and every other
result of this module uses it. The set $D$ need not be convex, and $E$ need not be
finite-dimensional. This is Theorem 18.1 of [rockafellar1970convex]. -/
theorem IsFace.subset_of_relint_inter_nonempty (hface : IsFace C C')
    (hDC : D ⊆ C) (h : (ri D ∩ C').Nonempty) : D ⊆ C' := by
  obtain ⟨z, hzD, hzC'⟩ := h
  intro x hx
  obtain ⟨μ, hμ, hy⟩ := exists_one_lt_smul_mem_of_mem_relint hzD (subset_affineSpan ℝ D hx)
  have hμ0 : (0 : ℝ) < μ := lt_trans zero_lt_one hμ
  have hinv : μ⁻¹ < 1 := by rw [inv_lt_one_iff₀]; exact Or.inr hμ
  refine hface.left_mem_of_mem_openSegment (hDC hx) (hDC hy) hzC' ?_
  exact ⟨1 - μ⁻¹, μ⁻¹, by linarith, inv_pos.2 hμ0, by ring, combo_prolong x z hμ0.ne'⟩

/-- Let $E$ be a finite-dimensional real normed space, let $C \subseteq E$ be convex, and let $C'$
be a face of $C$. Then $C'$ is cut out of $C$ by its own closure:
$$C' = C \cap \operatorname{cl} C'.$$
In particular, a face of a closed convex set is closed. -/
theorem IsFace.eq_inter_closure (hC : Convex ℝ C) (hface : IsFace C C') :
    C' = C ∩ closure C' := by
  refine Subset.antisymm (fun x hx => ⟨hface.subset hx, subset_closure hx⟩) ?_
  rcases C'.eq_empty_or_nonempty with rfl | hne
  · simp
  have hDconv : Convex ℝ (C ∩ closure C') := hC.inter hface.convex.closure
  have hDne : (C ∩ closure C').Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hface.subset hx, subset_closure hx⟩
  have hmeet : ((C ∩ closure C') ∩ ri C').Nonempty := by
    obtain ⟨z, hz⟩ := Convex.relint_nonempty hface.convex hne
    exact ⟨z, ⟨hface.subset (intrinsicInterior_subset hz),
      subset_closure (intrinsicInterior_subset hz)⟩, hz⟩
  have hri : ri (C ∩ closure C') ⊆ ri C' :=
    Convex.relint_subset_relint_of_subset_closure hface.convex hDconv inter_subset_right hmeet
  obtain ⟨z, hz⟩ := Convex.relint_nonempty hDconv hDne
  exact hface.subset_of_relint_inter_nonempty inter_subset_left
    ⟨z, hz, intrinsicInterior_subset (hri hz)⟩

/-- Let $E$ be finite-dimensional. A face of a closed convex set is closed. -/
theorem IsFace.isClosed (hC : Convex ℝ C) (hCcl : IsClosed C) (hface : IsFace C C') :
    IsClosed C' := by
  rw [hface.eq_inter_closure hC]
  exact hCcl.inter isClosed_closure

omit [FiniteDimensional ℝ E] in
/-- Two faces $C_1, C_2$ of $C$ whose relative interiors have a point in common are equal. This
makes the relative interiors of the faces a partition of $C$. -/
theorem IsFace.eq_of_relint_inter_nonempty (h₁ : IsFace C C₁) (h₂ : IsFace C C₂)
    (h : (ri C₁ ∩ ri C₂).Nonempty) : C₁ = C₂ := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  refine Subset.antisymm ?_ ?_
  · exact h₂.subset_of_relint_inter_nonempty h₁.subset ⟨z, hz₁, intrinsicInterior_subset hz₂⟩
  · exact h₁.subset_of_relint_inter_nonempty h₂.subset ⟨z, hz₂, intrinsicInterior_subset hz₁⟩

omit [FiniteDimensional ℝ E] in
/-- A face $C'$ of $C$ with $C' \neq C$ is disjoint from $\operatorname{ri} C$. -/
theorem IsFace.disjoint_relint (hface : IsFace C C') (hne : C' ≠ C) :
    Disjoint C' (ri C) := by
  rw [Set.disjoint_left]
  intro x hxC' hxri
  exact hne (Subset.antisymm hface.subset
    (hface.subset_of_relint_inter_nonempty Subset.rfl ⟨x, hxri, hxC'⟩))

/-- Let $E$ be finite-dimensional. A face $C'$ of $C$ with $C' \neq C$ is contained in the relative
boundary of $C$. -/
theorem IsFace.subset_intrinsicFrontier (hface : IsFace C C') (hne : C' ≠ C) :
    C' ⊆ intrinsicFrontier ℝ C := by
  intro x hx
  rw [← closure_sdiff_intrinsicInterior (𝕜 := ℝ) C]
  exact ⟨subset_closure (hface.subset hx),
    fun hxri => (Set.disjoint_left.1 (hface.disjoint_relint hne)) hx hxri⟩

/-- Let $E$ be finite-dimensional. A nonempty face $C'$ of $C$ with $C' \neq C$ has an affine hull
different from that of $C$. This is the step from the statement about the relative boundary to
the statement about the dimension. -/
theorem IsFace.affineSpan_ne (hface : IsFace C C') (hne' : C'.Nonempty)
    (hne : C' ≠ C) : affineSpan ℝ C' ≠ affineSpan ℝ C := by
  intro hspan
  obtain ⟨z, hz⟩ := Convex.relint_nonempty hface.convex hne'
  refine (Set.disjoint_left.1 (hface.disjoint_relint hne)) (intrinsicInterior_subset hz) ?_
  rw [mem_intrinsicInterior_iff] at hz ⊢
  obtain ⟨hzA, ε, hε, hball⟩ := hz
  exact ⟨hspan ▸ hzA, ε, hε, fun y hy hd => hface.subset (hball y (hspan ▸ hy) hd)⟩

/-- Let $E$ be finite-dimensional, and let $C'$ be a nonempty face of $C$ with $C' \neq C$. Then
$C'$ has strictly smaller dimension than $C$:
$$\dim \operatorname{span}(C' - C') < \dim \operatorname{span}(C - C).$$

The dimension of a set is the dimension of `vectorSpan`, the linear subspace parallel to its
affine hull. -/
theorem IsFace.finrank_vectorSpan_lt (hface : IsFace C C') (hne' : C'.Nonempty)
    (hne : C' ≠ C) :
    Module.finrank ℝ (vectorSpan ℝ C') < Module.finrank ℝ (vectorSpan ℝ C) := by
  have hle : vectorSpan ℝ C' ≤ vectorSpan ℝ C := vectorSpan_mono ℝ hface.subset
  refine lt_of_le_of_ne (Submodule.finrank_mono hle) fun heq => ?_
  have hdir : vectorSpan ℝ C' = vectorSpan ℝ C := Submodule.eq_of_le_of_finrank_eq hle heq
  refine hface.affineSpan_ne hne' hne (AffineSubspace.ext_of_direction_eq ?_ ?_)
  · rw [direction_affineSpan, direction_affineSpan, hdir]
  · obtain ⟨x, hx⟩ := hne'
    exact ⟨x, subset_affineSpan ℝ C' hx, subset_affineSpan ℝ C (hface.subset hx)⟩

/-! ### The relative interiors of the faces partition the set -/

/-- Let $E$ be finite-dimensional, let $C$ be convex, and let $D \subseteq C$ be a nonempty convex
set that is relatively open, $\operatorname{ri} D = D$. Then there is a face $C'$ of $C$ with
$$D \subseteq \operatorname{ri} C'.$$

The face is the smallest face that contains $D$. If $D$ were in the relative boundary of this
face, a supporting hyperplane through $D$ would cut out a strictly smaller face that still
contains $D$. -/
theorem exists_isFace_subset_relint (hC : Convex ℝ C) (hD : Convex ℝ D) (hDC : D ⊆ C)
    (hne : D.Nonempty) (hopen : ri D = D) : ∃ C', IsFace C C' ∧ D ⊆ ri C' := by
  classical
  set F : Set (Set E) := {B | IsFace C B ∧ D ⊆ B} with hFdef
  have hFne : F.Nonempty := ⟨C, Convex.isFace_self hC, hDC⟩
  set C' : Set E := ⋂₀ F with hC'def
  have hC'face : IsFace C C' := isFace_sInter hFne fun B hB => hB.1
  have hDC' : D ⊆ C' := fun x hx => mem_sInter.2 fun B hB => hB.2 hx
  have hmeet : (D ∩ ri C').Nonempty := by
    obtain ⟨x, hxD⟩ := hne
    by_contra hcon
    have hxnot : x ∉ ri C' := fun h => hcon ⟨x, hxD, h⟩
    obtain ⟨g, hle, y, hyC', hyne⟩ :=
      (notMem_relint_iff_exists_isMaxOn hC'face.convex (hDC' hxD)).1 hxnot
    -- `g` is maximised over `C'` at `x ∈ ri D`, hence constant on `D`
    have hxriD : x ∈ ri D := by rw [hopen]; exact hxD
    have hconst : ∀ w ∈ D, (g : E →ₗ[ℝ] ℝ) w = (g : E →ₗ[ℝ] ℝ) x :=
      eq_of_isMaxOn_of_mem_relint (C := D) hxriD fun w hw => hle w (hDC' hw)
    have hface'' : IsFace C' (C' ∩ {w | (g : E →ₗ[ℝ] ℝ) w = (g : E →ₗ[ℝ] ℝ) x}) :=
      Convex.isFace_inter_setOf_eq hC'face.convex fun w hw => hle w hw
    have hmem : C' ∩ {w | (g : E →ₗ[ℝ] ℝ) w = (g : E →ₗ[ℝ] ℝ) x} ∈ F :=
      ⟨hC'face.trans hface'', fun w hw => ⟨hDC' hw, hconst w hw⟩⟩
    exact hyne (mem_sInter.1 (hC'def ▸ hyC') _ hmem).2
  have hsub : ri D ⊆ ri C' :=
    Convex.relint_subset_relint_of_subset_closure hC'face.convex hD (hDC'.trans subset_closure)
      hmeet
  exact ⟨C', hC'face, hopen ▸ hsub⟩

/-- Let $E$ be finite-dimensional and let $C$ be convex. Every point $x \in C$ is a relative
interior point of some face of $C$. This is the union half of the partition. -/
theorem exists_isFace_mem_relint (hC : Convex ℝ C) {x : E} (hx : x ∈ C) :
    ∃ C', IsFace C C' ∧ x ∈ ri C' := by
  obtain ⟨C', hface, hsub⟩ := exists_isFace_subset_relint hC (convex_singleton x)
    (singleton_subset_iff.2 hx) ⟨x, rfl⟩ (intrinsicInterior_singleton x)
  exact ⟨C', hface, hsub rfl⟩

/-- Let $E$ be finite-dimensional and let $C$ be convex. Then $C$ is the union of the relative
interiors of its faces:
$$C = \bigcup_{C' \text{ a face of } C} \operatorname{ri} C'.$$
-/
theorem eq_iUnion_relint_isFace (hC : Convex ℝ C) :
    C = ⋃ C' ∈ {B : Set E | IsFace C B}, ri C' := by
  refine Subset.antisymm (fun x hx => ?_) ?_
  · obtain ⟨C', hface, hmem⟩ := exists_isFace_mem_relint hC hx
    exact mem_biUnion hface hmem
  · exact iUnion₂_subset fun C' hface => intrinsicInterior_subset.trans hface.subset

omit [FiniteDimensional ℝ E] in
/-- Two distinct faces $C_1 \neq C_2$ of $C$ have disjoint relative interiors. This is the
disjointness half of the partition. -/
theorem IsFace.relint_pairwise_disjoint (h₁ : IsFace C C₁) (h₂ : IsFace C C₂) (hne : C₁ ≠ C₂) :
    Disjoint (ri C₁) (ri C₂) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hcon
  exact hne (h₁.eq_of_relint_inter_nonempty h₂ (nonempty_iff_ne_empty.2 hcon))

/-- Let $E$ be finite-dimensional, let $C$ be convex, and let $C'$ be a nonempty face of $C$. If $D$
is a relatively open convex set with $\operatorname{ri} C' \subseteq D \subseteq C$, then
$D = \operatorname{ri} C'$. Thus the relative interior of a nonempty face is a maximal
relatively open convex subset of $C$. -/
theorem IsFace.relint_maximal (hC : Convex ℝ C) (hface : IsFace C C') (hne' : C'.Nonempty)
    (hD : Convex ℝ D) (hopen : ri D = D) (hsub : ri C' ⊆ D) (hDC : D ⊆ C) : D = ri C' := by
  obtain ⟨z, hz⟩ := Convex.relint_nonempty hface.convex hne'
  obtain ⟨C'', hface'', hDsub⟩ := exists_isFace_subset_relint hC hD hDC ⟨z, hsub hz⟩ hopen
  have : C' = C'' := hface.eq_of_relint_inter_nonempty hface'' ⟨z, hz, hDsub (hsub hz)⟩
  exact Subset.antisymm (this ▸ hDsub) hsub

/-- The relative interior of a face is relatively open: $\operatorname{ri}(\operatorname{ri} C') =
\operatorname{ri} C'$. Hence `ConvexAnalysis.IsFace.relint_maximal` is a maximality statement
inside the family over which it quantifies. -/
theorem IsFace.relint_relint (hface : IsFace C C') : ri (ri C') = ri C' :=
  Convex.relint_relint hface.convex

end Main

/-! ### The bounded case: Minkowski's theorem -/

section Bounded

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {C : Set E}

omit [FiniteDimensional ℝ E] in
/-- **The analytic core of the segment theorem.** Let $C$ be a closed subset of a real normed space,
let $x \in \operatorname{ri} C$, and let $d \neq 0$ be a direction parallel to the affine hull
of $C$. If the set $\{t \in \mathbb{R} \mid x + td \in C\}$ is bounded, then there are
$a, b \in C$ with $a, b \notin \operatorname{ri} C$ and $x \in [a, b]$.

The points $a$ and $b$ are the two ends of the intersection of $C$ with the line through $x$ in
the direction $d$. The convexity of $C$ is not used. -/
theorem exists_notMem_relint_mem_segment_of_isBounded {x d : E} (hCcl : IsClosed C) (hd0 : d ≠ 0)
    (hd : d ∈ vectorSpan ℝ C) (hx : x ∈ ri C)
    (hbdd : Bornology.IsBounded {t : ℝ | x + t • d ∈ C}) :
    ∃ a ∈ C, ∃ b ∈ C, a ∉ ri C ∧ b ∉ ri C ∧ x ∈ segment ℝ a b := by
  have hdnorm : 0 < ‖d‖ := norm_pos_iff.2 hd0
  have hxC : x ∈ C := intrinsicInterior_subset hx
  set T : Set ℝ := {t : ℝ | x + t • d ∈ C} with hTdef
  have hline : ∀ t : ℝ, x + t • d ∈ affineSpan ℝ C := by
    intro t
    have hv : t • d ∈ (affineSpan ℝ C).direction := by
      rw [direction_affineSpan]
      exact Submodule.smul_mem _ t hd
    have hmem := AffineSubspace.vadd_mem_of_mem_direction hv (subset_affineSpan ℝ C hxC)
    rwa [vadd_eq_add, add_comm] at hmem
  have hcont : Continuous fun t : ℝ => x + t • d := by fun_prop
  have hTclosed : IsClosed T := hCcl.preimage hcont
  have hTcomp : IsCompact T := Metric.isCompact_of_isClosed_isBounded hTclosed hbdd
  have hT0 : (0 : ℝ) ∈ T := by
    change x + (0 : ℝ) • d ∈ C
    simpa using hxC
  obtain ⟨tp, htp⟩ := hTcomp.exists_isGreatest ⟨0, hT0⟩
  obtain ⟨tm, htm⟩ := hTcomp.exists_isLeast ⟨0, hT0⟩
  obtain ⟨hxA, ε, hε, hball⟩ := mem_intrinsicInterior_iff.1 hx
  set s : ℝ := ε / (2 * ‖d‖) with hsdef
  have hspos : 0 < s := by positivity
  have hsT : ∀ u : ℝ, |u| ≤ s → u ∈ T := by
    intro u hu
    refine hball _ (hline u) ?_
    have he : x + u • d - x = u • d := by module
    rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs]
    have hprod : |u| * ‖d‖ ≤ s * ‖d‖ := by nlinarith
    have hs' : s * ‖d‖ = ε / 2 := by
      rw [hsdef]
      field_simp
    linarith [hs' ▸ hprod]
  have htppos : 0 < tp := lt_of_lt_of_le hspos (htp.2 (hsT s (le_of_eq (abs_of_pos hspos))))
  have htmneg : tm < 0 := by
    have hle := htm.2 (hsT (-s) (by rw [abs_neg, abs_of_pos hspos]))
    linarith
  have hgap : (0 : ℝ) < tp - tm := by linarith
  refine ⟨x + tm • d, htm.1, x + tp • d, htp.1, ?_, ?_, ?_⟩
  · intro hari
    obtain ⟨μ, hμ, hw⟩ := exists_one_lt_smul_mem_of_mem_relint hari (hline tp)
    have heq : (1 - μ) • (x + tp • d) + μ • (x + tm • d)
        = x + ((1 - μ) * tp + μ * tm) • d := by module
    rw [heq] at hw
    have hmem : (1 - μ) * tp + μ * tm ∈ T := hw
    nlinarith [htm.2 hmem, mul_pos (sub_pos.2 hμ) hgap]
  · intro hbri
    obtain ⟨μ, hμ, hw⟩ := exists_one_lt_smul_mem_of_mem_relint hbri (hline tm)
    have heq : (1 - μ) • (x + tm • d) + μ • (x + tp • d)
        = x + ((1 - μ) * tm + μ * tp) • d := by module
    rw [heq] at hw
    have hmem : (1 - μ) * tm + μ * tp ∈ T := hw
    nlinarith [htp.2 hmem, mul_pos (sub_pos.2 hμ) hgap]
  · refine ⟨tp / (tp - tm), -tm / (tp - tm), div_nonneg htppos.le hgap.le,
      div_nonneg (neg_nonneg.2 htmneg.le) hgap.le, by field_simp; ring, ?_⟩
    match_scalars <;> field_simp <;> ring

omit [FiniteDimensional ℝ E] in
/-- Let $C$ be a compact subset of a real normed space with positive dimension, that is,
$\operatorname{span}(C - C) \neq 0$. Then every $x \in \operatorname{ri} C$ lies on a segment
$[a, b]$ with $a, b \in C$ and $a, b \notin \operatorname{ri} C$.

The general form of this statement asks that $C$ be a closed convex set that is neither an
affine set nor a closed half of an affine set. Compactness is a stronger hypothesis, but it is
all that Minkowski's theorem needs. The convexity of $C$ is not used. -/
theorem exists_notMem_relint_mem_segment (hcomp : IsCompact C) (hdim : vectorSpan ℝ C ≠ ⊥)
    {x : E} (hx : x ∈ ri C) :
    ∃ a ∈ C, ∃ b ∈ C, a ∉ ri C ∧ b ∉ ri C ∧ x ∈ segment ℝ a b := by
  obtain ⟨d, hdmem, hdne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hdim
  refine exists_notMem_relint_mem_segment_of_isBounded hcomp.isClosed hdne hdmem hx ?_
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall x).1 hcomp.isBounded
  refine (Metric.isBounded_Icc (-(R / ‖d‖)) (R / ‖d‖)).subset fun t ht => ?_
  have hmem : x + t • d ∈ Metric.closedBall x R := hR ht
  rw [Metric.mem_closedBall, dist_eq_norm] at hmem
  have he : x + t • d - x = t • d := by module
  rw [he, norm_smul, Real.norm_eq_abs] at hmem
  exact Set.mem_Icc.2 (abs_le.1 ((le_div_iff₀ (norm_pos_iff.2 hdne)).2 hmem))

/-- The induction behind Minkowski's theorem: for every $n$, a compact convex set of dimension at
most $n$ is contained in the convex hull of its extreme points. -/
private theorem subset_convexHull_extremePoints_aux :
    ∀ (n : ℕ) (C : Set E), Module.finrank ℝ (vectorSpan ℝ C) ≤ n → IsCompact C → Convex ℝ C →
      C ⊆ convexHull ℝ (C.extremePoints ℝ) := by
  intro n
  induction n with
  | zero =>
    intro C hcard _ _ x hx
    have hbot : vectorSpan ℝ C = ⊥ := Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hcard)
    have hCx : C = {x} := ((vectorSpan_eq_bot_iff_subsingleton ℝ).1 hbot).eq_singleton_of_mem hx
    rw [hCx, extremePoints_singleton, convexHull_singleton]
    exact rfl
  | succ n ih =>
    intro C hcard hcomp hconv x hx
    -- a relative boundary point sits in the relative interior of a strictly smaller face
    have hbd : ∀ y ∈ C, y ∉ ri C → y ∈ convexHull ℝ (C.extremePoints ℝ) := by
      intro y hy hyri
      obtain ⟨C', hface, hyC'⟩ := exists_isFace_mem_relint hconv hy
      have hC'ne : C' ≠ C := fun h => hyri (h ▸ hyC')
      have hC'comp : IsCompact C' :=
        hcomp.of_isClosed_subset (hface.isClosed hconv hcomp.isClosed) hface.subset
      have hlt : Module.finrank ℝ (vectorSpan ℝ C') < Module.finrank ℝ (vectorSpan ℝ C) :=
        hface.finrank_vectorSpan_lt ⟨y, intrinsicInterior_subset hyC'⟩ hC'ne
      exact convexHull_mono hface.toIsExtreme.extremePoints_subset_extremePoints
        (ih C' (by omega) hC'comp hface.convex (intrinsicInterior_subset hyC'))
    by_cases hri : x ∈ ri C
    · by_cases hbot : vectorSpan ℝ C = ⊥
      · have hCx : C = {x} := ((vectorSpan_eq_bot_iff_subsingleton ℝ).1 hbot).eq_singleton_of_mem hx
        rw [hCx, extremePoints_singleton, convexHull_singleton]
        exact rfl
      · obtain ⟨a, haC, b, hbC, hari, hbri, hseg⟩ :=
          exists_notMem_relint_mem_segment hcomp hbot hri
        exact (convex_convexHull ℝ _).segment_subset (hbd a haC hari) (hbd b hbC hbri) hseg
    · exact hbd x hx hri

/-- **Minkowski's theorem.** Let $E$ be a finite-dimensional real normed space, and let
$C \subseteq E$ be compact and convex. Then $C$ is the convex hull of its extreme points:
$$\operatorname{conv}(\operatorname{ext} C) = C.$$

This is the case of the general representation theorem in which $C$ has no direction of
recession. It is stronger than Mathlib's Krein–Milman theorem
`closure_convexHull_extremePoints`, which gives only the closed convex hull: the set of extreme
points need not be closed, even for compact $C$. The proof is an induction on the dimension of
$C$, through the partition of $C$ by the relative interiors of its faces and
`ConvexAnalysis.exists_notMem_relint_mem_segment`. -/
theorem convexHull_extremePoints (hcomp : IsCompact C) (hconv : Convex ℝ C) :
    convexHull ℝ (C.extremePoints ℝ) = C :=
  Subset.antisymm (convexHull_min extremePoints_subset hconv)
    (subset_convexHull_extremePoints_aux _ C le_rfl hcomp hconv)

end Bounded

end ConvexAnalysis
