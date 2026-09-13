import Numlib.Analysis.Convex.Exposed
import Numlib.Analysis.Convex.Face
import Numlib.Analysis.Convex.Representation
import Numlib.Analysis.Convex.Tangent
import NumlibSurface.Rockafellar.Part2.Section06

/-!
# Rockafellar, §18: Extreme Points and Faces of Convex Sets

The facial structure of a convex set, the internal representations `C = conv S` and
`C = cl (conv S)` it produces, and the external representation dual to the second.

All sixteen numbered results of §18 are formalized over `Rn n = ℝⁿ`: Theorems 18.1–18.8 and
Corollaries 18.1.1–18.1.3, 18.3.1, 18.5.1–18.5.3, 18.7.1.

A face is the backbone's `IsFace`, Rockafellar's definition verbatim, and an extreme point is
Mathlib's `Set.extremePoints ℝ`, a zero-dimensional face. A *direction* is recorded by a generating
vector rather than by a quotient, so `extremeDirections C` is closed under positive scaling; and
`conv S`, for `S` a set of points and directions, is `convexHullPD P D`.

Several statements here are more general than the book's, or supply what it omits. `theorem_18_1`
and `theorem_18_3` drop hypotheses the book states. `theorem_18_5_lineality` is the "obvious
extension" of Theorem 18.5 to a closed convex set of arbitrary lineality, which the book states in
words and never proves, and `facesEquivFacesInterOrthogonal` is the face correspondence it asserts
"evidently" on p. 166. Corollaries 18.5.2 and 18.7.1 do not need the cone to contain more than the
origin, and Corollary 18.7.1 is printed with no proof at all.

## References

* [rockafellar1970convex] §18.
-/

open Set

namespace Rockafellar

open ConvexAnalysis NumlibSurface
open scoped Pointwise

variable {n : ℕ} {C C' C₁ C₂ D : Set (Rn n)}

/-! ### Faces (p. 162) -/

/-- **§18 (p. 162).** A **face** of a convex set `C` is a convex subset `C'` of `C` such that every
closed line segment in `C` with a relative interior point in `C'` has both endpoints in `C'`.
Convexity of `C'` is a genuine extra requirement: `{0, 1}` is an extreme subset of `[0, 1]` but not
a face of it. -/
theorem isFace_iff : IsFace C C' ↔ Convex ℝ C' ∧ C' ⊆ C ∧
    ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C', z ∈ openSegment ℝ x y → x ∈ C' ∧ y ∈ C' :=
  ⟨fun h => ⟨h.convex, h.subset, fun _ hx _ hy _ hz hseg =>
      ⟨h.toIsExtreme.left_mem_of_mem_openSegment hx hy hz hseg,
        h.toIsExtreme.right_mem_of_mem_openSegment hx hy hz hseg⟩⟩,
    fun h => ⟨⟨h.2.1, fun _ hx _ hy _ hz hseg => (h.2.2 _ hx _ hy _ hz hseg).1⟩, h.1⟩⟩

theorem isFace_self (hC : Convex ℝ C) : IsFace C C := Convex.isFace_self hC

theorem isFace_empty : IsFace C (∅ : Set (Rn n)) := IsFace.empty

theorem isFace_trans (h₁ : IsFace C C') (h₂ : IsFace C' C₁) : IsFace C C₁ := h₁.trans h₂

/-- **§18 (p. 163).** A face of `C` is a fortiori a face of any convex `D` with `C' ⊆ D ⊆ C`. -/
theorem isFace_mono (h : IsFace C C') (hDC : D ⊆ C) (hC'D : C' ⊆ D) : IsFace D C' :=
  h.mono hDC hC'D

/-- **§18 (p. 162).** The **extreme points** of `C` are its zero-dimensional faces. -/
theorem isFace_singleton_iff {x : Rn n} : IsFace C {x} ↔ x ∈ C.extremePoints ℝ :=
  isFace_singleton

/-- **§18 (p. 162)**, the book's wording: `x ∈ C` is extreme iff `x = (1 - λ) y + λ z` with
`y, z ∈ C` and `0 < λ < 1` forces `y = z = x`. -/
theorem mem_extremePoints_iff {x : Rn n} :
    x ∈ C.extremePoints ℝ ↔ x ∈ C ∧ ∀ y ∈ C, ∀ z ∈ C, ∀ l : ℝ, 0 < l → l < 1 →
      x = (1 - l) • y + l • z → y = x ∧ z = x := by
  rw [mem_extremePoints]
  refine and_congr_right fun _ => ⟨fun h y hy z hz l hl0 hl1 heq => ?_, fun h y hy z hz hseg => ?_⟩
  · exact h y hy z hz ⟨1 - l, l, by linarith, hl0, by ring, heq.symm⟩
  · obtain ⟨a, b, ha, hb, hab, hval⟩ := hseg
    exact h y hy z hz b hb (by linarith) (by rw [← hval, show (1 : ℝ) - b = a by linarith])

/-! ### The lattice of faces (p. 164) -/

/-- **§18 (p. 164).** A non-empty intersection of faces of `C` is a face, and is their greatest
lower bound in `F(C)`. -/
theorem faces_isGLB {F : Set (Set (Rn n))} (hF : F.Nonempty) (h : ∀ B ∈ F, IsFace C B) :
    IsFace C (⋂₀ F) ∧ IsGLB F (⋂₀ F) :=
  ⟨isFace_sInter hF h,
    ⟨fun _ hB => sInter_subset_of_mem hB, fun _ hB => subset_sInter fun _ hC' => hB hC'⟩⟩

/-- **§18 (p. 164).** Every set of faces of `C` has a least upper bound in `F(C)`; with
`faces_isGLB` this makes `F(C)` a complete lattice under inclusion. -/
theorem faces_isLUB (hC : Convex ℝ C) (F : Set (Set (Rn n))) (h : ∀ B ∈ F, IsFace C B) :
    ∃ G, IsFace C G ∧ (∀ B ∈ F, B ⊆ G) ∧ ∀ G', IsFace C G' → (∀ B ∈ F, B ⊆ G') → G ⊆ G' :=
  ⟨⋂₀ {H | IsFace C H ∧ ∀ B ∈ F, B ⊆ H},
    isFace_sInter ⟨C, Convex.isFace_self hC, fun B hB => (h B hB).subset⟩ fun _ hH => hH.1,
    fun _ hB _ hx => mem_sInter.2 fun _ hH => hH.2 _ hB hx,
    fun _ hG' hsub => sInter_subset_of_mem ⟨hG', hsub⟩⟩

/-! ### Theorem 18.1 and its corollaries -/

/-- **Theorem 18.1**. If `C'` is a face of `C` and `D ⊆ C` has a relative interior point in `C'`,
then `D ⊆ C'`. The book also assumes `D` convex; the proof uses only the prolongation lemma of §6,
which says nothing about `D` beyond `ri D`. -/
theorem theorem_18_1 (hface : IsFace C C') (hDC : D ⊆ C) (h : (ri D ∩ C').Nonempty) : D ⊆ C' :=
  hface.subset_of_relint_inter_nonempty hDC h

/-- **Corollary 18.1.1**. A face of a convex set `C` satisfies `C' = C ∩ cl C'`. -/
theorem corollary_18_1_1 (hC : Convex ℝ C) (hface : IsFace C C') : C' = C ∩ closure C' :=
  hface.eq_inter_closure hC

/-- **Corollary 18.1.1**, second sentence: a face of a closed convex set is closed. -/
theorem corollary_18_1_1_isClosed (hC : Convex ℝ C) (hCcl : IsClosed C) (hface : IsFace C C') :
    IsClosed C' :=
  hface.isClosed hC hCcl

/-- **Corollary 18.1.2**. Two faces of `C` whose relative interiors meet are equal. -/
theorem corollary_18_1_2 (h₁ : IsFace C C₁) (h₂ : IsFace C C₂) (h : (ri C₁ ∩ ri C₂).Nonempty) :
    C₁ = C₂ :=
  h₁.eq_of_relint_inter_nonempty h₂ h

/-- **Corollary 18.1.3**. A face of `C` other than `C` lies in the relative boundary of `C`. -/
theorem corollary_18_1_3 (hface : IsFace C C') (hne : C' ≠ C) : C' ⊆ relbd C := by
  rw [relbd_eq_intrinsicFrontier]
  exact hface.subset_intrinsicFrontier hne

/-- **Corollary 18.1.3**, the dimension statement: a non-empty face other than `C` itself has
`dim C' < dim C`. -/
theorem corollary_18_1_3_dim (hC : Convex ℝ C) (hface : IsFace C C') (hne' : C'.Nonempty)
    (hne : C' ≠ C) : dim C' < dim C :=
  corollary_6_3_3 hface.convex hC (hne'.mono hface.subset) (corollary_18_1_3 hface hne)

/-! ### Theorem 18.2: the relative interiors of the faces partition `C` -/

/-- **Theorem 18.2**, the union half: the relative interiors of the faces of `C` cover `C`.
(`ri ∅ = ∅`, so the empty face contributes nothing.) -/
theorem theorem_18_2_union (hC : Convex ℝ C) : C = ⋃ C' ∈ {B : Set (Rn n) | IsFace C B}, ri C' :=
  eq_iUnion_relint_isFace hC

/-- **Theorem 18.2**, the disjointness half: the relative interiors of distinct faces are disjoint,
so with `theorem_18_2_union` they partition `C`. -/
theorem theorem_18_2_disjoint (h₁ : IsFace C C₁) (h₂ : IsFace C C₂) (hne : C₁ ≠ C₂) :
    Disjoint (ri C₁) (ri C₂) :=
  h₁.relint_pairwise_disjoint h₂ hne

/-- **Theorem 18.2**, the containment half: every non-empty relatively open convex subset of `C`
lies in the relative interior of some face. -/
theorem theorem_18_2_subset (hC : Convex ℝ C) (hD : Convex ℝ D) (hDC : D ⊆ C) (hne : D.Nonempty)
    (hopen : IsRelativelyOpen D) : ∃ C', IsFace C C' ∧ D ⊆ ri C' :=
  exists_isFace_subset_relint hC hD hDC hne hopen

/-- **Theorem 18.2**, the maximality half: the relative interiors of the non-empty faces of `C` are
exactly the maximal relatively open convex subsets of `C`. -/
theorem theorem_18_2_maximal (hC : Convex ℝ C) (hface : IsFace C C') (hne' : C'.Nonempty)
    (hD : Convex ℝ D) (hopen : IsRelativelyOpen D) (hsub : ri C' ⊆ D) (hDC : D ⊆ C) :
    D = ri C' :=
  hface.relint_maximal hC hne' hD hopen hsub hDC

/-! ### Theorem 18.3: the faces of a hull of points and directions -/

/-- **Theorem 18.3**. If `C = conv S` for a set `S` of points and directions and `C'` is a face of
`C`, then `C' = conv S'`, where `S'` consists of the points of `S` lying in `C'` and the directions
of `S` in which `C'` recedes. The book's hypothesis that `C'` be non-empty is not needed. -/
theorem theorem_18_3 {P D : Set (Rn n)} (hface : IsFace (convexHullPD P D) C') :
    C' = convexHullPD (P ∩ C') {y ∈ D | y ∈ recessionCone C'} :=
  hface.eq_convexHullPD

/-- **Corollary 18.3.1**, first half: every extreme point of `conv S` is a point of `S`. -/
theorem corollary_18_3_1_points (P D : Set (Rn n)) :
    (convexHullPD P D).extremePoints ℝ ⊆ P :=
  extremePoints_convexHullPD_subset P D

/-- **Corollary 18.3.1**, second half: if no half-line contains an unbounded set of points of `S`,
every extreme direction of `conv S` is a direction of `S` — a positive multiple of a vector of
`D`. -/
theorem corollary_18_3_1_directions (P D : Set (Rn n))
    (hP : ∀ x z : Rn n, Bornology.IsBounded (P ∩ halfLine x z)) {y : Rn n}
    (hy : y ∈ extremeDirections (convexHullPD P D)) : ∃ z ∈ D, ∃ a : ℝ, 0 < a ∧ y = a • z :=
  exists_mem_eq_smul_of_mem_extremeDirections P D hP hy

/-- **Corollary 18.3.1**, second half in the case the book highlights: all points of `S` bounded. -/
theorem corollary_18_3_1_directions_of_isBounded (P D : Set (Rn n))
    (hP : Bornology.IsBounded P) {y : Rn n}
    (hy : y ∈ extremeDirections (convexHullPD P D)) : ∃ z ∈ D, ∃ a : ℝ, 0 < a ∧ y = a • z :=
  exists_mem_eq_smul_of_mem_extremeDirections_of_isBounded P D hP hy

/-! ### Theorem 18.4: a closed convex set is the hull of its relative boundary -/

/-- **Theorem 18.4**. If a closed convex set `C` is neither an affine set nor a closed half of one,
every relative interior point of `C` lies on a segment joining two relative boundary points. The
book's two exceptional cases are the single predicate `IsAffineHalf`: allowing the functional to be
`0` makes "affine set" the degenerate case of "closed half of an affine set". -/
theorem theorem_18_4 (hC : Convex ℝ C) (hCcl : IsClosed C) (hhalf : ¬ IsAffineHalf C) {x : Rn n}
    (hx : x ∈ ri C) : ∃ a ∈ relbd C, ∃ b ∈ relbd C, x ∈ segment ℝ a b := by
  obtain ⟨a, haC, b, hbC, hari, hbri, hseg⟩ :=
    exists_notMem_relint_mem_segment_of_not_isAffineHalf hC hCcl hhalf hx
  exact ⟨a, ⟨subset_closure haC, hari⟩, b, ⟨subset_closure hbC, hbri⟩, hseg⟩

/-! ### Theorem 18.5: the fundamental internal representation -/

/-- **Theorem 18.5**. A closed convex set containing no lines is `conv S`, for `S` the set of its
extreme points and extreme directions. -/
theorem theorem_18_5 (hC : Convex ℝ C) (hCcl : IsClosed C) (hnl : ContainsNoLine C) :
    convexHullPD (C.extremePoints ℝ) (extremeDirections C) = C :=
  convexHullPD_extremePoints_extremeDirections hC hCcl hnl

/-- **Theorem 18.5** for a closed convex set of arbitrary lineality — the "obvious extension" of
p. 166, which the book states in words and never proves. With `L` the lineality space of `C` and
`C₀ = C ∩ L^⊥`, one has `C = L + conv S₀` for `S₀` the extreme points and extreme directions of
`C₀`; `C₀` contains no lines because the direction of such a line would lie in both `L` and
`L^⊥`. -/
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

/-- **§18 (p. 166).** A face splits as `C' = C₀' + L`, with `L` the lineality space of `C` and
`C₀' = C' ∩ L^⊥`: a face absorbs the lineality of the set it is a face of. -/
theorem eq_add_inter_orthogonal_of_isFace (h : IsFace C C') :
    C' = (linealitySubmodule C : Set (Rn n)) +
      (C' ∩ ((linealitySubmodule C)ᗮ : Set (Rn n))) :=
  h.eq_add_inter_of_isCompl_of_le (coe_linealitySubmodule C).subset
    (Submodule.isCompl_orthogonal _)

/-- **§18 (p. 166).** With `L` the lineality space of `C` and `C₀ = C ∩ L^⊥`, the faces of `C`
correspond one-to-one with those of `C₀`, by `C' = C₀' + L` and `C₀' = C' ∩ L^⊥`. The book asserts
this "evidently"; nothing in it needs `C` closed, convex or finite-dimensional, only that `L^⊥` is
a complement of `L`. -/
noncomputable def facesEquivFacesInterOrthogonal (A : Set (Rn n)) :
    {C' : Set (Rn n) // IsFace A C'} ≃
      {C₀ : Set (Rn n) // IsFace (A ∩ ((linealitySubmodule A)ᗮ : Set (Rn n))) C₀} :=
  isFaceEquivInter (coe_linealitySubmodule A).subset (Submodule.isCompl_orthogonal _)

/-- **Corollary 18.5.1** (Minkowski's theorem). A closed bounded convex set is the convex hull of
its extreme points. -/
theorem corollary_18_5_1 (hC : Convex ℝ C) (hCcl : IsClosed C) (hbdd : Bornology.IsBounded C) :
    convexHull ℝ (C.extremePoints ℝ) = C :=
  convexHull_extremePoints (Metric.isCompact_of_isClosed_isBounded hCcl hbdd) hC

/-- **Corollary 18.5.3**. A non-empty closed convex set containing no lines has an extreme
point. -/
theorem corollary_18_5_3 (hC : Convex ℝ C) (hCcl : IsClosed C) (hnl : ContainsNoLine C)
    (hne : C.Nonempty) : (C.extremePoints ℝ).Nonempty :=
  extremePoints_nonempty_of_containsNoLine hC hCcl hnl hne

/-! ### Rays of a convex cone (p. 162)

For a cone the useful zero-dimensional object is not an extreme point — the origin is the only
candidate — but an extreme *ray*: a face which is a half-line emanating from the origin. -/

/-- **§18 (p. 162).** An **extreme ray** of a convex cone `K` is a face of `K` which is a half-line
emanating from the origin, recorded by a generating vector. -/
def IsExtremeRay (K : Set (Rn n)) (y : Rn n) : Prop := y ≠ 0 ∧ IsFace K (halfLine 0 y)

/-- **§18 (p. 162).** An **exposed ray** of a convex cone `K` is an exposed face of `K` which is a
half-line emanating from the origin. -/
def IsExposedRay (K : Set (Rn n)) (y : Rn n) : Prop := y ≠ 0 ∧ IsExposed ℝ K (halfLine 0 y)

/-- **A half-line extreme subset of a cone starts at the origin.** This is the content of the
book's assertion that the extreme rays of a convex cone are in one-to-one correspondence with its
extreme directions. -/
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

/-- **§18 (p. 162).** For a convex cone, extreme rays and extreme directions are the same data. -/
theorem isExtremeRay_iff_isExtremeDirection {K : Set (Rn n)} (hne : K.Nonempty)
    (hcone : ∀ x ∈ K, ∀ a : ℝ, 0 ≤ a → a • x ∈ K) {y : Rn n} :
    IsExtremeRay K y ↔ IsExtremeDirection K y := by
  refine ⟨fun h => ⟨h.1, 0, h.2⟩, fun h => ⟨h.1, ?_⟩⟩
  obtain ⟨x, hface⟩ := h.2
  rwa [eq_zero_of_isExtreme_halfLine hne hcone h.1 hface.toIsExtreme] at hface

theorem isExposedRay_iff_isExposedDirection {K : Set (Rn n)} (hne : K.Nonempty)
    (hcone : ∀ x ∈ K, ∀ a : ℝ, 0 ≤ a → a • x ∈ K) {y : Rn n} :
    IsExposedRay K y ↔ IsExposedDirection K y := by
  refine ⟨fun h => ⟨h.1, 0, h.2⟩, fun h => ⟨h.1, ?_⟩⟩
  obtain ⟨x, hexp⟩ := h.2
  rwa [eq_zero_of_isExtreme_halfLine hne hcone h.1 hexp.isExtreme] at hexp

/-- A non-empty closed cone in Rockafellar's sense — closed under *positive* scalar multiplication
— is closed under non-negative scaling, which is the form the backbone's cone theorems take. -/
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

/-- **Corollary 18.5.2**. If `K` is a closed convex cone containing no lines and every extreme ray
of `K` is generated by some `x ∈ T ⊆ K`, then `K` is the convex cone generated by `T`. The book's
"containing more than just the origin" is unnecessary: the zero cone has no extreme rays, so the
hypothesis on `T` is vacuous and both sides are `{0}`. -/
theorem corollary_18_5_2 {K T : Set (Rn n)} (hK : Convex ℝ K) (hKcl : IsClosed K)
    (hcone : IsCone K) (hne : K.Nonempty) (hnl : ContainsNoLine K) (hTK : T ⊆ K)
    (hgen : ∀ y, IsExtremeRay K y → ∃ x ∈ T, ∃ a : ℝ, 0 < a ∧ y = a • x) :
    (PointedCone.hull ℝ T : Set (Rn n)) = K := by
  have hsmul := forall_smul_mem_of_isCone hcone hKcl
  exact coneHull_of_forall_extremeDirection hK hKcl hne hsmul hnl hTK fun y hy =>
    hgen y ((isExtremeRay_iff_isExtremeDirection hne hsmul).2 hy)

/-! ### Directions at infinity pass to the recession cone (p. 163)

If `C'` is a half-line face of a closed convex set `C` with endpoint `x` then `C' ⊆ x + 0⁺C ⊆ C` by
Theorem 8.3, so `C' - x` is an extreme ray of `0⁺C`. The converse fails: a parabolic set in `ℝ²`
has no half-line face at all, while its recession cone is a ray. -/

/-- **§18 (p. 163).** Every extreme direction of a closed convex set `C` is an extreme direction of
`0⁺C` — sharper than Theorem 8.3, which gives only that it is a direction of recession. -/
theorem subset_extremeDirections_recessionCone (hC : Convex ℝ C) (hCcl : IsClosed C) :
    extremeDirections C ⊆ extremeDirections (recessionCone C) :=
  extremeDirections_subset_extremeDirections_recessionCone hC hCcl

/-- **§18 (p. 163).** Every exposed direction of a closed convex set `C` is one of `0⁺C`. -/
theorem subset_exposedDirections_recessionCone (hC : Convex ℝ C) (hCcl : IsClosed C) :
    exposedDirections C ⊆ exposedDirections (recessionCone C) :=
  exposedDirections_subset_exposedDirections_recessionCone hC hCcl

/-- **§18 (p. 163)**, in the book's own wording: if `C'` is a half-line face of the closed convex
set `C` with endpoint `x`, then `C' - x` is an extreme **ray** of the cone `0⁺C`. -/
theorem isExtremeRay_recessionCone {y : Rn n} (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hy : IsExtremeDirection C y) : IsExtremeRay (recessionCone C) y :=
  (isExtremeRay_iff_isExtremeDirection ⟨0, zero_mem_recessionCone C⟩
    fun _ hx _ ha => smul_mem_recessionCone ha hx).2
    (subset_extremeDirections_recessionCone hC hCcl hy)

theorem isExposedRay_recessionCone {y : Rn n} (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hy : IsExposedDirection C y) : IsExposedRay (recessionCone C) y :=
  (isExposedRay_iff_isExposedDirection ⟨0, zero_mem_recessionCone C⟩
    fun _ hx _ ha => smul_mem_recessionCone ha hx).2
    (subset_exposedDirections_recessionCone hC hCcl hy)

/-! ### Theorem 18.6: Straszewicz's theorem -/

/-- **Theorem 18.6** (Straszewicz's Theorem). Every extreme point of a closed convex set is the
limit of a sequence of exposed points. -/
theorem theorem_18_6 (hC : Convex ℝ C) (hCcl : IsClosed C) :
    C.extremePoints ℝ ⊆ closure (C.exposedPoints ℝ) :=
  extremePoints_subset_closure_exposedPoints hC hCcl

/-- **Theorem 18.6** in the book's own phrasing: the exposed points of a closed convex set form a
dense subset of its extreme points. -/
theorem theorem_18_6_closure (hC : Convex ℝ C) (hCcl : IsClosed C) :
    C.exposedPoints ℝ ⊆ C.extremePoints ℝ ∧
      closure (C.exposedPoints ℝ) = closure (C.extremePoints ℝ) :=
  ⟨exposedPoints_subset_extremePoints, closure_exposedPoints_eq_closure_extremePoints hC hCcl⟩

/-! ### Exposed faces and exposed points (p. 162) -/

/-- **§18 (p. 162).** The **exposed faces** of `C` are the sets of points at which some linear
function `⟨·, b⟩` attains its maximum over `C`. The book's vector `b` and Mathlib's continuous
linear functional are the same quantification in `ℝⁿ`. -/
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

/-- **§18 (p. 162).** An **exposed point** of `C` is a point through which there is a supporting
hyperplane containing no other point of `C`. -/
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

/-- **Theorem 18.7**. A closed convex set containing no lines is `cl (conv S)`, for `S` the set of
its exposed points and exposed directions. Unlike Theorem 18.5 the closure cannot be dropped: the
exposed points of a closed convex set need not form a closed set. -/
theorem theorem_18_7 (hC : Convex ℝ C) (hCcl : IsClosed C) (hnl : ContainsNoLine C) :
    closure (convexHullPD (C.exposedPoints ℝ) (exposedDirections C)) = C :=
  closure_convexHullPD_exposedPoints_exposedDirections hC hCcl hnl

/-- **Corollary 18.7.1**. If `K` is a closed convex cone containing no lines and every exposed ray
of `K` is generated by some `x ∈ T ⊆ K`, then `K` is the closure of the convex cone generated by
`T`.

**The book prints this corollary with no proof.** The argument it wants is the one given for
Corollary 18.5.2, one layer up: by Theorem 18.7, `K = cl (conv S)` for `S` the exposed points and
exposed directions of `K`; the origin is the only exposed point, being the only extreme point of a
line-free cone; and `conv` of the origin with a set of directions is the cone they generate. -/
theorem corollary_18_7_1 {K T : Set (Rn n)} (hK : Convex ℝ K) (hKcl : IsClosed K)
    (hcone : IsCone K) (hne : K.Nonempty) (hnl : ContainsNoLine K) (hTK : T ⊆ K)
    (hgen : ∀ y, IsExposedRay K y → ∃ x ∈ T, ∃ a : ℝ, 0 < a ∧ y = a • x) :
    closure (PointedCone.hull ℝ T : Set (Rn n)) = K := by
  have hsmul := forall_smul_mem_of_isCone hcone hKcl
  exact closure_coneHull_of_forall_exposedDirection hK hKcl hne hsmul hnl hTK fun y hy =>
    hgen y ((isExposedRay_iff_isExposedDirection hne hsmul).2 hy)

/-! ### Theorem 18.8: the tangent representation -/

/-- **§18 (p. 168).** A hyperplane is **tangent** to a closed convex set `C` at `x` if it is the
unique supporting hyperplane to `C` at `x`; here it is `{z | ⟨z, b⟩ = ⟨x, b⟩}`, with tangent
half-space `{z | ⟨z, b⟩ ≤ ⟨x, b⟩}`. `IsTangentAt` renders "unique hyperplane" as uniqueness of the
functional up to a *positive* multiple: a hyperplane fixes its functional up to a non-zero scalar,
and the supporting inequality fixes the sign. -/
def IsTangentHyperplaneAt (C : Set (Rn n)) (b : Rn n) (x : Rn n) : Prop :=
  IsTangentAt C (linFn b) x

/-- **Theorem 18.8**. An `n`-dimensional closed convex set in `ℝⁿ` is the intersection of the
closed half-spaces tangent to it. "`n`-dimensional in `ℝⁿ`" is `(interior C).Nonempty`. -/
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
