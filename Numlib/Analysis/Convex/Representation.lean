import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Numlib.Analysis.Convex.Face
import Numlib.Analysis.Convex.HullDirections
import Numlib.Analysis.Convex.Recession.Cone

/-!
# Internal representation of a closed convex set

The theorems that recover a closed convex set from its extremal structure: once it contains no
line it is the convex hull of its extreme points and extreme directions, its faces are themselves
such hulls, and its exposed points are dense in its extreme points. `Face.lean` supplies the faces
themselves, and `HullDirections.lean` supplies `convexHullPD`, the convex hull of a set of points
together with a set of directions, which is what "`C = conv S`" means once `S` may contain
directions. The *exposed* representation is in `Exposed.lean`.

## Main definitions

* `ContainsNoLine C` — no line is contained in `C`; Rockafellar's "`C` contains no lines".
* `IsExtremeDirection C y` — the direction of `y` is an *extreme direction* of `C`: some closed
  half-line in the direction of `y` is a face of `C`. `extremeDirections C` is the set of such `y`.
* `IsAffineHalf C` — `C` is an affine set or a closed half of one: the intersection of `aff C`
  with a closed half-space. Allowing the functional to vanish makes the affine case the case
  `φ = 0`, so the two exceptional families of the segment theorem below become one predicate.

## Main results

* `exists_notMem_relint_mem_segment_of_not_isAffineHalf` — in a closed convex set that is neither
  an affine set nor a closed half of one, every relative interior point lies on a segment joining
  two relative boundary points (Theorem 18.4 in [^1]). The analytic core is
  `exists_notMem_relint_mem_segment_of_isBounded`, the geometric input
  `exists_notMem_relint_mem_segment_of_not_convex`, and `isAffineHalf_of_convex_sdiff_relint`
  identifies the exceptions.
* `convexHullPD_extremePoints_extremeDirections` — the **Minkowski–Klee representation**: a closed
  convex set containing no lines is the convex hull of its extreme points and extreme directions
  (Theorem 18.5 in [^1]). `extremePoints_nonempty_of_containsNoLine` extracts an extreme point,
  `coneHull_extremeDirections_eq` and `coneHull_of_forall_extremeDirection` treat cones, and
  **Minkowski's theorem** for compact sets is `convexHull_extremePoints` in `Face.lean`, used here
  as the base case of the induction.
* `isFace_recessionCone` — the recession cone of a face is a face of the recession cone, given
  that it is contained in it. `extremeDirections_subset_extremeDirections_recessionCone` is the
  consequence for extreme directions; `isExtremeDirection_recessionCone` needs no topology.
* `isFaceEquivInter` — the face correspondence: for `N` a subspace of the lineality space of `C`
  and `M` a complement of `N`, the faces of `C` correspond one-to-one with the faces of `C ∩ M`.
  The mechanism is `IsFace.linealitySpace_subset`: a face is linear in every direction in which
  `C` is.
* `IsFace.eq_convexHullPD` — a nonempty face of `conv S` is the hull of the points of `S` it
  contains and the directions of `S` in which it recedes. `extremePoints_convexHullPD_subset` and
  `exists_mem_eq_smul_of_mem_extremeDirections` are the two corollaries — every extreme point is a
  generating point, every extreme direction a generating direction — and
  `finite_extremePoints_convexHullPD` the counting corollary a finitely generated set wants.
* `containsNoLine_inter_of_isCompl` — intersecting a closed convex set with a complement of its
  lineality space leaves a set containing no lines. With `eq_add_inter_of_isCompl` this is the
  reduction of a general closed convex set to a line-free one.
* `extremePoints_subset_closure_exposedPoints` — **Straszewicz's theorem**: the exposed points of a
  closed convex set are dense in its extreme points (Theorem 18.6 in [^1]); Mathlib does not have
  this. `mem_exposedPoints_of_forall_norm_sub_le` is the geometric heart (a farthest point is
  exposed) and `closure_convexHull_exposedPoints` the representation `C = cl (conv (exp C))`.

## Implementation notes

The description of a face of `conv S` avoids the appeal to the prolongation principle — which
would need the positive-coefficient description of `ri (conv S)` — by splitting the generating
points into those inside the face and those outside (`IsExtreme.mem_convexHull_inter`) and handling
the directions by an induction over the cone hull. The induction proving the Minkowski–Klee
representation splits on `finrank ℝ (vectorSpan ℝ C)`: dimension `≤ 1` is settled by
`exists_eq_halfLine`, the bounded case in every dimension by Minkowski's theorem, and only the
unbounded case of dimension `≥ 2` uses the segment theorem. Straszewicz is proved in a Euclidean
space, its farthest-point construction being inner-product geometry, and transported to a general
finite-dimensional normed space through `toEuclidean`.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §18.
-/

open Set Bornology

open scoped Pointwise RealInnerProductSpace

namespace ConvexAnalysis

/-! ### Lines, extreme directions, and half-line faces -/

section Directions

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C C' : Set E} {x y : E}

/-- `C` **contains no line**: no full line lies in `C`. This is the standing hypothesis of the
extreme and exposed representation theorems. For a nonempty closed convex set it says that the
lineality space is trivial (`containsNoLine_iff_linealitySpace_eq_zero`), but unlike that
formulation it is also correct for `C = ∅`. -/
def ContainsNoLine (C : Set E) : Prop := ∀ x y : E, y ≠ 0 → ∃ t : ℝ, x + t • y ∉ C

/-- A subset of a set containing no line contains no line. -/
theorem ContainsNoLine.mono (h : ContainsNoLine C) (hC' : C' ⊆ C) : ContainsNoLine C' := by
  intro x y hy
  obtain ⟨t, ht⟩ := h x y hy
  exact ⟨t, fun hmem => ht (hC' hmem)⟩

/-- The empty set contains no lines. -/
@[simp]
theorem containsNoLine_empty : ContainsNoLine (∅ : Set E) := fun x _ _ => ⟨0, by simp⟩

/-- `y` generates an **extreme direction** of `C`: `y ≠ 0` and some closed half-line in the
direction of `y` is a face of `C`. Rockafellar's *extreme direction* is the direction of such a
half-line face; representing it by a generating vector avoids a quotient, at the cost of the set
`extremeDirections C` being closed under multiplication by positive scalars. -/
def IsExtremeDirection (C : Set E) (y : E) : Prop :=
  y ≠ 0 ∧ ∃ x, IsFace C (halfLine x y)

/-- The set of vectors that generate extreme directions of `C`. -/
def extremeDirections (C : Set E) : Set E := {y | IsExtremeDirection C y}

/-- Membership in `extremeDirections`, unfolded. -/
theorem mem_extremeDirections : y ∈ extremeDirections C ↔ IsExtremeDirection C y := Iff.rfl

/-- Extreme directions do not change under positive rescaling of the generator. -/
theorem IsExtremeDirection.smul (h : IsExtremeDirection C y) {a : ℝ} (ha : 0 < a) :
    IsExtremeDirection C (a • y) :=
  ⟨smul_ne_zero ha.ne' h.1, by
    obtain ⟨x, hx⟩ := h.2
    exact ⟨x, by rwa [halfLine_smul x y ha]⟩⟩

/-- An extreme direction of a face of `C` is an extreme direction of `C`: this is `IsFace.trans`. -/
theorem IsFace.extremeDirections_subset (h : IsFace C C') :
    extremeDirections C' ⊆ extremeDirections C := by
  rintro y ⟨hy, x, hx⟩
  exact ⟨hy, x, h.trans hx⟩

/-- The half-line in an extreme direction lies in `C`. -/
theorem IsExtremeDirection.halfLine_subset (h : IsExtremeDirection C y) :
    ∃ x, halfLine x y ⊆ C := by
  obtain ⟨-, x, hx⟩ := h
  exact ⟨x, hx.subset⟩

/-- **The recession cone of a half-line is the half-line in the same direction issuing from the
origin.** A restatement of `recessionCone_halfLine`, which produces the ray as a set-builder. -/
theorem recessionCone_halfLine_eq_halfLine_zero (x y : E) :
    recessionCone (halfLine x y) = halfLine 0 y := by
  rw [recessionCone_halfLine]
  ext z
  simp [halfLine]

/-- **The recession cone of a face is a face of the recession cone.** The inclusion `0⁺C' ⊆ 0⁺C` is
genuinely a hypothesis: the recession cone is not monotone in general, and for a nonempty subset of
a closed convex set it comes from the description of recession by unbounded directions. Everything
else is algebraic — no topology, no convexity of `C`, no nonemptiness. The case that matters is a
half-line face: if `C'` has endpoint `x`, then `C' - x` is an extreme ray of `0⁺C`. -/
theorem isFace_recessionCone (h : IsFace C C') (hrec : recessionCone C' ⊆ recessionCone C) :
    IsFace (recessionCone C) (recessionCone C') := by
  refine ⟨⟨hrec, ?_⟩, convex_recessionCone C'⟩
  rintro u hu v hv z hz ⟨a, b, ha, hb, hab, hzab⟩ w hw t ht
  have hwC : w ∈ C := h.subset hw
  have hseg : w + t • z ∈ openSegment ℝ (w + t • u) (w + t • v) := by
    refine ⟨a, b, ha, hb, hab, ?_⟩
    have hexp : a • (w + t • u) + b • (w + t • v) = (a + b) • w + t • (a • u + b • v) := by
      module
    rw [hexp, hab, one_smul, hzab]
  exact h.left_mem_of_mem_openSegment (add_smul_mem_of_mem_recessionCone hu hwC ht)
    (add_smul_mem_of_mem_recessionCone hv hwC ht)
    (add_smul_mem_of_mem_recessionCone hz hw ht) hseg

/-- **An extreme direction in which `C` recedes is an extreme direction of `0⁺C`.** The half-line
face `x + ℝ₊ y` of `C` becomes the half-line face `ℝ₊ y` of `0⁺C`, an extreme ray of that cone. The
hypothesis `y ∈ 0⁺C` is automatic for a closed convex `C`; assuming it directly keeps the statement
free of topology. -/
theorem isExtremeDirection_recessionCone (h : IsExtremeDirection C y)
    (hy : y ∈ recessionCone C) : IsExtremeDirection (recessionCone C) y := by
  obtain ⟨hy0, x, hface⟩ := h
  have hrec : recessionCone (halfLine x y) ⊆ recessionCone C := by
    rw [recessionCone_halfLine_eq_halfLine_zero]
    rintro z ⟨a, ha, rfl⟩
    simpa using smul_mem_recessionCone ha hy
  have hfin := isFace_recessionCone hface hrec
  rw [recessionCone_halfLine_eq_halfLine_zero] at hfin
  exact ⟨hy0, 0, hfin⟩

end Directions

/-! ### Faces and the lineality space -/

section Lineality

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C C' C₀ : Set E} {N M : Submodule ℝ E}

/-- **A face is linear in every direction in which the ambient set is linear.** For `y` in the
lineality space of `C` and `x` in a face `C'`, the segment from `x - y` to `x + y` lies in `C` and
has `x` as its midpoint, so both endpoints lie in `C'`. This is what makes Rockafellar's reduction
of the facial structure to lineality zero work: a face of `C` is a union of translates of the
lineality space. -/
theorem IsFace.linealitySpace_subset (h : IsFace C C') :
    linealitySpace C ⊆ linealitySpace C' := by
  have key : ∀ y ∈ linealitySpace C, ∀ x ∈ C', x + y ∈ C' := by
    intro y hy x hx
    have hyC := mem_linealitySpace.1 hy
    have hseg : x ∈ openSegment ℝ (x + -y) (x + y) :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
    exact h.right_mem_of_mem_openSegment (add_mem_of_mem_recessionCone hyC.2 (h.subset hx))
      (add_mem_of_mem_recessionCone hyC.1 (h.subset hx)) hx hseg
  intro y hy
  have hsmul : ∀ a : ℝ, a • y ∈ linealitySpace C := fun a =>
    mem_linealitySubmodule.1 ((linealitySubmodule C).smul_mem a (mem_linealitySubmodule.2 hy))
  refine mem_linealitySpace.2 ⟨fun x hx a _ => key _ (hsmul a) x hx, fun x hx a _ => ?_⟩
  have hneg : a • -y = (-a) • y := by module
  rw [hneg]
  exact key _ (hsmul (-a)) x hx

/-- **A face inherits Rockafellar's direct-sum decomposition.** If `N` is a subspace of the
lineality space of `C` and `M` is a complement of `N`, then every face `C'` of `C` splits as
`N + (C' ∩ M)`. This is `eq_add_inter_of_isCompl_of_le` applied to `C'`, which is legitimate
because a face absorbs the lineality of `C`. -/
theorem IsFace.eq_add_inter_of_isCompl_of_le (h : IsFace C C')
    (hN : (N : Set E) ⊆ linealitySpace C) (hcompl : IsCompl N M) :
    C' = (N : Set E) + (C' ∩ (M : Set E)) :=
  _root_.ConvexAnalysis.eq_add_inter_of_isCompl_of_le
    (hN.trans h.linealitySpace_subset) hcompl

/-- **Adding a complemented subspace back is undone by cutting with the complement.** For
`C₀ ⊆ M` and `M` a complement of `N`, `(N + C₀) ∩ M = C₀`. -/
theorem inter_add_eq_self_of_isCompl (hcompl : IsCompl N M) (hC₀ : C₀ ⊆ (M : Set E)) :
    ((N : Set E) + C₀) ∩ (M : Set E) = C₀ := by
  refine Set.Subset.antisymm ?_ fun c hc => ⟨⟨0, N.zero_mem, c, hc, by simp⟩, hC₀ hc⟩
  rintro w ⟨⟨p, hp, c, hc, hpc⟩, hwM⟩
  have hpc' : p + c = w := hpc
  have hpM : p ∈ M := by
    have : p = w - c := by rw [← hpc']; abel
    rw [this]
    exact M.sub_mem hwM (hC₀ hc)
  have hp0 : p = 0 := (Submodule.disjoint_def.1 hcompl.disjoint) p hp hpM
  rw [← hpc', hp0, zero_add]
  exact hc

/-- **A face of the reduced set generates a face of the whole set.** If `N` is a subspace of the
lineality space of `C`, `M` a complement of `N`, and `C₀` a face of `C ∩ M`, then `N + C₀` is a
face of `C`. With `IsFace.inter_convex` and `IsFace.eq_add_inter_of_isCompl_of_le` this is
Rockafellar's remark that the faces of `C` correspond one-to-one with those of `C ∩ L^⊥`; the
inverse pair is packaged as `isFaceEquivInter`. -/
theorem isFace_add_of_isFace_inter (hN : (N : Set E) ⊆ linealitySpace C) (hcompl : IsCompl N M)
    (h : IsFace (C ∩ (M : Set E)) C₀) : IsFace C ((N : Set E) + C₀) := by
  have hdec : C = (N : Set E) + (C ∩ (M : Set E)) := eq_add_inter_of_isCompl_of_le hN hcompl
  have hsub : (N : Set E) + C₀ ⊆ C := by
    rintro w ⟨p, hp, c, hc, hpc⟩
    have hpc' : p + c = w := hpc
    rw [← hpc', add_comm]
    exact add_mem_of_mem_recessionCone (mem_linealitySpace.1 (hN hp)).1 (h.subset hc).1
  refine ⟨⟨hsub, ?_⟩, N.convex.add h.convex⟩
  rintro u hu v hv w hw ⟨a, b, ha, hb, hab, hseg⟩
  obtain ⟨r, hr, z, hz, hrz⟩ := hw
  have hrz' : r + z = w := hrz
  rw [hdec] at hu hv
  obtain ⟨p, hp, u₀, hu₀, hpu⟩ := hu
  obtain ⟨q, hq, v₀, hv₀, hqv⟩ := hv
  have hpu' : p + u₀ = u := hpu
  have hqv' : q + v₀ = v := hqv
  -- the `M`-components of the two decompositions of `w` agree
  have hsplit : a • (p + u₀) + b • (q + v₀) = r + z := by rw [hpu', hqv', hseg, hrz']
  have hzeq : z = a • (p + u₀) + b • (q + v₀) - r := by rw [hsplit]; abel
  have hval : z - (a • u₀ + b • v₀) = a • p + b • q - r := by rw [hzeq]; module
  have hzero : z - (a • u₀ + b • v₀) = 0 := by
    refine (Submodule.disjoint_def.1 hcompl.disjoint) _ ?_ ?_
    · rw [hval]
      exact N.sub_mem (N.add_mem (N.smul_mem a hp) (N.smul_mem b hq)) hr
    · exact M.sub_mem (h.subset hz).2
        (M.add_mem (M.smul_mem a hu₀.2) (M.smul_mem b hv₀.2))
  have hmid : a • u₀ + b • v₀ = z := (sub_eq_zero.1 hzero).symm
  have hu₀C₀ := h.left_mem_of_mem_openSegment hu₀ hv₀ hz ⟨a, b, ha, hb, hab, hmid⟩
  rw [← hpu']
  exact Set.add_mem_add hp hu₀C₀

/-- **The face correspondence**: for `N` a subspace of the lineality space of `C` and `M` a
complement of `N`, the faces of `C` are in one-to-one correspondence with the faces of `C ∩ M`, by
`C' ↦ C' ∩ M` and `C₀ ↦ N + C₀`. Rockafellar takes `N` the full lineality space `L` and `M = L^⊥`
in `ℝⁿ`; every subspace of `L` and every complement of it works, and no closedness or
finite-dimensionality is used. -/
def isFaceEquivInter (hN : (N : Set E) ⊆ linealitySpace C) (hcompl : IsCompl N M) :
    {C' : Set E // IsFace C C'} ≃ {C₀ : Set E // IsFace (C ∩ (M : Set E)) C₀} where
  toFun C' := ⟨(C' : Set E) ∩ (M : Set E), C'.2.inter_convex M.convex⟩
  invFun C₀ := ⟨(N : Set E) + (C₀ : Set E), isFace_add_of_isFace_inter hN hcompl C₀.2⟩
  left_inv C' := Subtype.ext (C'.2.eq_add_inter_of_isCompl_of_le hN hcompl).symm
  right_inv C₀ :=
    Subtype.ext (inter_add_eq_self_of_isCompl hcompl fun _ hx => (C₀.2.subset hx).2)

end Lineality

/-! ### Extreme points of a subset -/

section ExtremeSubset

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C K : Set E} {x : E}

/-- An extreme point of `C` that happens to lie in a subset `K` of `C` is an extreme point of `K`.
Extremality only becomes harder to satisfy as the ambient set grows. -/
theorem mem_extremePoints_of_subset (hx : x ∈ C.extremePoints ℝ) (hKC : K ⊆ C) (hxK : x ∈ K) :
    x ∈ K.extremePoints ℝ :=
  ⟨hxK, fun _ h₁ _ h₂ h => hx.2 (hKC h₁) (hKC h₂) h⟩


/-- **An extreme set absorbs the vertices of a convex combination it contains.** If `u` lies in an
extreme subset `C'` of `C` and is a convex combination of points of `P ⊆ C`, then `u` is already a
convex combination of those points of `P` that lie in `C'`. This is the mechanism behind the
description of a face of a hull below; the textbook argument instead puts `u` in the relative
interior of the hull of the points actually used. -/
theorem IsExtreme.mem_convexHull_inter {C C' P : Set E} (h : IsExtreme ℝ C C')
    (hCconv : Convex ℝ C) (hPC : P ⊆ C) {u : E} (hu : u ∈ C')
    (huP : u ∈ convexHull ℝ P) : u ∈ convexHull ℝ (P ∩ C') := by
  have hAC : convexHull ℝ P ⊆ C := convexHull_min hPC hCconv
  have hAconv : Convex ℝ (convexHull ℝ P) := convex_convexHull ℝ P
  have hAext : IsExtreme ℝ (convexHull ℝ P) (C' ∩ convexHull ℝ P) :=
    ⟨inter_subset_right, fun _ h₁ _ h₂ _ hz hopen =>
      ⟨h.left_mem_of_mem_openSegment (hAC h₁) (hAC h₂) hz.1 hopen, h₁⟩⟩
  have hdiff : Convex ℝ (convexHull ℝ P \ (C' ∩ convexHull ℝ P)) :=
    IsExtreme.convex_sdiff hAconv hAext
  rcases eq_empty_or_nonempty (P \ C') with hPD | hPD
  · rwa [Set.inter_eq_self_of_subset_left (Set.sdiff_eq_empty.1 hPD)]
  rcases eq_empty_or_nonempty (P ∩ C') with hPI | hPI
  · exfalso
    have hsub : P ⊆ convexHull ℝ P \ (C' ∩ convexHull ℝ P) := by
      intro z hz
      refine ⟨subset_convexHull ℝ P hz, fun hcon => ?_⟩
      exact absurd (show z ∈ P ∩ C' from ⟨hz, hcon.1⟩) (by rw [hPI]; exact notMem_empty z)
    exact (convexHull_min hsub hdiff huP).2 ⟨hu, huP⟩
  · have huA : u ∈ convexHull ℝ P := huP
    have hsplit : convexHull ℝ P
        = convexJoin ℝ (convexHull ℝ (P ∩ C')) (convexHull ℝ (P \ C')) := by
      rw [← convexHull_union hPI hPD, Set.inter_union_sdiff]
    rw [hsplit] at huP
    obtain ⟨a, ha, b, hb, hseg⟩ := mem_convexJoin.1 huP
    have hbdiff : b ∈ convexHull ℝ P \ (C' ∩ convexHull ℝ P) := by
      refine convexHull_min ?_ hdiff hb
      rintro z ⟨hzP, hzC'⟩
      exact ⟨subset_convexHull ℝ P hzP, fun hcon => hzC' hcon.1⟩
    have haA : a ∈ convexHull ℝ P :=
      convexHull_min (fun z hz => subset_convexHull ℝ P hz.1) hAconv ha
    rw [← insert_endpoints_openSegment, Set.mem_insert_iff, Set.mem_insert_iff] at hseg
    rcases hseg with hua | hub | hopen
    · rw [hua]; exact ha
    · exfalso; rw [hub] at hu; exact hbdiff.2 ⟨hu, hbdiff.1⟩
    · exfalso
      rw [openSegment_symm] at hopen
      exact hbdiff.2 (hAext.left_mem_of_mem_openSegment hbdiff.1 haA ⟨hu, huA⟩ hopen)

end ExtremeSubset

/-! ### Convex cones, and the extreme points and directions of a hull -/

section ConeExtreme

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {K : Set E}

/-- A nonempty set closed under multiplication by non-negative scalars contains the origin. -/
theorem zero_mem_of_forall_smul_mem (hne : K.Nonempty)
    (hcone : ∀ x ∈ K, ∀ a : ℝ, 0 ≤ a → a • x ∈ K) : (0 : E) ∈ K := by
  obtain ⟨x, hx⟩ := hne
  simpa using hcone x hx 0 le_rfl

/-- **A convex set closed under multiplication by non-negative scalars is closed under
addition**: `u + v` is twice the midpoint of `u` and `v`. -/
theorem add_mem_of_convex_of_forall_smul_mem (hK : Convex ℝ K)
    (hcone : ∀ x ∈ K, ∀ a : ℝ, 0 ≤ a → a • x ∈ K) {u v : E} (hu : u ∈ K) (hv : v ∈ K) :
    u + v ∈ K := by
  have hmid : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v ∈ K :=
    hK hu hv (by norm_num) (by norm_num) (by norm_num)
  have h2 := hcone _ hmid 2 (by norm_num)
  have heq : (2 : ℝ) • ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v) = u + v := by module
  rwa [heq] at h2

/-- **The cone hull of a subset of a convex cone stays inside it.** The cone `K` is described by
the two properties Rockafellar uses — convexity and closure under non-negative scalar
multiplication — rather than as a bundled `PointedCone`. -/
theorem coeHull_subset_of_forall_smul_mem (hK : Convex ℝ K) (hne : K.Nonempty)
    (hcone : ∀ x ∈ K, ∀ a : ℝ, 0 ≤ a → a • x ∈ K) {T : Set E} (hTK : T ⊆ K) :
    (PointedCone.hull ℝ T : Set E) ⊆ K := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem u hu => exact hTK hu
  | zero => exact zero_mem_of_forall_smul_mem hne hcone
  | add u v _ _ hu hv => exact add_mem_of_convex_of_forall_smul_mem hK hcone hu hv
  | smul a u _ hu =>
    have h : (a : ℝ) • u ∈ K := hcone u hu a a.2
    exact h

/-- **The origin is the only extreme point of a cone containing no lines.** The half needing the
no-lines hypothesis is that the origin *is* extreme: a segment through the origin with endpoints
in a cone spans a whole line inside that cone. -/
theorem extremePoints_eq_singleton_zero (hne : K.Nonempty)
    (hcone : ∀ x ∈ K, ∀ a : ℝ, 0 ≤ a → a • x ∈ K) (hnl : ContainsNoLine K) :
    K.extremePoints ℝ = {0} := by
  have h0 : (0 : E) ∈ K := zero_mem_of_forall_smul_mem hne hcone
  refine Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · -- `x` extreme forces `2 • x = x`
    have h2 : (2 : ℝ) • x ∈ K := hcone x hx.1 2 (by norm_num)
    have hopen : x ∈ openSegment ℝ ((2 : ℝ) • x) 0 :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
    have heq : (2 : ℝ) • x = x := hx.2 h2 h0 hopen
    have h5 : x + x = x + 0 := by rw [add_zero, ← two_smul ℝ x]; exact heq
    exact Set.mem_singleton_iff.2 (add_left_cancel h5)
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨h0, ?_⟩
    intro a ha b hb hmem
    obtain ⟨p, q, hp, hq, hpq, hval⟩ := hmem
    by_contra hane
    obtain ⟨t, ht⟩ := hnl 0 a hane
    refine ht ?_
    rw [zero_add]
    rcases le_or_gt 0 t with h | h
    · exact hcone a ha t h
    · -- for negative `t`, the vector `t • a` is a non-negative multiple of `b`
      have hp0 : (p : ℝ) ≠ 0 := ne_of_gt hp
      have hc : (0 : ℝ) ≤ -t * q / p := div_nonneg (mul_nonneg (by linarith) hq.le) hp.le
      have h2 : (-t / p) • (p • a + q • b) = (0 : E) := by rw [hval, smul_zero]
      rw [smul_add, smul_smul, smul_smul] at h2
      have h3 : (-t / p * p) = -t := by field_simp
      have h4 : (-t / p * q) = -t * q / p := by ring
      rw [h3, h4, neg_smul, neg_add_eq_zero] at h2
      rw [h2]
      exact hcone b hb _ hc

/-- **Every extreme point of a hull of points and directions is one of its points.** It can be
deduced from the description of a face of such a hull by taking the face to be a single point;
directly, a nonzero direction of recession at an extreme point would place that point strictly
inside a segment. -/
theorem extremePoints_convexHullPD_subset (P D : Set E) :
    (convexHullPD P D).extremePoints ℝ ⊆ P := by
  intro x hx
  obtain ⟨u, hu, v, hv, huv⟩ := mem_convexHullPD.1 hx.1
  have huC : u ∈ convexHullPD P D := convexHull_subset_convexHullPD P D hu
  have hxv : x + v ∈ convexHullPD P D :=
    add_mem_of_mem_recessionCone (coneHull_subset_recessionCone_convexHullPD P D hv) hx.1
  have hopen : x ∈ openSegment ℝ u (x + v) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [← huv]
    module
  have hux : u = x := hx.2 huC hxv hopen
  exact extremePoints_convexHull_subset
    (mem_extremePoints_of_subset hx (convexHull_subset_convexHullPD P D) (hux ▸ hu))

/-- **A hull of finitely many points and directions has finitely many extreme points.** Immediate
from `extremePoints_convexHullPD_subset`, which puts every extreme point among the generating
points. -/
theorem finite_extremePoints_convexHullPD (P D : Finset E) :
    ((convexHullPD (P : Set E) (D : Set E)).extremePoints ℝ).Finite :=
  P.finite_toSet.subset (extremePoints_convexHullPD_subset _ _)

end ConeExtreme

/-! ### Faces and directions of recession -/

section FaceRecession

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C C' : Set E}

/-- **Splitting off a direction of recession at a point of a face.** If a point `x` of the face
`C'` is obtained from a point `w` of `C` by adding a direction of recession `v` of `C`, then both
`w` and `x + v` lie in `C'`, because `x` is the midpoint of the segment from `w` to `x + v`. -/
theorem IsFace.mem_and_add_mem (hface : IsFace C C') {x w v : E} (hx : x ∈ C') (hw : w ∈ C)
    (hv : v ∈ recessionCone C) (hxwv : x = w + v) : w ∈ C' ∧ x + v ∈ C' := by
  have hxv : x + v ∈ C := add_mem_of_mem_recessionCone hv (hface.subset hx)
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [add_zero] at hxwv
    exact ⟨by rw [← hxwv]; exact hx, by rw [add_zero]; exact hx⟩
  · have hopen : x ∈ openSegment ℝ w (x + v) := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      rw [hxwv]; module
    refine ⟨hface.left_mem_of_mem_openSegment hw hxv hx hopen, ?_⟩
    rw [openSegment_symm] at hopen
    exact hface.left_mem_of_mem_openSegment hxv hw hx hopen

/-- Iterating `IsFace.mem_and_add_mem`: the face contains every point `x + n * t • y`. -/
theorem IsFace.add_nsmul_mem (hface : IsFace C C') {x w y : E} (hx : x ∈ C') (hw : w ∈ C)
    (hy : y ∈ recessionCone C) {t : ℝ} (ht : 0 ≤ t) (hxwv : x = w + t • y) :
    ∀ n : ℕ, x + ((n : ℝ) * t) • y ∈ C' := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    have hwn : w + ((n : ℝ) * t) • y ∈ C :=
      add_smul_mem_of_mem_recessionCone hy hw (mul_nonneg (Nat.cast_nonneg n) ht)
    have heq : x + ((n : ℝ) * t) • y = w + ((n : ℝ) * t) • y + t • y := by
      rw [hxwv]; module
    have h := (hface.mem_and_add_mem ih hwn (smul_mem_recessionCone ht hy) heq).2
    have hcast : x + ((n : ℝ) * t) • y + t • y = x + (((n + 1 : ℕ) : ℝ) * t) • y := by
      push_cast; module
    rwa [hcast] at h

end FaceRecession



section DirectionsTopology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {C : Set E} {x y : E}

/-- A line inside a convex set is a line of directions in the lineality space. -/
theorem mem_linealitySpace_of_forall_add_smul_mem (hC : Convex ℝ C) (hCcl : IsClosed C)
    (h : ∀ t : ℝ, x + t • y ∈ C) : y ∈ linealitySpace C := by
  refine mem_linealitySpace.2 ⟨mem_recessionCone_of_exists_ray hC hCcl ⟨x, fun a _ => h a⟩, ?_⟩
  refine mem_recessionCone_of_exists_ray hC hCcl ⟨x, fun a _ => ?_⟩
  have heq : x + a • (-y) = x + (-a) • y := by module
  rw [heq]
  exact h (-a)

/-- **"Contains no line" is lineality zero**, for a nonempty closed convex set. -/
theorem containsNoLine_iff_linealitySpace_eq_zero (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hne : C.Nonempty) : ContainsNoLine C ↔ linealitySpace C = {0} := by
  constructor
  · intro h
    refine subset_antisymm (fun y hy => ?_) ?_
    · by_contra hy0
      obtain ⟨x, hx⟩ := hne
      obtain ⟨t, ht⟩ := h x y hy0
      rcases le_or_gt 0 t with hpos | hneg
      · exact ht (add_smul_mem_of_mem_recessionCone hy.1 hx hpos)
      · have hmem := add_smul_mem_of_mem_recessionCone (mem_linealitySpace.1 hy).2 hx
          (le_of_lt (neg_pos.2 hneg))
        have heq : x + (-t) • (-y) = x + t • y := by module
        rw [heq] at hmem
        exact ht hmem
    · simp
  · intro h x y hy0
    by_contra hall
    push Not at hall
    have hy : y ∈ linealitySpace C := mem_linealitySpace_of_forall_add_smul_mem hC hCcl hall
    rw [h] at hy
    exact hy0 hy

/-- **Intersecting a closed convex set with a complement of its lineality space kills every line.**
This is what makes the direct-sum decomposition `C = L + (C ∩ N)` useful: the second summand is a
set to which every theorem carrying a "contains no lines" hypothesis applies. A line in `C ∩ N` has
direction in `L`, is also a difference of two points of `N`, and `L ⊓ N = ⊥`. -/
theorem containsNoLine_inter_of_isCompl (hC : Convex ℝ C) (hCcl : IsClosed C)
    {N : Submodule ℝ E} (hN : IsCompl (linealitySubmodule C) N) :
    ContainsNoLine (C ∩ (N : Set E)) := by
  intro a y hy0
  by_contra hcon
  push Not at hcon
  have hyL : y ∈ linealitySubmodule C :=
    mem_linealitySubmodule.2
      (mem_linealitySpace_of_forall_add_smul_mem hC hCcl fun t => (hcon t).1)
  have hyN : y ∈ N := by
    have hdiff := N.sub_mem (hcon 1).2 (hcon 0).2
    rwa [show a + (1 : ℝ) • y - (a + (0 : ℝ) • y) = y by module] at hdiff
  exact hy0 (by simpa using hN.disjoint.le_bot ⟨hyL, hyN⟩)

/-- An extreme direction is a direction of recession: a closed convex set recedes in every
direction in which it contains a half-line. -/
theorem extremeDirections_subset_recessionCone (hC : Convex ℝ C) (hCcl : IsClosed C) :
    extremeDirections C ⊆ recessionCone C := by
  rintro y ⟨-, x, hx⟩
  exact mem_recessionCone_of_exists_ray hC hCcl ⟨x, fun a ha => hx.subset ⟨a, ha, rfl⟩⟩

/-- **Every extreme direction of a closed convex set is an extreme direction of its recession
cone.** This sharpens `extremeDirections_subset_recessionCone`, which says only that an extreme
direction *is* a direction of recession. The converse fails: a parabolic region in the plane has no
half-line faces at all, while its recession cone is a ray. -/
theorem extremeDirections_subset_extremeDirections_recessionCone (hC : Convex ℝ C)
    (hCcl : IsClosed C) : extremeDirections C ⊆ extremeDirections (recessionCone C) :=
  fun _ hy =>
    isExtremeDirection_recessionCone hy (extremeDirections_subset_recessionCone hC hCcl hy)

end DirectionsTopology

/-! ### Relatively open closed convex sets are affine -/

section Affine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E} {x d : E}

omit [FiniteDimensional ℝ E] in
/-- **A closed convex set that coincides with its relative interior contains whole lines.** If
`C ⊆ ri C` then, for every `x ∈ C` and every direction `d` of the affine hull, the entire line
`x + ℝ d` lies in `C`. This is what makes the exceptional sets below exceptional. -/
theorem forall_add_smul_mem_of_subset_relint (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hsub : C ⊆ ri C) (hx : x ∈ C) (hd : d ∈ vectorSpan ℝ C) (t : ℝ) : x + t • d ∈ C := by
  rcases eq_or_ne d 0 with rfl | hd0
  · simpa using hx
  set J : Set ℝ := {s : ℝ | x + s • d ∈ C} with hJdef
  have hline : ∀ s : ℝ, x + s • d ∈ affineSpan ℝ C := by
    intro s
    have hv : s • d ∈ (affineSpan ℝ C).direction := by
      rw [direction_affineSpan]
      exact Submodule.smul_mem _ s hd
    have hmem := AffineSubspace.vadd_mem_of_mem_direction hv (subset_affineSpan ℝ C hx)
    rwa [vadd_eq_add, add_comm] at hmem
  have hJclosed : IsClosed J := hCcl.preimage (by fun_prop)
  have hJconv : Convex ℝ J := by
    intro u hu v hv a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    have hval : a • (x + u • d) + (1 - a) • (x + v • d)
        = x + (a * u + (1 - a) * v) • d := by module
    have hmem : a • (x + u • d) + (1 - a) • (x + v • d) ∈ C := hC hu hv ha hb hab
    rw [hval] at hmem
    exact hmem
  have hJ0 : (0 : ℝ) ∈ J := by
    change x + (0 : ℝ) • d ∈ C
    simpa using hx
  -- from a point of `J` one can always move a little further away from `0`
  have hkey : ∀ s ∈ J, ∃ μ > (1 : ℝ), μ * s ∈ J := by
    intro s hs
    obtain ⟨μ, hμ, hw⟩ :=
      exists_one_lt_smul_mem_of_mem_relint (hsub hs) (subset_affineSpan ℝ C hx)
    refine ⟨μ, hμ, ?_⟩
    have hval : (1 - μ) • x + μ • (x + s • d) = x + (μ * s) • d := by module
    rwa [hval] at hw
  -- `J` contains a small positive and a small negative parameter
  obtain ⟨-, ε, hε, hball⟩ := mem_intrinsicInterior_iff.1 (hsub hx)
  have hdnorm : 0 < ‖d‖ := norm_pos_iff.2 hd0
  have hsmall : ∀ s : ℝ, |s| * ‖d‖ < ε → s ∈ J := by
    intro s hs
    refine hball _ (hline s) ?_
    have he : x + s • d - x = s • d := by module
    rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs]
    exact hs
  set t₀ : ℝ := ε / (2 * ‖d‖) with ht₀
  have ht₀pos : 0 < t₀ := by positivity
  have ht₀val : t₀ * ‖d‖ = ε / 2 := by rw [ht₀]; field_simp
  have ht₀J : t₀ ∈ J := hsmall t₀ (by rw [abs_of_pos ht₀pos, ht₀val]; linarith)
  have hnt₀J : -t₀ ∈ J := hsmall (-t₀) (by rw [abs_neg, abs_of_pos ht₀pos, ht₀val]; linarith)
  -- hence `J` is unbounded in both directions, and convex, so `J = ℝ`
  have hup : ¬ BddAbove J := by
    intro hbdd
    have hmem : sSup J ∈ J := hJclosed.csSup_mem ⟨0, hJ0⟩ hbdd
    obtain ⟨μ, hμ, hμJ⟩ := hkey _ hmem
    have hle : t₀ ≤ sSup J := le_csSup hbdd ht₀J
    have : sSup J < μ * sSup J := by nlinarith
    exact absurd (le_csSup hbdd hμJ) (not_le.2 this)
  have hdown : ¬ BddBelow J := by
    intro hbdd
    have hmem : sInf J ∈ J := hJclosed.csInf_mem ⟨0, hJ0⟩ hbdd
    obtain ⟨μ, hμ, hμJ⟩ := hkey _ hmem
    have hle : sInf J ≤ -t₀ := csInf_le hbdd hnt₀J
    have : μ * sInf J < sInf J := by nlinarith
    exact absurd (csInf_le hbdd hμJ) (not_le.2 this)
  obtain ⟨a, haJ, hat⟩ : ∃ a ∈ J, a < t := by
    by_contra hcon
    push Not at hcon
    exact hdown ⟨t, fun a ha => hcon a ha⟩
  obtain ⟨b, hbJ, htb⟩ : ∃ b ∈ J, t < b := by
    by_contra hcon
    push Not at hcon
    exact hup ⟨t, fun b hb => hcon b hb⟩
  have hba : (0 : ℝ) < b - a := by linarith
  refine hJconv.segment_subset haJ hbJ ⟨(b - t) / (b - a), (t - a) / (b - a),
    div_nonneg (by linarith) hba.le, div_nonneg (by linarith) hba.le, by field_simp; ring, ?_⟩
  simp only [smul_eq_mul]
  field_simp
  ring

omit [FiniteDimensional ℝ E] in
/-- **A closed convex set that coincides with its relative interior is an affine set.** -/
theorem affineSpan_subset_of_subset_relint (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hsub : C ⊆ ri C) : (affineSpan ℝ C : Set E) ⊆ C := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  intro u hu
  have hd : u - x ∈ vectorSpan ℝ C := by
    rw [← direction_affineSpan]
    simpa using AffineSubspace.vsub_mem_direction hu (subset_affineSpan ℝ C hx)
  have := forall_add_smul_mem_of_subset_relint hC hCcl hsub hx hd 1
  simpa using this

end Affine

/-! ### Relative interior points on segments between relative boundary points -/

section Segment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E} {x d : E}

omit [FiniteDimensional ℝ E] in
/-- **The analytic core of the segment theorem.** If the line through a relative interior point `x`
of a closed set `C`, in a direction of the affine hull of `C`, meets `C` in a bounded set, then `x`
lies on a segment joining the two ends of that intersection, neither of which is a relative
interior point. Convexity of `C` is not used. -/
theorem exists_notMem_relint_mem_segment_of_isBounded (hCcl : IsClosed C) (hd0 : d ≠ 0)
    (hd : d ∈ vectorSpan ℝ C) (hx : x ∈ ri C)
    (hbdd : IsBounded {t : ℝ | x + t • d ∈ C}) :
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

/-- **The segment theorem** in the form the proof produces: if the relative boundary of a closed
convex set `C` is *not convex*, then every relative interior point of `C` lies on a segment joining
two relative boundary points. Rockafellar's own hypothesis — that `C` is neither an affine set nor
a closed half of one — is equivalent; see `exists_notMem_relint_mem_segment_of_not_isAffineHalf`.
Non-convexity of the relative boundary produces two relative boundary points whose segment meets
`ri C`; the line through them meets `C` in exactly that segment, by the line segment principle, so
every parallel line meets `C` in a bounded set. -/
theorem exists_notMem_relint_mem_segment_of_not_convex (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hD : ¬ Convex ℝ (C \ ri C)) (hx : x ∈ ri C) :
    ∃ a ∈ C, ∃ b ∈ C, a ∉ ri C ∧ b ∉ ri C ∧ x ∈ segment ℝ a b := by
  -- a failure of convexity of the relative boundary
  obtain ⟨p, hp, q, hq, a, b, ha, hb, hab, hw⟩ :
      ∃ p ∈ C \ ri C, ∃ q ∈ C \ ri C, ∃ a b : ℝ,
        0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a • p + b • q ∉ C \ ri C := by
    by_contra hcon
    push Not at hcon
    refine hD ?_
    intro p hp q hq a b ha hb hab
    exact hcon p hp q hq a b ha hb hab
  have hwC : a • p + b • q ∈ C := hC hp.1 hq.1 ha hb hab
  have hwri : a • p + b • q ∈ ri C := by
    by_contra hcon
    exact hw ⟨hwC, hcon⟩
  -- both coefficients are positive, and the two boundary points are distinct
  have hbpos : 0 < b := by
    rcases hb.lt_or_eq with h | h
    · exact h
    · exfalso
      have ha1 : a = 1 := by linarith
      rw [ha1, ← h] at hwri
      simp only [one_smul, zero_smul, add_zero] at hwri
      exact hp.2 hwri
  have hapos : 0 < a := by
    rcases ha.lt_or_eq with h | h
    · exact h
    · exfalso
      have hb1 : b = 1 := by linarith
      rw [hb1, ← h] at hwri
      simp only [one_smul, zero_smul, zero_add] at hwri
      exact hq.2 hwri
  have hb1 : b < 1 := by linarith
  set d : E := q - p with hddef
  have hd0 : d ≠ 0 := by
    rw [hddef, sub_ne_zero]
    intro hpq
    have hpp : a • p + b • q = p := by
      rw [hpq, ← add_smul, hab, one_smul]
    rw [hpp] at hwri
    exact hp.2 hwri
  have hdmem : d ∈ vectorSpan ℝ C := vsub_mem_vectorSpan ℝ hq.1 hp.1
  have hwd : a • p + b • q = p + b • d := by
    have haa : a = 1 - b := by linarith
    rw [hddef, haa]
    module
  rw [hwd] at hwri
  -- the line through `p` and `q` meets `C` in the segment between them
  have hJ : ∀ t : ℝ, p + t • d ∈ C → 0 ≤ t ∧ t ≤ 1 := by
    intro t ht
    constructor
    · by_contra hcon
      push Not at hcon
      set c : ℝ := b / (b - t) with hcdef
      have hbt : 0 < b - t := by linarith
      have hc0 : 0 ≤ c := by positivity
      have hc1 : c < 1 := by
        rw [hcdef, div_lt_one hbt]
        linarith
      have hmem := Convex.segment_mem_relint hC hwri (subset_closure ht) hc0 hc1
      have heq : (1 - c) • (p + b • d) + c • (p + t • d) = p + ((1 - c) * b + c * t) • d := by
        module
      have hzero : (1 - c) * b + c * t = 0 := by
        rw [hcdef]
        field_simp
        ring
      rw [heq, hzero, zero_smul, add_zero] at hmem
      exact hp.2 hmem
    · by_contra hcon
      push Not at hcon
      set c : ℝ := (1 - b) / (t - b) with hcdef
      have hbt : 0 < t - b := by linarith
      have hc0 : 0 ≤ c := by positivity
      have hc1 : c < 1 := by
        rw [hcdef, div_lt_one hbt]
        linarith
      have hmem := Convex.segment_mem_relint hC hwri (subset_closure ht) hc0 hc1
      have heq : (1 - c) • (p + b • d) + c • (p + t • d) = p + ((1 - c) * b + c * t) • d := by
        module
      have hone : (1 - c) * b + c * t = 1 := by
        rw [hcdef]
        field_simp
        ring
      rw [heq, hone, one_smul, hddef] at hmem
      have hpq : p + (q - p) = q := by abel
      rw [hpq] at hmem
      exact hq.2 hmem
  -- hence every parallel line meets `C` in a bounded set
  set W : Submodule ℝ E := Submodule.span ℝ {d} with hWdef
  set M : AffineSubspace ℝ E := AffineSubspace.mk' p W with hMdef
  set N : AffineSubspace ℝ E := AffineSubspace.mk' x W with hNdef
  have hMdir : M.direction = W := AffineSubspace.direction_mk' p W
  have hNdir : N.direction = W := AffineSubspace.direction_mk' x W
  have hMne : ((M : Set E) ∩ C).Nonempty := ⟨p, AffineSubspace.self_mem_mk' p W, hp.1⟩
  have hMbdd : IsBounded ((M : Set E) ∩ C) := by
    refine (Metric.isBounded_closedBall (x := p) (r := ‖d‖)).subset ?_
    rintro z ⟨hzM, hzC⟩
    rw [SetLike.mem_coe, hMdef, AffineSubspace.mem_mk', vsub_eq_sub, hWdef,
      Submodule.mem_span_singleton] at hzM
    obtain ⟨t, ht⟩ := hzM
    have hz : z = p + t • d := by rw [ht]; abel
    rw [hz] at hzC
    obtain ⟨ht0, ht1⟩ := hJ t hzC
    rw [Metric.mem_closedBall, dist_eq_norm, hz]
    have he : p + t • d - p = t • d := by abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc t * ‖d‖ ≤ 1 * ‖d‖ := mul_le_mul_of_nonneg_right ht1 (norm_nonneg d)
      _ = ‖d‖ := one_mul _
  have hNbdd : IsBounded ((N : Set E) ∩ C) :=
    isBounded_inter_of_direction_eq hC hCcl (by rw [hMdir, hNdir]) hMne hMbdd
  have hTbdd : IsBounded {t : ℝ | x + t • d ∈ C} := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall x).1 hNbdd
    have hdnorm : 0 < ‖d‖ := norm_pos_iff.2 hd0
    refine Bornology.IsBounded.subset (Metric.isBounded_Icc (-(R / ‖d‖)) (R / ‖d‖)) ?_
    intro t ht
    have hxN : x + t • d ∈ N := by
      rw [hNdef, AffineSubspace.mem_mk', vsub_eq_sub, hWdef, Submodule.mem_span_singleton]
      exact ⟨t, by abel⟩
    have hmem : x + t • d ∈ Metric.closedBall x R := hR ⟨hxN, ht⟩
    rw [Metric.mem_closedBall, dist_eq_norm] at hmem
    have he : x + t • d - x = t • d := by abel
    rw [he, norm_smul, Real.norm_eq_abs] at hmem
    exact Set.mem_Icc.2 (abs_le.1 ((le_div_iff₀ hdnorm).2 hmem))
  exact exists_notMem_relint_mem_segment_of_isBounded hCcl hd0 hdmem hx hTbdd

end Segment

/-! ### Affine sets and closed halves of affine sets -/

section AffineHalf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E} {x : E}

/-- `C` is **an affine set or a closed half of an affine set**: the intersection of its own affine
hull with a closed half-space. The two exceptional cases of the segment theorem are one predicate
here, because the degenerate choice `φ = 0`, `α = 0` gives exactly the affine sets. -/
def IsAffineHalf (C : Set E) : Prop :=
  ∃ (φ : E →ₗ[ℝ] ℝ) (α : ℝ), C = (affineSpan ℝ C : Set E) ∩ {x | φ x ≤ α}

omit [FiniteDimensional ℝ E] in
/-- An affine set is a (degenerate) closed half of an affine set. -/
theorem isAffineHalf_of_affineSpan_subset (h : (affineSpan ℝ C : Set E) ⊆ C) : IsAffineHalf C :=
  ⟨0, 0, subset_antisymm (fun x hx => ⟨subset_affineSpan ℝ C hx, by simp⟩) fun _ hx => h hx.1⟩

/-- **The exceptional sets are exactly those whose relative boundary is convex.** If the relative
boundary of a closed convex set `C` is convex, then `C` is an affine set or a closed half of one.
A supporting hyperplane at a relative interior point of the relative boundary contains the whole
relative boundary, `ri C` lies strictly on one side, and every point of `aff C` strictly on that
side already lies in `C`. -/
theorem isAffineHalf_of_convex_sdiff_relint (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hD : Convex ℝ (C \ ri C)) : IsAffineHalf C := by
  rcases Set.eq_empty_or_nonempty (C \ ri C) with hempty | hDne
  · refine isAffineHalf_of_affineSpan_subset (affineSpan_subset_of_subset_relint hC hCcl ?_)
    intro z hz
    by_contra hcon
    exact (Set.eq_empty_iff_forall_notMem.1 hempty z) ⟨hz, hcon⟩
  obtain ⟨z, hz⟩ := Convex.relint_nonempty hD hDne
  have hzD : z ∈ C \ ri C := intrinsicInterior_subset hz
  obtain ⟨g, hgmax, y, hyC, hgy⟩ := (notMem_relint_iff_exists_isMaxOn hC hzD.1).1 hzD.2
  set φ : E →ₗ[ℝ] ℝ := (g : E →ₗ[ℝ] ℝ) with hφdef
  set α : ℝ := g z with hαdef
  -- the relative boundary lies in the hyperplane `φ = α`
  have hDeq : ∀ w ∈ C \ ri C, φ w = α :=
    eq_of_isMaxOn_of_mem_relint (φ := φ) hz fun u hu => hgmax u hu.1
  -- the relative interior lies strictly below it
  have hrilt : ∀ w ∈ ri C, φ w < α := by
    intro w hw
    rcases lt_or_eq_of_le (hgmax w (intrinsicInterior_subset hw)) with h | h
    · exact h
    · exfalso
      have hconst := eq_of_isMaxOn_of_mem_relint (φ := φ) hw
        (fun u hu => by rw [show φ w = α from h]; exact hgmax u hu) y hyC
      exact hgy (hconst.trans (show φ w = α from h))
  -- every point of `aff C` strictly below the hyperplane is already in `C`
  have hkey : ∀ u ∈ affineSpan ℝ C, φ u < α → u ∈ C := by
    intro u huA hult
    by_contra huC
    obtain ⟨v, hv⟩ := Convex.relint_nonempty hC ⟨z, hzD.1⟩
    have hvC : v ∈ C := intrinsicInterior_subset hv
    set K : Set ℝ := {t : ℝ | 0 ≤ t ∧ (1 - t) • v + t • u ∈ C} with hKdef
    have hKcl : IsClosed K := by
      refine IsClosed.inter isClosed_Ici (hCcl.preimage (by fun_prop))
    have hKconv : Convex ℝ K := by
      rintro t₁ ⟨ht₁, hm₁⟩ t₂ ⟨ht₂, hm₂⟩ a b ha hb hab
      refine ⟨by positivity, ?_⟩
      have hb' : b = 1 - a := by linarith
      subst hb'
      have hval : a • ((1 - t₁) • v + t₁ • u) + (1 - a) • ((1 - t₂) • v + t₂ • u)
          = (1 - (a * t₁ + (1 - a) * t₂)) • v + (a * t₁ + (1 - a) * t₂) • u := by module
      have hmem := hC hm₁ hm₂ ha hb hab
      rw [hval] at hmem
      simpa using hmem
    have hK0 : (0 : ℝ) ∈ K := ⟨le_rfl, by simpa using hvC⟩
    have hK1 : (1 : ℝ) ∉ K := by
      rintro ⟨-, hmem⟩
      exact huC (by simpa using hmem)
    have hKle : ∀ t ∈ K, t ≤ 1 := by
      intro t ht
      by_contra hcon
      push Not at hcon
      have ht0 : (0 : ℝ) < t := by linarith
      have hmem := hKconv hK0 ht (a := 1 - 1 / t) (b := 1 / t)
        (by rw [sub_nonneg, div_le_one ht0]; linarith) (by positivity)
        (by field_simp; ring)
      have hval : (1 - 1 / t) • (0 : ℝ) + (1 / t) • t = 1 := by
        simp only [smul_eq_mul, mul_zero, zero_add]
        field_simp
      rw [hval] at hmem
      exact hK1 hmem
    have hbdd : BddAbove K := ⟨1, hKle⟩
    have hmax : sSup K ∈ K := hKcl.csSup_mem ⟨0, hK0⟩ hbdd
    set s : ℝ := sSup K with hsdef
    have hs1 : s < 1 := lt_of_le_of_ne (hKle s hmax) (fun h => hK1 (h ▸ hmax))
    have hs0 : 0 ≤ s := hmax.1
    set p : E := (1 - s) • v + s • u with hpdef
    have hpC : p ∈ C := hmax.2
    -- `p` is a relative boundary point, so `φ p = α`; but `φ p < α`
    have hpri : p ∉ ri C := by
      intro hpri
      have hwA : (1 - (-1 : ℝ)) • p + (-1 : ℝ) • u ∈ affineSpan ℝ C :=
        AffineSubspace.combo_mem (subset_affineSpan ℝ C hpC) huA (-1)
      obtain ⟨μ, hμ, hmem⟩ := exists_one_lt_smul_mem_of_mem_relint hpri hwA
      set t' : ℝ := s + (μ - 1) * (1 - s) with ht'
      have hval : (1 - μ) • ((1 - (-1 : ℝ)) • p + (-1 : ℝ) • u) + μ • p
          = (1 - t') • v + t' • u := by
        rw [hpdef, ht']
        module
      rw [hval] at hmem
      have ht'K : t' ∈ K := ⟨by nlinarith, hmem⟩
      have : s < t' := by nlinarith
      exact absurd (le_csSup hbdd ht'K) (not_le.2 this)
    have hpα : φ p = α := hDeq p ⟨hpC, hpri⟩
    have hvlt : φ v < α := hrilt v hv
    have hpval : φ p = (1 - s) * φ v + s * φ u := by
      rw [hpdef]
      simp [map_add, map_smul]
    rw [hpval] at hpα
    nlinarith
  -- assemble: `C = aff C ∩ {φ ≤ α}`
  refine ⟨φ, α, ?_⟩
  set K : Set E := (affineSpan ℝ C : Set E) ∩ {w | φ w ≤ α} with hKdef
  have hCK : C ⊆ K := fun w hw => ⟨subset_affineSpan ℝ C hw, hgmax w hw⟩
  have hKconv : Convex ℝ K :=
    (AffineSubspace.convex _).inter (convex_halfSpace_le (LinearMap.isLinear φ) α)
  have hKcl : IsClosed K :=
    (affineSpan ℝ C).closed_of_finiteDimensional.inter
      (isClosed_le (map_continuous g) continuous_const)
  have hriK : ri K ⊆ C := by
    intro w hw
    have hwK : w ∈ K := intrinsicInterior_subset hw
    refine hkey w hwK.1 ?_
    rcases lt_or_eq_of_le (show φ w ≤ α from hwK.2) with h | h
    · exact h
    · exfalso
      have hconst := eq_of_isMaxOn_of_mem_relint (φ := φ) hw
        (fun u hu => by rw [h]; exact hu.2) y (hCK hyC)
      exact hgy (hconst.trans h)
  have hcl := Convex.closure_eq_of_relint_subset_of_subset_closure hKconv hriK
    (hCK.trans hKcl.closure_eq.symm.subset)
  rw [hCcl.closure_eq, hKcl.closure_eq] at hcl
  exact hcl

/-- **The segment theorem**: if a closed convex set is neither an affine set nor a closed half of
an affine set, then each of its relative interior points lies on a line segment joining two
relative boundary points. -/
theorem exists_notMem_relint_mem_segment_of_not_isAffineHalf (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hhalf : ¬ IsAffineHalf C) (hx : x ∈ ri C) :
    ∃ a ∈ C, ∃ b ∈ C, a ∉ ri C ∧ b ∉ ri C ∧ x ∈ segment ℝ a b :=
  exists_notMem_relint_mem_segment_of_not_convex hC hCcl
    (fun hconv => hhalf (isAffineHalf_of_convex_sdiff_relint hC hCcl hconv)) hx

/-- **An affine set, or a closed half of an affine set, of dimension at least two contains a
line.** This is why the segment theorem applies to every closed convex set of dimension at least
two that contains no lines, and hence why the induction below only has to treat dimensions `0` and
`1` separately. -/
theorem not_containsNoLine_of_isAffineHalf (h : IsAffineHalf C) (hne : C.Nonempty)
    (hdim : 2 ≤ Module.finrank ℝ (vectorSpan ℝ C)) : ¬ ContainsNoLine C := by
  obtain ⟨φ, α, hCeq⟩ := h
  obtain ⟨x, hx⟩ := hne
  have hxK : x ∈ (affineSpan ℝ C : Set E) ∩ {w | φ w ≤ α} := hCeq ▸ hx
  set W : Submodule ℝ E := vectorSpan ℝ C with hWdef
  set ψ : W →ₗ[ℝ] ℝ := φ.domRestrict W with hψdef
  have hrange : Module.finrank ℝ (LinearMap.range ψ) ≤ 1 := by
    simpa using Submodule.finrank_le (LinearMap.range ψ)
  have hsum : Module.finrank ℝ (LinearMap.range ψ) + Module.finrank ℝ (LinearMap.ker ψ)
      = Module.finrank ℝ W := LinearMap.finrank_range_add_finrank_ker ψ
  have hkerpos : 0 < Module.finrank ℝ (LinearMap.ker ψ) := by omega
  have hker : LinearMap.ker ψ ≠ ⊥ := fun hbot => by
    rw [hbot] at hkerpos
    simp at hkerpos
  obtain ⟨v, hvker, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  intro hnl
  obtain ⟨t, ht⟩ := hnl x (v : E) (fun h => hv0 (Submodule.coe_eq_zero.1 h))
  refine ht ?_
  rw [hCeq]
  constructor
  · have hmem := AffineSubspace.vadd_mem_of_mem_direction
      (show t • (v : E) ∈ (affineSpan ℝ C).direction by
        rw [direction_affineSpan]
        exact Submodule.smul_mem _ t v.2) hxK.1
    rwa [vadd_eq_add, add_comm] at hmem
  · have hφv : φ (v : E) = 0 := LinearMap.mem_ker.1 hvker
    have : φ (x + t • (v : E)) = φ x := by
      rw [map_add, map_smul, hφv, smul_zero, add_zero]
    change φ (x + t • (v : E)) ≤ α
    rw [this]
    exact hxK.2

end AffineHalf

/-! ### Half-lines: the one-dimensional unbounded case -/

section HalfLine

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {x y : E}

/-- **The endpoint of a closed half-line is an extreme point of it.** -/
theorem mem_extremePoints_halfLine (x y : E) (hy : y ≠ 0) :
    x ∈ (halfLine x y).extremePoints ℝ := by
  refine ⟨left_mem_halfLine x y, ?_⟩
  rintro x₁ ⟨a, ha, rfl⟩ x₂ ⟨b, hb, rfl⟩ ⟨c, e, hc, he, hce, hx⟩
  have he' : e = 1 - c := by linarith
  subst he'
  have hval : c • (x + a • y) + (1 - c) • (x + b • y) = x + (c * a + (1 - c) * b) • y := by
    module
  rw [hval] at hx
  have hzero : (c * a + (1 - c) * b) • y = 0 := by
    simpa using sub_eq_zero_of_eq hx
  rcases smul_eq_zero.1 hzero with h | h
  · have ha0 : a ≤ 0 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - c) hb]
    rw [le_antisymm ha0 ha, zero_smul, add_zero]
  · exact absurd h hy

/-- **The direction of a closed half-line is an extreme direction of it**: the half-line is a face
of itself. -/
theorem mem_extremeDirections_halfLine (x y : E) (hy : y ≠ 0) :
    y ∈ extremeDirections (halfLine x y) :=
  ⟨hy, x, Convex.isFace_self (convex_halfLine x y)⟩

/-- A closed half-line is the convex hull of its unique extreme point and its unique extreme
direction. -/
theorem halfLine_subset_convexHullPD (x y : E) (hy : y ≠ 0) :
    halfLine x y ⊆
      convexHullPD ((halfLine x y).extremePoints ℝ) (extremeDirections (halfLine x y)) := by
  have h := convexHullPD_mono (singleton_subset_iff.2 (mem_extremePoints_halfLine x y hy))
    (singleton_subset_iff.2 (mem_extremeDirections_halfLine x y hy))
  rwa [convexHullPD_singleton] at h

end HalfLine

/-! ### The faces of a hull of points and directions -/

section FaceHull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C C' P D : Set E}

/-- A direction of recession of `C` that carries a point of `C` into the face `C'` is a direction
of recession of `C'` itself. This is the delicate step: the face contains a whole half-line in that
direction, so `cl C'` recedes in it, and a face is the trace on `C` of its own closure. -/
theorem IsFace.mem_recessionCone_of_eq_add_smul (hCconv : Convex ℝ C) (hface : IsFace C C')
    {x w y : E} (hx : x ∈ C') (hw : w ∈ C) (hy : y ∈ recessionCone C) {t : ℝ} (ht : 0 < t)
    (hxwv : x = w + t • y) : y ∈ recessionCone C' := by
  have hray := hface.add_nsmul_mem hx hw hy ht.le hxwv
  have hu : ∀ n : ℕ, x + ((n : ℝ) + 1) • (t • y) ∈ closure C' := by
    intro n
    refine subset_closure ?_
    have h := hray (n + 1)
    rwa [show (((n + 1 : ℕ) : ℝ) * t) = ((n : ℝ) + 1) * t by push_cast; ring, mul_smul] at h
  have hty : t • y ∈ recessionCone (closure C') :=
    mem_recessionCone_of_tendsto (Convex.closure hface.convex) isClosed_closure
      (l := fun n : ℕ => ((n : ℝ) + 1)⁻¹) hu (fun n => by positivity)
      tendsto_inv_nat_add_one_atTop_nhds_zero (tendsto_inv_smul_ray x (t • y))
  have hyc : y ∈ recessionCone (closure C') := by
    have h := smul_mem_recessionCone (le_of_lt (inv_pos.2 ht)) hty
    rwa [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h
  rw [hface.eq_inter_closure hCconv]
  exact fun z hz a ha => ⟨hy z hz.1 a ha, hyc z hz.2 a ha⟩

/-- The directions used by a point of a face of `conv S` are directions of recession of that
face. Proved by induction over the cone hull; the scaling parameter `t` is carried through the
induction so that the `smul` step can be reduced to the `mem` step. -/
private theorem mem_coneHull_filter_of_isFace (hface : IsFace (convexHullPD P D) C') :
    ∀ v ∈ PointedCone.hull ℝ D, ∀ t : ℝ, 0 < t → ∀ x ∈ C', ∀ w ∈ convexHullPD P D,
      x = w + t • v → v ∈ PointedCone.hull ℝ {y ∈ D | y ∈ recessionCone C'} := by
  have hCconv : Convex ℝ (convexHullPD P D) := convex_convexHullPD P D
  intro v hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    intro t ht x hx w hw hxwv
    have hyrec : y ∈ recessionCone (convexHullPD P D) := subset_recessionCone_convexHullPD P D hy
    exact PointedCone.subset_hull
      ⟨hy, hface.mem_recessionCone_of_eq_add_smul hCconv hx hw hyrec ht hxwv⟩
  | zero => exact fun _ _ _ _ _ _ _ => zero_mem _
  | add v₁ v₂ hv₁ hv₂ ih₁ ih₂ =>
    intro t ht x hx w hw hxwv
    have hr₁ : t • v₁ ∈ recessionCone (convexHullPD P D) :=
      smul_mem_recessionCone ht.le (coneHull_subset_recessionCone_convexHullPD P D hv₁)
    have hr₂ : t • v₂ ∈ recessionCone (convexHullPD P D) :=
      smul_mem_recessionCone ht.le (coneHull_subset_recessionCone_convexHullPD P D hv₂)
    refine add_mem (ih₁ t ht x hx (w + t • v₂) (add_mem_of_mem_recessionCone hr₂ hw) ?_)
      (ih₂ t ht x hx (w + t • v₁) (add_mem_of_mem_recessionCone hr₁ hw) ?_)
    · rw [hxwv]; module
    · rw [hxwv]; module
  | smul c v₁ hv₁ ih₁ =>
    intro t ht x hx w hw hxwv
    rcases eq_or_lt_of_le c.2 with hc | hc
    · have hz : c • v₁ = (0 : E) := by
        change (c : ℝ) • v₁ = (0 : E)
        rw [← hc, zero_smul]
      rw [hz]
      exact zero_mem _
    · refine Submodule.smul_mem _ c (ih₁ (t * (c : ℝ)) (mul_pos ht hc) x hx w hw ?_)
      rw [hxwv]
      change w + t • ((c : ℝ) • v₁) = w + (t * (c : ℝ)) • v₁
      rw [smul_smul]

/-- A face of a convex hull of points and directions is itself the convex hull of the points it
contains and the directions in which it recedes. -/
theorem IsFace.eq_convexHullPD (hface : IsFace (convexHullPD P D) C') :
    C' = convexHullPD (P ∩ C') {y ∈ D | y ∈ recessionCone C'} := by
  have hCconv : Convex ℝ (convexHullPD P D) := convex_convexHullPD P D
  refine Subset.antisymm (fun x hx => ?_)
    (convexHullPD_min hface.convex inter_subset_right fun y hy => hy.2)
  have hxC : x ∈ convexHullPD P D := hface.subset hx
  obtain ⟨u, hu, v, hv, huv⟩ := mem_convexHullPD.1 hxC
  have hvrec : v ∈ recessionCone (convexHullPD P D) :=
    coneHull_subset_recessionCone_convexHullPD P D hv
  have huC : u ∈ convexHullPD P D := convexHull_subset_convexHullPD P D hu
  have huC' : u ∈ C' := (hface.mem_and_add_mem hx huC hvrec huv.symm).1
  have huhull : u ∈ convexHull ℝ (P ∩ C') :=
    IsExtreme.mem_convexHull_inter hface.toIsExtreme hCconv (subset_convexHullPD P D) huC' hu
  have hvhull : v ∈ PointedCone.hull ℝ {y ∈ D | y ∈ recessionCone C'} :=
    mem_coneHull_filter_of_isFace hface v hv 1 one_pos x hx u huC (by rw [one_smul, huv])
  exact mem_convexHullPD.2 ⟨u, huhull, v, hvhull, huv⟩

/-- If no half-line meets the points of `S` in an unbounded set, then every extreme direction of
`conv S` is the direction of one of the vectors of `S`. -/
theorem exists_mem_eq_smul_of_mem_extremeDirections (P D : Set E)
    (hP : ∀ x z : E, IsBounded (P ∩ halfLine x z)) {y : E}
    (hy : y ∈ extremeDirections (convexHullPD P D)) :
    ∃ z ∈ D, ∃ a : ℝ, 0 < a ∧ y = a • z := by
  obtain ⟨hy0, x, hface⟩ := hy
  have heq := hface.eq_convexHullPD
  by_contra hcon
  push Not at hcon
  -- under the assumption, no vector of `S` can recede along the half-line unless it is `0`
  have hall : ∀ z ∈ {z ∈ D | z ∈ recessionCone (halfLine x y)}, z = 0 := by
    rintro z ⟨hzD, hzr⟩
    rw [recessionCone_halfLine] at hzr
    obtain ⟨a, ha, rfl⟩ := hzr
    rcases eq_or_lt_of_le ha with rfl | ha'
    · rw [zero_smul]
    · exact absurd (show y = a⁻¹ • (a • y) by
        rw [smul_smul, inv_mul_cancel₀ ha'.ne', one_smul])
        (hcon (a • y) hzD a⁻¹ (inv_pos.2 ha'))
  have hbot : PointedCone.hull ℝ {z ∈ D | z ∈ recessionCone (halfLine x y)} = ⊥ := by
    refine le_antisymm (Submodule.span_le.2 fun z hz => ?_) bot_le
    rw [Submodule.bot_coe, Set.mem_singleton_iff]
    exact hall z hz
  have hsub : convexHullPD (P ∩ halfLine x y) {z ∈ D | z ∈ recessionCone (halfLine x y)}
      ⊆ convexHull ℝ (P ∩ halfLine x y) := by
    intro w hw
    obtain ⟨u, hu, v, hv, huv⟩ := mem_convexHullPD.1 hw
    rw [hbot, Submodule.bot_coe, Set.mem_singleton_iff] at hv
    rw [← huv, hv, add_zero]
    exact hu
  refine not_isBounded_halfLine (x := x) hy0 ?_
  rw [heq]
  exact (isBounded_convexHull.2 (hP x y)).subset hsub

/-- The same under the hypothesis Rockafellar highlights: if the points of `S` form a bounded set,
every extreme direction of `conv S` is the direction of a vector of `S`. -/
theorem exists_mem_eq_smul_of_mem_extremeDirections_of_isBounded (P D : Set E)
    (hP : IsBounded P) {y : E} (hy : y ∈ extremeDirections (convexHullPD P D)) :
    ∃ z ∈ D, ∃ a : ℝ, 0 < a ∧ y = a • z :=
  exists_mem_eq_smul_of_mem_extremeDirections P D (fun _ _ => hP.subset inter_subset_left) hy

end FaceHull

/-! ### The Minkowski–Klee representation -/

section Representation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E}

/-- **An unbounded closed convex set of dimension at most one that contains no line is a closed
half-line.** This is the only case the induction below cannot reduce, and it is trivial. -/
theorem exists_eq_halfLine (hC : Convex ℝ C) (hCcl : IsClosed C) (hne : C.Nonempty)
    (hnl : ContainsNoLine C) (hdim : Module.finrank ℝ (vectorSpan ℝ C) ≤ 1)
    (hb : ¬ IsBounded C) : ∃ x y : E, y ≠ 0 ∧ C = halfLine x y := by
  obtain ⟨y, hyrec, hy0⟩ := exists_ne_zero_mem_recessionCone_of_not_isBounded hC hCcl hne hb
  obtain ⟨x, hx⟩ := hne
  have hxy : x + y ∈ C := add_mem_of_mem_recessionCone hyrec hx
  have hyV : y ∈ vectorSpan ℝ C := by
    have h := vsub_mem_vectorSpan ℝ hxy hx
    simpa using h
  have hspan : (ℝ ∙ y) = vectorSpan ℝ C :=
    Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).2 hyV)
      (by rw [finrank_span_singleton hy0]; exact hdim)
  -- the set of parameters along the line through `x` in the direction `y`
  set J : Set ℝ := {t : ℝ | x + t • y ∈ C} with hJdef
  have hJcl : IsClosed J := hCcl.preimage (by fun_prop)
  have hJconv : Convex ℝ J := by
    intro u hu v hv a b ha hb' hab
    have hb'' : b = 1 - a := by linarith
    subst hb''
    have hval : a • (x + u • y) + (1 - a) • (x + v • y) = x + (a * u + (1 - a) * v) • y := by
      module
    have hmem := hC hu hv ha hb' hab
    rw [hval] at hmem
    exact hmem
  have hJord := hJconv.ordConnected
  have hJnonneg : ∀ t : ℝ, 0 ≤ t → t ∈ J := fun t ht =>
    add_smul_mem_of_mem_recessionCone hyrec hx ht
  have hJbdd : BddBelow J := by
    by_contra hcon
    obtain ⟨t, htJ⟩ := hnl x y hy0
    rw [not_bddBelow_iff] at hcon
    obtain ⟨a, haJ, hat⟩ := hcon t
    exact htJ (hJord.out haJ (hJnonneg (max t 0) (le_max_right _ _))
      ⟨hat.le, le_max_left _ _⟩)
  have hm : sInf J ∈ J := hJcl.csInf_mem ⟨0, hJnonneg 0 le_rfl⟩ hJbdd
  refine ⟨x + sInf J • y, y, hy0, ?_⟩
  refine subset_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · have hzV : z - x ∈ vectorSpan ℝ C := by
      have h := vsub_mem_vectorSpan ℝ hz hx
      simpa using h
    rw [← hspan, Submodule.mem_span_singleton] at hzV
    obtain ⟨t, ht⟩ := hzV
    have hzt : z = x + t • y := by rw [ht]; abel
    have htJ : t ∈ J := by
      change x + t • y ∈ C
      rw [← hzt]
      exact hz
    refine ⟨t - sInf J, by linarith [csInf_le hJbdd htJ], ?_⟩
    rw [hzt]
    module
  · obtain ⟨a, ha, rfl⟩ := hz
    have hmem : sInf J + a ∈ J :=
      hJord.out hm (hJnonneg (max (sInf J + a) 0) (le_max_right _ _))
        ⟨by linarith, le_max_left _ _⟩
    have heq : x + sInf J • y + a • y = x + (sInf J + a) • y := by module
    rw [heq]
    exact hmem

/-- The representation for bounded sets: **Minkowski's theorem**, `convexHull_extremePoints`, with
the extreme directions (of which there are none) carried along. -/
theorem subset_convexHullPD_of_isBounded (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hb : IsBounded C) :
    C ⊆ convexHullPD (C.extremePoints ℝ) (extremeDirections C) := by
  have hcomp : IsCompact C := Metric.isCompact_of_isClosed_isBounded hCcl hb
  intro z hz
  rw [← convexHull_extremePoints hcomp hC] at hz
  exact convexHull_subset_convexHullPD _ _ hz

/-- The representation in dimension `≤ 1`: `C` is empty, a point, a segment, or a half-line. -/
theorem subset_convexHullPD_of_finrank_le_one (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hnl : ContainsNoLine C) (hdim : Module.finrank ℝ (vectorSpan ℝ C) ≤ 1) :
    C ⊆ convexHullPD (C.extremePoints ℝ) (extremeDirections C) := by
  by_cases hb : IsBounded C
  · exact subset_convexHullPD_of_isBounded hC hCcl hb
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨x, y, hy0, rfl⟩ := exists_eq_halfLine hC hCcl hne hnl hdim hb
  exact halfLine_subset_convexHullPD x y hy0

/-- The induction behind the representation theorem, on the dimension of `C`. -/
private theorem subset_convexHullPD_aux :
    ∀ (n : ℕ) (C : Set E), Module.finrank ℝ (vectorSpan ℝ C) ≤ n → Convex ℝ C → IsClosed C →
      ContainsNoLine C → C ⊆ convexHullPD (C.extremePoints ℝ) (extremeDirections C) := by
  intro n
  induction n with
  | zero =>
    intro C hdim hC hCcl hnl
    exact subset_convexHullPD_of_finrank_le_one hC hCcl hnl (by omega)
  | succ n ih =>
    intro C hdim hC hCcl hnl
    by_cases hdim1 : Module.finrank ℝ (vectorSpan ℝ C) ≤ 1
    · exact subset_convexHullPD_of_finrank_le_one hC hCcl hnl hdim1
    push Not at hdim1
    have hne : C.Nonempty := by
      rcases C.eq_empty_or_nonempty with rfl | h
      · refine absurd hdim1 (not_lt.2 ?_)
        rw [vectorSpan_empty]
        simp
      · exact h
    have hhalf : ¬ IsAffineHalf C := fun h =>
      not_containsNoLine_of_isAffineHalf h hne hdim1 hnl
    have hbd : ∀ w ∈ C, w ∉ ri C →
        w ∈ convexHullPD (C.extremePoints ℝ) (extremeDirections C) := by
      intro w hw hwri
      obtain ⟨C', hface, hwC'⟩ := exists_isFace_mem_relint hC hw
      have hC'ne : C' ≠ C := fun h => hwri (h ▸ hwC')
      have hC'cl : IsClosed C' := hface.isClosed hC hCcl
      have hlt : Module.finrank ℝ (vectorSpan ℝ C') < Module.finrank ℝ (vectorSpan ℝ C) :=
        hface.finrank_vectorSpan_lt ⟨w, intrinsicInterior_subset hwC'⟩ hC'ne
      have hsub := ih C' (by omega) hface.convex hC'cl (hnl.mono hface.subset)
        (intrinsicInterior_subset hwC')
      exact convexHullPD_mono hface.toIsExtreme.extremePoints_subset_extremePoints
        hface.extremeDirections_subset hsub
    intro w hw
    by_cases hwri : w ∈ ri C
    · obtain ⟨a, haC, b, hbC, hari, hbri, hseg⟩ :=
        exists_notMem_relint_mem_segment_of_not_isAffineHalf hC hCcl hhalf hwri
      exact (convex_convexHullPD _ _).segment_subset (hbd a haC hari) (hbd b hbC hbri) hseg
    · exact hbd w hw hwri

/-- **The Minkowski–Klee representation**: a closed convex set containing no lines is the convex
hull of its extreme points and extreme directions. The proof is an induction on `dim C`: for a set
of dimension at least two the relative boundary is not convex, so every relative interior point
lies on a segment joining two relative boundary points, and each of those lies in the relative
interior of a face of strictly smaller dimension, again closed and line-free. Dimensions `0` and
`1` are the base cases: a bounded set by Minkowski's theorem, an unbounded one a half-line. -/
theorem convexHullPD_extremePoints_extremeDirections (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hnl : ContainsNoLine C) :
    convexHullPD (C.extremePoints ℝ) (extremeDirections C) = C :=
  subset_antisymm
    (convexHullPD_min hC extremePoints_subset (extremeDirections_subset_recessionCone hC hCcl))
    (subset_convexHullPD_aux _ C le_rfl hC hCcl hnl)

/-- A nonempty closed convex set containing no lines has at least one extreme point: a hull of
directions alone would be empty. -/
theorem extremePoints_nonempty_of_containsNoLine (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hnl : ContainsNoLine C) (hne : C.Nonempty) : (C.extremePoints ℝ).Nonempty := by
  rcases (C.extremePoints ℝ).eq_empty_or_nonempty with hem | h
  · rw [← convexHullPD_extremePoints_extremeDirections hC hCcl hnl, hem,
      convexHullPD_empty_left] at hne
    exact absurd hne Set.not_nonempty_empty
  · exact h


/-- **A closed convex cone containing no lines is the cone generated by its extreme directions.**
The version for an arbitrary set of generators of the extreme rays follows by monotonicity of the
cone hull; it is `coneHull_of_forall_extremeDirection` below. -/
theorem coneHull_extremeDirections_eq (hC : Convex ℝ C) (hCcl : IsClosed C) (hne : C.Nonempty)
    (hcone : ∀ x ∈ C, ∀ a : ℝ, 0 ≤ a → a • x ∈ C) (hnl : ContainsNoLine C) :
    (PointedCone.hull ℝ (extremeDirections C) : Set E) = C := by
  have h := convexHullPD_extremePoints_extremeDirections hC hCcl hnl
  rwa [extremePoints_eq_singleton_zero hne hcone hnl, convexHullPD_zero_singleton] at h

/-- The same for an arbitrary generating set: if every extreme ray of a closed convex cone `C`
containing no lines is generated by some vector of a subset `T` of `C`, then `T` generates `C`.
Rockafellar assumes the cone contains more than the origin; that is unnecessary, since the zero
cone has no extreme directions and both sides are `{0}`. -/
theorem coneHull_of_forall_extremeDirection {T : Set E} (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hne : C.Nonempty) (hcone : ∀ x ∈ C, ∀ a : ℝ, 0 ≤ a → a • x ∈ C) (hnl : ContainsNoLine C)
    (hTC : T ⊆ C) (hgen : ∀ y ∈ extremeDirections C, ∃ x ∈ T, ∃ a : ℝ, 0 < a ∧ y = a • x) :
    (PointedCone.hull ℝ T : Set E) = C := by
  refine subset_antisymm (coeHull_subset_of_forall_smul_mem hC hne hcone hTC) ?_
  rw [← coneHull_extremeDirections_eq hC hCcl hne hcone hnl]
  have hle : PointedCone.hull ℝ (extremeDirections C) ≤ PointedCone.hull ℝ T := by
    refine Submodule.span_le.2 fun y hy => ?_
    obtain ⟨u, huT, a, ha, rfl⟩ := hgen y hy
    exact Submodule.smul_mem _ (⟨a, ha.le⟩ : {r : ℝ // 0 ≤ r}) (PointedCone.subset_hull huT)
  exact hle

end Representation


/-! ### Straszewicz's theorem, the Euclidean core -/

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {C : Set E}

/-- **A farthest point is an exposed point.** If `p ∈ C` maximises the distance to `y` over `C`,
then `p` is an exposed point of `C`: the linear functional `⟪p - y, ·⟫` attains its maximum over
`C` at `p` and nowhere else. Geometrically, the sphere about `y` through `p` contains `C`, and the
tangent hyperplane to that sphere at `p` meets it only at `p`. Neither convexity nor closedness of
`C` is needed. -/
theorem mem_exposedPoints_of_forall_norm_sub_le (y : E) {p : E} (hp : p ∈ C)
    (hmax : ∀ z ∈ C, ‖z - y‖ ≤ ‖p - y‖) : p ∈ C.exposedPoints ℝ := by
  refine ⟨hp, innerSL ℝ (p - y), fun z hz => ?_⟩
  have hkey : 2 * ⟪p - y, z - p⟫ + ‖z - p‖ ^ 2 ≤ 0 := by
    have h1 : ‖z - y‖ ^ 2 = ‖p - y‖ ^ 2 + 2 * ⟪p - y, z - p⟫ + ‖z - p‖ ^ 2 := by
      rw [show z - y = (p - y) + (z - p) by abel, norm_add_sq_real]
    have h2 : ‖z - y‖ ^ 2 ≤ ‖p - y‖ ^ 2 := by
      have h3 := hmax z hz
      have h4 := norm_nonneg (z - y)
      nlinarith
    linarith
  have hsub : ⟪p - y, z - p⟫ = ⟪p - y, z⟫ - ⟪p - y, p⟫ := inner_sub_right _ _ _
  have hsq : (0 : ℝ) ≤ ‖z - p‖ ^ 2 := sq_nonneg _
  simp only [innerSL_apply_apply]
  refine ⟨by linarith, fun hle => ?_⟩
  have hzero : ‖z - p‖ = 0 := by nlinarith [norm_nonneg (z - p)]
  exact sub_eq_zero.1 (norm_eq_zero.1 hzero)

/-- A nonempty compact set has at least one exposed point: any point farthest from the origin. -/
private theorem exposedPoints_nonempty_aux (hC : IsCompact C) (hne : C.Nonempty) :
    (C.exposedPoints ℝ).Nonempty := by
  obtain ⟨p, hp, hmax⟩ :=
    hC.exists_isMaxOn (f := fun z : E => ‖z - (0 : E)‖) hne (by fun_prop)
  exact ⟨p, mem_exposedPoints_of_forall_norm_sub_le 0 hp fun z hz => isMaxOn_iff.1 hmax z hz⟩

variable [FiniteDimensional ℝ E]

/-- **Straszewicz's theorem** for a *compact* convex set in a Euclidean space. This is the
substance of the theorem; the general statements below are obtained from it by transport along
`toEuclidean` and by truncating an unbounded set with a ball. -/
private theorem extremePoints_subset_closure_exposedPoints_aux
    (hC : Convex ℝ C) (hCcomp : IsCompact C) :
    C.extremePoints ℝ ⊆ closure (C.exposedPoints ℝ) := by
  intro x hx
  by_contra hxS
  have hxC : x ∈ C := hx.1
  have hSC : C.exposedPoints ℝ ⊆ C := exposedPoints_subset
  have hclSC : closure (C.exposedPoints ℝ) ⊆ C := closure_minimal hSC hCcomp.isClosed
  have hclScomp : IsCompact (closure (C.exposedPoints ℝ)) :=
    hCcomp.of_isClosed_subset isClosed_closure hclSC
  -- `C₀`, the convex hull of the closure of the exposed points, is compact, and misses `x`
  have hC₀conv : Convex ℝ (convexHull ℝ (closure (C.exposedPoints ℝ))) := convex_convexHull ℝ _
  have hC₀comp : IsCompact (convexHull ℝ (closure (C.exposedPoints ℝ))) :=
    IsCompact.convexHull hclScomp
  have hC₀C : convexHull ℝ (closure (C.exposedPoints ℝ)) ⊆ C := convexHull_min hclSC hC
  have hxC₀ : x ∉ convexHull ℝ (closure (C.exposedPoints ℝ)) := fun hmem =>
    hxS (extremePoints_convexHull_subset (mem_extremePoints_of_subset hx hC₀C hmem))
  have hC₀ne : (convexHull ℝ (closure (C.exposedPoints ℝ))).Nonempty := by
    obtain ⟨s, hs⟩ := exposedPoints_nonempty_aux hCcomp ⟨x, hxC⟩
    exact ⟨s, subset_convexHull ℝ _ (subset_closure hs)⟩
  -- separate `x` from `C₀` by the nearest-point projection
  obtain ⟨v, hvC₀, hv⟩ :=
    exists_norm_eq_iInf_of_complete_convex hC₀ne hC₀comp.isComplete hC₀conv x
  have hproj : ∀ w ∈ convexHull ℝ (closure (C.exposedPoints ℝ)), ⟪x - v, w - v⟫ ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hC₀conv hvC₀).1 hv
  have hd0 : x - v ≠ 0 := sub_ne_zero.2 fun h => hxC₀ (h ▸ hvC₀)
  have hn : 0 < ‖x - v‖ ^ 2 := pow_pos (norm_pos_iff.2 hd0) 2
  have hupper : ∀ w ∈ convexHull ℝ (closure (C.exposedPoints ℝ)), ⟪x - v, w⟫ ≤ ⟪x - v, v⟫ := by
    intro w hw
    have h := hproj w hw
    rw [inner_sub_right] at h
    linarith
  have hxv : ⟪x - v, x⟫ = ⟪x - v, v⟫ + ‖x - v‖ ^ 2 := by
    have h : ⟪x - v, x - v⟫ = ⟪x - v, x⟫ - ⟪x - v, v⟫ := inner_sub_right _ _ _
    rw [real_inner_self_eq_norm_sq] at h
    linarith
  -- a radius containing `C`
  obtain ⟨r, hr⟩ := hCcomp.isBounded.subset_closedBall x
  have hrC : ∀ z ∈ C, ‖z - x‖ ≤ r := fun z hz => by
    rw [← dist_eq_norm]; exact Metric.mem_closedBall.1 (hr hz)
  -- push the centre far out along the separating direction
  set lam : ℝ := (r ^ 2 + 1) / (2 * ‖x - v‖ ^ 2) with hlam
  have hlampos : 0 < lam := div_pos (by positivity) (by linarith)
  have hlamid : 2 * lam * ‖x - v‖ ^ 2 = r ^ 2 + 1 := by
    rw [hlam]; field_simp
  obtain ⟨p, hpC, hpmax⟩ := hCcomp.exists_isMaxOn (f := fun z : E => ‖z - (x - lam • (x - v))‖)
    ⟨x, hxC⟩ (by fun_prop)
  have hpmax' : ∀ z ∈ C, ‖z - (x - lam • (x - v))‖ ≤ ‖p - (x - lam • (x - v))‖ :=
    fun z hz => isMaxOn_iff.1 hpmax z hz
  -- `p` is exposed, hence lies in `C₀`, hence is on the wrong side
  have hpexp : p ∈ C.exposedPoints ℝ :=
    mem_exposedPoints_of_forall_norm_sub_le _ hpC hpmax'
  have hpC₀ : ⟪x - v, p⟫ ≤ ⟪x - v, v⟫ :=
    hupper p (subset_convexHull ℝ _ (subset_closure hpexp))
  -- but the farthest point cannot be on that side
  have hxdist : ‖x - (x - lam • (x - v))‖ ^ 2 = lam ^ 2 * ‖x - v‖ ^ 2 := by
    rw [show x - (x - lam • (x - v)) = lam • (x - v) by abel, norm_smul, Real.norm_eq_abs,
      abs_of_pos hlampos, mul_pow]
  have hpdist : ‖p - (x - lam • (x - v))‖ ^ 2
      = ‖p - x‖ ^ 2 + 2 * (lam * ⟪p - x, x - v⟫) + lam ^ 2 * ‖x - v‖ ^ 2 := by
    rw [show p - (x - lam • (x - v)) = (p - x) + lam • (x - v) by abel, norm_add_sq_real,
      real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hlampos, mul_pow]
  have hinner : ⟪p - x, x - v⟫ ≤ -‖x - v‖ ^ 2 := by
    rw [real_inner_comm, inner_sub_right]
    linarith
  have hpx : ‖p - x‖ ^ 2 ≤ r ^ 2 := by
    have h1 := hrC p hpC
    have h2 := norm_nonneg (p - x)
    nlinarith
  have hcontr : ‖x - (x - lam • (x - v))‖ ≤ ‖p - (x - lam • (x - v))‖ := hpmax' x hxC
  have h1 : ‖x - (x - lam • (x - v))‖ ^ 2 ≤ ‖p - (x - lam • (x - v))‖ ^ 2 := by
    have := norm_nonneg (x - (x - lam • (x - v)))
    nlinarith
  nlinarith [hlamid, hn, hlampos]

end Euclidean

/-! ### Transport of exposed points along a linear homeomorphism -/

section Transport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Exposed points are preserved by a linear homeomorphism. The `Mathlib` counterpart for extreme
points is `image_extremePoints`; the proof here is the same idea, composing the exposing functional
with the inverse map. -/
theorem image_exposedPoints (f : E ≃L[ℝ] F) (s : Set E) :
    f '' s.exposedPoints ℝ = (f '' s).exposedPoints ℝ := by
  ext b
  constructor
  · rintro ⟨a, ⟨haS, l, hl⟩, rfl⟩
    refine ⟨⟨a, haS, rfl⟩, l.comp (f.symm : F →L[ℝ] E), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨h1, h2⟩ := hl z hz
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
    exact ⟨h1, fun h => congrArg f (h2 h)⟩
  · rintro ⟨⟨a, haS, rfl⟩, l, hl⟩
    refine ⟨a, ⟨haS, l.comp (f : E →L[ℝ] F), ?_⟩, rfl⟩
    intro z hz
    obtain ⟨h1, h2⟩ := hl (f z) ⟨z, hz, rfl⟩
    exact ⟨h1, fun h => f.injective (h2 h)⟩

end Transport

/-! ### Straszewicz's theorem in a general finite-dimensional space -/

section Straszewicz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}

/-- **Exposedness is a local property of a convex set.** A point exposed in the truncation
`C ∩ closedBall c r` that lies in the *open* ball is already exposed in `C`.

This is the reduction of Straszewicz's theorem to the bounded case. -/
theorem mem_exposedPoints_of_mem_exposedPoints_inter_closedBall (hC : Convex ℝ C) {c : E} {r : ℝ}
    {p : E} (hp : p ∈ (C ∩ Metric.closedBall c r).exposedPoints ℝ) (hlt : dist p c < r) :
    p ∈ C.exposedPoints ℝ := by
  obtain ⟨⟨hpC, hpB⟩, l, hl⟩ := hp
  refine ⟨hpC, l, fun z hz => ?_⟩
  set t : ℝ := min 1 ((r - dist p c) / (‖z - p‖ + 1)) with ht
  have hm : (0 : ℝ) ≤ ‖z - p‖ := norm_nonneg _
  have hden : (0 : ℝ) < ‖z - p‖ + 1 := by linarith
  have ha : (0 : ℝ) < r - dist p c := by linarith
  have htpos : 0 < t := lt_min one_pos (div_pos ha hden)
  have htle : t ≤ 1 := min_le_left _ _
  have htbound : t * ‖z - p‖ < r - dist p c := by
    have h2 : t ≤ (r - dist p c) / (‖z - p‖ + 1) := min_le_right _ _
    have h3 := mul_le_mul_of_nonneg_right h2 hm
    have h4 : (r - dist p c) / (‖z - p‖ + 1) * ‖z - p‖ < r - dist p c := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith
    linarith
  -- the point `w` moves from `p` a little towards `z`, staying inside the ball
  have hwsub : (1 - t) • p + t • z - p = t • (z - p) := by module
  have hwC : (1 - t) • p + t • z ∈ C := hC hpC hz (by linarith) htpos.le (by ring)
  have hwB : (1 - t) • p + t • z ∈ Metric.closedBall c r := by
    have hdw : dist ((1 - t) • p + t • z) p = t * ‖z - p‖ := by
      rw [dist_eq_norm, hwsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have := dist_triangle ((1 - t) • p + t • z) p c
    rw [hdw] at this
    exact Metric.mem_closedBall.2 (by linarith)
  obtain ⟨hlw, hlwu⟩ := hl _ ⟨hwC, hwB⟩
  have hlval : l ((1 - t) • p + t • z) = (1 - t) * l p + t * l z := by
    simp [map_add, map_smul, smul_eq_mul]
  rw [hlval] at hlw hlwu
  refine ⟨by nlinarith, fun hle => ?_⟩
  have hwp : (1 - t) • p + t • z = p := hlwu (by nlinarith)
  have hzp : t • (z - p) = 0 := by rw [← hwsub, hwp, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 hzp).resolve_left (ne_of_gt htpos))

variable [FiniteDimensional ℝ E]

/-- A nonempty compact set in a finite-dimensional real normed space has an exposed point. -/
theorem exposedPoints_nonempty_of_isCompact (hC : IsCompact C) (hne : C.Nonempty) :
    (C.exposedPoints ℝ).Nonempty := by
  obtain ⟨b, hb⟩ :=
    exposedPoints_nonempty_aux (hC.image (toEuclidean (E := E)).continuous) (hne.image _)
  rw [← image_exposedPoints] at hb
  exact ⟨_, hb.choose_spec.1⟩

/-- **Straszewicz's theorem for a compact convex set**: every extreme point is a limit of exposed
points. -/
theorem extremePoints_subset_closure_exposedPoints_of_isCompact
    (hC : Convex ℝ C) (hCcomp : IsCompact C) :
    C.extremePoints ℝ ⊆ closure (C.exposedPoints ℝ) := by
  intro x hx
  have hconv : Convex ℝ (toEuclidean (E := E) '' C) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ s t hs ht hst
    exact ⟨s • a + t • b, hC ha hb hs ht hst, by simp⟩
  have himg : toEuclidean (E := E) x ∈ (toEuclidean (E := E) '' C).extremePoints ℝ := by
    rw [← image_extremePoints]
    exact ⟨x, hx, rfl⟩
  have h2 : toEuclidean (E := E) x ∈ closure ((toEuclidean (E := E) '' C).exposedPoints ℝ) :=
    extremePoints_subset_closure_exposedPoints_aux hconv
      (hCcomp.image (toEuclidean (E := E)).continuous) himg
  have hcl : toEuclidean (E := E) '' closure (C.exposedPoints ℝ)
      = closure (toEuclidean (E := E) '' C.exposedPoints ℝ) := by
    simpa only [ContinuousLinearEquiv.coe_toHomeomorph] using
      (toEuclidean (E := E)).toHomeomorph.image_closure (C.exposedPoints ℝ)
  rw [← image_exposedPoints, ← hcl] at h2
  obtain ⟨y, hy, hfy⟩ := h2
  rwa [(toEuclidean (E := E)).injective hfy] at hy

/-- **Straszewicz's theorem.** For a closed convex set `C`, every extreme point of `C` is a limit
of exposed points of `C`. Together with `Set.exposedPoints_subset_extremePoints` this says that the
exposed points of `C` form a dense subset of its extreme points. -/
theorem extremePoints_subset_closure_exposedPoints (hC : Convex ℝ C) (hCcl : IsClosed C) :
    C.extremePoints ℝ ⊆ closure (C.exposedPoints ℝ) := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hKconv : Convex ℝ (C ∩ Metric.closedBall x ε) := hC.inter (convex_closedBall x ε)
  have hKcomp : IsCompact (C ∩ Metric.closedBall x ε) :=
    (isCompact_closedBall x ε).inter_left hCcl
  have hxK : x ∈ C ∩ Metric.closedBall x ε := ⟨hx.1, Metric.mem_closedBall_self hε.le⟩
  have hxKext : x ∈ (C ∩ Metric.closedBall x ε).extremePoints ℝ :=
    mem_extremePoints_of_subset hx inter_subset_left hxK
  obtain ⟨p, hpK, hdist⟩ := Metric.mem_closure_iff.1
    (extremePoints_subset_closure_exposedPoints_of_isCompact hKconv hKcomp hxKext) ε hε
  exact ⟨p, mem_exposedPoints_of_mem_exposedPoints_inter_closedBall hC hpK
    (by rwa [dist_comm]), hdist⟩

/-- Straszewicz's theorem, in the form "the exposed points and the extreme points of a closed
convex set have the same closure". -/
theorem closure_exposedPoints_eq_closure_extremePoints (hC : Convex ℝ C) (hCcl : IsClosed C) :
    closure (C.exposedPoints ℝ) = closure (C.extremePoints ℝ) :=
  Subset.antisymm (closure_mono exposedPoints_subset_extremePoints)
    (closure_minimal (extremePoints_subset_closure_exposedPoints hC hCcl) isClosed_closure)

/-- Straszewicz's theorem in representation form: a compact convex set is the *closed* convex hull
of its exposed points. The closure cannot be dropped — the exposed points of a compact convex set
need not be closed — which is why the exposed representation carries a closure where the extreme
representation does not. -/
theorem closure_convexHull_exposedPoints (hC : Convex ℝ C) (hCcomp : IsCompact C) :
    closure (convexHull ℝ (C.exposedPoints ℝ)) = C := by
  refine subset_antisymm
    (closure_minimal (convexHull_min exposedPoints_subset hC) hCcomp.isClosed) ?_
  have h1 : C.extremePoints ℝ ⊆ closure (convexHull ℝ (C.exposedPoints ℝ)) :=
    (extremePoints_subset_closure_exposedPoints hC hCcomp.isClosed).trans
      (closure_mono (subset_convexHull ℝ _))
  calc C = convexHull ℝ (C.extremePoints ℝ) := (convexHull_extremePoints hCcomp hC).symm
    _ ⊆ closure (convexHull ℝ (C.exposedPoints ℝ)) :=
        convexHull_min h1 (convex_convexHull ℝ _).closure

end Straszewicz

end ConvexAnalysis
