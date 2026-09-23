import Numlib.Analysis.Convex.Continuity
import Numlib.Analysis.Convex.Polyhedral.Defs
import Numlib.Analysis.Convex.Polyhedral.Ops
import Numlib.Analysis.Convex.Representation
import Numlib.Analysis.Convex.Subdifferential.Defs

/-!
# The maximum of a convex function

Maximising a convex function behaves nothing like minimising one. The **maximum principle** says
that a maximiser in the relative interior of `C` forces `f` to be constant on `C`, so maxima live
on the boundary: on faces, and ultimately on extreme points. Taking a convex hull raises neither
the supremum nor the maximiser set, so the supremum over a closed convex set is already carried by
its relative boundary and — when `C` contains no lines and `f` is bounded above on each half-line
of `C` — by the extreme points of `C`. That boundedness is what makes the extreme *directions*
invisible: `f x = x` on `C = [0, ∞)` has supremum `⊤` over `C` and `0` over the one extreme point,
and `ConvexFn.iSup_extremePoints_add_coneHull` is the unconditional statement keeping them.

## Main definitions

* `BddAboveOnRays f C` — `f` is bounded above on every half-line of `C`. The direction `0` makes
  this include `C ⊆ dom f`, so it carries both standing hypotheses of the extreme point principle.

## Main results

* `ConvexFn.eq_of_isMaxOn_mem_relint` — the maximum principle
  ([rockafellar1970convex] Theorem 32.1), with `exists_isFace_forall_eq_of_isMaxOn` for the face it
  forces; `ConvexFn.iSup_convexHull`, `exists_eq_of_isMaxOn_convexHull` — the convex hull raises
  neither the supremum nor the maximiser set; `ConvexFn.iSup_sdiff_relint`,
  `exists_notMem_relint_eq_of_isMaxOn` — the relative boundary carries both.
* `ConvexFn.iSup_extremePoints_of_containsNoLine`, `ConvexFn.iSup_extremePoints_inter_of_isCompl`,
  `ConvexFn.iSup_extremePoints_add_coneHull` — the extreme point principle
  ([rockafellar1970convex] Theorem 32.3): for a line-free `C`, for a general `C` cut down by a
  complement of its lineality space, and in representation form.
* `exists_isMaxOn_of_polyhedral_of_bddAboveOnRays`,
  `exists_mem_extremePoints_isMaxOn_of_finitelyGenerated` — attainment over a polyhedral and over
  a finitely generated set; `ConvexFn.iSup_extremePoints`,
  `exists_mem_extremePoints_isMaxOn_of_isCompact` — the compact case.
* `mem_normalCone_of_mem_subdifferential_of_isMaxOn` — at a maximiser, every subgradient is normal.

## Implementation notes

Maximisation is spelled `∀ z ∈ C, f z ≤ f x` rather than `IsMaxOn`, the form every proof consumes;
`isMaxOn_iff` bridges. The lineality space `L` of `C` is quotiented out by intersecting with a
complement `N` rather than by passing to `E ⧸ L`: `C = L + (C ∩ N)` holds for *any* `N`, so no
inner product is needed where the book takes `N = L⊥`.

## References

* [rockafellar1970convex] §32.
-/

open scoped Pointwise

namespace ConvexAnalysis

/-! ### The maximum principle -/

section Relint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {C : Set E}

/-- **The maximum principle**: a convex function attaining its supremum over a convex `C ⊆ dom f`
at a *relative interior* point of `C` is constant on `C`. -/
theorem ConvexFn.eq_of_isMaxOn_mem_relint (hf : ConvexFn f) (hCdom : C ⊆ convexDom f) {z : E}
    (hz : z ∈ ri C) (hmax : ∀ w ∈ C, f w ≤ f z) {x : E} (hx : x ∈ C) : f x = f z := by
  refine le_antisymm (hmax x hx) ?_
  by_contra hcon
  have hxlt : f x < f z := not_le.1 hcon
  obtain ⟨t, ht, hy⟩ := exists_one_lt_smul_mem_of_mem_relint hz (subset_affineSpan ℝ C hx)
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
  have htinv0 : (0 : ℝ) < t⁻¹ := inv_pos.2 ht0
  have htinv1 : t⁻¹ < 1 := by
    have hcancel : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0.ne'
    nlinarith
  obtain ⟨ζ, hζ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (ne_bot_of_gt hxlt)
    (mem_convexDom.1 (hCdom (intrinsicInterior_subset hz)))
  rw [hζ] at hxlt
  obtain ⟨ξ, hξ1, hξ2⟩ := EReal.lt_iff_exists_real_btwn.1 hxlt
  have hξlt : ξ < ζ := by exact_mod_cast hξ2
  have hcomb := hf.epi_combo hξ1.le ((hmax _ hy).trans hζ.le)
    (by linarith : (0 : ℝ) ≤ 1 - t⁻¹) htinv0.le (by ring)
  rw [combo_prolong x z ht0.ne', hζ, EReal.coe_le_coe_iff] at hcomb
  nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - t⁻¹) (by linarith : (0 : ℝ) < ζ - ξ)]

/-- Every maximiser lies in a face of `C` on which `f` is constant, so the maximiser set is a union
of faces: the maximum principle applied on the face whose relative interior contains it. -/
theorem exists_isFace_forall_eq_of_isMaxOn [FiniteDimensional ℝ E] (hf : ConvexFn f)
    (hC : Convex ℝ C) (hCdom : C ⊆ convexDom f) {z : E} (hz : z ∈ C) (hmax : ∀ w ∈ C, f w ≤ f z) :
    ∃ C', IsFace C C' ∧ z ∈ C' ∧ ∀ x ∈ C', f x = f z := by
  obtain ⟨C', hface, hzri⟩ := exists_isFace_mem_relint hC hz
  have hsub : C' ⊆ C := hface.toIsExtreme.1
  exact ⟨C', hface, intrinsicInterior_subset hzri,
    fun x hx => hf.eq_of_isMaxOn_mem_relint (hsub.trans hCdom) hzri
      (fun w hw => hmax w (hsub hw)) hx⟩

end Relint

/-! ### Passing to the convex hull -/

section Hull

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {S : Set E}

/-- Taking the convex hull does not raise the supremum of a convex function: the sublevel set at
the supremum over `S` is convex and contains `S`, hence contains `conv S`. -/
theorem ConvexFn.iSup_convexHull (hf : ConvexFn f) (S : Set E) :
    (⨆ x ∈ convexHull ℝ S, f x) = ⨆ x ∈ S, f x := by
  refine le_antisymm (iSup₂_le fun x hx => ?_)
    (iSup₂_le fun x hx => le_iSup₂ (f := fun z (_ : z ∈ convexHull ℝ S) => f z) x
      (subset_convexHull ℝ S hx))
  exact convexHull_min (fun z hz => le_iSup₂ (f := fun w (_ : w ∈ S) => f w) z hz)
    (hf.convex_le _) hx

/-- The convex hull creates no new maximisers either, because the *strict* sublevel set is convex
too. -/
theorem exists_eq_of_isMaxOn_convexHull (hf : ConvexFn f) {x : E} (hx : x ∈ convexHull ℝ S)
    (hmax : ∀ z ∈ convexHull ℝ S, f z ≤ f x) : ∃ z ∈ S, f z = f x := by
  by_contra hcon
  push Not at hcon
  have hlt : S ⊆ {w : E | f w < f x} := fun z hz =>
    lt_of_le_of_ne (hmax z (subset_convexHull ℝ S hz)) (hcon z hz)
  exact absurd (convexHull_min hlt (hf.convex_lt (f x)) hx) (lt_irrefl (f x))

end Hull

/-! ### The supremum over the relative boundary -/

section Boundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {C : Set E}

/-- A closed convex set that is neither an affine set nor a closed half of one is the convex hull
of its relative boundary. -/
theorem convexHull_sdiff_relint (hC : Convex ℝ C) (hCcl : IsClosed C) (hhalf : ¬ IsAffineHalf C) :
    convexHull ℝ (C \ ri C) = C := by
  refine subset_antisymm (convexHull_min Set.sdiff_subset hC) fun w hw => ?_
  by_cases hwri : w ∈ ri C
  · obtain ⟨a, haC, b, hbC, hari, hbri, hseg⟩ :=
      exists_notMem_relint_mem_segment_of_not_isAffineHalf hC hCcl hhalf hwri
    exact (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ (C \ ri C) ⟨haC, hari⟩)
      (subset_convexHull ℝ (C \ ri C) ⟨hbC, hbri⟩) hseg
  · exact subset_convexHull ℝ (C \ ri C) ⟨hw, hwri⟩

/-- The supremum over a closed convex set is already its supremum over the relative boundary. The
hypothesis — `C` neither an affine set nor a closed half of one — cannot be dropped: over `[0, ∞)`
the relative boundary is `{0}`, yet `f x = x` has supremum `⊤`. -/
theorem ConvexFn.iSup_sdiff_relint (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hhalf : ¬ IsAffineHalf C) : (⨆ x ∈ C, f x) = ⨆ x ∈ C \ ri C, f x := by
  conv_lhs => rw [← convexHull_sdiff_relint hC hCcl hhalf]
  exact hf.iSup_convexHull _

/-- Attainment: a maximiser can be replaced by one on the relative boundary. -/
theorem exists_notMem_relint_eq_of_isMaxOn (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hhalf : ¬ IsAffineHalf C) {x : E} (hx : x ∈ C) (hmax : ∀ z ∈ C, f z ≤ f x) :
    ∃ z ∈ C \ ri C, f z = f x := by
  rw [← convexHull_sdiff_relint hC hCcl hhalf] at hx hmax
  exact exists_eq_of_isMaxOn_convexHull hf hx hmax

/-- The relative-boundary supremum under a hypothesis easier to check: a closed convex set of
dimension at least two containing no lines is neither affine nor a closed half of an affine set. -/
theorem ConvexFn.iSup_sdiff_relint_of_containsNoLine (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hnl : ContainsNoLine C) (hne : C.Nonempty)
    (hdim : 2 ≤ Module.finrank ℝ (vectorSpan ℝ C)) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ C \ ri C, f x :=
  hf.iSup_sdiff_relint hC hCcl fun h => not_containsNoLine_of_isAffineHalf h hne hdim hnl

end Boundary

/-! ### The extreme point principle -/

section Ray

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {C : Set E}

/-- **A convex function bounded above on a half-line does not increase along it**: if
`f (u + t • v) ≤ β` for every `t ≥ 0` then `f (u + v) ≤ f u`. -/
theorem ConvexFn.add_le_of_forall_add_smul_le (hf : ConvexFn f) {u v : E} {β : ℝ}
    (hray : ∀ t : ℝ, 0 ≤ t → f (u + t • v) ≤ (β : EReal)) : f (u + v) ≤ f u := by
  by_contra hcon
  have hlt : f u < f (u + v) := not_le.1 hcon
  obtain ⟨ξ, hξ1, hξ2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  obtain ⟨η, hη1, hη2⟩ := EReal.lt_iff_exists_real_btwn.1 hξ2
  have hξη : ξ < η := by exact_mod_cast hη1
  set t : ℝ := max 1 (1 + (β - ξ) / (η - ξ)) with ht
  have ht1 : (1 : ℝ) ≤ t := le_max_left _ _
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  have hcancel : (β - ξ) / (η - ξ) * (η - ξ) = β - ξ := div_mul_cancel₀ _ (by linarith)
  have hkey : β - ξ < t * (η - ξ) := by
    nlinarith [le_max_right (1 : ℝ) (1 + (β - ξ) / (η - ξ))]
  have hcomb := hf.epi_combo hξ1.le (hray t ht0.le) (a := 1 - t⁻¹) (b := t⁻¹)
    (by simp [inv_le_one_of_one_le₀ ht1]) (by positivity) (by ring)
  have hpt : (1 - t⁻¹) • u + t⁻¹ • (u + t • v) = u + v := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul, sub_smul, one_smul]
    abel
  rw [hpt] at hcomb
  have hηlt : (η : EReal) < (((1 - t⁻¹) * ξ + t⁻¹ * β : ℝ) : EReal) := lt_of_lt_of_le hη2 hcomb
  have hηlt' : η < (1 - t⁻¹) * ξ + t⁻¹ * β := by exact_mod_cast hηlt
  have hinv0 : (0 : ℝ) < t⁻¹ := inv_pos.2 ht0
  have hmul : t⁻¹ * (β - ξ) < η - ξ := by
    have h := mul_lt_mul_of_pos_left hkey hinv0
    rwa [← mul_assoc, inv_mul_cancel₀ ht0.ne', one_mul] at h
  linarith

/-- **Bounded above on `C` implies non-increasing along a direction of recession of `C`** — the
analytic core of the extreme point principle. -/
theorem ConvexFn.add_le_of_mem_recessionCone (hf : ConvexFn f) {β : ℝ}
    (hbdd : ∀ x ∈ C, f x ≤ (β : EReal)) {u v : E} (hu : u ∈ C) (hv : v ∈ recessionCone C) :
    f (u + v) ≤ f u :=
  hf.add_le_of_forall_add_smul_le fun t ht => hbdd _ (hv u hu t ht)

/-- **`f` is bounded above on every half-line of `C`**: for every `u` and `v` with `u + t • v ∈ C`
for all `t ≥ 0`, some real `β` bounds `f` there. The direction `v = 0` makes it say `C ⊆ dom f` as
well, so this one predicate carries both standing hypotheses of the extreme point principle. -/
def BddAboveOnRays (f : E → EReal) (C : Set E) : Prop :=
  ∀ u v : E, (∀ t : ℝ, 0 ≤ t → u + t • v ∈ C) →
    ∃ β : ℝ, ∀ t : ℝ, 0 ≤ t → f (u + t • v) ≤ (β : EReal)

theorem bddAboveOnRays_of_forall_le {β : ℝ} (hbdd : ∀ x ∈ C, f x ≤ (β : EReal)) :
    BddAboveOnRays f C := fun _ _ hray => ⟨β, fun t ht => hbdd _ (hray t ht)⟩

theorem BddAboveOnRays.mono {C' : Set E} (hray : BddAboveOnRays f C) (hsub : C' ⊆ C) :
    BddAboveOnRays f C' := fun u v hr => hray u v fun t ht => hsub (hr t ht)

/-- The degenerate half-lines — the points — of `C` already force `C ⊆ dom f`. -/
theorem BddAboveOnRays.subset_convexDom (hray : BddAboveOnRays f C) : C ⊆ convexDom f := by
  intro u hu
  obtain ⟨β, hβ⟩ := hray u 0 fun t _ => by simpa using hu
  have hle := hβ 0 le_rfl
  simp only [smul_zero, add_zero] at hle
  exact lt_of_le_of_lt hle (by simp)

/-- The previous bound weakened to the one half-line the proof actually uses. -/
theorem ConvexFn.add_le_of_bddAboveOnRays (hf : ConvexFn f) (hray : BddAboveOnRays f C) {u v : E}
    (hu : u ∈ C) (hv : v ∈ recessionCone C) : f (u + v) ≤ f u := by
  obtain ⟨β, hβ⟩ := hray u v fun t ht => hv u hu t ht
  exact hf.add_le_of_forall_add_smul_le hβ

/-- **Bounded above on the half-lines of `C` implies constant along the lineality space of `C`**:
the two opposite directions of recession give inequalities that close on each other. -/
theorem ConvexFn.add_eq_of_mem_linealitySpace (hf : ConvexFn f) (hray : BddAboveOnRays f C)
    {u v : E} (hu : u ∈ C) (hv : v ∈ linealitySpace C) : f (u + v) = f u := by
  obtain ⟨hv1, hv2⟩ := mem_linealitySpace.1 hv
  refine le_antisymm (hf.add_le_of_bddAboveOnRays hray hu hv1) ?_
  have huv : u + v ∈ C := add_mem_of_mem_recessionCone hv1 hu
  have hback := hf.add_le_of_bddAboveOnRays hray huv hv2
  rwa [show u + v + -v = u by abel] at hback

/-- **Reduction of `C` to `C ∩ N` at the level of values**: for any complement `N` of the lineality
space of `C`, every point of `C` carries the same value of `f` as some point of `C ∩ N`. The
decomposition `C = L + (C ∩ N)` is algebraic: no closedness, no finite dimension. -/
theorem ConvexFn.exists_mem_inter_eq_of_isCompl (hf : ConvexFn f) (hray : BddAboveOnRays f C)
    {N : Submodule ℝ E} (hN : IsCompl (linealitySubmodule C) N) {w : E} (hw : w ∈ C) :
    ∃ q ∈ C ∩ (N : Set E), f w = f q := by
  have hdec : C = (linealitySubmodule C : Set E) + (C ∩ (N : Set E)) :=
    eq_add_inter_of_isCompl hN
  obtain ⟨p, hp, q, hq, rfl⟩ :=
    (hdec ▸ hw : w ∈ (linealitySubmodule C : Set E) + (C ∩ (N : Set E)))
  refine ⟨q, hq, ?_⟩
  change f (p + q) = f q
  rw [show p + q = q + p by abel]
  exact hf.add_eq_of_mem_linealitySpace hray hq.1 (by simpa using hp)

/-- **A convex function bounded above on the whole space is constant** — the unbounded companion of
the maximum principle, where the absence of any boundary replaces `ri C`. -/
theorem ConvexFn.eq_of_forall_le (hf : ConvexFn f) {β : ℝ} (hbdd : ∀ x : E, f x ≤ (β : EReal))
    (x y : E) : f x = f y := by
  have key : ∀ u v : E, f (u + v) ≤ f u := fun u v =>
    hf.add_le_of_forall_add_smul_le fun t _ => hbdd _
  have hxy : x + (y - x) = y := by abel
  have hyx : y + (x - y) = x := by abel
  have h₁ := key x (y - x)
  have h₂ := key y (x - y)
  rw [hxy] at h₁
  rw [hyx] at h₂
  exact le_antisymm h₂ h₁

end Ray

section ExtremeUnbounded

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {C : Set E}

/-- **Every point of `C` is dominated by a point of `conv (ext C)`**, for `f` bounded above on the
half-lines of a closed convex line-free `C`; the representation of `C` splits `x` as `u + v`. -/
theorem ConvexFn.exists_mem_convexHull_extremePoints_le (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hnl : ContainsNoLine C) (hray : BddAboveOnRays f C)
    {x : E} (hx : x ∈ C) : ∃ u ∈ convexHull ℝ (C.extremePoints ℝ), f x ≤ f u := by
  have hrep := convexHullPD_extremePoints_extremeDirections hC hCcl hnl
  have hx' : x ∈ convexHullPD (C.extremePoints ℝ) (extremeDirections C) := by rw [hrep]; exact hx
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_convexHullPD.1 hx'
  refine ⟨u, hu, hf.add_le_of_bddAboveOnRays hray ?_ ?_⟩
  · rw [← hrep]
    exact convexHull_subset_convexHullPD _ _ hu
  · rw [← hrep]
    exact coneHull_subset_recessionCone_convexHullPD _ _ hv

/-- **The extreme point principle** for `L = 0`: the supremum of a convex function over a closed
convex `C` with no lines, bounded above on every half-line of `C`, is its supremum over `ext C`.
`BddAboveOnRays` is genuinely weaker than a uniform bound: `f (ξ₁, ξ₂) = ξ₁` on
`C = {(ξ₁, ξ₂) | ξ₁² ≤ ξ₂}` is bounded on each half-line and unbounded on `C`. -/
theorem ConvexFn.iSup_extremePoints_of_containsNoLine (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hnl : ContainsNoLine C) (hray : BddAboveOnRays f C) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ C.extremePoints ℝ, f x := by
  refine le_antisymm (iSup₂_le fun x hx => ?_)
    (iSup₂_le fun x hx => le_iSup₂ (f := fun z (_ : z ∈ C) => f z) x (extremePoints_subset hx))
  obtain ⟨u, hu, hle⟩ := hf.exists_mem_convexHull_extremePoints_le hC hCcl hnl hray hx
  refine hle.trans ?_
  rw [← hf.iSup_convexHull (C.extremePoints ℝ)]
  exact le_iSup₂ (f := fun z (_ : z ∈ convexHull ℝ (C.extremePoints ℝ)) => f z) u hu

/-- A supremum over a closed convex line-free set, if attained at all, is attained at an extreme
point. No boundedness hypothesis is needed, but `f x ≠ ⊤` is: on `[0, ∞)` with `f = 0` on `[0, 1)`
and `⊤` beyond, `⊤` is a maximum yet the extreme point carries `0`. -/
theorem exists_mem_extremePoints_eq_of_isMaxOn_of_containsNoLine (hf : ConvexFn f)
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hnl : ContainsNoLine C) {x : E} (hx : x ∈ C)
    (hxt : f x ≠ ⊤) (hmax : ∀ z ∈ C, f z ≤ f x) : ∃ z ∈ C.extremePoints ℝ, f z = f x := by
  rcases eq_or_ne (f x) ⊥ with hbot | hbot
  · obtain ⟨z, hz⟩ := extremePoints_nonempty_of_containsNoLine hC hCcl hnl ⟨x, hx⟩
    have hzle : f z ≤ ⊥ := hbot ▸ hmax z (extremePoints_subset hz)
    exact ⟨z, hz, by rw [le_bot_iff.1 hzle, hbot]⟩
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hbot (lt_top_iff_ne_top.2 hxt)
  have hbdd : ∀ z ∈ C, f z ≤ (r : EReal) := fun z hz => hr ▸ hmax z hz
  obtain ⟨u, hu, hle⟩ :=
    hf.exists_mem_convexHull_extremePoints_le hC hCcl hnl (bddAboveOnRays_of_forall_le hbdd) hx
  have hsub : convexHull ℝ (C.extremePoints ℝ) ⊆ C := convexHull_min extremePoints_subset hC
  have hux : f u = f x := le_antisymm (hmax u (hsub hu)) hle
  obtain ⟨z, hz, hzu⟩ :=
    exists_eq_of_isMaxOn_convexHull hf hu fun z hz => hux ▸ hmax z (hsub hz)
  exact ⟨z, hz, by rw [hzu, hux]⟩

/-- **The extreme point principle** in representation form, with no boundedness hypothesis: the
supremum over a closed convex line-free set is the supremum over the sums of an extreme point and
a non-negative combination of extreme directions. -/
theorem ConvexFn.iSup_extremePoints_add_coneHull (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hnl : ContainsNoLine C) :
    (⨆ x ∈ C, f x)
      = ⨆ x ∈ C.extremePoints ℝ + (PointedCone.hull ℝ (extremeDirections C) : Set E), f x := by
  have hcone : Convex ℝ ((PointedCone.hull ℝ (extremeDirections C) : Set E)) :=
    ((PointedCone.hull ℝ (extremeDirections C) : ConvexCone ℝ E)).convex
  have hhull : convexHull ℝ
      (C.extremePoints ℝ + (PointedCone.hull ℝ (extremeDirections C) : Set E)) = C := by
    rw [convexHull_add, hcone.convexHull_eq, ← convexHullPD_def]
    exact convexHullPD_extremePoints_extremeDirections hC hCcl hnl
  conv_lhs => rw [← hhull]
  exact hf.iSup_convexHull _

/-! ### The lineality space quotiented out -/

/-- **The extreme point principle** in full: for *any* complement `N` of the lineality space of a
closed convex `C`, the supremum of a convex function bounded above on the half-lines of `C` is its
supremum over the extreme points of `C ∩ N`. The book takes `N = L⊥`; every complement works. -/
theorem ConvexFn.iSup_extremePoints_inter_of_isCompl (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hray : BddAboveOnRays f C) {N : Submodule ℝ E}
    (hN : IsCompl (linealitySubmodule C) N) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ (C ∩ (N : Set E)).extremePoints ℝ, f x := by
  rw [← hf.iSup_extremePoints_of_containsNoLine (hC.inter (Submodule.convex N))
    (hCcl.inter (Submodule.closed_of_finiteDimensional N))
    (containsNoLine_inter_of_isCompl hC hCcl hN) (hray.mono Set.inter_subset_left)]
  refine le_antisymm (iSup₂_le fun x hx => ?_) (iSup₂_le fun x hx =>
    le_iSup₂ (f := fun z (_ : z ∈ C) => f z) x (Set.inter_subset_left hx))
  obtain ⟨q, hq, hfq⟩ := hf.exists_mem_inter_eq_of_isCompl hray hN hx
  rw [hfq]
  exact le_iSup₂ (f := fun z (_ : z ∈ C ∩ (N : Set E)) => f z) q hq

/-- Attainment for an arbitrary complement `N` of the lineality space: a maximiser over `C` can be
replaced by an extreme point of `C ∩ N`. -/
theorem exists_mem_extremePoints_inter_eq_of_isMaxOn_of_isCompl (hf : ConvexFn f)
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hray : BddAboveOnRays f C) {N : Submodule ℝ E}
    (hN : IsCompl (linealitySubmodule C) N) {x : E} (hx : x ∈ C) (hmax : ∀ w ∈ C, f w ≤ f x) :
    ∃ z ∈ (C ∩ (N : Set E)).extremePoints ℝ, f z = f x := by
  obtain ⟨q, hq, hfq⟩ := hf.exists_mem_inter_eq_of_isCompl hray hN hx
  obtain ⟨z, hz, hzq⟩ := exists_mem_extremePoints_eq_of_isMaxOn_of_containsNoLine hf
    (hC.inter (Submodule.convex N)) (hCcl.inter (Submodule.closed_of_finiteDimensional N))
    (containsNoLine_inter_of_isCompl hC hCcl hN) hq
    (by rw [← hfq]; exact (mem_convexDom.1 (hray.subset_convexDom hx)).ne)
    (fun w hw => by rw [← hfq]; exact hmax w hw.1)
  exact ⟨z, hz, by rw [hzq, ← hfq]⟩

end ExtremeUnbounded

/-! ### Finitely generated sets -/

section Polyhedral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {C : Set E}

/-- **The extreme point principle for a finitely generated set**: bounded above on every half-line
of a nonempty finitely generated line-free convex set, `f` attains its supremum at an extreme
point — of which there are only finitely many. -/
theorem exists_mem_extremePoints_isMaxOn_of_finitelyGenerated_of_bddAboveOnRays (hf : ConvexFn f)
    (hC : FinitelyGenerated C) (hnl : ContainsNoLine C) (hne : C.Nonempty)
    (hray : BddAboveOnRays f C) : ∃ z ∈ C.extremePoints ℝ, ∀ w ∈ C, f w ≤ f z := by
  have hcl : IsClosed C := hC.isClosed
  obtain ⟨P, D, hCeq⟩ := hC
  have hCPD : C = convexHullPD (P : Set E) (D : Set E) := hCeq
  have hconv : Convex ℝ C := by rw [hCPD]; exact convex_convexHullPD _ _
  have hfin : (C.extremePoints ℝ).Finite := by
    rw [hCPD]; exact finite_extremePoints_convexHullPD P D
  obtain ⟨z, hz, hzmax⟩ := Set.exists_max_image (C.extremePoints ℝ) f hfin
    (extremePoints_nonempty_of_containsNoLine hconv hcl hnl hne)
  refine ⟨z, hz, fun w hw => ?_⟩
  obtain ⟨u, hu, hle⟩ := hf.exists_mem_convexHull_extremePoints_le hconv hcl hnl hray hw
  exact hle.trans (convexHull_min (fun y hy => hzmax y hy) (hf.convex_le (f z)) hu)

/-- A convex function bounded above on a nonempty polyhedral convex set containing no lines
attains its supremum at one of its finitely many extreme points. -/
theorem exists_mem_extremePoints_isMaxOn_of_finitelyGenerated (hf : ConvexFn f)
    (hC : FinitelyGenerated C) (hnl : ContainsNoLine C) (hne : C.Nonempty) {β : ℝ}
    (hbdd : ∀ x ∈ C, f x ≤ (β : EReal)) : ∃ z ∈ C.extremePoints ℝ, ∀ w ∈ C, f w ≤ f z :=
  exists_mem_extremePoints_isMaxOn_of_finitelyGenerated_of_bddAboveOnRays hf hC hnl hne
    (bddAboveOnRays_of_forall_le hbdd)

/-- A convex function bounded above on every half-line of a nonempty polyhedral convex `C ⊆ dom f`
attains its supremum relative to `C`. Unlike the previous result this asks nothing about lines in
`C`, and claims nothing about extreme points of `C` — a set containing a line has none. The
maximiser is an extreme point of `C ∩ N` and depends on the complement `N` chosen, hence the bare
attainment conclusion. -/
theorem exists_isMaxOn_of_polyhedral_of_bddAboveOnRays (hf : ConvexFn f) (hC : Polyhedral C)
    (hne : C.Nonempty) (hray : BddAboveOnRays f C) : ∃ z ∈ C, ∀ w ∈ C, f w ≤ f z := by
  obtain ⟨N, hN⟩ := Submodule.exists_isCompl (linealitySubmodule C)
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨q₀, hq₀, -⟩ := hf.exists_mem_inter_eq_of_isCompl hray hN hx₀
  obtain ⟨z, hz, hzmax⟩ := exists_mem_extremePoints_isMaxOn_of_finitelyGenerated_of_bddAboveOnRays
    hf (hC.inter (polyhedral_coe_submodule N)).finitelyGenerated
    (containsNoLine_inter_of_isCompl hC.convex hC.isClosed hN) ⟨q₀, hq₀⟩
    (hray.mono Set.inter_subset_left)
  refine ⟨z, (extremePoints_subset hz : z ∈ C ∩ (N : Set E)).1, fun w hw => ?_⟩
  obtain ⟨q, hq, hwq⟩ := hf.exists_mem_inter_eq_of_isCompl hray hN hw
  rw [hwq]
  exact hzmax q hq

end Polyhedral

/-! ### The extreme point principle, compact case -/

section Extreme

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {C : Set E}

/-- For compact `C` the supremum over the set is its supremum over the extreme points:
**Minkowski's theorem** fed to the convex hull identity. -/
theorem ConvexFn.iSup_extremePoints (hf : ConvexFn f) (hcomp : IsCompact C) (hconv : Convex ℝ C) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ C.extremePoints ℝ, f x := by
  conv_lhs => rw [← convexHull_extremePoints hcomp hconv]
  exact hf.iSup_convexHull _

/-- A maximiser over a compact convex set is matched by an extreme point. -/
theorem exists_mem_extremePoints_eq_of_isMaxOn (hf : ConvexFn f) (hcomp : IsCompact C)
    (hconv : Convex ℝ C) {x : E} (hx : x ∈ C) (hmax : ∀ z ∈ C, f z ≤ f x) :
    ∃ z ∈ C.extremePoints ℝ, f z = f x := by
  rw [← convexHull_extremePoints hcomp hconv] at hx hmax
  exact exists_eq_of_isMaxOn_convexHull hf hx hmax

/-- The "supremum is attained" clause: a convex function attains its supremum over a nonempty
compact convex `C ⊆ ri (dom f)` at an extreme point. The hypothesis is `C ⊆ ri (dom f)`, not the
book's `C ⊆ dom f`, under which the clause is false. -/
theorem exists_mem_extremePoints_isMaxOn_of_isCompact (hf : ConvexFn f) (hp : ProperConvex f)
    (hcomp : IsCompact C) (hconv : Convex ℝ C) (hne : C.Nonempty) (hCri : C ⊆ ri (convexDom f)) :
    ∃ z ∈ C.extremePoints ℝ, ∀ w ∈ C, f w ≤ f z := by
  obtain ⟨x, hx, hxmax⟩ :=
      hcomp.exists_isMaxOn hne ((hf.continuousOn_relint_convexDom hp).mono hCri)
  obtain ⟨z, hz, hzx⟩ :=
    exists_mem_extremePoints_eq_of_isMaxOn hf hcomp hconv hx fun w hw => isMaxOn_iff.1 hxmax w hw
  exact ⟨z, hz, fun w hw => hzx ▸ isMaxOn_iff.1 hxmax w hw⟩

end Extreme

/-! ### Subgradients at a maximiser -/

section Optimality

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {C : Set E} {x : E} {y : F}

/-- At a point where `f` attains its supremum over `C`, every subgradient of `f` is normal to `C`.
All that is needed is that `f x` be real. -/
theorem mem_normalCone_of_mem_subdifferential_of_isMaxOn (hxb : f x ≠ ⊥) (hxt : f x ≠ ⊤)
    (hmax : ∀ z ∈ C, f z ≤ f x) (hy : y ∈ subdifferential B f x) : y ∈ normalCone B C x := by
  intro z hz
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hxb (lt_top_iff_ne_top.2 hxt)
  have h2 : f x + ((B (z - x) y : ℝ) : EReal) ≤ f x := le_trans (hy z) (hmax z hz)
  rw [hr, ← EReal.coe_add, EReal.coe_le_coe_iff] at h2
  linarith

/-- Non-vanishing clause: if `f` is not constant on `C`, no subgradient at a maximiser can be
zero. -/
theorem ne_zero_of_mem_subdifferential_of_isMaxOn (hmax : ∀ z ∈ C, f z ≤ f x) {z₀ : E}
    (hz₀ : z₀ ∈ C) (hne : f z₀ ≠ f x) (hy : y ∈ subdifferential B f x) : y ≠ 0 := by
  rintro rfl
  have hle : f x ≤ f z₀ := by simpa using hy z₀
  exact hne (le_antisymm (hmax z₀ hz₀) hle)

/-- A vector normal to `C` at `x` is one whose linear functional attains its supremum over `C`
at `x`. -/
theorem le_of_mem_normalCone (hy : y ∈ normalCone B C x) {z : E} (hz : z ∈ C) : B z y ≤ B x y := by
  have h := hy z hz
  rw [map_sub, LinearMap.sub_apply] at h
  linarith

end Optimality

end ConvexAnalysis
