import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Instances.EReal.Lemmas
import Numlib.Analysis.Convex.Epigraph

/-!
# Separation theorems

Separation of convex sets by hyperplanes, over a real topological vector space — locally convex
where separation is actually invoked. Almost all of the *mathematics* is already in Mathlib, as the
`geometric_hahn_banach_*` family and `iInter_halfSpaces_eq`; what this file supplies is the
*vocabulary* — the three notions of separation, supporting hyperplanes and half-spaces — together
with the statements Mathlib does not have.

Two statements of the textbook are **false** at this generality and are corrected rather than
dropped. That a convex set other than the whole space lies in a closed half-space is proved there
through `ri (cl C) ⊆ C`, and fails in infinite dimensions: the kernel of a discontinuous linear
functional is a proper convex subset that is dense, so no nonzero continuous functional is bounded
above on it. The hypothesis here is `closure s ≠ univ`, and likewise for the cone version.

Proper separation by relative interiors, and the existence of a supporting hyperplane at every
relative boundary point, rest on the line segment principle and on `ri C ≠ ∅` for nonempty convex
`C`; they are finite-dimensional and live in `Numlib/Analysis/Convex/RelativeInterior.lean`.

## Main definitions

* `Separates f c s t` — the hyperplane `{x | f x = c}` separates `s` and `t`: `s` lies in the
  closed half-space `{x | f x ≤ c}` and `t` in the opposite one.
* `SeparatesProperly f c s t` — separation in which `s` and `t` are not *both* contained in the
  hyperplane.
* `SeparatesStrongly f c s t` — separation with a *gap*: `⨆_{s} f < c < ⨅_{t} f`, the extrema
  being taken in `EReal`.
* `IsSupporting f c s` — `{x | f x ≤ c}` is a supporting half-space to `s` and `{x | f x = c}` a
  supporting hyperplane: `f ≠ 0`, `f ≤ c` on `s`, and `f x = c` somewhere on `s`.
* `halfSpaceCone f` — the homogeneous closed half-space `{x | f x ≤ 0}`, bundled as a
  `PointedCone ℝ E`.

## Main results

* `separates_iff_iSup_le_iInf`, `exists_separatesProperly_iff_iSup_le_iInf`,
  `exists_separatesStrongly_iff_iSup_lt_iInf` — the description of the three notions by the extrema
  of `f` over the two sets ([rockafellar1970convex] Theorem 11.1).
* `separatesStrongly_iff_exists_gap`, `separatesStrongly_iff_exists_nhds`,
  `separatesStrongly_iff_exists_closedBall` — the three faces of strong separation: a uniform gap,
  a neighbourhood of the origin, and — in a normed space — the textbook's `ε`-balls.
* `exists_separates_of_isOpen_of_disjoint_affine` — an open convex set and a disjoint affine set
  are separated by a hyperplane containing the affine set.
* `separatesStrongly_iff_zero_notMem_closure_sub` — strong separation is possible exactly when
  `0 ∉ closure (s - t)`; `separatesStrongly_of_disjoint_isCompact_isClosed` is the compact/closed
  case.
* `isClosed_convex_eq_iInter_halfspaces` — a closed convex set is the intersection of the closed
  half-spaces containing it ([rockafellar1970convex] Theorem 11.5), with
  `mem_iff_forall_le_halfSpace` as its pointwise form and `closure_convexHull_eq_iInter_halfspaces`
  for an arbitrary set.
* `exists_isSupporting_iff_disjoint_interior` — a convex subset lies in a non-trivial supporting
  hyperplane exactly when it misses the interior.
* `SeparatesProperly.zero_of_isCone_left` — proper separation of a cone can always be moved to a
  hyperplane through the origin, whence the half-space representations of cones.
* `exists_separating_of_notMem_closed_convex` — the point/closed-convex-set case, in the form the
  conjugacy module consumes.
* `exists_affine_lt_of_notMem`, `exists_affine_le_of_isClosed_epi` — the `E × ℝ` specialisation:
  separating a point from a closed convex set that has a point vertically above it produces a
  *non-vertical* functional, hence a continuous affine function on `E`.

## Implementation notes

Strong separation is *defined* by the gap `⨆_{s} f < c < ⨅_{t} f` rather than by the textbook's
`C₁ + εB`: the gap presupposes no topology on `E`, so its description by the extrema sits one layer
below the separation theorems that produce it, and taking the extrema in `EReal` removes the
`Nonempty` and `BddAbove` side conditions a real-valued `sSup` would force. Note that *pointwise*
strict separation — `f < c` on `s` and `c < f` on `t` — is a genuinely weaker notion and is not
among the three. General closed half-spaces are left as a pair `(f, c)`, since the only facts ever
needed of `{x | f x ≤ c}` apply to that description directly; only the homogeneous ones are
bundled, as `halfSpaceCone`.

## References

* [rockafellar1970convex] §11.
-/

open Set Filter Topology Pointwise

namespace ConvexAnalysis

/-! ### The three notions of separation -/

section Defs

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- `Separates f c s t` : the hyperplane `{x | f x = c}` separates `s` and `t`, in the sense that
`s` lies in the closed half-space `{x | f x ≤ c}` and `t` in the opposite one. Rockafellar asks in
addition that `f ≠ 0`; that is not built in here, because it is automatic in the two notions where
it matters (`SeparatesProperly.ne_zero`, `SeparatesStrongly.ne_zero`). -/
structure Separates (f : E →L[ℝ] ℝ) (c : ℝ) (s t : Set E) : Prop where
  /-- `f` is at most `c` on `s`. -/
  le_of_mem_left : ∀ ⦃x⦄, x ∈ s → f x ≤ c
  /-- `f` is at least `c` on `t`. -/
  le_of_mem_right : ∀ ⦃x⦄, x ∈ t → c ≤ f x

/-- `SeparatesProperly f c s t` : `f` separates `s` and `t` at level `c`, and `s` and `t` are not
*both* contained in the hyperplane `{x | f x = c}`. One of the two may be. -/
structure SeparatesProperly (f : E →L[ℝ] ℝ) (c : ℝ) (s t : Set E) : Prop
    extends Separates f c s t where
  /-- `s` and `t` do not both lie inside the separating hyperplane. -/
  not_subset : ¬ (s ∪ t ⊆ {x | f x = c})

/-- `SeparatesStrongly f c s t` : `f` separates `s` and `t` with a *gap*, the extrema being taken in
`EReal` so that empty and unbounded sets need no special treatment. Rockafellar's own definition
presupposes a norm, and is recovered by `separatesStrongly_iff_exists_closedBall`. -/
structure SeparatesStrongly (f : E →L[ℝ] ℝ) (c : ℝ) (s t : Set E) : Prop where
  /-- `f` stays bounded away from `c` from below on `s`. -/
  iSup_lt : (⨆ x ∈ s, (f x : EReal)) < (c : EReal)
  /-- `f` stays bounded away from `c` from above on `t`. -/
  lt_iInf : (c : EReal) < ⨅ x ∈ t, (f x : EReal)

variable {f : E →L[ℝ] ℝ} {c : ℝ} {s t : Set E}

/-- Separation is symmetric under exchanging the two sets and negating the functional. -/
theorem Separates.symm (h : Separates f c s t) : Separates (-f) (-c) t s :=
  ⟨fun _ hx => by simpa using neg_le_neg (h.le_of_mem_right hx),
   fun _ hx => by simpa using neg_le_neg (h.le_of_mem_left hx)⟩

/-- Separation passes to subsets. -/
theorem Separates.mono {s' t' : Set E} (h : Separates f c s t) (hs : s' ⊆ s) (ht : t' ⊆ t) :
    Separates f c s' t' :=
  ⟨fun _ hx => h.le_of_mem_left (hs hx), fun _ hx => h.le_of_mem_right (ht hx)⟩

/-- Separation passes to closures: closed half-spaces are closed. -/
theorem Separates.closure (h : Separates f c s t) : Separates f c (closure s) (closure t) :=
  ⟨fun _ hx => closure_minimal (fun _ hy => h.le_of_mem_left hy)
      (isClosed_le f.continuous continuous_const) hx,
   fun _ hx => closure_minimal (fun _ hy => h.le_of_mem_right hy)
      (isClosed_le continuous_const f.continuous) hx⟩

/-- Separation passes to convex hulls: closed half-spaces are convex. -/
theorem Separates.convexHull (h : Separates f c s t) :
    Separates f c (convexHull ℝ s) (convexHull ℝ t) :=
  ⟨fun _ hx => convexHull_min (fun _ hy => h.le_of_mem_left hy)
      (convex_halfSpace_le f.toLinearMap.isLinear c) hx,
   fun _ hx => convexHull_min (fun _ hy => h.le_of_mem_right hy)
      (convex_halfSpace_ge f.toLinearMap.isLinear c) hx⟩

/-- Proper separation is symmetric under exchanging the two sets and negating the functional. -/
theorem SeparatesProperly.symm (h : SeparatesProperly f c s t) :
    SeparatesProperly (-f) (-c) t s where
  toSeparates := h.toSeparates.symm
  not_subset hsub := h.not_subset fun x hx => by
    have hx' : (-f) x = -c := hsub (by rwa [union_comm] at hx)
    have : -f x = -c := by simpa using hx'
    exact neg_injective this

/-- A properly separating functional is nonzero, so that `{x | f x = c}` really is a hyperplane. -/
theorem SeparatesProperly.ne_zero (h : SeparatesProperly f c s t) (hs : s.Nonempty)
    (ht : t.Nonempty) : f ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx⟩ := hs
  obtain ⟨y, hy⟩ := ht
  have h₁ : (0 : ℝ) ≤ c := by simpa using h.le_of_mem_left hx
  have h₂ : c ≤ (0 : ℝ) := by simpa using h.le_of_mem_right hy
  exact h.not_subset fun z _ => by simp [le_antisymm h₂ h₁]

end Defs

/-! ### Separation and the extrema of a linear function -/

section Extrema

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {f : E →L[ℝ] ℝ} {c : ℝ} {s t : Set E}

/-- The value of `f` at a point of `s` is at most the supremum of `f` over `s`. Spelling out the
indexed family is what keeps `le_iSup₂` from having to guess it through a coercion. -/
theorem coe_apply_le_iSup₂ {x : E} (hx : x ∈ s) :
    ((f x : ℝ) : EReal) ≤ ⨆ y ∈ s, (f y : EReal) :=
  le_iSup₂ (f := fun y (_ : y ∈ s) => ((f y : ℝ) : EReal)) x hx

/-- The infimum of `f` over `t` is at most the value of `f` at a point of `t`. -/
theorem iInf₂_le_coe_apply {x : E} (hx : x ∈ t) :
    (⨅ y ∈ t, (f y : EReal)) ≤ ((f x : ℝ) : EReal) :=
  iInf₂_le (f := fun y (_ : y ∈ t) => ((f y : ℝ) : EReal)) x hx

/-- Strong separation passes to subsets, exactly as ordinary separation does: shrinking the sets
only shrinks the two extrema. -/
theorem SeparatesStrongly.mono {s' t' : Set E} (h : SeparatesStrongly f c s t) (hs : s' ⊆ s)
    (ht : t' ⊆ t) : SeparatesStrongly f c s' t' :=
  ⟨lt_of_le_of_lt (iSup₂_le fun _ hx => coe_apply_le_iSup₂ (hs hx)) h.iSup_lt,
    lt_of_lt_of_le h.lt_iInf (le_iInf₂ fun _ hx => iInf₂_le_coe_apply (ht hx))⟩

/-- `f` separates `s` and `t` at level `c` exactly when `c` lies between the supremum of `f` over
`s` and its infimum over `t`. -/
theorem separates_iff_iSup_le_iInf :
    Separates f c s t ↔
      (⨆ x ∈ s, (f x : EReal)) ≤ (c : EReal) ∧ (c : EReal) ≤ ⨅ x ∈ t, (f x : EReal) := by
  constructor
  · intro h
    exact ⟨iSup₂_le fun x hx => by exact_mod_cast h.le_of_mem_left hx,
      le_iInf₂ fun x hx => by exact_mod_cast h.le_of_mem_right hx⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · exact_mod_cast (coe_apply_le_iSup₂ hx).trans h₁
    · exact_mod_cast h₂.trans (iInf₂_le_coe_apply hx)

/-- The supremum of a real-valued function over a nonempty set is not `⊥`. -/
theorem bot_lt_iSup₂_of_nonempty (hs : s.Nonempty) : (⊥ : EReal) < ⨆ x ∈ s, (f x : EReal) := by
  obtain ⟨x, hx⟩ := hs
  exact lt_of_lt_of_le (EReal.bot_lt_coe _) (coe_apply_le_iSup₂ hx)

/-- The infimum of a real-valued function over a nonempty set is not `⊤`. -/
theorem iInf₂_lt_top_of_nonempty (ht : t.Nonempty) : (⨅ x ∈ t, (f x : EReal)) < ⊤ := by
  obtain ⟨x, hx⟩ := ht
  exact lt_of_le_of_lt (iInf₂_le_coe_apply hx) (EReal.coe_lt_top _)

/-- Over a nonempty set the infimum is at most the supremum. -/
theorem iInf₂_le_iSup₂_of_nonempty (hs : s.Nonempty) :
    (⨅ x ∈ s, (f x : EReal)) ≤ ⨆ x ∈ s, (f x : EReal) := by
  obtain ⟨x, hx⟩ := hs
  exact (iInf₂_le_coe_apply hx).trans (coe_apply_le_iSup₂ hx)

/-- Some hyperplane orthogonal to `f` separates two nonempty sets exactly when `f` never exceeds on
`s` what it attains on `t`. -/
theorem exists_separates_iff_iSup_le_iInf (hs : s.Nonempty) (ht : t.Nonempty) :
    (∃ c, Separates f c s t) ↔ (⨆ x ∈ s, (f x : EReal)) ≤ ⨅ x ∈ t, (f x : EReal) := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨h₁, h₂⟩ := separates_iff_iSup_le_iInf.1 hc
    exact h₁.trans h₂
  · intro h
    obtain ⟨a, ha⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
      (bot_lt_iSup₂_of_nonempty (f := f) hs).ne' (lt_of_le_of_lt h (iInf₂_lt_top_of_nonempty ht))
    exact ⟨a, separates_iff_iSup_le_iInf.2 ⟨ha.le, ha ▸ h⟩⟩

/-- Proper separation is separation in which `f` dips strictly below `c` somewhere on `s`, or rises
strictly above it somewhere on `t`. -/
theorem separatesProperly_iff_iInf_lt_or_lt_iSup :
    SeparatesProperly f c s t ↔ Separates f c s t ∧
      ((⨅ x ∈ s, (f x : EReal)) < (c : EReal) ∨ (c : EReal) < ⨆ x ∈ t, (f x : EReal)) := by
  constructor
  · intro h
    refine ⟨h.toSeparates, ?_⟩
    by_contra hcon
    rw [not_or, not_lt, not_lt] at hcon
    refine h.not_subset fun x hx => ?_
    rcases hx with hx | hx
    · have h₁ : (c : EReal) ≤ (f x : EReal) := le_trans hcon.1 (iInf₂_le_coe_apply hx)
      exact le_antisymm (h.le_of_mem_left hx) (by exact_mod_cast h₁)
    · have h₂ : (f x : EReal) ≤ (c : EReal) := le_trans (coe_apply_le_iSup₂ hx) hcon.2
      exact le_antisymm (by exact_mod_cast h₂) (h.le_of_mem_right hx)
  · rintro ⟨h, hlt⟩
    refine ⟨h, fun hsub => ?_⟩
    rcases hlt with hlt | hlt
    · simp only [iInf_lt_iff] at hlt
      obtain ⟨x, hx, hlt⟩ := hlt
      have hfx : f x = c := hsub (Or.inl hx)
      rw [hfx] at hlt
      exact lt_irrefl _ hlt
    · simp only [lt_iSup_iff] at hlt
      obtain ⟨x, hx, hlt⟩ := hlt
      have hfx : f x = c := hsub (Or.inr hx)
      rw [hfx] at hlt
      exact lt_irrefl _ hlt

/-- Two nonempty sets are properly separated by some hyperplane orthogonal to `f` exactly when `f`
never exceeds on `s` what it attains on `t`, and is not constant with one and the same value on
both. -/
theorem exists_separatesProperly_iff_iSup_le_iInf (hs : s.Nonempty) (ht : t.Nonempty) :
    (∃ c, SeparatesProperly f c s t) ↔
      (⨆ x ∈ s, (f x : EReal)) ≤ ⨅ x ∈ t, (f x : EReal) ∧
        (⨅ x ∈ s, (f x : EReal)) < ⨆ x ∈ t, (f x : EReal) := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨h₁, h₂⟩ := separates_iff_iSup_le_iInf.1 hc.toSeparates
    refine ⟨h₁.trans h₂, ?_⟩
    rcases (separatesProperly_iff_iInf_lt_or_lt_iSup.1 hc).2 with hlt | hlt
    · exact hlt.trans_le (h₂.trans (iInf₂_le_iSup₂_of_nonempty ht))
    · exact lt_of_le_of_lt ((iInf₂_le_iSup₂_of_nonempty hs).trans h₁) hlt
  · rintro ⟨h₁, h₂⟩
    obtain ⟨a, ha⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
      (bot_lt_iSup₂_of_nonempty (f := f) hs).ne' (lt_of_le_of_lt h₁ (iInf₂_lt_top_of_nonempty ht))
    refine ⟨a, separatesProperly_iff_iInf_lt_or_lt_iSup.2
      ⟨separates_iff_iSup_le_iInf.2 ⟨ha.le, ha ▸ h₁⟩, ?_⟩⟩
    rcases lt_or_ge (⨅ x ∈ s, (f x : EReal)) (a : EReal) with hlt | hge
    · exact Or.inl hlt
    · have hEq : (⨅ x ∈ s, (f x : EReal)) = (a : EReal) :=
        le_antisymm ((iInf₂_le_iSup₂_of_nonempty hs).trans ha.le) hge
      exact Or.inr (hEq ▸ h₂)

/-- Strong separation by *some* hyperplane orthogonal to `f` is exactly a gap between the two
extrema. No nonemptiness is needed here: for empty sets the extrema are `⊥` and `⊤`. -/
theorem exists_separatesStrongly_iff_iSup_lt_iInf :
    (∃ c, SeparatesStrongly f c s t) ↔ (⨆ x ∈ s, (f x : EReal)) < ⨅ x ∈ t, (f x : EReal) := by
  constructor
  · rintro ⟨c, hc⟩
    exact hc.iSup_lt.trans hc.lt_iInf
  · intro h
    obtain ⟨c, h₁, h₂⟩ := EReal.lt_iff_exists_real_btwn.1 h
    exact ⟨c, h₁, h₂⟩

/-- Strong separation is separation. -/
theorem SeparatesStrongly.separates (h : SeparatesStrongly f c s t) : Separates f c s t :=
  separates_iff_iSup_le_iInf.2 ⟨h.iSup_lt.le, h.lt_iInf.le⟩

/-- On `s`, a strongly separating functional stays strictly below the level. -/
theorem SeparatesStrongly.lt_of_mem_left (h : SeparatesStrongly f c s t) {x : E} (hx : x ∈ s) :
    f x < c := by
  exact_mod_cast (coe_apply_le_iSup₂ hx).trans_lt h.iSup_lt

/-- On `t`, a strongly separating functional stays strictly above the level. -/
theorem SeparatesStrongly.lt_of_mem_right (h : SeparatesStrongly f c s t) {x : E} (hx : x ∈ t) :
    c < f x := by
  exact_mod_cast h.lt_iInf.trans_le (iInf₂_le_coe_apply hx)

/-- **Strong separation as a uniform gap.** This is the form of Rockafellar's condition (c) that
proofs actually consume. -/
theorem separatesStrongly_iff_exists_gap :
    SeparatesStrongly f c s t ↔
      ∃ δ > 0, (∀ x ∈ s, f x ≤ c - δ) ∧ ∀ x ∈ t, c + δ ≤ f x := by
  constructor
  · intro h
    obtain ⟨p, hp₁, hp₂⟩ := EReal.lt_iff_exists_real_btwn.1 h.iSup_lt
    obtain ⟨q, hq₁, hq₂⟩ := EReal.lt_iff_exists_real_btwn.1 h.lt_iInf
    have hp : p < c := by exact_mod_cast hp₂
    have hq : c < q := by exact_mod_cast hq₁
    refine ⟨min (c - p) (q - c), lt_min (by linarith) (by linarith), fun x hx => ?_,
      fun x hx => ?_⟩
    · have hxp : (f x : EReal) ≤ (p : EReal) := le_trans (coe_apply_le_iSup₂ hx) hp₁.le
      have hxp' : f x ≤ p := by exact_mod_cast hxp
      have hmin : min (c - p) (q - c) ≤ c - p := min_le_left _ _
      linarith
    · have hxq : (q : EReal) ≤ (f x : EReal) := le_trans hq₂.le (iInf₂_le_coe_apply hx)
      have hxq' : q ≤ f x := by exact_mod_cast hxq
      have hmin : min (c - p) (q - c) ≤ q - c := min_le_right _ _
      linarith
  · rintro ⟨δ, hδ, h₁, h₂⟩
    constructor
    · refine lt_of_le_of_lt (iSup₂_le fun x hx => ?_)
        (show ((c - δ : ℝ) : EReal) < (c : EReal) by exact_mod_cast (by linarith : c - δ < c))
      exact_mod_cast h₁ x hx
    · refine lt_of_lt_of_le
        (show (c : EReal) < ((c + δ : ℝ) : EReal) by exact_mod_cast (by linarith : c < c + δ))
        (le_iInf₂ fun x hx => ?_)
      exact_mod_cast h₂ x hx

/-- The workhorse constructor for strong separation out of Mathlib's separation theorems, which
produce two levels `u < v` with `f < u` on `s` and `v < f` on `t`. -/
theorem separatesStrongly_of_forall_lt {u v : ℝ} (hs : ∀ x ∈ s, f x < u) (huv : u < v)
    (ht : ∀ x ∈ t, v < f x) : SeparatesStrongly f ((u + v) / 2) s t :=
  separatesStrongly_iff_exists_gap.2
    ⟨(v - u) / 2, by linarith, fun x hx => by have := hs x hx; linarith,
      fun x hx => by have := ht x hx; linarith⟩

/-- A strongly separating functional is nonzero, provided both sets are nonempty. -/
theorem SeparatesStrongly.ne_zero (h : SeparatesStrongly f c s t) (hs : s.Nonempty)
    (ht : t.Nonempty) : f ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx⟩ := hs
  obtain ⟨y, hy⟩ := ht
  have h₁ : c < (0 : ℝ) := by simpa using h.lt_of_mem_right hy
  have h₂ : (0 : ℝ) < c := by simpa using h.lt_of_mem_left hx
  linarith

/-- Strong separation is symmetric under exchanging the two sets and negating the functional. -/
theorem SeparatesStrongly.symm (h : SeparatesStrongly f c s t) :
    SeparatesStrongly (-f) (-c) t s := by
  obtain ⟨δ, hδ, h₁, h₂⟩ := separatesStrongly_iff_exists_gap.1 h
  refine separatesStrongly_iff_exists_gap.2 ⟨δ, hδ, fun x hx => ?_, fun x hx => ?_⟩
  · have := h₂ x hx
    simpa using (by linarith : -f x ≤ -c - δ)
  · have := h₁ x hx
    simpa using (by linarith : -c + δ ≤ -f x)

/-- Strong separation is proper, provided at least one of the two sets is nonempty. -/
theorem SeparatesStrongly.separatesProperly (h : SeparatesStrongly f c s t)
    (hst : (s ∪ t).Nonempty) : SeparatesProperly f c s t where
  toSeparates := h.separates
  not_subset hsub := by
    obtain ⟨x, hx⟩ := hst
    have hfx : f x = c := hsub hx
    rcases hx with hx | hx
    · exact absurd hfx (h.lt_of_mem_left hx).ne
    · exact absurd hfx (h.lt_of_mem_right hx).ne'

end Extrema

/-! ### Strong separation by a neighbourhood of the origin -/

section TopologicalVectorSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {f : E →L[ℝ] ℝ} {c : ℝ} {s t : Set E}

omit [IsTopologicalAddGroup E] in
/-- A nonzero continuous linear functional is strictly positive somewhere on every neighbourhood of
the origin. This is the substitute, in a space with no norm, for "`|⟨y, b⟩| < δ` for `y` small
enough". -/
theorem exists_mem_pos_of_ne_zero (hf : f ≠ 0) {V : Set E} (hV : V ∈ 𝓝 (0 : E)) :
    ∃ v ∈ V, 0 < f v := by
  obtain ⟨z, hz⟩ : ∃ z, 0 < f z := by
    by_contra hcon
    refine hf (ContinuousLinearMap.ext fun x => ?_)
    have h₁ : f x ≤ 0 := not_lt.1 fun h => hcon ⟨x, h⟩
    have h₂ : f (-x) ≤ 0 := not_lt.1 fun h => hcon ⟨-x, h⟩
    rw [map_neg, neg_nonpos] at h₂
    simpa using le_antisymm h₁ h₂
  have hmem : {a : ℝ | a • z ∈ V} ∈ 𝓝 (0 : ℝ) := by
    have hcont : Continuous fun a : ℝ => a • z := continuous_id.smul continuous_const
    have htend : Tendsto (fun a : ℝ => a • z) (𝓝 0) (𝓝 (0 : E)) := by
      simpa using hcont.tendsto (0 : ℝ)
    exact htend hV
  have hmem' : {a : ℝ | a • z ∈ V} ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds hmem
  obtain ⟨a, haV, ha⟩ :=
    Filter.nonempty_of_mem (Filter.inter_mem hmem' self_mem_nhdsWithin)
  exact ⟨a • z, haV, by rw [map_smul, smul_eq_mul]; exact mul_pos ha hz⟩

omit [IsTopologicalAddGroup E] in
/-- A continuous linear functional that is nonpositive on a neighbourhood of the origin is zero. -/
theorem eq_zero_of_forall_le_zero {V : Set E} (hV : V ∈ 𝓝 (0 : E)) (h : ∀ v ∈ V, f v ≤ 0) :
    f = 0 := by
  by_contra hf
  obtain ⟨v, hvV, hv⟩ := exists_mem_pos_of_ne_zero hf hV
  exact absurd (h v hvV) (not_le.2 hv)

/-- A continuous linear functional attaining its maximum over a set at an *interior* point of that
set is zero. This is what makes a supporting hyperplane at an interior point impossible. -/
theorem eq_zero_of_mem_interior_of_isMaxOn {C : Set E} {x : E} (hx : x ∈ interior C)
    (hfx : f x = c) (h : ∀ y ∈ C, f y ≤ c) : f = 0 := by
  refine eq_zero_of_forall_le_zero (V := (fun v => x + v) ⁻¹' C) ?_ fun v hv => ?_
  · refine ContinuousAt.preimage_mem_nhds (by fun_prop) ?_
    rw [add_zero]
    exact mem_interior_iff_mem_nhds.1 hx
  · have hmem := h _ hv
    rw [map_add, hfx] at hmem
    linarith

omit [IsTopologicalAddGroup E] in
/-- **Strong separation by a neighbourhood of the origin**: the phrasing of Rockafellar's
definition that survives the loss of a norm. `s + V` and `t + V` lie in opposite *open* half-spaces
for some neighbourhood `V` of the origin. -/
theorem separatesStrongly_iff_exists_nhds :
    SeparatesStrongly f c s t ↔
      ∃ V ∈ 𝓝 (0 : E), (∀ x ∈ s + V, f x < c) ∧ ∀ x ∈ t + V, c < f x := by
  constructor
  · intro h
    obtain ⟨δ, hδ, h₁, h₂⟩ := separatesStrongly_iff_exists_gap.1 h
    refine ⟨f ⁻¹' Ioo (-δ) δ, ?_, ?_, ?_⟩
    · refine f.continuous.continuousAt.preimage_mem_nhds ?_
      simpa using Ioo_mem_nhds (by linarith : -δ < (0 : ℝ)) hδ
    · rintro _ ⟨x, hx, v, hv, rfl⟩
      have hxs := h₁ x hx
      have hv' : f v < δ := hv.2
      rw [map_add]
      linarith
    · rintro _ ⟨x, hx, v, hv, rfl⟩
      have hxt := h₂ x hx
      have hv' : -δ < f v := hv.1
      rw [map_add]
      linarith
  · rintro ⟨V, hV, h₁, h₂⟩
    by_cases hf : f = 0
    · subst hf
      have hs0 : ∀ x ∈ s, (0 : ℝ) < c := fun x hx => by
        simpa using h₁ (x + 0) (Set.add_mem_add hx (mem_of_mem_nhds hV))
      have ht0 : ∀ x ∈ t, c < (0 : ℝ) := fun x hx => by
        simpa using h₂ (x + 0) (Set.add_mem_add hx (mem_of_mem_nhds hV))
      rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · rcases t.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
        · exact separatesStrongly_iff_exists_gap.2 ⟨1, one_pos, by simp, by simp⟩
        · have hc := ht0 y hy
          refine separatesStrongly_iff_exists_gap.2 ⟨-c / 2, by linarith, by simp, fun z hz => ?_⟩
          have := ht0 z hz
          simpa using (by linarith : c + -c / 2 ≤ (0 : ℝ))
      · rcases t.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
        · have hc := hs0 x hx
          refine separatesStrongly_iff_exists_gap.2 ⟨c / 2, by linarith, fun z hz => ?_, by simp⟩
          have := hs0 z hz
          simpa using (by linarith : (0 : ℝ) ≤ c - c / 2)
        · exact absurd (hs0 x hx) (not_lt.2 (ht0 y hy).le)
    · obtain ⟨v, hvV, hv⟩ := exists_mem_pos_of_ne_zero hf hV
      obtain ⟨w, hwV, hw'⟩ := exists_mem_pos_of_ne_zero (f := -f) (neg_ne_zero.2 hf) hV
      have hw : f w < 0 := by simpa using hw'
      refine separatesStrongly_iff_exists_gap.2 ⟨min (f v) (-f w), lt_min hv (by linarith),
        fun x hx => ?_, fun x hx => ?_⟩
      · have hxv := h₁ (x + v) (Set.add_mem_add hx hvV)
        rw [map_add] at hxv
        have hmin : min (f v) (-f w) ≤ f v := min_le_left _ _
        linarith
      · have hxw := h₂ (x + w) (Set.add_mem_add hx hwV)
        rw [map_add] at hxw
        have hmin : min (f v) (-f w) ≤ -f w := min_le_right _ _
        linarith

/-! ### A hyperplane through a disjoint affine set -/

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- A continuous linear functional bounded below on an affine set is constant on it: along a
direction in which `f` decreases, an affine set is unbounded below for `f`. -/
theorem eq_of_le_on_affineSubspace {M : AffineSubspace ℝ E} {u : ℝ} (h : ∀ x ∈ M, u ≤ f x)
    {p q : E} (hp : p ∈ M) (hq : q ∈ M) : f p = f q := by
  have hd : q - p ∈ M.direction := by
    simpa using AffineSubspace.vsub_mem_direction hq hp
  have hmem : ∀ a : ℝ, a • (q - p) + p ∈ M := fun a => by
    simpa using AffineSubspace.vadd_mem_of_mem_direction (M.direction.smul_mem a hd) hp
  have key : ∀ a : ℝ, u ≤ a * (f q - f p) + f p := fun a => by
    have hm := h _ (hmem a)
    rwa [map_add, map_smul, map_sub, smul_eq_mul] at hm
  have hzero : f q - f p = 0 := by
    by_contra hne
    have hkey := key ((u - f p - 1) / (f q - f p))
    rw [div_mul_cancel₀ _ hne] at hkey
    linarith
  linarith [sub_eq_zero.1 hzero]

/-- **An open convex set and a disjoint affine set can be separated** by a hyperplane containing
the affine set, with the convex set inside one of the *open* half-spaces. Rockafellar's hypothesis
is that `C` be *relatively* open, which in `ℝⁿ` covers every nonempty convex set through `ri C`;
outside finite dimensions the relative interior is not available and openness is the right
hypothesis. The relatively open version is `exists_lt_of_notMem_relint`. -/
theorem exists_separates_of_isOpen_of_disjoint_affine {C : Set E} {M : AffineSubspace ℝ E}
    (hC₁ : Convex ℝ C) (hC₂ : IsOpen C) (hC₃ : C.Nonempty) {p : E} (hp : p ∈ M)
    (hdisj : Disjoint C (M : Set E)) :
    ∃ g : E →L[ℝ] ℝ, g ≠ 0 ∧ (∀ x ∈ M, g x = g p) ∧ ∀ x ∈ C, g x < g p := by
  obtain ⟨g, u, hgC, hgM⟩ := geometric_hahn_banach_open hC₁ hC₂ M.convex hdisj
  have hconst : ∀ x ∈ M, g x = g p := fun x hx =>
    eq_of_le_on_affineSubspace (fun y hy => hgM y hy) hx hp
  have hup : u ≤ g p := hgM p hp
  refine ⟨g, ?_, hconst, fun x hx => lt_of_lt_of_le (hgC x hx) hup⟩
  rintro rfl
  obtain ⟨x, hx⟩ := hC₃
  have h₁ : (0 : ℝ) < u := by simpa using hgC x hx
  have h₂ : u ≤ (0 : ℝ) := by simpa using hup
  linarith

/-- The same in the vocabulary of this file: an open convex set and a disjoint affine set are
separated properly, by a hyperplane containing the affine set. -/
theorem exists_separatesProperly_of_isOpen_of_disjoint_affine {C : Set E}
    {M : AffineSubspace ℝ E} (hC₁ : Convex ℝ C) (hC₂ : IsOpen C) (hC₃ : C.Nonempty) {p : E}
    (hp : p ∈ M) (hdisj : Disjoint C (M : Set E)) :
    ∃ (g : E →L[ℝ] ℝ) (b : ℝ), SeparatesProperly g b C (M : Set E) := by
  obtain ⟨g, -, hM, hC⟩ :=
    exists_separates_of_isOpen_of_disjoint_affine hC₁ hC₂ hC₃ hp hdisj
  obtain ⟨x, hx⟩ := hC₃
  exact ⟨g, g p, ⟨fun y hy => (hC y hy).le, fun y hy => (hM y hy).ge⟩,
    fun hsub => absurd (hsub (Or.inl hx)) (hC x hx).ne⟩

/-! ### Supporting hyperplanes and half-spaces -/

/-- `IsSupporting f c s` : the closed half-space `{x | f x ≤ c}` is a *supporting half-space* to
`s`, and its boundary `{x | f x = c}` a *supporting hyperplane* — a closed half-space containing
`s` with a point of `s` in its boundary, `f ≠ 0` making the boundary a hyperplane rather than the
whole space. A supporting hyperplane is *non-trivial* when `∃ x ∈ s, f x ≠ c`, written inline. -/
structure IsSupporting (f : E →L[ℝ] ℝ) (c : ℝ) (s : Set E) : Prop where
  /-- A supporting hyperplane is a genuine hyperplane. -/
  ne_zero : f ≠ 0
  /-- The half-space contains `s`. -/
  le_of_mem : ∀ ⦃x⦄, x ∈ s → f x ≤ c
  /-- The hyperplane touches `s`. -/
  exists_eq : ∃ x ∈ s, f x = c

/-- A supporting hyperplane misses the interior of the set it supports. -/
theorem IsSupporting.disjoint_interior {C : Set E} (h : IsSupporting f c C) :
    Disjoint (interior C) {x | f x = c} := by
  rw [Set.disjoint_left]
  intro x hx hfx
  exact h.ne_zero (eq_zero_of_mem_interior_of_isMaxOn hx hfx fun y hy => h.le_of_mem hy)

/-- **A nonempty convex subset `D` of a convex set `C` with nonempty interior lies in a non-trivial
supporting hyperplane to `C` exactly when `D` misses the interior of `C`.** Rockafellar's statement
is about `ri C` and needs no interior hypothesis, because in `ℝⁿ` a nonempty convex set has
nonempty relative interior; outside finite dimensions that fails. The relative-interior
consequences are in `Numlib/Analysis/Convex/RelativeInterior.lean`. -/
theorem exists_isSupporting_iff_disjoint_interior {C D : Set E} (hC : Convex ℝ C)
    (hD : Convex ℝ D) (hDC : D ⊆ C) (hD' : D.Nonempty) (hCi : (interior C).Nonempty) :
    (∃ (g : E →L[ℝ] ℝ) (b : ℝ), IsSupporting g b C ∧ (∀ x ∈ D, g x = b) ∧ ∃ x ∈ C, g x ≠ b) ↔
      Disjoint (interior C) D := by
  constructor
  · rintro ⟨g, b, hsupp, hDb, -⟩
    rw [Set.disjoint_left]
    intro x hx hxD
    exact Set.disjoint_left.1 hsupp.disjoint_interior hx (hDb x hxD)
  · intro hdisj
    obtain ⟨g, b, hg0, hgC, hgD⟩ :=
      geometric_hahn_banach_of_nonempty_interior hC hD hdisj hCi hD'
    have hDb : ∀ x ∈ D, g x = b := fun x hx => le_antisymm (hgC x (hDC hx)) (hgD x hx)
    obtain ⟨x₀, hx₀⟩ := hD'
    refine ⟨g, b, ⟨hg0, fun x hx => hgC x hx, ⟨x₀, hDC hx₀, hDb x₀ hx₀⟩⟩, hDb, ?_⟩
    by_contra hcon
    obtain ⟨y, hy⟩ := hCi
    have hall : ∀ x ∈ C, g x = b := by
      intro x hx
      by_contra hne
      exact hcon ⟨x, hx, hne⟩
    exact hg0 (eq_zero_of_mem_interior_of_isMaxOn hy (hall y (interior_subset hy))
      fun z hz => (hall z hz).le)

end TopologicalVectorSpace

/-! ### Strong separation by `ε`-balls -/

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E →L[ℝ] ℝ} {c : ℝ}
  {s t : Set E}

/-- **Rockafellar's own definition of strong separation**, available once there is a norm: `s + εB`
and `t + εB` lie in opposite open half-spaces for some `ε > 0`. With
`separatesStrongly_iff_exists_nhds` this shows nothing is lost by taking the gap as the
definition. -/
theorem separatesStrongly_iff_exists_closedBall :
    SeparatesStrongly f c s t ↔
      ∃ ε > 0, (∀ x ∈ s + Metric.closedBall 0 ε, f x < c) ∧
        ∀ x ∈ t + Metric.closedBall 0 ε, c < f x := by
  rw [separatesStrongly_iff_exists_nhds]
  constructor
  · rintro ⟨V, hV, h₁, h₂⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
    have hsub : Metric.closedBall (0 : E) (ε / 2) ⊆ V := fun y hy => by
      refine hball ?_
      have : dist y 0 ≤ ε / 2 := hy
      simpa using lt_of_le_of_lt this (by linarith : ε / 2 < ε)
    exact ⟨ε / 2, by linarith, fun x hx => h₁ x (Set.add_subset_add_left hsub hx),
      fun x hx => h₂ x (Set.add_subset_add_left hsub hx)⟩
  · rintro ⟨ε, hε, h₁, h₂⟩
    exact ⟨Metric.closedBall 0 ε, Metric.closedBall_mem_nhds 0 hε, h₁, h₂⟩

end Normed

/-! ### Cones, and half-spaces through the origin -/

section Cone

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {f : E →L[ℝ] ℝ} {c : ℝ} {s t : Set E}

/-- The homogeneous closed half-space `{x | f x ≤ 0}`, bundled as a `PointedCone ℝ E`. The
*homogeneous* closed half-spaces — those with the origin on their boundary — are exactly these, and
bundling them makes `Submodule.span_le` available, which is what turns the cone representations
below into two lines. -/
def halfSpaceCone (f : E →L[ℝ] ℝ) : PointedCone ℝ E where
  carrier := {x | f x ≤ 0}
  add_mem' {x y} hx hy := by
    have hx' : f x ≤ 0 := hx
    have hy' : f y ≤ 0 := hy
    change f (x + y) ≤ 0
    rw [map_add]
    linarith
  zero_mem' := by simp
  smul_mem' a {x} hx := by
    have hx' : f x ≤ 0 := hx
    have ha : (0 : ℝ) ≤ (a : ℝ) := a.2
    change f ((a : ℝ) • x) ≤ 0
    rw [map_smul, smul_eq_mul]
    nlinarith

/-- Membership in the homogeneous half-space cone is the inequality defining it. -/
@[simp]
theorem mem_halfSpaceCone {x : E} : x ∈ halfSpaceCone f ↔ f x ≤ 0 := Iff.rfl

/-- The underlying set of `halfSpaceCone f` is the homogeneous half-space `{x | f x ≤ 0}`. -/
@[simp]
theorem coe_halfSpaceCone : (halfSpaceCone f : Set E) = {x | f x ≤ 0} := rfl

/-- A linear functional bounded above on a cone is nonpositive on it: otherwise scaling up a point
where it is positive breaks the bound. -/
theorem le_zero_of_isCone_of_forall_le {K : Set E} {u : ℝ}
    (hcone : ∀ ⦃a : ℝ⦄, 0 < a → ∀ ⦃x⦄, x ∈ K → a • x ∈ K) (h : ∀ x ∈ K, f x ≤ u) {x : E}
    (hx : x ∈ K) : f x ≤ 0 := by
  by_contra hcon
  rw [not_le] at hcon
  have hpos : (0 : ℝ) < max u 0 + 1 := by linarith [le_max_right u 0]
  have ha : 0 < (max u 0 + 1) / f x := div_pos hpos hcon
  have hk := h _ (hcone ha hx)
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hcon.ne'] at hk
  linarith [le_max_left u 0]

/-- A bound above for a linear functional on a nonempty cone is nonnegative: the functional comes
arbitrarily close to `0` along any ray of the cone. -/
theorem nonneg_of_isCone_of_forall_le {K : Set E} {u : ℝ}
    (hcone : ∀ ⦃a : ℝ⦄, 0 < a → ∀ ⦃x⦄, x ∈ K → a • x ∈ K) (h : ∀ x ∈ K, f x ≤ u)
    (hK : K.Nonempty) : 0 ≤ u := by
  obtain ⟨x, hx⟩ := hK
  by_contra hcon
  rw [not_le] at hcon
  have hfx : f x ≤ 0 := le_zero_of_isCone_of_forall_le hcone h hx
  rcases eq_or_lt_of_le hfx with heq | hlt
  · have := h x hx
    rw [heq] at this
    linarith
  · have hne : f x ≠ 0 := hlt.ne
    have ha : 0 < u / (2 * f x) := by
      rw [← neg_div_neg_eq]
      exact div_pos (by linarith) (by linarith)
    have hk := h _ (hcone ha hx)
    rw [map_smul, smul_eq_mul] at hk
    have hval : u / (2 * f x) * f x = u / 2 := by field_simp
    rw [hval] at hk
    linarith

/-- **If two nonempty sets are properly separated and the *first* is a cone, then they are properly
separated by a hyperplane through the origin.** Both sets must be nonempty: on the line, the cone
`{0}` and the empty set are properly separated at level `1` but not at level `0`. -/
theorem SeparatesProperly.zero_of_isCone_left (h : SeparatesProperly f c s t)
    (hcone : ∀ ⦃a : ℝ⦄, 0 < a → ∀ ⦃x⦄, x ∈ s → a • x ∈ s) (hs : s.Nonempty) (ht : t.Nonempty) :
    SeparatesProperly f 0 s t := by
  have hbdd : ∀ x ∈ s, f x ≤ c := fun x hx => h.le_of_mem_left hx
  have hle : ∀ x ∈ s, f x ≤ 0 := fun x hx => le_zero_of_isCone_of_forall_le hcone hbdd hx
  have hc : 0 ≤ c := nonneg_of_isCone_of_forall_le hcone hbdd hs
  refine ⟨⟨fun x hx => hle x hx, fun x hx => le_trans hc (h.le_of_mem_right hx)⟩, fun hsub => ?_⟩
  obtain ⟨y, hy⟩ := ht
  have hy0 : f y = 0 := hsub (Or.inr hy)
  have hcle : c ≤ 0 := hy0 ▸ h.le_of_mem_right hy
  have hc0 : c = 0 := le_antisymm hcle hc
  exact h.not_subset (by rw [hc0]; exact hsub)

/-- The same with the cone on the right. -/
theorem SeparatesProperly.zero_of_isCone_right (h : SeparatesProperly f c s t)
    (hcone : ∀ ⦃a : ℝ⦄, 0 < a → ∀ ⦃x⦄, x ∈ t → a • x ∈ t) (hs : s.Nonempty) (ht : t.Nonempty) :
    SeparatesProperly f 0 s t := by
  have h' := (h.symm.zero_of_isCone_left hcone ht hs).symm
  simpa using h'

end Cone

/-! ### Strong separation, half-space representations, and separation from a point -/

section LocallyConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] {s t : Set E}

/-- **Two convex sets can be separated strongly exactly when the origin is not in the closure of
their difference** — in a normed space, exactly when the distance between them is positive.
Rockafellar assumes both sets nonempty; that is not needed, the empty set being strongly separated
from anything by the zero functional. -/
theorem separatesStrongly_iff_zero_notMem_closure_sub (hs : Convex ℝ s) (ht : Convex ℝ t) :
    (∃ (f : E →L[ℝ] ℝ) (c : ℝ), SeparatesStrongly f c s t) ↔ (0 : E) ∉ closure (s - t) := by
  constructor
  · rintro ⟨f, c, hsep⟩ h0
    obtain ⟨δ, hδ, h₁, h₂⟩ := separatesStrongly_iff_exists_gap.1 hsep
    have hclosed : IsClosed {x : E | f x ≤ -(2 * δ)} := isClosed_le f.continuous continuous_const
    have hsub : s - t ⊆ {x : E | f x ≤ -(2 * δ)} := by
      rintro _ ⟨x, hx, y, hy, rfl⟩
      have hx' := h₁ x hx
      have hy' := h₂ y hy
      have hxy : f (x - y) = f x - f y := map_sub f x y
      have : f (x - y) ≤ -(2 * δ) := by linarith
      exact this
    have hzero : f 0 ≤ -(2 * δ) := closure_minimal hsub hclosed h0
    rw [map_zero] at hzero
    linarith
  · intro h0
    rcases s.eq_empty_or_nonempty with rfl | hs'
    · exact ⟨0, -1, separatesStrongly_iff_exists_gap.2 ⟨1, one_pos, by simp, by simp⟩⟩
    rcases t.eq_empty_or_nonempty with rfl | ht'
    · exact ⟨0, 1, separatesStrongly_iff_exists_gap.2 ⟨1, one_pos, by simp, by simp⟩⟩
    obtain ⟨f, u, hlt, hu⟩ :=
      geometric_hahn_banach_closed_point (hs.sub ht).closure isClosed_closure h0
    rw [map_zero] at hu
    have hpair : ∀ x ∈ s, ∀ y ∈ t, f x - f y < u := by
      intro x hx y hy
      have hmem := hlt _ (subset_closure (Set.sub_mem_sub hx hy))
      rwa [map_sub] at hmem
    obtain ⟨x₀, hx₀⟩ := hs'
    have hbdd : BddBelow (f '' t) := by
      refine ⟨f x₀ - u, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      have := hpair x₀ hx₀ y hy
      linarith
    have hle : ∀ y ∈ t, sInf (f '' t) ≤ f y := fun y hy =>
      csInf_le hbdd (Set.mem_image_of_mem f hy)
    have hge : ∀ x ∈ s, f x - u ≤ sInf (f '' t) := by
      intro x hx
      refine le_csInf (ht'.image f) ?_
      rintro _ ⟨y, hy, rfl⟩
      have := hpair x hx y hy
      linarith
    refine ⟨f, sInf (f '' t) + u / 2, separatesStrongly_iff_exists_gap.2
      ⟨-u / 2, by linarith, fun x hx => ?_, fun y hy => ?_⟩⟩
    · have := hge x hx
      linarith
    · have := hle y hy
      linarith

/-- **A compact convex set and a disjoint closed convex set can be separated strongly.** The book
deduces this from a criterion phrased with recession cones, which is not available yet; the proof
here goes through Mathlib's compact/closed geometric Hahn–Banach theorem. -/
theorem separatesStrongly_of_disjoint_isCompact_isClosed (hs₁ : Convex ℝ s) (hs₂ : IsCompact s)
    (ht₁ : Convex ℝ t) (ht₂ : IsClosed t) (hd : Disjoint s t) :
    ∃ (f : E →L[ℝ] ℝ) (c : ℝ), SeparatesStrongly f c s t := by
  obtain ⟨f, u, v, h₁, huv, h₂⟩ := geometric_hahn_banach_compact_closed hs₁ hs₂ ht₁ ht₂ hd
  exact ⟨f, (u + v) / 2, separatesStrongly_of_forall_lt h₁ huv h₂⟩

/-- The other order: a closed convex set and a disjoint compact convex set can be separated
strongly. -/
theorem separatesStrongly_of_disjoint_isClosed_isCompact (hs₁ : Convex ℝ s) (hs₂ : IsClosed s)
    (ht₁ : Convex ℝ t) (ht₂ : IsCompact t) (hd : Disjoint s t) :
    ∃ (f : E →L[ℝ] ℝ) (c : ℝ), SeparatesStrongly f c s t := by
  obtain ⟨f, u, v, h₁, huv, h₂⟩ := geometric_hahn_banach_closed_compact hs₁ hs₂ ht₁ ht₂ hd
  exact ⟨f, (u + v) / 2, separatesStrongly_of_forall_lt h₁ huv h₂⟩

/-- **Separation of a point from a closed convex set**, in the form the conjugacy module consumes:
a point outside a closed convex set is separated from it *strongly*. This is the workhorse instance
of the compact/closed case, and the only separation the **Fenchel–Moreau theorem** needs. -/
theorem exists_separating_of_notMem_closed_convex (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) {x : E}
    (hx : x ∉ s) : ∃ (f : E →L[ℝ] ℝ) (c : ℝ), SeparatesStrongly f c s {x} :=
  separatesStrongly_of_disjoint_isClosed_isCompact hs₁ hs₂ (convex_singleton x)
    isCompact_singleton (Set.disjoint_singleton_right.2 hx)

/-- **A point belongs to a closed convex set as soon as it satisfies every weak linear inequality
that the set satisfies.** -/
theorem mem_iff_forall_le_halfSpace (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) {x : E} :
    x ∈ s ↔ ∀ (f : E →L[ℝ] ℝ) (c : ℝ), (∀ y ∈ s, f y ≤ c) → f x ≤ c := by
  refine ⟨fun hx f c hf => hf x hx, fun h => ?_⟩
  by_contra hx
  obtain ⟨f, c, hfs, hfx⟩ := geometric_hahn_banach_closed_point hs₁ hs₂ hx
  exact absurd (h f c fun y hy => (hfs y hy).le) (not_le.2 hfx)

/-- **A closed convex set is the intersection of the closed half-spaces containing it.** -/
theorem isClosed_convex_eq_iInter_halfspaces (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) :
    ⋂ (f : E →L[ℝ] ℝ) (c : ℝ) (_ : ∀ y ∈ s, f y ≤ c), {x | f x ≤ c} = s := by
  ext x
  simp only [Set.mem_iInter, Set.mem_ofPred]
  exact (mem_iff_forall_le_halfSpace hs₁ hs₂).symm

/-- The closed convex hull of an arbitrary set is the intersection of the closed half-spaces
containing that set. -/
theorem closure_convexHull_eq_iInter_halfspaces (s : Set E) :
    ⋂ (f : E →L[ℝ] ℝ) (c : ℝ) (_ : ∀ y ∈ s, f y ≤ c), {x | f x ≤ c} =
      closure (convexHull ℝ s) := by
  have hkey : ∀ (f : E →L[ℝ] ℝ) (c : ℝ),
      (∀ y ∈ s, f y ≤ c) ↔ ∀ y ∈ closure (convexHull ℝ s), f y ≤ c := by
    refine fun f c => ⟨fun h y hy => ?_, fun h y hy =>
      h y (subset_closure (subset_convexHull ℝ s hy))⟩
    exact closure_minimal (convexHull_min h (convex_halfSpace_le f.toLinearMap.isLinear c))
      (isClosed_le f.continuous continuous_const) hy
  rw [← isClosed_convex_eq_iInter_halfspaces (convex_convexHull ℝ s).closure isClosed_closure]
  ext x
  simp only [Set.mem_iInter, Set.mem_ofPred]
  exact forall₂_congr fun f c => imp_congr_left (hkey f c)

/-- **A nonempty convex set whose closure is not everything lies in a closed half-space**, the
statement corrected for infinite dimensions. The book's hypothesis is `C ≠ ℝⁿ`, enough there
because `ri (cl C) ⊆ C`, but not here: the kernel of a discontinuous linear functional is a proper
convex subset which is dense, and no nonzero continuous functional is bounded above on it. -/
theorem exists_ne_zero_forall_le_of_closure_ne_univ (hs₁ : Convex ℝ s) (hs₂ : s.Nonempty)
    (h : closure s ≠ univ) : ∃ (f : E →L[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ ∀ x ∈ s, f x ≤ c := by
  obtain ⟨a, ha⟩ := nonempty_compl.2 h
  obtain ⟨f, c, hfs, hfa⟩ := geometric_hahn_banach_closed_point hs₁.closure isClosed_closure ha
  refine ⟨f, c, ?_, fun x hx => (hfs x (subset_closure hx)).le⟩
  rintro rfl
  obtain ⟨x, hx⟩ := hs₂
  have h₁ : (0 : ℝ) < c := by simpa using hfs x (subset_closure hx)
  have h₂ : c < (0 : ℝ) := by simpa using hfa
  linarith

/-! ### Corollaries 11.7.1 to 11.7.3 -/

omit [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] in
/-- The closure of a cone is a cone. -/
theorem smul_mem_closure_of_isCone {K : Set E}
    (hcone : ∀ ⦃a : ℝ⦄, 0 < a → ∀ ⦃x⦄, x ∈ K → a • x ∈ K) :
    ∀ ⦃a : ℝ⦄, 0 < a → ∀ ⦃x⦄, x ∈ closure K → a • x ∈ closure K := by
  intro a ha x hx
  have hmaps : MapsTo (fun y : E => a • y) K (closure K) := fun y hy =>
    subset_closure (hcone ha hy)
  have hcl := hmaps.closure (continuous_const.smul continuous_id) hx
  rwa [closure_closure] at hcl

/-- A nonempty closed convex cone is the intersection of the homogeneous closed half-spaces
containing it. -/
theorem isClosed_convex_isCone_eq_iInter_halfSpaceCone {K : Set E} (hconv : Convex ℝ K)
    (hcone : ∀ ⦃a : ℝ⦄, 0 < a → ∀ ⦃x⦄, x ∈ K → a • x ∈ K) (hcl : IsClosed K) (hne : K.Nonempty) :
    ⋂ (f : E →L[ℝ] ℝ) (_ : ∀ y ∈ K, f y ≤ 0), (halfSpaceCone f : Set E) = K := by
  ext x
  simp only [Set.mem_iInter, coe_halfSpaceCone, Set.mem_ofPred]
  refine ⟨fun h => ?_, fun hx f hf => hf x hx⟩
  by_contra hx
  obtain ⟨f, u, hfK, hfx⟩ := geometric_hahn_banach_closed_point hconv hcl hx
  have hle : ∀ y ∈ K, f y ≤ 0 := fun y hy =>
    le_zero_of_isCone_of_forall_le hcone (fun z hz => (hfK z hz).le) hy
  have hu : 0 ≤ u := nonneg_of_isCone_of_forall_le hcone (fun z hz => (hfK z hz).le) hne
  exact absurd (h f hle) (not_le.2 (lt_of_le_of_lt hu hfx))

/-- For an arbitrary set `S`, the closure of the convex cone generated by `S` is the intersection
of the homogeneous closed half-spaces containing `S`. -/
theorem closure_hull_eq_iInter_halfSpaceCone (S : Set E) :
    ⋂ (f : E →L[ℝ] ℝ) (_ : ∀ y ∈ S, f y ≤ 0), (halfSpaceCone f : Set E) =
      closure (PointedCone.hull ℝ S : Set E) := by
  have hkey : ∀ f : E →L[ℝ] ℝ,
      (∀ y ∈ S, f y ≤ 0) ↔ ∀ y ∈ closure (PointedCone.hull ℝ S : Set E), f y ≤ 0 := by
    refine fun f => ⟨fun h y hy => ?_, fun h y hy =>
      h y (subset_closure (PointedCone.subset_hull hy))⟩
    have hspan : (PointedCone.hull ℝ S : Set E) ⊆ (halfSpaceCone f : Set E) :=
      Submodule.span_le.2 h
    exact closure_minimal hspan (isClosed_le f.continuous continuous_const) hy
  rw [← isClosed_convex_isCone_eq_iInter_halfSpaceCone
    (PointedCone.convex (PointedCone.hull ℝ S)).closure
    (smul_mem_closure_of_isCone fun a ha x hx => (PointedCone.hull ℝ S).smul_mem ha.le hx)
    isClosed_closure ⟨0, subset_closure (PointedCone.hull ℝ S).zero_mem⟩]
  exact iInter_congr fun f => by rw [hkey f]

/-- A nonempty convex cone whose closure is not everything is contained in a homogeneous closed
half-space, corrected for infinite dimensions exactly as
`exists_ne_zero_forall_le_of_closure_ne_univ` is. -/
theorem exists_ne_zero_forall_le_zero_of_closure_ne_univ {K : Set E} (hconv : Convex ℝ K)
    (hcone : ∀ ⦃a : ℝ⦄, 0 < a → ∀ ⦃x⦄, x ∈ K → a • x ∈ K) (hne : K.Nonempty)
    (h : closure K ≠ univ) : ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ ∀ x ∈ K, f x ≤ 0 := by
  obtain ⟨a, ha⟩ := nonempty_compl.2 h
  obtain ⟨f, u, hfK, hfa⟩ := geometric_hahn_banach_closed_point hconv.closure isClosed_closure ha
  have hbdd : ∀ z ∈ K, f z ≤ u := fun z hz => (hfK z (subset_closure hz)).le
  have hle : ∀ y ∈ K, f y ≤ 0 := fun y hy => le_zero_of_isCone_of_forall_le hcone hbdd hy
  have hu : 0 ≤ u := nonneg_of_isCone_of_forall_le hcone hbdd hne
  refine ⟨f, ?_, hle⟩
  rintro rfl
  have : u < 0 := by simpa using hfa
  linarith

/-! ### The `E × ℝ` specialisation: non-vertical separation of an epigraph -/

/-- **Separation in `E × ℝ` by a non-vertical functional.** If `(x₀, μ) ∉ F` while `(x₀, ν) ∈ F` for
some `ν > μ`, the functional separating `(x₀, μ)` from the closed convex set `F` cannot be
*vertical*: a functional of the form `(y, 0)` takes the same value at `(x₀, μ)` and at `(x₀, ν)`.
Normalising the vertical component to `-1` turns it into a continuous affine function of `E` that
stays strictly below `F` and strictly above `μ` at `x₀`. -/
theorem exists_affine_lt_of_notMem {F : Set (E × ℝ)} (hF₁ : Convex ℝ F) (hF₂ : IsClosed F)
    {x₀ : E} {μ ν : ℝ} (hμν : μ < ν) (hν : (x₀, ν) ∈ F) (hμ : (x₀, μ) ∉ F) :
    ∃ (y : E →L[ℝ] ℝ) (b : ℝ), (∀ (x : E) (r : ℝ), (x, r) ∈ F → y x - b < r) ∧ μ < y x₀ - b := by
  obtain ⟨L, u, hLF, hLx⟩ := geometric_hahn_banach_closed_point hF₁ hF₂ hμ
  have hL : ∀ (x : E) (r : ℝ), L (x, r) = L (x, 0) + r * L (0, 1) := by
    intro x r
    have hsplit : ((x, r) : E × ℝ) = (x, 0) + r • ((0 : E), (1 : ℝ)) := by simp
    rw [hsplit, map_add, map_smul, smul_eq_mul]
  have hA := hLF _ hν
  rw [hL] at hA hLx
  have hd : L ((0 : E), (1 : ℝ)) < 0 := by
    by_contra hcon
    have h0 : 0 ≤ L ((0 : E), (1 : ℝ)) := not_lt.1 hcon
    nlinarith [mul_nonneg (sub_nonneg.2 hμν.le) h0]
  set k : ℝ := -L ((0 : E), (1 : ℝ)) with hk_def
  have hk : 0 < k := by simpa [hk_def] using hd
  have hdk : L ((0 : E), (1 : ℝ)) = -k := by simp [hk_def]
  refine ⟨k⁻¹ • L.comp (ContinuousLinearMap.inl ℝ E ℝ), u / k, fun x r hxr => ?_, ?_⟩
  · have happ : (k⁻¹ • L.comp (ContinuousLinearMap.inl ℝ E ℝ)) x = k⁻¹ * L (x, 0) := by simp
    have hLr := hLF (x, r) hxr
    rw [hL, hdk] at hLr
    have hstep : L (x, 0) - u < r * k := by linarith
    rw [happ]
    have hval : k⁻¹ * L (x, 0) - u / k = (L (x, 0) - u) / k := by field_simp
    rw [hval, div_lt_iff₀ hk]
    exact hstep
  · have happ : (k⁻¹ • L.comp (ContinuousLinearMap.inl ℝ E ℝ)) x₀ = k⁻¹ * L (x₀, 0) := by simp
    rw [hdk] at hLx
    have hstep : μ * k < L (x₀, 0) - u := by linarith
    rw [happ]
    have hval : k⁻¹ * L (x₀, 0) - u / k = (L (x₀, 0) - u) / k := by field_simp
    rw [hval, lt_div_iff₀ hk]
    exact hstep

/-- **The epigraph form.** A convex function with a closed epigraph has, at every point of its
domain and below every value it takes there, a continuous affine minorant passing above that value.
`exists_affine_le_of_closed_proper` is this lemma with `μ := f x₀ - 1`. -/
theorem exists_affine_le_of_isClosed_epi {g : E → EReal} (hg : ConvexFn g)
    (hcl : IsClosed (epi g)) {x₀ : E} {μ ν : ℝ} (hν : g x₀ ≤ (ν : EReal))
    (hμ : (μ : EReal) < g x₀) :
    ∃ (y : E →L[ℝ] ℝ) (b : ℝ), (∀ x, ((y x - b : ℝ) : EReal) ≤ g x) ∧ μ < y x₀ - b := by
  have hμν : μ < ν := by exact_mod_cast lt_of_lt_of_le hμ hν
  obtain ⟨y, b, hy, hx₀⟩ := exists_affine_lt_of_notMem hg.convex_epi hcl hμν (mk_mem_epi.2 hν)
    (fun hmem => absurd (mk_mem_epi.1 hmem) (not_le.2 hμ))
  refine ⟨y, b, fun x => ?_, hx₀⟩
  by_contra hcon
  obtain ⟨ρ, hρ₁, hρ₂⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hcon)
  have hmem : (x, ρ) ∈ epi g := mk_mem_epi.2 hρ₁.le
  have hlt : y x - b < ρ := hy x ρ hmem
  have hgt : ρ < y x - b := by exact_mod_cast hρ₂
  linarith

end LocallyConvex

end ConvexAnalysis
