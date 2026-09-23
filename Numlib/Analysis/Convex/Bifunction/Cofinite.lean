import Numlib.Analysis.Convex.Bifunction.Algebra
import Numlib.Analysis.Convex.Duality.Relint
import Numlib.Analysis.Convex.Saddle.Kernel

/-!
# Co-finite bifunctions

A convex bifunction is **co-finite** when every slice `Fu` is a co-finite convex function: closed,
proper, convex, with an epigraph containing no non-vertical half-line. This is the condition under
which the algebra of bifunctions loses its side conditions — a co-finite bifunction has all of `U`
as its effective domain and an everywhere-finite inner product `⟨Fu, y⟩`, so the relative-interior
hypotheses become vacuous. The identity `⟨GFu, z⟩ = ⟨u, F* G* z⟩` lives here too, for the same
reason: it needs a relative interior, hence a topology and a finite dimension.

## Main definitions

* `CofiniteBifun F` — a convex bifunction all of whose slices are co-finite convex functions.

## Main results

* `CofiniteBifun.convexDomBifun_eq_univ`, `CofiniteBifun.proper` — a co-finite bifunction has full
  effective domain and is proper.
* `CofiniteBifun.bracket_lt_top`, `cofiniteBifun_of_forall_bracket_lt_top` — a closed convex
  bifunction is co-finite exactly when `⟨Fu, y⟩` is finite for every `u` and `y`
  ([rockafellar1970convex] Corollary 13.3.1, slice by slice).
* `cofinite_infConv`, `cofiniteBifun_infConvBifun`, `convexAdjointBifun_infConvBifun_of_cofinite` —
  Rockafellar's closing remark: `F₁ □ F₂` is co-finite and `(F₁ □ F₂)* = F₁* □ F₂*`, with no
  hypothesis beyond co-finiteness. `cofinite_smulRight` and `cofiniteBifun_smulRightBifun` are the
  same for `F ↦ Fλ`, `λ > 0`.
* `cofiniteBifun_iff_convexDomBifun_eq_univ` — a closed proper convex bifunction is co-finite
  **iff** `dom F = U` and `dom F* = Y`. Rockafellar deduces this from the saddle-function
  correspondence; the proof here is the finiteness criterion for conjugates, slice by slice.
* `CofiniteBifun.bracket_eq_concaveBracket_convexAdjointBifun` — `⟨Fu, y⟩ = ⟨u, F* y⟩` for *every*
  `u`; and `bracket_compBifun_eq_concaveBracket_concaveCompBifun` is the corresponding
  `⟨GFu, z⟩ = ⟨u, F* G* z⟩` for a product of bifunctions.

## Implementation notes

Rockafellar defines co-finiteness for convex bifunctions only, and the convexity is genuinely extra
data — the graph function of a bifunction all of whose slices are convex need not be convex on
`U × X` — so `CofiniteBifun` carries `ConvexBifun` as a field.

Elsewhere the relative-interior conditions are carried as `IsExactSum` hypotheses; here they are
discharged, because the functions being added are finite on the whole space and
`IsExactSum.of_relint` applies at the origin. That is why this module is finite-dimensional.

## References

* [rockafellar1970convex] §38 and §13.
-/

open Set

namespace ConvexAnalysis

/-! ### Co-finite bifunctions -/

section Defs

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace X] {F : Bifun U X}

/-- A **co-finite convex bifunction**: every slice is a co-finite convex function. This forces
`dom F = U` and makes `F` proper. -/
structure CofiniteBifun (F : Bifun U X) : Prop where
  /-- The bifunction is convex. -/
  convexBifun : ConvexBifun F
  /-- Every slice is a co-finite convex function. -/
  cofinite_apply : ∀ u, Cofinite (F u)

theorem CofiniteBifun.closedProperConvexFn_apply (hF : CofiniteBifun F) (u : U) :
    ClosedProperConvexFn (F u) := (hF.cofinite_apply u).toClosedProperConvexFn

/-- **Co-finiteness forces a full effective domain**: every slice is proper. -/
theorem CofiniteBifun.convexDomBifun_eq_univ (hF : CofiniteBifun F) : convexDomBifun F = univ :=
  eq_univ_of_forall fun u =>
    mem_convexDomBifun_iff_convexDom_nonempty.2 (hF.cofinite_apply u).proper.convexDom_nonempty

theorem CofiniteBifun.proper (hF : CofiniteBifun F) : ProperConvex (graphFn F) := by
  obtain ⟨x, hx⟩ := (hF.cofinite_apply (0 : U)).proper.convexDom_nonempty
  exact ⟨⟨((0 : U), x), hx⟩, fun p => (hF.cofinite_apply p.1).proper.ne_bot p.2⟩

theorem CofiniteBifun.ne_bot (hF : CofiniteBifun F) (u : U) (x : X) : F u x ≠ ⊥ :=
  (hF.cofinite_apply u).proper.ne_bot x

end Defs

/-! ### Finiteness of the inner product -/

section BracketNeBot

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace X] [AddCommGroup Y] [Module ℝ Y] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  {F : Bifun U X}

/-- With `CofiniteBifun.bracket_lt_top`: `⟨Fu, y⟩` is finite, every slice being proper. -/
theorem CofiniteBifun.bracket_ne_bot (hF : CofiniteBifun F) (u : U) (y : Y) :
    bracket Bx F u y ≠ ⊥ :=
  convexConj_ne_bot (hF.cofinite_apply u).proper.convexDom_nonempty y

end BracketNeBot

section Bracket

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
  {F : Bifun U X}

/-- **For a co-finite bifunction the inner product `⟨Fu, y⟩` is never `+∞`.** This is the
finiteness criterion for the conjugate of a co-finite function, read at the slice `Fu`. -/
theorem CofiniteBifun.bracket_lt_top (hF : CofiniteBifun F) (u : U) (y : Y) :
    bracket Bx F u y < ⊤ :=
  (cofinite_iff_forall_convexConj_lt_top (B := Bx) (hF.closedProperConvexFn_apply u)).1
    (hF.cofinite_apply u) y

/-- The converse: closed proper convex slices and a finite `⟨Fu, y⟩` give co-finiteness. -/
theorem cofiniteBifun_of_forall_bracket_lt_top (hF : ConvexBifun F)
    (hcl : ∀ u, ClosedProperConvexFn (F u)) (h : ∀ (u : U) (y : Y), bracket Bx F u y < ⊤) :
    CofiniteBifun F :=
  ⟨hF, fun u => (cofinite_iff_forall_convexConj_lt_top (B := Bx) (hcl u)).2 (h u)⟩

end Bracket

/-! ### Infimal convolution of co-finite functions -/

section CofiniteInfConv

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
  {f g : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- **The conjugate of a co-finite function is finite everywhere.** -/
theorem Cofinite.convexConj_lt_top (hf : Cofinite f) (y : F) : convexConj B f y < ⊤ :=
  (cofinite_iff_forall_convexConj_lt_top (B := B) hf.toClosedProperConvexFn).1 hf y

/-- **The conjugates of two co-finite functions add exactly**: their effective domains are the whole
space, so the relative-interior condition for an exact sum holds at the origin. -/
theorem Cofinite.isExactSum_convexConj (hf : Cofinite f) (hg : Cofinite g) :
    IsExactSum B.flip (convexConj B f) (convexConj B g) := by
  have hdf : (0 : F) ∈ ri (convexDom (convexConj B f)) := by
    rw [Cofinite.convexDom_convexConj_eq_univ (B := B) hf, intrinsicInterior_univ]; trivial
  have hdg : (0 : F) ∈ ri (convexDom (convexConj B g)) := by
    rw [Cofinite.convexDom_convexConj_eq_univ (B := B) hg, intrinsicInterior_univ]; trivial
  exact IsExactSum.of_relint (convexFn_convexConj B f)
      (properConvex_convexConj hf.toClosedProperConvexFn)
    (convexFn_convexConj B g) (properConvex_convexConj hg.toClosedProperConvexFn) hdf hdg

/-- **The infimal convolution of two co-finite functions is a conjugate**, namely the conjugate of
`f* + g*`. This is what makes it closed. -/
theorem Cofinite.infConv_eq_convexConj_add (hf : Cofinite f) (hg : Cofinite g) :
    infConv f g = convexConj B.flip (convexConj B f + convexConj B g) := by
  have hbf : convexConj B.flip (convexConj B f) = f := convexBiconj_eq_self hf.convex hf.closed
  have hbg : convexConj B.flip (convexConj B g) = g := convexBiconj_eq_self hg.convex hg.closed
  rw [(Cofinite.isExactSum_convexConj (B := B) hf hg).convexConj_add, hbf, hbg]

omit [FiniteDimensional ℝ E] in
theorem Cofinite.properConvex_convexConj_add (hf : Cofinite f) (hg : Cofinite g) :
    ProperConvex (convexConj B f + convexConj B g) := by
  refine ⟨⟨0, ?_⟩, fun y => ?_⟩
  · rw [mem_convexDom, Pi.add_apply]
    exact EReal.add_lt_top (Cofinite.convexConj_lt_top (B := B) hf 0).ne
      (Cofinite.convexConj_lt_top (B := B) hg 0).ne
  · rw [Pi.add_apply, ne_eq, EReal.add_eq_bot_iff]
    push Not
    exact ⟨convexConj_ne_bot hf.proper.convexDom_nonempty y,
        convexConj_ne_bot hg.proper.convexDom_nonempty y⟩

/-- **The infimal convolution of two co-finite convex functions is co-finite**: `f □ g` is the
conjugate of `f* + g*`, hence closed proper convex, and its own conjugate is `f* + g*`, which is
finite everywhere. -/
theorem cofinite_infConv (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [IsCompatiblePairing B] [IsCompatiblePairing B.flip] (hf : Cofinite f) (hg : Cofinite g) :
    Cofinite (infConv f g) := by
  have heq : infConv f g = convexConj B.flip (convexConj B f + convexConj B g) :=
    Cofinite.infConv_eq_convexConj_add (B := B) hf hg
  have hproper : ProperConvex (infConv f g) := by
    refine ⟨?_, fun x => ?_⟩
    · obtain ⟨x, hx⟩ := hf.proper.convexDom_nonempty
      obtain ⟨z, hz⟩ := hg.proper.convexDom_nonempty
      exact ⟨x + z, by rw [convexDom_infConv]; exact ⟨x, hx, z, hz, rfl⟩⟩
    · rw [heq]
      exact convexConj_ne_bot
          (Cofinite.properConvex_convexConj_add (B := B) hf hg).convexDom_nonempty x
  have hclosed : ClosedConvex (infConv f g) := by rw [heq]; exact closedConvex_convexConj
  have hcpc : ClosedProperConvexFn (infConv f g) :=
    ⟨convexFn_infConv hf.convex hg.convex, hclosed, hproper⟩
  refine (cofinite_iff_forall_convexConj_lt_top (B := B) hcpc).2 fun y => ?_
  rw [convexConj_infConv, Pi.add_apply]
  exact EReal.add_lt_top (Cofinite.convexConj_lt_top (B := B) hf y).ne
    (Cofinite.convexConj_lt_top (B := B) hg y).ne

end CofiniteInfConv

/-! ### Infimal convolution of co-finite bifunctions -/

section CofiniteAlgebra

variable {U V X Y : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
  {F F₁ F₂ : Bifun U X}

omit [FiniteDimensional ℝ U] in
/-- Slice by slice this is `cofinite_infConv`; convexity of `F₁ □ F₂` is
`convexBifun_infConvBifun`. -/
theorem cofiniteBifun_infConvBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF₁ : CofiniteBifun F₁)
    (hF₂ : CofiniteBifun F₂) : CofiniteBifun (infConvBifun F₁ F₂) :=
  ⟨convexBifun_infConvBifun hF₁.ne_bot hF₂.ne_bot hF₁.convexBifun hF₂.convexBifun,
    fun u => cofinite_infConv Bx (hF₁.cofinite_apply u) (hF₂.cofinite_apply u)⟩

omit [FiniteDimensional ℝ X] in
/-- The two brackets add exactly, both being finite everywhere. This is what makes
`convexAdjointBifun_infConvBifun` unconditional for co-finite bifunctions. -/
theorem isExactSum_neg_bracket_of_cofinite (hF₁ : CofiniteBifun F₁) (hF₂ : CofiniteBifun F₂)
    (y : Y) : IsExactSum Bu (fun u => -(bracket Bx F₁ u y)) (fun u => -(bracket Bx F₂ u y)) := by
  have hp : ∀ G : Bifun U X, CofiniteBifun G → ProperConvex (fun u => -(bracket Bx G u y)) := by
    intro G hG
    refine ⟨⟨0, ?_⟩, fun u => ?_⟩
    · rw [mem_convexDom, lt_top_iff_ne_top, ne_eq, EReal.neg_eq_top_iff]
      exact CofiniteBifun.bracket_ne_bot (Bx := Bx) hG 0 y
    · rw [ne_eq, EReal.neg_eq_bot_iff]
      exact (CofiniteBifun.bracket_lt_top (Bx := Bx) hG u y).ne
  have hd : ∀ G : Bifun U X, CofiniteBifun G →
      (0 : U) ∈ ri (convexDom fun u => -(bracket Bx G u y)) := by
    intro G hG
    have hdom : (convexDom fun u => -(bracket Bx G u y)) = univ :=
      eq_univ_of_forall fun u => by
        rw [mem_convexDom, lt_top_iff_ne_top, ne_eq, EReal.neg_eq_top_iff]
        exact CofiniteBifun.bracket_ne_bot (Bx := Bx) hG u y
    rw [hdom, intrinsicInterior_univ]; trivial
  exact IsExactSum.of_relint (concaveFn_iff_convexFn_neg.1 (concaveFn_bracket hF₁.convexBifun Bx y))
    (hp F₁ hF₁) (concaveFn_iff_convexFn_neg.1 (concaveFn_bracket hF₂.convexBifun Bx y))
    (hp F₂ hF₂) (hd F₁ hF₁) (hd F₂ hF₂)

omit [FiniteDimensional ℝ X] in
/-- **`(F₁ □ F₂)* = F₁* □ F₂*` for co-finite bifunctions**, with the exactness hypothesis
discharged. -/
theorem convexAdjointBifun_infConvBifun_of_cofinite (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF₁ : CofiniteBifun F₁) (hF₂ : CofiniteBifun F₂) :
    convexAdjointBifun Bu Bx (infConvBifun F₁ F₂)
      = supConvBifun (convexAdjointBifun Bu Bx F₁) (convexAdjointBifun Bu Bx F₂) :=
  convexAdjointBifun_infConvBifun_eq_supConvBifun Bu Bx F₁ F₂
    (isExactSum_neg_bracket_of_cofinite hF₁ hF₂)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
/-- **For a co-finite bifunction the two inner products agree at every `u`**,
`⟨Fu, y⟩ = ⟨u, F* y⟩`. They agree on `ri (dom F)`, and `dom F` is all of `U`. -/
theorem CofiniteBifun.bracket_eq_concaveBracket_convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : CofiniteBifun F) (u : U) (y : Y) :
    bracket Bx F u y = concaveBracket Bu (convexAdjointBifun Bu Bx F) u y :=
  bracket_eq_concaveBracket_convexAdjointBifun_of_mem_relint Bu Bx hF.convexBifun
    (by rw [hF.convexDomBifun_eq_univ, intrinsicInterior_univ]; trivial) y

end CofiniteAlgebra

/-! ### Right scalar multiplication of co-finite functions -/

section CofiniteSmulRight

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {f : E → EReal} {a : ℝ}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **`fa` is the conjugate of `a f*`**, for `a > 0` and closed convex `f`: the conjugation rule
`convexConj_smul` at `g = f*`, with Fenchel–Moreau turning `f**` back into `f`. It supplies
closedness of `fa`, which the epigraph-image definition of `smulRight` does not see. -/
theorem smulRight_eq_convexConj_smul (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [IsCompatiblePairing B] [IsCompatiblePairing B.flip] (hc : ConvexFn f) (hcl : ClosedConvex f)
    (ha : 0 < a) : smulRight f a = convexConj B.flip (fun y => (a : EReal) * convexConj B f y) := by
  have hbi : convexConj B.flip (convexConj B f) = f := convexBiconj_eq_self hc hcl
  rw [convexConj_smul ha B.flip (convexConj B f), hbi]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **`fa` is closed** when `f` is closed convex and `a > 0`. It is a conjugate
(`smulRight_eq_convexConj_smul`). -/
theorem closedConvex_smulRight (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [IsCompatiblePairing B] [IsCompatiblePairing B.flip] (hc : ConvexFn f) (hcl : ClosedConvex f)
    (ha : 0 < a) : ClosedConvex (smulRight f a) := by
  rw [smulRight_eq_convexConj_smul B hc hcl ha]
  exact closedConvex_convexConj

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
theorem coe_mul_ne_bot (ha : 0 < a) {u : EReal} (hu : u ≠ ⊥) : (a : EReal) * u ≠ ⊥ := by
  intro h
  refine EReal.coe_mul_ne_top ha (u := -u) (by rwa [Ne, EReal.neg_eq_top_iff]) ?_
  rw [mul_neg, h, EReal.neg_bot]

omit [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- **`fa` is proper** when `f` is and `a > 0`. -/
theorem properConvex_smulRight (hf : ProperConvex f)
    (ha : 0 < a) : ProperConvex (smulRight f a) := by
  refine ⟨?_, fun x => ?_⟩
  · obtain ⟨x₀, hx₀⟩ := hf.convexDom_nonempty
    refine ⟨a • x₀, mem_convexDom.2 (lt_top_iff_ne_top.2 ?_)⟩
    rw [smulRight_apply_pos ha, inv_smul_smul₀ ha.ne']
    exact EReal.coe_mul_ne_top ha (mem_convexDom.1 hx₀).ne
  · rw [smulRight_apply_pos ha]
    exact coe_mul_ne_bot ha (hf.ne_bot _)

omit [FiniteDimensional ℝ E] in
/-- **Right scalar multiplication preserves co-finiteness**, for `a > 0`. -/
theorem cofinite_smulRight (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [IsCompatiblePairing B] [IsCompatiblePairing B.flip] (hf : Cofinite f) (ha : 0 < a) :
    Cofinite (smulRight f a) := by
  have hne : ∀ y : F, (a : EReal) * convexConj B f y ≠ ⊤ :=
    fun y => EReal.coe_mul_ne_top ha (Cofinite.convexConj_lt_top (B := B) hf y).ne
  have hcpc : ClosedProperConvexFn (smulRight f a) :=
    ⟨convexFn_smulRight a hf.convex, closedConvex_smulRight B hf.convex hf.closed ha,
      properConvex_smulRight hf.proper ha⟩
  refine (cofinite_iff_forall_convexConj_lt_top (B := B) hcpc).2 fun y => ?_
  rw [convexConj_smulRight ha B f]
  exact lt_top_iff_ne_top.2 (hne y)

end CofiniteSmulRight

/-! ### Right scalar multiplication, and the co-finiteness criterion -/

section CofiniteCriterion

variable {U V X Y : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
  {F : Bifun U X} {l : ℝ}

omit [FiniteDimensional ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [FiniteDimensional ℝ X] in
/-- **`F ↦ Fλ` preserves co-finiteness** for `λ > 0`. Slice by slice this is `cofinite_smulRight`;
the convexity of `Fλ` is `convexBifun_smulRightBifun`. -/
theorem cofiniteBifun_smulRightBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : CofiniteBifun F) (hl : 0 < l) :
    CofiniteBifun (smulRightBifun F l) :=
  ⟨convexBifun_smulRightBifun hl hF.convexBifun,
    fun u => cofinite_smulRight Bx (hF.cofinite_apply u) hl⟩

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ X] in
/-- **`dom F* = Y`**, the half of the co-finiteness criterion needing no closedness: `⟨F·, y⟩` is a
finite concave function on `U`, so its negative is proper convex and its conjugate is proper; the
sign dictionary carries that back to `F* y`. -/
theorem CofiniteBifun.concaveDomBifun_convexAdjointBifun_eq_univ (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : CofiniteBifun F) :
    concaveDomBifun (convexAdjointBifun Bu Bx F) = univ := by
  refine eq_univ_of_forall fun y => ?_
  have hgc : ConvexFn (fun u => -(bracket Bx F u y)) :=
    concaveFn_iff_convexFn_neg.1 (concaveFn_bracket hF.convexBifun Bx y)
  have hgp : ProperConvex (fun u => -(bracket Bx F u y)) := by
    refine ⟨⟨0, mem_convexDom.2 (lt_top_iff_ne_top.2 ?_)⟩, fun u => ?_⟩
    · rw [ne_eq, EReal.neg_eq_top_iff]
      exact CofiniteBifun.bracket_ne_bot (Bx := Bx) hF 0 y
    · rw [ne_eq, EReal.neg_eq_bot_iff]
      exact (CofiniteBifun.bracket_lt_top (Bx := Bx) hF u y).ne
  obtain ⟨w, hw⟩ := (properConvex_convexConj_of_properConvex (B := Bu) hgc hgp).convexDom_nonempty
  refine ⟨-w, ?_⟩
  have hneg : -(concaveConj Bu (fun u => bracket Bx F u y) (-w))
      = convexConj Bu (fun u => -(bracket Bx F u y)) w := by
    rw [neg_concaveConj, neg_neg]
  rw [convexAdjointBifun_eq_concaveConj_bracket, ne_eq, ← EReal.neg_eq_top_iff, hneg]
  exact (mem_convexDom.1 hw).ne

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] [FiniteDimensional ℝ X]
  [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] in
/-- The substantial direction: `dom F = U` makes every bracket `⟨Fu, y⟩` finite below, and
`dom F* = Y` makes it finite above — if `⟨Fu₀, y⟩ = +∞` for a single `u₀` then `F* y ≡ -∞`. The
finiteness criterion for conjugates, slice by slice, does the rest. -/
theorem cofiniteBifun_of_convexDomBifun_eq_univ (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hp : ProperConvex (graphFn F)) (hdom : convexDomBifun F = univ)
    (hadj : concaveDomBifun (convexAdjointBifun Bu Bx F) = univ) : CofiniteBifun F := by
  refine cofiniteBifun_of_forall_bracket_lt_top (Bx := Bx) hF (fun u => ?_) (fun u y => ?_)
  · refine ⟨hF.convexFn_apply u, hcl.imageClosedBifun u, ⟨?_, fun x => hp.ne_bot (u, x)⟩⟩
    exact mem_convexDomBifun_iff_convexDom_nonempty.1 (by rw [hdom]; trivial)
  · rcases lt_or_eq_of_le (le_top : bracket Bx F u y ≤ ⊤) with h | htop
    · exact h
    · exfalso
      obtain ⟨v, hv⟩ : y ∈ concaveDomBifun (convexAdjointBifun Bu Bx F) := by rw [hadj]; trivial
      refine hv ?_
      rw [convexAdjointBifun_eq_concaveConj_bracket]
      exact congrFun (concaveConj_of_eq_top (B := Bu)
        (g := fun u' => bracket Bx F u' y) htop) v

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ X] [IsCompatiblePairing Bu.flip] in
/-- **A closed proper convex bifunction is co-finite iff `dom F = U` and `dom F* = Y`.** The proof
here is the finiteness criterion for conjugates, slice by slice. -/
theorem cofiniteBifun_iff_convexDomBifun_eq_univ (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hp : ProperConvex (graphFn F)) :
    CofiniteBifun F ↔
      convexDomBifun F = univ ∧ concaveDomBifun (convexAdjointBifun Bu Bx F) = univ :=
  ⟨fun h => ⟨h.convexDomBifun_eq_univ,
      CofiniteBifun.concaveDomBifun_convexAdjointBifun_eq_univ Bu Bx h⟩,
    fun h => cofiniteBifun_of_convexDomBifun_eq_univ hF hcl hp h.1 h.2⟩

end CofiniteCriterion

/-! ### The inner product of a product of bifunctions -/

section CompBifunBracket

variable {U V X W Y Z : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup X] [Module ℝ X] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  {F : Bifun U X} {G : Bifun X Y}

/-- **`⟨GFu, z⟩ = ⟨u, F* G* z⟩`.** The two brackets of `GF` agree at a relative interior point of
`dom (GF)`, and `convexAdjointBifun_compBifun` rewrites `(GF)*` as `F* G*`. The companion equality
`⟨GFu, z⟩ = ⟨Fu, G* z⟩` is `bracket_compBifun_eq_fenchelPairing`. -/
theorem bracket_compBifun_eq_concaveBracket_concaveCompBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] W →ₗ[ℝ] ℝ) (By : Y →ₗ[ℝ] Z →ₗ[ℝ] ℝ)
    (hbF : ∀ u x, F u x ≠ ⊥) (hGF : ConvexBifun (compBifun G F)) {u : U}
    (hu : u ∈ ri (convexDomBifun (compBifun G F))) {z : Z}
    (hex : ∀ v : V, IsExactSum Bx (concaveBracket Bu.flip (inverseBifun F) v)
      (fun x => -(bracket By G x z))) :
    bracket By (compBifun G F) u z
      = concaveBracket
          Bu (concaveCompBifun (convexAdjointBifun Bx By G) (convexAdjointBifun Bu Bx F)) u z := by
  rw [bracket_eq_concaveBracket_convexAdjointBifun_of_mem_relint Bu By hGF hu z,
      concaveBracket_apply,
    concaveBracket_apply]
  exact iInf_congr fun v => by rw [convexAdjointBifun_compBifun Bu Bx By hbF (hex v)]

end CompBifunBracket

end ConvexAnalysis
