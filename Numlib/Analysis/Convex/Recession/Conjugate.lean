import Numlib.Analysis.Convex.Duality.Polar
import Numlib.Analysis.Convex.Duality.Support
import Numlib.Analysis.Convex.Recession.ConeHull
import Numlib.Analysis.Convex.Recession.Function

/-!
# Recession functions, conjugates and polar cones

Two dual dictionaries between a function's recession data and its conjugate's effective domain.
At the level of functions, the recession function of a conjugate is the support function of the
effective domain; at the level of cones, the recession *cone* of a conjugate is the *polar* of the
effective domain, which is the same statement read at the level `0`.

One direction is free: bounding the supremum that defines `f*` termwise gives
`(f*) 0⁺ ≤ δ*(· | dom f)` with no hypothesis at all. The reverse needs a `z` at which `f*` is
finite, so that Fenchel's inequality at `z + a • y` can be pushed to `a → ∞`; that is the
hypothesis `Proper (conj B f)`, automatic for a closed proper convex `f`.

## Main results

* `recessionFn_conj` — `(f*) 0⁺ = δ*(· | dom f)` (Theorem 13.3 in [^1]). The dual form
  `f 0⁺ = δ*(· | dom f*)` is `recessionFn_eq_supportFn_dom_conj` in `Duality/Level.lean`.
* `constancySpace_conj` — the constancy space of `f*` is the annihilator of `dom f`. This is the
  form the image and duality theorems consume: "`f*` is constant along `z`" becomes "`z`
  annihilates `dom f`", which a relative-interior hypothesis can discharge.
* `recessionConeFn_conj`, `recessionConeFn_conj_hull`, `recessionConeFn_eq_polarCone_dom_conj`,
  `polarCone_recessionConeFn` — both polar assertions (Theorem 14.2 in [^1]), each in the direct
  form and in the cone-generated phrasing. The direct form is stated against `dom f` rather than
  the cone it generates; a polar cone cannot tell the two apart (`polarCone_hull`).
* `zero_mem_interior_iff_polarCone_eq_zero` — a nonempty convex set has the origin in its interior
  exactly when its polar cone is trivial. Composed with the polar dictionary and the level-set
  theory this gives `isBounded_setOf_le_iff_zero_mem_interior_dom_conj`.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §13 and §14.
-/

open scoped Pointwise

namespace ConvexAnalysis

section RecessionConj

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- **The unconditional half**: `(f*) 0⁺ ≤ δ*(· | dom f)`.

Bounding the supremum that defines `f*` termwise: off `dom f` the term is `⊥`, and on `dom f` the
bound `⟨x, y⟩ ≤ ν` moves `a⟨x, y⟩` past the supremum. -/
theorem recessionFn_conj_le_supportFn_dom (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) :
    recessionFn (conj B f) ≤ supportFn B (dom f) := by
  intro y
  refine EReal.le_of_forall_coe_le fun ν hν => ?_
  rw [supportFn_le_coe_iff] at hν
  rw [recessionFn_le_coe_iff, mk_mem_recessionCone_epi_iff]
  intro z a ha
  rw [conj_apply]
  refine iSup_le fun x => ?_
  by_cases hx : x ∈ dom f
  · have hBx : B x (z + a • y) = B x z + a * B x y := by rw [map_add, map_smul, smul_eq_mul]
    have hmul : a * B x y ≤ a * ν := mul_le_mul_of_nonneg_left (hν x hx) ha
    have hle : B x (z + a • y) ≤ B x z + a * ν := by rw [hBx]; linarith
    calc ((B x (z + a • y) : ℝ) : EReal) - f x
        ≤ ((B x z + a * ν : ℝ) : EReal) - f x :=
          EReal.sub_le_sub (EReal.coe_le_coe_iff.2 hle) le_rfl
      _ = (((B x z : ℝ) : EReal) - f x) + ((a * ν : ℝ) : EReal) :=
          EReal.coe_add_sub _ _ _
      _ ≤ conj B f z + ((a * ν : ℝ) : EReal) :=
          add_le_add (sub_le_conj B f x z) le_rfl
  · rw [mem_dom, not_lt, top_le_iff] at hx
    rw [hx, EReal.sub_top]
    exact bot_le

/-- **The half that needs properness of `f*`**: `δ*(· | dom f) ≤ (f*) 0⁺`.

`Proper (conj B f)` supplies a `z` at which `f*` is finite; Fenchel's inequality at `z + a • y`
then reads `⟨x, z⟩ + a⟨x, y⟩ - f x ≤ f* z + a ν`, and letting `a → ∞` forces `⟨x, y⟩ ≤ ν`. -/
theorem supportFn_dom_le_recessionFn_conj (hp : Proper f) (hc : Proper (conj B f)) :
    supportFn B (dom f) ≤ recessionFn (conj B f) := by
  intro y
  refine EReal.le_of_forall_coe_le fun ν hν => ?_
  rw [supportFn_le_coe_iff]
  intro x hx
  obtain ⟨z, hz⟩ := hc.dom_nonempty
  obtain ⟨c, hcz⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hc.ne_bot z) hz
  obtain ⟨r, hrx⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
  have hrec : ∀ a : ℝ, 0 ≤ a → conj B f (z + a • y) ≤ conj B f z + ((a * ν : ℝ) : EReal) :=
    fun a ha => mk_mem_recessionCone_epi_iff.1 (recessionFn_le_coe_iff.1 hν) z a ha
  have hbound : ∀ a : ℝ, 0 ≤ a → B x z + a * B x y - r ≤ c + a * ν := by
    intro a ha
    have hsub := sub_le_conj B f x (z + a • y)
    rw [hrx] at hsub
    have hle := hsub.trans (hrec a ha)
    rw [hcz, ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff] at hle
    have hBx : B x (z + a • y) = B x z + a * B x y := by rw [map_add, map_smul, smul_eq_mul]
    rw [hBx] at hle
    linarith
  by_contra hcon
  push Not at hcon
  have hd : 0 < B x y - ν := by linarith
  set q : ℝ := (c + r - B x z) / (B x y - ν) with hq
  set a : ℝ := max (q + 1) 0 with ha
  have ha0 : 0 ≤ a := le_max_right _ _
  have haq : q < a := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hqmul : q * (B x y - ν) = c + r - B x z := by rw [hq, div_mul_cancel₀ _ hd.ne']
  have hb := hbound a ha0
  have hexp : a * (B x y - ν) = a * B x y - a * ν := by ring
  have hstep : a * (B x y - ν) ≤ q * (B x y - ν) := by rw [hqmul, hexp]; linarith
  exact absurd (le_of_mul_le_mul_right hstep hd) (not_le.2 haq)

/-- The recession function of a conjugate is the support function of the effective domain,
`(f*) 0⁺ = δ*(· | dom f)`. -/
theorem recessionFn_conj (hp : Proper f) (hc : Proper (conj B f)) :
    recessionFn (conj B f) = supportFn B (dom f) :=
  le_antisymm (recessionFn_conj_le_supportFn_dom B f) (supportFn_dom_le_recessionFn_conj hp hc)

/-- **The constancy space of a conjugate is the annihilator of the effective domain.** This is
what the constancy hypothesis of the image theorem becomes for `f*`: "`f*` is constant along `y`"
says exactly that `y` pairs to zero with every point of `dom f`. -/
theorem constancySpace_conj (hp : Proper f) (hc : Proper (conj B f)) :
    constancySpace (conj B f) = {y : F | ∀ x ∈ dom f, B x y = 0} := by
  ext y
  rw [mem_constancySpace, recessionFn_conj hp hc, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h₁, h₂⟩
    rw [supportFn_le_zero_iff] at h₁ h₂
    intro x hx
    have hneg := h₂ x hx
    rw [map_neg] at hneg
    linarith [h₁ x hx]
  · intro h
    constructor <;> rw [supportFn_le_zero_iff] <;> intro x hx
    · exact le_of_eq (h x hx)
    · rw [map_neg, h x hx, neg_zero]

end RecessionConj

/-! ### Recession cones and polars of effective domains -/

section RecessionPolar

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- **The recession cone of a conjugate is the polar of the effective domain.** Stated against
`dom f` rather than the cone it generates, which a polar cone cannot tell apart from it;
`recessionConeFn_conj_hull` is the cone-generated phrasing. The proof reads the support-function
identity at the level `0`: `(f*)0⁺ y ≤ 0` says `⟨x, y⟩ ≤ 0` for every `x ∈ dom f`. -/
theorem recessionConeFn_conj (hp : Proper f) (hc : Proper (conj B f)) :
    recessionConeFn (conj B f) = polarCone B (dom f) := by
  ext y
  rw [mem_recessionConeFn, recessionFn_conj hp hc, supportFn_le_zero_iff]
  exact Iff.rfl

/-- The same in cone-generated form: the polar of the convex cone generated by `dom f` is the
recession cone of `f*`. -/
theorem recessionConeFn_conj_hull (hp : Proper f) (hc : Proper (conj B f)) :
    polarCone B (PointedCone.hull ℝ (dom f) : Set E) = recessionConeFn (conj B f) := by
  rw [polarCone_hull, recessionConeFn_conj hp hc]

end RecessionPolar

section RecessionPolarDual

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f : E → EReal}

/-- **Before polars are taken**: the recession cone of a closed proper convex function is the
polar of the effective domain of its conjugate — the previous result applied to `f*`, using
`f** = f`. This is the form the existence theory for minimisers consumes. -/
theorem recessionConeFn_eq_polarCone_dom_conj (hf : ConvexFn f) (hcl : ClosedFn f) (hp : Proper f) :
    recessionConeFn f = polarCone B.flip (dom (conj B f)) := by
  have hbi : biconj B f = f := biconj_eq_self hf hcl
  have h := recessionConeFn_conj (B := B.flip) (f := conj B f) (proper_conj ⟨hf, hcl, hp⟩)
    (by rw [show conj B.flip (conj B f) = f from hbi]; exact hp)
  rwa [show conj B.flip (conj B f) = f from hbi] at h

end RecessionPolarDual

section RecessionPolarBipolar

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] [IsCompatiblePairing B.flip] {f : E → EReal}

/-- **The polar of the recession cone** of a closed proper convex function is the closure of the
convex cone generated by `dom f*`. Take polars in `recessionConeFn_eq_polarCone_dom_conj` and
apply the bipolar theorem. -/
theorem polarCone_recessionConeFn (hf : ConvexFn f) (hcl : ClosedFn f) (hp : Proper f) :
    polarCone B (recessionConeFn f)
      = closure (PointedCone.hull ℝ (dom (conj B f)) : Set F) := by
  set K : PointedCone ℝ F := PointedCone.hull ℝ (dom (conj B f)) with hK
  rw [recessionConeFn_eq_polarCone_dom_conj (B := B) hf hcl hp, ← polarCone_hull B.flip,
    ← hK]
  exact polarCone_polarCone (B := B.flip) (K : ConvexCone ℝ F).convex
    (smul_coe_pointedCone K) ⟨0, K.zero_mem⟩

end RecessionPolarBipolar

/-! ### Bounded level sets -/

section BoundedLevel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] [IsCompatiblePairing B.flip]

omit [FiniteDimensional ℝ E] in
/-- **The origin is interior to a convex set exactly when its polar cone is trivial.** Both
directions run on the absorbency criterion for interior points: forwards, absorbency at the origin
makes every value of the pairing vanish, and the pairing separates points; backwards, the bipolar
theorem turns a trivial polar into "the cone generated by `D` is dense", which passing to the
relative interior of a closure upgrades to absorbency again. Nonemptiness is not decorative: for
`D = ∅` between two trivial spaces the polar is `{0}` while the interior is empty. -/
theorem zero_mem_interior_iff_polarCone_eq_zero {D : Set F} (hD : Convex ℝ D) (hne : D.Nonempty) :
    (0 : F) ∈ interior D ↔ polarCone B.flip D = {(0 : E)} := by
  have hconv : Convex ℝ ((PointedCone.hull ℝ D : PointedCone ℝ F) : Set F) :=
    ((PointedCone.hull ℝ D : PointedCone ℝ F) : ConvexCone ℝ F).convex
  constructor
  · intro hint
    have habs := (Convex.mem_interior_iff_absorbs hD).1 hint
    refine subset_antisymm (fun x hx => ?_) ?_
    · have key : ∀ w : F, B x w ≤ 0 := by
        intro w
        obtain ⟨ε, hε, hmem⟩ := habs w
        have hx' := hx _ (show ε • w ∈ D by simpa using hmem)
        rw [LinearMap.flip_apply, map_smul, smul_eq_mul] at hx'
        nlinarith
      have hall : ∀ y : F, B x y = 0 := by
        intro y
        have h1 := key y
        have h2 := key (-y)
        rw [map_neg] at h2
        linarith
      have hx0 : x = 0 := SeparatingDual.eq_zero_of_forall_dual_eq_zero fun g => by
        obtain ⟨y, hy⟩ := exists_pairing_eq B g
        rw [hy x]
        exact hall y
      simpa using hx0
    · rintro x rfl
      intro y _
      simp
  · intro hpol
    have hbip : closure ((PointedCone.hull ℝ D : PointedCone ℝ F) : Set F) = Set.univ := by
      have h := polarCone_polarCone (B := B.flip)
        (K := ((PointedCone.hull ℝ D : PointedCone ℝ F) : Set F))
        hconv (smul_coe_pointedCone _) ⟨0, Submodule.zero_mem _⟩
      rw [polarCone_hull, hpol] at h
      rw [← h]
      ext x'
      simp [polarCone]
    have hfull : ((PointedCone.hull ℝ D : PointedCone ℝ F) : Set F) = Set.univ := by
      have hri : ri ((PointedCone.hull ℝ D : PointedCone ℝ F) : Set F) = Set.univ := by
        rw [← Convex.relint_closure hconv, hbip,
          intrinsicInterior_eq_interior (s := (Set.univ : Set F)) (by simp), interior_univ]
      exact subset_antisymm (Set.subset_univ _) (hri ▸ intrinsicInterior_subset)
    have hmemhull : ∀ y : F, y = 0 ∨ ∃ t : ℝ, 0 < t ∧ y ∈ t • D := fun y =>
      (mem_coe_hull_iff_of_convex hD).1 (hfull ▸ Set.mem_univ y)
    have hzero : (0 : F) ∈ D := by
      obtain ⟨d, hd⟩ := hne
      rcases hmemhull (-d) with h0 | ⟨t, ht, e, he, hed⟩
      · rwa [show d = 0 from by simpa using congrArg Neg.neg h0] at hd
      · have hcomb := hD hd he (by positivity : (0 : ℝ) ≤ 1 / (1 + t))
          (by positivity : (0 : ℝ) ≤ t / (1 + t)) (by field_simp)
        have hval : (1 / (1 + t)) • d + (t / (1 + t)) • e = (0 : F) := by
          have h1 : (t / (1 + t)) • e = (1 / (1 + t)) • (t • e) := by
            rw [smul_smul]
            congr 1
            field_simp
          have hed' : t • e = -d := hed
          rw [h1, hed', smul_neg, add_neg_cancel]
        rwa [hval] at hcomb
    rw [Convex.mem_interior_iff_absorbs hD]
    intro y
    rcases hmemhull y with rfl | ⟨t, ht, e, he, hey⟩
    · exact ⟨1, one_pos, by simpa using hzero⟩
    · refine ⟨t⁻¹, by positivity, ?_⟩
      have hey' : t • e = y := hey
      rw [zero_add, ← hey', smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      exact he

/-- **Every level set of a closed proper convex function is bounded exactly when the origin is
interior to the effective domain of the conjugate.** The polar dictionary turns the recession cone
of `f` into the polar of `dom f*`, every nonempty level set has that same recession cone, and a
nonempty closed convex set is bounded exactly when its recession cone is trivial. -/
theorem isBounded_setOf_le_iff_zero_mem_interior_dom_conj {f : E → EReal}
    (hf : ConvexFn f) (hcl : ClosedFn f) (hp : Proper f) :
    (∀ α : ℝ, Bornology.IsBounded {z : E | f z ≤ (α : EReal)})
      ↔ (0 : F) ∈ interior (dom (conj B f)) := by
  have hpc : Proper (conj B f) := proper_conj ⟨hf, hcl, hp⟩
  have hepi : IsClosed (epi f) := ClosedProperConvexFn.isClosed_epi ⟨hf, hcl, hp⟩
  have hlev : ∀ α : ℝ, IsClosed {z : E | f z ≤ (α : EReal)} := fun α =>
    lowerSemicontinuous_iff_isClosed_le.1 (lowerSemicontinuous_iff_isClosed_epi.2 hepi) α
  rw [zero_mem_interior_iff_polarCone_eq_zero (B := B) (convexFn_conj B f).convex_dom
      hpc.dom_nonempty,
    ← recessionConeFn_eq_polarCone_dom_conj (B := B) hf hcl hp]
  constructor
  · intro hbd
    obtain ⟨x, hx⟩ := hp.dom_nonempty
    obtain ⟨α, hα⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
    have hlevne : {z : E | f z ≤ (α : EReal)}.Nonempty := ⟨x, le_of_eq hα⟩
    rw [← recessionCone_setOf_le hf hepi hlevne]
    exact (isBounded_iff_recessionCone_eq_zero (hf.convex_le _) (hlev α) hlevne).1 (hbd α)
  · intro hrec α
    rcases Set.eq_empty_or_nonempty {z : E | f z ≤ (α : EReal)} with hem | hlevne
    · rw [hem]
      exact Bornology.isBounded_empty
    · refine (isBounded_iff_recessionCone_eq_zero (hf.convex_le _) (hlev α) hlevne).2 ?_
      rw [recessionCone_setOf_le hf hepi hlevne]
      exact hrec

end BoundedLevel

end ConvexAnalysis
