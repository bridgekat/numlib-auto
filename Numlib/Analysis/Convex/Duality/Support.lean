import Numlib.Analysis.Convex.Duality.Conjugate
import Numlib.Analysis.Convex.Homogeneous

/-!
# Support functions

The **support function** of a set `s ⊆ E` with respect to a pairing `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ` is
`δ*(y ∣ s) = sup {⟨x, y⟩ ∣ x ∈ s}`. It describes all the closed half-spaces containing `s`, since
`s ⊆ {x ∣ ⟨x, y⟩ ≤ c}` exactly when `δ*(y ∣ s) ≤ c`. Support functions are the conjugates of
indicators (`supportFn_eq_conj_indicatorFn`), so every property of `δ*(· ∣ s)` is inherited from
`Duality/Conjugate.lean` rather than proved again.

The main theorem is the correspondence: the support functions of the nonempty convex sets are
exactly the closed proper positively homogeneous convex functions, and the two classes are in
bijection. Note that the support function lives on the *other* side of the pairing,
`supportFn B s : F → EReal` for `s : Set E`, so the correspondence — which asks both that
`g : F → EReal` be closed and that the set it supports be closed in `E` — needs a topology and a
compatible pairing on both sides.

## Main definitions

* `supportFn B s` — the support function `δ*(· ∣ s)`.
* `supportSet B f` — the set `{y ∣ ∀ x, ⟨x, y⟩ ≤ f x}`, of which `f` is the support function when
  `f` is closed, proper, positively homogeneous and convex. It inverts the correspondence.
* `supportEquiv` — the correspondence as a bijection between the nonempty closed convex subsets of
  `E` and the closed proper positively homogeneous convex functions on `F`.

## Main results

* `supportFn_eq_conj_indicatorFn` — `δ*(· ∣ s) = (δ(· ∣ s))*`.
* `mem_closure_convexHull_iff_le_supportFn` — `x ∈ cl (conv s)` if and only if `⟨x, y⟩ ≤ δ*(y ∣ s)`
  for every `y` (Theorem 13.1 in [^1]).
* `conj_supportFn`, `exists_supportFn_iff`, `supportEquiv` — the indicator and the support function
  of a closed convex set are conjugate, and the correspondence above (Theorem 13.2 in [^1]).
  `exists_supportFn_finite_iff` reads it as bounded ⟺ finite.
* `clFn_eq_supportFn_of_posHomogeneous` — the closure of a positively homogeneous convex function
  is a support function. `supportSet_clFn` is the consequence that closure does not change the set
  supported.
* `conj_eq_indicatorFn_of_posHomogeneous` — the engine of both: the conjugate of a positively
  homogeneous function is an *indicator*. Reindexing the supremum defining `f*` along `x ↦ a • x`
  shows `f*(y) = a f*(y)` for every `a > 0`, so `f*(y)` is `0`, `⊤` or `⊥`, and `⊥` is excluded as
  soon as `f ≢ ⊤`. No topology is used, which is why none of this needs separation theory beyond
  what biconjugation already used.
* `supportFn_singleton`, `supportFn_union`, `supportFn_convexHull`, `supportFn_closure`,
  `supportFn_smul`, `supportFn_add` — the support functions of the basic constructions.

## Divergences from the reference

**The finite form needs closedness.** The classical deduction that a *finite* positively
homogeneous convex function is a support function goes through "a finite convex function on `Rⁿ` is
closed", which is false in infinite dimensions: a discontinuous linear functional is finite, convex
and positively homogeneous, is not closed, and is the support function of nothing. So
`exists_supportFn_finite_iff` carries `ClosedFn`, and reads "bounded" as "`⟨·, y⟩` is bounded above
on the set, for each `y`" — which is what the classical proof actually uses.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §13.
-/

open Set Pointwise

namespace ConvexAnalysis

/-! ### The support function -/

section Defs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The **support function** `δ*(· | s)` of a set `s ⊆ E`, with respect to the pairing `B`:
`δ*(y | s) = sup {⟨x, y⟩ | x ∈ s}`. The `δ*` notation is justified by
`supportFn_eq_conj_indicatorFn`: it really is the conjugate of the indicator function. -/
noncomputable def supportFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) : F → EReal :=
  fun y => ⨆ x ∈ s, ((B x y : ℝ) : EReal)

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s t : Set E} {x : E} {y : F}

theorem supportFn_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) (y : F) :
    supportFn B s y = ⨆ x ∈ s, ((B x y : ℝ) : EReal) := rfl

/-- **Support functions are conjugates of indicators.** This is why the file is short: every
property of `δ*(· | s)` below is a property of a conjugate, cited from `Conjugate.lean`. -/
theorem supportFn_eq_conj_indicatorFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) :
    supportFn B s = conj B (indicatorFn s) := by
  funext y
  rw [conj_apply]
  refine iSup_congr fun x => ?_
  by_cases hx : x ∈ s
  · rw [iSup_pos hx, indicatorFn_of_mem hx, sub_zero]
  · rw [iSup_neg hx, indicatorFn_of_notMem hx, EReal.sub_top]

theorem le_supportFn (hx : x ∈ s) (y : F) : ((B x y : ℝ) : EReal) ≤ supportFn B s y :=
  le_iSup₂ (f := fun x (_ : x ∈ s) => ((B x y : ℝ) : EReal)) x hx

theorem supportFn_le_iff {c : EReal} :
    supportFn B s y ≤ c ↔ ∀ x ∈ s, ((B x y : ℝ) : EReal) ≤ c := iSup₂_le_iff

/-- **The closed half-spaces containing `s`**: `s ⊆ {x | ⟨x, y⟩ ≤ c}` if and only if
`c ≥ δ*(y | s)`. -/
theorem supportFn_le_coe_iff {c : ℝ} :
    supportFn B s y ≤ (c : EReal) ↔ ∀ x ∈ s, B x y ≤ c := by
  rw [supportFn_le_iff]
  exact forall₂_congr fun _ _ => EReal.coe_le_coe_iff

/-- `δ*(y | s) ≤ 0` says that the pairing with `y` is nowhere positive on `s` — the level `0` of
`supportFn_le_coe_iff`, which is where a polar cone is cut out. -/
theorem supportFn_le_zero_iff : supportFn B s y ≤ 0 ↔ ∀ x ∈ s, B x y ≤ 0 := by
  rw [← EReal.coe_zero, supportFn_le_coe_iff]

/-- `0 < δ*(y | s)` says that the pairing with `y` is positive somewhere on `s`. -/
theorem zero_lt_supportFn_iff : 0 < supportFn B s y ↔ ∃ x ∈ s, 0 < B x y := by
  rw [supportFn_apply, ← EReal.coe_zero]
  simp only [lt_iSup_iff, exists_prop, EReal.coe_lt_coe_iff]

theorem supportFn_mono (h : s ⊆ t) : supportFn B s ≤ supportFn B t :=
  fun _ => iSup₂_le fun _ hx => le_supportFn (h hx) _

@[simp] theorem supportFn_empty (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    supportFn B (∅ : Set E) = fun _ => (⊥ : EReal) := by
  funext y; simp [supportFn]

@[simp] theorem supportFn_singleton (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (x : E) :
    supportFn B {x} = fun y => ((B x y : ℝ) : EReal) := by
  funext y; simp [supportFn]

theorem supportFn_union (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s t : Set E) :
    supportFn B (s ∪ t) = supportFn B s ⊔ supportFn B t := by
  funext y
  rw [Pi.sup_apply, supportFn_apply, supportFn_apply, supportFn_apply, iSup_union]

theorem supportFn_iUnion {ι : Sort*} (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (u : ι → Set E) :
    supportFn B (⋃ i, u i) = fun y => ⨆ i, supportFn B (u i) y := by
  funext y
  rw [supportFn_apply, iSup_iUnion]
  rfl

theorem supportFn_ne_bot (hs : s.Nonempty) (y : F) : supportFn B s y ≠ ⊥ := by
  obtain ⟨x, hx⟩ := hs
  exact fun hc => absurd (hc ▸ le_supportFn (B := B) hx y) (by simp)

@[simp] theorem supportFn_zero (hs : s.Nonempty) : supportFn B s 0 = 0 := by
  obtain ⟨x, hx⟩ := hs
  refine le_antisymm (iSup₂_le fun z _ => ?_) ?_
  · rw [map_zero]; rfl
  · have h := le_supportFn (B := B) hx (0 : F)
    rwa [map_zero, EReal.coe_zero] at h

theorem proper_supportFn (hs : s.Nonempty) : Proper (supportFn B s) :=
  ⟨⟨0, by rw [mem_dom, supportFn_zero hs]; exact lt_top_iff_ne_top.2 (by simp)⟩,
    supportFn_ne_bot hs⟩

/-- **The effective domain of a support function is the barrier cone** of `s`: the directions in
which the pairing is bounded above on `s`. -/
theorem dom_supportFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) :
    dom (supportFn B s) = {y : F | ∃ c : ℝ, ∀ x ∈ s, B x y ≤ c} := by
  ext y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨c, hc, -⟩ := EReal.lt_iff_exists_real_btwn.1 (hy : supportFn B s y < ⊤)
    exact ⟨c, supportFn_le_coe_iff.1 hc.le⟩
  · obtain ⟨c, hc⟩ := hy
    exact lt_of_le_of_lt (supportFn_le_coe_iff.2 hc) (EReal.coe_lt_top c)

theorem supportFn_lt_top_iff : supportFn B s y < ⊤ ↔ ∃ c : ℝ, ∀ x ∈ s, B x y ≤ c := by
  rw [← mem_dom, dom_supportFn]
  exact Iff.rfl

/-! ### Convexity and positive homogeneity

Both are inherited: convexity from `conj`, and homogeneity by reindexing the supremum. -/

/-- **The support function of any set is convex** — it is a conjugate. -/
theorem convexFn_supportFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) : ConvexFn (supportFn B s) := by
  rw [supportFn_eq_conj_indicatorFn]; exact convexFn_conj B _

/-- **The support function of any set is positively homogeneous.** -/
theorem posHomogeneous_supportFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) :
    PosHomogeneous (supportFn B s) := by
  intro a ha y
  simp only [supportFn]
  rw [EReal.coe_mul_iSup ha]
  refine iSup_congr fun x => ?_
  rw [EReal.coe_mul_iSup ha]
  refine iSup_congr fun _ => ?_
  rw [map_smul, smul_eq_mul, EReal.coe_mul]

/-- Support functions are **subadditive in the dual variable**: a positively homogeneous convex
function is subadditive, applied to `posHomogeneous_supportFn`. -/
theorem supportFn_add_le (hs : s.Nonempty) (y₁ y₂ : F) :
    supportFn B s (y₁ + y₂) ≤ supportFn B s y₁ + supportFn B s y₂ :=
  ((posHomogeneous_supportFn B s).convexFn_iff_subadditive (supportFn_ne_bot hs)).1
    (convexFn_supportFn B s) y₁ y₂

theorem convex_setOf_pairing_le (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (y : F) (M : EReal) :
    Convex ℝ {x : E | ((B x y : ℝ) : EReal) ≤ M} := by
  have h := (convexFn_affineFn (B := B) y 0).convex_le M
  simpa only [affineFn_apply, EReal.coe_zero, sub_zero] using h

/-- **The support function does not see the convex hull.** -/
theorem supportFn_convexHull (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) :
    supportFn B (convexHull ℝ s) = supportFn B s := by
  funext y
  refine le_antisymm (iSup₂_le fun x hx => ?_) (supportFn_mono (subset_convexHull ℝ s) y)
  exact convexHull_min (fun z hz => le_supportFn hz y)
    (convex_setOf_pairing_le B y (supportFn B s y)) hx

/-- **The support function of a positive multiple of a set** is the corresponding multiple of the
support function. -/
theorem supportFn_smul (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {a : ℝ} (ha : 0 < a) (s : Set E) (y : F) :
    supportFn B (a • s) y = (a : EReal) * supportFn B s y := by
  rw [supportFn_apply, supportFn_apply, EReal.coe_mul_iSup ha, ← Set.image_smul, iSup_image]
  refine iSup_congr fun z => ?_
  rw [EReal.coe_mul_iSup ha]
  refine iSup_congr fun _ => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, EReal.coe_mul]

/-- **The support function of a sum of sets is the sum of the support functions.** Unconditional,
unlike the corresponding statement for a sum of *functions*, because the two suprema never
interact through an `∞ - ∞`. -/
theorem supportFn_add (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s t : Set E) :
    supportFn B (s + t) = supportFn B s + supportFn B t := by
  funext y
  calc supportFn B (s + t) y
      = ⨆ a ∈ s, ⨆ b ∈ t, ((B (a + b) y : ℝ) : EReal) := by
        rw [supportFn_apply, ← Set.image2_add, iSup_image2]
    _ = ⨆ a ∈ s, ⨆ b ∈ t, (((B b y : ℝ) : EReal) + ((B a y : ℝ) : EReal)) := by
        refine iSup_congr fun a => iSup_congr fun _ => iSup_congr fun b => iSup_congr fun _ => ?_
        rw [map_add, LinearMap.add_apply, ← EReal.coe_add, add_comm]
    _ = ⨆ a ∈ s, (((B a y : ℝ) : EReal) + supportFn B t y) := by
        refine iSup_congr fun a => iSup_congr fun _ => ?_
        rw [supportFn_apply, ← EReal.biSup_add_coe, add_comm]
    _ = supportFn B s y + supportFn B t y := by
        rw [← EReal.biSup_add_of_ne_bot (u := fun a => ((B a y : ℝ) : EReal))
          fun a _ => EReal.coe_ne_bot _]
        rfl

end Defs

/-! ### Conjugates of positively homogeneous functions

The mechanism behind everything that follows, and it needs no topology: reindexing the supremum
that defines `f*` along `x ↦ a • x` shows that `f*(y)` is fixed by every positive scalar. -/

section PosHom

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- The set `{y | ∀ x, ⟨x, y⟩ ≤ f x}`. When `f` is closed, proper, convex and positively
homogeneous this is the set whose support function is `f` (`supportFn_supportSet`); in general it
is the effective domain of `f*`, viewed as an indicator. -/
def supportSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : Set F :=
  {y | ∀ x, ((B x y : ℝ) : EReal) ≤ f x}

@[simp] theorem mem_supportSet {y : F} :
    y ∈ supportSet B f ↔ ∀ x, ((B x y : ℝ) : EReal) ≤ f x := Iff.rfl

theorem supportSet_eq_setOf_conj_le (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) :
    supportSet B f = {y | conj B f y ≤ 0} := by
  ext y
  change (∀ x, ((B x y : ℝ) : EReal) ≤ f x) ↔ conj B f y ≤ 0
  rw [show ((0 : EReal)) = ((0 : ℝ) : EReal) from EReal.coe_zero.symm, conj_le_coe_iff,
    Pi.le_def]
  exact forall_congr' fun x => by rw [affineFn_apply, EReal.coe_zero, sub_zero]

theorem convex_supportSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : Convex ℝ (supportSet B f) := by
  rw [supportSet_eq_setOf_conj_le]
  exact (convexFn_conj B f).convex_le 0

/-- **The conjugate of a positively homogeneous function is fixed by every positive scalar**: the
substance of `f = λf ↔ f* = f*λ`, obtained by reindexing the defining supremum. -/
theorem conj_smul_eq_self (hf : PosHomogeneous f) {a : ℝ} (ha : 0 < a) (y : F) :
    conj B f y = (a : EReal) * conj B f y := by
  by_cases hb : ∃ x, f x = ⊥
  · obtain ⟨x₀, hx₀⟩ := hb
    rw [conj_of_eq_bot hx₀]
    exact (EReal.coe_mul_top_of_pos ha).symm
  push Not at hb
  have hterm : ∀ x : E, ((B (a • x) y : ℝ) : EReal) - f (a • x)
      = (a : EReal) * (((B x y : ℝ) : EReal) - f x) := by
    intro x
    rw [hf a ha x, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rcases eq_or_ne (f x) ⊤ with h | h
    · rw [h, EReal.coe_mul_top_of_pos ha, EReal.sub_top, EReal.sub_top,
        EReal.coe_mul_bot_of_pos ha]
    · obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hb x) (lt_top_iff_ne_top.2 h)
      rw [hr, ← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_sub,
        ← EReal.coe_mul]
      congr 1
      ring
  have hsurj : Function.Surjective fun x : E => a • x := fun z =>
    ⟨a⁻¹ • z, smul_inv_smul₀ ha.ne' z⟩
  have hre : (⨆ x : E, (((B (a • x) y : ℝ) : EReal) - f (a • x))) = conj B f y :=
    hsurj.iSup_comp fun z => ((B z y : ℝ) : EReal) - f z
  calc conj B f y = ⨆ x : E, (((B (a • x) y : ℝ) : EReal) - f (a • x)) := hre.symm
    _ = ⨆ x : E, (a : EReal) * (((B x y : ℝ) : EReal) - f x) := iSup_congr hterm
    _ = (a : EReal) * conj B f y := (EReal.coe_mul_iSup ha _).symm

/-- **The conjugate of a positively homogeneous function is an indicator function.** With
`supportFn_eq_conj_indicatorFn` this is the duality between positive homogeneity and being an
indicator that gauges and polarity rest on. The one hypothesis, `f ≢ +∞`, is genuinely needed:
`(+∞)* = -∞` is no indicator. -/
theorem conj_eq_indicatorFn_of_posHomogeneous (hf : PosHomogeneous f) (hne : ∃ x, f x ≠ ⊤) :
    conj B f = indicatorFn (supportSet B f) := by
  funext y
  have hval : conj B f y = 0 ∨ conj B f y = ⊤ := by
    rcases EReal.eq_zero_or_eq_top_or_eq_bot (a := 2) (by norm_num)
      (conj_smul_eq_self hf (by norm_num : (0 : ℝ) < 2) y).symm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · obtain ⟨x₀, hx₀⟩ := hne
      exact absurd (conj_eq_bot_iff.1 h x₀) hx₀
  have hiff : y ∈ supportSet B f ↔ conj B f y ≤ 0 := by
    rw [supportSet_eq_setOf_conj_le]; exact Iff.rfl
  by_cases hy : y ∈ supportSet B f
  · rw [indicatorFn_of_mem hy]
    rcases hval with h | h
    · exact h
    · exact absurd (hiff.1 hy) (by rw [h]; simp)
  · rw [indicatorFn_of_notMem hy]
    rcases hval with h | h
    · exact absurd (hiff.2 h.le) hy
    · exact h

end PosHom

/-! ### Closedness of the support function -/

section Closed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B.flip] {s : Set E}

theorem lowerSemicontinuous_supportFn : LowerSemicontinuous (supportFn B s) := by
  rw [supportFn_eq_conj_indicatorFn]; exact lowerSemicontinuous_conj

variable [IsTopologicalAddGroup F]

/-- **The support function of any set is a closed convex function** — it is a conjugate. -/
theorem closedFn_supportFn : ClosedFn (supportFn B s) := by
  rw [supportFn_eq_conj_indicatorFn]; exact closedFn_conj

end Closed

/-! ### The closure of the set -/

section ContinuousPairing

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B] {s : Set E}

theorem isClosed_setOf_pairing_le (y : F) (M : EReal) :
    IsClosed {x : E | ((B x y : ℝ) : EReal) ≤ M} :=
  isClosed_Iic.preimage (EReal.continuous_coe_iff.2 (continuous_pairing B y))

/-- **The support function does not see the closure.** -/
theorem supportFn_closure (s : Set E) : supportFn B (closure s) = supportFn B s := by
  funext y
  refine le_antisymm (iSup₂_le fun x hx => ?_) (supportFn_mono subset_closure y)
  exact closure_minimal (fun z hz => le_supportFn hz y)
    (isClosed_setOf_pairing_le y (supportFn B s y)) hx

theorem isClosed_supportSet (g : F → EReal) : IsClosed (supportSet B.flip g) := by
  rw [supportSet_eq_setOf_conj_le,
    show ((0 : EReal)) = ((0 : ℝ) : EReal) from EReal.coe_zero.symm]
  exact lowerSemicontinuous_iff_isClosed_le.1 (lowerSemicontinuous_conj (B := B.flip)) 0

end ContinuousPairing

/-! ### The closed convex hull -/

section ClosedConvexHull

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B]

/-- A point lies in the closed convex hull of `s` if and only if it satisfies every weak linear
inequality that the support function of `s` records. -/
theorem mem_closure_convexHull_iff_le_supportFn (s : Set E) (x : E) :
    x ∈ closure (convexHull ℝ s) ↔ ∀ y : F, ((B x y : ℝ) : EReal) ≤ supportFn B s y := by
  rw [← closure_convexHull_eq_iInter_halfspaces s]
  simp only [Set.mem_iInter, Set.mem_ofPred]
  constructor
  · intro h y
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨c, hc₁, hc₂⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    have hbnd : ∀ z ∈ s, evalCLM B y z ≤ c := supportFn_le_coe_iff.1 hc₁.le
    have hx := h (evalCLM B y) c hbnd
    rw [evalCLM_apply] at hx
    exact absurd hc₂ (not_lt.2 (by exact_mod_cast hx))
  · intro h g c hg
    obtain ⟨y, hy⟩ := exists_pairing_eq B g
    have hsup : supportFn B s y ≤ (c : EReal) :=
      supportFn_le_coe_iff.2 fun z hz => hy z ▸ hg z hz
    rw [hy x]
    exact_mod_cast (h y).trans hsup

/-- Closed convex hulls are ordered by their support functions. -/
theorem closure_convexHull_subset_iff_supportFn_le (s t : Set E) :
    closure (convexHull ℝ s) ⊆ closure (convexHull ℝ t) ↔ supportFn B s ≤ supportFn B t := by
  constructor
  · intro h y
    have h' := supportFn_mono (B := B) h y
    rwa [supportFn_closure, supportFn_convexHull, supportFn_closure,
      supportFn_convexHull] at h'
  · intro h x hx
    rw [mem_closure_convexHull_iff_le_supportFn (B := B)] at hx ⊢
    exact fun y => (hx y).trans (h y)

end ClosedConvexHull

/-! ### The closure of a positively homogeneous convex function

Only the space `F` carries a topology here: this is `biconj_eq_clFn` for the *flipped* pairing. -/

section PosHomClosure

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B.flip] {g : F → EReal}

/-- The closure of a positively homogeneous convex function that is not identically `+∞` is the
support function of the closed convex set
`supportSet B.flip g = {x | ∀ y, ⟨x, y⟩ ≤ g y}`.

The improper case is included: if `g` takes `-∞` then both sides are the support function of `∅`. -/
theorem clFn_eq_supportFn_of_posHomogeneous
    (hg : PosHomogeneous g) (hconv : ConvexFn g) (hne : ∃ y, g y ≠ ⊤) :
    clFn g = supportFn B (supportSet B.flip g) := by
  rw [supportFn_eq_conj_indicatorFn,
    ← conj_eq_indicatorFn_of_posHomogeneous (B := B.flip) hg hne]
  exact (biconj_eq_clFn (B := B.flip) hconv).symm

omit [LocallyConvexSpace ℝ F] in
/-- **Taking the closure of a positively homogeneous function does not change the set it
supports**: the two conjugates agree and both are indicators, so the two supported sets agree.
Convexity of `g` is not needed. -/
theorem supportSet_clFn (hg : PosHomogeneous g) (hne : ∃ y, g y ≠ ⊤) :
    supportSet B.flip (clFn g) = supportSet B.flip g := by
  obtain ⟨w, hw⟩ := hne
  have hne' : ∃ y, clFn g y ≠ ⊤ := ⟨w, fun h => hw (top_le_iff.1 (h ▸ clFn_le g w))⟩
  have h₁ := conj_eq_indicatorFn_of_posHomogeneous (B := B.flip) hg ⟨w, hw⟩
  have h₂ := conj_eq_indicatorFn_of_posHomogeneous (B := B.flip) (posHomogeneous_clFn hg) hne'
  rw [conj_clFn, h₁] at h₂
  rw [← dom_indicatorFn (supportSet B.flip (clFn g)), ← h₂, dom_indicatorFn]

/-- A closed positively homogeneous convex function *is* the support function of
`supportSet B.flip g`. -/
theorem supportFn_supportSet (hg : PosHomogeneous g) (hconv : ConvexFn g) (hcl : ClosedFn g)
    (hne : ∃ y, g y ≠ ⊤) : supportFn B (supportSet B.flip g) = g :=
  (clFn_eq_supportFn_of_posHomogeneous hg hconv hne).symm.trans hcl

theorem nonempty_supportSet (hg : PosHomogeneous g) (hcpc : ClosedProperConvexFn g) :
    (supportSet B.flip g).Nonempty := by
  obtain ⟨y₀, hy₀⟩ := hcpc.proper.dom_nonempty
  have hg' := supportFn_supportSet (B := B) hg hcpc.convex hcpc.closed ⟨y₀, hy₀.ne⟩
  rcases (supportSet B.flip g).eq_empty_or_nonempty with hemp | hne
  · rw [hemp, supportFn_empty] at hg'
    exact absurd (congrFun hg' y₀).symm (hcpc.proper.ne_bot y₀)
  · exact hne

end PosHomClosure

/-! ### Sets and their support functions, in bijection

Both spaces carry topologies compatible with the pairing, exactly as for `conjEquiv`. -/

section SupportCorrespondence

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s : Set E} {g : F → EReal}

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] in
/-- **The indicator and the support function are conjugate** to each other, for a closed convex
set. -/
theorem conj_supportFn [IsCompatiblePairing B] (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) :
    conj B.flip (supportFn B s) = indicatorFn s := by
  rw [supportFn_eq_conj_indicatorFn]
  change biconj B (indicatorFn s) = indicatorFn s
  rw [biconj_eq_clFn (convexFn_indicatorFn.2 hs₁), clFn_indicatorFn, hs₂.closure_eq]

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] in
/-- The same with the closedness hypothesis dropped: the conjugate of a support function
is the indicator of the *closure* of the set. This is the form a closedness *conclusion* is read
off from, `dom` of the left side being `cl s`. -/
theorem conj_supportFn_of_convex [IsCompatiblePairing B] (hs₁ : Convex ℝ s) :
    conj B.flip (supportFn B s) = indicatorFn (closure s) := by
  rw [supportFn_eq_conj_indicatorFn]
  change biconj B (indicatorFn s) = indicatorFn (closure s)
  rw [biconj_eq_clFn (convexFn_indicatorFn.2 hs₁), clFn_indicatorFn]

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] in
/-- **A closed convex set is recovered from its support function.** -/
theorem supportSet_supportFn [IsCompatiblePairing B] (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) :
    supportSet B.flip (supportFn B s) = s := by
  ext x
  simp only [mem_supportSet, LinearMap.flip_apply]
  rw [← mem_closure_convexHull_iff_le_supportFn, hs₁.convexHull_eq, hs₂.closure_eq]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- **The characterisation**: the support functions of the nonempty convex sets are exactly the
closed proper positively homogeneous convex functions.

Stated for the nonempty *closed convex* sets, which give the same functions since the support
function sees neither the closure nor the convex hull, so that the correspondence is one-to-one. -/
theorem exists_supportFn_iff [IsContinuousPairing B] [IsCompatiblePairing B.flip] :
    (∃ C : Set E, C.Nonempty ∧ Convex ℝ C ∧ IsClosed C ∧ g = supportFn B C) ↔
      (ClosedProperConvexFn g ∧ PosHomogeneous g) := by
  constructor
  · rintro ⟨C, hne, -, -, rfl⟩
    exact ⟨⟨convexFn_supportFn B C, closedFn_supportFn, proper_supportFn hne⟩,
      posHomogeneous_supportFn B C⟩
  · rintro ⟨hcpc, hph⟩
    obtain ⟨y₀, hy₀⟩ := hcpc.proper.dom_nonempty
    have hg : supportFn B (supportSet B.flip g) = g :=
      supportFn_supportSet hph hcpc.convex hcpc.closed ⟨y₀, hy₀.ne⟩
    exact ⟨supportSet B.flip g, nonempty_supportSet hph hcpc,
      convex_supportSet B.flip g, isClosed_supportSet g, hg.symm⟩

/-- **The correspondence as a bijection** between the nonempty closed convex sets and the closed
proper positively homogeneous convex functions: the restriction of `conjEquiv` along the embeddings
`s ↦ δ(· | s)` and "positively homogeneous". -/
noncomputable def supportEquiv (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] :
    {C : Set E // C.Nonempty ∧ Convex ℝ C ∧ IsClosed C} ≃
      {g : F → EReal // ClosedProperConvexFn g ∧ PosHomogeneous g} where
  toFun C := ⟨supportFn B C.1, ⟨convexFn_supportFn B C.1, closedFn_supportFn,
    proper_supportFn C.2.1⟩, posHomogeneous_supportFn B C.1⟩
  invFun g := ⟨supportSet B.flip g.1, nonempty_supportSet g.2.2 g.2.1,
    convex_supportSet B.flip g.1, isClosed_supportSet g.1⟩
  left_inv C := Subtype.ext (supportSet_supportFn C.2.2.1 C.2.2.2)
  right_inv g := Subtype.ext <| by
    obtain ⟨y₀, hy₀⟩ := g.2.1.proper.dom_nonempty
    exact supportFn_supportSet g.2.2 g.2.1.convex g.2.1.closed ⟨y₀, hy₀.ne⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- The support functions of the nonempty sets on which every `⟨·, y⟩` is bounded above are
exactly the *finite closed* positively homogeneous convex functions.

The book has no `ClosedFn` hypothesis; it is needed outside finite dimensions, where a
discontinuous linear functional is finite, convex, positively homogeneous and not closed. -/
theorem exists_supportFn_finite_iff [IsContinuousPairing B] [IsCompatiblePairing B.flip] :
    (∃ C : Set E, C.Nonempty ∧ (∀ y : F, ∃ c : ℝ, ∀ x ∈ C, B x y ≤ c) ∧ g = supportFn B C) ↔
      ((∀ y, g y ≠ ⊥) ∧ (∀ y, g y ≠ ⊤) ∧ ConvexFn g ∧ ClosedFn g ∧ PosHomogeneous g) := by
  constructor
  · rintro ⟨C, hne, hbdd, rfl⟩
    exact ⟨supportFn_ne_bot hne, fun y => (supportFn_lt_top_iff.2 (hbdd y)).ne,
      convexFn_supportFn B C, closedFn_supportFn, posHomogeneous_supportFn B C⟩
  · rintro ⟨hb, ht, hconv, hcl, hph⟩
    have hp : Proper g := ⟨⟨0, lt_top_iff_ne_top.2 (ht 0)⟩, hb⟩
    obtain ⟨C, hne, -, -, hg⟩ :=
      (exists_supportFn_iff (B := B)).2 ⟨⟨hconv, hcl, hp⟩, hph⟩
    refine ⟨C, hne, fun y => supportFn_lt_top_iff.1 ?_, hg⟩
    rw [← hg]
    exact lt_top_iff_ne_top.2 (ht y)

end SupportCorrespondence

end ConvexAnalysis
