import Numlib.Analysis.Convex.Duality.InnerPairing
import Numlib.Analysis.Convex.Duality.RelintSeparation

/-!
# Convex analysis on a finite product

A finite product `ι → E` carries a pairing, a notion of product set, and — once `E` is
finite-dimensional — a relative interior, and all three are computed coordinatewise. This file
establishes that dictionary and then reads one theorem through it: a finite family of convex sets
has a common relative-interior point exactly when a certain family of dual vectors summing to zero
does not exist.

## Main definitions

* `piPairing B` — the pairing of `ι → E` with `ι → F` given by `⟨x, y⟩ = ∑ i, ⟨xᵢ, yᵢ⟩`, together
  with the four pairing classes as instances. It is to `Set.pi` what `prodPairing` is to `×ˢ`.

## Main results

* `supportFn_univ_pi` — the support function of a product set is the sum of the support functions
  of the factors.
* `conj_piFn` — the conjugate of a separable sum of proper functions is the separable sum of the
  conjugates, `(∑ i, fᵢ ∘ prᵢ)* = ∑ i, fᵢ* ∘ prᵢ`.
* `iInter_relint_nonempty_iff_supportFn`, `iInter_relint_dom_nonempty_iff` — a finite family of
  convex sets (resp. of effective domains) has a common relative-interior point exactly when there
  is no family `y` with `∑ i, yᵢ = 0`, `∑ i, δ*(yᵢ ∣ Cᵢ) ≤ 0` and `∑ i, δ*(-yᵢ ∣ Cᵢ) > 0`
  (Corollary 16.2.2 in [^1]). The diagonal `{x ∣ x₁ = ⋯ = xₘ}` is a subspace of `ι → E` whose
  annihilator under the product pairing is the family of `y` summing to zero, so this is the
  subspace criterion of `Duality/RelintSeparation.lean` read at a product set.

## Implementation notes

`piPairing` sums over `Finset.univ`, so the index has to be a `Fintype`. The product is
non-dependent because the diagonal subspace needs all the factors to be the same space; the
`Set.pi` results would hold verbatim for a dependent product.

`⊥` absorbs, so `supportFn_univ_pi` needs no nonemptiness hypothesis — but its two sides are `⊥`
for different reasons when a factor is empty, and the proof splits. The nonempty branch is an
induction over the index `Finset` whose step decouples one coordinate with `Function.update`.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §16, §6 and §13.
-/

open Set

namespace ConvexAnalysis

/-! ### The pairing of a finite product -/

section Pairing

variable {ι E F : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **The pairing of `ι → E` with `ι → F`**, `⟨x, y⟩ = ∑ i, ⟨xᵢ, yᵢ⟩`: `prodPairing` for a finite
family, and the pairing under which a product of sets has a separable support function. -/
def piPairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : (ι → E) →ₗ[ℝ] (ι → F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i, B (x i) (y i))
    (fun _ _ _ => by simp [← Finset.sum_add_distrib])
    (fun _ _ _ => by simp [Finset.mul_sum])
    (fun _ _ _ => by simp [← Finset.sum_add_distrib])
    (fun _ _ _ => by simp [Finset.mul_sum])

@[simp] theorem piPairing_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (x : ι → E) (y : ι → F) :
    piPairing B x y = ∑ i, B (x i) (y i) := rfl

/-- Flipping the product pairing flips the pairing of the factors. -/
theorem piPairing_flip (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    (piPairing (ι := ι) B).flip = piPairing B.flip :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => by simp

end Pairing

section PairingInstances

variable {ι E F : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F]

/-- A finite product of copies of a continuous pairing is continuous. -/
instance instIsContinuousPairingPi (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsContinuousPairing B] :
    IsContinuousPairing (piPairing (ι := ι) B) where
  continuous_left y := by
    simp only [piPairing_apply]
    exact continuous_finsetSum _ fun i _ => (continuous_pairing B (y i)).comp (continuous_apply i)

/-- A finite product of copies of a compatible pairing is compatible. -/
instance instIsCompatiblePairingPi (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B] :
    IsCompatiblePairing (piPairing (ι := ι) B) where
  toIsContinuousPairing := instIsContinuousPairingPi B
  surjective_eval g := by
    classical
    choose y hy using fun i : ι =>
      exists_pairing_eq B (g.comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) i))
    refine ⟨y, ContinuousLinearMap.ext fun x => ?_⟩
    rw [evalCLM_apply, piPairing_apply,
      ← ContinuousLinearMap.sum_comp_single ℝ (fun _ : ι => E) g x]
    exact Finset.sum_congr rfl fun i _ => (hy i (x i)).symm

end PairingInstances

section InnerInstances

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ}

/-- A finite product of copies of an inner pairing is an inner pairing. The product carries no
inner-product structure of its own, but the pairing does not care. -/
instance isInnerPairing_piPairing [IsInnerPairing B] : IsInnerPairing (piPairing (ι := ι) B) where
  pairing_comm _ _ := Finset.sum_congr rfl fun i _ => pairing_comm B _ _
  self_nonneg _ := Finset.sum_nonneg fun i _ => self_pairing_nonneg B _
  eq_zero_of_self_eq_zero x h := by
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      fun i _ => self_pairing_nonneg B (x i)).1 h
    funext i
    exact self_pairing_eq_zero_iff.1 (hzero i (Finset.mem_univ i))

/-- The quadratic form of a finite product of inner pairings is continuous. -/
instance isContinuousInnerPairing_piPairing [TopologicalSpace E] [IsContinuousInnerPairing B] :
    IsContinuousInnerPairing (piPairing (ι := ι) B) where
  continuous_self :=
    continuous_finsetSum _ fun i _ => (continuous_self_pairing' B).comp (continuous_apply i)

end InnerInstances

/-! ### The relative interior of a product set -/

section Relint

variable {ι E : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

end Relint

/-! ### The support function of a product set

The supremum of a separable sum over a product of sets is the sum of the suprema. -/

section Support

variable {ι E F : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

omit [Fintype ι] [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] in
/-- The supremum over a product set of a sum indexed by a `Finset`, decoupled coordinate by
coordinate. The values are only asked to avoid `⊥` *on the sets*; nonemptiness is needed only for
the empty `Finset`, where the supremum of the constant `0` has to be `0` rather than `⊥`. -/
private theorem biSup_sum_univ_pi {C : ι → Set E} (hne : ∀ i, (C i).Nonempty) (u : ι → E → EReal)
    (hu : ∀ i, ∀ z ∈ C i, u i z ≠ ⊥) (t : Finset ι) :
    (⨆ x ∈ univ.pi C, ∑ i ∈ t, u i (x i)) = ∑ i ∈ t, ⨆ z ∈ C i, u i z := by
  classical
  obtain ⟨x₀, hx₀⟩ : (univ.pi C).Nonempty := Set.univ_pi_nonempty_iff.2 hne
  induction t using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact le_antisymm (iSup₂_le fun _ _ => le_rfl)
      (le_iSup₂_of_le (f := fun x (_ : x ∈ univ.pi C) => (0 : EReal)) x₀ hx₀ le_rfl)
  | cons i t hi ih =>
    have hgne : ∀ x ∈ univ.pi C, (∑ j ∈ t, u j (x j)) ≠ ⊥ := fun x hx =>
      EReal.sum_ne_bot fun j _ => hu j (x j) (hx j (mem_univ j))
    have key : (⨆ x ∈ univ.pi C, (u i (x i) + ∑ j ∈ t, u j (x j)))
        = (⨆ z ∈ C i, u i z) + ⨆ x ∈ univ.pi C, ∑ j ∈ t, u j (x j) := by
      rw [EReal.biSup_add_biSup (hu i) hgne]
      refine le_antisymm (iSup₂_le fun x hx => ?_) (iSup₂_le fun z hz => iSup₂_le fun x hx => ?_)
      · exact le_iSup₂_of_le (x i) (hx i (mem_univ i)) (le_iSup₂_of_le x hx le_rfl)
      · refine le_iSup₂_of_le (Function.update x i z) (fun j _ => ?_) ?_
        · rcases eq_or_ne j i with rfl | hj
          · rw [Function.update_self]; exact hz
          · rw [Function.update_of_ne hj]; exact hx j (mem_univ j)
        · have hsum : ∑ j ∈ t, u j (Function.update x i z j) = ∑ j ∈ t, u j (x j) :=
            Finset.sum_congr rfl fun j hj => by
              rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
          rw [Function.update_self, hsum]
    simp only [Finset.sum_cons]
    rw [key, ih]

/-- **The support function of a product set is the sum of the support functions of its factors**,
with no hypothesis. If some factor is empty both sides are `⊥`. -/
theorem supportFn_univ_pi (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : ι → Set E) (y : ι → F) :
    supportFn (piPairing B) (univ.pi C) y = ∑ i, supportFn B (C i) (y i) := by
  classical
  by_cases hne : ∀ i, (C i).Nonempty
  · have hcoe : ∀ x : ι → E,
        ((piPairing B x y : ℝ) : EReal) = ∑ i, ((B (x i) (y i) : ℝ) : EReal) := fun x => by
      rw [piPairing_apply, EReal.coe_sum]
    rw [supportFn_apply]
    simp only [hcoe, supportFn_apply]
    exact biSup_sum_univ_pi hne (fun i z => ((B z (y i) : ℝ) : EReal))
      (fun i z _ => EReal.coe_ne_bot _) Finset.univ
  · simp only [not_forall, Set.not_nonempty_iff_eq_empty] at hne
    obtain ⟨i₀, hi₀⟩ := hne
    have hempty : univ.pi C = ∅ := Set.univ_pi_eq_empty_iff.2 ⟨i₀, hi₀⟩
    rw [← Finset.add_sum_erase _ (fun i => supportFn B (C i) (y i)) (Finset.mem_univ i₀), hi₀]
    simp only [hempty, supportFn_empty]
    exact (EReal.bot_add _).symm

end Support

/-! ### The conjugate of a separable sum

The other half of the finite-product dictionary. `⟨x, y⟩ - ∑ fᵢ (xᵢ)` splits as
`∑ (⟨xᵢ, yᵢ⟩ - fᵢ (xᵢ))` only once the `⊤` case is disposed of, which `⊥` absorbing does. -/

section SeparableAux

/-- A supremum is unchanged by restricting to a set off which the function is `⊥`. -/
private theorem iSup_eq_biSup_of_notMem {α : Type*} {s : Set α} {w : α → EReal}
    (h : ∀ a ∉ s, w a = ⊥) : (⨆ a, w a) = ⨆ a ∈ s, w a := by
  refine le_antisymm (iSup_le fun a => ?_) (iSup₂_le fun a _ => le_iSup w a)
  by_cases ha : a ∈ s
  · exact le_iSup₂_of_le a ha le_rfl
  · rw [h a ha]
    exact bot_le

/-- A `Finset` sum with a `⊥` term is `⊥`: on `EReal` addition, `⊥` absorbs `⊤`. -/
private theorem sum_eq_bot_of_mem {ι : Type*} {v : ι → EReal} {t : Finset ι} {j : ι} (hj : j ∈ t)
    (h : v j = ⊥) : (∑ k ∈ t, v k) = ⊥ := by
  classical
  rw [← Finset.add_sum_erase t v hj, h, EReal.bot_add]

/-- A real minuend distributes over a two-term subtrahend, provided neither term is `⊥`. Both `⊤`
cases come out `⊥` on each side, which is why no finiteness is needed. -/
private theorem coe_add_sub_add (a b : ℝ) {p q : EReal} (hp : p ≠ ⊥) (hq : q ≠ ⊥) :
    ((a + b : ℝ) : EReal) - (p + q) = (((a : ℝ) : EReal) - p) + (((b : ℝ) : EReal) - q) := by
  induction p with
  | bot => exact absurd rfl hp
  | top =>
    rw [EReal.top_add_of_ne_bot hq, EReal.sub_top, EReal.sub_top,
      EReal.bot_add]
  | coe r =>
    induction q with
    | bot => exact absurd rfl hq
    | top =>
      rw [EReal.add_top_of_ne_bot (EReal.coe_ne_bot r), EReal.sub_top,
        EReal.sub_top, EReal.add_bot]
    | coe s =>
      simp only [← EReal.coe_add, ← EReal.coe_sub]
      rw [EReal.coe_eq_coe_iff]
      ring

/-- The `Finset` form of `coe_add_sub_add`: a real minuend distributes over a finite sum of
subtrahends none of which is `⊥`. -/
private theorem coe_sum_sub_sum {ι : Type*} (c : ι → ℝ) (v : ι → EReal) (t : Finset ι)
    (hv : ∀ j, v j ≠ ⊥) :
    ((∑ j ∈ t, c j : ℝ) : EReal) - ∑ j ∈ t, v j
      = ∑ j ∈ t, (((c j : ℝ) : EReal) - v j) := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons j t hj ih =>
    rw [Finset.sum_cons, Finset.sum_cons, Finset.sum_cons, ← ih]
    exact coe_add_sub_add (c j) (∑ k ∈ t, c k) (hv j) (EReal.sum_ne_bot fun k _ => hv k)

end SeparableAux

section Separable

variable {ι E F : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **The conjugate of a separable sum is the separable sum of the conjugates.** For a finite
family of proper functions, `(∑ i, fᵢ ∘ prᵢ)* = ∑ i, fᵢ* ∘ prᵢ` against `piPairing B`.

Properness keeps the two sides from colliding at `∞ - ∞`: it lets the supremum defining `fᵢ*` be
taken over `dom fᵢ`, and it keeps `fᵢ* yᵢ` off `⊥`, so no summand on the right can absorb. -/
theorem conj_piFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : ι → E → EReal) (hf : ∀ i, Proper (f i))
    (y : ι → F) :
    conj (piPairing B) (fun x => ∑ i, f i (x i)) y = ∑ i, conj B (f i) (y i) := by
  have hbot : ∀ i z, f i z ≠ ⊥ := fun i z => (hf i).ne_bot z
  have hoff : ∀ i, ∀ z ∉ dom (f i), (((B z (y i) : ℝ) : EReal) - f i z) = ⊥ := by
    intro i z hz
    have hz' : ¬ (f i z < ⊤) := hz
    rw [top_le_iff.1 (not_lt.1 hz'), EReal.sub_top]
  have hval : ∀ i, ∀ z ∈ dom (f i), (((B z (y i) : ℝ) : EReal) - f i z) ≠ ⊥ := by
    intro i z hz
    obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hbot i z) hz
    rw [hr, ← EReal.coe_sub]
    exact EReal.coe_ne_bot _
  have hcoord : ∀ i, conj B (f i) (y i)
      = ⨆ z ∈ dom (f i), (((B z (y i) : ℝ) : EReal) - f i z) :=
    fun i => iSup_eq_biSup_of_notMem (hoff i)
  have hsplit : ∀ x : ι → E, ((piPairing B x y : ℝ) : EReal) - (∑ i, f i (x i))
      = ∑ i, (((B (x i) (y i) : ℝ) : EReal) - f i (x i)) := by
    intro x
    rw [piPairing_apply]
    exact coe_sum_sub_sum (fun i => B (x i) (y i)) (fun i => f i (x i)) Finset.univ
      fun i => hbot i (x i)
  have hprod : conj (piPairing B) (fun x => ∑ i, f i (x i)) y
      = ⨆ x ∈ univ.pi fun i => dom (f i), ∑ i, (((B (x i) (y i) : ℝ) : EReal) - f i (x i)) := by
    rw [conj_apply]
    simp only [hsplit]
    refine iSup_eq_biSup_of_notMem fun x hx => ?_
    obtain ⟨i₀, -, hi₀⟩ : ∃ i₀ ∈ (univ : Set ι), x i₀ ∉ dom (f i₀) := by
      simpa [Set.mem_pi] using hx
    exact sum_eq_bot_of_mem (Finset.mem_univ i₀) (hoff i₀ (x i₀) hi₀)
  rw [hprod]
  simp only [hcoord]
  exact biSup_sum_univ_pi (fun i => (hf i).dom_nonempty)
    (fun i z => ((B z (y i) : ℝ) : EReal) - f i z) hval Finset.univ

end Separable

/-! ### A common relative interior point of a finite family

The diagonal `{x | x₁ = ⋯ = xₘ}` is a subspace of `ι → E` whose annihilator, under the product
pairing, is the family of `y` summing to zero. -/

section Diagonal

variable {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}
  [IsCompatiblePairing B]

/-- **A finite family of convex sets has a common relative interior point** exactly when there is
no family `y` of dual vectors summing to zero with `∑ i, δ*(yᵢ | Cᵢ) ≤ 0 < ∑ i, δ*(-yᵢ | Cᵢ)`.

This is `submodule_inter_relint_nonempty_iff_supportFn` in `ι → E` at the diagonal subspace and the
product set `∏ Cᵢ`. Separation on the right of the pairing is what turns the annihilator of the
diagonal into `∑ i, yᵢ = 0`. -/
theorem iInter_relint_nonempty_iff_supportFn (hB : B.SeparatingRight) (C : ι → Set E)
    (hC : ∀ i, Convex ℝ (C i)) (hne : ∀ i, (C i).Nonempty) :
    (⋂ i, ri (C i)).Nonempty ↔
      ¬ ∃ y : ι → F, (∑ i, y i = 0) ∧ (∑ i, supportFn B (C i) (y i)) ≤ 0 ∧
        0 < ∑ i, supportFn B (C i) (-(y i)) := by
  obtain ⟨L, hL⟩ : ∃ L : Submodule ℝ (ι → E), ∀ x : ι → E, x ∈ L ↔ ∃ z : E, ∀ i, x i = z := by
    refine ⟨LinearMap.range (LinearMap.pi fun _ : ι => LinearMap.id), fun x => ?_⟩
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, fun _ => rfl⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, funext fun i => (hz i).symm⟩
  have hstep := submodule_inter_relint_nonempty_iff_supportFn (B := piPairing B) L
    (convex_pi fun i _ => hC i) (Set.univ_pi_nonempty_iff.2 hne)
  rw [Convex.relint_univ_pi C hC] at hstep
  simp only [supportFn_univ_pi, Pi.neg_apply] at hstep
  have hleft : ((L : Set (ι → E)) ∩ univ.pi fun i => ri (C i)).Nonempty
      ↔ (⋂ i, ri (C i)).Nonempty := by
    constructor
    · rintro ⟨x, hxL, hxpi⟩
      obtain ⟨z, hz⟩ := (hL x).1 hxL
      refine ⟨z, mem_iInter.2 fun i => ?_⟩
      have hmem := hxpi i (mem_univ i)
      rwa [hz i] at hmem
    · rintro ⟨z, hz⟩
      rw [mem_iInter] at hz
      exact ⟨fun _ => z, (hL _).2 ⟨z, fun _ => rfl⟩, fun i _ => hz i⟩
  have hann : ∀ y : ι → F, (∀ x ∈ L, piPairing B x y = 0) ↔ ∑ i, y i = 0 := by
    intro y
    constructor
    · intro h
      refine hB _ fun z => ?_
      have hz := h (fun _ => z) ((hL _).2 ⟨z, fun _ => rfl⟩)
      rw [piPairing_apply] at hz
      rw [map_sum]
      exact hz
    · intro h x hx
      obtain ⟨z, hz⟩ := (hL x).1 hx
      have hval : ∑ i, B (x i) (y i) = B z (∑ i, y i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hz i]
      rw [piPairing_apply, hval, h, map_zero]
  rw [← hleft, hstep]
  exact not_congr (exists_congr fun y => and_congr_left' (hann y))

/-- **A finite family of proper convex functions has a common relative interior point of their
effective domains** exactly when there is no family `y` summing to zero with
`∑ i, (fᵢ* 0⁺)(yᵢ) ≤ 0 < ∑ i, (fᵢ* 0⁺)(-yᵢ)`: the previous statement at `Cᵢ = dom fᵢ`, whose
support function is the recession function of `fᵢ*`. -/
theorem iInter_relint_dom_nonempty_iff (hB : B.SeparatingRight) (f : ι → E → EReal)
    (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, Proper (f i)) (hc : ∀ i, Proper (conj B (f i))) :
    (⋂ i, ri (dom (f i))).Nonempty ↔
      ¬ ∃ y : ι → F, (∑ i, y i = 0) ∧ (∑ i, recessionFn (conj B (f i)) (y i)) ≤ 0 ∧
        0 < ∑ i, recessionFn (conj B (f i)) (-(y i)) := by
  have hrec : ∀ i, recessionFn (conj B (f i)) = supportFn B (dom (f i)) :=
    fun i => recessionFn_conj (hp i) (hc i)
  simp only [hrec]
  exact iInter_relint_nonempty_iff_supportFn hB _ (fun i => (hf i).convex_dom)
    fun i => (hp i).dom_nonempty

end Diagonal

end ConvexAnalysis
