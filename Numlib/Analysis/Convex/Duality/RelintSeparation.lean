import Numlib.Analysis.Convex.Duality.Relint

/-!
# When a subspace meets a relative interior

The constraint qualifications of the exactness theory — "the range of `A` meets `ri (dom g)`", "the
effective domains have a common relative interior point" — are *primal* conditions. This file turns
them into dual ones: statements about the directions of the pairing in which the sets are bounded.

The engine is proper separation. Two nonempty convex sets have disjoint relative interiors exactly
when some hyperplane separates them properly, and over a compatible pairing the separating
functional is `⟨·, y⟩` for a `y` of the second space; the two conditions defining proper separation
then read as two inequalities between values of the pairing. When one of the two sets is a
*subspace* `L`, a direction in which the pairing is bounded on `L` is one in which it vanishes on
`L`, so both extrema over `L` collapse to `0` and the condition becomes a statement about a single
set together with the annihilator of `L`.

## Main results

* `exists_pairing_le_iff_disjoint_relint` — proper separation over a pairing: `ri C₁` and `ri C₂`
  are disjoint exactly when the pairing with some `y` is nowhere larger on `C₁` than on `C₂` and is
  strictly smaller somewhere.
* `submodule_inter_relint_nonempty_iff`, `submodule_inter_relint_nonempty_iff_supportFn` — the
  subspace case, pointwise and through the support function.
* `submodule_inter_relint_dom_nonempty_iff` — the effective-domain case, with the support function
  of `dom f` rewritten as the recession function of `f*` (Lemma 16.2 in [^1]).
* `exists_apply_mem_relint_dom_iff` — the same for the range of a linear map, whose annihilator on
  the other side of the pairing is the kernel of the adjoint (Corollary 16.2.1 in [^1]).

## Implementation notes

The general statement is written with pointwise inequalities `⟨x₁, y⟩ ≤ ⟨x₂, y⟩`, which mention no
`EReal`; the support function appears only once one of the two sets is a subspace, where two of the
four extrema of the proper-separation criterion become `0`.

Only `E` is topologised: proper separation happens there and needs finite dimension, while `F`
enters through `IsCompatiblePairing` alone and is a bare module. `Proper (conj B f)` is a
hypothesis rather than a conclusion, following `recessionFn_conj`; a caller in finite dimensions
discharges it with `proper_conj_of_proper`.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §16, §11 and §13.
-/

open Set

namespace ConvexAnalysis

/-! ### Boundedness on a subspace -/

section Support

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {y : F}

/-- **A linear function bounded above on a subspace vanishes on it.** A subspace is closed under
arbitrary real scaling, so a single nonzero value would make the pairing unbounded. -/
theorem forall_pairing_eq_zero_of_forall_le {L : Submodule ℝ E} {c : ℝ}
    (h : ∀ x ∈ L, B x y ≤ c) : ∀ x ∈ L, B x y = 0 := by
  intro x hx
  by_contra hne
  have hmem : ((c + 1) / B x y) • x ∈ L := L.smul_mem _ hx
  have hbound := h _ hmem
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hne] at hbound
  linarith

end Support

/-! ### A subspace is relatively open -/

section Relint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The relative interior of a subspace is the subspace itself. -/
theorem intrinsicInterior_coe_submodule (L : Submodule ℝ E) : ri (L : Set E) = (L : Set E) :=
  AffineSubspace.intrinsicInterior_coe (L : AffineSubspace ℝ E)

end Relint

/-! ### Proper separation, read through the pairing -/

section Separation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {C C₁ C₂ : Set E}

/-- **Proper separation over a pairing.** Two nonempty convex sets have disjoint relative interiors
exactly when the pairing with some `y` is nowhere larger on `C₁` than on `C₂` and is strictly
smaller at one pair of points. -/
theorem exists_pairing_le_iff_disjoint_relint (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂)
    (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) :
    (∃ y : F, (∀ x₁ ∈ C₁, ∀ x₂ ∈ C₂, B x₁ y ≤ B x₂ y) ∧
        ∃ x₁ ∈ C₁, ∃ x₂ ∈ C₂, B x₁ y < B x₂ y) ↔ Disjoint (ri C₁) (ri C₂) := by
  rw [← exists_separatesProperly_iff_disjoint_relint h₁ h₂ hne₁ hne₂]
  constructor
  · rintro ⟨y, hle, x₁, hx₁, x₂, hx₂, hlt⟩
    refine ⟨evalCLM B y, ?_⟩
    rw [exists_separatesProperly_iff_iSup_le_iInf hne₁ hne₂]
    constructor
    · refine iSup₂_le fun a ha => le_iInf₂ fun b hb => ?_
      have hab : evalCLM B y a ≤ evalCLM B y b := hle a ha b hb
      exact_mod_cast hab
    · have hlt' : evalCLM B y x₁ < evalCLM B y x₂ := hlt
      calc (⨅ x ∈ C₁, ((evalCLM B y x : ℝ) : EReal))
          ≤ ((evalCLM B y x₁ : ℝ) : EReal) := iInf₂_le_coe_apply hx₁
        _ < ((evalCLM B y x₂ : ℝ) : EReal) := by exact_mod_cast hlt'
        _ ≤ ⨆ x ∈ C₂, ((evalCLM B y x : ℝ) : EReal) := coe_apply_le_iSup₂ hx₂
  · rintro ⟨g, c, hsep⟩
    obtain ⟨y, hy⟩ := exists_pairing_eq B g
    have hle : ∀ x₁ ∈ C₁, ∀ x₂ ∈ C₂, B x₁ y ≤ B x₂ y := by
      intro x₁ hx₁ x₂ hx₂
      have h₁ : g x₁ ≤ c := hsep.le_of_mem_left hx₁
      have h₂ : c ≤ g x₂ := hsep.le_of_mem_right hx₂
      rw [hy x₁] at h₁
      rw [hy x₂] at h₂
      linarith
    obtain ⟨q, hq, hqc⟩ : ∃ q, q ∈ C₁ ∪ C₂ ∧ g q ≠ c := by
      by_contra hcon
      push Not at hcon
      exact hsep.not_subset fun q hq => hcon q hq
    refine ⟨y, hle, ?_⟩
    rcases hq with hq | hq
    · obtain ⟨x₂, hx₂⟩ := hne₂
      refine ⟨q, hq, x₂, hx₂, ?_⟩
      have h₁ : g q < c := lt_of_le_of_ne (hsep.le_of_mem_left hq) hqc
      have h₂ : c ≤ g x₂ := hsep.le_of_mem_right hx₂
      rw [hy q] at h₁
      rw [hy x₂] at h₂
      linarith
    · obtain ⟨x₁, hx₁⟩ := hne₁
      refine ⟨x₁, hx₁, q, hq, ?_⟩
      have h₁ : g x₁ ≤ c := hsep.le_of_mem_left hx₁
      have h₂ : c < g q := lt_of_le_of_ne (hsep.le_of_mem_right hq) (Ne.symm hqc)
      rw [hy x₁] at h₁
      rw [hy q] at h₂
      linarith

/-- **A subspace meets the relative interior of a convex set** exactly when no direction of the
pairing annihilates the subspace, is nowhere positive on the set and is negative somewhere on it.
The annihilator condition is not assumed but implied: a direction along which the pairing is
bounded below on a subspace vanishes on it. -/
theorem submodule_inter_relint_nonempty_iff (L : Submodule ℝ E) (hC : Convex ℝ C)
    (hne : C.Nonempty) :
    ((L : Set E) ∩ ri C).Nonempty ↔
      ¬ ∃ y : F, (∀ x ∈ L, B x y = 0) ∧ (∀ x ∈ C, B x y ≤ 0) ∧ ∃ x ∈ C, B x y < 0 := by
  have hzeroL : (0 : E) ∈ (L : Set E) := L.zero_mem
  have hkey : (∃ y : F, (∀ x ∈ L, B x y = 0) ∧ (∀ x ∈ C, B x y ≤ 0) ∧ ∃ x ∈ C, B x y < 0) ↔
      Disjoint (ri C) (ri (L : Set E)) := by
    rw [← exists_pairing_le_iff_disjoint_relint (B := B) hC L.convex hne ⟨0, hzeroL⟩]
    constructor
    · rintro ⟨y, hzero, hnonpos, x, hx, hlt⟩
      refine ⟨y, fun x₁ hx₁ x₂ hx₂ => ?_, x, hx, 0, hzeroL, ?_⟩
      · rw [hzero x₂ hx₂]
        exact hnonpos x₁ hx₁
      · rwa [hzero 0 L.zero_mem]
    · rintro ⟨y, hle, x₁, hx₁, x₂, hx₂, hlt⟩
      have hzero : ∀ x ∈ L, B x y = 0 := by
        have hneg : ∀ x ∈ L, B x (-y) ≤ -B x₁ y := by
          intro x hx
          rw [map_neg (B x) y]
          linarith [hle x₁ hx₁ x hx]
        intro x hx
        have h := forall_pairing_eq_zero_of_forall_le hneg x hx
        rw [map_neg (B x) y, neg_eq_zero] at h
        exact h
      refine ⟨y, hzero, fun x hx => ?_, x₁, hx₁, ?_⟩
      · rw [← hzero 0 L.zero_mem]
        exact hle x hx 0 hzeroL
      · rwa [← hzero x₂ hx₂]
  rw [hkey, intrinsicInterior_coe_submodule]
  constructor
  · rintro ⟨x, hxL, hxC⟩
    exact Set.not_disjoint_iff_nonempty_inter.2 ⟨x, hxC, hxL⟩
  · intro h
    obtain ⟨x, hxC, hxL⟩ := Set.not_disjoint_iff_nonempty_inter.1 h
    exact ⟨x, hxL, hxC⟩

/-- **A subspace meets the relative interior of a convex set**, with the two conditions on the set
read off its support function: `δ*(y | C) ≤ 0` and `δ*(-y | C) > 0`. -/
theorem submodule_inter_relint_nonempty_iff_supportFn (L : Submodule ℝ E) (hC : Convex ℝ C)
    (hne : C.Nonempty) :
    ((L : Set E) ∩ ri C).Nonempty ↔
      ¬ ∃ y : F, (∀ x ∈ L, B x y = 0) ∧ supportFn B C y ≤ 0 ∧ 0 < supportFn B C (-y) := by
  rw [submodule_inter_relint_nonempty_iff (B := B) L hC hne]
  refine not_congr (exists_congr fun y => and_congr_right fun _ => ?_)
  rw [supportFn_le_zero_iff, zero_lt_supportFn_iff]
  refine and_congr_right fun _ => exists_congr fun x => and_congr_right fun _ => ?_
  rw [map_neg (B x) y, neg_pos]

end Separation

/-! ### The effective domain of a convex function -/

section Function

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f : E → EReal}

/-- A subspace `L` meets `ri (dom f)` exactly when there is no `y` annihilating `L` with
`(f*) 0⁺ y ≤ 0 < (f*) 0⁺ (-y)`. The support function of `dom f` is the recession function of `f*`
(`recessionFn_conj`), so this is the previous statement at `C = dom f`. -/
theorem submodule_inter_relint_dom_nonempty_iff (L : Submodule ℝ E) (hf : ConvexFn f)
    (hp : Proper f) (hc : Proper (conj B f)) :
    ((L : Set E) ∩ ri (dom f)).Nonempty ↔
      ¬ ∃ y : F, (∀ x ∈ L, B x y = 0) ∧ recessionFn (conj B f) y ≤ 0 ∧
        0 < recessionFn (conj B f) (-y) := by
  rw [recessionFn_conj hp hc]
  exact submodule_inter_relint_nonempty_iff_supportFn L hf.convex_dom hp.dom_nonempty

end Function

/-! ### The range of a linear transformation -/

section Image

variable {E F G H : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [AddCommGroup H] [Module ℝ H]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ} [IsCompatiblePairing B']
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {g : G → EReal}

omit [FiniteDimensional ℝ G] [IsCompatiblePairing B'] in
/-- **The annihilator of the range of `A` is the kernel of its adjoint.** `B.SeparatingRight` is
what recovers `A' y = 0` from "`⟨·, A' y⟩` vanishes identically". -/
theorem forall_mem_range_eq_zero_iff (hB : B.SeparatingRight) (hA : IsAdjointPair B B' A A')
    (y : H) : (∀ z ∈ LinearMap.range A, B' z y = 0) ↔ A' y = 0 := by
  constructor
  · intro h
    refine hB _ fun x => ?_
    rw [← hA x y]
    exact h (A x) (LinearMap.mem_range_self A x)
  · intro h z hz
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hz
    rw [hA x y, h, map_zero]

/-- For a linear transformation `A` with adjoint `A'` and a proper convex `g`, some `A x` lies in
`ri (dom g)` exactly when no `y` in the kernel of `A'` has `(g*) 0⁺ y ≤ 0 < (g*) 0⁺ (-y)`: the
subspace criterion above for `L = range A`. -/
theorem exists_apply_mem_relint_dom_iff (hB : B.SeparatingRight) (hA : IsAdjointPair B B' A A')
    (hg : ConvexFn g) (hp : Proper g) (hc : Proper (conj B' g)) :
    (∃ x, A x ∈ ri (dom g)) ↔
      ¬ ∃ y : H, A' y = 0 ∧ recessionFn (conj B' g) y ≤ 0 ∧ 0 < recessionFn (conj B' g) (-y) := by
  have hmem : (∃ x, A x ∈ ri (dom g)) ↔
      ((LinearMap.range A : Set G) ∩ ri (dom g)).Nonempty := by
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨A x, LinearMap.mem_range_self A x, hx⟩
    · rintro ⟨z, hzL, hz⟩
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hzL
      exact ⟨x, hz⟩
  rw [hmem, submodule_inter_relint_dom_nonempty_iff (LinearMap.range A) hg hp hc]
  exact not_congr (exists_congr fun y =>
    and_congr (forall_mem_range_eq_zero_iff hB hA y) Iff.rfl)

end Image

end ConvexAnalysis
