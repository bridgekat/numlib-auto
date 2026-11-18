/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Projection

/-!
# Outer inverses of linear maps

An outer inverse with prescribed range and kernel is obtained by projecting onto the image
of the prescribed range, then inverting the restriction to that range.
-/

namespace LinearMap

variable {K E F : Type*} [Ring K] [AddCommGroup E] [AddCommGroup F]
  [Module K E] [Module K F]

/-- An outer inverse of $A$ with range $T$ and kernel $S$ exists uniquely if and only
if $A$ is injective on $T$ and the image of $T$ under $A$ is complementary to $S$. -/
theorem existsUnique_outerInverse_iff (A : E →ₗ[K] F) (T : Submodule K E)
    (S : Submodule K F) :
    (∃! X : F →ₗ[K] E, (X.comp A).comp X = X ∧ X.range = T ∧ X.ker = S) ↔
      Disjoint T A.ker ∧ IsCompl (T.map A) S := by
  have properties (X : F →ₗ[K] E)
      (hX : (X.comp A).comp X = X ∧ X.range = T ∧ X.ker = S) :
      IsIdempotentElem (A.comp X) ∧ (A.comp X).range = T.map A ∧
        (A.comp X).ker = S ∧ Disjoint T A.ker := by
    obtain ⟨ho, hr, hk⟩ := hX
    have hfix (y : F) : X (A (X y)) = X y := LinearMap.congr_fun ho y
    refine ⟨?_, by rw [range_comp, hr], ?_, ?_⟩
    · change (A.comp X).comp (A.comp X) = A.comp X
      ext y
      exact congrArg A (hfix y)
    · rw [← hk]
      ext y
      simp only [mem_ker, comp_apply]
      exact ⟨fun h => by rw [← hfix y, h, map_zero], fun h => by rw [h, map_zero]⟩
    · rw [← hr, Submodule.disjoint_def]
      rintro _ ⟨y, rfl⟩ hy
      exact (hfix y).symm.trans (by rw [mem_ker.mp hy, map_zero])
  constructor
  · rintro ⟨X, hX, _⟩
    obtain ⟨hid, hr, hk, hd⟩ := properties X hX
    refine ⟨hd, ?_⟩
    rw [← hr, ← hk]
    exact LinearMap.IsIdempotentElem.isCompl hid
  · rintro ⟨hd, hc⟩
    have hmap (x : E) (hx : x ∈ T) : A x ∈ T.map A := ⟨x, hx, rfl⟩
    let e : T ≃ₗ[K] T.map A := LinearEquiv.ofBijective (A.restrict hmap)
      ⟨(injective_restrict_iff hmap).mpr hd, range_eq_top.mp (by
        rw [range_restrict, Submodule.comap_subtype_self])⟩
    let P := (T.map A).projectionOnto S hc
    let X : F →ₗ[K] E := T.subtype.comp (e.symm.toLinearMap.comp P)
    have hfix (t : T) : X (A t) = t := by
      change (e.symm (P (A t)) : E) = t
      rw [Submodule.projectionOnto_apply_of_mem_left hc (hmap t t.2)]
      exact congrArg Subtype.val (e.symm_apply_apply t)
    have hX : (X.comp A).comp X = X ∧ X.range = T ∧ X.ker = S := by
      refine ⟨?_, ?_, ?_⟩
      · ext y
        exact hfix (e.symm (P y))
      · refine le_antisymm ?_ ?_
        · rintro _ ⟨y, rfl⟩
          exact (e.symm (P y)).2
        · intro t ht
          exact ⟨A t, hfix ⟨t, ht⟩⟩
      · ext y
        rw [mem_ker]
        change (e.symm (P y) : E) = 0 ↔ y ∈ S
        rw [Submodule.coe_eq_zero, ← e.symm.map_zero, e.symm.injective.eq_iff,
          Submodule.projectionOnto_apply_eq_zero_iff hc]
    refine ⟨X, hX, ?_⟩
    intro Y hY
    obtain ⟨hXi, hXr, hXk, _⟩ := properties X hX
    obtain ⟨hYi, hYr, hYk, _⟩ := properties Y hY
    have hAX : A.comp Y = A.comp X :=
      LinearMap.IsIdempotentElem.ext hYi hXi ⟨hYr.trans hXr.symm, hYk.trans hXk.symm⟩
    ext y
    apply (disjoint_ker_iff_injOn.mp hd)
    · rw [← hY.2.1]
      exact mem_range_self Y y
    · rw [← hX.2.1]
      exact mem_range_self X y
    · exact LinearMap.congr_fun hAX y

end LinearMap
