/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.GeneralizedInverse
import NumlibSurface.BenIsraelGreville.Chapter00.Section04
import NumlibSurface.BenIsraelGreville.Chapter02.Section04
import NumlibSurface.BenIsraelGreville.Chapter04.Section04

/-!
# Generalized inverses with prescribed range and null space

Section 2.6 of [benIsrael2003generalized] determines when an inverse with specified
range and kernel exists. The outer inverse is unique because those subspaces
determine the projection used to construct it.
-/

namespace BenIsraelGreville.Chapter02

open Matrix Module
open BenIsraelGreville.Chapter01 (definition_1 mem_one_two_iff)
open scoped ComplexOrder

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **Section 2.6** of [benIsrael2003generalized]. The class $A\{2\}_{T,S}$ consists of
the outer inverses of $A$ with range $T$ and kernel $S$. -/
def prescribedOuterInverses (A : Matrix m n ℂ) (T : Submodule ℂ (n → ℂ))
    (S : Submodule ℂ (m → ℂ)) : Set (Matrix n m ℂ) :=
  {X | A.IsOuterInverse X ∧ X.mulVecLin.range = T ∧ X.mulVecLin.ker = S}

/-- **Theorem 14** of [benIsrael2003generalized], Chapter 2. If $T$ and $S$ have
dimensions adding to the codomain dimension, an outer inverse with range $T$
and kernel $S$ exists precisely when $A(T)$ and $S$ are complementary. The
inverse is then unique. -/
theorem theorem_14 (A : Matrix m n ℂ) (T : Submodule ℂ (n → ℂ))
    (S : Submodule ℂ (m → ℂ)) (hdim : finrank ℂ T + finrank ℂ S = Fintype.card m) :
    (∃! X, X ∈ prescribedOuterInverses A T S) ↔ IsCompl (T.map A.mulVecLin) S := by
  classical
  simp only [prescribedOuterInverses, Set.mem_ofPred_eq]
  have he :
      (∃! X : Matrix n m ℂ, A.IsOuterInverse X ∧
        LinearMap.range X.mulVecLin = T ∧ LinearMap.ker X.mulVecLin = S) ↔
      ∃! X : (m → ℂ) →ₗ[ℂ] (n → ℂ),
        (X.comp A.mulVecLin).comp X = X ∧ X.range = T ∧ X.ker = S := by
    apply toLin'.toEquiv.existsUnique_congr
    intro X
    change _ ↔ (X.mulVecLin.comp A.mulVecLin).comp X.mulVecLin = X.mulVecLin ∧
      X.mulVecLin.range = T ∧ X.mulVecLin.ker = S
    rw [← mulVecLin_mul, ← mulVecLin_mul, isOuterInverse_iff]
    exact and_congr_left' toLin'.injective.eq_iff.symm
  rw [he, LinearMap.existsUnique_outerInverse_iff]
  refine ⟨And.right, fun hc => ⟨?_, hc⟩⟩
  have hmap (x : n → ℂ) (hx : x ∈ T) : A.mulVecLin x ∈ T.map A.mulVecLin :=
    ⟨x, hx, rfl⟩
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  rw [finrank_fintype_fun_eq_card] at hsum
  have heq : finrank ℂ T = finrank ℂ (T.map A.mulVecLin) := by omega
  apply (LinearMap.injective_restrict_iff hmap).mp
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr
  apply LinearMap.range_eq_top.mp
  rw [LinearMap.range_restrict, Submodule.comap_subtype_self]

/-- **Corollary 10** of [benIsrael2003generalized], Chapter 2. When $T$ has
dimension equal to the rank of $A$ and $S$ has that codimension, the complementarity
of $A(T)$ and $S$ is equivalent to the two prescribed complement conditions and to
the existence of a reflexive inverse having range $T$ and kernel $S$. -/
theorem corollary_10 (A : Matrix m n ℂ) (T : Submodule ℂ (n → ℂ))
    (S : Submodule ℂ (m → ℂ)) (hT : finrank ℂ T = A.rank)
    (hdim : finrank ℂ T + finrank ℂ S = Fintype.card m) :
    (IsCompl (T.map A.mulVecLin) S ↔
      IsCompl A.mulVecLin.range S ∧ IsCompl T A.mulVecLin.ker) ∧
    ((IsCompl A.mulVecLin.range S ∧ IsCompl T A.mulVecLin.ker) ↔
      ∃ X : Matrix n m ℂ, X ∈ definition_1 A {.inner, .outer} ∧
        X.mulVecLin.range = T ∧ X.mulVecLin.ker = S) := by
  have hReflexive (h : IsCompl (T.map A.mulVecLin) S) :
      ∃ X : Matrix n m ℂ, X ∈ definition_1 A {.inner, .outer} ∧
        X.mulVecLin.range = T ∧ X.mulVecLin.ker = S := by
    obtain ⟨X, ⟨ho, hr, hk⟩, _⟩ := (theorem_14 A T S hdim).mpr h
    have hx : X.rank = A.rank := by
      change finrank ℂ X.mulVecLin.range = A.rank
      rwa [hr]
    have hi' := isOuterInverse_iff_isInnerInverse.mp ho
    have hi : A.IsInnerInverse X := isOuterInverse_iff_isInnerInverse.mp
      (hi'.isOuterInverse_iff_rank_eq.mpr hx.symm)
    exact ⟨X, mem_one_two_iff.mpr ⟨hi, ho⟩, hr, hk⟩
  have hComp (X : Matrix n m ℂ) (hX : X ∈ definition_1 A {.inner, .outer})
      (hr : X.mulVecLin.range = T) (hk : X.mulVecLin.ker = S) :
      IsCompl A.mulVecLin.range S ∧ IsCompl T A.mulVecLin.ker := by
    obtain ⟨⟨h₁, _⟩, ⟨h₂, _⟩⟩ := corollary_7 hX
    exact ⟨hk ▸ h₁, hr ▸ h₂⟩
  have hImage (h : IsCompl A.mulVecLin.range S ∧ IsCompl T A.mulVecLin.ker) :
      IsCompl (T.map A.mulVecLin) S := by
    have hzero : A.mulVecLin.ker.map A.mulVecLin = ⊥ :=
      LinearMap.le_ker_iff_map.mp le_rfl
    have hrange : A.mulVecLin.range = T.map A.mulVecLin := by
      rw [LinearMap.range_eq_map, ← h.2.sup_eq_top, Submodule.map_sup, hzero, sup_bot_eq]
    exact hrange ▸ h.1
  refine ⟨⟨?_, hImage⟩, ⟨hReflexive ∘ hImage, fun ⟨X, hx, hr, hk⟩ => hComp X hx hr hk⟩⟩
  intro h
  obtain ⟨X, hx, hr, hk⟩ := hReflexive h
  exact hComp X hx hr hk

/-- The matrix of the projector onto $L$ along the complementary subspace $S$. -/
noncomputable def projectorMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L S : Submodule ℂ (ι → ℂ)} (h : IsCompl L S) : Matrix ι ι ℂ :=
  toLin'.symm (projector h)

private theorem mulVecLin_projectorMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L S : Submodule ℂ (ι → ℂ)} (h : IsCompl L S) :
    (projectorMatrix h).mulVecLin = projector h := by
  rw [← toLin'_apply', projectorMatrix, LinearEquiv.apply_symm_apply]

private theorem eq_projectorMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L S : Submodule ℂ (ι → ℂ)} (h : IsCompl L S) {E : Matrix ι ι ℂ} (hi : IsIdempotentElem E)
    (hr : E.mulVecLin.range = L) (hk : E.mulVecLin.ker = S) : E = projectorMatrix h := by
  have hid : IsIdempotentElem E.mulVecLin := by
    change E.mulVecLin.comp E.mulVecLin = E.mulVecLin
    rw [← mulVecLin_mul, hi.eq]
  apply toLin'.injective
  rw [toLin'_apply', toLin'_apply', mulVecLin_projectorMatrix]
  exact LinearMap.IsIdempotentElem.ext hid (Submodule.isIdempotentElem_projection h)
    ⟨hr.trans (Submodule.range_projection h).symm, hk.trans (Submodule.ker_projection h).symm⟩

private theorem prescribed_eq_iff [DecidableEq m] [DecidableEq n]
    {A : Matrix m n ℂ} {U : Matrix n m ℂ} (hU : A.IsInnerInverse U) (X Z : Matrix n m ℂ) :
    A * X = A * Z ∧ X * A = Z * A ↔
      ∃ Y : Matrix n m ℂ, X = Z + (1 - U * A) * Y * (1 - A * U) := by
  have hAU := isInnerInverse_iff.mp hU
  have hLeft : A * (1 - U * A) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hAU, sub_self]
  have hRight : (1 - A * U) * A = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hAU, sub_self]
  constructor
  · rintro ⟨h₁, h₂⟩
    have hz₁ : A * (X - Z) = 0 := by rw [Matrix.mul_sub, h₁, sub_self]
    have hz₂ : (X - Z) * A = 0 := by rw [Matrix.sub_mul, h₂, sub_self]
    refine ⟨X - Z, ?_⟩
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc U, hz₁, Matrix.mul_zero, sub_zero,
      Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc (X - Z), hz₂,
      Matrix.zero_mul, sub_zero, add_comm Z, sub_add_cancel]
  · rintro ⟨Y, rfl⟩
    constructor
    · rw [Matrix.mul_add, ← Matrix.mul_assoc A, ← Matrix.mul_assoc A, hLeft,
        Matrix.zero_mul, Matrix.zero_mul, add_zero]
    · rw [Matrix.add_mul, Matrix.mul_assoc _ (1 - A * U), hRight, Matrix.mul_zero, add_zero]

/-- **Theorem 12** of [benIsrael2003generalized], Chapter 2. The prescribed inner
inverses satisfy the two projection equations. Their solution family is centered
at $P_{T,N(A)} U P_{R(A),S}$, the unique reflexive inverse with range $T$ and kernel
$S$, for any inner inverse $U$ of $A$. -/
theorem theorem_12 [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ)
    {S : Submodule ℂ (m → ℂ)} {T : Submodule ℂ (n → ℂ)}
    (hS : IsCompl A.mulVecLin.range S) (hT : IsCompl T A.mulVecLin.ker)
    (U : Matrix n m ℂ) (hU : A.IsInnerInverse U) :
    let P := projectorMatrix hT
    let Q := projectorMatrix hS
    let C := P * U * Q
    (∀ X : Matrix n m ℂ,
      A.IsInnerInverse X ∧ (A * X).mulVecLin.ker = S ∧ (X * A).mulVecLin.range = T ↔
        A * X = Q ∧ X * A = P) ∧
    (∀ X : Matrix n m ℂ, A * X = Q ∧ X * A = P ↔
      ∃ Y : Matrix n m ℂ, X = C + (1 - U * A) * Y * (1 - A * U)) ∧
    (C ∈ definition_1 A {.inner, .outer} ∧ C.mulVecLin.range = T ∧ C.mulVecLin.ker = S) ∧
    (∀ X : Matrix n m ℂ,
      X ∈ definition_1 A {.inner, .outer} → X.mulVecLin.range = T →
      X.mulVecLin.ker = S → X = C) := by
  dsimp only
  let P := projectorMatrix hT
  let Q := projectorMatrix hS
  have hQA : Q * A = A := by
    apply toLin'.injective
    rw [toLin'_apply', toLin'_apply', mulVecLin_mul, mulVecLin_projectorMatrix]
    exact LinearMap.ext fun x =>
      Submodule.projection_apply_of_mem_left hS (LinearMap.mem_range_self A.mulVecLin x)
  have hEq (X : Matrix n m ℂ) :
      A.IsInnerInverse X ∧ (A * X).mulVecLin.ker = S ∧ (X * A).mulVecLin.range = T ↔
        A * X = Q ∧ X * A = P := by
    constructor
    · rintro ⟨hi, hk, hr⟩
      exact ⟨eq_projectorMatrix hS hi.isIdempotentElem_mul hi.range_mul hk,
        eq_projectorMatrix hT hi.isIdempotentElem_mul_rev hr hi.ker_mul_rev⟩
    · rintro ⟨hAX, hXA⟩
      refine ⟨isInnerInverse_iff.mpr (by rw [hAX, hQA]), ?_, ?_⟩
      · rw [hAX, mulVecLin_projectorMatrix]
        exact Submodule.ker_projection hS
      · rw [hXA, mulVecLin_projectorMatrix]
        exact Submodule.range_projection hT
  have hC (X : Matrix n m ℂ) (hX : X ∈ definition_1 A {.inner, .outer})
      (hR : X.mulVecLin.range = T) (hK : X.mulVecLin.ker = S) :
      A * X = Q ∧ X * A = P ∧ X = P * U * Q := by
    obtain ⟨hi, ho⟩ := mem_one_two_iff.mp hX
    have hSwap := isOuterInverse_iff_isInnerInverse.mp ho
    have hEqX := (hEq X).mp ⟨hi, hSwap.ker_mul_rev.trans hK, hSwap.range_mul.trans hR⟩
    refine ⟨hEqX.1, hEqX.2, ?_⟩
    calc
      X = X * A * X := (isOuterInverse_iff.mp ho).symm
      _ = X * (A * U * A) * X := by rw [isInnerInverse_iff.mp hU]
      _ = (X * A) * U * (A * X) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hEqX.1, hEqX.2]
  have hTDim := Submodule.finrank_add_eq_of_isCompl hT
  rw [finrank_fintype_fun_eq_card] at hTDim
  have hRank := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  change A.rank + finrank ℂ A.mulVecLin.ker = finrank ℂ (n → ℂ) at hRank
  rw [finrank_fintype_fun_eq_card] at hRank
  have hTCard : finrank ℂ T = A.rank := by omega
  have hDim := Submodule.finrank_add_eq_of_isCompl hS
  change A.rank + finrank ℂ S = finrank ℂ (m → ℂ) at hDim
  rw [← hTCard, finrank_fintype_fun_eq_card] at hDim
  obtain ⟨Z, hz, hzR, hzK⟩ := (corollary_10 A T S hTCard hDim).2.mp ⟨hS, hT⟩
  obtain ⟨hAZ, hZA, hZ⟩ := hC Z hz hzR hzK
  refine ⟨hEq, ?_, hZ ▸ ⟨hz, hzR, hzK⟩, fun X hx hr hk => (hC X hx hr hk).2.2⟩
  intro X
  change A * X = Q ∧ X * A = P ↔
    ∃ Y : Matrix n m ℂ, X = P * U * Q + (1 - U * A) * Y * (1 - A * U)
  rw [← hZ, ← hAZ, ← hZA]
  exact prescribed_eq_iff hU X Z

/-- **Corollary 9** of [benIsrael2003generalized], Chapter 2. Any prescribed inner
inverse $Z$ can serve as the center of the affine family of such inverses. -/
theorem corollary_9 [DecidableEq m] [DecidableEq n] {A : Matrix m n ℂ}
    {S : Submodule ℂ (m → ℂ)} {T : Submodule ℂ (n → ℂ)}
    (hS : IsCompl A.mulVecLin.range S) (hT : IsCompl T A.mulVecLin.ker)
    {Z : Matrix n m ℂ} (hZ : A.IsInnerInverse Z ∧
      (A * Z).mulVecLin.ker = S ∧ (Z * A).mulVecLin.range = T) (X : Matrix n m ℂ) :
    A.IsInnerInverse X ∧ (A * X).mulVecLin.ker = S ∧ (X * A).mulVecLin.range = T ↔
      ∃ Y : Matrix n m ℂ, X = Z + (1 - Z * A) * Y * (1 - A * Z) := by
  have h := (theorem_12 A hS hT Z hZ.1).1
  obtain ⟨hAZ, hZA⟩ := (h Z).mp hZ
  rw [h X, ← hAZ, ← hZA]
  exact prescribed_eq_iff hZ.1 X Z

private theorem mul_inner_mul_of_ker_le {p q r : Type*}
    [Fintype p] [Fintype q] {B : Matrix q p ℂ} {W : Matrix p q ℂ}
    (hW : B.IsInnerInverse W) (D : Matrix r p ℂ) (hK : B.mulVecLin.ker ≤ D.mulVecLin.ker) :
    D * W * B = D := by
  rw [ext_iff_mulVec]
  intro v
  have hv : (W * B).mulVecLin v - v ∈ B.mulVecLin.ker := by
    rw [LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply, ← mulVecLin_mul,
      ← Matrix.mul_assoc, isInnerInverse_iff.mp hW, sub_self]
  have hd := LinearMap.mem_ker.mp (hK hv)
  rw [map_sub, ← LinearMap.comp_apply, ← mulVecLin_mul, ← Matrix.mul_assoc, sub_eq_zero] at hd
  exact hd

private theorem mul_inner_mul_of_range_le {p q r : Type*}
    [Fintype p] [Fintype q] [Fintype r] {B : Matrix q p ℂ} {W : Matrix p q ℂ}
    (hW : B.IsInnerInverse W) (D : Matrix q r ℂ) (hR : D.mulVecLin.range ≤ B.mulVecLin.range) :
    B * W * D = D := by
  rw [ext_iff_mulVec]
  intro x
  obtain ⟨y, hy⟩ := hR (LinearMap.mem_range_self D.mulVecLin x)
  change (B * W * D).mulVecLin x = D.mulVecLin x
  rw [mulVecLin_mul, LinearMap.comp_apply, ← hy, ← LinearMap.comp_apply, ← mulVecLin_mul,
    isInnerInverse_iff.mp hW]

private theorem outerInverse_eq_of_eq_range_ker {A : Matrix m n ℂ} {X Y : Matrix n m ℂ}
    (hx : A.IsOuterInverse X) (hy : A.IsOuterInverse Y)
    (hR : Y.mulVecLin.range = X.mulVecLin.range) (hK : Y.mulVecLin.ker = X.mulVecLin.ker) :
    Y = X := by
  classical
  have hX := isOuterInverse_iff_isInnerInverse.mp hx
  have hY := isOuterInverse_iff_isInnerInverse.mp hy
  have hMap (Z : Matrix n m ℂ) :
      (A * Z).mulVecLin.range = Z.mulVecLin.range.map A.mulVecLin := by
    rw [mulVecLin_mul, LinearMap.range_comp]
  obtain ⟨hc, _⟩ := theorem_8.1 (A * X) hX.isIdempotentElem_mul_rev
  have hr : (A * Y).mulVecLin.range = (A * X).mulVecLin.range := by rw [hMap, hMap, hR]
  have hk : (A * Y).mulVecLin.ker = (A * X).mulVecLin.ker :=
    hY.ker_mul_rev.trans (hK.trans hX.ker_mul_rev.symm)
  have he : A * Y = A * X :=
    (eq_projectorMatrix hc hY.isIdempotentElem_mul_rev hr hk).trans
      (eq_projectorMatrix hc hX.isIdempotentElem_mul_rev rfl rfl).symm
  calc
    Y = X * A * Y := (mul_inner_mul_of_range_le hX Y hR.le).symm
    _ = X * (A * X) := by rw [Matrix.mul_assoc, he]
    _ = X := by rw [← Matrix.mul_assoc, isOuterInverse_iff.mp hx]

/-- **Theorem 13** of [benIsrael2003generalized], Chapter 2. For an inner inverse $W$
of $VAU$, the rank of $VAU$ controls whether $UWV$ is an inner inverse of $A$ or an
outer inverse with range $R(U)$ or kernel $N(V)$. The three equalities together
characterize the prescribed reflexive inverse. -/
theorem theorem_13 {p q : Type*} [Fintype p] [Fintype q]
    (A : Matrix m n ℂ) (U : Matrix n p ℂ) (V : Matrix q m ℂ) (W : Matrix p q ℂ)
    (hW : (V * A * U).IsInnerInverse W) :
    let B := V * A * U
    let X := U * W * V
    (A.IsInnerInverse X ↔ B.rank = A.rank) ∧
    (A.IsOuterInverse X ∧ X.mulVecLin.range = U.mulVecLin.range ↔ B.rank = U.rank) ∧
    (A.IsOuterInverse X ∧ X.mulVecLin.ker = V.mulVecLin.ker ↔ B.rank = V.rank) ∧
    (X ∈ definition_1 A {.inner, .outer} ∧
      X.mulVecLin.range = U.mulVecLin.range ∧ X.mulVecLin.ker = V.mulVecLin.ker ↔
      B.rank = A.rank ∧ B.rank = U.rank ∧ B.rank = V.rank) := by
  dsimp only
  let B := V * A * U
  let X := U * W * V
  have hB : B = V * (A * U) := Matrix.mul_assoc _ _ _
  have hXA : X * A * X = U * W * B * W * V := by
    simp only [X, B, Matrix.mul_assoc]
  have hRank : (X * A * X).rank ≤ B.rank := by
    rw [hXA]
    exact (rank_mul_le_left _ _).trans ((rank_mul_le_left _ _).trans (rank_mul_le_right _ _))
  have hUA : B.rank ≤ U.rank := rank_mul_le_right _ _
  have hAV : B.rank ≤ V.rank := hB.symm ▸ rank_mul_le_left V (A * U)
  have hi : A.IsInnerInverse X ↔ B.rank = A.rank := by
    constructor
    · intro hi
      have h' : A.IsInnerInverse (X * A * X) := hi.isInnerInverse_mul hi
      refine le_antisymm ?_ (h'.rank_le.trans hRank)
      rw [hB]
      exact (rank_mul_le_right _ _).trans (rank_mul_le_left _ _)
    · intro h
      have hr : (A * U).rank = A.rank :=
        le_antisymm (rank_mul_le_left _ _) (h.ge.trans (hB.symm ▸ rank_mul_le_right V (A * U)))
      have hR := (Chapter01.exercise_10 A U).1.mpr hr
      have hK : B.mulVecLin.ker = (A * U).mulVecLin.ker := by
        rw [hB]
        exact (Chapter01.exercise_10 V (A * U)).2.mpr (hB ▸ h.trans hr.symm)
      have hFix : (A * X) * (A * U) = A * U := calc
        (A * X) * (A * U) = (A * U) * W * B := by simp only [X, B, Matrix.mul_assoc]
        _ = A * U := mul_inner_mul_of_ker_le hW (A * U) hK.le
      rw [isInnerInverse_iff, ext_iff_mulVec]
      intro x
      obtain ⟨y, hy⟩ := hR.symm ▸ LinearMap.mem_range_self A.mulVecLin x
      change (A * X * A).mulVecLin x = A.mulVecLin x
      rw [mulVecLin_mul, LinearMap.comp_apply, ← hy, ← LinearMap.comp_apply, ← mulVecLin_mul, hFix]
  have hoU : A.IsOuterInverse X ∧ X.mulVecLin.range = U.mulVecLin.range ↔ B.rank = U.rank := by
    constructor
    · rintro ⟨ho, hr⟩
      have hx : X.rank = U.rank := congrArg (fun L : Submodule ℂ (n → ℂ) => finrank ℂ L) hr
      refine le_antisymm hUA ?_
      rw [← hx, ← isOuterInverse_iff.mp ho]
      exact hRank
    · intro h
      have hK := (Chapter01.exercise_10 (V * A) U).2.mpr h
      have hFix : X * A * U = U := calc
        X * A * U = U * W * B := by simp only [X, B, Matrix.mul_assoc]
        _ = U := mul_inner_mul_of_ker_le hW U hK.le
      constructor
      · rw [isOuterInverse_iff]
        calc
          X * A * X = (X * A * U) * W * V := by simp only [X, Matrix.mul_assoc]
          _ = X := by rw [hFix]
      · refine le_antisymm ?_ ?_
        · rw [show X = U * (W * V) from Matrix.mul_assoc _ _ _, mulVecLin_mul]
          exact LinearMap.range_comp_le_range _ _
        · calc
            U.mulVecLin.range = (X * A * U).mulVecLin.range := by rw [hFix]
            _ ≤ X.mulVecLin.range := by
              rw [Matrix.mul_assoc, mulVecLin_mul]
              exact LinearMap.range_comp_le_range _ _
  have hoV : A.IsOuterInverse X ∧ X.mulVecLin.ker = V.mulVecLin.ker ↔ B.rank = V.rank := by
    constructor
    · rintro ⟨ho, hk⟩
      have hx : X.rank = V.rank := (Chapter01.exercise_10 (U * W) V).2.mp hk
      refine le_antisymm hAV ?_
      rw [← hx, ← isOuterInverse_iff.mp ho]
      exact hRank
    · intro h
      have hr : B.mulVecLin.range = V.mulVecLin.range := by
        rw [hB]
        exact (Chapter01.exercise_10 V (A * U)).1.mpr (hB ▸ h)
      have hFix : V * A * X = V := calc
        V * A * X = B * W * V := by simp only [X, B, Matrix.mul_assoc]
        _ = V := mul_inner_mul_of_range_le hW V hr.ge
      constructor
      · rw [isOuterInverse_iff]
        calc
          X * A * X = U * W * (V * A * X) := by simp only [X, Matrix.mul_assoc]
          _ = X := by rw [hFix]
      · refine le_antisymm ?_ ?_
        · calc
            X.mulVecLin.ker ≤ ((V * A) * X).mulVecLin.ker := by
              rw [mulVecLin_mul (V * A) X]
              exact LinearMap.ker_le_ker_comp _ _
            _ = V.mulVecLin.ker := by rw [hFix]
        · change V.mulVecLin.ker ≤ ((U * W) * V).mulVecLin.ker
          rw [mulVecLin_mul]
          exact LinearMap.ker_le_ker_comp _ _
  refine ⟨hi, hoU, hoV, ?_⟩
  rw [mem_one_two_iff]
  exact ⟨fun ⟨⟨h₁, h₂⟩, hR, hK⟩ => ⟨hi.mp h₁, hoU.mp ⟨h₂, hR⟩, hoV.mp ⟨h₂, hK⟩⟩,
    fun ⟨hA, hU, hV⟩ => ⟨⟨hi.mpr hA, (hoU.mpr hU).1⟩, (hoU.mpr hU).2, (hoV.mpr hV).2⟩⟩

/-- **Exercise 37** of [benIsrael2003generalized], Chapter 2. The prescribed reflexive
inverse is the unique solution of the projection equations and $XP_{R(A),S}=X$. -/
theorem exercise_37 [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ)
    {S : Submodule ℂ (m → ℂ)} {T : Submodule ℂ (n → ℂ)}
    (hS : IsCompl A.mulVecLin.range S) (hT : IsCompl T A.mulVecLin.ker)
    (U : Matrix n m ℂ) (hU : A.IsInnerInverse U) (X : Matrix n m ℂ) :
    (A * X = projectorMatrix hS ∧ X * A = projectorMatrix hT ∧ X * projectorMatrix hS = X) ↔
      X = projectorMatrix hT * U * projectorMatrix hS := by
  obtain ⟨hEq, _, ⟨hc, hcR, hcK⟩, hUnique⟩ := theorem_12 A hS hT U hU
  constructor
  · rintro ⟨hAX, hXA, hX⟩
    have hi := (hEq X).mpr ⟨hAX, hXA⟩
    have ho : A.IsOuterInverse X := by
      rw [isOuterInverse_iff, Matrix.mul_assoc, hAX, hX]
    have hs := isOuterInverse_iff_isInnerInverse.mp ho
    exact hUnique X (mem_one_two_iff.mpr ⟨hi.1, ho⟩)
      (hs.range_mul.symm.trans hi.2.2) (hs.ker_mul_rev.symm.trans hi.2.1)
  · rintro rfl
    obtain ⟨hi, ho⟩ := mem_one_two_iff.mp hc
    have hs := isOuterInverse_iff_isInnerInverse.mp ho
    obtain ⟨hAX, hXA⟩ := (hEq _).mp ⟨hi, hs.ker_mul_rev.trans hcK, hs.range_mul.trans hcR⟩
    refine ⟨hAX, hXA, ?_⟩
    let C := projectorMatrix hT * U * projectorMatrix hS
    calc
      C * projectorMatrix hS = C * (A * C) := congrArg (fun Q => C * Q) hAX.symm
      _ = C * A * C := (Matrix.mul_assoc C A C).symm
      _ = C := isOuterInverse_iff.mp ho

/-- **Exercise 38** of [benIsrael2003generalized], Chapter 2. The Moore–Penrose inverse
is the unique reflexive inverse with the range and kernel of the adjoint. -/
theorem exercise_38 [DecidableEq n] (A : Matrix m n ℂ) :
    (A.pinv ∈ definition_1 A {.inner, .outer} ∧ A.pinv.mulVecLin.range = Aᴴ.mulVecLin.range ∧
      A.pinv.mulVecLin.ker = Aᴴ.mulVecLin.ker) ∧
    (∀ X : Matrix n m ℂ, X ∈ definition_1 A {.inner, .outer} →
      X.mulVecLin.range = Aᴴ.mulVecLin.range → X.mulVecLin.ker = Aᴴ.mulVecLin.ker →
      X = A.pinv) := by
  have hi : A.IsInnerInverse A.pinv := A.mul_pinv_mul_self
  have ho : A.IsOuterInverse A.pinv := A.pinv_mul_self_mul_pinv
  have hs : A.pinv * A * Aᴴ = Aᴴ := by
    rw [← A.isHermitian_pinv_mul.eq, ← conjTranspose_mul, ← Matrix.mul_assoc, A.mul_pinv_mul_self]
  have hR : A.pinv.mulVecLin.range = Aᴴ.mulVecLin.range := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [← hs, Matrix.mul_assoc, mulVecLin_mul]
      exact LinearMap.range_comp_le_range _ _
    · change Aᴴ.rank = A.pinv.rank
      exact (rank_conjTranspose A).trans ((hi.isOuterInverse_iff_rank_eq).mp ho).symm
  have hK : A.pinv.mulVecLin.ker = Aᴴ.mulVecLin.ker := by
    refine le_antisymm ?_ ?_
    · have he : Aᴴ * A * A.pinv = Aᴴ := by rw [Matrix.mul_assoc, A.conjTranspose_mul_mul_pinv]
      rw [← he, mulVecLin_mul (Aᴴ * A) A.pinv]
      exact LinearMap.ker_le_ker_comp _ _
    · rw [A.pinv_def, mulVecLin_mul]
      exact LinearMap.ker_le_ker_comp _ _
  refine ⟨⟨mem_one_two_iff.mpr ⟨hi, ho⟩, hR, hK⟩, ?_⟩
  intro Y hy hyR hyK
  exact outerInverse_eq_of_eq_range_ker ho (mem_one_two_iff.mp hy).2
    (hyR.trans hR.symm) (hyK.trans hK.symm)

/-- **Exercise 39** of [benIsrael2003generalized], Chapter 2. Every inner inverse
of $A^H A A^H$, sandwiched between two copies of $A^H$, gives $A^\dagger$. -/
theorem exercise_39 [DecidableEq n] (A : Matrix m n ℂ) (Y : Matrix m n ℂ)
    (hY : (Aᴴ * A * Aᴴ).IsInnerInverse Y) : A.pinv = Aᴴ * Y * Aᴴ := by
  have hR : (Aᴴ * A * Aᴴ).rank = A.rank := by
    refine le_antisymm ((rank_mul_le_left _ _).trans_eq (rank_conjTranspose_mul_self A)) ?_
    calc
      A.rank = ((Aᴴ * A)ᴴ * (Aᴴ * A)).rank := by
        rw [rank_conjTranspose_mul_self, rank_conjTranspose_mul_self]
      _ = (Aᴴ * A * Aᴴ * A).rank := by
        rw [(isHermitian_conjTranspose_mul_self A).eq, Matrix.mul_assoc (Aᴴ * A)]
      _ ≤ (Aᴴ * A * Aᴴ).rank := rank_mul_le_left _ _
  have h := (theorem_13 A Aᴴ Aᴴ Y hY).2.2.2.mpr
    ⟨hR, hR.trans (rank_conjTranspose A).symm, hR.trans (rank_conjTranspose A).symm⟩
  exact ((exercise_38 A).2 _ h.1 h.2.1 h.2.2).symm

/-- **Exercise 40** of [benIsrael2003generalized], Chapter 2. Inner inverses of
$AA^H$ and $A^HA$ give the Moore–Penrose inverse through Decell's formula. -/
theorem exercise_40 [DecidableEq n] (A : Matrix m n ℂ) (X : Matrix m m ℂ) (Y : Matrix n n ℂ)
    (hX : (A * Aᴴ).IsInnerInverse X) (hY : (Aᴴ * A).IsInnerInverse Y) :
    A.pinv = Aᴴ * X * A * Y * Aᴴ := by
  have hR := (Chapter01.exercise_10 A Aᴴ).1.mpr (rank_self_mul_conjTranspose A)
  have hK := ker_mulVecLin_conjTranspose_mul_self A
  have hM := mul_inner_mul_of_range_le hX A hR.ge
  have hN := mul_inner_mul_of_ker_le hY A hK.le
  have h : (Aᴴ * A * Aᴴ).IsInnerInverse (X * A * Y) := by
    rw [isInnerInverse_iff]
    calc
      (Aᴴ * A * Aᴴ) * (X * A * Y) * (Aᴴ * A * Aᴴ) =
          Aᴴ * ((A * Aᴴ) * X * A) * Y * (Aᴴ * A) * Aᴴ := by simp only [Matrix.mul_assoc]
      _ = Aᴴ * (A * Y * (Aᴴ * A)) * Aᴴ := by rw [hM]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hN]
  simpa only [Matrix.mul_assoc] using exercise_39 A (X * A * Y) h

/-- **Exercise 41** of [benIsrael2003generalized], Chapter 2. The Moore–Penrose
inverse of a product of two Hermitian idempotents is idempotent. -/
theorem exercise_41 [DecidableEq n] {E F : Matrix n n ℂ} (hE : IsIdempotentElem E)
    (hF : IsIdempotentElem F) (he : E.IsHermitian) (hf : F.IsHermitian) :
    IsIdempotentElem (E * F).pinv := by
  let C := F * E
  have hC : (E * F)ᴴ = C := by rw [conjTranspose_mul, he.eq, hf.eq]
  have hB : (E * F)ᴴ * (E * F) * (E * F)ᴴ = C * C := by
    rw [hC]
    calc
      C * (E * F) * C = F * (E * E) * (F * F) * E := by simp only [C, Matrix.mul_assoc]
      _ = C * C := by rw [hE.eq, hF.eq]; simp only [C, Matrix.mul_assoc]
  let Y := (C * C).pinv
  have hy : ((E * F)ᴴ * (E * F) * (E * F)ᴴ).IsInnerInverse Y := by
    rw [hB, isInnerInverse_iff]
    exact (C * C).mul_pinv_mul_self
  have hx : (E * F).pinv = C * Y * C := by
    rw [exercise_39 _ Y hy, hC]
  rw [hx]
  change (C * Y * C) * (C * Y * C) = C * Y * C
  calc
    (C * Y * C) * (C * Y * C) = C * (Y * (C * C) * Y) * C := by
      simp only [Matrix.mul_assoc]
    _ = C * Y * C := by rw [(C * C).pinv_mul_self_mul_pinv]

/-- **Exercise 42** of [benIsrael2003generalized], Chapter 2. For the matrix in
Equation (0.80), the prescribed reflexive inverse has nonzero entries $-i$
and $-1/3$ in positions $(3,1)$ and $(4,2)$ respectively. -/
theorem exercise_42 :
    let A := Chapter00.hermiteExampleMatrix
    let U : Matrix (Fin 6) (Fin 2) ℂ := !![0, 0; 0, 0; 1, 0; 0, 1; 0, 0; 0, 0]
    let S : Matrix (Fin 3) (Fin 1) ℂ := !![0; 0; 1]
    let X : Matrix (Fin 6) (Fin 3) ℂ :=
      !![0, 0, 0; 0, 0, 0; -Complex.I, 0, 0; 0, -(1 / 3 : ℂ), 0; 0, 0, 0; 0, 0, 0]
    (X ∈ definition_1 A {.inner, .outer} ∧
      X.mulVecLin.range = U.mulVecLin.range ∧ X.mulVecLin.ker = S.mulVecLin.range) ∧
    (∀ Y : Matrix (Fin 6) (Fin 3) ℂ, Y ∈ definition_1 A {.inner, .outer} →
      Y.mulVecLin.range = U.mulVecLin.range → Y.mulVecLin.ker = S.mulVecLin.range →
      Y = X) := by
  intro A U S X
  let P : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, 1, 0; -Complex.I, -(1 / 3 : ℂ), 0]
  have hAX : A * X = P := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, X, P, Chapter00.hermiteExampleMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
        Complex.I_mul_I]
  have hi : A.IsInnerInverse X := by
    rw [isInnerInverse_iff, hAX]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, P, Chapter00.hermiteExampleMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
        Complex.I_mul_I] <;> ring_nf <;> norm_num [Complex.I_sq]
    all_goals ring
  have ho : A.IsOuterInverse X := by
    rw [isOuterInverse_iff, Matrix.mul_assoc, hAX]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [X, P, Matrix.mul_apply, Fin.sum_univ_succ]
  have hR : X.mulVecLin.range = U.mulVecLin.range := by
    ext v
    change (∃ x, X.mulVecLin x = v) ↔ (∃ u, U.mulVecLin u = v)
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨![-Complex.I * x 0, -(1 / 3 : ℂ) * x 1], ?_⟩
      funext i
      fin_cases i <;> simp [X, U, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    · rintro ⟨u, rfl⟩
      refine ⟨![Complex.I * u 0, -3 * u 1, 0], ?_⟩
      funext i
      fin_cases i <;>
        norm_num [X, U, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, ← mul_assoc, Complex.I_mul_I]
  have hK : X.mulVecLin.ker = S.mulVecLin.range := by
    ext v
    change X.mulVecLin v = 0 ↔ ∃ t, S.mulVecLin t = v
    constructor
    · intro h
      have hv₀ : v 0 = 0 := by
        simpa [X, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Complex.I_ne_zero] using
          congrFun h (2 : Fin 6)
      have hv₁ : v 1 = 0 := by
        simpa [X, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using congrFun h (3 : Fin 6)
      refine ⟨![v 2], ?_⟩
      funext i
      fin_cases i <;> simp [S, Matrix.mulVec, dotProduct, hv₀, hv₁]
    · rintro ⟨t, rfl⟩
      funext i
      fin_cases i <;> simp [X, S, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  refine ⟨⟨mem_one_two_iff.mpr ⟨hi, ho⟩, hR, hK⟩, ?_⟩
  intro Y hy hyR hyK
  exact outerInverse_eq_of_eq_range_ker ho (mem_one_two_iff.mp hy).2
    (hyR.trans hR.symm) (hyK.trans hK.symm)

/-- **Exercise 43** of [benIsrael2003generalized], Chapter 2. If the columns of $F$
and $G^H$ are bases for the ranges of $E$ and $E^H$, respectively, then the idempotent
$E$ equals $F(GF)^{-1}G$. -/
theorem exercise_43 {k : Type*} [Fintype k] [DecidableEq k] {E : Matrix n n ℂ}
    (hE : IsIdempotentElem E) (F : Matrix n k ℂ) (G : Matrix k n ℂ)
    (hF : F.mulVecLin.range = E.mulVecLin.range)
    (hG : Gᴴ.mulVecLin.range = Eᴴ.mulVecLin.range) (hRankF : F.rank = Fintype.card k) :
    IsUnit (G * F) ∧ E = F * (G * F)⁻¹ * G := by
  have hInner : E.IsInnerInverse E := by rw [isInnerInverse_iff, hE.eq, hE.eq]
  have hAdjId : Eᴴ * Eᴴ = Eᴴ := by rw [← conjTranspose_mul, hE.eq]
  have hAdjInner : Eᴴ.IsInnerInverse Eᴴ := by rw [isInnerInverse_iff, hAdjId, hAdjId]
  have hEF : E * F = F := by
    simpa only [hE.eq] using mul_inner_mul_of_range_le hInner F hF.le
  have hAdjFix : Eᴴ * Gᴴ = Gᴴ := by
    simpa only [hAdjId] using mul_inner_mul_of_range_le hAdjInner Gᴴ hG.le
  have hGE : G * E = G := by
    rw [← conjTranspose_conjTranspose (G * E), conjTranspose_mul, hAdjFix,
      conjTranspose_conjTranspose]
  have hRankG : G.rank = E.rank := calc
    G.rank = Gᴴ.rank := (rank_conjTranspose _).symm
    _ = Eᴴ.rank := congrArg (fun L : Submodule ℂ (n → ℂ) => finrank ℂ L) hG
    _ = E.rank := rank_conjTranspose _
  have hKer : G.mulVecLin.ker = E.mulVecLin.ker := by
    have hr : (G * E).rank = E.rank := by rwa [hGE]
    simpa only [hGE] using (Chapter01.exercise_10 G E).2.mpr hr
  have hKerF : F.mulVecLin.ker = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    have hr := LinearMap.finrank_range_add_finrank_ker F.mulVecLin
    change F.rank + finrank ℂ F.mulVecLin.ker = finrank ℂ (k → ℂ) at hr
    rw [hRankF, finrank_fintype_fun_eq_card] at hr
    omega
  have hKerGF : (G * F).mulVecLin.ker = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hxG : F.mulVecLin x ∈ G.mulVecLin.ker := by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← mulVecLin_mul]
      exact hx
    have hxE : F.mulVecLin x ∈ E.mulVecLin.ker := hKer ▸ hxG
    have hxF : E.mulVecLin (F.mulVecLin x) = F.mulVecLin x := by
      rw [← LinearMap.comp_apply, ← mulVecLin_mul, hEF]
    have hzero : F.mulVecLin x = 0 := hxF.symm.trans (LinearMap.mem_ker.mp hxE)
    exact LinearMap.ker_eq_bot'.mp hKerF x hzero
  have hUnit : IsUnit (G * F) :=
    mulVec_injective_iff_isUnit.mp (LinearMap.ker_eq_bot.mp hKerGF)
  refine ⟨hUnit, ?_⟩
  let Y := F * (G * F)⁻¹ * G
  have hYF : Y * F = F := calc
    Y * F = F * ((G * F)⁻¹ * (G * F)) := by simp only [Y, Matrix.mul_assoc]
    _ = F := by rw [nonsing_inv_mul _ (isUnit_iff_isUnit_det _ |>.mp hUnit), Matrix.mul_one]
  have hYE : Y * E = Y := by dsimp only [Y]; rw [Matrix.mul_assoc, hGE]
  change E = Y
  rw [ext_iff_mulVec]
  intro x
  obtain ⟨y, hy⟩ := hF.symm ▸ LinearMap.mem_range_self E.mulVecLin x
  change E.mulVecLin x = Y.mulVecLin x
  calc
    E.mulVecLin x = F.mulVecLin y := hy.symm
    _ = Y.mulVecLin (F.mulVecLin y) := by rw [← LinearMap.comp_apply, ← mulVecLin_mul, hYF]
    _ = Y.mulVecLin (E.mulVecLin x) := by rw [hy]
    _ = Y.mulVecLin x := by rw [← LinearMap.comp_apply, ← mulVecLin_mul, hYE]

/-- **Exercise 44** of [benIsrael2003generalized], Chapter 2. For a full-rank
factorization $A=FG$, a reflexive inverse with the range and kernel of $A$ exists
precisely when $GF$ is invertible. Its value is then $F(GF)^{-2}G$. -/
theorem exercise_44 {k : Type*} [Fintype k] [DecidableEq k]
    (F : Matrix n k ℂ) (G : Matrix k n ℂ)
    (hF : F.rank = Fintype.card k) (hG : G.rank = Fintype.card k) (X : Matrix n n ℂ) :
    let A := F * G
    (X ∈ definition_1 A {.inner, .outer} ∧
      X.mulVecLin.range = A.mulVecLin.range ∧ X.mulVecLin.ker = A.mulVecLin.ker) ↔
      IsUnit (G * F) ∧ X = F * (G * F)⁻¹ ^ 2 * G := by
  classical
  dsimp only
  let A := F * G
  rw [← Chapter04.theorem_4_3 F G hF hG X]
  change _ ↔ _root_.IsGroupInverse A X
  rw [isGroupInverse_iff]
  constructor
  · rintro ⟨hX, hR, hK⟩
    obtain ⟨hi, ho⟩ := mem_one_two_iff.mp hX
    have hs := isOuterInverse_iff_isInnerInverse.mp ho
    obtain ⟨⟨hc, _⟩, _⟩ := corollary_7 hX
    have hComp : IsCompl A.mulVecLin.range A.mulVecLin.ker := hK ▸ hc
    have hAX := eq_projectorMatrix hComp hi.isIdempotentElem_mul hi.range_mul
      (hs.ker_mul_rev.trans hK)
    have hXA := eq_projectorMatrix hComp hi.isIdempotentElem_mul_rev (hs.range_mul.trans hR)
      hi.ker_mul_rev
    exact ⟨hAX.trans hXA.symm, hi, ho⟩
  · rintro ⟨hComm, hi, ho⟩
    have hInner := isInnerInverse_iff.mpr hi
    have hs := isOuterInverse_iff_isInnerInverse.mp ho
    exact ⟨mem_one_two_iff.mpr ⟨hInner, ho⟩,
      hs.range_mul.symm.trans (hComm.eq ▸ hInner.range_mul),
      hs.ker_mul_rev.symm.trans (hComm.eq.symm ▸ hInner.ker_mul_rev)⟩

end BenIsraelGreville.Chapter02
