/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Rank
import Numlib.LinearAlgebra.Matrix.HermitianPart

/-!
# Solvability of saddle-point block matrices

For a real matrix `[A, Bᵀ; B, -C]` with positive semidefinite symmetric part of `A` and
positive semidefinite `C`, the null space is governed by the quadratic forms of the two
diagonal blocks. When `A` is itself symmetric, this gives a complete nonsingularity
criterion in terms of two kernel intersections.
-/

namespace Matrix

variable {n m K : Type*}

/-- A rectangular matrix over a field has injective multiplication on column vectors
exactly when its rank equals its number of columns. -/
theorem mulVec_injective_iff_rank_eq_card [Fintype n] [Field K] {M : Matrix m n K} :
    Function.Injective M.mulVec ↔ M.rank = Fintype.card n := by
  rw [mulVec_injective_iff, M.rank_eq_finrank_span_cols,
    linearIndependent_iff_card_eq_finrank_span, Set.finrank, eq_comm]

private theorem sumElim_zero [Zero K] :
    Sum.elim (0 : n → K) (0 : m → K) = (0 : n ⊕ m → K) := by
  funext i
  cases i <;> rfl

variable [Fintype n] [Fintype m]

/-- Multiplication by a block matrix kills a vector exactly when both block equations
vanish. -/
theorem fromBlocks_mulVec_sumElim_eq_zero_iff [Semiring K]
    (A : Matrix n n K) (D : Matrix n m K) (B : Matrix m n K) (C : Matrix m m K)
    (x : n → K) (y : m → K) :
    fromBlocks A D B C *ᵥ Sum.elim x y = 0 ↔
      A *ᵥ x + D *ᵥ y = 0 ∧ B *ᵥ x + C *ᵥ y = 0 := by
  rw [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, ← sumElim_zero, Sum.elim_eq_iff]

/-- With positive semidefinite symmetric part of `A` and positive semidefinite `C`,
a null vector of `[A, Bᵀ; B, -C]` satisfies the top block equation, and its components
are separately killed by the symmetric part of `A`, by `B`, and by `C` as indicated. -/
theorem fromBlocks_transpose_neg_mulVec_eq_zero_iff
    {A : Matrix n n ℝ} (B : Matrix m n ℝ) {C : Matrix m m ℝ}
    (hA : (hermitianPart A).PosSemidef) (hC : C.PosSemidef)
    (x : n → ℝ) (y : m → ℝ) :
    fromBlocks A Bᵀ B (-C) *ᵥ Sum.elim x y = 0 ↔
      A *ᵥ x + Bᵀ *ᵥ y = 0 ∧ hermitianPart A *ᵥ x = 0 ∧
        B *ᵥ x = 0 ∧ C *ᵥ y = 0 := by
  rw [fromBlocks_mulVec_sumElim_eq_zero_iff, neg_mulVec, ← sub_eq_add_neg, sub_eq_zero]
  constructor
  · rintro ⟨htop, hbottom⟩
    have hsum : x ⬝ᵥ (hermitianPart A *ᵥ x) + y ⬝ᵥ (C *ᵥ y) = 0 := by
      rw [dotProduct_mulVec_hermitianPart, ← hbottom, ← dotProduct_transpose_mulVec B x y,
        ← dotProduct_add, htop, dotProduct_zero]
    have hx : 0 ≤ x ⬝ᵥ (hermitianPart A *ᵥ x) := by
      simpa using hA.dotProduct_mulVec_nonneg x
    have hy : 0 ≤ y ⬝ᵥ (C *ᵥ y) := by simpa using hC.dotProduct_mulVec_nonneg y
    have hx0 : x ⬝ᵥ (hermitianPart A *ᵥ x) = 0 := by linarith
    have hy0 : y ⬝ᵥ (C *ᵥ y) = 0 := by linarith
    have hCy : C *ᵥ y = 0 := hC.dotProduct_mulVec_zero_iff.mp (by simpa using hy0)
    exact ⟨htop, hA.dotProduct_mulVec_zero_iff.mp (by simpa using hx0), hbottom.trans hCy, hCy⟩
  · rintro ⟨htop, _, hBx, hCy⟩
    exact ⟨htop, hBx.trans hCy.symm⟩

/-- A square matrix on a direct sum is nonsingular exactly when its homogeneous
equation forces both components to vanish. -/
theorem isUnit_iff_mulVec_sumElim [Field K] [DecidableEq n] [DecidableEq m]
    {M : Matrix (n ⊕ m) (n ⊕ m) K} :
    IsUnit M ↔ ∀ (x : n → K) (y : m → K), M *ᵥ Sum.elim x y = 0 → x = 0 ∧ y = 0 := by
  rw [← mulVec_injective_iff_isUnit, ← coe_mulVecLin, ← LinearMap.ker_eq_bot,
    ker_mulVecLin_eq_bot_iff]
  constructor
  · intro h x y hxy
    have hz := h _ hxy
    rwa [← sumElim_zero, Sum.elim_eq_iff] at hz
  · intro h z hz
    rw [← Sum.elim_comp_inl_inr z] at hz ⊢
    obtain ⟨hx, hy⟩ := h _ _ hz
    rw [hx, hy, sumElim_zero]

variable [DecidableEq n] [DecidableEq m]

/-- If both diagonal data blocks are positive semidefinite, nonsingularity of the
saddle-point matrix is equivalent to triviality of both kernel intersections. -/
theorem isUnit_fromBlocks_transpose_neg_iff
    {A : Matrix n n ℝ} (B : Matrix m n ℝ) {C : Matrix m m ℝ}
    (hA : A.PosSemidef) (hC : C.PosSemidef) :
    IsUnit (fromBlocks A Bᵀ B (-C)) ↔
      LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ ∧
      LinearMap.ker C.mulVecLin ⊓ LinearMap.ker Bᵀ.mulVecLin = ⊥ := by
  rw [isUnit_iff_mulVec_sumElim]
  simp only [fromBlocks_transpose_neg_mulVec_eq_zero_iff B
    (hA.isHermitian.hermitianPart_eq ▸ hA) hC, hA.isHermitian.hermitianPart_eq,
    Submodule.eq_bot_iff, Submodule.mem_inf, LinearMap.mem_ker, mulVecLin_apply]
  constructor
  · intro h
    refine ⟨fun x ⟨hxA, hxB⟩ ↦ ?_, fun y ⟨hyC, hyB⟩ ↦ ?_⟩
    · exact (h x 0 (by simp [hxA, hxB])).1
    · exact (h 0 y (by simp [hyC, hyB])).2
  · rintro ⟨hx, hy⟩ x y ⟨htop, hxA, hxB, hyC⟩
    exact ⟨hx x ⟨hxA, hxB⟩, hy y ⟨hyC, by simpa [hxA] using htop⟩⟩

/-- A saddle-point matrix with positive semidefinite symmetric part of `A` and
positive semidefinite `C` is nonsingular if the symmetric part of `A` and `B`
have trivial common kernel and `B` has full row rank. -/
theorem isUnit_fromBlocks_transpose_neg_of_hermitianPart
    {A : Matrix n n ℝ} {B : Matrix m n ℝ} {C : Matrix m m ℝ}
    (hA : (hermitianPart A).PosSemidef) (hC : C.PosSemidef)
    (hB : Function.Injective Bᵀ.mulVec)
    (hker : LinearMap.ker (hermitianPart A).mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥) :
    IsUnit (fromBlocks A Bᵀ B (-C)) := by
  rw [isUnit_iff_mulVec_sumElim]
  intro x y hxy
  obtain ⟨htop, hHx, hBx, _⟩ := (fromBlocks_transpose_neg_mulVec_eq_zero_iff B hA hC x y).1 hxy
  have hx : x = 0 := (Submodule.eq_bot_iff _).mp hker x ⟨hHx, hBx⟩
  refine ⟨hx, hB ?_⟩
  simpa [hx] using htop

/-- Nonsingularity of a block matrix forces the first block column to have trivial kernel. -/
theorem ker_inter_eq_bot_of_isUnit_fromBlocks
    [Field K] {A : Matrix n n K} {B : Matrix m n K} {D : Matrix n m K}
    {C : Matrix m m K} (h : IsUnit (fromBlocks A D B C)) :
    LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun x ⟨hxA, hxB⟩ ↦ ?_
  change A *ᵥ x = 0 at hxA
  change B *ᵥ x = 0 at hxB
  exact ((isUnit_iff_mulVec_sumElim.mp h) x 0
    ((fromBlocks_mulVec_sumElim_eq_zero_iff A D B C x 0).2
      (by simpa using And.intro hxA hxB))).1

/-- If `[A, B₁ᵀ; B₂, 0]` is nonsingular, `B₁` has full row rank and the stack of
`A` above `B₂` has full column rank. -/
theorem ranks_of_isUnit_fromBlocks_transpose_zero
    [Field K] {A : Matrix n n K} {B₁ B₂ : Matrix m n K}
    (h : IsUnit (fromBlocks A B₁ᵀ B₂ (0 : Matrix m m K))) :
    B₁.rank = Fintype.card m ∧ (fromRows A B₂).rank = Fintype.card n := by
  have hnull := isUnit_iff_mulVec_sumElim.mp h
  constructor
  · rw [← rank_transpose, ← mulVec_injective_iff_rank_eq_card, ← coe_mulVecLin,
      ← LinearMap.ker_eq_bot, ker_mulVecLin_eq_bot_iff]
    intro y hy
    exact (hnull 0 y ((fromBlocks_mulVec_sumElim_eq_zero_iff A B₁ᵀ B₂ 0 0 y).2
      (by simp [hy]))).2
  · rw [← mulVec_injective_iff_rank_eq_card, ← coe_mulVecLin, ← LinearMap.ker_eq_bot,
      ker_mulVecLin_eq_bot_iff]
    intro x hx
    rw [fromRows_mulVec, ← sumElim_zero, Sum.elim_eq_iff] at hx
    exact (Submodule.eq_bot_iff _).mp (ker_inter_eq_bot_of_isUnit_fromBlocks h) x hx

end Matrix
