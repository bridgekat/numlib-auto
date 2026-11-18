/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter00.Section05
import NumlibSurface.BenIsraelGreville.Chapter01.Section06
import NumlibSurface.BenIsraelGreville.Chapter02.Section07
import NumlibSurface.BenIsraelGreville.Chapter04.Section06
import Numlib.LinearAlgebra.Matrix.SaddlePoint.NullSpaceReduction

/-!
# Partitioned matrices and linear equations

Section 5.2 of [benIsrael2003generalized] uses a nonsingular leading block to
eliminate variables in a partitioned system. When the block has the rank of
the whole matrix, the remaining Schur complement vanishes.

## Deviations from the source

* **Exercise 6** (notation). The nonsingularity test is for $I_r+TS$.
  The correctly sized criteria $I+ST$ and $I+TS$ are equivalent by the
  rectangular determinant identity.
* **Exercise 8(d)** (correction). The kernel basis is $[-S^*;I]$, as
  required by the block dimensions and by the Gram formula.
-/

namespace BenIsraelGreville.Chapter05

open Matrix

section Pivot

variable {K r m n : Type*} [Field K] [Fintype r] [Fintype n] [DecidableEq r]

/-- **Equations (7) and (21)** of [benIsrael2003generalized], Chapter 5. The
column multiplier expresses the right block in the columns of the pivot block. -/
noncomputable def columnMultiplier (A : Matrix r r K) (B : Matrix r n K) : Matrix r n K :=
  A⁻¹ * B

/-- **Equations (13) and (21)** of [benIsrael2003generalized], Chapter 5. The
row multiplier expresses the lower block in the rows of the pivot block. -/
noncomputable def rowMultiplier (A : Matrix r r K) (C : Matrix m r K) : Matrix m r K :=
  C * A⁻¹

/-- **Exercise 2** of [benIsrael2003generalized], Chapter 5, Equation (37). Pivoting
interchanges the leading blocks of the unknown and the right-hand side. -/
noncomputable def partitionPivot (A : Matrix r r K) (B : Matrix r n K)
    (C : Matrix m r K) (D : Matrix m n K) : Matrix (r ⊕ m) (r ⊕ n) K :=
  fromBlocks A⁻¹ (-columnMultiplier A B) (rowMultiplier A C)
    (Chapter00.schurComplement A B C D)

/-- **Exercise 2** of [benIsrael2003generalized], Chapter 5. With a nonsingular
pivot block the pivoted equations describe exactly the original system. -/
theorem exercise_2 {A : Matrix r r K} (B : Matrix r n K) (C : Matrix m r K)
    (D : Matrix m n K) (hA : IsUnit A) (x : r → K) (y : n → K)
    (f : r → K) (g : m → K) :
    fromBlocks A B C D *ᵥ Sum.elim x y = Sum.elim f g ↔
      partitionPivot A B C D *ᵥ Sum.elim f y = Sum.elim x g := by
  have hInv := nonsing_inv_mul A ((isUnit_iff_isUnit_det A).mp hA)
  have hInv' := mul_nonsing_inv A ((isUnit_iff_isUnit_det A).mp hA)
  simp only [partitionPivot, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Sum.elim_eq_iff]
  have hTop : A *ᵥ x + B *ᵥ y = f ↔ A⁻¹ *ᵥ f + (-columnMultiplier A B) *ᵥ y = x := by
    constructor
    · intro h
      rw [← h, mulVec_add, mulVec_mulVec, mulVec_mulVec, hInv, one_mulVec,
        columnMultiplier, neg_mulVec, add_neg_cancel_right]
    · intro h
      rw [← h, mulVec_add, mulVec_mulVec, hInv', one_mulVec, neg_mulVec, mulVec_neg,
        mulVec_mulVec, columnMultiplier, ← Matrix.mul_assoc, hInv', Matrix.one_mul,
        neg_add_cancel_right]
  have hBottom : rowMultiplier A C *ᵥ f + Chapter00.schurComplement A B C D *ᵥ y =
      C *ᵥ (A⁻¹ *ᵥ f + (-columnMultiplier A B) *ᵥ y) + D *ᵥ y := by
    simp only [rowMultiplier, columnMultiplier, Chapter00.schurComplement, sub_mulVec,
      mulVec_add, mulVec_mulVec, neg_mulVec, mulVec_neg, Matrix.mul_assoc]
    abel
  rw [hTop, hBottom]
  exact and_congr_right fun h => by rw [h]

/-- **Exercise 1(b)** of [benIsrael2003generalized], Chapter 5. Eliminating the
leading unknown gives the Schur complement equation and the back substitution. -/
theorem exercise_1_b {A : Matrix r r K} (B : Matrix r n K) (C : Matrix m r K)
    (D : Matrix m n K) (hA : IsUnit A) (x : r → K) (y : n → K)
    (f : r → K) (g : m → K) :
    fromBlocks A B C D *ᵥ Sum.elim x y = Sum.elim f g ↔
      Chapter00.schurComplement A B C D *ᵥ y = g - rowMultiplier A C *ᵥ f ∧
        x = A⁻¹ *ᵥ (f - B *ᵥ y) := by
  rw [exercise_2 B C D hA]
  simp only [partitionPivot, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Sum.elim_eq_iff, neg_mulVec, columnMultiplier, mulVec_sub, mulVec_mulVec, ← sub_eq_add_neg]
  rw [add_comm (rowMultiplier A C *ᵥ f), ← eq_sub_iff_add_eq]
  exact ⟨fun ⟨hx, hy⟩ => ⟨hy, hx.symm⟩, fun ⟨hy, hx⟩ => ⟨hx.symm, hy⟩⟩

/-- **Exercise 1(a)** of [benIsrael2003generalized], Chapter 5. The kernel
equations reduce to a homogeneous system for the Schur complement. -/
theorem exercise_1_a {A : Matrix r r K} (B : Matrix r n K) (C : Matrix m r K)
    (D : Matrix m n K) (hA : IsUnit A) (x : r → K) (y : n → K) :
    fromBlocks A B C D *ᵥ Sum.elim x y = 0 ↔
      Chapter00.schurComplement A B C D *ᵥ y = 0 ∧
        x = -(columnMultiplier A B *ᵥ y) := by
  have hz : Sum.elim (0 : r → K) (0 : m → K) = 0 := by
    ext i
    cases i <;> rfl
  simpa only [hz, mulVec_zero, sub_zero, zero_sub, mulVec_neg,
    columnMultiplier, mulVec_mulVec] using exercise_1_b B C D hA x y 0 0

end Pivot

section RankAdapted

variable {K r m n : Type*} [Field K] [Fintype r] [Finite m] [Fintype n] [DecidableEq r]

/-- **Equation (19)** of [benIsrael2003generalized], Chapter 5. Reordering
the rows and columns puts a maximal nonsingular minor in the leading block. -/
theorem exists_rankAdapted_partition (M : Matrix m n K) :
    ∃ (p : Fin M.rank ↪ m) (q : Fin M.rank ↪ n),
      ∃ (e : Fin M.rank ⊕ {i : m // i ∉ Set.range p} ≃ m)
        (f : Fin M.rank ⊕ {j : n // j ∉ Set.range q} ≃ n),
        IsUnit ((M.submatrix e f).toBlocks₁₁) := by
  classical
  obtain ⟨i, j, h⟩ := exists_det_submatrix_ne_zero M
  let p : Fin M.rank ↪ m := ⟨i, injective_of_det_submatrix_ne_zero_left M h⟩
  let q : Fin M.rank ↪ n := ⟨j, injective_of_det_submatrix_ne_zero_right M h⟩
  let e := (Equiv.sumCongr (Equiv.ofInjective p p.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range p))
  let f := (Equiv.sumCongr (Equiv.ofInjective q q.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range q))
  refine ⟨p, q, e, f, ?_⟩
  change IsUnit (M.submatrix i j)
  exact (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)

/-- The leading block and its Schur complement account for the rank of the
whole matrix when the leading block is invertible. -/
theorem rank_fromBlocks_eq_add_rank_schurComplement {A : Matrix r r K}
    (B : Matrix r n K) (C : Matrix m r K) (D : Matrix m n K) (hA : IsUnit A) :
    (fromBlocks A B C D).rank = A.rank + (Chapter00.schurComplement A B C D).rank := by
  classical
  let := Fintype.ofFinite m
  let L := fromBlocks (1 : Matrix r r K) 0 (-rowMultiplier A C) (1 : Matrix m m K)
  let R := fromBlocks (1 : Matrix r r K) (-columnMultiplier A B) 0 (1 : Matrix n n K)
  have hL : IsUnit L := isUnit_fromBlocks_zero₁₂.mpr ⟨isUnit_one, isUnit_one⟩
  have hR : IsUnit R := isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one, isUnit_one⟩
  have hd := (isUnit_iff_isUnit_det A).mp hA
  have hLeft : L * fromBlocks A B C D = fromBlocks A B 0 (Chapter00.schurComplement A B C D) := by
    simp [L, fromBlocks_multiply, rowMultiplier, Chapter00.schurComplement,
      nonsing_inv_mul_cancel_right A C hd, sub_eq_add_neg, add_comm]
  have h : L * fromBlocks A B C D * R =
      fromBlocks A 0 0 (Chapter00.schurComplement A B C D) := by
    rw [hLeft]
    simp [R, fromBlocks_multiply, columnMultiplier, mul_nonsing_inv_cancel_left A B hd]
  have heq := congrArg rank h
  rwa [rank_mul_eq_left_of_isUnit_det R _ ((isUnit_iff_isUnit_det R).mp hR),
    rank_mul_eq_right_of_isUnit_det L _ ((isUnit_iff_isUnit_det L).mp hL),
    rank_fromBlocks_diagonal] at heq

/-- **Exercise 3** of [benIsrael2003generalized], Chapter 5. A nonsingular
leading block has the full matrix rank exactly when its Schur complement is zero. -/
theorem exercise_3 {A : Matrix r r K} (B : Matrix r n K) (C : Matrix m r K)
    (D : Matrix m n K) (hA : IsUnit A) :
    (fromBlocks A B C D).rank = A.rank ↔ Chapter00.schurComplement A B C D = 0 := by
  rw [rank_fromBlocks_eq_add_rank_schurComplement B C D hA,
    Nat.add_eq_left, Matrix.rank_eq_zero_iff]

/-- **Equation (22)** of [benIsrael2003generalized], Chapter 5. A rank-adapted
block matrix factors through the leading block using its row and column multipliers. -/
theorem eq_rank_factorization_of_isUnit_block {A : Matrix r r K}
    (B : Matrix r n K) (C : Matrix m r K) (D : Matrix m n K)
    (hA : IsUnit A) (hr : (fromBlocks A B C D).rank = A.rank) :
    fromBlocks A B C D =
      fromRows 1 (rowMultiplier A C) * A * fromCols 1 (columnMultiplier A B) := by
  have hSchur := (exercise_3 B C D hA).mp hr
  change D - C * A⁻¹ * B = 0 at hSchur
  have hd := (isUnit_iff_isUnit_det A).mp hA
  rw [fromRows_mul, fromRows_mul_fromCols]
  simp only [rowMultiplier, columnMultiplier, Matrix.one_mul,
    Matrix.mul_one, nonsing_inv_mul_cancel_right A C hd,
    mul_nonsing_inv_cancel_left A B hd]
  rw [sub_eq_zero.mp hSchur, Matrix.mul_assoc]

omit [Finite m] in
private theorem fromRows_one_injective (S : Matrix m r K) :
    Function.Injective (fromRows (1 : Matrix r r K) S).mulVec := by
  intro x y h
  simpa only [fromRows_mulVec, one_mulVec, Sum.elim_comp_inl] using
    congrArg (fun v : r ⊕ m → K => v ∘ Sum.inl) h

private theorem fromCols_one_surjective (T : Matrix r n K) :
    Function.Surjective (fromCols (1 : Matrix r r K) T).mulVec := by
  intro x
  refine ⟨Sum.elim x 0, ?_⟩
  simp

omit [Finite m] in
/-- **Lemma 1** of [benIsrael2003generalized], Chapter 5. In block coordinates
the columns of $[-T;I]$ form a basis of the kernel and the columns of $[I;S]$
form a basis of the range. -/
theorem lemma_5_1 [DecidableEq n] {A : Matrix r r K} (S : Matrix m r K)
    (T : Matrix r n K) (hA : IsUnit A) :
    let F := fromRows (1 : Matrix r r K) S
    let G := fromCols (1 : Matrix r r K) T
    let M := F * A * G
    IsNullBasis M (fromRows (-T) (1 : Matrix n n K)) ∧
      Function.Injective F.mulVec ∧ F.mulVecLin.range = M.mulVecLin.range := by
  dsimp only
  let F := fromRows (1 : Matrix r r K) S
  let G := fromCols (1 : Matrix r r K) T
  have hF := fromRows_one_injective S
  have hG := fromCols_one_surjective T
  have hAi := mulVec_injective_of_isUnit hA
  have hAs := mulVec_surjective_iff_isUnit.mpr hA
  have hKer : (F * A * G).mulVecLin.ker = G.mulVecLin.ker := by
    ext x
    simp only [LinearMap.mem_ker, mulVecLin_apply, ← mulVec_mulVec]
    exact ⟨fun h => hAi (hF (by simpa only [mulVec_zero] using h)),
      fun h => by rw [h, mulVec_zero, mulVec_zero]⟩
  have hRange : (F * A * G).mulVecLin.range = F.mulVecLin.range := by
    rw [mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr hG), mulVecLin_mul,
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hAs)]
  have hZ : IsNullBasis G (fromRows (-T) (1 : Matrix n n K)) := by
    simpa only [inv_one, Matrix.one_mul] using
      (isNullBasis_fundamental T (isUnit_one : IsUnit (1 : Matrix r r K)))
  exact ⟨⟨hZ.injective, hZ.range_eq_ker.trans hKer.symm⟩, hF, hRange.symm⟩

/-- **Theorem 1** of [benIsrael2003generalized], Chapter 5. A rank-adapted
system is consistent exactly when the lower right-hand side is determined by
the row multiplier. In that case the trailing unknown can be chosen freely. -/
theorem theorem_5_1 {A : Matrix r r K} (B : Matrix r n K) (C : Matrix m r K)
    (D : Matrix m n K) (hA : IsUnit A) (hr : (fromBlocks A B C D).rank = A.rank)
    (f : r → K) (g : m → K) :
    ((∃ z, fromBlocks A B C D *ᵥ z = Sum.elim f g) ↔ g = rowMultiplier A C *ᵥ f) ∧
      ∀ x y, fromBlocks A B C D *ᵥ Sum.elim x y = Sum.elim f g ↔
        g = rowMultiplier A C *ᵥ f ∧
          x = A⁻¹ *ᵥ f - columnMultiplier A B *ᵥ y := by
  have hS := (exercise_3 B C D hA).mp hr
  have hSol (x : r → K) (y : n → K) :
      fromBlocks A B C D *ᵥ Sum.elim x y = Sum.elim f g ↔
        g = rowMultiplier A C *ᵥ f ∧ x = A⁻¹ *ᵥ f - columnMultiplier A B *ᵥ y := by
    rw [exercise_1_b B C D hA, hS, zero_mulVec, eq_comm (a := 0), sub_eq_zero,
      mulVec_sub, mulVec_mulVec, columnMultiplier]
  refine ⟨⟨?_, ?_⟩, hSol⟩
  · rintro ⟨z, hz⟩
    rw [← Sum.elim_comp_inl_inr z] at hz
    exact ((hSol _ _).mp hz).1
  · intro hg
    exact ⟨Sum.elim _ 0, (hSol _ 0).mpr ⟨hg, rfl⟩⟩

/-- **Exercise 4(a)** of [benIsrael2003generalized], Chapter 5. In a
rank-adapted partition the trailing component of a kernel vector is arbitrary. -/
theorem exercise_4_a {A : Matrix r r K} (B : Matrix r n K) (C : Matrix m r K)
    (D : Matrix m n K) (hA : IsUnit A) (hr : (fromBlocks A B C D).rank = A.rank)
    (x : r → K) (y : n → K) :
    fromBlocks A B C D *ᵥ Sum.elim x y = 0 ↔ x = -(columnMultiplier A B *ᵥ y) := by
  simp only [exercise_1_a B C D hA, (exercise_3 B C D hA).mp hr, zero_mulVec, eq_self, true_and]

end RankAdapted

section Inverses

open scoped ComplexOrder

variable {r m n : Type*} [Fintype r] [Fintype m] [Fintype n] [DecidableEq r]

private theorem factorized_inverse {A : Matrix r r ℂ} (hA : IsUnit A)
    (F : Matrix (r ⊕ m) r ℂ) (G : Matrix r (r ⊕ n) ℂ)
    (U : Matrix r (r ⊕ m) ℂ) (V : Matrix (r ⊕ n) r ℂ)
    (hU : U * F = 1) (hV : G * V = 1) :
    let M := F * A * G
    let X := V * A⁻¹ * U
    M.IsInnerInverse X ∧ M.IsOuterInverse X ∧ M * X = F * U ∧ X * M = V * G := by
  let M := F * A * G
  let X := V * A⁻¹ * U
  change M.IsInnerInverse X ∧ M.IsOuterInverse X ∧ M * X = F * U ∧ X * M = V * G
  have hd := (isUnit_iff_isUnit_det A).mp hA
  have hMX : M * X = F * U := calc
    M * X = F * (A * (G * V) * A⁻¹) * U := by simp only [M, X, Matrix.mul_assoc]
    _ = F * U := by rw [hV, Matrix.mul_one, mul_nonsing_inv A hd, Matrix.mul_one]
  have hXM : X * M = V * G := calc
    X * M = V * (A⁻¹ * (U * F) * A) * G := by simp only [M, X, Matrix.mul_assoc]
    _ = V * G := by rw [hU, Matrix.mul_one, nonsing_inv_mul A hd, Matrix.mul_one]
  refine ⟨?_, ?_, hMX, hXM⟩
  · rw [isInnerInverse_iff, hMX]
    calc
      F * U * M = F * (U * F) * A * G := by simp only [M, Matrix.mul_assoc]
      _ = M := by rw [hU, Matrix.mul_one]
  · rw [isOuterInverse_iff, hXM]
    calc
      V * G * X = V * (G * V) * A⁻¹ * U := by simp only [X, Matrix.mul_assoc]
      _ = X := by rw [hV, Matrix.mul_one]

/-- **Theorem 2** of [benIsrael2003generalized], Chapter 5, Equations (25)–(28).
The leading block and its row and column multipliers determine reflexive,
least-squares, minimum-norm, and Moore–Penrose inverses in block coordinates. -/
theorem theorem_5_2 [DecidableEq n] {A : Matrix r r ℂ}
    (B : Matrix r n ℂ) (C : Matrix m r ℂ) (D : Matrix m n ℂ)
    (hA : IsUnit A) (hr : (fromBlocks A B C D).rank = A.rank) :
    let M := fromBlocks A B C D
    let S := rowMultiplier A C
    let T := columnMultiplier A B
    let F := fromRows (1 : Matrix r r ℂ) S
    let G := fromCols (1 : Matrix r r ℂ) T
    let U₀ := fromCols (1 : Matrix r r ℂ) (0 : Matrix r m ℂ)
    let V₀ := fromRows (1 : Matrix r r ℂ) (0 : Matrix n r ℂ)
    let U := (1 + Sᴴ * S)⁻¹ * Fᴴ
    let V := Gᴴ * (1 + T * Tᴴ)⁻¹
    V₀ * A⁻¹ * U₀ ∈ Chapter01.definition_1 M {.inner, .outer} ∧
      V₀ * A⁻¹ * U ∈ Chapter01.definition_1 M {.inner, .outer, .hermitianMul} ∧
      V * A⁻¹ * U₀ ∈ Chapter01.definition_1 M {.inner, .outer, .hermitianMulRev} ∧
      M.pinv = V * A⁻¹ * U := by
  classical
  dsimp only
  let M := fromBlocks A B C D
  let S := rowMultiplier A C
  let T := columnMultiplier A B
  let F := fromRows (1 : Matrix r r ℂ) S
  let G := fromCols (1 : Matrix r r ℂ) T
  let U₀ := fromCols (1 : Matrix r r ℂ) (0 : Matrix r m ℂ)
  let V₀ := fromRows (1 : Matrix r r ℂ) (0 : Matrix n r ℂ)
  let U := (1 + Sᴴ * S)⁻¹ * Fᴴ
  let V := Gᴴ * (1 + T * Tᴴ)⁻¹
  change V₀ * A⁻¹ * U₀ ∈ Chapter01.definition_1 M {.inner, .outer} ∧
    V₀ * A⁻¹ * U ∈ Chapter01.definition_1 M {.inner, .outer, .hermitianMul} ∧
    V * A⁻¹ * U₀ ∈ Chapter01.definition_1 M {.inner, .outer, .hermitianMulRev} ∧
    M.pinv = V * A⁻¹ * U
  have hM : M = F * A * G := eq_rank_factorization_of_isUnit_block B C D hA hr
  have hU₀ : U₀ * F = 1 := by simp [U₀, F, fromCols_mul_fromRows]
  have hV₀ : G * V₀ = 1 := by simp [V₀, G, fromCols_mul_fromRows]
  have hF : F.rank = Fintype.card r :=
    mulVec_injective_iff_rank_eq_card.mp (fromRows_one_injective S)
  have hG : G.rank = Fintype.card r :=
    mulVec_surjective_iff_rank_eq_card.mp (fromCols_one_surjective T)
  have hFGram : Fᴴ * F = 1 + Sᴴ * S := by
    simp [F, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]
  have hGGram : G * Gᴴ = 1 + T * Tᴴ := by
    simp [G, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows]
  have hFu : IsUnit (Fᴴ * F) := mulVec_surjective_iff_isUnit.mp
    (mulVec_surjective_iff_rank_eq_card.mpr (F.rank_conjTranspose_mul_self.trans hF))
  have hGu : IsUnit (G * Gᴴ) := mulVec_surjective_iff_isUnit.mp
    (mulVec_surjective_iff_rank_eq_card.mpr (G.rank_self_mul_conjTranspose.trans hG))
  have hU : U = F.pinv := by
    dsimp only [U]
    rw [← hFGram, Matrix.pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit hFu]
  have hV : V = G.pinv := by
    change Gᴴ * (1 + T * Tᴴ)⁻¹ = G.pinv
    rw [← hGGram]
    have hGu' : IsUnit (Gᴴᴴ * Gᴴ) := by rwa [conjTranspose_conjTranspose]
    have h := congrArg Matrix.conjTranspose
      (Matrix.pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit hGu')
    simpa only [Matrix.pinv_conjTranspose, conjTranspose_conjTranspose, conjTranspose_mul,
      (isHermitian_mul_conjTranspose_self G).inv.eq] using h.symm
  have hUF : U * F = 1 := by
    rw [hU]
    exact (Chapter01.lemma_2_a (Chapter01.mem_one_iff.mpr F.mul_pinv_mul_self)).mpr hF
  have hGV : G * V = 1 := by
    rw [hV]
    exact (Chapter01.lemma_2_b (Chapter01.mem_one_iff.mpr G.mul_pinv_mul_self)).mpr hG
  rw [hM]
  obtain ⟨h12i, h12o, -, -⟩ := factorized_inverse hA F G U₀ V₀ hU₀ hV₀
  obtain ⟨h123i, h123o, h123h, -⟩ := factorized_inverse hA F G U V₀ hUF hV₀
  obtain ⟨h124i, h124o, -, h124h⟩ := factorized_inverse hA F G U₀ V hU₀ hGV
  obtain ⟨h1234i, h1234o, hLeft, hRight⟩ := factorized_inverse hA F G U V hUF hGV
  refine ⟨Chapter01.mem_one_two_iff.mpr ⟨h12i, h12o⟩, ?_, ?_, ?_⟩
  · rw [Chapter01.definition_1, mem_penroseInverses_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    refine ⟨h123i, h123o, ?_⟩
    change ((F * A * G) * (V₀ * A⁻¹ * U)).IsHermitian
    rw [h123h, hU]
    exact F.isHermitian_mul_pinv
  · rw [Chapter01.definition_1, mem_penroseInverses_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    refine ⟨h124i, h124o, ?_⟩
    change ((V * A⁻¹ * U₀) * (F * A * G)).IsHermitian
    rw [h124h, hV]
    exact G.isHermitian_pinv_mul
  · symm
    refine (F * A * G).pinv_unique h1234i h1234o ?_ ?_
    · rw [hLeft, hU]
      exact F.isHermitian_mul_pinv
    · rw [hRight, hV]
      exact G.isHermitian_pinv_mul

/-- **Exercise 5** of [benIsrael2003generalized], Chapter 5.
The row and column slices of a rank-adapted partition give the
Zlobec formula for the Moore–Penrose inverse. -/
theorem exercise_5 [DecidableEq n] {A : Matrix r r ℂ}
    (B : Matrix r n ℂ) (C : Matrix m r ℂ) (D : Matrix m n ℂ)
    (hA : IsUnit A) (hr : (fromBlocks A B C D).rank = A.rank) :
    let M := fromBlocks A B C D
    let F := fromRows A C
    let G := fromCols A B
    IsUnit (G * Mᴴ * F) ∧ M.pinv = Gᴴ * (G * Mᴴ * F)⁻¹ᴴ * Fᴴ := by
  classical
  let M := fromBlocks A B C D
  let F := fromRows A C
  let G := fromCols A B
  change IsUnit (G * Mᴴ * F) ∧ M.pinv = Gᴴ * (G * Mᴴ * F)⁻¹ᴴ * Fᴴ
  have hd := (isUnit_iff_isUnit_det A).mp hA
  have hF : F = fromRows (1 : Matrix r r ℂ) (rowMultiplier A C) * A := by
    simp [F, fromRows_mul, rowMultiplier, nonsing_inv_mul_cancel_right A C hd]
  have hG : G = A * fromCols (1 : Matrix r r ℂ) (columnMultiplier A B) := by
    simp [G, mul_fromCols, columnMultiplier, mul_nonsing_inv_cancel_left A B hd]
  have hM : M = (F * A⁻¹) * G := by
    change fromBlocks A B C D = _
    rw [eq_rank_factorization_of_isUnit_block B C D hA hr, hF, hG,
      Matrix.mul_assoc _ A A⁻¹, mul_nonsing_inv A hd, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  have hCard : M.rank = Fintype.card r := hr.trans (rank_of_isUnit _ hA)
  have hRank := hM ▸ hCard
  have hrF : F.rank = Fintype.card r := le_antisymm F.rank_le_card_width <|
    hRank.symm.le.trans ((rank_mul_le_left (F * A⁻¹) G).trans (rank_mul_le_left F A⁻¹))
  have hrG : G.rank = Fintype.card r := le_antisymm G.rank_le_card_height <|
    hRank.symm.le.trans (rank_mul_le_right (F * A⁻¹) G)
  have hFu : IsUnit (Fᴴ * F) := isUnit_of_rank_eq_card (F.rank_conjTranspose_mul_self.trans hrF)
  have hGu : IsUnit (G * Gᴴ) := isUnit_of_rank_eq_card (G.rank_self_mul_conjTranspose.trans hrG)
  have hcenter : Fᴴ * M * Gᴴ = (Fᴴ * F) * A⁻¹ * (G * Gᴴ) := by
    conv_lhs => rw [hM]
    simp only [Matrix.mul_assoc]
  have hU := ((hFu.mul ((isUnit_nonsing_inv_iff).mpr hA)).mul hGu)
  have hCenterUnit : IsUnit (Fᴴ * M * Gᴴ) := hcenter ▸ hU
  have hAdj : (G * Mᴴ * F)ᴴ = Fᴴ * M * Gᴴ := by
    simp [conjTranspose_mul, Matrix.mul_assoc]
  have hU' : IsUnit (G * Mᴴ * F) := by
    simpa only [← hAdj, star_eq_conjTranspose, conjTranspose_conjTranspose] using hCenterUnit.star
  refine ⟨hU', ?_⟩
  have hu : F.pinv = (Fᴴ * F)⁻¹ * Fᴴ :=
    pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit hFu
  have hv : G.pinv = Gᴴ * (G * Gᴴ)⁻¹ := by
    have h : IsUnit (Gᴴᴴ * Gᴴ) := by simpa only [conjTranspose_conjTranspose] using hGu
    simpa only [pinv_conjTranspose, conjTranspose_conjTranspose, conjTranspose_mul,
      (isHermitian_mul_conjTranspose_self G).inv.eq] using
      congrArg Matrix.conjTranspose
        (Matrix.pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit h)
  have hUF : F.pinv * F = 1 :=
    (Chapter01.lemma_2_a (Chapter01.mem_one_iff.mpr F.mul_pinv_mul_self)).mpr hrF
  have hGV : G * G.pinv = 1 :=
    (Chapter01.lemma_2_b (Chapter01.mem_one_iff.mpr G.mul_pinv_mul_self)).mpr hrG
  obtain ⟨h₁, h₂, h₃, h₄⟩ := factorized_inverse
    (isUnit_nonsing_inv_iff.mpr hA) F G F.pinv G.pinv hUF hGV
  conv_lhs => rw [hM]
  rw [conjTranspose_nonsing_inv, hAdj, hcenter, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  let := hA.invertible
  rw [Matrix.inv_inv_of_invertible]
  have hp : (F * A⁻¹ * G).pinv = G.pinv * A⁻¹⁻¹ * F.pinv := by
    symm
    refine (F * A⁻¹ * G).pinv_unique h₁ h₂ ?_ ?_
    · rw [h₃]
      exact F.isHermitian_mul_pinv
    · rw [h₄]
      exact G.isHermitian_pinv_mul
  rw [hp, Matrix.inv_inv_of_invertible, hu, hv]
  simp only [Matrix.mul_assoc]

end Inverses

section Reindex

variable {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']

/-- Row and column permutations in Equations (25)–(28) transport every
Penrose inverse class between the original matrix and its block coordinates. -/
theorem penroseInverses_submatrix_equiv (A : Matrix m n ℂ) (X : Matrix n m ℂ)
    (e : m' ≃ m) (f : n' ≃ n) (s : Set PenroseCondition) :
    X.submatrix f e ∈ Chapter01.definition_1 (A.submatrix e f) s ↔
      X ∈ Chapter01.definition_1 A s := by
  simp only [Chapter01.definition_1, mem_penroseInverses_iff]
  refine forall_congr' fun c => imp_congr_right fun _ => ?_
  cases c <;> simp only [PenroseCondition.Holds, isInnerInverse_iff, isOuterInverse_iff,
    submatrix_mul_equiv, (submatrix_injective e.surjective f.surjective).eq_iff,
    (submatrix_injective f.surjective e.surjective).eq_iff, isHermitian_submatrix_equiv]

/-- **Equation (28)** of [benIsrael2003generalized], Chapter 5. The
Moore–Penrose inverse reorders its indices by the column and row permutations. -/
theorem pinv_submatrix_equiv [DecidableEq n] [DecidableEq n']
    (A : Matrix m n ℂ) (e : m' ≃ m) (f : n' ≃ n) :
    (A.submatrix e f).pinv = A.pinv.submatrix f e := by
  have h : A.pinv ∈ Chapter01.definition_1 A Set.univ := fun c _ => A.penroseCondition_pinv c
  have h' := (penroseInverses_submatrix_equiv A A.pinv e f Set.univ).mpr h
  change _ ∈ (A.submatrix e f).penroseInverses Set.univ at h'
  rw [Matrix.penroseInverses_univ, Set.mem_singleton_iff] at h'
  exact h'.symm

end Reindex

section Square

variable {r m : Type*} [Fintype r] [Fintype m] [DecidableEq r] [DecidableEq m]

/-- The two correctly sized nonsingularity tests in **Exercise 6**
are equivalent, although the formula uses the pivot-sized matrix. -/
theorem exercise_6_isUnit_iff (S : Matrix m r ℂ) (T : Matrix r m ℂ) :
    IsUnit (1 + S * T) ↔ IsUnit (1 + T * S) := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_isUnit_det, det_one_add_mul_comm]

/-- **Exercise 6** of [benIsrael2003generalized], Chapter 5. The group inverse
of $[I;S]A[I,T]$ is determined by $I+TS$ and the leading nonsingular block. -/
theorem exercise_6 {A : Matrix r r ℂ} (S : Matrix m r ℂ) (T : Matrix r m ℂ)
    (hA : IsUnit A) (X : Matrix (r ⊕ m) (r ⊕ m) ℂ) :
    let F := fromRows (1 : Matrix r r ℂ) S
    let G := fromCols (1 : Matrix r r ℂ) T
    let J := 1 + T * S
    Chapter04.IsGroupInverse (F * A * G) X ↔ IsUnit J ∧ X = F * (J * A * J)⁻¹ * G := by
  dsimp only
  let F := fromRows (1 : Matrix r r ℂ) S
  let G := fromCols (1 : Matrix r r ℂ) T
  let J := 1 + T * S
  change Chapter04.IsGroupInverse (F * A * G) X ↔ IsUnit J ∧ X = F * (J * A * J)⁻¹ * G
  have hF : F.rank = Fintype.card r :=
    mulVec_injective_iff_rank_eq_card.mp (fromRows_one_injective S)
  have hG : (A * G).rank = Fintype.card r :=
    (rank_mul_eq_right_of_isUnit_det A G ((isUnit_iff_isUnit_det _).mp hA)).trans
      (mulVec_surjective_iff_rank_eq_card.mp (fromCols_one_surjective T))
  have hGF : G * F = J := by simp [F, G, J, fromCols_mul_fromRows]
  have hAj : IsUnit (A * J) ↔ IsUnit J := by
    rw [isUnit_iff_isUnit_det (A * J), isUnit_iff_isUnit_det J, det_mul,
      (Commute.all _ _).isUnit_mul_iff]
    exact and_iff_right ((isUnit_iff_isUnit_det A).mp hA)
  rw [Matrix.mul_assoc, Chapter04.theorem_4_3 F (A * G) hF hG,
    Matrix.mul_assoc A G F, hGF, hAj]
  refine and_congr_right fun hJ => ?_
  have hEq : F * (A * J)⁻¹ ^ 2 * (A * G) = F * (J * A * J)⁻¹ * G := calc
    F * (A * J)⁻¹ ^ 2 * (A * G) = F * (J⁻¹ * A⁻¹ * J⁻¹ * (A⁻¹ * A)) * G := by
      simp only [Introduction.inv_mul hA hJ, pow_two, Matrix.mul_assoc]
    _ = F * (J * A * J)⁻¹ * G := by
      rw [nonsing_inv_mul A ((isUnit_iff_isUnit_det _).mp hA), Matrix.mul_one,
        Introduction.inv_mul (hJ.mul hA) hJ, Introduction.inv_mul hJ hA]
      simp only [Matrix.mul_assoc]
  rw [hEq]

private theorem mem_toEuclideanLin_range_iff {u v : Type*} [Fintype v] [DecidableEq v]
    (A : Matrix u v ℂ) (x : u → ℂ) :
    WithLp.toLp 2 x ∈ LinearMap.range (toEuclideanLin A) ↔ x ∈ A.mulVecLin.range := by
  rw [LinearMap.mem_range, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨WithLp.ofLp y, congrArg WithLp.ofLp hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨WithLp.toLp 2 y, congrArg (WithLp.toLp 2) hy⟩

omit [Fintype m] [DecidableEq m] in
private theorem range_toEuclideanLin_eq_iff {u v w : Type*} [Fintype v] [Fintype w]
    [DecidableEq v] [DecidableEq w] (A : Matrix u v ℂ) (B : Matrix u w ℂ) :
    LinearMap.range (toEuclideanLin A) = LinearMap.range (toEuclideanLin B) ↔
      A.mulVecLin.range = B.mulVecLin.range := by
  constructor
  · intro h
    ext x
    rw [← mem_toEuclideanLin_range_iff A, ← mem_toEuclideanLin_range_iff B, h]
  · intro h
    ext x
    rw [← WithLp.toLp_ofLp 2 x, mem_toEuclideanLin_range_iff A,
      mem_toEuclideanLin_range_iff B, h]

/-- **Exercise 7** of [benIsrael2003generalized], Chapter 5. The row and
column multipliers of a range-Hermitian matrix are adjoints of each other. -/
theorem exercise_7 {A : Matrix r r ℂ} (S : Matrix m r ℂ) (T : Matrix r m ℂ)
    (hA : IsUnit A) :
    Chapter04.IsRangeHermitian (fromRows (1 : Matrix r r ℂ) S * A * fromCols 1 T) ↔
      S = Tᴴ := by
  let F := fromRows (1 : Matrix r r ℂ) S
  let G := fromCols (1 : Matrix r r ℂ) T
  let M := F * A * G
  change Chapter04.IsRangeHermitian M ↔ S = Tᴴ
  have hM : M.mulVecLin.range = F.mulVecLin.range := (lemma_5_1 S T hA).2.2.symm
  have hG : Gᴴ = fromRows 1 Tᴴ := by simp [G, conjTranspose_fromCols_eq_fromRows_conjTranspose]
  have hF : Fᴴ = fromCols 1 Sᴴ := by simp [F, conjTranspose_fromRows_eq_fromCols_conjTranspose]
  have hMH : Mᴴ.mulVecLin.range = (fromRows (1 : Matrix r r ℂ) Tᴴ).mulVecLin.range := by
    simp only [M, conjTranspose_mul, hG, hF, ← Matrix.mul_assoc]
    exact (lemma_5_1 Tᴴ Sᴴ ((isUnit_conjTranspose A).mpr hA)).2.2.symm
  rw [Chapter04.IsRangeHermitian, range_toEuclideanLin_eq_iff, hM, hMH]
  constructor
  · intro h
    apply (ext_iff_mulVec).mpr
    intro x
    have hx : F *ᵥ x ∈ (fromRows (1 : Matrix r r ℂ) Tᴴ).mulVecLin.range :=
      h ▸ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx
    simp only [mulVecLin_apply, F, fromRows_mulVec, one_mulVec, Sum.elim_eq_iff] at hy
    simpa only [hy.1] using hy.2.symm
  · intro h
    simp only [F, h]

end Square

section BlockProjectors

open Chapter02
open scoped ComplexOrder

variable {r m n : Type*} [Fintype r] [Fintype m] [Fintype n]
  [DecidableEq r] [DecidableEq m] [DecidableEq n]

omit [Fintype m] [DecidableEq m] in
private theorem range_toEuclideanLin_eq_of_range_mulVecLin_eq
    {F : Matrix m r ℂ} {M : Matrix m n ℂ} (h : F.mulVecLin.range = M.mulVecLin.range) :
    (toEuclideanLin F).range = (toEuclideanLin M).range := by
  ext z
  have hmem (K : Matrix m r ℂ) :
      z ∈ (toEuclideanLin K).range ↔ WithLp.ofLp z ∈ K.mulVecLin.range := by
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨WithLp.ofLp x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨WithLp.toLp 2 x, WithLp.ofLp_injective 2 hx⟩
  rw [hmem, h]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨WithLp.toLp 2 x, WithLp.ofLp_injective 2 hx⟩
  · rintro ⟨x, rfl⟩
    exact ⟨WithLp.ofLp x, rfl⟩

omit [Fintype m] [DecidableEq m] in
private theorem range_toEuclideanLin_eq_ker_of_nullBasis
    {M : Matrix m n ℂ} {Z : Matrix n r ℂ} (h : IsNullBasis M Z) :
    (toEuclideanLin Z).range = (toEuclideanLin M).ker := by
  ext x
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨y, rfl⟩
    rw [← toEuclideanLin_mul_apply, h.mul_eq_zero, map_zero, LinearMap.zero_apply]
  · intro hx
    have he : WithLp.ofLp x ∈ M.mulVecLin.ker := by
      rw [LinearMap.mem_ker, mulVecLin_apply, ← ofLp_toEuclideanLin, hx, WithLp.ofLp_zero]
    rw [← h.range_eq_ker] at he
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp he
    exact ⟨WithLp.toLp 2 y, WithLp.ofLp_injective 2 hy⟩

private theorem gramProjector_exact {F : Matrix m r ℂ} (hF : Function.Injective F.mulVec) :
    orthogonalProjector (toEuclideanLin F).range = F * (Fᴴ * F)⁻¹ * Fᴴ := by
  classical
  have hG : IsUnit (Fᴴ * F) := isUnit_of_rank_eq_card <|
    F.rank_conjTranspose_mul_self.trans (mulVec_injective_iff_rank_eq_card.mp hF)
  have hP : orthogonalProjector (toEuclideanLin F).range = F * F.pinv := by
    apply toEuclideanLin.injective
    rw [toEuclideanLin_orthogonalProjector, F.mul_pinv_eq_starProjection]
  rw [hP, Matrix.pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit hG,
    Matrix.mul_assoc]

/-- **Exercise 8** of [benIsrael2003generalized], Chapter 5.
The four orthogonal projectors of a rank-adapted partition are the Gram
projectors of the indicated range and null bases in block coordinates. -/
theorem exercise_8 {A : Matrix r r ℂ} (B : Matrix r n ℂ) (C : Matrix m r ℂ)
    (D : Matrix m n ℂ) (hA : IsUnit A) (hr : (fromBlocks A B C D).rank = A.rank) :
    let M := fromBlocks A B C D
    let S := rowMultiplier A C
    let T := columnMultiplier A B
    let F := fromRows (1 : Matrix r r ℂ) S
    let G := fromRows (1 : Matrix r r ℂ) Tᴴ
    let Z := fromRows (-T) (1 : Matrix n n ℂ)
    let W := fromRows (-Sᴴ) (1 : Matrix m m ℂ)
    orthogonalProjector (toEuclideanLin M).range = F * (1 + Sᴴ * S)⁻¹ * Fᴴ ∧
      orthogonalProjector (toEuclideanLin Mᴴ).range = G * (1 + T * Tᴴ)⁻¹ * Gᴴ ∧
      orthogonalProjector (toEuclideanLin M).ker = Z * (1 + Tᴴ * T)⁻¹ * Zᴴ ∧
      orthogonalProjector (toEuclideanLin Mᴴ).ker = W * (1 + S * Sᴴ)⁻¹ * Wᴴ := by
  dsimp only
  let S := rowMultiplier A C
  let T := columnMultiplier A B
  let F := fromRows (1 : Matrix r r ℂ) S
  let G := fromRows (1 : Matrix r r ℂ) Tᴴ
  let Z := fromRows (-T) (1 : Matrix n n ℂ)
  let W := fromRows (-Sᴴ) (1 : Matrix m m ℂ)
  have hM : fromBlocks A B C D = F * A * fromCols 1 T :=
    eq_rank_factorization_of_isUnit_block B C D hA hr
  have hMH : (fromBlocks A B C D)ᴴ = G * Aᴴ * fromCols 1 Sᴴ := by
    rw [hM, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_fromCols_eq_fromRows_conjTranspose,
      conjTranspose_fromRows_eq_fromCols_conjTranspose]
    simp [G, Matrix.mul_assoc]
  have ⟨hZ, hFi, hF⟩ := lemma_5_1 S T hA
  have hAH : IsUnit Aᴴ := hA.star
  have ⟨hW, hGi, hG⟩ := lemma_5_1 Tᴴ Sᴴ hAH
  change IsNullBasis (F * A * fromCols 1 T) Z at hZ
  change IsNullBasis (G * Aᴴ * fromCols 1 Sᴴ) W at hW
  have hFg : Fᴴ * F = 1 + Sᴴ * S := by
    simp [F, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]
  have hGg : Gᴴ * G = 1 + T * Tᴴ := by
    simp [G, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]
  have hZg : Zᴴ * Z = 1 + Tᴴ * T := by
    simp [Z, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows, add_comm]
  have hWg : Wᴴ * W = 1 + S * Sᴴ := by
    simp [W, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows, add_comm]
  have hR := congrArg (fun M => (toEuclideanLin M).range) hM
  have hRH := congrArg (fun M => (toEuclideanLin M).range) hMH
  have hK := congrArg (fun M => (toEuclideanLin M).ker) hM
  have hKH := congrArg (fun M => (toEuclideanLin M).ker) hMH
  rw [hR, hRH, hK, hKH]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← range_toEuclideanLin_eq_of_range_mulVecLin_eq hF, ← hFg]
    exact gramProjector_exact hFi
  · rw [← range_toEuclideanLin_eq_of_range_mulVecLin_eq hG, ← hGg]
    exact gramProjector_exact hGi
  · rw [← range_toEuclideanLin_eq_ker_of_nullBasis hZ, ← hZg]
    exact gramProjector_exact hZ.injective
  · rw [← range_toEuclideanLin_eq_ker_of_nullBasis hW, ← hWg]
    exact gramProjector_exact hW.injective

private theorem rangeProjector_eq_mul_pinv
    {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (X : Matrix a b ℂ) :
    orthogonalProjector (toEuclideanLin X).range = X * X.pinv := by
  apply toEuclideanLin.injective
  rw [toEuclideanLin_orthogonalProjector, X.mul_pinv_eq_starProjection]

private theorem kerProjector_eq_one_sub_pinv_mul
    {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (X : Matrix a b ℂ) :
    orthogonalProjector (toEuclideanLin X).ker = 1 - X.pinv * X := by
  have h : (toEuclideanLin X).ker = (toEuclideanLin Xᴴ).rangeᗮ := by
    rw [toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.orthogonal_range,
      LinearMap.adjoint_adjoint]
  rw [h, Chapter02.exercise_56, rangeProjector_eq_mul_pinv, pinv_conjTranspose,
    ← conjTranspose_mul, X.isHermitian_pinv_mul.eq]

/-- The row and column permutations in **Exercise 8** transport the four
Gram formulas between block coordinates and the original matrix. -/
theorem exercise_8_reindex {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (M : Matrix a b ℂ) (e : r ⊕ m ≃ a) (f : r ⊕ n ≃ b)
    {A : Matrix r r ℂ} (B : Matrix r n ℂ) (C : Matrix m r ℂ)
    (D : Matrix m n ℂ) (hA : IsUnit A) (hr : (fromBlocks A B C D).rank = A.rank)
    (hM : M.submatrix e f = fromBlocks A B C D) :
    let S := rowMultiplier A C
    let T := columnMultiplier A B
    let F := fromRows (1 : Matrix r r ℂ) S
    let G := fromRows (1 : Matrix r r ℂ) Tᴴ
    let Z := fromRows (-T) (1 : Matrix n n ℂ)
    let W := fromRows (-Sᴴ) (1 : Matrix m m ℂ)
    (orthogonalProjector (toEuclideanLin M).range).submatrix e e = F * (1 + Sᴴ * S)⁻¹ * Fᴴ ∧
      (orthogonalProjector (toEuclideanLin Mᴴ).range).submatrix f f = G * (1 + T * Tᴴ)⁻¹ * Gᴴ ∧
      (orthogonalProjector (toEuclideanLin M).ker).submatrix f f = Z * (1 + Tᴴ * T)⁻¹ * Zᴴ ∧
      (orthogonalProjector (toEuclideanLin Mᴴ).ker).submatrix e e = W * (1 + S * Sᴴ)⁻¹ * Wᴴ := by
  have hp := exercise_8 B C D hA hr
  dsimp only at hp ⊢
  rw [← hM, conjTranspose_submatrix] at hp
  simp only [rangeProjector_eq_mul_pinv, kerProjector_eq_one_sub_pinv_mul] at hp ⊢
  have hf : (1 - M.pinv * M).submatrix f f = 1 - (M.pinv * M).submatrix f f := by
    rw [← submatrix_one_equiv f]
    rfl
  have he : (1 - Mᴴ.pinv * Mᴴ).submatrix e e = 1 - (Mᴴ.pinv * Mᴴ).submatrix e e := by
    rw [← submatrix_one_equiv e]
    rfl
  rw [hf, he]
  simpa only [pinv_submatrix_equiv, submatrix_mul_equiv] using hp

end BlockProjectors

section PositiveBlocks

open scoped ComplexOrder

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

private theorem generalizedSchurFactor
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (U : Matrix m m ℂ) (hRight : A * U * B = B) (hLeft : Bᴴ * U * A = Bᴴ) :
    fromBlocks A B Bᴴ D =
      fromBlocks 1 0 (Bᴴ * U) 1 * fromBlocks A 0 0 (D - Bᴴ * U * B) *
        fromBlocks 1 (U * B) 0 1 := by
  have hR : A * (U * B) = B := by rwa [← Matrix.mul_assoc]
  simp [fromBlocks_multiply, hLeft, hR, Matrix.mul_assoc, add_comm]

omit [DecidableEq m] [DecidableEq n] in
private theorem posSemidef_diagonalBlocks_iff (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    (fromBlocks A 0 0 D).PosSemidef ↔ A.PosSemidef ∧ D.PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h
    exact ⟨(posSemidef_iff_dotProduct_mulVec.mpr h).submatrix Sum.inl,
      (posSemidef_iff_dotProduct_mulVec.mpr h).submatrix Sum.inr⟩
  · rintro ⟨hA, hD⟩
    refine ⟨IsHermitian.fromBlocks hA.isHermitian conjTranspose_zero hD.isHermitian, ?_⟩
    intro x
    rw [← Sum.elim_comp_inl_inr x, fromBlocks_mulVec]
    simpa [dotProduct, Fintype.sum_sum_type, Function.comp_def] using
      add_nonneg (hA.dotProduct_mulVec_nonneg (x ∘ Sum.inl))
        (hD.dotProduct_mulVec_nonneg (x ∘ Sum.inr))

private theorem posDef_diagonalBlocks_iff (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    (fromBlocks A 0 0 D).PosDef ↔ A.PosDef ∧ D.PosDef := by
  rw [posDef_iff_posSemidef_and_mulVec_injective,
    posDef_iff_posSemidef_and_mulVec_injective (A := A),
    posDef_iff_posSemidef_and_mulVec_injective (A := D),
    posSemidef_diagonalBlocks_iff, mulVec_injective_iff_isUnit,
    mulVec_injective_iff_isUnit, mulVec_injective_iff_isUnit, isUnit_fromBlocks_zero₂₁]
  tauto

omit [DecidableEq n] in
private theorem pinvOffDiagonal (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (D : Matrix n n ℂ) (h : (fromBlocks A B Bᴴ D).PosSemidef) : A * A.pinv * B = B := by
  let P := (1 : Matrix m m ℂ) - A * A.pinv
  have hp : P.IsHermitian := by
    change (1 - A * A.pinv)ᴴ = _
    rw [conjTranspose_sub, conjTranspose_one, A.isHermitian_mul_pinv.eq]
  have hA : A.IsHermitian := h.isHermitian.submatrix Sum.inl
  have hAP : A * P = 0 := by
    simp only [P, Matrix.mul_sub, Matrix.mul_one]
    have hh : A * (A * A.pinv) = A := calc
      _ = Aᴴ * (A * A.pinv) := congrArg (fun X => X * (A * A.pinv)) hA.eq.symm
      _ = Aᴴ := conjTranspose_mul_mul_pinv A
      _ = A := hA.eq
    rw [hh, sub_self]
  have hBP : Bᴴ * P = 0 := by
    apply Matrix.mulVec_injective
    funext x
    change (Bᴴ * P) *ᵥ x = 0 *ᵥ x
    let y := P *ᵥ x
    have hy : A *ᵥ y = 0 := by
      dsimp only [y]
      rw [mulVec_mulVec, hAP, zero_mulVec]
    have hz :
        (fromBlocks A B Bᴴ D) *ᵥ Sum.elim y 0 = Sum.elim (0 : m → ℂ) (Bᴴ *ᵥ y) := by
      simp [fromBlocks_mulVec, hy]
    have he : star (Sum.elim y (0 : n → ℂ)) ⬝ᵥ
        (fromBlocks A B Bᴴ D *ᵥ Sum.elim y 0) = 0 := by
      simp [hz, dotProduct, Fintype.sum_sum_type]
    have he' := h.dotProduct_mulVec_zero_iff.mp he
    rw [hz] at he'
    simpa [y, mulVec_mulVec] using congrArg (fun z : m ⊕ n → ℂ => z ∘ Sum.inr) he'
  have hPB : P * B = 0 := by
    simpa only [conjTranspose_mul, hp.eq, conjTranspose_conjTranspose, conjTranspose_zero] using
      congrArg Matrix.conjTranspose hBP
  simpa only [P, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero, eq_comm] using hPB

private theorem posSemidef_iff_pinvSchur
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hA : A.IsHermitian) (hRange : A * A.pinv * B = B) :
    (fromBlocks A B Bᴴ D).PosSemidef ↔
      (fromBlocks A 0 0 (D - Bᴴ * A.pinv * B)).PosSemidef := by
  have hP : A.pinv.IsHermitian := by
    change A.pinvᴴ = _
    rw [← pinv_conjTranspose, hA.eq]
  have hLeft : Bᴴ * A.pinv * A = Bᴴ := by
    simpa only [conjTranspose_mul, hP.eq, hA.eq, Matrix.mul_assoc] using
      congrArg Matrix.conjTranspose hRange
  let L : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 1 0 (Bᴴ * A.pinv) 1
  have hL : IsUnit L := isUnit_fromBlocks_zero₁₂.mpr ⟨isUnit_one, isUnit_one⟩
  have hLH : Lᴴ = fromBlocks 1 (A.pinv * B) 0 1 := by
    simp [L, fromBlocks_conjTranspose, conjTranspose_mul, hP.eq]
  rw [generalizedSchurFactor A B D A.pinv hRange hLeft, ← hLH]
  exact hL.posSemidef_star_right_conjugate_iff

/-- **Exercise 9(a)** of [benIsrael2003generalized], Chapter 5.
Positive semidefiniteness is equivalent to positivity of the leading block
and generalized Schur complement and the compatibility of the off-diagonal block. -/
theorem exercise_9_a (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ) :
    (fromBlocks A B Bᴴ D).PosSemidef ↔
      A.PosSemidef ∧ A * A.pinv * B = B ∧ (D - Bᴴ * A.pinv * B).PosSemidef := by
  constructor
  · intro h
    have hA : A.PosSemidef := h.submatrix Sum.inl
    have hR := pinvOffDiagonal A B D h
    exact ⟨hA, hR, ((posSemidef_diagonalBlocks_iff _ _).mp
      ((posSemidef_iff_pinvSchur A B D hA.isHermitian hR).mp h)).2⟩
  · rintro ⟨hA, hR, hG⟩
    exact (posSemidef_iff_pinvSchur A B D hA.isHermitian hR).mpr
      ((posSemidef_diagonalBlocks_iff _ _).mpr ⟨hA, hG⟩)

private theorem posDef_iff_schurLeading (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (D : Matrix n n ℂ) (hA : A.PosDef) :
    (fromBlocks A B Bᴴ D).PosDef ↔ (D - Bᴴ * A⁻¹ * B).PosDef := by
  have h := hA.isUnit
  have hdet := (isUnit_iff_isUnit_det A).mp h
  have hInvH : A⁻¹.IsHermitian := hA.isHermitian.inv
  have hR : A * A⁻¹ * B = B := by rw [mul_nonsing_inv _ hdet, Matrix.one_mul]
  have hL : Bᴴ * A⁻¹ * A = Bᴴ := by
    rw [Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.mul_one]
  let L : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 1 0 (Bᴴ * A⁻¹) 1
  have hLU : IsUnit L := isUnit_fromBlocks_zero₁₂.mpr ⟨isUnit_one, isUnit_one⟩
  have hLH : Lᴴ = fromBlocks 1 (A⁻¹ * B) 0 1 := by
    simp [L, fromBlocks_conjTranspose, conjTranspose_mul, hInvH.eq]
  rw [generalizedSchurFactor A B D A⁻¹ hR hL, ← hLH]
  change (L * fromBlocks A 0 0 (D - Bᴴ * A⁻¹ * B) * star L).PosDef ↔ _
  rw [hLU.posDef_star_right_conjugate_iff, posDef_diagonalBlocks_iff]
  exact and_iff_right hA

/-- **Exercise 9(b)** of [benIsrael2003generalized], Chapter 5.
Positive definiteness is tested by the leading block and the two indicated
Schur complements. -/
theorem exercise_9_b (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ) :
    (fromBlocks A B Bᴴ D).PosDef ↔
      A.PosDef ∧ (A - B * D.pinv * Bᴴ).PosDef ∧ (D - Bᴴ * A⁻¹ * B).PosDef := by
  constructor
  · intro h
    have hA : A.PosDef := h.submatrix Sum.inl_injective
    have hD : D.PosDef := h.submatrix Sum.inr_injective
    have hFlip : (fromBlocks D Bᴴ B A).PosDef := by
      simpa [Equiv.sumComm_apply, fromBlocks_submatrix_sum_swap_sum_swap] using
        h.submatrix (Equiv.sumComm n m).injective
    refine ⟨hA, ?_, (posDef_iff_schurLeading A B D hA).mp h⟩
    rw [pinv_eq_inv hD.isUnit]
    simpa only [conjTranspose_conjTranspose] using
      (posDef_iff_schurLeading D Bᴴ A hD).mp
        (by simpa only [conjTranspose_conjTranspose] using hFlip)
  · rintro ⟨hA, -, hG⟩
    exact (posDef_iff_schurLeading A B D hA).mpr hG

/-- **Equation (42)** of [benIsrael2003generalized], Chapter 5.
Rohde's block inverse constructed from inverses of the leading block and
its generalized Schur complement. -/
def rohdeSchurInverse (B : Matrix m n ℂ) (U : Matrix m m ℂ) (V : Matrix n n ℂ) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  fromBlocks (U + U * B * V * Bᴴ * U) (-(U * B * V)) (-(V * Bᴴ * U)) V

omit [Fintype n] [DecidableEq n] in
private theorem left_schur_eq_of_inner
    {A U : Matrix m m ℂ} (B : Matrix m n ℂ) (hU : A.IsInnerInverse U)
    (hR : A * A.pinv * B = B) : A * U * B = B := calc
  A * U * B = (A * U * A) * (A.pinv * B) := by
    conv_lhs => rw [← hR]
    simp only [Matrix.mul_assoc]
  _ = B := by rw [isInnerInverse_iff.mp hU, ← Matrix.mul_assoc, hR]

omit [Fintype n] [DecidableEq n] in
private theorem right_schur_eq_of_inner
    {A U : Matrix m m ℂ} (B : Matrix m n ℂ) (hA : A.IsHermitian)
    (hU : A.IsInnerInverse U) (hR : A * A.pinv * B = B) : Bᴴ * U * A = Bᴴ := by
  have hP : A.pinv.IsHermitian := by
    change A.pinvᴴ = _
    rw [← pinv_conjTranspose, hA.eq]
  have hL : Bᴴ = Bᴴ * A.pinv * A := by
    simpa only [conjTranspose_mul, hP.eq, hA.eq, Matrix.mul_assoc] using
      congrArg Matrix.conjTranspose hR.symm
  calc
    Bᴴ * U * A = Bᴴ * A.pinv * (A * U * A) := by
      conv_lhs => rw [hL]
      simp only [Matrix.mul_assoc]
    _ = Bᴴ := by rw [isInnerInverse_iff.mp hU, ← hL]

private def lowerUnit (C : Matrix n m ℂ) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  fromBlocks 1 0 C 1

private def upperUnit (B : Matrix m n ℂ) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  fromBlocks 1 B 0 1

private theorem isUnit_lowerUnit (C : Matrix n m ℂ) : IsUnit (lowerUnit C) :=
  isUnit_fromBlocks_zero₁₂.mpr ⟨isUnit_one, isUnit_one⟩

private theorem isUnit_upperUnit (B : Matrix m n ℂ) : IsUnit (upperUnit B) :=
  isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one, isUnit_one⟩

private theorem lowerUnit_mul_neg (C : Matrix n m ℂ) : lowerUnit C * lowerUnit (-C) = 1 := by
  simp [lowerUnit, fromBlocks_multiply, fromBlocks_one]

private theorem upperUnit_mul_neg (B : Matrix m n ℂ) : upperUnit B * upperUnit (-B) = 1 := by
  simp [upperUnit, fromBlocks_multiply, fromBlocks_one]

private theorem rohdeSchurInverse_factor (B : Matrix m n ℂ)
    (U : Matrix m m ℂ) (V : Matrix n n ℂ) :
    rohdeSchurInverse B U V =
      upperUnit (-(U * B)) * fromBlocks U 0 0 V * lowerUnit (-(Bᴴ * U)) := by
  simp [rohdeSchurInverse, upperUnit, lowerUnit, fromBlocks_multiply, Matrix.mul_assoc]

private theorem rohdeSchurInverse_mul_forms
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (U : Matrix m m ℂ) (V : Matrix n n ℂ)
    (hR : A * U * B = B) (hL : Bᴴ * U * A = Bᴴ) :
    let H := fromBlocks A B Bᴴ D
    let G := D - Bᴴ * U * B
    let X := rohdeSchurInverse B U V
    let L := lowerUnit (Bᴴ * U)
    let R := upperUnit (U * B)
    H * X = L * fromBlocks (A * U) 0 0 (G * V) * lowerUnit (-(Bᴴ * U)) ∧
      X * H = upperUnit (-(U * B)) * fromBlocks (U * A) 0 0 (V * G) * R := by
  dsimp only
  let G := D - Bᴴ * U * B
  have hH : fromBlocks A B Bᴴ D =
      lowerUnit (Bᴴ * U) * fromBlocks A 0 0 G * upperUnit (U * B) :=
    generalizedSchurFactor A B D U hR hL
  have hRn : upperUnit (U * B) * upperUnit (-(U * B)) = 1 := upperUnit_mul_neg _
  have hLn : lowerUnit (-(Bᴴ * U)) * lowerUnit (Bᴴ * U) = 1 := by
    simpa only [neg_neg] using lowerUnit_mul_neg (-(Bᴴ * U))
  rw [hH, rohdeSchurInverse_factor]
  constructor
  · calc
      _ = lowerUnit (Bᴴ * U) * fromBlocks A 0 0 G *
          (upperUnit (U * B) * upperUnit (-(U * B))) *
          fromBlocks U 0 0 V * lowerUnit (-(Bᴴ * U)) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hRn, Matrix.mul_one, Matrix.mul_assoc (lowerUnit _) (fromBlocks _ _ _ _) _,
          fromBlocks_multiply]
        simp [G]
  · calc
      _ = upperUnit (-(U * B)) * fromBlocks U 0 0 V *
          (lowerUnit (-(Bᴴ * U)) * lowerUnit (Bᴴ * U)) *
          fromBlocks A 0 0 G * upperUnit (U * B) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hLn, Matrix.mul_one, Matrix.mul_assoc (upperUnit _) (fromBlocks _ _ _ _) _,
          fromBlocks_multiply]
        simp [G]

/-- **Exercise 10(a)** of [benIsrael2003generalized], Chapter 5.
The block expression is an inner inverse, and it is reflexive if the
two supplied block inverses are reflexive. -/
theorem exercise_10_a (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (h : (fromBlocks A B Bᴴ D).PosSemidef) (U : Matrix m m ℂ) (V : Matrix n n ℂ)
    (hU : A.IsInnerInverse U) (hV : (D - Bᴴ * U * B).IsInnerInverse V) :
    let H := fromBlocks A B Bᴴ D
    let X := rohdeSchurInverse B U V
    H.IsInnerInverse X ∧
      (A.IsOuterInverse U → (D - Bᴴ * U * B).IsOuterInverse V → H.IsOuterInverse X) := by
  dsimp only
  let G := D - Bᴴ * U * B
  have hRange := pinvOffDiagonal A B D h
  have hA : A.IsHermitian := h.isHermitian.submatrix Sum.inl
  have hR := left_schur_eq_of_inner B hU hRange
  have hL := right_schur_eq_of_inner B hA hU hRange
  have hH : fromBlocks A B Bᴴ D =
      lowerUnit (Bᴴ * U) * fromBlocks A 0 0 G * upperUnit (U * B) :=
    generalizedSchurFactor A B D U hR hL
  obtain ⟨hHX, hXH⟩ := rohdeSchurInverse_mul_forms A B D U V hR hL
  change fromBlocks A B Bᴴ D * rohdeSchurInverse B U V =
    lowerUnit (Bᴴ * U) * fromBlocks (A * U) 0 0 (G * V) * lowerUnit (-(Bᴴ * U)) at hHX
  change rohdeSchurInverse B U V * fromBlocks A B Bᴴ D =
    upperUnit (-(U * B)) * fromBlocks (U * A) 0 0 (V * G) * upperUnit (U * B) at hXH
  change G.IsInnerInverse V at hV
  have hRn : upperUnit (U * B) * upperUnit (-(U * B)) = 1 := upperUnit_mul_neg _
  have hLn : lowerUnit (-(Bᴴ * U)) * lowerUnit (Bᴴ * U) = 1 := by
    simpa only [neg_neg] using lowerUnit_mul_neg (-(Bᴴ * U))
  constructor
  · rw [isInnerInverse_iff, hHX, hH]
    calc
      _ = lowerUnit (Bᴴ * U) * fromBlocks (A * U) 0 0 (G * V) *
          (lowerUnit (-(Bᴴ * U)) * lowerUnit (Bᴴ * U)) *
          fromBlocks A 0 0 G * upperUnit (U * B) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hLn, Matrix.mul_one, Matrix.mul_assoc (lowerUnit _) (fromBlocks _ _ _ _) _,
          fromBlocks_multiply]
        simp [isInnerInverse_iff.mp hU, isInnerInverse_iff.mp hV]
  · intro hoU hoV
    change G.IsOuterInverse V at hoV
    rw [isOuterInverse_iff, hXH, rohdeSchurInverse_factor]
    calc
      _ = upperUnit (-(U * B)) * fromBlocks (U * A) 0 0 (V * G) *
          (upperUnit (U * B) * upperUnit (-(U * B))) *
          fromBlocks U 0 0 V * lowerUnit (-(Bᴴ * U)) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hRn, Matrix.mul_one, Matrix.mul_assoc (upperUnit _) (fromBlocks _ _ _ _) _,
          fromBlocks_multiply]
        simp [isOuterInverse_iff.mp hoU, isOuterInverse_iff.mp hoV]

private theorem rohdeSchurInverse_mul_of_unit
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (U : Matrix m m ℂ) (V : Matrix n n ℂ)
    (hR : A * U * B = B) (hL : Bᴴ * U * A = Bᴴ)
    (hGV : (D - Bᴴ * U * B) * V = 1) (hVG : V * (D - Bᴴ * U * B) = 1) :
    fromBlocks A B Bᴴ D * rohdeSchurInverse B U V = fromBlocks (A * U) 0 0 1 ∧
      rohdeSchurInverse B U V * fromBlocks A B Bᴴ D = fromBlocks (U * A) 0 0 1 := by
  obtain ⟨hHX, hXH⟩ := rohdeSchurInverse_mul_forms A B D U V hR hL
  have hBL : Bᴴ * U * (A * U) = Bᴴ * U := by rw [← Matrix.mul_assoc, hL]
  have hBR : U * A * (U * B) = U * B := by
    rw [Matrix.mul_assoc U A, ← Matrix.mul_assoc A U, hR]
  rw [hHX, hXH, hGV, hVG]
  simp [lowerUnit, upperUnit, fromBlocks_multiply, hBL, hBR]

private theorem isUnit_schurComplement_of_rank
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (U : Matrix m m ℂ) (hR : A * U * B = B) (hL : Bᴴ * U * A = Bᴴ)
    (hD : IsUnit D) (hr : (fromBlocks A B Bᴴ D).rank = A.rank + D.rank) :
    IsUnit (D - Bᴴ * U * B) := by
  let G := D - Bᴴ * U * B
  have hH : fromBlocks A B Bᴴ D =
      lowerUnit (Bᴴ * U) * fromBlocks A 0 0 G * upperUnit (U * B) :=
    generalizedSchurFactor A B D U hR hL
  rw [hH, rank_mul_eq_left_of_isUnit_det _ _
      ((isUnit_iff_isUnit_det _).mp (isUnit_upperUnit (U * B))),
    rank_mul_eq_right_of_isUnit_det _ _
      ((isUnit_iff_isUnit_det _).mp (isUnit_lowerUnit (Bᴴ * U))), rank_fromBlocks_diagonal] at hr
  exact isUnit_of_rank_eq_card ((Nat.add_left_cancel hr).trans (rank_of_isUnit _ hD))

/-- **Exercise 10(b)** of [benIsrael2003generalized], Chapter 5.
Under the rank-additivity condition with invertible trailing block, the
Schur formula also preserves each Hermitian Penrose condition. -/
theorem exercise_10_b (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (h : (fromBlocks A B Bᴴ D).PosSemidef) (hD : IsUnit D)
    (hr : (fromBlocks A B Bᴴ D).rank = A.rank + D.rank)
    (U : Matrix m m ℂ) (V : Matrix n n ℂ)
    (hU : A.IsInnerInverse U) (hV : (D - Bᴴ * U * B).IsInnerInverse V) :
    let H := fromBlocks A B Bᴴ D
    let X := rohdeSchurInverse B U V
    IsUnit (D - Bᴴ * U * B) ∧
      ((A * U).IsHermitian → (H * X).IsHermitian) ∧
      ((U * A).IsHermitian → (X * H).IsHermitian) := by
  have hRange := pinvOffDiagonal A B D h
  have hA : A.IsHermitian := h.isHermitian.submatrix Sum.inl
  have hR := left_schur_eq_of_inner B hU hRange
  have hL := right_schur_eq_of_inner B hA hU hRange
  have hG := isUnit_schurComplement_of_rank A B D U hR hL hD hr
  let G := D - Bᴴ * U * B
  have hRank : G.rank = Fintype.card n := rank_of_isUnit _ hG
  have hGV : G * V = 1 := (Chapter01.lemma_2_b (Chapter01.mem_one_iff.mpr hV)).mpr hRank
  have hVG : V * G = 1 := (Chapter01.lemma_2_a (Chapter01.mem_one_iff.mpr hV)).mpr hRank
  obtain ⟨hHX, hXH⟩ := rohdeSchurInverse_mul_of_unit A B D U V hR hL hGV hVG
  refine ⟨hG, ?_, ?_⟩
  · intro hAU
    rw [hHX]
    exact hAU.fromBlocks conjTranspose_zero isHermitian_one
  · intro hUA
    rw [hXH]
    exact hUA.fromBlocks conjTranspose_zero isHermitian_one

/-- The Moore–Penrose specialization of **Exercise 10(b)**. -/
theorem exercise_10_b_pinv (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (h : (fromBlocks A B Bᴴ D).PosSemidef) (hD : IsUnit D)
    (hr : (fromBlocks A B Bᴴ D).rank = A.rank + D.rank) :
    (fromBlocks A B Bᴴ D).pinv = rohdeSchurInverse B A.pinv (D - Bᴴ * A.pinv * B).pinv := by
  let G := D - Bᴴ * A.pinv * B
  have hAi := A.mul_pinv_mul_self
  have hGi := G.mul_pinv_mul_self
  obtain ⟨hi, ho⟩ := exercise_10_a A B D h A.pinv G.pinv hAi hGi
  obtain ⟨-, hl, hr'⟩ := exercise_10_b A B D h hD hr A.pinv G.pinv hAi hGi
  exact ((fromBlocks A B Bᴴ D).pinv_unique hi
    (ho A.pinv_mul_self_mul_pinv G.pinv_mul_self_mul_pinv)
    (hl A.isHermitian_mul_pinv) (hr' A.isHermitian_pinv_mul)).symm

end PositiveBlocks

section UpperBlockGroupInverse

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

private theorem groupInverse_toBlocks₂₁_zero
    (A : Matrix m m ℂ) (C : Matrix m n ℂ) (B : Matrix n n ℂ)
    (X : Matrix (m ⊕ n) (m ⊕ n) ℂ) (hX : Chapter04.IsGroupInverse (fromBlocks A C 0 B) X) :
    X.toBlocks₂₁ = 0 := by
  let M := fromBlocks A C 0 B
  have hIdx := (Chapter04.theorem_4_2 M).mp ⟨X, hX, fun Y hY => hY.unique hX⟩
  obtain ⟨Y, ⟨hYi, hYo, p, hY⟩, _⟩ := (Chapter04.corollary_4_2_polynomial M).mpr hIdx
  have hg : Chapter04.IsGroupInverse M Y := by
    apply isGroupInverse_iff.mpr
    refine ⟨?_, hYi, hYo⟩
    rw [hY]
    exact (Commute.refl M).aeval_right p
  have he := hX.unique hg
  let b : m ⊕ n → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)
  let S := blockTriangularSubalgebra ℂ ℂ b
  have hM : M ∈ S := upper_two_blockTriangular A C B Nat.zero_lt_one
  let M' : S := ⟨M, hM⟩
  have hP : Polynomial.aeval M p ∈ S := by
    rw [← Polynomial.aeval_subalgebra_coe p S M']
    exact (Polynomial.aeval M' p).prop
  have hU : X.BlockTriangular b := by
    rw [he, hY]
    exact hP
  ext i j
  exact hU (i := Sum.inr i) (j := Sum.inl j) Nat.zero_lt_one

private theorem groupInverse_complement_relations {A G : Matrix m m ℂ}
    (h : Chapter04.IsGroupInverse A G) :
    A * (1 - A * G) = 0 ∧ (1 - A * G) * A = 0 ∧
      A * G ^ 2 = G ∧ G ^ 2 * A = G ∧ (A * G) * (1 - A * G) = 0 := by
  obtain ⟨hc, ha, hg⟩ := isGroupInverse_iff.mp h
  have hAA : A * (A * G) = A := by rw [hc.eq, ← Matrix.mul_assoc, ha]
  have hGG : A * G * G = G := by rw [hc.eq, hg]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_sub, Matrix.mul_one, hAA, sub_self]
  · rw [Matrix.sub_mul, Matrix.one_mul, ha, sub_self]
  · rw [pow_two, ← Matrix.mul_assoc, hGG]
  · rw [pow_two, Matrix.mul_assoc, ← hc.eq, ← Matrix.mul_assoc, hg]
  · rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ha, sub_self]

/-- The upper-right entry of the group inverse in **Exercise 11**. -/
def upperBlockGroupInverseEntry (A G : Matrix m m ℂ) (B H : Matrix n n ℂ)
    (C : Matrix m n ℂ) : Matrix m n ℂ :=
  G ^ 2 * C * (1 - B * H) + (1 - A * G) * C * H ^ 2 - G * C * H

private theorem upperBlockGroupInverse_correct
    {A G : Matrix m m ℂ} {B H : Matrix n n ℂ} (C : Matrix m n ℂ)
    (hG : Chapter04.IsGroupInverse A G) (hH : Chapter04.IsGroupInverse B H)
    (hC : (1 - A * G) * C * (1 - B * H) = 0) :
    Chapter04.IsGroupInverse (fromBlocks A C 0 B)
      (fromBlocks G (upperBlockGroupInverseEntry A G B H C) 0 H) := by
  let P := A * G
  let Q := B * H
  let E := (1 : Matrix m m ℂ) - P
  let F := (1 : Matrix n n ℂ) - Q
  let Z := upperBlockGroupInverseEntry A G B H C
  let K := G * C * F + E * C * H
  obtain ⟨hAg, hAgA, hGaG⟩ := isGroupInverse_iff.mp hG
  obtain ⟨hBh, hBhB, hHbH⟩ := isGroupInverse_iff.mp hH
  obtain ⟨hAE, -, hAG₂, -, hPE⟩ := groupInverse_complement_relations hG
  obtain ⟨-, hFB, -, hH₂B, -⟩ := groupInverse_complement_relations hH
  change A * E = 0 at hAE
  change P * E = 0 at hPE
  change F * B = 0 at hFB
  have hPG : P * G = G := by
    change (A * G) * G = _
    rw [hAg.eq, hGaG]
  have hFH : F * H = 0 := by
    change (1 - B * H) * H = 0
    rw [Matrix.sub_mul, Matrix.one_mul, hBh.eq, hHbH, sub_self]
  have hEC : E * C = C - P * C := by simp only [E, Matrix.sub_mul, Matrix.one_mul]
  have hCF : G * C * F = G * C - G * C * Q := by
    simp only [F, Matrix.mul_sub, Matrix.mul_one]
  have hAZ : A * Z + C * H = K := by
    change A * (G ^ 2 * C * F + E * C * H ^ 2 - G * C * H) + C * H = _
    simp only [K, Matrix.mul_sub, Matrix.mul_add, ← Matrix.mul_assoc, hAG₂, hAE, Matrix.zero_mul]
    rw [hEC, Matrix.sub_mul]
    abel
  have hZB : G * C + Z * B = K := by
    change G * C + (G ^ 2 * C * F + E * C * H ^ 2 - G * C * H) * B = _
    simp only [K, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, hFB, hH₂B, Matrix.mul_zero,
      zero_add]
    rw [← hBh.eq]
    change G * C + (E * (C * H) - G * (C * Q)) = G * (C * F) + E * (C * H)
    simp only [← Matrix.mul_assoc, hCF]
    abel
  have hKB : K * B = E * C * Q := by
    simp only [K, Matrix.add_mul, Matrix.mul_assoc, hFB, Matrix.mul_zero, zero_add, ← hBh.eq]
    rfl
  have hPC : P * C + K * B = C := by
    have he : E * C - E * C * Q = 0 := by
      change E * C * F = 0 at hC
      simpa only [F, Matrix.mul_sub, Matrix.mul_one] using hC
    rw [hKB, ← sub_eq_zero.mp he, hEC, add_sub_cancel]
  have hPZ : P * Z = G ^ 2 * C * F - G * C * H := by
    change P * (G ^ 2 * C * F + E * C * H ^ 2 - G * C * H) = _
    simp only [Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc, hPE, hPG, Matrix.zero_mul,
      add_zero]
    rw [pow_two, ← Matrix.mul_assoc, hPG]
  have hKH : K * H = E * C * H ^ 2 := by
    simp only [K, Matrix.add_mul, Matrix.mul_assoc, hFH, Matrix.mul_zero, zero_add, pow_two]
  have hPZh : P * Z + K * H = Z := by
    rw [hPZ, hKH]
    change G ^ 2 * C * F - G * C * H + E * C * H ^ 2 =
      G ^ 2 * C * F + E * C * H ^ 2 - G * C * H
    abel
  have hMX : fromBlocks A C 0 B * fromBlocks G Z 0 H = fromBlocks P K 0 Q := by
    simp [fromBlocks_multiply, P, Q, hAZ]
  have hXM : fromBlocks G Z 0 H * fromBlocks A C 0 B = fromBlocks P K 0 Q := by
    simp [fromBlocks_multiply, P, Q, hZB, ← hAg.eq, ← hBh.eq]
  change Chapter04.IsGroupInverse (fromBlocks A C 0 B) (fromBlocks G Z 0 H)
  apply isGroupInverse_iff.mpr
  refine ⟨hMX.trans hXM.symm, ?_, ?_⟩
  · rw [hMX]
    simp [fromBlocks_multiply, hPC, P, Q, hAgA, hBhB]
  · rw [hXM]
    simp [fromBlocks_multiply, hPZh, hPG, Q, hBh.eq, hHbH]

/-- **Exercise 11(a)–(b)** of [benIsrael2003generalized], Chapter 5.
An upper block triangular matrix has a group inverse precisely when
the two diagonal group inverses exist and the stated corner vanishes. -/
theorem exercise_11 (A : Matrix m m ℂ) (C : Matrix m n ℂ) (B : Matrix n n ℂ) :
    (∃ Y, Chapter04.IsGroupInverse (fromBlocks A C 0 B) Y) ↔
      ∃ G H, Chapter04.IsGroupInverse A G ∧ Chapter04.IsGroupInverse B H ∧
        (1 - A * G) * C * (1 - B * H) = 0 := by
  constructor
  · rintro ⟨Y, hY⟩
    let G := Y.toBlocks₁₁
    let Z := Y.toBlocks₁₂
    let H := Y.toBlocks₂₂
    have hz := groupInverse_toBlocks₂₁_zero A C B Y hY
    have hBlock : Y = fromBlocks G Z 0 H := by
      conv_lhs => rw [← fromBlocks_toBlocks Y, hz]
    rw [hBlock] at hY
    obtain ⟨hc, hi, ho⟩ := isGroupInverse_iff.mp hY
    have hce := hc.eq
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      fromBlocks_inj, true_and] at hce hi ho
    obtain ⟨hAG, -, hBH⟩ := hce
    obtain ⟨hAGA, hTop, hBHB⟩ := hi
    obtain ⟨hGAG, -, hHBH⟩ := ho
    have hG : Chapter04.IsGroupInverse A G := isGroupInverse_iff.mpr ⟨hAG, hAGA, hGAG⟩
    have hH : Chapter04.IsGroupInverse B H := isGroupInverse_iff.mpr ⟨hBH, hBHB, hHBH⟩
    refine ⟨G, H, hG, hH, ?_⟩
    let E := (1 : Matrix m m ℂ) - A * G
    let F := (1 : Matrix n n ℂ) - B * H
    have hEL : E * (A * G) = 0 := by
      change (1 - A * G) * (A * G) = 0
      rw [Matrix.sub_mul, Matrix.one_mul, ← Matrix.mul_assoc, hAGA, sub_self]
    have hBR : B * F = 0 := (groupInverse_complement_relations hH).1
    change E * C * F = 0
    rw [← hTop, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc E (A * G) C,
      hEL, Matrix.zero_mul, Matrix.zero_mul, zero_add]
    simp only [Matrix.mul_assoc, hBR, Matrix.mul_zero]
  · rintro ⟨G, H, hG, hH, hC⟩
    exact ⟨_, upperBlockGroupInverse_correct C hG hH hC⟩

/-- The block formula of **Exercise 11** determines the group inverse uniquely. -/
theorem exercise_11_formula
    {A G : Matrix m m ℂ} {B H : Matrix n n ℂ} (C : Matrix m n ℂ)
    (hG : Chapter04.IsGroupInverse A G) (hH : Chapter04.IsGroupInverse B H)
    (hC : (1 - A * G) * C * (1 - B * H) = 0) (Y : Matrix (m ⊕ n) (m ⊕ n) ℂ) :
    Chapter04.IsGroupInverse (fromBlocks A C 0 B) Y ↔
      Y = fromBlocks G (upperBlockGroupInverseEntry A G B H C) 0 H := by
  have he := upperBlockGroupInverse_correct C hG hH hC
  exact ⟨fun h => h.unique he, fun h => h.symm ▸ he⟩

/-- **Equation (43)** of [benIsrael2003generalized], Chapter 5.
The upper block formula simplifies when the leading diagonal block is
invertible. -/
theorem exercise_11_invertible
    (A : Matrix m m ℂ) {B H : Matrix n n ℂ} (C : Matrix m n ℂ)
    (hA : IsUnit A) (hH : Chapter04.IsGroupInverse B H) (Y : Matrix (m ⊕ n) (m ⊕ n) ℂ) :
    Chapter04.IsGroupInverse (fromBlocks A C 0 B) Y ↔
      Y = fromBlocks A⁻¹ (A⁻¹ ^ 2 * C * (1 - B * H) - A⁻¹ * C * H) 0 H := by
  have hd := (isUnit_iff_isUnit_det _).mp hA
  have hl := mul_nonsing_inv A hd
  have hr := nonsing_inv_mul A hd
  have hG : Chapter04.IsGroupInverse A A⁻¹ := isGroupInverse_iff.mpr
    ⟨hl.trans hr.symm, by rw [hl, Matrix.one_mul], by rw [hr, Matrix.one_mul]⟩
  have hC : (1 - A * A⁻¹) * C * (1 - B * H) = 0 := by simp [hl]
  rw [exercise_11_formula C hG hH hC, upperBlockGroupInverseEntry, hl]
  simp

end UpperBlockGroupInverse

end BenIsraelGreville.Chapter05
