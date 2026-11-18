/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter00.Section05
import NumlibSurface.BenIsraelGreville.Chapter01.Section06
import NumlibSurface.BenIsraelGreville.Chapter04.Section04
import Numlib.LinearAlgebra.Matrix.SaddlePoint.NullSpaceReduction

/-!
# Partitioned matrices and linear equations

Section 5.2 of [benIsrael2003generalized] uses a nonsingular leading block to
eliminate variables in a partitioned system. When the block has the rank of
the whole matrix, the remaining Schur complement vanishes.

## Deviations from the source

* **Exercise 6** (correction). The nonsingularity test is for $I_r+TS$.
  The printed product $ST$ has the dimensions of the trailing square block.
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

variable {K r m n : Type*} [Field K] [Fintype r] [Fintype m] [Fintype n] [DecidableEq r]

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

omit [Fintype m] in
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

omit [Fintype m] in
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
theorem theorem_5_2 [DecidableEq m] [DecidableEq n] {A : Matrix r r ℂ}
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

end BenIsraelGreville.Chapter05
