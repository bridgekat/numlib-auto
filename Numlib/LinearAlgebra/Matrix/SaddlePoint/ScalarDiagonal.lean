/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.SVD

/-!
# Saddle point matrices with a scalar diagonal block

A scalar top diagonal block and a zero bottom diagonal block allow an exact
characteristic polynomial via a Schur determinant.
-/

open Polynomial

namespace Matrix

section Charpoly

variable {K n m : Type*} [Field K] [Infinite K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

/-- With scalar top block and zero bottom block, the characteristic polynomial is
`(X - η)^(n - m) χ(BD)(X(X - η))`, where `D` and `B` are the off-diagonal blocks. -/
theorem charpoly_fromBlocks_smul_one_zero (hsize : Fintype.card m ≤ Fintype.card n)
    (η : K) (D : Matrix n m K) (B : Matrix m n K) :
    (fromBlocks (η • (1 : Matrix n n K)) D B 0).charpoly =
      (X - C η) ^ (Fintype.card n - Fintype.card m) *
        (B * D).charpoly.comp (X * (X - C η)) := by
  refine eq_of_infinite_eval_eq _ _ (Set.Infinite.mono ?_ (Set.infinite_univ.sdiff
    (Set.finite_singleton η)))
  intro t ht
  have hη : t - η ≠ 0 := sub_ne_zero.mpr (by simpa using ht)
  let u := t - η
  have hu : u ≠ 0 := hη
  have hA : IsUnit (u • (1 : Matrix n n K)) := by
    rw [isUnit_iff_isUnit_det, det_smul, det_one, mul_one]
    exact (isUnit_iff_ne_zero.mpr hu).pow _
  let _ := hA.invertible
  have hinv : ⅟(u • (1 : Matrix n n K)) = u⁻¹ • (1 : Matrix n n K) :=
    invOf_eq_right_inv (by simp [hu])
  have hblock :
      Matrix.scalar (n ⊕ m) t - fromBlocks (η • (1 : Matrix n n K)) D B 0 =
        fromBlocks (u • (1 : Matrix n n K)) (-D) (-B) (t • (1 : Matrix m m K)) := by
    change algebraMap K _ t - _ = _
    rw [Algebra.algebraMap_eq_smul_one]
    ext i j
    cases i <;> cases j <;> simp [u, Matrix.one_apply]
    split_ifs <;> simp
  let E : Matrix m m K := t • 1 - (-B) * (u⁻¹ • (1 : Matrix n n K)) * (-D)
  have hE : u • E = (t * u) • 1 - B * D := by
    simp [E, smul_sub, smul_smul, Matrix.mul_smul, Matrix.smul_mul, hu, mul_comm t u]
  have hdet :
      (((t * u) • 1 - B * D) : Matrix m m K).det =
        u ^ Fintype.card m * E.det := by
    rw [← hE, det_smul]
  change (fromBlocks (η • (1 : Matrix n n K)) D B 0).charpoly.eval t = _
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_comp, eval_charpoly]
  rw [hblock, det_fromBlocks₁₁, hinv, det_smul, det_one, mul_one]
  change u ^ Fintype.card n * E.det =
    u ^ (Fintype.card n - Fintype.card m) * (algebraMap K _ (t * u) - B * D).det
  rw [Algebra.algebraMap_eq_smul_one, hdet, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hsize]

end Charpoly

private theorem charpoly_smul_mul_transpose {n m : ℕ} (hmn : m ≤ n)
    (B : Matrix (Fin m) (Fin n) ℝ) (ε : ℝ) :
    (ε • (B * Bᵀ)).charpoly = ∏ i : Fin m, (X - C (ε * B.sortedSingularValues i ^ 2)) := by
  obtain ⟨U, hU, V, hV, hsvd⟩ := B.exists_svd
  let D : Matrix (Fin m) (Fin n) ℝ := rectDiagonal B.sortedSingularValues
  have hB : B = U * D * star V := eq_mul_mul_star_of_star_mul_mul_eq hU hV hsvd
  have hV₁ := mem_unitaryGroup_iff'.1 hV
  have hU₁ := mem_unitaryGroup_iff'.1 hU
  have hgram : B * Bᵀ = U * (D * Dᵀ) * star U := by
    have hBT : Bᵀ = V * Dᵀ * star U := by
      rw [hB, transpose_mul, transpose_mul]
      simp [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc]
    conv_lhs => rw [hBT, hB]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star V) V, hV₁, Matrix.one_mul]
  have hdiag : D * Dᵀ = diagonal (fun i : Fin m => B.sortedSingularValues i ^ 2) := by
    rw [show D = rectDiagonal B.sortedSingularValues from rfl, rectDiagonal_transpose,
      rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal]
    congr 1
    funext i
    simp [lt_of_lt_of_le i.isLt hmn, pow_two]
  have hscale : ε • (U * (D * Dᵀ) * star U) = U * (ε • (D * Dᵀ)) * star U := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hgram, hscale, charpoly_mul_comm, ← Matrix.mul_assoc, hU₁, Matrix.one_mul,
    hdiag, ← diagonal_smul, charpoly_diagonal]
  rfl

private theorem prod_tail_constant {R : Type*} [CommMonoid R] {n m r : ℕ}
    (hr : r ≤ m) (hmn : m ≤ n) (x q : R) (f : ℕ → R)
    (hf : ∀ i ≥ r, f i = x * q) :
    q ^ (n - m) * (∏ i : Fin m, f i) =
      x ^ (m - r) * q ^ (n - r) * (∏ i : Fin r, f i) := by
  rw [Fin.prod_univ_eq_prod_range f m, Fin.prod_univ_eq_prod_range f r]
  have hprod := Finset.prod_range_add f r (m - r)
  rw [Nat.add_sub_of_le hr] at hprod
  rw [hprod]
  have htail : ∏ i ∈ Finset.range (m - r), f (r + i) = (x * q) ^ (m - r) := by
    calc
      _ = ∏ _i ∈ Finset.range (m - r), x * q :=
        Finset.prod_congr rfl (fun i _ ↦ hf _ (Nat.le_add_right _ _))
      _ = _ := by simp
  rw [htail, mul_pow, show n - r = n - m + (m - r) by omega, pow_add]
  ac_rfl

/-- For transpose-related off-diagonal blocks, the characteristic polynomial consists of one
quadratic for each nonzero singular value, with the remaining powers of `X` and `X - η`
recording the left and right nullities. -/
theorem charpoly_fromBlocks_smul_one_transpose_zero {n m : ℕ} (hmn : m ≤ n)
    (B : Matrix (Fin m) (Fin n) ℝ) (η ε : ℝ) :
    (fromBlocks (η • (1 : Matrix (Fin n) (Fin n) ℝ)) Bᵀ (ε • B) 0).charpoly =
      X ^ (m - B.rank) * (X - C η) ^ (n - B.rank) *
        ∏ i : Fin B.rank, (X * (X - C η) - C (ε * B.sortedSingularValues i ^ 2)) := by
  have hr : B.rank ≤ m := by simpa using B.rank_le_card_height
  have hmn' : Fintype.card (Fin m) ≤ Fintype.card (Fin n) := by simpa using hmn
  rw [charpoly_fromBlocks_smul_one_zero hmn', Fintype.card_fin,
    Fintype.card_fin, Matrix.smul_mul, charpoly_smul_mul_transpose hmn, prod_comp]
  simp only [sub_comp, X_comp, C_comp]
  let f : ℕ → ℝ[X] := fun i => X * (X - C η) - C (ε * B.sortedSingularValues i ^ 2)
  change (X - C η) ^ (n - m) * (∏ i : Fin m, f i) =
    X ^ (m - B.rank) * (X - C η) ^ (n - B.rank) * ∏ i : Fin B.rank, f i
  refine prod_tail_constant hr hmn X (X - C η) f fun i hi ↦ ?_
  simp only [f, (B.sortedSingularValues_eq_zero_iff_rank_le i).2 hi, zero_pow (by decide : 2 ≠ 0),
    mul_zero, C_0, sub_zero]

private theorem quadratic_factor {η d δ : ℂ} (hδ : δ ^ 2 = η ^ 2 + 4 * d) :
    X * (X - C η) - C d =
      (X - C ((η + δ) / 2)) * (X - C ((η - δ) / 2)) := by
  apply Polynomial.funext
  intro z
  simp
  linear_combination hδ / 4

/-- The roots of the scalar-block saddle point matrix, counted with algebraic multiplicity.
A choice of square root of each discriminant gives the two roots of its quadratic factor. -/
theorem roots_charpoly_complexify_fromBlocks_smul_one_transpose_zero
    {n m : ℕ} (hmn : m ≤ n) (B : Matrix (Fin m) (Fin n) ℝ) (η ε : ℝ)
    (δ : Fin B.rank → ℂ)
    (hδ : ∀ i, δ i ^ 2 = (η : ℂ) ^ 2 + 4 * (ε : ℂ) * (B.sortedSingularValues i : ℂ) ^ 2) :
    (complexify (fromBlocks (η • (1 : Matrix (Fin n) (Fin n) ℝ)) Bᵀ (ε • B) 0)).charpoly.roots =
      (m - B.rank) • ({0} : Multiset ℂ) + (n - B.rank) • ({(η : ℂ)} : Multiset ℂ) +
        Finset.univ.val.bind (fun i : Fin B.rank =>
          ({((η : ℂ) + δ i) / 2} : Multiset ℂ) + {((η : ℂ) - δ i) / 2}) := by
  rw [charpoly_complexify, charpoly_fromBlocks_smul_one_transpose_zero hmn]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub,
    Polynomial.map_C, Polynomial.map_prod, Complex.coe_algebraMap, Complex.ofReal_mul,
    Complex.ofReal_pow]
  let f : Fin B.rank → ℂ[X] := fun i =>
    (X - C (((η : ℂ) + δ i) / 2)) * (X - C (((η : ℂ) - δ i) / 2))
  have hfactor :
      (∏ i : Fin B.rank, (X * (X - C (η : ℂ)) -
        C ((ε : ℂ) * (B.sortedSingularValues i : ℂ) ^ 2))) = ∏ i : Fin B.rank, f i := by
    apply Finset.prod_congr rfl
    intro i _
    exact quadratic_factor (by simpa [mul_assoc] using hδ i)
  rw [hfactor]
  have hf (i : Fin B.rank) : f i ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  have hp : ∏ i : Fin B.rank, f i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hf i
  have hbase : X ^ (m - B.rank) * (X - C (η : ℂ)) ^ (n - B.rank) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ (X_sub_C_ne_zero _))
  rw [roots_mul (mul_ne_zero hbase hp), roots_mul hbase, roots_X_pow, roots_pow,
    roots_X_sub_C, roots_prod _ _ hp]
  congr 2
  funext i
  dsimp [f]
  rw [roots_mul (hf i), roots_X_sub_C, roots_X_sub_C]
  rfl

end Matrix
