/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.SingularValues
import NumlibSurface.BenIsraelGreville.Chapter00.Section02

/-!
# Singular values and unitary equivalence

Section 6.1 of [benIsrael2003generalized] introduces the singular value
decomposition and relates its diagonal to the Hermitian dilation, matrix
norms, and sensitivity of linear systems.

## Deviations from the source

* **Equation (3)** (reading). The diagonal representation of a map from
  $\mathbb C^n$ to $\mathbb C^m$ has $m$ rows and $n$ columns.
-/

namespace BenIsraelGreville.Chapter06

open Matrix

/-- **Equation (4)** of [benIsrael2003generalized], Chapter 6. A singular value
decomposition has two unitary factors and a descending nonnegative rectangular
diagonal. The singular value sequence is padded by zeros at and beyond the rank. -/
def IsSingularValueDecomposition {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (σ : ℕ → ℝ) (V : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  A.IsSVD U σ V ∧ ∀ i, A.rank ≤ i → σ i = 0

/-- The padding convention makes the entire diagonal sequence unique. -/
theorem IsSingularValueDecomposition.eq_sortedSingularValues {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℂ} {U : Matrix (Fin m) (Fin m) ℂ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℂ} (h : IsSingularValueDecomposition A U σ V) :
    σ = A.sortedSingularValues := by
  funext i
  by_cases hm : i < m
  · by_cases hn : i < n
    · exact h.1.singularValues_eq hm hn
    · have hr := A.rank_le_width.trans (Nat.le_of_not_gt hn)
      rw [h.2 i hr, (A.sortedSingularValues_eq_zero_iff_rank_le i).mpr hr]
  · have hr := A.rank_le_height.trans (Nat.le_of_not_gt hm)
    rw [h.2 i hr, (A.sortedSingularValues_eq_zero_iff_rank_le i).mpr hr]

/-- **Equation (3)** of [benIsrael2003generalized], Chapter 6. The matrix
takes the $j$th right singular vector to the corresponding left singular
vector scaled by the singular value, or to zero if the output index is absent. -/
theorem IsSingularValueDecomposition.mulVec_col {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℂ} {U : Matrix (Fin m) (Fin m) ℂ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℂ} (h : IsSingularValueDecomposition A U σ V) (j : Fin n) :
    A *ᵥ V.col j = if hj : (j : ℕ) < m then (σ j : ℂ) • U.col ⟨j, hj⟩ else 0 := by
  let D : Matrix (Fin m) (Fin n) ℂ := rectDiagonal (fun i => (σ i : ℂ))
  have hV : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp h.1.mem_unitaryGroup_right
  have hAV : A * V = U * D := by
    calc
      A * V = (U * D * Vᴴ) * V := by
        exact congrArg (fun B : Matrix (Fin m) (Fin n) ℂ => B * V) h.1.eq_mul_mul_star
      _ = U * D := by rw [Matrix.mul_assoc, hV, Matrix.mul_one]
  change (A * V).col j = _
  rw [hAV]
  funext i
  rw [col_apply, mul_rectDiagonal_apply]
  split_ifs <;> simp [col_apply, mul_comm]

section Exercises

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Exercise 1** of [benIsrael2003generalized], Chapter 6. Adjointing a
matrix preserves the ordered singular values. -/
theorem exercise_1 [DecidableEq m] (A : Matrix m n ℂ) :
    Aᴴ.sortedSingularValues = A.sortedSingularValues :=
  Matrix.sortedSingularValues_conjTranspose A

/-- **Exercise 2** of [benIsrael2003generalized], Chapter 6. Unitary
changes on either side preserve the ordered singular values. -/
theorem exercise_2 [DecidableEq m] (A : Matrix m n ℂ)
    {U : Matrix m m ℂ} {V : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup m ℂ) (hV : V ∈ unitaryGroup n ℂ) :
    (U * A * V).sortedSingularValues = A.sortedSingularValues :=
  A.sortedSingularValues_unitary_mul_mul hU hV

/-- **Exercise 3** of [benIsrael2003generalized], Chapter 6. The descending
eigenvalues of the block matrix $[0,A;A^H,0]$ are the singular values, zeros
between the positive and negative parts, and the negatives in reverse order. -/
theorem exercise_3 [DecidableEq m] (A : Matrix m n ℂ)
    (i : Fin (Fintype.card (m ⊕ n))) :
    (isHermitian_hermitianDilation Aᴴ).eigenvalues₀ i =
      A.sortedSingularValues i - A.sortedSingularValues (Fintype.card (m ⊕ n) - 1 - i) := by
  have h (j : ℕ) := congrFun (Matrix.sortedSingularValues_conjTranspose A) j
  rw [(isHermitian_hermitianDilation Aᴴ).eigenvalues₀_hermitianDilation i, h, h]

/-- **Exercise 4** of [benIsrael2003generalized], Chapter 6, Equation (5).
The next singular value is the maximum norm of the image of a unit vector
orthogonal to the earlier right singular vectors in the sorted Gram basis. -/
theorem exercise_4 (A : Matrix m n ℂ) (i : Fin (Fintype.card n)) :
    let h := isSymmetric_toEuclideanLin_iff.mpr (isHermitian_conjTranspose_mul_self A)
    let hn : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n := finrank_euclideanSpace
    IsGreatest {c : ℝ | ∃ x : EuclideanSpace ℂ n, ‖x‖ = 1 ∧
      (∀ j < i, inner ℂ (h.eigenvectorBasis hn j) x = 0) ∧ ‖toEuclideanLin A x‖ = c}
      (A.sortedSingularValues i) := by
  classical
  intro h hn
  let T := toEuclideanLin A
  have hGram : T.adjoint ∘ₗ T = toEuclideanLin (Aᴴ * A) := by
    rw [toEuclideanLin_mul, toEuclideanLin_conjTranspose_eq_adjoint]
  have hEigen : T.isSymmetric_adjoint_comp_self.eigenvalues hn = h.eigenvalues hn := by
    rw [LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff, hGram]
  have hσ : A.sortedSingularValues i ^ 2 = h.eigenvalues hn i := by
    change T.singularValues i ^ 2 = _
    rw [T.sq_singularValues_fin hn i, hEigen]
  have hObj (x : EuclideanSpace ℂ n) :
      RCLike.re (inner ℂ (toEuclideanLin (Aᴴ * A) x) x) = ‖T x‖ ^ 2 := by
    rw [← hGram, LinearMap.comp_apply, LinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
    change Complex.re ((‖T x‖ : ℂ) ^ 2) = ‖T x‖ ^ 2
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hMax := Chapter00.hermitian_rayleigh_recursion (isHermitian_conjTranspose_mul_self A) i
  constructor
  · obtain ⟨x, hx, horth, he⟩ := hMax.1
    refine ⟨x, hx, horth, ?_⟩
    rw [hObj] at he
    exact (pow_left_inj₀ (norm_nonneg _) (A.sortedSingularValues_nonneg i) two_ne_zero).mp
      (he.trans hσ.symm)
  · rintro _ ⟨x, hx, horth, rfl⟩
    have hb := hMax.2 ⟨x, hx, horth, rfl⟩
    change RCLike.re (inner ℂ (toEuclideanLin (Aᴴ * A) x) x) ≤ h.eigenvalues hn i at hb
    rw [hObj, ← hσ] at hb
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (A.sortedSingularValues_nonneg i) two_ne_zero).mp
      hb

/-- **Exercise 4, dual statement** of [benIsrael2003generalized], Chapter 6.
The same extremum for the adjoint uses the earlier left singular vectors. -/
theorem exercise_4_adjoint [DecidableEq m] (A : Matrix m n ℂ)
    (i : Fin (Fintype.card m)) :
    let h := isSymmetric_toEuclideanLin_iff.mpr (isHermitian_mul_conjTranspose_self A)
    let hn : Module.finrank ℂ (EuclideanSpace ℂ m) = Fintype.card m := finrank_euclideanSpace
    IsGreatest {c : ℝ | ∃ x : EuclideanSpace ℂ m, ‖x‖ = 1 ∧
      (∀ j < i, inner ℂ (h.eigenvectorBasis hn j) x = 0) ∧ ‖toEuclideanLin Aᴴ x‖ = c}
      (A.sortedSingularValues i) := by
  have hσ := congrFun (Matrix.sortedSingularValues_conjTranspose A) i.val
  simpa only [conjTranspose_conjTranspose, hσ] using exercise_4 Aᴴ i

open scoped Matrix.Norms.Frobenius in
/-- **Exercise 8** of [benIsrael2003generalized], Chapter 6, Equation (8).
The squared Frobenius norm is the sum of squares of the positive singular values. -/
theorem exercise_8 (A : Matrix m n ℂ) :
    ‖A‖ ^ 2 = ∑ i ∈ Finset.range A.rank, A.sortedSingularValues i ^ 2 := by
  rw [A.frobenius_norm_sq_eq_sum_sq_sortedSingularValues, ← Finset.sum_range_add_sum_Ico _
    A.rank_le_card_width]
  have hz : ∑ i ∈ Finset.Ico A.rank (Fintype.card n), A.sortedSingularValues i ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [(A.sortedSingularValues_eq_zero_iff_rank_le i).mpr (Finset.mem_Ico.mp hi).1]
  rw [hz, add_zero]

/-- **Exercise 10** of [benIsrael2003generalized], Chapter 6, Equation (11).
The condition number in the matrix norm $N$ is the product of the norms
of the matrix and its ordinary inverse. -/
noncomputable def conditionNumber (N : Matrix n n ℂ → ℝ) (A : Matrix n n ℂ) : ℝ :=
  N A * N A⁻¹

/-- **Exercise 10** of [benIsrael2003generalized], Chapter 6, Equations
(12)–(15). With compatible matrix and vector norms, the condition number
bounds the relative amplification of a change in the right-hand side. -/
theorem exercise_10 (N : Matrix n n ℂ → ℝ) (ν : (n → ℂ) → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hCompat : ∀ B x, ν (B *ᵥ x) ≤ N B * ν x)
    {A : Matrix n n ℂ} (hA : IsUnit A) {x b δx δb : n → ℂ}
    (hx : A *ᵥ x = b) (hδ : A *ᵥ δx = δb) (hxb : 0 < ν x) (hbb : 0 < ν b) :
    ν δx / ν x ≤ conditionNumber N A * (ν δb / ν b) := by
  have hδx : A⁻¹ *ᵥ δb = δx := by
    rw [← hδ, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA), one_mulVec]
  have hDb : ν δx ≤ N A⁻¹ * ν δb := hδx ▸ hCompat A⁻¹ δb
  have hAx : ν b ≤ N A * ν x := hx ▸ hCompat A x
  rw [← mul_div_assoc, div_le_div_iff₀ hxb hbb]
  calc
    ν δx * ν b ≤ (N A⁻¹ * ν δb) * (N A * ν x) :=
      mul_le_mul hDb hAx (hν b) ((hν δx).trans hDb)
    _ = (conditionNumber N A * ν δb) * ν x := by
      unfold conditionNumber
      ring

open scoped Matrix.Norms.L2Operator in
/-- **Equation (16)** of [benIsrael2003generalized], Chapter 6. For a
nonsingular matrix the spectral condition number is the ratio of its
largest to its smallest singular value. -/
theorem spectralConditionNumber_eq_ratio [Nonempty n] (A : Matrix n n ℂ) (hA : IsUnit A) :
    conditionNumber norm A =
      A.sortedSingularValues 0 / A.sortedSingularValues (Fintype.card n - 1) := by
  rw [conditionNumber, ← A.sortedSingularValues_zero_eq_l2_opNorm,
    A.l2_opNorm_inv_eq_inv_iInf_colSingularValues ((isUnit_iff_isUnit_det A).mp hA),
    ← A.sortedSingularValues_eq_iInf_colSingularValues, div_eq_mul_inv]

open scoped Matrix.Norms.L2Operator ComplexOrder in
/-- **Exercise 11** of [benIsrael2003generalized], Chapter 6. Forming the
normal equations squares the spectral condition number of a nonsingular matrix. -/
theorem exercise_11 [Nonempty n] (A : Matrix n n ℂ) (hA : IsUnit A) :
    conditionNumber norm (Aᴴ * A) = conditionNumber norm A ^ 2 := by
  have hLI : LinearIndependent ℂ Aᵀ := linearIndependent_cols_of_isUnit hA
  have hG : IsUnit (Aᴴ * A) := ((isUnit_conjTranspose A).mpr hA).mul hA
  simpa only [pinvCondNumberLp, lpOpNorm_two, Matrix.pinv_eq_inv hA, Matrix.pinv_eq_inv hG,
    conditionNumber] using Matrix.pinvCondNumberLp_two_conjTranspose_mul_self hLI

end Exercises

end BenIsraelGreville.Chapter06
