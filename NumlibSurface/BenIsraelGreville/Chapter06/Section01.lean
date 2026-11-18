/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.SingularValues
import Numlib.Eigen.Normal
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Matrix.Permutation
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

private theorem permMatrix_mem_unitaryGroup {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (θ : Equiv.Perm (Fin n)) : θ.permMatrix 𝕜 ∈ unitaryGroup (Fin n) 𝕜 := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_permMatrix, ← permMatrix_mul, mul_inv_cancel,
    permMatrix_one]

/-- **Exercise 6** of [benIsrael2003generalized], Chapter 6.
A normal matrix has a unitary diagonalization whose eigenvalues, padded
by zero, have moduli equal to its sorted singular values. -/
theorem exercise_6 {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A) :
    ∃ U ∈ unitaryGroup (Fin n) ℂ, ∃ d : ℕ → ℂ,
      A = U * diagonal (fun i : Fin n => d i) * Uᴴ ∧
      ∀ i, ‖d i‖ = A.sortedSingularValues i := by
  obtain ⟨U, hU, a, _, hdiag, _⟩ :=
    hA.exists_unitary_conj_diagonal_of_commute hA (Commute.refl A)
  let θ := Tuple.sortDesc (fun i => ‖a i‖)
  let P := θ⁻¹.permMatrix ℂ
  let V := U * P
  let d : ℕ → ℂ := fun i => if hi : i < n then a (θ ⟨i, hi⟩) else 0
  have hV : V ∈ unitaryGroup (Fin n) ℂ := mul_mem hU (permMatrix_mem_unitaryGroup θ⁻¹)
  have hperm : Pᴴ * diagonal a * P = diagonal (fun i : Fin n => d i) := by
    rw [show Pᴴ = θ.permMatrix ℂ by simp [P]]
    change (_ * diagonal a) * (θ⁻¹ : Equiv.Perm (Fin n)).toPEquiv.toMatrix = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    change diagonal a (θ i) (θ j) = diagonal (fun i : Fin n => d i) i j
    by_cases hij : i = j
    · subst j
      simp [d]
    · simp [hij, show θ i ≠ θ j from fun he => hij (θ.injective he)]
  have hVdiag : Vᴴ * A * V = diagonal (fun i : Fin n => d i) := by
    calc
      Vᴴ * A * V = Pᴴ * (Uᴴ * A * U) * P := by
        simp only [V, conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [show Uᴴ * A * U = diagonal a from hdiag, hperm]
  let φ : Fin n → ℂ := fun i => if d i = 0 then 1 else d i / (‖d i‖ : ℂ)
  have hφ (i : Fin n) : ‖φ i‖ = 1 := by
    by_cases hi : d i = 0
    · simp [φ, hi]
    · have hp := norm_pos_iff.mpr hi
      simp [φ, hi, hp.ne']
  have hφU : diagonal φ ∈ unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    change starRingEnd ℂ (φ i) * φ i = 1
    rw [mul_comm, Complex.mul_conj, ← Complex.sq_norm, hφ, one_pow, Complex.ofReal_one]
  let W := V * (diagonal φ)ᴴ
  have hW : W ∈ unitaryGroup (Fin n) ℂ :=
    mul_mem hV (Unitary.star_mem hφU)
  have hdφ (i : Fin n) : d i * star (φ i) = (‖d i‖ : ℂ) := by
    by_cases hi : d i = 0
    · simp [hi]
    · have hp : (‖d i‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr hi).ne'
      change d i * starRingEnd ℂ (φ i) = _
      rw [show φ i = d i / (‖d i‖ : ℂ) by simp [φ, hi], map_div₀, Complex.conj_ofReal]
      rw [← mul_div_assoc, Complex.mul_conj, ← Complex.sq_norm, Complex.ofReal_pow, sq, mul_div_cancel_right₀ _ hp]
  have hσ : Antitone (fun i => ‖d i‖) := by
    intro i j hij
    by_cases hj : j < n
    · have hi := hij.trans_lt hj
      simpa [d, hi, hj] using
        (Tuple.antitone_sortDesc (fun i => ‖a i‖)
          (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from hij))
    · simp [d, hj]
  have hS : A.IsSVD V (fun i => ‖d i‖) W := by
    refine ⟨⟨hV, hW, ?_⟩, hσ, fun i => norm_nonneg _⟩
    change Vᴴ * A * (V * (diagonal φ)ᴴ) = _
    rw [← Matrix.mul_assoc, hVdiag, diagonal_conjTranspose, diagonal_mul_diagonal,
      rectDiagonal_eq_diagonal]
    exact congrArg diagonal (funext hdφ)
  refine ⟨V, hV, d, eq_mul_mul_star_of_star_mul_mul_eq hV hV hVdiag, fun i => ?_⟩
  by_cases hi : i < n
  · exact hS.singularValues_eq hi hi
  · have hr := A.rank_le_width.trans (Nat.le_of_not_gt hi)
    rw [(A.sortedSingularValues_eq_zero_iff_rank_le i).mpr hr]
    simp [d, hi]

private def reversePrefix {n : ℕ} (r : ℕ) (hr : r ≤ n) (i : Fin n) : Fin n :=
  if hi : (i : ℕ) < r then ⟨r - 1 - i, by omega⟩ else i

private theorem reversePrefix_involutive {n : ℕ} (r : ℕ) (hr : r ≤ n) :
    Function.Involutive (reversePrefix r hr) := by
  intro i
  by_cases hi : (i : ℕ) < r
  · have hj : r - 1 - (i : ℕ) < r := by omega
    simp only [reversePrefix, dite_eq_left hi, dite_eq_left hj]
    apply Fin.ext
    dsimp
    omega
  · simp [reversePrefix, hi]

/-- **Exercise 7**, Equation (7), of [benIsrael2003generalized], Chapter 6.
The positive singular values of the Moore–Penrose inverse are the reciprocals
in reverse order. The statement also gives the zero-padded tail. -/
theorem exercise_7 {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜) (i : ℕ) :
    A.pinv.sortedSingularValues i =
      if i < A.rank then (A.sortedSingularValues (A.rank - 1 - i))⁻¹ else 0 := by
  obtain ⟨U, hU, V, hV, hA⟩ := A.exists_svd
  let r := A.rank
  let σ := A.sortedSingularValues
  let τ : ℕ → ℝ := fun j => if j < r then (σ (r - 1 - j))⁻¹ else 0
  let D : Matrix (Fin n) (Fin m) 𝕜 := rectDiagonal fun j => ((σ j : 𝕜))⁻¹
  let ψ : Equiv.Perm (Fin n) :=
    (reversePrefix_involutive r A.rank_le_width).toPerm (reversePrefix r A.rank_le_width)
  let θ : Equiv.Perm (Fin m) :=
    (reversePrefix_involutive r A.rank_le_height).toPerm (reversePrefix r A.rank_le_height)
  let P := ψ.permMatrix 𝕜
  let Q := θ⁻¹.permMatrix 𝕜
  have hψ (j : Fin n) : (ψ j : ℕ) = if j.val < r then r - 1 - j.val else j.val := by
    by_cases hj : (j : ℕ) < r <;> simp [ψ, reversePrefix, hj]
  have hθ (j : Fin m) : (θ j : ℕ) = if j.val < r then r - 1 - j.val else j.val := by
    by_cases hj : (j : ℕ) < r <;> simp [θ, reversePrefix, hj]
  have hD : P * D * Q = (rectDiagonal fun j => (τ j : 𝕜) : Matrix (Fin n) (Fin m) 𝕜) := by
    change ψ.toPEquiv.toMatrix * D * θ⁻¹.toPEquiv.toMatrix = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext j k
    change D (ψ j) (θ k) = _
    simp only [D, rectDiagonal_apply, hψ, hθ]
    by_cases hj : (j : ℕ) < r <;> by_cases hk : (k : ℕ) < r
    · by_cases he : j.val = k.val
      · simp [τ, hk, he]
      · have hne : r - 1 - j.val ≠ r - 1 - k.val := by omega
        simp [hj, hk, he, hne]
    · have hne : r - 1 - j.val ≠ k.val := by omega
      have he : j.val ≠ k.val := by omega
      simp [hj, hk, he, hne]
    · have hne : j.val ≠ r - 1 - k.val := by omega
      have he : j.val ≠ k.val := by omega
      simp [hj, hk, he, hne]
    · have hz : σ j = 0 :=
        (A.sortedSingularValues_eq_zero_iff_rank_le j).mpr (Nat.le_of_not_gt hj)
      simp [τ, hj, hk, hz]
  have hτ_nonneg (j : ℕ) : 0 ≤ τ j := by
    by_cases hj : j < r
    · rw [show τ j = (σ (r - 1 - j))⁻¹ by simp [τ, hj]]
      exact inv_nonneg.mpr (A.sortedSingularValues_nonneg _)
    · simp [τ, hj]
  have hτ_anti : Antitone τ := by
    intro j k hjk
    by_cases hk : k < r
    · have hj := hjk.trans_lt hk
      simp only [τ, ite_eq_left hj, ite_eq_left hk]
      apply inv_anti₀
      · exact lt_of_le_of_ne (A.sortedSingularValues_nonneg _) (Ne.symm fun hz =>
          (not_le_of_gt (show r - 1 - j < r by omega))
            ((A.sortedSingularValues_eq_zero_iff_rank_le _).mp hz))
      · exact A.sortedSingularValues_antitone (by omega)
    · simpa [τ, hk] using hτ_nonneg j
  have hpinv : A.pinv = V * D * Uᴴ := pinv_eq_of_svd hU hV hA
  have hHP : P ∈ unitaryGroup (Fin n) 𝕜 := permMatrix_mem_unitaryGroup ψ
  have hHQ : Q ∈ unitaryGroup (Fin m) 𝕜 := permMatrix_mem_unitaryGroup θ⁻¹
  have hsing := sortedSingularValues_unitary_mul_mul (A := D) hHP hHQ
  have hDU := sortedSingularValues_unitary_mul_mul (A := D) hV (Unitary.star_mem hU)
  have hrec : A.pinv.sortedSingularValues =
      (rectDiagonal fun j => (τ j : 𝕜) : Matrix (Fin n) (Fin m) 𝕜).sortedSingularValues := by
    rw [hpinv, ← hD, hsing]
    exact hDU
  rw [hrec]
  change (rectDiagonal fun j => (τ j : 𝕜) : Matrix (Fin n) (Fin m) 𝕜).sortedSingularValues i = τ i
  by_cases hi : i < min n m
  · have hS : (rectDiagonal fun j => (τ j : 𝕜) : Matrix (Fin n) (Fin m) 𝕜).IsSVD 1 τ 1 :=
      ⟨⟨one_mem _, one_mem _, by simp⟩, hτ_anti, hτ_nonneg⟩
    exact (hS.singularValues_eq (hi.trans_le (min_le_left _ _))
      (hi.trans_le (min_le_right _ _))).symm
  · have hir : ¬ i < r := fun h => hi (h.trans_le
      (le_min A.rank_le_width A.rank_le_height))
    rw [sortedSingularValues_eq_zero_of_min_le _ (by simpa using Nat.le_of_not_gt hi)]
    simp [τ, hir]

open scoped Matrix.Norms.L2Operator in
/-- **Exercise 9**, Equation (9), of [benIsrael2003generalized], Chapter 6.
The product of the spectral norms of a positive-rank matrix and its
Moore–Penrose inverse is the ratio of its extreme positive singular values. -/
theorem exercise_9 {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜)
    (hA : 0 < A.rank) :
    ‖A‖ * ‖A.pinv‖ = A.sortedSingularValues 0 / A.sortedSingularValues (A.rank - 1) := by
  rw [← A.sortedSingularValues_zero_eq_l2_opNorm, ← A.pinv.sortedSingularValues_zero_eq_l2_opNorm,
    exercise_7, ite_eq_left hA, Nat.sub_zero, div_eq_mul_inv]

end BenIsraelGreville.Chapter06
