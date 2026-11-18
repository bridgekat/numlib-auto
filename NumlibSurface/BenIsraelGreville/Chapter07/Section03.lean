/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Direct.Substitution
import Numlib.LinearAlgebra.Matrix.QR
import NumlibSurface.BenIsraelGreville.Chapter00.Section03
import NumlibSurface.BenIsraelGreville.Chapter01.Section06

/-!
# Computation of inner inverses with Hermitian image projection

Section 7.3 of [benIsrael2003generalized] constructs $\{1,2,3\}$-inverses
using rank factorizations, thin QR factorizations, and basic columns.
-/

namespace BenIsraelGreville.Chapter07

open Matrix
open scoped ComplexOrder
open BenIsraelGreville.Chapter01 (definition_1 mem_one_iff)

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

private theorem mem_one_two_three_iff {A : Matrix m n ℂ} {X : Matrix n m ℂ} :
    X ∈ definition_1 A {.inner, .outer, .hermitianMul} ↔
      A.IsInnerInverse X ∧ A.IsOuterInverse X ∧ (A * X).IsHermitian := by
  change (∀ c ∈ ({.inner, .outer, .hermitianMul} : Set PenroseCondition), c.Holds A X) ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  rfl

/-- **Equations (9)–(10)** of [benIsrael2003generalized], Chapter 7. If $A=FG$
is a full-rank factorization, any inner inverse $Y$ of $G$ gives the
$\{1,2,3\}$-inverse $YF^\dagger$ of $A$. -/
theorem isPenrose123_of_fullRankFactorization [DecidableEq k]
    {A : Matrix m n ℂ} {F : Matrix m k ℂ} {G : Matrix k n ℂ} {Y : Matrix n k ℂ}
    (hA : A = F * G) (hF : F.rank = Fintype.card k) (hG : G.rank = Fintype.card k)
    (hY : G.IsInnerInverse Y) :
    Y * F.pinv ∈ definition_1 A {.inner, .outer, .hermitianMul} := by
  have hL := (Chapter01.lemma_2_a (mem_one_iff.mpr F.mul_pinv_mul_self)).mpr hF
  have hR := (Chapter01.lemma_2_b (mem_one_iff.mpr hY)).mpr hG
  have hp : A * (Y * F.pinv) = F * F.pinv := by
    calc
      _ = F * (G * Y) * F.pinv := by rw [hA]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hR, Matrix.mul_one]
  refine mem_one_two_three_iff.mpr ⟨?_, ?_, hp ▸ F.isHermitian_mul_pinv⟩
  · rw [isInnerInverse_iff, hp, hA, ← Matrix.mul_assoc, F.mul_pinv_mul_self]
  · rw [isOuterInverse_iff]
    calc
      (Y * F.pinv) * A * (Y * F.pinv) = Y * (F.pinv * F) * (G * Y) * F.pinv := by
        rw [hA]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hL, hR, Matrix.mul_one, Matrix.mul_one]

/-- **Equations (11)–(12)** of [benIsrael2003generalized], Chapter 7. In a thin
QR rank factorization the pseudoinverse of $Q$ is its adjoint, and
$YQ^H$ is a $\{1,2,3\}$-inverse for any inner inverse $Y$ of $R$. -/
theorem isPenrose123_of_thinQR [DecidableEq k]
    {A : Matrix m n ℂ} {Q : Matrix m k ℂ} {R : Matrix k n ℂ} {Y : Matrix n k ℂ}
    (hA : A = Q * R) (hQ : Qᴴ * Q = 1) (hR : R.rank = Fintype.card k)
    (hY : R.IsInnerInverse Y) :
    Q.pinv = Qᴴ ∧ Y * Qᴴ ∈ definition_1 A {.inner, .outer, .hermitianMul} := by
  have hQp : Q.pinv = Qᴴ := by
    symm
    refine Q.pinv_unique ?_ ?_ (isHermitian_mul_conjTranspose_self Q) ?_
    · rw [Matrix.mul_assoc, hQ, Matrix.mul_one]
    · rw [hQ, Matrix.one_mul]
    · rw [hQ]
      exact isHermitian_one
  have hrank : Q.rank = Fintype.card k := by
    rw [← rank_conjTranspose_mul_self Q, hQ, rank_one]
  refine ⟨hQp, ?_⟩
  rw [← hQp]
  exact isPenrose123_of_fullRankFactorization hA hrank hR hY

/-- **Section 7.3** of [benIsrael2003generalized]. Applying thin QR to the
pivot columns of a rank factorization produces a nonsingular triangular
leading block of the right factor after the pivot permutation. -/
theorem exists_thinQR_with_pivot {r : ℕ}
    {A : Matrix m (Fin r ⊕ n) ℂ} {F : Matrix m (Fin r) ℂ}
    {G : Matrix (Fin r) (Fin r ⊕ n) ℂ} {P : Matrix (Fin r ⊕ n) (Fin r ⊕ n) ℂ}
    {K : Matrix (Fin r) n ℂ}
    (hA : A = F * G) (hF : LinearIndependent ℂ Fᵀ) (hP : G * P = fromCols 1 K) :
    ∃ (Q : Matrix m (Fin r) ℂ) (R : Matrix (Fin r) (Fin r ⊕ n) ℂ)
      (T : Matrix (Fin r) (Fin r) ℂ),
      A = Q * R ∧ Qᴴ * Q = 1 ∧ R * P = fromCols T (T * K) ∧
        IsUnit T ∧ T.IsUpperTriangular := by
  obtain ⟨Q, T, hQT, -⟩ := F.exists_isThinQR hF
  refine ⟨Q, T * G, T, ?_, hQT.conjTranspose_mul_self, ?_,
    hQT.isUnit_of_linearIndependent hF, hQT.isUpperTriangular⟩
  · rw [hA, ← hQT.mul_eq, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, hP, mul_fromCols, Matrix.mul_one]

/-- **Equation (13)** of [benIsrael2003generalized], Chapter 7. Inverting the
nonsingular triangular pivot gives a right inverse of the thin right factor.
The inverse pivot is triangular as well. -/
theorem isRightInverse_of_pivot_triangle [DecidableEq k] [LinearOrder k]
    {R : Matrix k (k ⊕ n) ℂ} {T : Matrix k k ℂ} {K : Matrix k n ℂ}
    {P : Matrix (k ⊕ n) (k ⊕ n) ℂ}
    (hR : R * P = fromCols T K) (hT : IsUnit T) (htri : T.IsUpperTriangular) :
    R * (P * fromRows T⁻¹ (0 : Matrix n k ℂ)) = 1 ∧ T⁻¹.IsUpperTriangular := by
  refine ⟨?_, htri.inv⟩
  rw [← Matrix.mul_assoc, hR, fromCols_mul_fromRows,
    T.mul_nonsing_inv ((isUnit_iff_isUnit_det T).mp hT), Matrix.mul_zero, add_zero]

/-- **Equation (13)** of [benIsrael2003generalized], Chapter 7. Back
substitution against the coordinate vectors computes the columns of the
inverse triangular pivot. -/
theorem pivot_inverse_col_eq_backSubst [LinearOrder k]
    {T : Matrix k k ℂ} (hT : IsUnit T) (htri : T.IsUpperTriangular) (j : k) :
    T⁻¹.col j = backSubst T (Pi.single j 1) :=
  inv_col_eq_backSubst htri (htri.isUnit_iff.mp hT) j

/-- **Exercise 4**, Equations (14)–(16) of [benIsrael2003generalized], Chapter 7.
Selecting the pivot columns in a Hermite rank factorization gives the basic
$\{1,2,3\}$-inverse. Its pivot rows reproduce the rows of $F^\dagger$ and
the other rows vanish. -/
theorem isPenrose123_of_basic_columns [DecidableEq k] [DecidableEq n]
    {A : Matrix m (k ⊕ n) ℂ} {F : Matrix m k ℂ} {G : Matrix k (k ⊕ n) ℂ}
    (hA : A = F * G) (hF : F.rank = Fintype.card k) (hG : G.rank = Fintype.card k)
    (π : Equiv.Perm (k ⊕ n)) (K : Matrix k n ℂ)
    (hP : G * π.permMatrix ℂ = fromCols 1 K) :
    let P₁ := (π.permMatrix ℂ).submatrix id Sum.inl
    let X := P₁ * ((Fᴴ * F)⁻¹ * Fᴴ)
    F = A * P₁ ∧ X ∈ definition_1 A {.inner, .outer, .hermitianMul} ∧
      ∀ i, X.row i = Sum.elim F.pinv.row (fun _ => 0) (π i) := by
  intro P₁ X
  have hEmb :
      (1 : Matrix (k ⊕ n) (k ⊕ n) ℂ).submatrix id Sum.inl =
        fromRows (1 : Matrix k k ℂ) (0 : Matrix n k ℂ) := by
    ext i j
    cases i <;> simp [Matrix.one_apply]
  have hE : P₁ = π.permMatrix ℂ * fromRows (1 : Matrix k k ℂ) 0 := by
    change (π.permMatrix ℂ).submatrix id Sum.inl = _
    rw [← hEmb]
    exact
      (mul_submatrix_one (Equiv.refl (k ⊕ n)) Sum.inl (π.permMatrix ℂ)).symm
  have hRight : G * P₁ = 1 := by
    rw [hE, ← Matrix.mul_assoc, hP, fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero,
      add_zero]
  have hGram : IsUnit (Fᴴ * F) := mulVec_surjective_iff_isUnit.mp
    (mulVec_surjective_iff_rank_eq_card.mpr (F.rank_conjTranspose_mul_self.trans hF))
  have hX : X = P₁ * F.pinv := by
    dsimp [X]
    rw [pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit hGram]
  refine ⟨?_, ?_, ?_⟩
  · rw [hA, Matrix.mul_assoc, hRight, Matrix.mul_one]
  · rw [hX]
    exact isPenrose123_of_fullRankFactorization hA hF hG
      (isInnerInverse_iff.mpr (by rw [hRight, Matrix.one_mul]))
  · intro i
    have hm : X = (fromRows F.pinv (0 : Matrix n m ℂ)).submatrix π id := by
      rw [hX, hE, Matrix.mul_assoc, fromRows_mul, Matrix.one_mul, Matrix.zero_mul]
      exact (Chapter00.permutationMatrix_mul_eq_submatrix (K := ℂ) π
        (fromRows F.pinv (0 : Matrix n m ℂ)) (0 : Matrix m (k ⊕ n) ℂ)).1
    rw [hm]
    funext j
    change fromRows F.pinv (0 : Matrix n m ℂ) (π i) j =
      Sum.elim F.pinv.row (fun _ : n => (0 : m → ℂ)) (π i) j
    cases π i <;> rfl

/-- The matrix of **Exercise 5** of [benIsrael2003generalized], Chapter 7,
also used by the worked computations in the following sections. -/
def exercise_7_5_matrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 1; 1, 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1]

/-- **Exercise 5** of [benIsrael2003generalized], Chapter 7. For the displayed
matrix, the basic inverse with last row zero is obtained by both the Gram
formula on the first three columns and the thin QR formula with the same pivots. -/
theorem exercise_7_5 :
    let A := exercise_7_5_matrix
    let P : Matrix (Fin 4) (Fin 3) ℂ := !![1, 0, 0; 0, 1, 0; 0, 0, 1; 0, 0, 0]
    let F := A * P
    let X : Matrix (Fin 4) (Fin 4) ℂ :=
      !![3/4, 1/4, -1/4, 1/4; -1/2, 1/2, 1/2, -1/2; 1/4, -1/4, 1/4, 3/4; 0, 0, 0, 0]
    X ∈ definition_1 A {.inner, .outer, .hermitianMul} ∧
      X = P * ((Fᴴ * F)⁻¹ * Fᴴ) ∧
      ∃ (Q : Matrix (Fin 4) (Fin 3) ℂ) (R : Matrix (Fin 3) (Fin 4) ℂ)
        (T : Matrix (Fin 3) (Fin 3) ℂ),
        A = Q * R ∧ Qᴴ * Q = 1 ∧ R * P = T ∧ IsUnit T ∧
          T.IsUpperTriangular ∧ X = P * T⁻¹ * Qᴴ := by
  intro A P F X
  let F₀ : Matrix (Fin 4) (Fin 3) ℂ := !![1, 0, 0; 1, 1, 0; 0, 1, 1; 0, 0, 1]
  let G : Matrix (Fin 3) (Fin 4) ℂ := !![1, 0, 0, 1; 0, 1, 0, -1; 0, 0, 1, 1]
  let H : Matrix (Fin 3) (Fin 3) ℂ := !![3/4, -1/2, 1/4; -1/2, 1, -1/2; 1/4, -1/2, 3/4]
  let Y : Matrix (Fin 3) (Fin 4) ℂ :=
      !![3/4, 1/4, -1/4, 1/4; -1/2, 1/2, 1/2, -1/2; 1/4, -1/4, 1/4, 3/4]
  have hF₀ : F = F₀ := by
    change A * P = F₀
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, exercise_7_5_matrix, P, F₀, Matrix.mul_apply, Fin.sum_univ_succ]
  have hA : A = F * G := by
    rw [hF₀]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, exercise_7_5_matrix, F₀, G, Matrix.mul_apply, Fin.sum_univ_succ]
  have hP : G * P = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [G, P, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  have hPY : P * Y = X := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [P, Y, X, Matrix.mul_apply, Fin.sum_univ_succ]
  have hYF : Y * F = 1 := by
    rw [hF₀]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Y, F₀, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  have hGm : Fᴴ * F = !![2, 1, 0; 1, 2, 1; 0, 1, 2] := by
    rw [hF₀]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [F₀, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
  have hH : (Fᴴ * F) * H = 1 := by
    rw [hGm]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [H, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  have hHY : H * Fᴴ = Y := by
    rw [hF₀]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [H, F₀, Y, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_succ]
  have hFu : IsUnit (Fᴴ * F) :=
    (isUnit_iff_isUnit_det _).mpr (isUnit_det_of_right_inverse hH)
  have hFp : F.pinv = Y := by
    rw [pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit hFu,
      inv_eq_right_inv hH, hHY]
  have hFr : F.rank = Fintype.card (Fin 3) := by
    have hi : F.IsInnerInverse Y := isInnerInverse_iff.mpr (by
      rw [Matrix.mul_assoc, hYF, Matrix.mul_one])
    exact (Chapter01.lemma_2_a (mem_one_iff.mpr hi)).mp hYF
  have hGi : G.IsInnerInverse P := isInnerInverse_iff.mpr (by rw [hP, Matrix.one_mul])
  have hGr : G.rank = Fintype.card (Fin 3) :=
    (Chapter01.lemma_2_b (mem_one_iff.mpr hGi)).mp hP
  refine ⟨?_, ?_, ?_⟩
  · rw [← hPY, ← hFp]
    exact isPenrose123_of_fullRankFactorization hA hFr hGr hGi
  · rw [inv_eq_right_inv hH, hHY, hPY]
  · have hCols : LinearIndependent ℂ Fᵀ := by
      change LinearIndependent ℂ F.col
      apply mulVec_injective_iff.mp
      intro x y he
      have hh := congrArg (fun v => Y *ᵥ v) he
      simpa only [mulVec_mulVec, hYF, one_mulVec] using hh
    obtain ⟨Q, T, hQT, -⟩ := F.exists_isThinQR hCols
    have hT := hQT.isUnit_of_linearIndependent hCols
    have hd := (isUnit_iff_isUnit_det T).mp hT
    let R := T * G
    have hR : R * P = T := by
      change T * G * P = T
      rw [Matrix.mul_assoc, hP, Matrix.mul_one]
    have hFQ : F.pinv = T⁻¹ * Qᴴ := by
      have hQ := hQT.conjTranspose_mul_self
      have hLeft : (T⁻¹ * Qᴴ) * F = 1 := by
        rw [← hQT.mul_eq]
        calc
          _ = T⁻¹ * (Qᴴ * Q) * T := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hQ, Matrix.mul_one, T.nonsing_inv_mul hd]
      have hRight : F * (T⁻¹ * Qᴴ) = Q * Qᴴ := by
        rw [← hQT.mul_eq]
        calc
          _ = Q * (T * T⁻¹) * Qᴴ := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [T.mul_nonsing_inv hd, Matrix.mul_one]
      symm
      apply F.pinv_unique
      · rw [Matrix.mul_assoc, hLeft, Matrix.mul_one]
      · rw [hLeft, Matrix.one_mul]
      · rw [hRight]
        exact isHermitian_mul_conjTranspose_self Q
      · rw [hLeft]
        exact isHermitian_one
    refine ⟨Q, R, T, ?_, hQT.conjTranspose_mul_self, hR, hT, hQT.isUpperTriangular, ?_⟩
    · rw [hA, ← hQT.mul_eq]
      exact Matrix.mul_assoc Q T G
    · rw [Matrix.mul_assoc, ← hFQ, hFp, hPY]

end BenIsraelGreville.Chapter07
