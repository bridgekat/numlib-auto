/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter00.Section05
import NumlibSurface.BenIsraelGreville.Chapter01.Section06
import Numlib.LinearAlgebra.Matrix.GeneralizedInverse
import Numlib.LinearAlgebra.Matrix.LeastSquares
import Numlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Least-squares solutions and basic solutions

Chapter 3, §5 of [benIsrael2003generalized] expresses the Moore–Penrose
inverse as a convex combination of the zero-extended inverses of maximal
nonsingular submatrices.

Example 1 multiplies the printed residual weight by the positive scalar
ε. This scaling preserves the weighted solution operator.
-/

noncomputable section

namespace BenIsraelGreville.Chapter03

open Matrix BigOperators
open scoped ComplexOrder

section OrderedMinors

variable {m : Type*} [Fintype m] [LinearOrder m] {r : ℕ}

private theorem det_mul_eq_sum_increasing {R : Type*} [Field R] [CharZero R]
    (P : Matrix (Fin r) m R) (Q : Matrix m (Fin r) R) :
    (P * Q).det = ∑ I : Fin r ↪o m, (P.submatrix id I).det * (Q.submatrix I id).det := by
  let e := Fintype.orderIsoFinOfCardEq m (rfl : Fintype.card m = Fintype.card m)
  let f : (Fin r ↪o Fin (Fintype.card m)) ≃ (Fin r ↪o m) :=
    { toFun := fun I => I.trans e.toOrderEmbedding
      invFun := fun I => I.trans e.symm.toOrderEmbedding
      left_inv := fun I => by
        apply RelEmbedding.ext
        intro i
        exact e.symm_apply_apply (I i)
      right_inv := fun I => by
        apply RelEmbedding.ext
        intro i
        exact e.apply_symm_apply (I i) }
  have hmul : P * Q = P.submatrix id e * Q.submatrix e id := by
    simpa only [submatrix_id_id] using submatrix_mul P Q id e id e.toEquiv.bijective
  rw [hmul, Chapter00.det_mul_eq_sum_minors, ← f.sum_comp]
  rfl

variable {n : Type*} [Fintype n] [LinearOrder n]
variable {R : Type*} [Field R] [CharZero R]

/-- The double Cauchy–Binet identity, using increasing choices of rows and
columns, contracts a product of corresponding maximal minors. -/
theorem sum_cross_minors_eq_det (C : Matrix n (Fin r) R) (D : Matrix (Fin r) m R)
    (B : Matrix m n R) :
    (∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n, ((C * D).submatrix J I).det * (B.submatrix I J).det) =
      (D * B * C).det := by
  rw [det_mul_eq_sum_increasing, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  have hC (I : Fin r ↪o m) : (C * D).submatrix J I = C.submatrix J id * D.submatrix id I :=
    submatrix_mul _ _ _ id _ Function.bijective_id
  have hD : (D * B).submatrix id J = D * B.submatrix id J := by
    simpa only [submatrix_id_id] using submatrix_mul D B id id J Function.bijective_id
  simp_rw [hC, det_mul]
  rw [hD, det_mul_eq_sum_increasing, Finset.sum_mul]
  exact Finset.sum_congr rfl fun I _ => by
    rw [submatrix_submatrix, Function.id_comp, Function.comp_id]
    ring

end OrderedMinors

section Basics

variable {𝕜 m n k : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq m] [DecidableEq n] [DecidableEq k]

/-- The restriction onto the coordinates given by the row selection. -/
def minorRowSelector (I : k → m) : Matrix k m 𝕜 := (1 : Matrix m m 𝕜).submatrix I id

/-- The extension by zeros in the coordinates outside the column selection. -/
def minorColumnSelector (J : k → n) : Matrix n k 𝕜 := (1 : Matrix n n 𝕜).submatrix id J

/-- Equation (75) of [benIsrael2003generalized], Chapter 3.
The inverse of the selected minor, extended by zero to the ambient indices. -/
def basicInverse (A : Matrix m n 𝕜) (I : k → m) (J : k → n) : Matrix n m 𝕜 :=
  minorColumnSelector J * (A.submatrix I J)⁻¹ * minorRowSelector I

/-- Equations (76)–(82) of [benIsrael2003generalized], Chapter 3.
Solve the square system on the selected coordinates and extend by zero. -/
def basicSolution (A : Matrix m n 𝕜) (I : k → m) (J : k → n) (b : m → 𝕜) : n → 𝕜 :=
  basicInverse A I J *ᵥ b

omit [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k] in
@[simp]
theorem minorRowSelector_mul (A : Matrix m n 𝕜) (I : k → m) :
    minorRowSelector I * A = A.submatrix I id := by
  simpa only [minorRowSelector, Equiv.coe_refl, Equiv.refl_symm, Function.id_comp] using
    Matrix.one_submatrix_mul I (Equiv.refl m) A

omit [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k] in
@[simp]
theorem mul_minorColumnSelector (A : Matrix m n 𝕜) (J : k → n) :
    A * minorColumnSelector J = A.submatrix id J := by
  simpa only [minorColumnSelector, Equiv.coe_refl, Equiv.refl_symm, Function.id_comp] using
    Matrix.mul_submatrix_one (Equiv.refl n) J A

omit [Fintype m] [Fintype n] in
/-- On selected coordinates, a basic inverse agrees with the entries of
the inverse of the selected submatrix. -/
theorem basicInverse_apply_selected (A : Matrix m n 𝕜) (I : k ↪ m) (J : k ↪ n) (i j : k) :
    basicInverse A I J (J j) (I i) = (A.submatrix I J)⁻¹ j i := by
  simp only [basicInverse, minorColumnSelector, minorRowSelector, Matrix.mul_apply,
    submatrix_apply, id_eq, Matrix.one_apply, I.injective.eq_iff, J.injective.eq_iff]
  simp [eq_comm]

omit [Fintype m] [Fintype n] in
/-- A basic inverse has zero entries outside its selected rows and columns. -/
theorem basicInverse_apply_eq_zero (A : Matrix m n 𝕜) (I : k → m) (J : k → n)
    (i : m) (j : n) (h : i ∉ Set.range I ∨ j ∉ Set.range J) :
    basicInverse A I J j i = 0 := by
  rcases h with h | h
  · have hp (p : k) : minorRowSelector (𝕜 := 𝕜) I p i = 0 := by
      have hn : I p ≠ i := fun he => h ⟨p, he⟩
      simp [minorRowSelector, hn]
    simp [basicInverse, Matrix.mul_apply, hp]
  · have hp (p : k) : minorColumnSelector (𝕜 := 𝕜) J j p = 0 := by
      have hn : j ≠ J p := fun he => h ⟨p, he.symm⟩
      simp [minorColumnSelector, hn]
    simp [basicInverse, Matrix.mul_apply, hp]

omit [DecidableEq m] in
private theorem pinv_of_fullRank_factorization
    {r : ℕ} {A : Matrix m n 𝕜} {F : Matrix m (Fin r) 𝕜} {G : Matrix (Fin r) n 𝕜}
    (hA : A = F * G) (hF : F.rank = r) (hG : G.rank = r) :
    IsUnit (Fᴴ * A * Gᴴ) ∧ A.pinv = Gᴴ * (Fᴴ * A * Gᴴ)⁻¹ * Fᴴ := by
  have hFunit : IsUnit (Fᴴ * F) := mulVec_surjective_iff_isUnit.mp
    (mulVec_surjective_iff_rank_eq_card.mpr (by simpa using F.rank_conjTranspose_mul_self.trans hF))
  have hGunit : IsUnit (G * Gᴴ) := mulVec_surjective_iff_isUnit.mp
    (mulVec_surjective_iff_rank_eq_card.mpr (by simpa using G.rank_self_mul_conjTranspose.trans hG))
  have hFp : F.pinv = (Fᴴ * F)⁻¹ * Fᴴ :=
    Matrix.pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit hFunit
  have hGp : G.pinv = Gᴴ * (G * Gᴴ)⁻¹ := by
    have hGu : IsUnit (Gᴴᴴ * Gᴴ) := by simpa only [conjTranspose_conjTranspose] using hGunit
    have he := congrArg Matrix.conjTranspose
      (Matrix.pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit hGu)
    simpa only [Matrix.pinv_conjTranspose, conjTranspose_conjTranspose, conjTranspose_mul,
      (isHermitian_mul_conjTranspose_self G).inv.eq] using he
  have hFleft : F.pinv * F = 1 := by
    rw [hFp, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hFunit)]
  have hGright : G * G.pinv = 1 := by
    rw [hGp, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hGunit)]
  have hmid : Fᴴ * A * Gᴴ = (Fᴴ * F) * (G * Gᴴ) := by
    rw [hA]
    simp only [Matrix.mul_assoc]
  have hAX : A * (G.pinv * F.pinv) = F * F.pinv := by
    rw [hA, Matrix.mul_assoc F G _, ← Matrix.mul_assoc G G.pinv F.pinv, hGright, Matrix.one_mul]
  have hXA : (G.pinv * F.pinv) * A = G.pinv * G := by
    rw [hA, Matrix.mul_assoc G.pinv _ _, ← Matrix.mul_assoc F.pinv F G, hFleft, Matrix.one_mul]
  have hpinv : A.pinv = G.pinv * F.pinv := by
    symm
    apply A.pinv_unique
    · rw [hAX, hA, ← Matrix.mul_assoc _ F G, F.mul_pinv_mul_self]
    · rw [hXA, ← Matrix.mul_assoc, G.pinv_mul_self_mul_pinv]
    · rw [hAX]
      exact F.isHermitian_mul_pinv
    · rw [hXA]
      exact G.isHermitian_pinv_mul
  refine ⟨hmid ▸ hFunit.mul hGunit, ?_⟩
  rw [hpinv, hFp, hGp, hmid, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

end Basics

section Average

variable {𝕜 m n k : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [Fintype k]
  [LinearOrder m] [LinearOrder n] [DecidableEq k] {r : ℕ}

/-- Total squared determinant weight of the minors of order r. -/
def minorWeightSum (A : Matrix m n 𝕜) (r : ℕ) : ℝ :=
  ∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n, ‖(A.submatrix I J).det‖ ^ 2

/-- The normalized squared determinant weight of a selected minor. -/
def maximalMinorWeight (A : Matrix m n 𝕜) (I : Fin r ↪o m) (J : Fin r ↪o n) : ℝ :=
  ‖(A.submatrix I J).det‖ ^ 2 / minorWeightSum A r

/-- The determinant of the compressed update of the reciprocal is the
average of the determinants of the corresponding basic inverse updates. -/
theorem det_update_pinv_eq_average (A : Matrix m n 𝕜) (hr : A.rank = r)
    (U : Matrix m k 𝕜) (V : Matrix k n 𝕜) :
    (1 + V * A.pinv * U).det = ∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n,
      (maximalMinorWeight A I J : 𝕜) * (1 + V * basicInverse A I J * U).det := by
  obtain ⟨F, G, hA⟩ := (Matrix.rank_le_iff_exists_mul A r).mp hr.le
  have hrF : F.rank = r := by
    have hF := rank_mul_le_left F G
    rw [← hA, hr] at hF
    exact le_antisymm (by simpa using rank_le_card_width F) hF
  have hrG : G.rank = r := by
    have hG := rank_mul_le_right F G
    rw [← hA, hr] at hG
    exact le_antisymm (by simpa using rank_le_card_height G) hG
  let H := Fᴴ * A * Gᴴ
  obtain ⟨hH, hpinv⟩ := pinv_of_fullRank_factorization hA hrF hrG
  have hdH : IsUnit H.det := (isUnit_iff_isUnit_det H).mp hH
  have hdet (B : Matrix m n 𝕜) :
      (∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n,
        star ((A.submatrix I J).det) * (B.submatrix I J).det) =
        (Fᴴ * B * Gᴴ).det := by
    have hAF : Aᴴ = Gᴴ * Fᴴ := by rw [hA, conjTranspose_mul]
    rw [← sum_cross_minors_eq_det Gᴴ Fᴴ B, ← hAF]
    simp only [← conjTranspose_submatrix, det_conjTranspose]
  have hcast (z : 𝕜) : ((‖z‖ ^ 2 : ℝ) : 𝕜) = star z * z := by
    rw [RCLike.ofReal_pow, RCLike.star_def, RCLike.conj_mul]
  have hwt : ((minorWeightSum A r : ℝ) : 𝕜) = H.det := by
    simp only [minorWeightSum, map_sum, hcast]
    exact hdet A
  have hpiv (I : Fin r ↪o m) (J : Fin r ↪o n) :
      star ((A.submatrix I J).det) * ((A + U * V).submatrix I J).det =
        ((‖(A.submatrix I J).det‖ ^ 2 : ℝ) : 𝕜) * (1 + V * basicInverse A I J * U).det := by
    let M := A.submatrix I J
    have hUV : (U * V).submatrix I J = U.submatrix I id * V.submatrix id J :=
      submatrix_mul _ _ _ id _ Function.bijective_id
    rw [hcast]
    by_cases hd : M.det = 0
    · simp only [show (A.submatrix I J).det = 0 from hd, star_zero, zero_mul]
    · have hd' : IsUnit M.det := isUnit_iff_ne_zero.mpr hd
      rw [show (A + U * V).submatrix I J = M + (U * V).submatrix I J from rfl,
        hUV, det_add_mul _ _ hd', ← mul_assoc]
      have he : V.submatrix id J * M⁻¹ * U.submatrix I id = V * basicInverse A I J * U := by
        rw [← mul_minorColumnSelector, ← minorRowSelector_mul]
        simp only [basicInverse, M, Matrix.mul_assoc]
      rw [he]
  have hL : (Fᴴ * (A + U * V) * Gᴴ).det = H.det * (1 + V * A.pinv * U).det := by
    have he : Fᴴ * (A + U * V) * Gᴴ = H + (Fᴴ * U) * (V * Gᴴ) := by
      simp only [H, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [he, det_add_mul _ _ hdH, hpinv]
    simp only [H, Matrix.mul_assoc]
  apply mul_left_cancel₀ (isUnit_iff_ne_zero.mp hdH)
  rw [← hL, ← hdet, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  rw [hpiv, ← mul_assoc]
  congr 1
  rw [maximalMinorWeight, RCLike.ofReal_div, hwt, mul_comm H.det,
    div_mul_cancel₀ _ (isUnit_iff_ne_zero.mp hdH)]

private theorem topCoeff_det_one_add_X_smul (M : Matrix k k 𝕜) :
    ((1 + (Polynomial.X : Polynomial 𝕜) • M.map (Polynomial.C : 𝕜 →+* Polynomial 𝕜)).det).coeff
      (Fintype.card k) = M.det := by
  classical
  rw [coeff_det_one_add_X_smul_eq_sum_minors, ← Finset.card_univ, Finset.powersetCard_self,
    Finset.sum_singleton]
  let e : {i // i ∈ (Finset.univ : Finset k)} ≃ k :=
    ⟨Subtype.val, fun i => ⟨i, Finset.mem_univ _⟩, fun _ => rfl, fun _ => rfl⟩
  exact det_submatrix_equiv_self e M

private theorem eval_det_one_add_X_smul (M : Matrix k k 𝕜) (t : 𝕜) :
    Polynomial.eval t
        ((1 + (Polynomial.X : Polynomial 𝕜) • M.map (Polynomial.C : 𝕜 →+* Polynomial 𝕜)).det) =
      (1 + t • M).det := by
  change Polynomial.evalRingHom t _ = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  change Polynomial.eval t
    ((if i = j then 1 else 0) + Polynomial.X * Polynomial.C (M i j)) =
      (if i = j then 1 else 0) + t * M i j
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  by_cases h : i = j
  · simp only [ite_eq_left h, Polynomial.eval_one]
  · simp only [ite_eq_right h, Polynomial.eval_zero]

/-- The same convex average gives the determinant of every square
compression of the pseudoinverse. -/
theorem pinv_compression_det_eq_sum_basic (A : Matrix m n 𝕜) (hr : A.rank = r)
    (U : Matrix m k 𝕜) (V : Matrix k n 𝕜) :
    (V * A.pinv * U).det = ∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n,
      (maximalMinorWeight A I J : 𝕜) * (V * basicInverse A I J * U).det := by
  let f (M : Matrix n m 𝕜) : Polynomial 𝕜 :=
    (1 + (Polynomial.X : Polynomial 𝕜) • (V * M * U).map (Polynomial.C : 𝕜 →+* Polynomial 𝕜)).det
  have he :
      f A.pinv = ∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n,
          Polynomial.C (maximalMinorWeight A I J : 𝕜) * f (basicInverse A I J) := by
    apply Polynomial.funext
    intro t
    change Polynomial.evalRingHom t _ = Polynomial.evalRingHom t _
    simp only [map_sum, map_mul, Polynomial.coe_evalRingHom, Polynomial.eval_C, f,
      eval_det_one_add_X_smul]
    simpa only [Matrix.smul_mul] using det_update_pinv_eq_average A hr U (t • V)
  have hcoeff := congrArg (fun p : Polynomial 𝕜 => p.coeff (Fintype.card k)) he
  simpa only [f, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, topCoeff_det_one_add_X_smul]
    using hcoeff

/-- The same convex average gives every minor of the pseudoinverse. -/
theorem pinv_submatrix_det_eq_sum_basic (A : Matrix m n 𝕜) (hr : A.rank = r)
    (α : k → m) (β : k → n) :
    (A.pinv.submatrix β α).det =
      ∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n,
        (maximalMinorWeight A I J : 𝕜) * ((basicInverse A I J).submatrix β α).det := by
  have hu (M : Matrix n m 𝕜) :
      minorRowSelector β * M * minorColumnSelector α = M.submatrix β α := by
    rw [minorRowSelector_mul, mul_minorColumnSelector, submatrix_submatrix, Function.id_comp,
      Function.comp_id]
  have h := pinv_compression_det_eq_sum_basic A hr (minorColumnSelector α) (minorRowSelector β)
  rw [hu A.pinv] at h
  simp_rw [hu] at h
  exact h

/-- **Equation (75)** of [benIsrael2003generalized], Chapter 3.
The pseudoinverse is the convex sum of zero-extended basic inverses. -/
theorem pinv_eq_sum_basicInverses (A : Matrix m n 𝕜) (hr : A.rank = r) :
    A.pinv = ∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n,
      (maximalMinorWeight A I J : 𝕜) • basicInverse A I J := by
  ext j i
  simpa only [det_unique, submatrix_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
    pinv_submatrix_det_eq_sum_basic A hr (fun _ : Unit => i) (fun _ : Unit => j)

/-- For rank-sized minors, all the squared determinant weights are
nonnegative and their sum is one. -/
theorem maximalMinorWeight_convex (A : Matrix m n 𝕜) (hr : A.rank = r) :
    (∀ (I : Fin r ↪o m) (J : Fin r ↪o n), 0 ≤ maximalMinorWeight A I J) ∧
      (∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n, maximalMinorWeight A I J) = 1 := by
  have hw : 0 ≤ minorWeightSum A r :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨fun I J => div_nonneg (sq_nonneg _) hw, ?_⟩
  have he := det_update_pinv_eq_average A hr (0 : Matrix m Unit 𝕜) (0 : Matrix Unit n 𝕜)
  simp only [Matrix.zero_mul, add_zero, det_one, mul_one] at he
  apply (RCLike.ofReal_injective (K := 𝕜))
  simp only [map_sum, map_one]
  exact he.symm

/-- **Theorem 6**, Equation (89), of [benIsrael2003generalized], Chapter 3.
The minimum-norm least-squares solution is the convex average of the
zero-extended basic solutions for nonsingular maximal minors. Singular
minors have zero weight in the displayed sum. -/
theorem theorem_6 (A : Matrix m n ℝ) (hr : A.rank = r) (b : m → ℝ) :
    A.pinv *ᵥ b = ∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n,
      maximalMinorWeight A I J • basicSolution A I J b := by
  rw [pinv_eq_sum_basicInverses A hr, Matrix.sum_mulVec]
  simp only [Matrix.sum_mulVec, basicSolution, Matrix.smul_mulVec, RCLike.ofReal_real_eq_id, id_eq]

/-- For a positive rank real matrix the normalizing sum is its squared
volume from Chapter 0. -/
theorem minorWeightSum_eq_matrixVolume_sq {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (hr : A.rank = r) (hpos : 0 < r) : minorWeightSum A r = Chapter00.matrixVolume A ^ 2 := by
  rw [Chapter00.matrixVolume_eq_sqrt_sum_minors A hr hpos.ne', Real.sq_sqrt]
  · simp [minorWeightSum, Real.norm_eq_abs, sq_abs]
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Exercise 46** of [benIsrael2003generalized], Chapter 3.
Corresponding rank-sized minors of a matrix and its reciprocal are
proportional, including when the selected minors are singular. -/
theorem correspondingMaximalMinors (A : Matrix m n 𝕜) (hr : A.rank = r)
    (I : Fin r ↪o m) (J : Fin r ↪o n) :
    (A.pinv.submatrix J I).det =
      star ((A.submatrix I J).det) / (minorWeightSum A r : 𝕜) := by
  obtain ⟨F, G, hA⟩ := (Matrix.rank_le_iff_exists_mul A r).mp hr.le
  have hrF : F.rank = r := by
    have hF := rank_mul_le_left F G
    rw [← hA, hr] at hF
    exact le_antisymm (by simpa using rank_le_card_width F) hF
  have hrG : G.rank = r := by
    have hG := rank_mul_le_right F G
    rw [← hA, hr] at hG
    exact le_antisymm (by simpa using rank_le_card_height G) hG
  let H := Fᴴ * A * Gᴴ
  obtain ⟨hH, hpinv⟩ := pinv_of_fullRank_factorization hA hrF hrG
  have hAF : Aᴴ = Gᴴ * Fᴴ := by rw [hA, conjTranspose_mul]
  have hs := sum_cross_minors_eq_det Gᴴ Fᴴ A
  rw [← hAF] at hs
  simp only [← conjTranspose_submatrix, det_conjTranspose] at hs
  have hcast (z : 𝕜) : ((‖z‖ ^ 2 : ℝ) : 𝕜) = star z * z := by
    rw [RCLike.ofReal_pow, RCLike.star_def, RCLike.conj_mul]
  have hwt : ((minorWeightSum A r : ℝ) : 𝕜) = H.det := by
    simp only [minorWeightSum, map_sum, hcast]
    exact hs
  have hsub := submatrix_mul (Gᴴ * H⁻¹) Fᴴ J id I Function.bijective_id
  have hsub' := submatrix_mul Gᴴ H⁻¹ J id id Function.bijective_id
  have hA' := submatrix_mul Gᴴ Fᴴ J id I Function.bijective_id
  rw [hpinv, hwt]
  change ((Gᴴ * H⁻¹ * Fᴴ).submatrix J I).det = _ / H.det
  rw [hsub, hsub', submatrix_id_id, det_mul, det_mul, det_nonsing_inv, Ring.inverse_eq_inv',
    ← det_conjTranspose, conjTranspose_submatrix, hAF, hA', det_mul, div_eq_mul_inv]
  ring

end Average

section FullRank

private theorem ordered_selfSelection_eq_id {r : ℕ} (I : Fin r ↪o Fin r) :
    (I : Fin r → Fin r) = id := by
  have hcard : (Finset.univ : Finset (Fin r)).card = r :=
    Finset.card_univ.trans (Fintype.card_fin r)
  have hI := Finset.orderEmbOfFin_unique' hcard
    (fun i => Finset.mem_univ (I i))
  have hid := Finset.orderEmbOfFin_unique' hcard
    (fun i => Finset.mem_univ ((RelEmbedding.refl _ : Fin r ↪o Fin r) i))
  exact congrArg (fun e : Fin r ↪o Fin r => (e : Fin r → Fin r)) (hI.trans hid.symm)

/-- **Lemma 2(a)–(b)** of [benIsrael2003generalized], Chapter 3.
For full column rank the average uses the full column index set. For full
row rank it uses the full row index set. -/
theorem lemma_2 {m n r : ℕ}
    (C : Matrix (Fin m) (Fin r) ℝ) (hC : C.rank = r) (b : Fin m → ℝ)
    (R : Matrix (Fin r) (Fin n) ℝ) (hR : R.rank = r) (y : Fin r → ℝ) :
    (C.pinv *ᵥ b = ∑ I : Fin r ↪o Fin m,
      ((C.submatrix I id).det ^ 2 / minorWeightSum C r) • basicSolution C I id b) ∧
    (R.pinv *ᵥ y = ∑ J : Fin r ↪o Fin n,
      ((R.submatrix id J).det ^ 2 / minorWeightSum R r) • basicSolution R id J y) := by
  let : Unique (Fin r ↪o Fin r) :=
    ⟨⟨RelEmbedding.refl _⟩, fun I =>
      RelEmbedding.ext fun i => congrFun (ordered_selfSelection_eq_id I) i⟩
  have h₁ := theorem_6 C hC b
  have h₂ := theorem_6 R hR y
  rw [Finset.sum_comm] at h₂
  have hid : ((default : Fin r ↪o Fin r) : Fin r → Fin r) = id :=
    ordered_selfSelection_eq_id _
  simpa only [Fintype.sum_unique, maximalMinorWeight, hid, Real.norm_eq_abs, sq_abs] using
    And.intro h₁ h₂

end FullRank

section Weighted

variable {m n : Type*} [Fintype m] [Fintype n] [LinearOrder m] [LinearOrder n] {r : ℕ}

omit [Fintype n] in
private theorem det_scaled_minor_sq (A : Matrix m n ℝ) (d : m → ℝ) (hd : ∀ i, 0 < d i)
    (I : Fin r ↪o m) (J : Fin r ↪o n) :
    ((diagonal (fun i => Real.sqrt (d i)) * A).submatrix I J).det ^ 2 =
      (∏ i : Fin r, d (I i)) * (A.submatrix I J).det ^ 2 := by
  have h : (diagonal (fun i => Real.sqrt (d i)) * A).submatrix I J =
      diagonal (fun i => Real.sqrt (d (I i))) * A.submatrix I J := by
    ext i j
    simp only [submatrix_apply, diagonal_mul]
  rw [h, det_mul, det_diagonal, mul_pow, ← Finset.prod_pow]
  simp only [Real.sq_sqrt (hd _).le]

omit [Fintype n] in
private theorem basicInverse_scaled_mul (A : Matrix m n ℝ) (d : m → ℝ) (hd : ∀ i, 0 < d i)
    (I : Fin r ↪o m) (J : Fin r ↪o n) :
    basicInverse (diagonal (fun i => Real.sqrt (d i)) * A) I J *
      diagonal (fun i => Real.sqrt (d i)) = basicInverse A I J := by
  let S : Matrix m m ℝ := diagonal (fun i => Real.sqrt (d i))
  let T : Matrix (Fin r) (Fin r) ℝ := diagonal (fun i => Real.sqrt (d (I i)))
  have hT : IsUnit T.det := by
    rw [show T = diagonal (fun i => Real.sqrt (d (I i))) from rfl, det_diagonal]
    exact isUnit_iff_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mpr (fun i _ => (Real.sqrt_pos.2 (hd _)).ne'))
  have hblock : (S * A).submatrix I J = T * A.submatrix I J := by
    ext i j
    simp only [S, T, submatrix_apply, diagonal_mul]
  have hrow : minorRowSelector I * S = T * minorRowSelector I := by
    ext i j
    simp only [S, T, minorRowSelector, diagonal_mul, mul_diagonal, submatrix_apply, id_eq,
      Matrix.one_apply]
    by_cases e : I i = j
    · simp [e]
    · simp [e]
  rw [basicInverse, basicInverse, hblock, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]
  rw [hrow, ← Matrix.mul_assoc T⁻¹ T _, Matrix.nonsing_inv_mul _ hT, Matrix.one_mul]

/-- Equation (94) of [benIsrael2003generalized], Chapter 3.
A positive diagonal weighting multiplies each squared determinant by the
product of weights in its selected rows. -/
def weightedBasicWeight (A : Matrix m n ℝ) (d : m → ℝ)
    (I : Fin r ↪o m) (J : Fin r ↪o n) : ℝ :=
  ((∏ i : Fin r, d (I i)) * (A.submatrix I J).det ^ 2) /
    ∑ K : Fin r ↪o m, ∑ L : Fin r ↪o n, (∏ i : Fin r, d (K i)) * (A.submatrix K L).det ^ 2

/-- **Theorem 7**, Equations (90)–(94), of [benIsrael2003generalized], Chapter 3.
The weighted residual minimizers are precisely the solutions of the
weighted normal equation. The one of least norm is the indicated
determinant-weighted average of the basic solutions of the original system. -/
theorem theorem_7 (A : Matrix m n ℝ) (hr : A.rank = r) (b : EuclideanSpace ℝ m)
    (d : m → ℝ) (hd : ∀ i, 0 < d i) :
    let D := diagonal d
    let S := diagonal (fun i => Real.sqrt (d i))
    let x := toEuclideanLin (S * A).pinv (toEuclideanLin S b)
    (∀ u : EuclideanSpace ℝ n,
      (∀ v : EuclideanSpace ℝ n,
        ‖toEuclideanLin S (toEuclideanLin A u - b)‖ ≤ ‖toEuclideanLin S (toEuclideanLin A v - b)‖)
        ↔ toEuclideanLin (Aᵀ * D * A) u = toEuclideanLin (Aᵀ * D) b) ∧
    IsMinNormLeastSquaresSolution (S * A) (toEuclideanLin S b) x ∧
    WithLp.ofLp x = ∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n,
      weightedBasicWeight A d I J • basicSolution A I J (WithLp.ofLp b) := by
  let D := diagonal d
  let S := diagonal (fun i => Real.sqrt (d i))
  have hS : IsUnit S.det := by
    rw [show S = diagonal (fun i => Real.sqrt (d i)) from rfl, det_diagonal]
    exact isUnit_iff_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mpr (fun i _ => (Real.sqrt_pos.2 (hd i)).ne'))
  have hrS : (S * A).rank = r := (rank_mul_eq_right_of_isUnit_det _ _ hS).trans hr
  have hSD : S * S = D := by
    rw [show S = diagonal (fun i => Real.sqrt (d i)) from rfl, diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hd i).le
  have hST : Sᵀ = S := diagonal_transpose _
  have hnorm : (S * A)ᴴ = Aᵀ * S := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, hST]
  refine ⟨?_, isMinNormLeastSquaresSolution_pinv _ _, ?_⟩
  · intro u
    simp only [map_sub, ← toEuclideanLin_mul_apply]
    change IsLeastSquaresSolution (S * A) (toEuclideanLin S b) u ↔ _
    rw [isLeastSquaresSolution_iff_normalEquations, ← toEuclideanLin_mul_apply, hnorm,
      ← Matrix.mul_assoc _ S A, Matrix.mul_assoc Aᵀ S S, hSD]
  · have hw (I : Fin r ↪o m) (J : Fin r ↪o n) :
        maximalMinorWeight (S * A) I J = weightedBasicWeight A d I J := by
      simp only [maximalMinorWeight, weightedBasicWeight, minorWeightSum, Real.norm_eq_abs,
        sq_abs, S, det_scaled_minor_sq A d hd]
    change (S * A).pinv *ᵥ (S *ᵥ WithLp.ofLp b) = _
    rw [theorem_6 (S * A) hrS, Finset.sum_congr rfl]
    intro I _
    apply Finset.sum_congr rfl
    intro J _
    rw [hw, basicSolution, basicSolution, Matrix.mulVec_mulVec, basicInverse_scaled_mul A d hd]

open scoped Matrix.Norms.L2Operator in
/-- The operator norms in **Equations (98)–(99)** are bounded
independently of the positive diagonal weights for each fixed matrix. -/
theorem weightedBasicOperator_uniformly_bounded (A : Matrix m n ℝ) (hr : A.rank = r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : m → ℝ), (∀ i, 0 < d i) →
      let K := (Aᵀ * diagonal d * A).pinv * Aᵀ * diagonal d
      ‖K‖ ≤ C ∧ ‖A * K‖ ≤ ‖A‖ * C := by
  let C := ∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n, ‖basicInverse A I J‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨C, hC, ?_⟩
  intro d hd K
  let S := diagonal fun i => Real.sqrt (d i)
  have hs : IsUnit S.det := by
    rw [show S = diagonal _ from rfl, det_diagonal]
    exact isUnit_iff_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mpr (fun i _ => (Real.sqrt_pos.mpr (hd i)).ne'))
  have hSR : (S * A).rank = r := (rank_mul_eq_right_of_isUnit_det _ _ hs).trans hr
  have hSS : S * S = diagonal d := by
    rw [show S = diagonal _ from rfl, diagonal_mul_diagonal]
    exact congrArg diagonal (funext fun i => Real.mul_self_sqrt (hd i).le)
  have hconj : (S * A)ᴴ = Aᵀ * S := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, diagonal_transpose]
  have hgram : (S * A)ᴴ * (S * A) = Aᵀ * diagonal d * A := by
    rw [hconj, ← hSS]
    simp only [Matrix.mul_assoc]
  have hsum : K = ∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n,
      maximalMinorWeight (S * A) I J • basicInverse A I J := calc
    K = (S * A).pinv * S := by
      rw [(Chapter01.pinv_gram (S * A)).1, hgram, hconj]
      simp only [K, ← hSS, Matrix.mul_assoc]
    _ = _ := by
      rw [pinv_eq_sum_basicInverses (S * A) hSR, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro I _
      rw [Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro J _
      rw [Matrix.smul_mul, basicInverse_scaled_mul A d hd I J]
      rfl
  obtain ⟨hweight, htotal⟩ := maximalMinorWeight_convex (S * A) hSR
  have hnorm (I : Fin r ↪o m) (J : Fin r ↪o n) : ‖basicInverse A I J‖ ≤ C := by
    calc
      _ ≤ ∑ j : Fin r ↪o n, ‖basicInverse A I j‖ :=
        Finset.single_le_sum (fun (j : Fin r ↪o n) _ => norm_nonneg (basicInverse A I j))
          (Finset.mem_univ J)
      _ ≤ C := by
        apply Finset.single_le_sum (f := fun i : Fin r ↪o m => ∑ j : Fin r ↪o n,
          ‖basicInverse A i j‖) (fun i _ => ?_) (Finset.mem_univ I)
        exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hK : ‖K‖ ≤ C := calc
    _ ≤ ∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n,
        ‖maximalMinorWeight (S * A) I J • basicInverse A I J‖ := by
      rw [hsum]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ => norm_sum_le _ _)
    _ ≤ ∑ I : Fin r ↪o m, ∑ J : Fin r ↪o n, maximalMinorWeight (S * A) I J * C := by
      apply Finset.sum_le_sum fun I _ => Finset.sum_le_sum fun J _ => ?_
      rw [norm_smul, Real.norm_of_nonneg (hweight I J)]
      exact mul_le_mul_of_nonneg_left (hnorm I J) (hweight I J)
    _ = C := by simp_rw [← Finset.sum_mul]; rw [htotal, one_mul]
  exact ⟨hK, (l2_opNorm_mul A K).trans (mul_le_mul_of_nonneg_left hK (norm_nonneg A))⟩

end Weighted

section Regularized

open Filter Set
open scoped Topology

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Exercise 45** of [benIsrael2003generalized], Chapter 3.
The unique minimizer of the squared residual plus the positive quadratic
penalty tends to the minimum-norm least-squares solution as the penalty
parameter tends to zero through nonzero values. -/
theorem exercise_3_45 (A : Matrix m n ℝ) (b : EuclideanSpace ℝ m) :
    (∀ α : ℝ, α ≠ 0 → ∀ x : EuclideanSpace ℝ n,
      IsMinOn (fun u => ‖toEuclideanLin A u - b‖ ^ 2 + α ^ 2 * ‖u‖ ^ 2) univ x ↔
        x = toEuclideanLin (A.tikhonov (α ^ 2)) b) ∧
    Tendsto (fun α : ℝ => toEuclideanLin (A.tikhonov (α ^ 2)) b) (𝓝[≠] 0)
      (𝓝 (toEuclideanLin A.pinv b)) := by
  constructor
  · intro α hα x
    exact (Matrix.eq_toEuclideanLin_tikhonov_iff_isMinOn A (sq_pos_of_ne_zero hα) b x).symm
  · let Eval : Matrix n m ℝ →ₗ[ℝ] EuclideanSpace ℝ n :=
      ((LinearMap.applyₗ (R := ℝ) (M₂ := EuclideanSpace ℝ n)) b).comp toEuclideanLin.toLinearMap
    have hEval : Continuous Eval := Eval.continuous_of_finiteDimensional
    have hpos : Tendsto (fun α : ℝ => α ^ 2) (𝓝[≠] 0) (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      have hc : Continuous (fun α : ℝ => α ^ 2) := continuous_id.pow 2
      have hzero : Tendsto (fun α : ℝ => α ^ 2) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
        simpa using hc.continuousAt (x := (0 : ℝ)).tendsto
      exact ⟨hzero.mono_left nhdsWithin_le_nhds,
        eventually_of_mem self_mem_nhdsWithin (fun x hx => sq_pos_of_ne_zero hx)⟩
    exact hEval.continuousAt.tendsto.comp (A.tendsto_tikhonov_pinv.comp hpos)

end Regularized

section BlockAverages

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
  [LinearOrder m] [LinearOrder n] [DecidableEq k] {r : ℕ}

/-- The reciprocal of the selected column submatrix, extended by zero. -/
def columnSliceInverse (A : Matrix m n ℝ) (J : Fin r ↪o n) : Matrix n m ℝ :=
  minorColumnSelector J * (A.submatrix id J).pinv

/-- The aggregate determinant weight of a column submatrix. It is zero
when the selected columns are dependent. -/
def columnSliceWeight (A : Matrix m n ℝ) (J : Fin r ↪o n) : ℝ :=
  minorWeightSum (A.submatrix id J) r / minorWeightSum A r

/-- The reciprocal of the selected row submatrix, extended by zero. -/
def rowSliceInverse (A : Matrix m n ℝ) (I : Fin r ↪o m) : Matrix n m ℝ :=
  (columnSliceInverse Aᵀ I)ᵀ

/-- The aggregate determinant weight of a row submatrix. -/
def rowSliceWeight (A : Matrix m n ℝ) (I : Fin r ↪o m) : ℝ :=
  columnSliceWeight Aᵀ I

private theorem minorWeightSum_ne_zero (A : Matrix m n ℝ) (hr : A.rank = r) :
    minorWeightSum A r ≠ 0 := by
  intro h
  have he := (maximalMinorWeight_convex A hr).2
  simp [maximalMinorWeight, h] at he

/-- The compressed determinant average may first group minors by column
selections and omit the singular selections with zero weight. -/
theorem pinv_compression_det_eq_sum_columnSlices (A : Matrix m n ℝ) (hr : A.rank = r)
    (U : Matrix m k ℝ) (V : Matrix k n ℝ) :
    (V * A.pinv * U).det = ∑ J : Fin r ↪o n,
      columnSliceWeight A J * (V * columnSliceInverse A J * U).det := by
  let : Unique (Fin r ↪o Fin r) :=
    ⟨⟨RelEmbedding.refl _⟩, fun I =>
      RelEmbedding.ext fun i => congrFun (ordered_selfSelection_eq_id I) i⟩
  have hid : ((default : Fin r ↪o Fin r) : Fin r → Fin r) = id :=
    ordered_selfSelection_eq_id _
  have ha := pinv_compression_det_eq_sum_basic A hr U V
  simp only [RCLike.ofReal_real_eq_id, id_eq] at ha
  rw [ha, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  let C := A.submatrix id J
  let T := minorColumnSelector (𝕜 := ℝ) J
  have hCminor (I : Fin r ↪o m) : C.submatrix I id = A.submatrix I J := rfl
  by_cases hC : C.rank = r
  · have hc := pinv_compression_det_eq_sum_basic C hC U (V * T)
    simp only [Fintype.sum_unique, RCLike.ofReal_real_eq_id, id_eq, hid] at hc
    rw [columnSliceInverse, show V * (minorColumnSelector J * C.pinv) * U =
      (V * T) * C.pinv * U by simp only [T, Matrix.mul_assoc], hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    have hb : (V * T) * basicInverse C I id * U = V * basicInverse A I J * U := by
      simp only [basicInverse, minorColumnSelector, submatrix_id_id, Matrix.one_mul, hCminor, T,
        Matrix.mul_assoc]
    have hw : columnSliceWeight A J * (‖(C.submatrix I id).det‖ ^ 2 / minorWeightSum C r) =
        maximalMinorWeight A I J := by
      rw [columnSliceWeight, maximalMinorWeight, hCminor]
      change minorWeightSum C r / minorWeightSum A r *
        (‖(A.submatrix I J).det‖ ^ 2 / minorWeightSum C r) = _
      field_simp [minorWeightSum_ne_zero C hC, minorWeightSum_ne_zero A hr]
    have hWC : maximalMinorWeight C I default =
        ‖(C.submatrix I id).det‖ ^ 2 / minorWeightSum C r := by
      rw [maximalMinorWeight, hid]
    rw [hWC, hb, ← mul_assoc, hw]
  · have hz (I : Fin r ↪o m) : (A.submatrix I J).det = 0 := by
      by_contra h
      have he := rank_submatrix_le C I id
      rw [hCminor, rank_of_det_ne_zero h, Fintype.card_fin] at he
      exact hC (le_antisymm (by simpa using rank_le_card_width C) he)
    have hz' (I : Fin r ↪o m) : ((A.submatrix id J).submatrix I id).det = 0 := hz I
    simp only [columnSliceWeight, maximalMinorWeight, hz, norm_zero, zero_pow (by decide : 2 ≠ 0),
      zero_div, zero_mul, Finset.sum_const_zero, minorWeightSum, Fintype.sum_unique, hid, hz']

private theorem real_pinv_transpose (A : Matrix m n ℝ) : Aᵀ.pinv = A.pinvᵀ := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using A.pinv_conjTranspose

/-- The compressed determinant average may instead group minors by row
selections. -/
theorem pinv_compression_det_eq_sum_rowSlices (A : Matrix m n ℝ) (hr : A.rank = r)
    (U : Matrix m k ℝ) (V : Matrix k n ℝ) :
    (V * A.pinv * U).det = ∑ I : Fin r ↪o m,
      rowSliceWeight A I * (V * rowSliceInverse A I * U).det := by
  have he := pinv_compression_det_eq_sum_columnSlices Aᵀ (A.rank_transpose.trans hr) Vᵀ Uᵀ
  rw [real_pinv_transpose] at he
  rw [show (Uᵀ * A.pinvᵀ * Vᵀ).det = (V * A.pinv * U).det by
    rw [← det_transpose (Uᵀ * A.pinvᵀ * Vᵀ)]
    simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro I _
  rw [← det_transpose (Uᵀ * columnSliceInverse Aᵀ I * Vᵀ)]
  simp only [transpose_mul, transpose_transpose, rowSliceWeight, rowSliceInverse, Matrix.mul_assoc]

/-- **Exercise 44** of [benIsrael2003generalized], Chapter 3.
Grouping the basic inverse average by either kind of selection gives an
average of the reciprocals of the corresponding full-rank submatrices. -/
theorem exercise_3_44 (A : Matrix m n ℝ) (hr : A.rank = r) :
    (A.pinv = ∑ J : Fin r ↪o n, columnSliceWeight A J • columnSliceInverse A J) ∧
    (A.pinv = ∑ I : Fin r ↪o m, rowSliceWeight A I • rowSliceInverse A I) := by
  constructor <;> ext j i
  · have he := pinv_compression_det_eq_sum_columnSlices A hr
      (minorColumnSelector (fun _ : Unit => i)) (minorRowSelector (fun _ : Unit => j))
    simpa only [minorRowSelector_mul, mul_minorColumnSelector, submatrix_submatrix,
      Function.id_comp, Function.comp_id, det_unique, submatrix_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
      using he
  · have he := pinv_compression_det_eq_sum_rowSlices A hr
      (minorColumnSelector (fun _ : Unit => i)) (minorRowSelector (fun _ : Unit => j))
    simpa only [minorRowSelector_mul, mul_minorColumnSelector, submatrix_submatrix,
      Function.id_comp, Function.comp_id, det_unique, submatrix_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
      using he

end BlockAverages

/-- **Example 1** of [benIsrael2003generalized], Chapter 3.
A positive definite nondiagonal residual weight produces the displayed
coefficient whose first entry grows without bound as ε tends to zero. -/
theorem example_3_1_weighted_nondiagonal (ε : ℝ) (hε : 0 < ε) :
    let A : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]
    let W : Matrix (Fin 2) (Fin 2) ℝ := !![2, ε; ε, ε ^ 2]
    W.PosDef ∧ (Aᵀ * W * A)⁻¹ * Aᵀ * W = !![ε⁻¹, 1] := by
  intro A W
  let R : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, ε]
  have hR : R.det = ε := by simp [R, det_fin_two]
  have hRW : Rᴴ * R = W := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [R, W, Matrix.mul_apply, Fin.sum_univ_two, pow_two]; ring
  have hw := (posSemidef_conjTranspose_mul_self R).posDef_iff_isUnit.mpr
    ((isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (by
      rw [det_mul, det_conjTranspose, star_trivial, hR]
      exact mul_ne_zero hε.ne' hε.ne')))
  refine ⟨hRW ▸ hw, ?_⟩
  have hgram : Aᵀ * W * A = !![ε ^ 2] := by
    ext i j
    fin_cases i
    fin_cases j
    simp [A, W, Matrix.mul_apply, Fin.sum_univ_two]
  have hInv : (Aᵀ * W * A)⁻¹ = !![(ε ^ 2)⁻¹] := by
    rw [hgram]
    ext i j
    fin_cases i
    fin_cases j
    simp [Ring.inverse_eq_inv']
  have hleft : Aᵀ * W = !![ε, ε ^ 2] := by
    ext i j
    fin_cases i
    fin_cases j <;> simp [A, W, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hInv, Matrix.mul_assoc, hleft]
  ext i j
  fin_cases i
  fin_cases j <;> simp [Matrix.mul_apply] <;> field_simp

end BenIsraelGreville.Chapter03
