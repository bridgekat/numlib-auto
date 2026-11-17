/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Basic
import Numlib.Krylov.JacobiReconstruction
import Numlib.LinearAlgebra.Matrix.Cholesky
import NumlibSurface.LiesenStrakos.Chapter03.Section01

/-!
# Factorisation of the matrix of moments

The Gram matrix of the monomials $1,X,\ldots,X^n$ for the integral pairing has entries given by
the moments of the distribution. Section 3.6 of [liesen2013krylov] also uses the shifted Hankel
matrix, which increases the moment index by one.

## Main definitions

* `LiesenStrakos.Chapter03.hankelMomentMatrix` is the Hankel matrix with entries $\xi_{i+j}$.
* `LiesenStrakos.Chapter03.shiftedHankelMomentMatrix` has entries $\xi_{i+j+1}$.

## Main results

* `LiesenStrakos.Chapter03.theorem_3_6_1` gives each coefficient of the orthonormal polynomials
  as an entry of the inverse lower Cholesky factor.

-/

open Matrix MeasureTheory OrthogonalPolynomial Polynomial
open scoped Polynomial

namespace LiesenStrakos.Chapter03

/-- Given the moments $(\xi_k)$ of a distribution, the order-$(n+1)$ matrix of moments has
entries $M_{ij}=\xi_{i+j}$. This is (3.6.1) of [liesen2013krylov]. -/
noncomputable def hankelMomentMatrix (μ : Measure ℝ) (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => stieltjesMoment μ (i.val + j.val)

/-- The shifted order-$(n+1)$ matrix of moments has entries $M'_{ij}=\xi_{i+j+1}$. This is
(3.6.2) of [liesen2013krylov]. -/
noncomputable def shiftedHankelMomentMatrix (μ : Measure ℝ) (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => stieltjesMoment μ (i.val + j.val + 1)

/-- **Theorem 3.6.1** of [liesen2013krylov]. Let $L$ be the lower Cholesky factor of
the order-$(n+1)$ moment matrix. Entry $(i,j)$ of $L^{-1}$ is the coefficient of $X^j$
in the orthonormal polynomial of degree $i$. Only the first $n+1$ norms need be positive. -/
theorem theorem_3_6_1 {μ : Measure ℝ}
    (hint : ∀ p : ℝ[X], Integrable (fun t => p.eval t) μ) {n : ℕ}
    (hnorm : ∀ k < n + 1, 0 < normSq μ k)
    {L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hL : (hankelMomentMatrix μ n).IsCholesky Lᵀ) :
    ∀ i j, L⁻¹ i j = (orthonormalFamily μ i).coeff j := by
  let M := hankelMomentMatrix μ n
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    fun i j => (orthonormalFamily μ i).coeff j
  have hdegree (i : Fin (n + 1)) : (orthonormalFamily μ i).natDegree = i :=
    natDegree_eq_of_degree_eq_some (degree_orthonormalFamily_of_normSq_pos (hnorm _ i.isLt))
  have hBl : B.IsLowerTriangular := by
    intro i j hij
    change (orthonormalFamily μ i).coeff j = 0
    apply coeff_eq_zero_of_natDegree_lt
    rw [hdegree]
    exact hij
  have hBp (i : Fin (n + 1)) : 0 < B i i := by
    change 0 < (orthonormalFamily μ i).coeff i
    have hcoeff : (orthonormalFamily μ i).coeff i = (orthonormalFamily μ i).leadingCoeff := by
      simpa only [hdegree] using (coeff_natDegree (p := orthonormalFamily μ i))
    rw [hcoeff, leadingCoeff_orthonormalFamily]
    exact inv_pos.mpr (Real.sqrt_pos.2 (hnorm _ i.isLt))
  have hEval (i : Fin (n + 1)) (t : ℝ) :
      (orthonormalFamily μ i).eval t = ∑ j : Fin (n + 1), B i j * t ^ (j : ℕ) := by
    change (orthonormalFamily μ i).eval t =
      ∑ j : Fin (n + 1), (orthonormalFamily μ i).coeff (j : ℕ) * t ^ (j : ℕ)
    rw [Fin.sum_univ_eq_sum_range (fun j => (orthonormalFamily μ i).coeff j * t ^ j) (n + 1)]
    exact eval_eq_sum_range' (by rw [hdegree]; exact i.isLt) t
  have hInt (i j : Fin (n + 1)) :
      (B * M * Bᵀ) i j = ∫ t, (orthonormalFamily μ i).eval t * (orthonormalFamily μ j).eval t ∂μ := by
    have hprod (t : ℝ) :
        (orthonormalFamily μ i).eval t * (orthonormalFamily μ j).eval t =
          ∑ k : Fin (n + 1), ∑ l : Fin (n + 1),
            (B i l * B j k) * t ^ (l.val + k.val) := by
      rw [hEval, hEval, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by rw [pow_add]; ring
    have hint' (k l : Fin (n + 1)) : Integrable
        (fun t : ℝ => (B i l * B j k) * t ^ (l.val + k.val)) μ :=
      (by simpa only [eval_pow, eval_X] using hint (X ^ (l.val + k.val)) :
        Integrable (fun t : ℝ => t ^ (l.val + k.val)) μ).const_mul _
    rw [integral_congr_ae (Filter.Eventually.of_forall hprod), integral_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun l _ => hint' k l, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, integral_finsetSum _ fun l _ => hint' k l]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, transpose_apply]
    change B i l * (∫ t, t ^ (l.val + k.val) ∂μ) * B j k =
      (B i l * B j k) * ∫ t, t ^ (l.val + k.val) ∂μ
    ring
  have hGram : B * M * Bᵀ = 1 := by
    ext i j
    rw [hInt, integral_orthonormalFamily_mul_of_normSq_pos hint hnorm i j, Matrix.one_apply]
  have hBdet : IsUnit B.det := hBl.isUnit_det_of_diag_ne_zero fun i => (hBp i).ne'
  let Q := B⁻¹
  have hQl : Q.IsLowerTriangular := hBl.inv
  have hQB : Q * B = 1 := Matrix.nonsing_inv_mul B hBdet
  have hQp (i : Fin (n + 1)) : 0 < Q i i := by
    have hii := congrFun (congrFun hQB i) i
    rw [hQl.mul_apply_self hBl i, one_apply_eq] at hii
    exact pos_of_mul_pos_left (by rw [hii]; norm_num) (hBp i).le
  have hBQ : Bᵀ * Qᵀ = 1 := by simpa using congrArg Matrix.transpose hQB
  have hQQ : Q * Qᵀ = M := calc
    Q * Qᵀ = Q * (B * M * Bᵀ) * Qᵀ := by rw [hGram, mul_one]
    _ = (Q * B) * M * (Bᵀ * Qᵀ) := by simp only [Matrix.mul_assoc]
    _ = M := by rw [hQB, hBQ, one_mul, mul_one]
  have hCQ : M.IsCholesky Qᵀ := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [← Matrix.conjTranspose_eq_transpose_of_trivial] using
        hQl.conjTranspose_isUpperTriangular
    · exact hQp
    · simpa only [conjTranspose_eq_transpose_of_trivial, transpose_transpose] using hQQ
  have hLQ : L = Q := by simpa using congrArg Matrix.transpose (hL.unique hCQ)
  have hQinv : Q⁻¹ = B := Matrix.inv_eq_right_inv hQB
  intro i j
  rw [hLQ, hQinv]

end LiesenStrakos.Chapter03
