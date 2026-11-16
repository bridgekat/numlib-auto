/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.SymmetricIndefinite
import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.Analysis.Normed.Ring.CondNumber

/-!
# Conn, Gould and Toint, Section 4.3: Direct methods for solving linear systems

This module formalizes Section 4.3 of [conn2000trust]. It first bounds the effect of perturbations
on a linear system $Ax = b$: if $\|A^{-1} \Delta A\| < 1$, a Neumann series argument (4.3.2)–(4.3.3)
bounds the solution error by the condition number $\kappa(A) = \|A\| \|A^{-1}\|$ times the relative
data errors (4.3.4). It then treats factorizations of real symmetric matrices. A positive-definite
matrix has a Cholesky factorization $A = LL^T$ with $L$ lower triangular (4.3.5), unique up to the
signs of the columns of $L$, and computed column by column (4.3.6)–(4.3.7) or row by row (4.3.8). A
symmetric indefinite matrix has, after a symmetric permutation, a factorization $LBL^T$ with $L$
unit lower triangular and $B$ block diagonal with blocks of order one and two (4.3.9).

The proofs use the backbone modules `Numlib.LinearAlgebra.Matrix.Cholesky`,
`Numlib.LinearAlgebra.Matrix.SymmetricIndefinite`, `Numlib.Analysis.Normed.Ring.Inverse` and
`Numlib.Analysis.Normed.Ring.CondNumber`.

## Main results

* Equation (4.3.1), `ConnGouldToint.Chapter04.perturbed_solution_4_3_1`: the solution error is
  $\Delta x = (I + A^{-1} \Delta A)^{-1} A^{-1} (\Delta b - \Delta A\, x)$.
* Equations (4.3.2)–(4.3.3), `ConnGouldToint.Chapter04.neumann_bound_4_3_3`: if $\|T\| < 1$, then
  $I + T$ is invertible and $\|(I + T)^{-1}\| \le 1 / (1 - \|T\|)$.
* Equation (4.3.4), `ConnGouldToint.Chapter04.relative_solution_error_4_3_4`: the bound on the
  relative solution error by the condition number and the relative data errors.
* Equation (4.3.5), `ConnGouldToint.Chapter04.cholesky_4_3_5`: a symmetric positive-definite matrix
  is $LL^T$ with $L$ lower triangular.
* Equation (4.3.5), `ConnGouldToint.Chapter04.cholesky_unique_up_to_column_signs_4_3_5`: every lower
  triangular factor is the positive-diagonal factor with some columns negated.
* After (4.3.5), `ConnGouldToint.Chapter04.cholesky_of_ldl`: if $A = L D L^T$ with $D \ge 0$
  diagonal, then $A = (L D^{1/2})(L D^{1/2})^T$.
* Equations (4.3.6)–(4.3.7), `ConnGouldToint.Chapter04.cholesky_first_column_4_3_7`: the first
  column of a Cholesky factor and the trailing Schur complement.
* Equation (4.3.8), `ConnGouldToint.Chapter04.cholesky_next_row_4_3_8`: the new row of a bordered
  Cholesky factor.
* Equation (4.3.9), `ConnGouldToint.Chapter04.indefinite_factorization_4_3_9`: a symmetric matrix
  has a permuted block $LBL^T$ factorization with pivots of order one and two.

## Implementation notes

* The perturbation results hold for bounded operators on a real Banach space $E$. The inverse is
  `Ring.inverse`, and the condition number is `NormedRing.condNumber`.

## Deviations from the source

* **Conversion after (4.3.5)** (correction). The diagonal square root multiplies the unit lower
  triangular factor on the right, $L_C = L_L D^{1/2}$, not on the left as printed. See
  `ConnGouldToint.Chapter04.cholesky_of_ldl`.
-/

open Matrix
open scoped Matrix

namespace ConnGouldToint.Chapter04

section Perturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Equations (4.3.2)–(4.3.3)** of [conn2000trust]. Let $E$ be a real Banach space, and let $T$ be
a bounded linear operator on $E$ with $\|T\| < 1$. Then $I + T$ is invertible and
$$\|(I + T)^{-1}\| \le \frac{1}{1 - \|T\|}.$$

In the application, $T = A^{-1} \Delta A$ is the scaled perturbation. -/
theorem neumann_bound_4_3_3 {T : E →L[ℝ] E} (hT : ‖T‖ < 1) :
    IsUnit (1 + T) ∧ ‖Ring.inverse (1 + T)‖ ≤ 1 / (1 - ‖T‖) := by
  have hn : ‖-T‖ < 1 := by simpa using hT
  constructor
  · simpa using isUnit_one_sub_of_norm_lt_one hn
  · have h₁ : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    simpa using NormedRing.norm_inverse_one_sub_le_of_norm_one_le h₁ hn

/-- **Equation (4.3.1)** of [conn2000trust]. Let $E$ be a real Banach space, and let $A$ and
$\Delta A$ be bounded linear operators on $E$ with $A$ invertible and $\|A^{-1} \Delta A\| < 1$.
If $Ax = b$ and $(A + \Delta A)(x + \Delta x) = b + \Delta b$, then
$$\Delta x = (I + A^{-1} \Delta A)^{-1} A^{-1} (\Delta b - \Delta A\, x).$$

The formula follows by subtracting the two equations. -/
theorem perturbed_solution_4_3_1 {A dA : E →L[ℝ] E} (hA : IsUnit A)
    {x dx b db : E} (hx : A x = b) (hxd : (A + dA) (x + dx) = b + db)
    (hsmall : ‖Ring.inverse A * dA‖ < 1) :
    dx = Ring.inverse (1 + Ring.inverse A * dA) (Ring.inverse A (db - dA x)) := by
  let B := 1 + Ring.inverse A * dA
  have hB : IsUnit B := (neumann_bound_4_3_3 hsmall).1
  have hfactor : A * B = A + dA := by
    dsimp [B]
    rw [mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel _ hA, one_mul]
  have he : (A + dA) dx = db - dA x := by
    rw [map_add, add_apply, hx, add_assoc] at hxd
    have hh := add_left_cancel hxd
    exact eq_sub_of_add_eq (by simpa [add_comm] using hh)
  calc
    dx = (Ring.inverse B * B) dx := by rw [Ring.inverse_mul_cancel _ hB]; rfl
    _ = Ring.inverse B (B dx) := rfl
    _ = Ring.inverse B ((Ring.inverse A * (A * B)) dx) := by
      rw [← mul_assoc, Ring.inverse_mul_cancel _ hA, one_mul]
    _ = Ring.inverse B (Ring.inverse A (db - dA x)) := by
      rw [hfactor]
      change Ring.inverse B (Ring.inverse A ((A + dA) dx)) = _
      rw [he]

/-- **Equation (4.3.4)** of [conn2000trust]. Let $E$ be a real Banach space, and let $A$ and
$\Delta A$ be bounded linear operators on $E$ with $A$ invertible and $\|A^{-1} \Delta A\| < 1$.
If $Ax = b$ with $b \neq 0$ and $(A + \Delta A)(x + \Delta x) = b + \Delta b$, then
$$\frac{\|\Delta x\|}{\|x\|} \le \frac{\kappa(A)}{1 - \|A^{-1} \Delta A\|} \left( \frac{\|\Delta
  A\|}{\|A\|} + \frac{\|\Delta b\|}{\|b\|} \right), \qquad \kappa(A) = \|A\| \|A^{-1}\|.$$

The hypothesis $b \neq 0$ makes the relative errors defined; it gives $x \neq 0$ and $A \neq 0$. -/
theorem relative_solution_error_4_3_4 {A dA : E →L[ℝ] E} (hA : IsUnit A)
    {x dx b db : E} (hx : A x = b) (hxd : (A + dA) (x + dx) = b + db)
    (hb : b ≠ 0) (hsmall : ‖Ring.inverse A * dA‖ < 1) :
    ‖dx‖ / ‖x‖ ≤ NormedRing.condNumber A / (1 - ‖Ring.inverse A * dA‖) *
      (‖dA‖ / ‖A‖ + ‖db‖ / ‖b‖) := by
  let q := 1 - ‖Ring.inverse A * dA‖
  let C := Ring.inverse (1 + Ring.inverse A * dA)
  have hq : 0 < q := sub_pos.2 hsmall
  have hx₀ : 0 < ‖x‖ := norm_pos_iff.2 fun h => hb (by simpa [h] using hx.symm)
  have hb₀ : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hbA : ‖b‖ ≤ ‖A‖ * ‖x‖ := by rw [← hx]; exact A.le_opNorm x
  have hA₀ : 0 < ‖A‖ := by
    by_contra! h
    exact (not_lt_of_ge ((hbA.trans (mul_nonpos_of_nonpos_of_nonneg h hx₀.le)))) hb₀
  have hC : ‖C‖ ≤ 1 / q := (neumann_bound_4_3_3 hsmall).2
  have herr : ‖dx‖ ≤ (1 / q * ‖Ring.inverse A‖) * (‖db‖ + ‖dA‖ * ‖x‖) := by
    rw [perturbed_solution_4_3_1 hA hx hxd hsmall]
    change ‖C (Ring.inverse A (db - dA x))‖ ≤ _
    calc
      _ ≤ ‖C‖ * ‖Ring.inverse A (db - dA x)‖ := C.le_opNorm _
      _ ≤ (1 / q) * (‖Ring.inverse A‖ * ‖db - dA x‖) := by
        gcongr
        exact (Ring.inverse A).le_opNorm _
      _ ≤ _ := by
        rw [mul_assoc]
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add_right (dA.le_opNorm x) _)
  have hratio : 1 / ‖x‖ ≤ ‖A‖ / ‖b‖ := by
    apply (div_le_div_iff₀ hx₀ hb₀).2
    simpa using hbA
  calc
    ‖dx‖ / ‖x‖ ≤ ((1 / q * ‖Ring.inverse A‖) * (‖db‖ + ‖dA‖ * ‖x‖)) / ‖x‖ :=
      div_le_div_of_nonneg_right herr hx₀.le
    _ = (1 / q * ‖Ring.inverse A‖) * (‖db‖ * (1 / ‖x‖) + ‖dA‖) := by
      field_simp
    _ ≤ (1 / q * ‖Ring.inverse A‖) * (‖db‖ * (‖A‖ / ‖b‖) + ‖dA‖) := by gcongr
    _ = _ := by
      change _ = NormedRing.condNumber A / q * (‖dA‖ / ‖A‖ + ‖db‖ / ‖b‖)
      rw [NormedRing.condNumber]
      field_simp; ring

end Perturbation

variable {n : ℕ}

/-- **Equation (4.3.5)** of [conn2000trust] (Cholesky factorization). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite. Then there is a lower triangular
$L \in \mathbb{R}^{n \times n}$ with $A = LL^T$. -/
theorem cholesky_4_3_5 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∃ L : Matrix (Fin n) (Fin n) ℝ, L.IsLowerTriangular ∧ A = L * Lᵀ := by
  refine ⟨Matrix.cholesky A, Matrix.isLowerTriangular_cholesky A, ?_⟩
  simpa [conjTranspose_eq_transpose_of_trivial, transpose_transpose] using
    (Matrix.isCholesky_cholesky hA).conjTranspose_mul_self.symm


/-- **Equation (4.3.5)** of [conn2000trust], uniqueness. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric positive definite, and let $L \in \mathbb{R}^{n \times n}$ be lower triangular with
$LL^T = A$. Then there are signs $s_i \in \{1, -1\}$ with
$$L = L_A \operatorname{diag}(s_1, \dots, s_n),$$
where $L_A$ is the Cholesky factor of $A$ with positive diagonal.

The factor $L_A$ is `Matrix.cholesky A`. -/
theorem cholesky_unique_up_to_column_signs_4_3_5 {A L : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hL : L.IsLowerTriangular) (he : L * Lᵀ = A) :
    ∃ s : Fin n → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
      L = Matrix.cholesky A * Matrix.diagonal s := by
  have hdet : L.det ≠ 0 := by
    intro hz
    have ha := (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
    rw [← he, Matrix.det_mul, hz, zero_mul] at ha
    exact not_isUnit_zero ha
  have hn (i : Fin n) : L i i ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular L hL, Finset.prod_ne_zero_iff] at hdet
    exact hdet i (Finset.mem_univ i)
  let s (i : Fin n) : ℝ := if 0 < L i i then 1 else -1
  let S := Matrix.diagonal s
  have hS : S * S = 1 := by
    rw [show S = Matrix.diagonal s from rfl, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases h : 0 < L i i <;> simp [s, h]
  have hSt : Sᵀ = S := Matrix.diagonal_transpose s
  have hLS : (L * S).IsLowerTriangular := by
    intro i j hij
    simp [S, Matrix.mul_diagonal, hL hij]
  have hpos (i : Fin n) : 0 < (L * S) i i := by
    rw [show S = Matrix.diagonal s from rfl, Matrix.mul_diagonal]
    by_cases hi : 0 < L i i
    · simp [s, hi]
    · have hneg : L i i < 0 := lt_of_le_of_ne (le_of_not_gt hi) (hn i)
      simpa [s, hi] using neg_pos.mpr hneg
  have hfac : (L * S) * (L * S)ᵀ = A := by
    rw [Matrix.transpose_mul, hSt, Matrix.mul_assoc, ← Matrix.mul_assoc S S, hS, one_mul, he]
  have hNorm : Matrix.IsCholesky A (L * S)ᵀ := by
    refine ⟨?_, fun i ↦ hpos i, ?_⟩
    · intro i j hij
      exact hLS hij
    · simpa only [conjTranspose_eq_transpose_of_trivial, transpose_transpose] using hfac
  have heq : L * S = Matrix.cholesky A := by
    have hT := congrArg Matrix.transpose (hNorm.unique (Matrix.isCholesky_cholesky hA))
    simpa only [transpose_transpose, conjTranspose_eq_transpose_of_trivial] using hT
  refine ⟨s, fun i ↦ ?_, ?_⟩
  · by_cases h : 0 < L i i <;> simp [s, h]
  · change L = Matrix.cholesky A * S
    rw [← heq, Matrix.mul_assoc, hS, mul_one]

/-- **Section 4.3** of [conn2000trust], the conversion after (4.3.5). Let
$L \in \mathbb{R}^{n \times n}$, let $d \in \mathbb{R}^n$ with $d_i \ge 0$ for all $i$, and let
$D = \operatorname{diag}(d)$. Then
$$(L D^{1/2})(L D^{1/2})^T = L D L^T,$$
so an $LDL^T$ factorization with unit lower triangular $L$ gives the Cholesky factor
$L_C = L D^{1/2}$.

**Correction.** The source multiplies the diagonal square root on the left of the unit lower
triangular factor. The factor order that gives $LDL^T$ is $L D^{1/2}$.

The identity holds for every square $L$; triangularity is not needed. -/
theorem cholesky_of_ldl (L : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) :
    let R := Matrix.diagonal (fun i => √(d i))
    (L * R) * (L * R)ᵀ = L * Matrix.diagonal d * Lᵀ := by
  dsimp only
  rw [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  simp only [Real.mul_self_sqrt (hd _), ← Matrix.mul_assoc]

/-- **Equations (4.3.6)–(4.3.7)** of [conn2000trust]. Let $a_{11}, l_{11} \in \mathbb{R}$ with
$l_{11} > 0$, let $a, l \in \mathbb{R}^n$, and let $A, L \in \mathbb{R}^{n \times n}$. If
$$\begin{bmatrix} a_{11} & a^T \\ a & A \end{bmatrix} = \begin{bmatrix} l_{11} & 0 \\ l & L
  \end{bmatrix} \begin{bmatrix} l_{11} & 0 \\ l & L \end{bmatrix}^T,$$
then
$$l_{11} = \sqrt{a_{11}}, \qquad l = a / l_{11}, \qquad LL^T = A - l l^T.$$
-/
theorem cholesky_first_column_4_3_7 (a₁₁ l₁₁ : ℝ) (a l : Fin n → ℝ)
    (A L : Matrix (Fin n) (Fin n) ℝ) (hl : 0 < l₁₁)
    (h : Matrix.fromBlocks (Matrix.of fun _ _ : Unit => a₁₁)
      (Matrix.of fun _ j => a j) (Matrix.of fun i _ => a i) A =
      Matrix.fromBlocks (Matrix.of fun _ _ : Unit => l₁₁) 0 (Matrix.of fun i _ => l i) L *
        (Matrix.fromBlocks (Matrix.of fun _ _ : Unit => l₁₁) 0 (Matrix.of fun i _ => l i) L)ᵀ) :
    l₁₁ = √a₁₁ ∧ (∀ i, l i = a i / l₁₁) ∧ L * Lᵀ = A - Matrix.vecMulVec l l := by
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply] at h
  obtain ⟨h11, -, h21, h22⟩ := Matrix.fromBlocks_inj.1 h
  have h11' : a₁₁ = l₁₁ * l₁₁ := by
    simpa [Matrix.mul_apply] using congrFun (congrFun h11 ()) ()
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [h11', Real.sqrt_mul_self hl.le]
  · apply (eq_div_iff hl.ne').2
    simpa [Matrix.mul_apply] using (congrFun (congrFun h21 i) ()).symm
  · ext i j
    have he := congrFun (congrFun h22 i) j
    simp [Matrix.mul_apply, Matrix.vecMulVec] at he ⊢
    linarith

/-- **Equation (4.3.8)** of [conn2000trust]. Let $L, A \in \mathbb{R}^{n \times n}$,
$a, l \in \mathbb{R}^n$, and $\alpha, \ell \in \mathbb{R}$ with $\ell \ge 0$. If
$$\begin{bmatrix} A & a \\ a^T & \alpha \end{bmatrix} = \begin{bmatrix} L & 0 \\ l^T & \ell
  \end{bmatrix} \begin{bmatrix} L & 0 \\ l^T & \ell \end{bmatrix}^T,$$
then the new row solves the triangular system $Ll = a$, and $\ell = \sqrt{\alpha - l^T l}$. -/
theorem cholesky_next_row_4_3_8 (L A : Matrix (Fin n) (Fin n) ℝ)
    (a l : Fin n → ℝ) (α ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (h : Matrix.fromBlocks A (Matrix.of fun i _ => a i)
      (Matrix.of fun _ j => a j) (Matrix.of fun _ _ : Unit => α) =
      Matrix.fromBlocks L 0 (Matrix.of fun _ j => l j) (Matrix.of fun _ _ : Unit => ℓ) *
        (Matrix.fromBlocks L 0 (Matrix.of fun _ j => l j) (Matrix.of fun _ _ : Unit => ℓ))ᵀ) :
    L *ᵥ l = a ∧ ℓ = √(α - l ⬝ᵥ l) := by
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply] at h
  obtain ⟨-, h12, -, h22⟩ := Matrix.fromBlocks_inj.1 h
  refine ⟨?_, ?_⟩
  · funext i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using (congrFun (congrFun h12 i) ()).symm
  · have he : α = l ⬝ᵥ l + ℓ * ℓ := by
      simpa [Matrix.mul_apply, dotProduct] using congrFun (congrFun h22 ()) ()
    rw [he, add_comm, add_sub_cancel_right, Real.sqrt_mul_self hℓ]

/-- **Equation (4.3.9)** of [conn2000trust]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric. Then
there are a permutation $\sigma$ of $\{1, \dots, n\}$ and matrices
$L, B \in \mathbb{R}^{n \times n}$ such that the permuted matrix
$P^T A P = (a_{\sigma(i) \sigma(j)})$ equals $L B L^T$, where $L$ is unit lower triangular, $B$
is block diagonal with diagonal blocks of order one and two, and $L$ is the identity on each
diagonal block of order two.

The factorization is `Matrix.IsBlockLDL (A.submatrix σ σ) L B`. -/
theorem indefinite_factorization_4_3_9 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    ∃ (σ : Equiv.Perm (Fin n)) (L B : Matrix (Fin n) (Fin n) ℝ),
      Matrix.IsBlockLDL (A.submatrix σ σ) L B :=
  Matrix.exists_perm_isBlockLDL hA

end ConnGouldToint.Chapter04
