/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Stationary.Splitting
import NumlibSurface.SaadSparse.Chapter04.Section01

/-!
# Saad, Section 10.2: Jacobi, SOR and SSOR preconditioners

This module formalizes Section 10.2 of [saad2003iterative], which reads the classical stationary
iterations of Chapter 4 as preconditioners. A splitting $A = M - N$ with $M$ nonsingular gives the
preconditioner $M$ and the iteration matrix $G = I - M^{-1} A$ of (10.4), and the stationary
iteration $x \leftarrow Gx + M^{-1} b$ is a fixed-point iteration for the preconditioned system
$M^{-1} A x = M^{-1} b$. With the splitting $A = D - E - F$ of Section 4.1 into the diagonal $D$,
the negated strictly lower part $E$ and the negated strictly upper part $F$, the Jacobi
preconditioner (10.5) is $M = D$ and the Gauss–Seidel preconditioner (10.6) is $M = D - E$.

The module also proves the two identities that the section derives for the symmetric Gauss–Seidel
preconditioner $M_{SGS} = (D - E) D^{-1} (D - F)$ of (10.9). First, $M_{SGS} = LU$ with
$L = I - E D^{-1}$ unit lower triangular and $U = D - F$ upper triangular, and each factor has the
sparsity pattern of the corresponding triangular part of $A$. Second, the error of this
factorization is $A - LU = -E D^{-1} F$. The book does not number the second identity; it is the
observation that motivates a factorization whose error vanishes where $A$ is nonzero, that is,
ILU(0). The proofs specialize the splittings of `Numlib.Stationary.Splitting`.

## Main definitions

* Equation (10.9), `SaadSparse.Chapter10.M_sgs`: the symmetric Gauss–Seidel preconditioner
  $M_{SGS} = (D - E) D^{-1} (D - F)$.

## Main results

* Equation (10.4), `SaadSparse.Chapter10.equation_10_4`: the iteration matrix of a splitting
  $A = M - N$ is $I - M^{-1} A$.
* Equation (10.5), `SaadSparse.Chapter10.equation_10_5`: the Jacobi preconditioner $M = D$ has the
  iteration matrix $I - D^{-1} A$.
* Equation (10.6), `SaadSparse.Chapter10.equation_10_6`: the Gauss–Seidel preconditioner $M = D - E$
  has the iteration matrix $I - (D - E)^{-1} A$.
* Section 10.2, `SaadSparse.Chapter10.M_sgs_eq_mul`: $M_{SGS} = LU$ with $L = I - E D^{-1}$ and
  $U = D - F$.
* Section 10.2, `SaadSparse.Chapter10.sub_M_sgs_eq`: the error of this factorization is
  $A - LU = -E D^{-1} F$.

## Conventions

* The matrices $D$, $E$ and $F$ are `SaadSparse.Chapter04.D`, `SaadSparse.Chapter04.E` and
  `SaadSparse.Chapter04.F` of Section 4.1, with $A = D - E - F$.
* "$D$ is nonsingular" is `IsUnit (diagPart A)`, that is, every diagonal entry of $A$ is nonzero.

## Implementation notes

* A splitting is `Stationary.Splitting A`, and its iteration matrix is
  `Stationary.Splitting.iterationOperator`. The Jacobi and Gauss–Seidel preconditioners are the $M$
  of `Matrix.jacobiSplitting` and `Matrix.gaussSeidelSplitting`, so (10.4)–(10.6) are the
  definitions of the backbone read from the preconditioning side.

## Deviations from the source

* **Totalization.** The SGS matrix and lower factor are totalized; their intended factor properties
  use a nonsingular diagonal. See `SaadSparse.Chapter10.M_sgs`, `SaadSparse.Chapter10.L_sgs`.

## Not formalized

* **Example 10.1.** Table 10.1 records a floating-point run of GMRES with the symmetric Gauss–Seidel
  preconditioner on the five test problems of Section 3.7; its measured iteration and operation
  counts carry no mathematical claim.
-/

open Matrix Stationary

namespace SaadSparse.Chapter10

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

/-! ### A splitting read as a preconditioner, (10.4)–(10.6) -/

/-- **Equation (10.4)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ and let
$A = M - N$ be a splitting with $M$ nonsingular. The iteration matrix of the splitting is
$$G = I - M^{-1} A.$$
So the stationary iteration $x \leftarrow Gx + M^{-1} b$ is a fixed-point iteration for the
preconditioned system $M^{-1} A x = M^{-1} b$.

The identity is the definition of `Stationary.Splitting.iterationOperator`: preconditioning and
stationary iteration are two readings of one object. The inverse is `Ring.inverse`. -/
theorem equation_10_4 (s : Splitting A) : s.iterationOperator = 1 - Ring.inverse s.m * A := rfl

/-- **Equation (10.5)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ have a
nonsingular diagonal part $D$. The Jacobi preconditioner is $M = D$, and its iteration matrix is
$$G = I - D^{-1} A.$$

The splitting is `Matrix.jacobiSplitting`. -/
theorem equation_10_5 (h : IsUnit (diagPart A)) :
    (jacobiSplitting A h).iterationOperator = 1 - Ring.inverse (Chapter04.D A) * A := rfl

/-- **Equation (10.6)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ have a
nonsingular diagonal part $D$. The Gauss–Seidel preconditioner is $M = D - E$, and its iteration
matrix is
$$G = I - (D - E)^{-1} A.$$

The splitting is `Matrix.gaussSeidelSplitting`. -/
theorem equation_10_6 (h : IsUnit (diagPart A)) :
    (gaussSeidelSplitting A h).iterationOperator =
      1 - Ring.inverse (Chapter04.D A - Chapter04.E A) * A := by
  rw [Chapter04.D_sub_E]
  rfl

/-! ### The symmetric Gauss–Seidel preconditioner (10.9) -/

/-- **Equation (10.9)** of [saad2003iterative]. For $A \in \mathbb{R}^{n \times n}$ with
$A = D - E - F$, the **symmetric Gauss–Seidel preconditioner** is
$$M_{SGS} = (D - E) D^{-1} (D - F).$$

The inverse $D^{-1}$ is Mathlib's matrix inverse, which is $0$ when $D$ is singular; the results
below assume that $D$ is nonsingular.

**Reading.** The matrix formulas allow a singular diagonal with Lean's zero matrix inverse. The
inverse-diagonal and unit-lower-triangular identities are stated for an invertible diagonal.
-/
noncomputable def M_sgs (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (Chapter04.D A - Chapter04.E A) * (Chapter04.D A)⁻¹ * (Chapter04.D A - Chapter04.F A)

/-- Let $A \in \mathbb{R}^{n \times n}$ have a nonsingular diagonal part. Then $M_{SGS}$ is the
preconditioner $M$ of the SSOR splitting `Matrix.ssorSplitting` with $\omega = 1$: symmetric
Gauss–Seidel is SSOR with $\omega = 1$, so $M_{SGS}$ inherits all results proved for SSOR. -/
theorem M_sgs_eq_ssorSplitting (h : IsUnit (diagPart A)) :
    M_sgs A = (ssorSplitting A h one_ne_zero (by norm_num)).m := by
  change M_sgs A =
    ((1 : ℝ) * (2 - 1))⁻¹ • ((diagPart A + (1 : ℝ) • strictLower A) * (diagPart A)⁻¹ *
      (diagPart A + (1 : ℝ) • strictUpper A))
  rw [M_sgs, Chapter04.D_sub_E, Chapter04.D_sub_F, Chapter04.D]
  norm_num

/-- The unit lower triangular factor $L = I - E D^{-1}$ of the factorization $M_{SGS} = LU$.

**Reading.** The matrix formulas allow a singular diagonal with Lean's zero matrix inverse. The
inverse-diagonal and unit-lower-triangular identities are stated for an invertible diagonal.
-/
noncomputable def L_sgs (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - Chapter04.E A * (Chapter04.D A)⁻¹

/-- The upper triangular factor $U = D - F$ of the factorization $M_{SGS} = LU$. -/
def U_sgs (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := Chapter04.D A - Chapter04.F A

/-- If the diagonal part $D$ of $A$ is nonsingular, then $D^{-1}$ is the diagonal matrix with the
entries $a_{ii}^{-1}$. The hypothesis is needed because Mathlib's inverse of a singular matrix
is $0$. -/
theorem inv_D_eq (h : IsUnit (diagPart A)) :
    (Chapter04.D A)⁻¹ = Matrix.diagonal fun i => (A i i)⁻¹ := by
  have hne : ∀ i, A i i ≠ 0 := (Matrix.isUnit_diagPart_iff A).mp h
  refine Matrix.inv_eq_right_inv ?_
  rw [Chapter04.D, Matrix.diagPart, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (hne i)

/-- If the diagonal part $D$ of $A$ is nonsingular, then $(D^{-1})_{ij} = a_{ii}^{-1}$ for $i = j$
and $(D^{-1})_{ij} = 0$ for $i \neq j$. -/
theorem inv_D_apply (h : IsUnit (diagPart A)) (i j : Fin n) :
    (Chapter04.D A)⁻¹ i j = if i = j then (A i i)⁻¹ else 0 := by
  rw [inv_D_eq h, Matrix.diagonal_apply]

/-- If the diagonal part of $A$ is nonsingular, then the entries of $L = I - E D^{-1}$ are
$l_{ii} = 1$, $l_{ij} = a_{ij} / a_{jj}$ for $j < i$, and $l_{ij} = 0$ for $j > i$. So $L$ is
unit lower triangular and has the sparsity pattern of the strictly lower part of $A$. -/
theorem L_sgs_apply (h : IsUnit (diagPart A)) (i j : Fin n) :
    L_sgs A i j = if i = j then 1 else if j < i then A i j * (A j j)⁻¹ else 0 := by
  have hprod : (strictLower A * (Chapter04.D A)⁻¹) i j = strictLower A i j * (A j j)⁻¹ := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [inv_D_apply h]
      simp
    · intro k _ hk
      rw [inv_D_apply h]
      simp [hk]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [L_sgs, Chapter04.E, Matrix.sub_apply, Matrix.one_apply, Matrix.neg_mul, Matrix.neg_apply,
    hprod, strictLower_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [hij]

/-- The entries of $U = D - F$ are $u_{ii} = a_{ii}$, $u_{ij} = a_{ij}$ for $i < j$, and
$u_{ij} = 0$ for $i > j$: the diagonal and the strictly upper part of $A$. -/
theorem U_sgs_apply (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    U_sgs A i j = if i = j then A i i else if i < j then A i j else 0 := by
  rw [U_sgs, Chapter04.D, Chapter04.F, sub_neg_eq_add, Matrix.add_apply, diagPart_apply,
    strictUpper_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.ne]
  · simp
  · simp [h.ne', asymm h]

/-- If the diagonal part of $A$ is nonsingular, then $L = I - E D^{-1}$ is lower triangular. -/
theorem isLowerTriangular_L_sgs (h : IsUnit (diagPart A)) : (L_sgs A).IsLowerTriangular := by
  intro i j hij
  have hlt : i < j := OrderDual.toDual_lt_toDual.mp hij
  simp [L_sgs_apply h, hlt.ne, asymm hlt]

/-- The factor $U = D - F$ is upper triangular. -/
theorem isUpperTriangular_U_sgs (A : Matrix (Fin n) (Fin n) ℝ) : (U_sgs A).IsUpperTriangular := by
  intro i j hij
  have hlt : j < i := hij
  simp [U_sgs_apply, hlt.ne', asymm hlt]

/-- **Section 10.2** of [saad2003iterative], factorization of the symmetric Gauss–Seidel
preconditioner. Let $A \in \mathbb{R}^{n \times n}$ have a nonsingular diagonal part $D$. Then
$$M_{SGS} = LU, \qquad L = I - E D^{-1}, \quad U = D - F.$$
Here $L$ is unit lower triangular and $U$ is upper triangular, and each has the sparsity pattern
of the corresponding triangular part of $A$ (`SaadSparse.Chapter10.L_sgs_apply`,
`SaadSparse.Chapter10.U_sgs_apply`). So a symmetric Gauss–Seidel sweep is an exact triangular
factorization of some matrix that has the sparsity pattern of $A$. -/
theorem M_sgs_eq_mul (h : IsUnit (diagPart A)) : M_sgs A = L_sgs A * U_sgs A := by
  have hdet : IsUnit (Chapter04.D A).det := (isUnit_iff_isUnit_det _).mp h
  rw [M_sgs, L_sgs, U_sgs, sub_mul, Matrix.mul_nonsing_inv _ hdet]

/-- **Section 10.2** of [saad2003iterative], the display before Example 10.1. Let
$A \in \mathbb{R}^{n \times n}$ have a nonsingular diagonal part $D$, and let $L = I - E D^{-1}$
and $U = D - F$. Then the error matrix of the factorization $M_{SGS} = LU$ is
$$A - LU = -E D^{-1} F.$$

In general this matrix is nonzero, also in positions where $A$ is nonzero. This observation
motivates a factorization whose error vanishes in those positions, that is, ILU(0). -/
theorem sub_M_sgs_eq (h : IsUnit (diagPart A)) :
    A - L_sgs A * U_sgs A = -(Chapter04.E A * (Chapter04.D A)⁻¹ * Chapter04.F A) := by
  have hdet : IsUnit (Chapter04.D A).det := (isUnit_iff_isUnit_det _).mp h
  have hA : A = Chapter04.D A - Chapter04.E A - Chapter04.F A := Chapter04.decomp A
  have hDD : Chapter04.E A * (Chapter04.D A)⁻¹ * Chapter04.D A = Chapter04.E A := by
    rw [mul_assoc, Matrix.nonsing_inv_mul _ hdet, mul_one]
  rw [L_sgs, U_sgs, sub_mul, one_mul, mul_sub, hDD]
  nth_rewrite 1 [hA]
  abel

end SaadSparse.Chapter10
