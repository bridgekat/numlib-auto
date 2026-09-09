import Numlib.LinearSolve.Stationary.Splitting
import NumlibSurface.SaadSparse.Chapter04.Section01

/-!
# Saad §10.2: Jacobi, SOR and SSOR preconditioners

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §10.2: the classical stationary iterations of Chapter 4 read as preconditioners.

Nothing is constructed here. A splitting `A = M - N` gives a preconditioner `M` and an iteration
matrix `G = I - M⁻¹ A` (10.4), and the Jacobi and Gauss–Seidel preconditioners (10.5)–(10.6) are
`Matrix.jacobiSplitting` and `Matrix.gaussSeidelSplitting` of the backbone seen from that side.
So this file is the dictionary between the two readings, plus the two identities Saad draws in the
section: that the symmetric Gauss–Seidel preconditioner `M_SGS = (D - E) D⁻¹ (D - F)` of (10.9) is
a product `L U` of matrices with the sparsity of the triangular parts of `A`, and that its error
matrix is `A - L U = -E D⁻¹ F`. The second is unnumbered in the book, but it is the observation
that motivates asking for a factorization whose error vanishes where `A` is nonzero, that is,
ILU(0).

The letters `D`, `E`, `F` are the ones fixed by §4.1, in `SaadSparse.Chapter04`.

Not formalized: Example 10.1, which is Table 10.1, the output of a floating point run of
SGS-preconditioned GMRES on the five test problems of §3.7. Stating it would mean asserting the
measured iteration counts and flop counts, which is not a claim about the preconditioner.
-/

open Matrix Stationary

namespace SaadSparse.Chapter10

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

/-! ### A splitting read as a preconditioner, (10.4)–(10.6) -/

/-- Saad (10.4): the iteration matrix of the splitting `A = M - N` is `G = I - M⁻¹ A`, so the
stationary iteration `x ← G x + M⁻¹ b` is a fixed-point iteration for the preconditioned system
`M⁻¹ A x = M⁻¹ b`. This is the definition of `Stationary.Splitting.iterationOperator`, which is
the whole point: preconditioning and stationary iteration are two readings of one object. -/
theorem equation_10_4 (s : Splitting A) : s.iterationOperator = 1 - Ring.inverse s.m * A := rfl

/-- Saad (10.5): the Jacobi preconditioner is `M = D`, with iteration matrix `I - D⁻¹ A`. -/
theorem equation_10_5 (h : IsUnit (diagPart A)) :
    (jacobiSplitting A h).iterationOperator = 1 - Ring.inverse (Chapter04.D A) * A := rfl

/-- Saad (10.6): the Gauss–Seidel preconditioner is `M = D - E`, with iteration matrix
`I - (D - E)⁻¹ A`. -/
theorem equation_10_6 (h : IsUnit (diagPart A)) :
    (gaussSeidelSplitting A h).iterationOperator =
      1 - Ring.inverse (Chapter04.D A - Chapter04.E A) * A := by
  rw [Chapter04.D_sub_E]
  rfl

/-! ### The symmetric Gauss–Seidel preconditioner (10.9) -/

/-- Saad (10.9): the symmetric Gauss–Seidel preconditioner `M_SGS = (D - E) D⁻¹ (D - F)`. -/
noncomputable def M_sgs (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (Chapter04.D A - Chapter04.E A) * (Chapter04.D A)⁻¹ * (Chapter04.D A - Chapter04.F A)

/-- Symmetric Gauss–Seidel is SSOR with `ω = 1`, so `M_SGS` is the `M` of the backbone's
`Matrix.ssorSplitting` at that parameter and inherits everything proved about it. -/
theorem M_sgs_eq_ssorSplitting (h : IsUnit (diagPart A)) :
    M_sgs A = (ssorSplitting A h one_ne_zero (by norm_num)).m := by
  change M_sgs A =
    ((1 : ℝ) * (2 - 1))⁻¹ • ((diagPart A + (1 : ℝ) • strictLower A) * (diagPart A)⁻¹ *
      (diagPart A + (1 : ℝ) • strictUpper A))
  rw [M_sgs, Chapter04.D_sub_E, Chapter04.D_sub_F, Chapter04.D]
  norm_num

/-- The unit lower triangular factor `L = I - E D⁻¹` of Saad's `M_SGS = L U`. -/
noncomputable def L_sgs (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - Chapter04.E A * (Chapter04.D A)⁻¹

/-- The upper triangular factor `U = D - F` of Saad's `M_SGS = L U`. -/
def U_sgs (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := Chapter04.D A - Chapter04.F A

/-- The inverse of the diagonal part is the diagonal matrix of reciprocals. The hypothesis is
needed: `Matrix.inv` is junk-valued at a singular matrix. -/
theorem inv_D_eq (h : IsUnit (diagPart A)) :
    (Chapter04.D A)⁻¹ = Matrix.diagonal fun i => (A i i)⁻¹ := by
  have hne : ∀ i, A i i ≠ 0 := (Matrix.isUnit_diagPart_iff A).mp h
  refine Matrix.inv_eq_right_inv ?_
  rw [Chapter04.D, Matrix.diagPart, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (hne i)

/-- The entries of `D⁻¹`: the reciprocals of the diagonal of `A`, and `0` off it. -/
theorem inv_D_apply (h : IsUnit (diagPart A)) (i j : Fin n) :
    (Chapter04.D A)⁻¹ i j = if i = j then (A i i)⁻¹ else 0 := by
  rw [inv_D_eq h, Matrix.diagonal_apply]

/-- The entries of `L`: `1` on the diagonal, `A i j / A j j` strictly below it and `0` strictly
above. So `L` is unit lower triangular and has exactly the sparsity of the strictly lower part
of `A`. -/
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

/-- The entries of `U = D - F`: the diagonal and strictly upper part of `A`. -/
theorem U_sgs_apply (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    U_sgs A i j = if i = j then A i i else if i < j then A i j else 0 := by
  rw [U_sgs, Chapter04.D, Chapter04.F, sub_neg_eq_add, Matrix.add_apply, diagPart_apply,
    strictUpper_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.ne]
  · simp
  · simp [h.ne', asymm h]

/-- `L` is lower triangular. -/
theorem isLowerTriangular_L_sgs (h : IsUnit (diagPart A)) : (L_sgs A).IsLowerTriangular := by
  intro i j hij
  have hlt : i < j := OrderDual.toDual_lt_toDual.mp hij
  simp [L_sgs_apply h, hlt.ne, asymm hlt]

/-- `U` is upper triangular. -/
theorem isUpperTriangular_U_sgs (A : Matrix (Fin n) (Fin n) ℝ) : (U_sgs A).IsUpperTriangular := by
  intro i j hij
  have hlt : j < i := hij
  simp [U_sgs_apply, hlt.ne', asymm hlt]

/-- Saad's factorization of the symmetric Gauss–Seidel preconditioner: `M_SGS = L U` with
`L = I - E D⁻¹` unit lower triangular and `U = D - F` upper triangular, both with the sparsity of
the corresponding triangular part of `A` (`SaadSparse.Chapter10.L_sgs_apply`,
`SaadSparse.Chapter10.U_sgs_apply`). So a symmetric Gauss–Seidel sweep is an exact triangular
factorization of *some* matrix with the sparsity of `A`. -/
theorem M_sgs_eq_mul (h : IsUnit (diagPart A)) : M_sgs A = L_sgs A * U_sgs A := by
  have hdet : IsUnit (Chapter04.D A).det := (isUnit_iff_isUnit_det _).mp h
  rw [M_sgs, L_sgs, U_sgs, sub_mul, Matrix.mul_nonsing_inv _ hdet]

/-- The error matrix of the symmetric Gauss–Seidel factorization, the display before Saad's
Example 10.1: `A - L U = -E D⁻¹ F`. It is generally nonzero exactly where `E` and `F` overlap
through `D⁻¹`, in particular in positions where `A` is nonzero — which is the observation that
motivates asking for a factorization whose error vanishes there, that is, ILU(0). -/
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
