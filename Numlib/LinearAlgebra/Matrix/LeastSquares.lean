import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Numlib.Analysis.Matrix.Frobenius
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Direct.Substitution
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.SVD

/-!
# Least-squares solutions of linear systems

Least-squares solutions of `A x = b` for a rectangular `A : Matrix m n 𝕜`, in the operator picture
of `Numlib/LinearAlgebra/Matrix/SVD`: `Matrix.toEuclideanLin A` acting on `EuclideanSpace`, so
that the pseudoinverse results there apply verbatim ([quarteroni2000numerical] §3.13).

## Main definitions

* `Matrix.IsLeastSquaresSolution A b x`: `x` minimizes `‖A y - b‖` over `y`,
  [quarteroni2000numerical] (3.73).
* `Matrix.IsMinNormLeastSquaresSolution A b x`: a least-squares solution of least norm, (3.76).

## Main results

* `Matrix.isLeastSquaresSolution_iff_normalEquations`: the least-squares solutions are the
  solutions of the normal equations `Aᴴ A x = Aᴴ b` ((3.74)). Both directions are the Pythagorean
  identity `‖A y - b‖² = ‖A x - b‖² + ‖A (y - x)‖²` for a solution `x` of the normal equations
  (`Matrix.norm_toEuclideanLin_sub_sq_eq_of_normalEquations`); for "minimizer ⇒ normal equations"
  the identity is applied with `x = A⁺ b`, which solves them.
* `Matrix.posDef_conjTranspose_mul_self_of_linearIndependent`,
  `Matrix.existsUnique_isLeastSquaresSolution`,
  `Matrix.pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose`,
  `Matrix.isLeastSquaresSolution_iff_eq_pinv_of_linearIndependent`: for full column rank the
  normal equations are positive definite, the solution is unique, and it is `(Aᴴ A)⁻¹ Aᴴ b = A⁺ b`.
* `Matrix.isLeastSquaresSolution_of_qr`, `Matrix.IsQR.isLeastSquaresSolution`,
  `Matrix.norm_sub_sq_eq_of_isQR`, `Matrix.norm_sub_sq_eq_of_isQR_of_isLeastSquaresSolution`:
  [quarteroni2000numerical] Theorem 3.8, the solution `R̃⁻¹ Q̃ᴴ b` through any reduced
  factorization and the value of the minimum, `∑_{i ≥ n} |(Qᴴ b)_i|²`.
* `Matrix.isMinNormLeastSquaresSolution_pinv`, `Matrix.IsMinNormLeastSquaresSolution.eq_pinv`:
  [quarteroni2000numerical] Theorem 3.9, the least-squares solution of least norm is `A⁺ b`, and
  only it.
* `Matrix.pinv_eq_conjTranspose_mul_inv_self_mul_conjTranspose`: for full row rank
  `A⁺ = Aᴴ (A Aᴴ)⁻¹`, the minimal-norm solution of an underdetermined system.
* The geometry of the problem ([golub2013matrix] §5.3.1, §5.5.1): the gradient of `‖A x - b‖²/2`
  is `Aᵀ (A x - b)` (`Matrix.hasGradientAt_leastSquaresObjective`), the solutions form a convex set
  (`Matrix.convex_setOf_isLeastSquaresSolution`) and differ by null vectors
  (`Matrix.IsLeastSquaresSolution.toEuclideanLin_sub_eq_zero`); the augmented system
  `[1 A; Aᴴ 0]` is nonsingular exactly for full column rank (`Matrix.isUnit_augmented_iff`,
  [golub2013matrix] (5.3.20)); `ran(A)⊥` is spanned by the trailing columns of a QR factor
  (`Matrix.IsQR.range_orthogonal_eq_span_lastColumns`, [golub2013matrix] Theorem 5.2.2); a matrix
  with orthonormal columns projects onto its range
  (`Matrix.toEuclideanLin_mul_conjTranspose_eq_starProjection`).
* `Matrix.isMinOn_norm_sub_mul_conjTranspose_iff`: least squares with a matrix unknown on the left,
  `F ↦ ‖A - F Kᴴ‖_F`, row by row ([golub2013matrix] (12.5.16)–(12.5.20)).

The children refine the problem: `LeastSquares/Weighted` (row and column weights, the augmented
system, Paige's generalized least squares), `LeastSquares/Regularized` (ridge regression and
general-form Tikhonov, cross-validation), `LeastSquares/Constrained` (LSQI and LSE),
`LeastSquares/Total` (total least squares) — [golub2013matrix] §6.1–6.3.

## Implementation notes

Vectors are `EuclideanSpace 𝕜 m`, never `m → 𝕜`, because the norm is the point; the
`Matrix.toEuclideanLin_*` glue of `Numlib/Analysis/Matrix/ToEuclideanLin` moves between the two.
The index types are arbitrary `Fintype`s wherever the statement makes sense; `Fin M`, `Fin N` enter
only with the *full* QR factorization `Matrix.IsQR` of `Numlib/LinearAlgebra/Matrix/QR`, whose
reduced factors are the first `N` columns and rows.

## References

* [quarteroni2000numerical] §3.4.3, §3.13; [golub2013matrix] §5.2–5.3, §5.5.
-/

open Finset
open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-! ### Least-squares solutions and the normal equations -/

section NormalEquations

/-- **A least-squares solution** of `A x = b`, [quarteroni2000numerical] (3.73): `x` minimizes the
Euclidean norm of the residual `A y - b` over all `y`. -/
def IsLeastSquaresSolution (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m) (x : EuclideanSpace 𝕜 n) :
    Prop :=
  ∀ y, ‖toEuclideanLin A x - b‖ ≤ ‖toEuclideanLin A y - b‖

variable {A : Matrix m n 𝕜} {b : EuclideanSpace 𝕜 m} {x : EuclideanSpace 𝕜 n}

/-- The definition of a least-squares solution, unfolded. -/
theorem isLeastSquaresSolution_iff :
    IsLeastSquaresSolution A b x ↔ ∀ y, ‖toEuclideanLin A x - b‖ ≤ ‖toEuclideanLin A y - b‖ :=
  Iff.rfl

variable [DecidableEq m]

/-- **The Pythagorean identity of least squares**: if `x` solves the normal equations
`Aᴴ A x = Aᴴ b`, then the residual `A x - b` is orthogonal to the range of `A`, so
`‖A y - b‖² = ‖A x - b‖² + ‖A (y - x)‖²` for every `y`. -/
theorem norm_toEuclideanLin_sub_sq_eq_of_normalEquations
    (hx : toEuclideanLin (Aᴴ * A) x = toEuclideanLin Aᴴ b) (y : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin A y - b‖ ^ 2 =
      ‖toEuclideanLin A x - b‖ ^ 2 + ‖toEuclideanLin A (y - x)‖ ^ 2 := by
  have hperp : (inner 𝕜 (toEuclideanLin A x - b) (toEuclideanLin A (y - x)) : 𝕜) = 0 := by
    rw [← toEuclideanLin_conjTranspose_inner_left, map_sub, ← toEuclideanLin_mul_apply, hx,
      sub_self, inner_zero_left]
  have hsplit : toEuclideanLin A y - b = (toEuclideanLin A x - b) + toEuclideanLin A (y - x) := by
    rw [map_sub]
    abel
  rw [hsplit, sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hperp, sq, sq]

/-- The pseudoinverse solves the normal equations: `Aᴴ A (A⁺ b) = Aᴴ b`. -/
theorem normalEquations_pinv (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m) :
    toEuclideanLin (Aᴴ * A) (toEuclideanLin A.pinv b) = toEuclideanLin Aᴴ b := by
  rw [← toEuclideanLin_mul_apply, Matrix.mul_assoc, conjTranspose_mul_mul_pinv]

/-- **The normal equations**, [quarteroni2000numerical] (3.74): `x` is a least-squares solution
of `A x = b` if and only if `Aᴴ A x = Aᴴ b`. Backwards, the Pythagorean identity; forwards, the
identity at the solution `A⁺ b` of the normal equations gives `‖A (x - A⁺ b)‖ = 0`, so
`A x = A A⁺ b` and `x` solves the normal equations too. -/
theorem isLeastSquaresSolution_iff_normalEquations :
    IsLeastSquaresSolution A b x ↔ toEuclideanLin (Aᴴ * A) x = toEuclideanLin Aᴴ b := by
  constructor
  · intro h
    have h1 := norm_toEuclideanLin_sub_sq_eq_of_normalEquations (normalEquations_pinv A b) x
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (h (toEuclideanLin A.pinv b)) 2
    have h3 : ‖toEuclideanLin A (x - toEuclideanLin A.pinv b)‖ ^ 2 = 0 :=
      le_antisymm (by linarith) (sq_nonneg _)
    rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero, map_sub, sub_eq_zero] at h3
    rw [toEuclideanLin_mul_apply, h3, ← toEuclideanLin_mul_apply, normalEquations_pinv]
  · intro hx y
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [norm_toEuclideanLin_sub_sq_eq_of_normalEquations hx y]
    exact le_add_of_nonneg_right (sq_nonneg _)

/-- The pseudoinverse gives a least-squares solution, for every right-hand side. -/
theorem isLeastSquaresSolution_pinv (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m) :
    IsLeastSquaresSolution A b (toEuclideanLin A.pinv b) :=
  isLeastSquaresSolution_iff_normalEquations.2 (normalEquations_pinv A b)

end NormalEquations

/-! ### Full column rank -/

section FullRank

variable {A : Matrix m n 𝕜}

omit [Fintype m] [DecidableEq n] in
/-- A matrix with linearly independent columns is injective on vectors. -/
theorem mulVec_injective_of_linearIndependent_transpose (hA : LinearIndependent 𝕜 Aᵀ) :
    Function.Injective A.mulVec :=
  mulVec_injective_iff.2 hA

omit [Fintype n] [DecidableEq n] in
/-- A matrix with linearly independent rows is injective on covectors. -/
theorem vecMul_injective_of_linearIndependent (hA : LinearIndependent 𝕜 A) :
    Function.Injective A.vecMul :=
  vecMul_injective_iff.2 hA

omit [Fintype n] [DecidableEq n] in
/-- [quarteroni2000numerical] §3.13: for a matrix of full column rank the Gram matrix `Aᴴ A` of
the normal equations is positive definite. -/
theorem posDef_conjTranspose_mul_self_of_linearIndependent [Finite n]
    (hA : LinearIndependent 𝕜 Aᵀ) : (Aᴴ * A).PosDef := by
  cases nonempty_fintype n
  exact PosDef.conjTranspose_mul_self A (mulVec_injective_of_linearIndependent_transpose hA)

omit [Fintype m] [DecidableEq n] in
/-- For a matrix of full row rank, `A Aᴴ` is positive definite. -/
theorem posDef_self_mul_conjTranspose_of_linearIndependent [Finite m]
    (hA : LinearIndependent 𝕜 A) : (A * Aᴴ).PosDef := by
  cases nonempty_fintype m
  exact PosDef.mul_conjTranspose_self A (vecMul_injective_of_linearIndependent hA)

/-- [quarteroni2000numerical] §3.13, after (3.74): for a matrix of full column rank the
least-squares solution exists and is unique, namely `(Aᴴ A)⁻¹ Aᴴ b`. -/
theorem existsUnique_isLeastSquaresSolution (hA : LinearIndependent 𝕜 Aᵀ)
    (b : EuclideanSpace 𝕜 m) : ∃! x, IsLeastSquaresSolution A b x := by
  classical
  have hG : IsUnit (Aᴴ * A) := (posDef_conjTranspose_mul_self_of_linearIndependent hA).isUnit
  refine ⟨toEuclideanLin ((Aᴴ * A)⁻¹ * Aᴴ) b, ?_, fun x hx => ?_⟩
  · dsimp only
    rw [isLeastSquaresSolution_iff_normalEquations, ← toEuclideanLin_mul_apply,
      ← Matrix.mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hG), Matrix.one_mul]
  · dsimp only at hx
    rw [isLeastSquaresSolution_iff_normalEquations] at hx
    rw [toEuclideanLin_mul_apply, ← hx, ← toEuclideanLin_mul_apply,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hG), toEuclideanLin_one, LinearMap.id_apply]

/-- For a matrix of full column rank the pseudoinverse is `(Aᴴ A)⁻¹ Aᴴ`: both satisfy the Penrose
conditions (`Matrix.pinv_unique`). -/
theorem pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose (hA : LinearIndependent 𝕜 Aᵀ) :
    A.pinv = (Aᴴ * A)⁻¹ * Aᴴ := by
  have hG : IsUnit (Aᴴ * A).det :=
    (isUnit_iff_isUnit_det _).1 (posDef_conjTranspose_mul_self_of_linearIndependent hA).isUnit
  have hleft : (Aᴴ * A)⁻¹ * Aᴴ * A = 1 := by
    rw [Matrix.mul_assoc, nonsing_inv_mul _ hG]
  have hH : ((Aᴴ * A)⁻¹).IsHermitian :=
    (isHermitian_conjTranspose_mul_self A).inv
  refine (pinv_unique A ?_ ?_ ?_ ?_).symm
  · rw [Matrix.mul_assoc, hleft, Matrix.mul_one]
  · rw [hleft, Matrix.one_mul]
  · rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH.eq,
      Matrix.mul_assoc]
  · rw [hleft]
    exact isHermitian_one

variable [DecidableEq m]

/-- For a matrix of full column rank, the least-squares solution is `A⁺ b`, and only it. -/
theorem isLeastSquaresSolution_iff_eq_pinv_of_linearIndependent (hA : LinearIndependent 𝕜 Aᵀ)
    {b : EuclideanSpace 𝕜 m} {x : EuclideanSpace 𝕜 n} :
    IsLeastSquaresSolution A b x ↔ x = toEuclideanLin A.pinv b := by
  obtain ⟨x₀, hx₀, huniq⟩ := existsUnique_isLeastSquaresSolution hA b
  have hp := huniq _ (isLeastSquaresSolution_pinv A b)
  exact ⟨fun hx => (huniq x hx).trans hp.symm, fun hx => hx ▸ isLeastSquaresSolution_pinv A b⟩

end FullRank

/-! ### The least-squares solution of least norm -/

section MinNorm

variable {A : Matrix m n 𝕜} {b : EuclideanSpace 𝕜 m} {x : EuclideanSpace 𝕜 n}

/-- **The least-squares solution of least norm**, [quarteroni2000numerical] (3.76): a
least-squares solution whose norm is at most that of every other one. -/
def IsMinNormLeastSquaresSolution (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m)
    (x : EuclideanSpace 𝕜 n) : Prop :=
  IsLeastSquaresSolution A b x ∧ ∀ y, IsLeastSquaresSolution A b y → ‖x‖ ≤ ‖y‖

variable [DecidableEq m]

/-- A least-squares solution differs from `A⁺ b` by an element of the kernel of `A`. -/
theorem toEuclideanLin_sub_pinv_eq_zero_of_normalEquations
    (hx : toEuclideanLin (Aᴴ * A) x = toEuclideanLin Aᴴ b) :
    toEuclideanLin A (x - toEuclideanLin A.pinv b) = 0 := by
  have hgram : toEuclideanLin (Aᴴ * A) (x - toEuclideanLin A.pinv b) = 0 := by
    rw [map_sub, hx, normalEquations_pinv, sub_self]
  have h := A.inner_toEuclideanLin_apply (x - toEuclideanLin A.pinv b)
    (x - toEuclideanLin A.pinv b)
  rw [hgram, inner_zero_right] at h
  exact inner_self_eq_zero.1 h

/-- `A⁺ b` is orthogonal to the kernel of `A`: it lies in the range of `A⁺ = A⁺ A A⁺`. -/
theorem inner_pinv_eq_zero_of_toEuclideanLin_eq_zero (b : EuclideanSpace 𝕜 m)
    {d : EuclideanSpace 𝕜 n} (hd : toEuclideanLin A d = 0) :
    (inner 𝕜 (toEuclideanLin A.pinv b) d : 𝕜) = 0 := by
  have hpp : toEuclideanLin (A.pinv * A) (toEuclideanLin A.pinv b) = toEuclideanLin A.pinv b := by
    rw [← toEuclideanLin_mul_apply, pinv_mul_self_mul_pinv]
  rw [← hpp, inner_toEuclideanLin_of_isHermitian A.isHermitian_pinv_mul,
    toEuclideanLin_mul_apply, hd, map_zero, inner_zero_right]

/-- **The Pythagorean identity of the minimal-norm solution**: for a solution `x` of the normal
equations, `‖x‖² = ‖A⁺ b‖² + ‖x - A⁺ b‖²`. -/
theorem norm_sq_eq_norm_pinv_sq_add_of_normalEquations
    (hx : toEuclideanLin (Aᴴ * A) x = toEuclideanLin Aᴴ b) :
    ‖x‖ ^ 2 = ‖toEuclideanLin A.pinv b‖ ^ 2 + ‖x - toEuclideanLin A.pinv b‖ ^ 2 := by
  have hxeq : toEuclideanLin A.pinv b + (x - toEuclideanLin A.pinv b) = x := by abel
  conv_lhs => rw [← hxeq]
  rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
    (inner_pinv_eq_zero_of_toEuclideanLin_eq_zero b
      (toEuclideanLin_sub_pinv_eq_zero_of_normalEquations hx)), sq, sq]

/-- **[quarteroni2000numerical] Theorem 3.9, existence**: `A⁺ b` is a least-squares solution of
least norm. -/
theorem isMinNormLeastSquaresSolution_pinv (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m) :
    IsMinNormLeastSquaresSolution A b (toEuclideanLin A.pinv b) :=
  ⟨isLeastSquaresSolution_pinv A b, fun _ hy =>
    norm_pinv_le_of_normalEquations A b (isLeastSquaresSolution_iff_normalEquations.1 hy)⟩

/-- **[quarteroni2000numerical] Theorem 3.9, uniqueness**: the least-squares solution of least
norm is `A⁺ b`. Minimality against `A⁺ b` gives `‖x‖ ≤ ‖A⁺ b‖`, and the Pythagorean identity
`‖x‖² = ‖A⁺ b‖² + ‖x - A⁺ b‖²` then forces `x = A⁺ b`. -/
theorem IsMinNormLeastSquaresSolution.eq_pinv (h : IsMinNormLeastSquaresSolution A b x) :
    x = toEuclideanLin A.pinv b := by
  have h1 := norm_sq_eq_norm_pinv_sq_add_of_normalEquations
    (isLeastSquaresSolution_iff_normalEquations.1 h.1)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (h.2 _ (isLeastSquaresSolution_pinv A b)) 2
  have h3 : ‖x - toEuclideanLin A.pinv b‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
  rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero, sub_eq_zero] at h3
  exact h3

omit [DecidableEq m] in
/-- A least-squares solution of least norm is unique. -/
theorem IsMinNormLeastSquaresSolution.unique {y : EuclideanSpace 𝕜 n}
    (hx : IsMinNormLeastSquaresSolution A b x) (hy : IsMinNormLeastSquaresSolution A b y) :
    x = y := by
  classical
  rw [hx.eq_pinv, hy.eq_pinv]

/-- **The underdetermined case** ([quarteroni2000numerical] §3.13, last paragraph): for a matrix
of full row rank, `A⁺ = Aᴴ (A Aᴴ)⁻¹`, so the solution of least norm of the (consistent) system
`A x = b` is `Aᴴ (A Aᴴ)⁻¹ b`. Both sides satisfy the Penrose conditions. -/
theorem pinv_eq_conjTranspose_mul_inv_self_mul_conjTranspose (hA : LinearIndependent 𝕜 A) :
    A.pinv = Aᴴ * (A * Aᴴ)⁻¹ := by
  have hG : IsUnit (A * Aᴴ).det :=
    (isUnit_iff_isUnit_det _).1 (posDef_self_mul_conjTranspose_of_linearIndependent hA).isUnit
  have hright : A * (Aᴴ * (A * Aᴴ)⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, mul_nonsing_inv _ hG]
  have hH : ((A * Aᴴ)⁻¹).IsHermitian := (isHermitian_mul_conjTranspose_self A).inv
  refine (pinv_unique A ?_ ?_ ?_ ?_).symm
  · rw [hright, Matrix.one_mul]
  · rw [Matrix.mul_assoc, hright, Matrix.mul_one]
  · rw [hright]
    exact isHermitian_one
  · rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH.eq,
      Matrix.mul_assoc]

/-- For a matrix of full row rank, `Aᴴ (A Aᴴ)⁻¹ b` solves `A x = b`: the system is consistent. -/
theorem toEuclideanLin_conjTranspose_mul_inv_self_mul_conjTranspose (hA : LinearIndependent 𝕜 A)
    (b : EuclideanSpace 𝕜 m) :
    toEuclideanLin A (toEuclideanLin (Aᴴ * (A * Aᴴ)⁻¹) b) = b := by
  have hG : IsUnit (A * Aᴴ).det :=
    (isUnit_iff_isUnit_det _).1 (posDef_self_mul_conjTranspose_of_linearIndependent hA).isUnit
  rw [← toEuclideanLin_mul_apply, ← Matrix.mul_assoc, mul_nonsing_inv _ hG, toEuclideanLin_one,
    LinearMap.id_apply]

end MinNorm

/-! ### The QR route -/

section QRSolve

variable {o : Type*} [Fintype o] [LinearOrder o] [DecidableEq m]

/-- **[quarteroni2000numerical] Theorem 3.8, (3.75)**: through any reduced QR factorization
`A = Q̃ R̃` with `Q̃ᴴ Q̃ = 1` and `R̃` upper triangular with nowhere-zero diagonal (in particular
the one of `Matrix.exists_isThinQR`), `x = R̃⁻¹ Q̃ᴴ b` is a least-squares solution of `A x = b`: it
solves the normal equations, `Aᴴ A x = R̃ᴴ Q̃ᴴ Q̃ R̃ R̃⁻¹ Q̃ᴴ b = R̃ᴴ Q̃ᴴ b = Aᴴ b`. -/
theorem isLeastSquaresSolution_of_qr {A Q : Matrix m o 𝕜} {R : Matrix o o 𝕜} (hA : A = Q * R)
    (hQ : Qᴴ * Q = 1) (hR : R.IsUpperTriangular) (hd : ∀ i, R i i ≠ 0) (b : EuclideanSpace 𝕜 m) :
    IsLeastSquaresSolution A b (toEuclideanLin (R⁻¹ * Qᴴ) b) := by
  have hRd : IsUnit R.det :=
    (isUnit_iff_isUnit_det R).1 (hR.isUnit_iff.2 hd)
  rw [isLeastSquaresSolution_iff_normalEquations, ← toEuclideanLin_mul_apply]
  have : Aᴴ * A * (R⁻¹ * Qᴴ) = Aᴴ := by
    rw [hA, conjTranspose_mul]
    calc Rᴴ * Qᴴ * (Q * R) * (R⁻¹ * Qᴴ) = Rᴴ * (Qᴴ * Q) * (R * R⁻¹) * Qᴴ := by
          simp only [Matrix.mul_assoc]
      _ = Rᴴ * Qᴴ := by rw [hQ, mul_nonsing_inv _ hRd, Matrix.mul_one, Matrix.mul_one]
  rw [this]

end QRSolve

/-! ### Least squares through a full QR factorization -/

section FullQR

variable {M N : ℕ} {A : Matrix (Fin M) (Fin N) 𝕜} {Q : Matrix (Fin M) (Fin M) 𝕜}
variable {R : Matrix (Fin M) (Fin N) 𝕜}

/-- **[quarteroni2000numerical] Theorem 3.8**, through a full QR factorization with `N ≤ M`: the
least-squares solution of `A x = b` is `R̃⁻¹ Q̃ᴴ b`, for `A` of full column rank. -/
theorem IsQR.isLeastSquaresSolution (h : IsQR A Q R) (hNM : N ≤ M) (hA : LinearIndependent 𝕜 Aᵀ)
    (b : EuclideanSpace 𝕜 (Fin M)) :
    IsLeastSquaresSolution A b
      (toEuclideanLin ((firstRows R hNM)⁻¹ * (firstColumns Q hNM)ᴴ) b) :=
  isLeastSquaresSolution_of_qr (h.firstColumns_mul_firstRows hNM).symm
    (h.conjTranspose_firstColumns_mul_self hNM) (h.isUpperTriangular_firstRows hNM)
    (h.firstRows_diag_ne_zero_of_linearIndependent hNM hA) b

/-- Through a full QR factorization the residual is `Q (R x - Qᴴ b)`, whose norm is
`‖R x - Qᴴ b‖`. -/
theorem IsQR.norm_sub_eq (h : IsQR A Q R) (b : EuclideanSpace 𝕜 (Fin M))
    (x : EuclideanSpace 𝕜 (Fin N)) :
    ‖toEuclideanLin A x - b‖ = ‖toEuclideanLin R x - toEuclideanLin Qᴴ b‖ := by
  have hQ : Q * Qᴴ = 1 := Unitary.mul_star_self_of_mem h.mem_unitaryGroup
  have : toEuclideanLin A x - b = toEuclideanLin Q (toEuclideanLin R x - toEuclideanLin Qᴴ b) := by
    rw [map_sub, ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, h.mul_eq, hQ,
      toEuclideanLin_one, LinearMap.id_apply]
  rw [this]
  exact norm_toEuclideanCLM_apply_of_mem_unitaryGroup h.mem_unitaryGroup _

/-- **[quarteroni2000numerical] Theorem 3.8, the display in its proof**: through a full QR
factorization with `N ≤ M`, for every `x`,
`‖A x - b‖² = ‖R̃ x - Q̃ᴴ b‖² + ∑_{i ≥ N} |(Qᴴ b)_i|²`. -/
theorem norm_sub_sq_eq_of_isQR (h : IsQR A Q R) (hNM : N ≤ M) (b : EuclideanSpace 𝕜 (Fin M))
    (x : EuclideanSpace 𝕜 (Fin N)) :
    ‖toEuclideanLin A x - b‖ ^ 2 =
      ‖toEuclideanLin (firstRows R hNM) x - toEuclideanLin (firstColumns Q hNM)ᴴ b‖ ^ 2 +
        ∑ i ∈ univ.filter (fun i : Fin M => N ≤ i), ‖(toEuclideanLin Qᴴ b) i‖ ^ 2 := by
  rw [h.norm_sub_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    ← Finset.sum_filter_add_sum_filter_not univ (fun i : Fin M => N ≤ i)
      (fun i => ‖(toEuclideanLin R x - toEuclideanLin Qᴴ b) i‖ ^ 2), add_comm]
  congr 1
  · -- the leading rows, reindexed by `Fin.castLE`
    symm
    refine Finset.sum_bij (fun (j : Fin N) _ => Fin.castLE hNM j) (fun j _ => ?_)
      (fun _ _ _ _ hk => Fin.castLE_injective hNM hk) (fun i hi => ?_) fun j _ => rfl
    · simp only [mem_filter, mem_univ, true_and, not_le, Fin.val_castLE]
      exact j.2
    · simp only [mem_filter, mem_univ, true_and, not_le] at hi
      exact ⟨⟨i, hi⟩, mem_univ _, Fin.ext rfl⟩
  · -- the trailing rows: `(R x) i = 0` for `N ≤ i`
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := (mem_filter.1 hi).2
    have hRx : (toEuclideanLin R x) i = 0 := by
      change (R *ᵥ WithLp.ofLp x) i = 0
      rw [mulVec, dotProduct]
      exact Finset.sum_eq_zero fun j _ => by rw [h.apply_eq_zero_of_le hi', zero_mul]
    rw [PiLp.sub_apply, hRx, zero_sub, norm_neg]

/-- **[quarteroni2000numerical] Theorem 3.8, the value of the minimum**: for `A` of full column
rank, the least-squares solution `x*` has residual `‖A x* - b‖² = ∑_{i ≥ N} |(Qᴴ b)_i|²`, since
`R̃ x* = Q̃ᴴ b`. -/
theorem norm_sub_sq_eq_of_isQR_of_isLeastSquaresSolution (h : IsQR A Q R) (hNM : N ≤ M)
    (hA : LinearIndependent 𝕜 Aᵀ) {b : EuclideanSpace 𝕜 (Fin M)} {x : EuclideanSpace 𝕜 (Fin N)}
    (hx : IsLeastSquaresSolution A b x) :
    ‖toEuclideanLin A x - b‖ ^ 2 =
      ∑ i ∈ univ.filter (fun i : Fin M => N ≤ i), ‖(toEuclideanLin Qᴴ b) i‖ ^ 2 := by
  rw [norm_sub_sq_eq_of_isQR h hNM]
  have hxs : x = toEuclideanLin ((firstRows R hNM)⁻¹ * (firstColumns Q hNM)ᴴ) b := by
    obtain ⟨x₀, -, huniq⟩ := existsUnique_isLeastSquaresSolution hA b
    exact (huniq x hx).trans (huniq _ (h.isLeastSquaresSolution hNM hA b)).symm
  have hR : IsUnit (firstRows R hNM).det :=
    (isUnit_iff_isUnit_det _).1 (h.isUnit_firstRows_of_linearIndependent hNM hA)
  rw [hxs, ← toEuclideanLin_mul_apply, ← Matrix.mul_assoc, mul_nonsing_inv _ hR, Matrix.one_mul,
    sub_self, norm_zero, zero_pow two_ne_zero, zero_add]

end FullQR

/-! ### More on the set of least-squares solutions -/

section Solutions

variable {A : Matrix m n 𝕜} {b : EuclideanSpace 𝕜 m} {x : EuclideanSpace 𝕜 n}

/-- **Two least-squares solutions differ by a null vector** ([golub2013matrix] §5.3.1): both
differ from `A⁺ b` by an element of the kernel
(`Matrix.toEuclideanLin_sub_pinv_eq_zero_of_normalEquations`). -/
theorem IsLeastSquaresSolution.toEuclideanLin_sub_eq_zero {y : EuclideanSpace 𝕜 n}
    (hx : IsLeastSquaresSolution A b x) (hy : IsLeastSquaresSolution A b y) :
    toEuclideanLin A (y - x) = 0 := by
  classical
  have h1 := toEuclideanLin_sub_pinv_eq_zero_of_normalEquations
    (isLeastSquaresSolution_iff_normalEquations.1 hx)
  have h2 := toEuclideanLin_sub_pinv_eq_zero_of_normalEquations
    (isLeastSquaresSolution_iff_normalEquations.1 hy)
  rw [map_sub] at h1 h2 ⊢
  rw [sub_eq_zero] at h1 h2
  rw [h1, h2, sub_self]

/-- **The least-squares solutions form a convex set** ([golub2013matrix] §5.5.1), indeed the
affine subspace of solutions of the normal equations. -/
theorem convex_setOf_isLeastSquaresSolution (A : Matrix m n 𝕜) (b : EuclideanSpace 𝕜 m) :
    Convex ℝ {x | IsLeastSquaresSolution A b x} := by
  classical
  intro x hx y hy a c ha hc hac
  simp only [Set.mem_ofPred_eq, isLeastSquaresSolution_iff_normalEquations] at hx hy ⊢
  rw [map_add, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, hx, hy, ← add_smul,
    hac, one_smul]

open scoped ComplexOrder in
/-- **The augmented system is nonsingular exactly for full column rank** ([golub2013matrix]
(5.3.20)): `det [1 A; Aᴴ 0] = (-1)^n det (Aᴴ A)`, and `Aᴴ A` is nonsingular iff the columns of `A`
are independent. -/
theorem isUnit_augmented_iff [DecidableEq m] (A : Matrix m n 𝕜) :
    IsUnit (fromBlocks 1 A Aᴴ 0) ↔ LinearIndependent 𝕜 Aᵀ := by
  rw [isUnit_iff_isUnit_det, det_fromBlocks_one₁₁, zero_sub, det_neg, IsUnit.mul_iff,
    ← isUnit_iff_isUnit_det]
  simp only [((isUnit_one.neg).pow _ : IsUnit ((-1 : 𝕜) ^ Fintype.card n)), true_and]
  constructor
  · intro h
    have hinj : Function.Injective A.mulVec := fun x y hxy => by
      have : (Aᴴ * A) *ᵥ x = (Aᴴ * A) *ᵥ y := by rw [← mulVec_mulVec, hxy, mulVec_mulVec]
      exact (mulVec_injective_iff_isUnit (A := Aᴴ * A)).2 h this
    exact mulVec_injective_iff.1 hinj
  · intro h
    exact (posDef_conjTranspose_mul_self_of_linearIndependent h).isUnit

/-- **A matrix with orthonormal columns gives the orthogonal projection onto its range**,
`V Vᴴ` ([golub2013matrix] §2.5.1): the case `V⁺ = Vᴴ` of `Matrix.mul_pinv_eq_starProjection`. -/
theorem toEuclideanLin_mul_conjTranspose_eq_starProjection {k : Type*} [Fintype k]
    [DecidableEq k] [DecidableEq m] {V : Matrix m k 𝕜} (hV : Vᴴ * V = 1) :
    toEuclideanLin (V * Vᴴ) = ((LinearMap.range (toEuclideanLin V)).starProjection :
      EuclideanSpace 𝕜 m →ₗ[𝕜] EuclideanSpace 𝕜 m) := by
  have hp : V.pinv = Vᴴ := by
    rw [pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit
      (by rw [hV]; exact isUnit_one), hV, inv_one, Matrix.one_mul]
  rw [← hp, mul_pinv_eq_starProjection]

omit [Fintype m] in
/-- The dimension of the range of `toEuclideanLin A` is the rank of `A`. -/
theorem finrank_range_toEuclideanLin [Finite m] (A : Matrix m n 𝕜) :
    Module.finrank 𝕜 (LinearMap.range (toEuclideanLin A)) = A.rank := by
  classical
  cases nonempty_fintype m
  rw [rank_eq_finrank_range_toLin A (EuclideanSpace.basisFun m 𝕜).toBasis
      (EuclideanSpace.basisFun n 𝕜).toBasis, ← toEuclideanLin_eq_toLin_orthonormal]

end Solutions

section Gradient

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] [DecidableEq m]

/-- **The gradient of the least-squares objective** ([golub2013matrix] §5.3.1): over `ℝ`, the
function `x ↦ ‖A x - b‖² / 2` has gradient `Aᵀ (A x - b)`, so the normal equations say that the
gradient vanishes. -/
theorem hasGradientAt_leastSquaresObjective (A : Matrix m n ℝ) (b : EuclideanSpace ℝ m)
    (x : EuclideanSpace ℝ n) :
    HasGradientAt (fun y => ‖toEuclideanLin A y - b‖ ^ 2 / 2)
      (toEuclideanLin Aᵀ (toEuclideanLin A x - b)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  set L := LinearMap.toContinuousLinearMap (toEuclideanLin A) with hL
  have hf : HasFDerivAt (fun y => toEuclideanLin A y - b) L x := L.hasFDerivAt.sub_const b
  have h1 : HasFDerivAt (fun y => ‖toEuclideanLin A y - b‖ ^ 2)
      (2 • (innerSL ℝ (toEuclideanLin A x - b)).comp L) x := hf.norm_sq
  have h2 := h1.mul_const (1 / 2 : ℝ)
  have hfun : (fun y => ‖toEuclideanLin A y - b‖ ^ 2 / 2)
      = fun y => ‖toEuclideanLin A y - b‖ ^ 2 * (1 / 2 : ℝ) := by
    funext y; ring
  rw [hfun]
  convert h2 using 1
  ext v
  have := toEuclideanLin_conjTranspose_inner_left A v (toEuclideanLin A x - b)
  rw [conjTranspose_eq_transpose_of_trivial] at this
  rw [InnerProductSpace.toDual_apply_apply, this]
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    hL, LinearMap.coe_toContinuousLinearMap', smul_eq_mul, nsmul_eq_mul]
  rw [real_inner_comm]
  ring

end Gradient

/-! ### The orthogonal complement of the range through a QR factorization -/

section RangeComplement

variable {M N : ℕ} {A : Matrix (Fin M) (Fin N) 𝕜} {Q : Matrix (Fin M) (Fin M) 𝕜}
  {R : Matrix (Fin M) (Fin N) 𝕜}

/-- **`ran(A)⊥` is spanned by the trailing columns of `Q`** ([golub2013matrix] Theorem 5.2.2): for
a full QR factorization of `A` with independent columns, the last `M - N` columns `q_i`
(`Matrix.lastColumns`) are orthogonal to the range (`Aᴴ q_i = Rᴴ e_i = 0`), and they are `M - N`
orthonormal vectors in a complement of dimension `M - N`. -/
theorem IsQR.range_orthogonal_eq_span_lastColumns (h : IsQR A Q R) (hNM : N ≤ M)
    (hA : LinearIndependent 𝕜 Aᵀ) :
    (LinearMap.range (toEuclideanLin A))ᗮ
      = Submodule.span 𝕜 (Set.range fun j : Fin (M - N) =>
          (WithLp.toLp 2 ((lastColumns Q (Nat.sub_le M N))ᵀ j) : EuclideanSpace 𝕜 (Fin M))) := by
  have hQ : Qᴴ * Q = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 h.mem_unitaryGroup
  have hq := orthonormal_toLp_transpose_of_conjTranspose_mul_self_eq_one hQ
  set e : Fin (M - N) → Fin M := fun j => ⟨M - (M - N) + j, by omega⟩ with he
  have he_inj : Function.Injective e := fun a b hab => by
    have := congrArg Fin.val hab
    simp only [he] at this
    exact Fin.ext (by omega)
  set T := Submodule.span 𝕜 (Set.range fun j : Fin (M - N) =>
    (WithLp.toLp 2 ((lastColumns Q (Nat.sub_le M N))ᵀ j) : EuclideanSpace 𝕜 (Fin M))) with hT
  have hle : T ≤ (LinearMap.range (toEuclideanLin A))ᗮ := by
    rw [hT, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal]
    rintro _ ⟨x, rfl⟩
    have hzero : toEuclideanLin Aᴴ (WithLp.toLp 2 (Qᵀ (e j))) = 0 := by
      rw [← h.mul_eq, conjTranspose_mul, toEuclideanLin_mul_apply]
      have hsingle : toEuclideanLin Qᴴ (WithLp.toLp 2 (Qᵀ (e j)))
          = WithLp.toLp 2 (Pi.single (e j) 1) := by
        rw [toEuclideanLin_toLp]
        congr 1
        have : Qᵀ (e j) = Q *ᵥ Pi.single (e j) 1 := by
          rw [mulVec_single_one]; rfl
        rw [this, mulVec_mulVec, hQ, one_mulVec]
      rw [hsingle, toEuclideanLin_toLp]
      ext l
      have hR := h.apply_eq_zero_of_le (show N ≤ (e j : ℕ) by simp only [he]; omega) l
      simp [hR]
    change inner 𝕜 (toEuclideanLin A x) (WithLp.toLp 2 (Qᵀ (e j)) : EuclideanSpace 𝕜 (Fin M)) = 0
    rw [← inner_conj_symm, ← toEuclideanLin_conjTranspose_inner_left, hzero, inner_zero_left,
      map_zero]
  have hrank : A.rank = N := by
    rw [rank_eq_finrank_span_cols]
    exact (finrank_span_eq_card hA).trans (Fintype.card_fin N)
  have h1 : Module.finrank 𝕜 (LinearMap.range (toEuclideanLin A))ᗮ = M - N := by
    have := (LinearMap.range (toEuclideanLin A)).finrank_add_finrank_orthogonal
    rw [finrank_range_toEuclideanLin, hrank, finrank_euclideanSpace_fin] at this
    omega
  have h2 : Module.finrank 𝕜 T = M - N := by
    rw [hT, show (fun j : Fin (M - N) => (WithLp.toLp 2 ((lastColumns Q (Nat.sub_le M N))ᵀ j) :
        EuclideanSpace 𝕜 (Fin M)))
        = (fun i => (WithLp.toLp 2 (Qᵀ i) : EuclideanSpace 𝕜 (Fin M))) ∘ e from rfl,
      finrank_span_eq_card (hq.comp _ he_inj).linearIndependent, Fintype.card_fin]
  exact (Submodule.eq_of_le_of_finrank_eq hle (h2.trans h1.symm)).symm

end RangeComplement

/-! ### Matrix least-squares problems -/

section Frobenius

open scoped Matrix.Norms.Frobenius

variable {p q : Type*} [Fintype p] [Fintype q]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **The pseudoinverse solves the matrix least-squares problem `min_X ‖A X - I‖_F` with least
Frobenius norm** ([golub2013matrix] (5.5.3), where `X` is `n × m`): `‖A A⁺ - I‖_F ≤ ‖A X - I‖_F`
for every `X`, and among the minimizers `A⁺` is the unique one of least Frobenius norm. Column
`j` of `X` is a least-squares problem with right-hand side `e_j`, whose minimal-norm solution is
`A⁺ e_j`. -/
theorem isMinOn_norm_mul_sub_one_pinv (A : Matrix m n 𝕜) :
    IsMinOn (fun X : Matrix n m 𝕜 => ‖A * X - 1‖) Set.univ A.pinv ∧
      ∀ X : Matrix n m 𝕜, ‖A * X - 1‖ = ‖A * A.pinv - 1‖ →
        ‖A.pinv‖ ≤ ‖X‖ ∧ (‖X‖ = ‖A.pinv‖ → X = A.pinv) := by
  set e : m → EuclideanSpace 𝕜 m := fun j => EuclideanSpace.single j 1 with he
  have hcol : ∀ (X : Matrix n m 𝕜) j,
      (WithLp.toLp 2 fun i => (A * X - 1 : Matrix m m 𝕜) i j : EuclideanSpace 𝕜 m)
        = toEuclideanLin A (WithLp.toLp 2 fun i => X i j) - e j := by
    intro X j
    ext i
    simp [he, mulVec, dotProduct, mul_apply, one_apply, eq_comm]
  have hpinv : ∀ j, (WithLp.toLp 2 fun i => A.pinv i j : EuclideanSpace 𝕜 n)
      = toEuclideanLin A.pinv (e j) := by
    intro j
    ext i
    simp [he, mulVec, dotProduct, Pi.single_apply]
  have hsq : ∀ X : Matrix n m 𝕜, ‖A * X - 1‖ ^ 2
      = ∑ j, ‖toEuclideanLin A (WithLp.toLp 2 fun i => X i j) - e j‖ ^ 2 := fun X => by
    rw [frobenius_norm_sq_eq_sum_norm_sq_col]
    exact Finset.sum_congr rfl fun j _ => by rw [hcol]
  have hterm : ∀ (X : Matrix n m 𝕜) j,
      ‖toEuclideanLin A (WithLp.toLp 2 fun i => A.pinv i j) - e j‖ ^ 2
        ≤ ‖toEuclideanLin A (WithLp.toLp 2 fun i => X i j) - e j‖ ^ 2 := fun X j => by
    rw [hpinv]
    exact pow_le_pow_left₀ (norm_nonneg _) (A.norm_toEuclideanLin_pinv_sub_le _ _) 2
  have hmin : ∀ X : Matrix n m 𝕜, ‖A * A.pinv - 1‖ ≤ ‖A * X - 1‖ := fun X => by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [hsq, hsq]
    exact Finset.sum_le_sum fun j _ => hterm X j
  refine ⟨isMinOn_univ_iff.2 hmin, fun X hX => ?_⟩
  -- every column of a minimizer is a least-squares solution
  have hls : ∀ j, IsLeastSquaresSolution A (e j) (WithLp.toLp 2 fun i => X i j) := by
    have heq : ∑ j, ‖toEuclideanLin A (WithLp.toLp 2 fun i => A.pinv i j) - e j‖ ^ 2
        = ∑ j, ‖toEuclideanLin A (WithLp.toLp 2 fun i => X i j) - e j‖ ^ 2 := by
      rw [← hsq, ← hsq, hX]
    have hj := (Finset.sum_eq_sum_iff_of_le fun j _ => hterm X j).1 heq
    intro j y
    have h1 := hj j (Finset.mem_univ _)
    rw [hpinv] at h1
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (A.norm_toEuclideanLin_pinv_sub_le (e j) y) 2
    rw [h1] at h2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  have hnorm : ∀ j, ‖toEuclideanLin A.pinv (e j)‖ ≤ ‖(WithLp.toLp 2 fun i => X i j :
      EuclideanSpace 𝕜 n)‖ := fun j =>
    A.norm_pinv_le_of_normalEquations _ (isLeastSquaresSolution_iff_normalEquations.1 (hls j))
  have hnormsq : ∀ Y : Matrix n m 𝕜, ‖Y‖ ^ 2
      = ∑ j, ‖(WithLp.toLp 2 fun i => Y i j : EuclideanSpace 𝕜 n)‖ ^ 2 :=
    frobenius_norm_sq_eq_sum_norm_sq_col
  have hle : ∀ j ∈ (Finset.univ : Finset m),
      ‖(WithLp.toLp 2 fun i => A.pinv i j : EuclideanSpace 𝕜 n)‖ ^ 2
        ≤ ‖(WithLp.toLp 2 fun i => X i j : EuclideanSpace 𝕜 n)‖ ^ 2 := fun j _ => by
    rw [hpinv]; exact pow_le_pow_left₀ (norm_nonneg _) (hnorm j) 2
  refine ⟨(pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_, fun hXn => ?_⟩
  · rw [hnormsq, hnormsq]
    exact Finset.sum_le_sum hle
  · have heq : ∑ j, ‖(WithLp.toLp 2 fun i => A.pinv i j : EuclideanSpace 𝕜 n)‖ ^ 2
        = ∑ j, ‖(WithLp.toLp 2 fun i => X i j : EuclideanSpace 𝕜 n)‖ ^ 2 := by
      rw [← hnormsq, ← hnormsq, hXn]
    have hj := (Finset.sum_eq_sum_iff_of_le hle).1 heq
    ext i j
    have hmn : IsMinNormLeastSquaresSolution A (e j) (WithLp.toLp 2 fun i => X i j) := by
      refine ⟨hls j, fun y hy => ?_⟩
      have h1 := hj j (Finset.mem_univ _)
      rw [hpinv] at h1
      have h2 := A.norm_pinv_le_of_normalEquations _
        (isLeastSquaresSolution_iff_normalEquations.1 hy)
      have h3 := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
      rw [← h3]
      exact h2
    have h := congrArg (fun w : EuclideanSpace 𝕜 n => w i) hmn.eq_pinv
    rw [← hpinv] at h
    simpa using h

end Frobenius

section MatrixUnknown

open scoped Matrix.Norms.Frobenius

variable {r : Type*} [Fintype r] [DecidableEq r]

omit [Fintype m] [Fintype r] [DecidableEq r] in
/-- The rows of `A - F Kᴴ` are the residuals `a_i - K̄ f_i`, with `K̄ = K.map star`. -/
private theorem toLp_sub_mul_conjTranspose_row (A : Matrix m r 𝕜) (K : Matrix r n 𝕜)
    (F : Matrix m n 𝕜) (i : m) :
    (WithLp.toLp 2 ((A - F * Kᴴ) i) : EuclideanSpace 𝕜 r)
      = -(toEuclideanLin (K.map star) (WithLp.toLp 2 (F i)) - WithLp.toLp 2 (A i)) := by
  classical
  rw [neg_sub, toEuclideanLin_toLp]
  congr 1
  funext j
  simp only [sub_apply, mul_apply, conjTranspose_apply, Pi.sub_apply]
  congr 1
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

omit [DecidableEq r] in
/-- The squared Frobenius residual splits into row least-squares residuals. -/
private theorem norm_sub_mul_conjTranspose_sq (A : Matrix m r 𝕜) (K : Matrix r n 𝕜)
    (F : Matrix m n 𝕜) :
    ‖A - F * Kᴴ‖ ^ 2 = ∑ i, ‖toEuclideanLin (K.map star) (WithLp.toLp 2 (F i))
      - WithLp.toLp 2 (A i)‖ ^ 2 := by
  classical
  rw [frobenius_norm_sq_eq_sum_norm_sq_row]
  exact Finset.sum_congr rfl fun i _ => by rw [toLp_sub_mul_conjTranspose_row, norm_neg]

omit [DecidableEq n] [DecidableEq r] in
/-- **Least squares with a matrix unknown on the left** (the normal equations of one CP-ALS update,
[golub2013matrix] (12.5.16)–(12.5.20)): `F` minimizes `F ↦ ‖A - F Kᴴ‖_F` iff
`F (Kᴴ K) = A K`. Row by row, `‖A - F Kᴴ‖_F² = ∑_i ‖K̄ f_i - a_i‖²` with `K̄ = K.map star`, and each
row is an ordinary least-squares problem (`Matrix.isLeastSquaresSolution_iff_normalEquations`);
a row that is not optimal can be replaced alone. -/
theorem isMinOn_norm_sub_mul_conjTranspose_iff (A : Matrix m r 𝕜)
    (K : Matrix r n 𝕜) (F : Matrix m n 𝕜) :
    IsMinOn (fun G : Matrix m n 𝕜 => ‖A - G * Kᴴ‖) Set.univ F ↔ F * (Kᴴ * K) = A * K := by
  classical
  rw [isMinOn_univ_iff]
  set Kb : Matrix r n 𝕜 := K.map star with hKb
  have hrow : ∀ i, IsLeastSquaresSolution Kb (WithLp.toLp 2 (A i)) (WithLp.toLp 2 (F i)) ↔
      (F * (Kᴴ * K)) i = (A * K) i := by
    intro i
    rw [isLeastSquaresSolution_iff_normalEquations]
    simp only [toEuclideanLin_toLp]
    rw [(WithLp.toLp_injective 2).eq_iff]
    have h1 : Kbᴴ * Kb = (Kᴴ * K)ᵀ := by
      rw [hKb, transpose_mul]
      ext a c
      simp [mul_apply, conjTranspose_apply]
    have h2 : Kbᴴ = Kᵀ := by ext a c; simp [hKb]
    rw [h1, h2, mulVec_transpose, mulVec_transpose]
    constructor <;> intro h <;> funext j <;>
      simpa [vecMul, dotProduct, mul_apply] using congrFun h j
  have hsum := norm_sub_mul_conjTranspose_sq A K
  constructor
  · intro h
    ext i
    refine congrFun ((hrow i).1 fun y => ?_) _
    by_contra hlt
    push Not at hlt
    set G := F.updateRow i (WithLp.ofLp y) with hG
    have hGF : ∀ j, j ≠ i → G j = F j := fun j hj => updateRow_ne hj
    have hGi : G i = WithLp.ofLp y := updateRow_self
    have hlt2 := h G
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hlt2 2
    rw [hsum, hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsq
    have heq : ∑ j ∈ Finset.univ.erase i, ‖toEuclideanLin Kb (WithLp.toLp 2 (G j))
        - WithLp.toLp 2 (A j)‖ ^ 2 = ∑ j ∈ Finset.univ.erase i,
        ‖toEuclideanLin Kb (WithLp.toLp 2 (F j)) - WithLp.toLp 2 (A j)‖ ^ 2 :=
      Finset.sum_congr rfl fun j hj => by rw [hGF j (Finset.ne_of_mem_erase hj)]
    rw [heq, hGi, WithLp.toLp_ofLp] at hsq
    have := pow_lt_pow_left₀ hlt (norm_nonneg _) two_ne_zero
    linarith
  · intro h G
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [hsum, hsum]
    refine Finset.sum_le_sum fun i _ => ?_
    exact pow_le_pow_left₀ (norm_nonneg _) (((hrow i).2 (congrFun h i)) _) 2

omit [DecidableEq n] [DecidableEq r] [Fintype m] in
/-- **The matrix least-squares problem `min_F ‖A - F Kᴴ‖_F` has a solution**: row `i` of `F` is
`K̄⁺ a_i`, the pseudoinverse solution of its row problem. -/
theorem exists_mul_conjTranspose_mul_self_eq [Finite m] (A : Matrix m r 𝕜)
    (K : Matrix r n 𝕜) : ∃ F : Matrix m n 𝕜, F * (Kᴴ * K) = A * K := by
  classical
  cases nonempty_fintype m
  refine ⟨Matrix.of fun i => WithLp.ofLp (toEuclideanLin (K.map star).pinv
    (WithLp.toLp 2 (A i))), ?_⟩
  refine (isMinOn_norm_sub_mul_conjTranspose_iff A K _).1 (isMinOn_univ_iff.2 fun G => ?_)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [norm_sub_mul_conjTranspose_sq A K, norm_sub_mul_conjTranspose_sq A K]
  refine Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  exact
    isLeastSquaresSolution_pinv (K.map star) (WithLp.toLp 2 (A i)) (WithLp.toLp 2 (G i))

end MatrixUnknown

/-! ### Underdetermined systems through a QR factorization of `Aᴴ` -/

section ThinQR

variable {N : ℕ} [DecidableEq m]

/-- **Minimal-norm solutions of a full-row-rank system through a QR factorization of `Aᴴ`**
([golub2013matrix] §5.6.2, Algorithm 5.6.2): if `Aᴴ = Q R` is a thin QR factorization with `R`
nonsingular, then `A⁺ = Q (Rᴴ)⁻¹`, so `x = Q (Rᴴ)⁻¹ b` is the minimal-norm solution of `A x = b`
(`Matrix.isMinNormLeastSquaresSolution_pinv`). With `A = Rᴴ Qᴴ`, `A (Q (Rᴴ)⁻¹) = 1` and
`Q (Rᴴ)⁻¹ A = Q Qᴴ`, so the four Penrose conditions hold. -/
theorem pinv_eq_of_isThinQR_conjTranspose {A : Matrix (Fin N) m 𝕜} {Q : Matrix m (Fin N) 𝕜}
    {R : Matrix (Fin N) (Fin N) 𝕜} (h : IsThinQR Aᴴ Q R) (hR : IsUnit R) :
    A.pinv = Q * (Rᴴ)⁻¹ := by
  have hA : A = Rᴴ * Qᴴ := by
    rw [← conjTranspose_mul, h.mul_eq, conjTranspose_conjTranspose]
  have hRd : IsUnit Rᴴ.det := by
    rw [det_conjTranspose]
    exact ((isUnit_iff_isUnit_det R).1 hR).star
  have hAB : A * (Q * (Rᴴ)⁻¹) = 1 := by
    rw [hA, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ, h.conjTranspose_mul_self, Matrix.one_mul,
      mul_nonsing_inv _ hRd]
  have hBA : Q * (Rᴴ)⁻¹ * A = Q * Qᴴ := by
    rw [hA, Matrix.mul_assoc, ← Matrix.mul_assoc (Rᴴ)⁻¹, nonsing_inv_mul _ hRd, Matrix.one_mul]
  refine (pinv_unique A ?_ ?_ ?_ ?_).symm
  · rw [hAB, Matrix.one_mul]
  · rw [Matrix.mul_assoc, hAB, Matrix.mul_one]
  · rw [hAB]; exact isHermitian_one
  · rw [hBA, IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]

end ThinQR

end Matrix
