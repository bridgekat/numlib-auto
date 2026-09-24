/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.LeastSquares`, beside the pseudoinverse of
`Numlib/LinearAlgebra/Matrix/SVD`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.Block
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

## Implementation notes

Vectors are `EuclideanSpace 𝕜 m`, never `m → 𝕜`, because the norm is the point; the
`Matrix.toEuclideanLin_*` glue of `Numlib/Analysis/Matrix/ToEuclideanLin` moves between the two.
The index types are arbitrary `Fintype`s wherever the statement makes sense; `Fin M`, `Fin N` enter
only with the *full* QR factorization `Matrix.IsQR` of `Numlib/LinearAlgebra/Matrix/QR`, whose
reduced factors are the first `N` columns and rows.

## References

* [quarteroni2000numerical] §3.4.3, §3.13.
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
the one of `Matrix.exists_qr`), `x = R̃⁻¹ Q̃ᴴ b` is a least-squares solution of `A x = b`: it solves
the normal equations, `Aᴴ A x = R̃ᴴ Q̃ᴴ Q̃ R̃ R̃⁻¹ Q̃ᴴ b = R̃ᴴ Q̃ᴴ b = Aᴴ b`. -/
theorem isLeastSquaresSolution_of_qr {A Q : Matrix m o 𝕜} {R : Matrix o o 𝕜} (hA : A = Q * R)
    (hQ : Qᴴ * Q = 1) (hR : R.IsUpperTriangular) (hd : ∀ i, R i i ≠ 0) (b : EuclideanSpace 𝕜 m) :
    IsLeastSquaresSolution A b (toEuclideanLin (R⁻¹ * Qᴴ) b) := by
  have hRd : IsUnit R.det :=
    (isUnit_iff_isUnit_det R).1 ((isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hR).2 hd)
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

end Matrix
