/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Hermitian`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Matrix.ToEuclideanLin

/-!
# The Hermitian part of a matrix

Every square matrix over `ℂ` splits as `A = H + i S` with `H = (A + Aᴴ)/2` and `S = (A - Aᴴ)/(2i)`
both Hermitian: `H` is the **Hermitian part** of `A` and `i S = (A - Aᴴ)/2` its skew-Hermitian
part. The decomposition is the one of Quarteroni–Sacco–Saleri, *Numerical Mathematics*, Theorem
5.1 (Hirsch's and Bendixson's eigenvalue bounds, which locate the spectrum of `A` in the rectangle
spanned by the extreme eigenvalues of `H` and of `S`), and equation (1.49) of Saad, *Iterative
Methods for Sparse Linear Systems*, §1.11.

## Main definitions

* `Matrix.hermitianPart A`: `H = (A + Aᴴ)/2`, over any `RCLike` field.
* `Matrix.skewHermitianPart A`: Saad's `S = (A - Aᴴ)/(2i)`, over `ℂ`.

## Main results

* `Matrix.hermitianPart_isHermitian`, `Matrix.skewHermitianPart_isHermitian`: both parts are
  Hermitian.
* `Matrix.eq_hermitianPart_add_I_smul_skewHermitianPart`: `A = H + i S`.
* `Matrix.skewHermitianPart_eq_hermitianPart`: `S` is the Hermitian part of `-i A`, which is how
  every statement about `S` reduces to one about `H`.
* `Matrix.re_inner_hermitianPart`: `re ⟪H x, x⟫ = re ⟪A x, x⟫` — the quadratic form of `A` sees
  only its Hermitian part — and `Matrix.mulVec_dotProduct_eq_hermitianPart`, the same identity
  for a real matrix and the dot product; `Matrix.star_dotProduct_hermitianPart_mulVec`,
  `xᴴ H x = re (xᴴ A x)`, and with it
  `Matrix.posDef_hermitianPart_iff_forall_dotProduct_mulVec_pos`, the unsymmetric "positive
  definite" of [golub2013matrix] §4.2 read through `H`.
* `Matrix.hermitianPart_conjTranspose_mul_mul`: the Hermitian part commutes with congruence, and
  `Matrix.l2_opNorm_hermitianPart_le`: `‖H‖₂ ≤ ‖A‖₂` ([golub2013matrix] §4.2.2).

## Implementation notes

The operator-level twin is the unbundled `½ (A + A†)` of
`ContinuousLinearMap.re_inner_hermitianPart_apply` and
`ContinuousLinearMap.isCoerciveWith_iff_hermitianPart` in
`Numlib/Analysis/InnerProductSpace/Coercive`; `Matrix.re_inner_hermitianPart` is that identity
read through `Matrix.toEuclideanLin`.

`skewHermitianPart` is stated over `ℂ` only: over a general `RCLike 𝕜` the imaginary unit may be
`0`, and the division by `2i` is then meaningless.
-/

open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*}

/-- The **Hermitian part** `H = (A + Aᴴ)/2` of a square matrix. -/
noncomputable def hermitianPart (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  (2⁻¹ : 𝕜) • (A + Aᴴ)

/-- The matrix `S = (A - Aᴴ)/(2i)`, so that `A = H + iS` with `H` the Hermitian part of `A`: `i S`
is the skew-Hermitian part `(A - Aᴴ)/2` of `A`, and `S` itself is Hermitian. Over `ℝ` the division
by `2i` is meaningless, so this is stated over `ℂ` only. -/
noncomputable def skewHermitianPart (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 * Complex.I)⁻¹ • (A - Aᴴ)

@[simp]
theorem hermitianPart_apply (A : Matrix n n 𝕜) (i j : n) :
    hermitianPart A i j = (2⁻¹ : 𝕜) * (A i j + starRingEnd 𝕜 (A j i)) := rfl

@[simp]
theorem skewHermitianPart_apply (A : Matrix n n ℂ) (i j : n) :
    skewHermitianPart A i j = (2 * Complex.I)⁻¹ * (A i j - starRingEnd ℂ (A j i)) := rfl

/-- The Hermitian part is Hermitian. -/
theorem hermitianPart_isHermitian (A : Matrix n n 𝕜) : (hermitianPart A).IsHermitian := by
  change ((2⁻¹ : 𝕜) • (A + Aᴴ))ᴴ = (2⁻¹ : 𝕜) • (A + Aᴴ)
  rw [conjTranspose_smul, show star (2⁻¹ : 𝕜) = 2⁻¹ by simp, conjTranspose_add,
    conjTranspose_conjTranspose, add_comm Aᴴ A]

/-- `S = (A - Aᴴ)/(2i)` is the Hermitian part of `-i A`. -/
theorem skewHermitianPart_eq_hermitianPart (A : Matrix n n ℂ) :
    skewHermitianPart A = hermitianPart ((-Complex.I) • A) := by
  ext i j
  simp only [skewHermitianPart_apply, hermitianPart_apply, smul_apply, smul_eq_mul, map_mul,
    map_neg, Complex.conj_I, neg_neg]
  rw [mul_inv, Complex.inv_I]
  ring

/-- The Hermitian part of `-i A` is `S = (A - Aᴴ)/(2i)`. -/
theorem hermitianPart_neg_I_smul (A : Matrix n n ℂ) :
    hermitianPart ((-Complex.I) • A) = skewHermitianPart A :=
  (skewHermitianPart_eq_hermitianPart A).symm

/-- `S = (A - Aᴴ)/(2i)` is Hermitian. -/
theorem skewHermitianPart_isHermitian (A : Matrix n n ℂ) : (skewHermitianPart A).IsHermitian := by
  rw [skewHermitianPart_eq_hermitianPart]
  exact hermitianPart_isHermitian _

/-- `i S = (A - Aᴴ)/2` is the skew-Hermitian part of `A`. -/
theorem I_smul_skewHermitianPart (A : Matrix n n ℂ) :
    Complex.I • skewHermitianPart A = (2⁻¹ : ℂ) • (A - Aᴴ) := by
  rw [skewHermitianPart, smul_smul]
  congr 1
  rw [mul_inv, ← mul_assoc, mul_comm Complex.I (2⁻¹ : ℂ), mul_assoc,
    mul_inv_cancel₀ Complex.I_ne_zero, mul_one]

/-- **The Hermitian decomposition** `A = H + iS` of a complex matrix. -/
theorem eq_hermitianPart_add_I_smul_skewHermitianPart (A : Matrix n n ℂ) :
    A = hermitianPart A + Complex.I • skewHermitianPart A := by
  rw [I_smul_skewHermitianPart, hermitianPart, ← smul_add,
    show A + Aᴴ + (A - Aᴴ) = (2 : ℂ) • A by module, smul_smul,
    inv_mul_cancel₀ (two_ne_zero' ℂ), one_smul]

variable [Fintype n]

/-- For a real matrix `A` and a real vector `u`, `(A u, u) = (H u, u)`: the quadratic form of `A`
is that of its symmetric part. -/
theorem mulVec_dotProduct_eq_hermitianPart (A : Matrix n n ℝ) (u : n → ℝ) :
    (A *ᵥ u) ⬝ᵥ u = (hermitianPart A *ᵥ u) ⬝ᵥ u := by
  have hT : (Aᵀ *ᵥ u) ⬝ᵥ u = (A *ᵥ u) ⬝ᵥ u := by
    rw [dotProduct_comm, dotProduct_mulVec, vecMul_transpose]
  have hH : hermitianPart A = (2⁻¹ : ℝ) • (A + Aᵀ) := by
    ext i j; simp [hermitianPart_apply]
  rw [hH, smul_mulVec, smul_dotProduct, add_mulVec, add_dotProduct, hT, smul_eq_mul]
  ring

variable [DecidableEq n]

/-- The real part of the quadratic form of `A` is that of its Hermitian part; the matrix form of
`ContinuousLinearMap.re_inner_hermitianPart_apply`. -/
theorem re_inner_hermitianPart (A : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    RCLike.re (inner 𝕜 (toEuclideanLin (hermitianPart A) x) x)
      = RCLike.re (inner 𝕜 (toEuclideanLin A x) x) := by
  have hH : toEuclideanLin (hermitianPart A) =
      (2⁻¹ : 𝕜) • (toEuclideanLin A + LinearMap.adjoint (toEuclideanLin A)) := by
    rw [hermitianPart, map_smul, map_add, toEuclideanLin_conjTranspose]
  have hadj : inner 𝕜 (LinearMap.adjoint (toEuclideanLin A) x) x
      = starRingEnd 𝕜 (inner 𝕜 (toEuclideanLin A x) x) := by
    rw [LinearMap.adjoint_inner_left, inner_conj_symm]
  have key : inner 𝕜 (toEuclideanLin (hermitianPart A) x) x
      = (2⁻¹ : 𝕜) * (inner 𝕜 (toEuclideanLin A x) x
        + starRingEnd 𝕜 (inner 𝕜 (toEuclideanLin A x) x)) := by
    rw [hH]
    simp only [LinearMap.smul_apply, LinearMap.add_apply, inner_smul_left, inner_add_left, hadj,
      map_inv₀, RCLike.conj_ofNat]
  rw [key, RCLike.add_conj, ← mul_assoc, show (2⁻¹ : 𝕜) * 2 = 1 by norm_num, one_mul,
    RCLike.ofReal_re]

/-! ### Congruence, definiteness and the spectral norm -/

omit [DecidableEq n] in
/-- The Hermitian part of a congruence is the congruence of the Hermitian part:
`hermitianPart (Xᴴ A X) = Xᴴ (hermitianPart A) X` for a rectangular `X`. -/
theorem hermitianPart_conjTranspose_mul_mul {k : Type*} (X : Matrix n k 𝕜)
    (A : Matrix n n 𝕜) : hermitianPart (Xᴴ * A * X) = Xᴴ * hermitianPart A * X := by
  simp only [hermitianPart, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]


omit [DecidableEq n] in
/-- The quadratic form of the Hermitian part is the real part of that of `A`:
`xᴴ H x = re (xᴴ A x)`. -/
theorem star_dotProduct_hermitianPart_mulVec (A : Matrix n n 𝕜) (x : n → 𝕜) :
    star x ⬝ᵥ (hermitianPart A *ᵥ x) = (RCLike.re (star x ⬝ᵥ (A *ᵥ x)) : 𝕜) := by
  have h : starRingEnd 𝕜 (star x ⬝ᵥ (A *ᵥ x)) = star x ⬝ᵥ (Aᴴ *ᵥ x) := by
    rw [starRingEnd_apply, star_dotProduct, star_star, star_mulVec, ← dotProduct_mulVec]
  rw [hermitianPart, smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, ← h,
    RCLike.add_conj, smul_eq_mul, ← mul_assoc, show (2⁻¹ : 𝕜) * 2 = 1 by norm_num, one_mul]

omit [DecidableEq n] in
/-- **Positive definiteness of the Hermitian part** is positivity of the real part of the
quadratic form: `(hermitianPart A).PosDef ↔ ∀ x ≠ 0, 0 < re (xᴴ A x)`. Over `ℝ` it reads
`∀ x ≠ 0, 0 < xᵀ A x`, the unsymmetric "positive definite" of [golub2013matrix] §4.2. -/
theorem posDef_hermitianPart_iff_forall_dotProduct_mulVec_pos (A : Matrix n n 𝕜) :
    (hermitianPart A).PosDef ↔ ∀ x : n → 𝕜, x ≠ 0 → 0 < RCLike.re (star x ⬝ᵥ (A *ᵥ x)) := by
  rw [posDef_iff_dotProduct_mulVec]
  simp only [hermitianPart_isHermitian, true_and, star_dotProduct_hermitianPart_mulVec,
    RCLike.ofReal_pos]

open scoped Matrix.Norms.L2Operator in
/-- The spectral norm of the Hermitian part is at most that of the matrix ([golub2013matrix]
§4.2.2): `‖(A + Aᴴ)/2‖₂ ≤ (‖A‖₂ + ‖Aᴴ‖₂)/2 = ‖A‖₂`. -/
theorem l2_opNorm_hermitianPart_le (A : Matrix n n 𝕜) :
    ‖hermitianPart A‖ ≤ ‖A‖ := by
  rw [hermitianPart, norm_smul, norm_inv, RCLike.norm_ofNat]
  calc 2⁻¹ * ‖A + Aᴴ‖ ≤ 2⁻¹ * (‖A‖ + ‖Aᴴ‖) := by gcongr; exact norm_add_le _ _
    _ = ‖A‖ := by rw [l2_opNorm_conjTranspose]; ring

end Matrix
