import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.PosDef
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.Schur

/-!
# Matrix pencils and the generalized eigenvalue problem

A **matrix pencil** `(A, B)` is the family `A - z B`; the **generalized eigenvalue problem** asks
for `λ` and `x ≠ 0` with `A x = λ B x` ([quarteroni2000numerical] §5.9, display (5.58);
[golub1989matrix] §7.7; [saad2011numerical] Ch. 9). The pencil with `B = 1` is the standard
eigenvalue problem, and the pencil `(A, P)` with `P` a preconditioner is what the spectrum of the
preconditioned matrix `P⁻¹ A` is really about ([quarteroni2000numerical] Remark 4.2).

## Main definitions

* `Matrix.pencilPoly A B`: the characteristic polynomial `det (A - X B)` of the pencil, over any
  commutative ring.
* `Matrix.IsRegularPencil A B`: the pencil is *regular* when its characteristic polynomial is not
  identically zero; otherwise it is *singular*, and every scalar is then an eigenvalue.
* `Matrix.pencilInftyMultiplicity A B`: the multiplicity `card n - natDegree (pencilPoly A B)` of
  the eigenvalue `∞` of a regular pencil, zero exactly when `B` is invertible.
* `Matrix.pencilSpectrum A B`: the finite eigenvalues `{μ | det (A - μ B) = 0}`, over a field.
* `Matrix.HasPencilEigenvector A B μ x`: the eigenpair `x ≠ 0`, `A x = μ B x`.

## Main results

* `Matrix.mem_pencilSpectrum_iff_exists`, `Matrix.mem_pencilSpectrum_iff_isRoot`: the spectrum is
  the set of eigenvalues with an eigenvector, and the root set of the characteristic polynomial.
* `Matrix.pencilSpectrum_one` and `Matrix.pencilSpectrum_eq_spectrum_of_isUnit`: the reductions to
  the standard problem, `σ(A, 1) = σ(A)` and `σ(A, B) = σ(B⁻¹ A)` for invertible `B`.
* `Matrix.natDegree_pencilPoly_eq_card_iff`: a pencil has `n` finite eigenvalues exactly when `B`
  is invertible, [quarteroni2000numerical] §5.9.1.
* `Matrix.exists_unitary_pencil_isUpperTriangular`: the **generalized Schur decomposition**
  ([quarteroni2000numerical] Property 5.10; [golub1989matrix] Theorem 7.7.1) — a regular pencil
  over an algebraically closed `RCLike` field is simultaneously triangularized by two unitary
  matrices, `Uᴴ A Z = T` and `Uᴴ B Z = S`; its eigenvalues are then the ratios `t_ii / s_ii` with
  `s_ii ≠ 0` (`Matrix.pencilSpectrum_eq_of_isUpperTriangular`).
* `Matrix.exists_simultaneous_diagonalization`: a **symmetric-definite pencil** — `A` Hermitian,
  `B` positive definite — is simultaneously diagonalized by an invertible congruence, `Mᴴ B M = 1`
  and `Mᴴ A M` real diagonal, whose diagonal is the spectrum of the pencil
  ([quarteroni2000numerical] Theorem 5.7). Its eigenvalues are therefore real
  (`Matrix.pencilSpectrum_subset_range_ofReal_of_posDef`), positive when `A` is positive definite
  too (`Matrix.re_pos_of_mem_pencilSpectrum_of_posDef`), and the columns of `M` are
  `B`-orthonormal eigenvectors (`Matrix.hasPencilEigenvector_col_of_conj_eq_diagonal`).
* `Matrix.mem_spectrum_inv_mul_iff_exists_mulVec_eq_smul`,
  `Matrix.spectrum_inv_mul_subset_of_posDef` and `Matrix.spectrum_inv_mul_subset_Icc_div`: the
  real symmetric-definite pencil `(A, P)` in the preconditioned form `P⁻¹ A`
  ([quarteroni2000numerical] Remark 4.2 and (4.33)) — the complex eigenvalues of `P⁻¹ A` are the
  generalized eigenvalues, they are real, they lie in `[lmin, lmax]` when the generalized Rayleigh
  quotient `(A x, x)/(P x, x)` does, and they are enclosed by
  `λ_min(A)/λ_max(P) ≤ λ ≤ λ_max(A)/λ_min(P)`.

## Implementation notes

The generalized Schur decomposition reduces to the Schur form of one matrix
(`Numlib/LinearAlgebra/Matrix/Schur`) and one QR factorization (`Numlib/LinearAlgebra/Matrix/QR`):
with `A₀ = A - μ₀ B` invertible, which regularity provides, triangularize `A₀⁻¹ B = Z T₀ Zᴴ` and
factor `A₀ Z = U S₀`; then `Uᴴ B Z = S₀ T₀` and `Uᴴ A Z = S₀ + μ₀ S₀ T₀`. The simultaneous
diagonalization uses no Cholesky factor: the unitary eigenbasis of `B` scaled by the inverse square
roots of its eigenvalues is a matrix `W` with `Wᴴ B W = 1`
(`Matrix.PosDef.exists_isUnit_conj_eq_one`), and the spectral theorem for the Hermitian matrix
`Wᴴ A W` does the rest.

The real statements about `P⁻¹ A` are proved directly from the Hermitian form of the
complexification (`Matrix.star_dotProduct_complexify_mulVec_of_isHermitian`), without the
`P`-inner-product operator of `Numlib/Krylov/Preconditioned`: an eigenvector equation
`A x = μ P x` over `ℂ` gives `μ = (xᴴ A x)/(xᴴ P x)`, a quotient of a real number by a positive one.
-/

open Polynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The characteristic polynomial of a pencil -/

section Ring

variable {R : Type*} [CommRing R]

/-- The characteristic polynomial `det (A - z B)` of the pencil `(A, B)`,
[quarteroni2000numerical] §5.9. It is defined over any commutative ring; the pencil is *regular*
(`Matrix.IsRegularPencil`) when it is not identically zero. -/
noncomputable def pencilPoly (A B : Matrix n n R) : R[X] :=
  (A.map C - (X : R[X]) • B.map C).det

/-- `pencilPoly` in the form `det (X • A' + B')` of Mathlib's degree and coefficient lemmas. -/
private theorem pencilPoly_eq_det_X_smul_add (A B : Matrix n n R) :
    pencilPoly A B = ((X : R[X]) • (-B).map C + A.map C).det := by
  rw [pencilPoly, Matrix.map_neg _ (map_neg C), smul_neg, ← sub_eq_neg_add]

/-- Evaluating the characteristic polynomial of a pencil at `μ` gives `det (A - μ B)`. -/
theorem pencilPoly_eval (A B : Matrix n n R) (μ : R) :
    (pencilPoly A B).eval μ = (A - μ • B).det := by
  rw [pencilPoly, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, map_apply, sub_apply, smul_apply, coe_evalRingHom,
    eval_sub, eval_C, eval_mul, eval_X, smul_eq_mul, Matrix.smul_apply]

/-- For `B = 1` the characteristic polynomial of the pencil is `(-1)^n` times the characteristic
polynomial of `A`, since `det (A - X) = (-1)^n det (X - A)`. -/
theorem pencilPoly_one (A : Matrix n n R) :
    pencilPoly A 1 = (-1) ^ Fintype.card n * A.charpoly := by
  rw [charpoly, ← det_neg, pencilPoly]
  congr 1
  ext i j
  simp [charmatrix_apply, Matrix.one_apply, diagonal_apply]

/-- The characteristic polynomial of a pencil has degree at most `n`. -/
theorem natDegree_pencilPoly_le (A B : Matrix n n R) :
    (pencilPoly A B).natDegree ≤ Fintype.card n := by
  rw [pencilPoly_eq_det_X_smul_add]
  exact natDegree_det_X_add_C_le _ _

/-- The coefficient of `X ^ n` in the characteristic polynomial of a pencil is `(-1)^n det B`, so
the pencil has `n` finite eigenvalues exactly when `B` is invertible
(`Matrix.natDegree_pencilPoly_eq_card_iff`). -/
theorem coeff_pencilPoly_card (A B : Matrix n n R) :
    (pencilPoly A B).coeff (Fintype.card n) = (-1) ^ Fintype.card n * B.det := by
  rw [pencilPoly_eq_det_X_smul_add, coeff_det_X_add_C_card, det_neg]

/-- A pencil is **regular** when its characteristic polynomial `det (A - z B)` is not identically
zero, and *singular* otherwise ([quarteroni2000numerical] §5.9). -/
def IsRegularPencil (A B : Matrix n n R) : Prop := pencilPoly A B ≠ 0

/-- A pencil whose second matrix has a unit determinant is regular: the leading coefficient
`(-1)^n det B` of its characteristic polynomial is a unit. -/
theorem isRegularPencil_of_isUnit [Nontrivial R] (A : Matrix n n R) {B : Matrix n n R}
    (hB : IsUnit B.det) : IsRegularPencil A B := by
  intro h
  have := coeff_pencilPoly_card A B
  rw [h, coeff_zero] at this
  exact hB.ne_zero (by simpa using this.symm)

/-- The standard eigenvalue problem is a regular pencil. -/
theorem isRegularPencil_one [Nontrivial R] (A : Matrix n n R) : IsRegularPencil A 1 :=
  isRegularPencil_of_isUnit A (by simp)

/-- The multiplicity of the eigenvalue `∞` of a regular pencil, `n - deg p`: the number of finite
eigenvalues the characteristic polynomial of degree `deg p` lacks
([quarteroni2000numerical] §5.9). -/
noncomputable def pencilInftyMultiplicity (A B : Matrix n n R) : ℕ :=
  Fintype.card n - (pencilPoly A B).natDegree

end Ring

/-! ### The spectrum of a pencil over a field -/

section Field

variable {K : Type*} [Field K]

/-- The finite generalized eigenvalues `σ(A, B) = {μ | det (A - μ B) = 0}` of the pencil
`(A, B)`, [quarteroni2000numerical] §5.9. -/
def pencilSpectrum (A B : Matrix n n K) : Set K := {μ | (A - μ • B).det = 0}

/-- An eigenvalue/eigenvector pair of the pencil `(A, B)`: `x ≠ 0` with `A x = μ B x`,
[quarteroni2000numerical] display (5.58). -/
def HasPencilEigenvector (A B : Matrix n n K) (μ : K) (x : n → K) : Prop :=
  x ≠ 0 ∧ A *ᵥ x = μ • (B *ᵥ x)

/-- Membership in the pencil spectrum, unfolded: `det (A - μ B) = 0`. -/
theorem mem_pencilSpectrum_iff_det {A B : Matrix n n K} {μ : K} :
    μ ∈ pencilSpectrum A B ↔ (A - μ • B).det = 0 := Iff.rfl

/-- A scalar is in the spectrum of a pencil exactly when it has an eigenvector. -/
theorem mem_pencilSpectrum_iff_exists (A B : Matrix n n K) (μ : K) :
    μ ∈ pencilSpectrum A B ↔ ∃ x, HasPencilEigenvector A B μ x := by
  rw [mem_pencilSpectrum_iff_det, ← Matrix.exists_mulVec_eq_zero_iff]
  simp only [HasPencilEigenvector, sub_mulVec, smul_mulVec, sub_eq_zero]

/-- The spectrum of a pencil is the root set of its characteristic polynomial. -/
theorem mem_pencilSpectrum_iff_isRoot (A B : Matrix n n K) (μ : K) :
    μ ∈ pencilSpectrum A B ↔ (pencilPoly A B).IsRoot μ := by
  rw [mem_pencilSpectrum_iff_det, IsRoot.def, pencilPoly_eval]

/-- The pencil `(A, 1)` is the standard eigenvalue problem: `σ(A, 1) = σ(A)`. -/
theorem pencilSpectrum_one (A : Matrix n n K) : pencilSpectrum A 1 = spectrum K A := by
  ext μ
  rw [mem_pencilSpectrum_iff_exists, mem_spectrum_iff_exists_mulVec_eq_smul]
  simp [HasPencilEigenvector]

/-- The reduction of a pencil with invertible `B` to the standard problem: `σ(A, B) = σ(B⁻¹ A)`,
[quarteroni2000numerical] §5.9.1 (their `C x = λ x` with `B C = A`). -/
theorem pencilSpectrum_eq_spectrum_of_isUnit (A : Matrix n n K) {B : Matrix n n K}
    (hB : IsUnit B) : pencilSpectrum A B = spectrum K (B⁻¹ * A) := by
  have hBd := (isUnit_iff_isUnit_det B).mp hB
  ext μ
  rw [mem_pencilSpectrum_iff_exists, mem_spectrum_iff_exists_mulVec_eq_smul]
  refine exists_congr fun x => and_congr_right' ⟨fun h => ?_, fun h => ?_⟩
  · rw [← mulVec_mulVec, h, mulVec_smul, mulVec_mulVec, nonsing_inv_mul _ hBd, one_mulVec]
  · have h' := congrArg (B *ᵥ ·) h
    simpa [mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ hBd, mulVec_smul] using h'

/-- A pencil has `n` finite eigenvalues — its characteristic polynomial has degree `n` — exactly
when `B` is nonsingular, [quarteroni2000numerical] §5.9.1. -/
theorem natDegree_pencilPoly_eq_card_iff (A B : Matrix n n K) :
    (pencilPoly A B).natDegree = Fintype.card n ↔ IsUnit B.det := by
  rw [isUnit_iff_ne_zero]
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos (Fintype.card n) with hn | hn
    · have : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
      simp
    · have hne : pencilPoly A B ≠ 0 := fun h0 => by
        rw [h0, natDegree_zero] at h
        omega
      have := leadingCoeff_ne_zero.mpr hne
      rw [leadingCoeff, h, coeff_pencilPoly_card] at this
      exact right_ne_zero_of_mul this
  · intro h
    refine le_antisymm (natDegree_pencilPoly_le A B) (le_natDegree_of_ne_zero ?_)
    rw [coeff_pencilPoly_card]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h

/-- A singular pencil has every scalar as an eigenvalue ([quarteroni2000numerical] Example 5.14,
third pencil). -/
theorem pencilSpectrum_eq_univ_of_not_isRegularPencil {A B : Matrix n n K}
    (h : ¬ IsRegularPencil A B) : pencilSpectrum A B = Set.univ := by
  rw [IsRegularPencil, not_not] at h
  ext μ
  simp [mem_pencilSpectrum_iff_isRoot, h]

/-- A regular pencil has finitely many eigenvalues, the roots of a nonzero polynomial. -/
theorem IsRegularPencil.finite_pencilSpectrum {A B : Matrix n n K} (h : IsRegularPencil A B) :
    (pencilSpectrum A B).Finite := by
  convert finite_setOfPred_isRoot h using 1
  ext μ
  exact mem_pencilSpectrum_iff_isRoot A B μ

/-- Over an infinite field a regular pencil has a non-eigenvalue: some `A - μ₀ B` is invertible.
This is the first step of the generalized Schur decomposition. -/
theorem IsRegularPencil.exists_isUnit_sub_smul [Infinite K] {A B : Matrix n n K}
    (h : IsRegularPencil A B) : ∃ μ₀ : K, IsUnit (A - μ₀ • B) := by
  obtain ⟨μ₀, hμ₀⟩ := h.finite_pencilSpectrum.exists_notMem
  exact ⟨μ₀, (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hμ₀)⟩

/-- The spectrum of a pencil is unchanged by an invertible equivalence `(U A Z, U B Z)`:
`det (U (A - μ B) Z) = det U · det (A - μ B) · det Z`. -/
theorem pencilSpectrum_mul_mul_of_isUnit (A B : Matrix n n K) {U Z : Matrix n n K}
    (hU : IsUnit U) (hZ : IsUnit Z) :
    pencilSpectrum (U * A * Z) (U * B * Z) = pencilSpectrum A B := by
  have hUd := (isUnit_iff_isUnit_det U).mp hU
  have hZd := (isUnit_iff_isUnit_det Z).mp hZ
  ext μ
  have : U * A * Z - μ • (U * B * Z) = U * (A - μ • B) * Z := by
    simp [Matrix.mul_sub, Matrix.sub_mul]
  rw [mem_pencilSpectrum_iff_det, mem_pencilSpectrum_iff_det, this, det_mul, det_mul,
    mul_eq_zero, mul_eq_zero]
  simp [hUd.ne_zero, hZd.ne_zero]

/-- The spectrum of a pencil of two diagonal matrices: `μ` with `d i = μ * e i` for some `i`. -/
theorem pencilSpectrum_diagonal (d e : n → K) :
    pencilSpectrum (diagonal d) (diagonal e) = {μ | ∃ i, d i = μ * e i} := by
  ext μ
  rw [mem_pencilSpectrum_iff_det, smul_eq_diagonal_mul, diagonal_mul_diagonal, diagonal_sub,
    det_diagonal, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

variable [LinearOrder n]

/-- The characteristic polynomial of a pencil of two upper triangular matrices is the product of
the diagonal pencils `t_ii - X s_ii`. -/
theorem pencilPoly_of_isUpperTriangular {T S : Matrix n n K} (hT : T.IsUpperTriangular)
    (hS : S.IsUpperTriangular) :
    pencilPoly T S = ∏ i, (C (T i i) - X * C (S i i)) := by
  rw [pencilPoly, det_of_isUpperTriangular]
  · simp
  · intro i j hij
    simp [hT hij, hS hij]

/-- The eigenvalues of a pencil of upper triangular matrices are read off the diagonals: `μ` is an
eigenvalue exactly when `t_ii = μ s_ii` for some `i`, that is, `μ = t_ii / s_ii` when `s_ii ≠ 0`;
a diagonal position with `s_ii = 0` and `t_ii ≠ 0` contributes no finite eigenvalue (it is the
eigenvalue `∞` of [quarteroni2000numerical] Property 5.10). -/
theorem pencilSpectrum_eq_of_isUpperTriangular {T S : Matrix n n K} (hT : T.IsUpperTriangular)
    (hS : S.IsUpperTriangular) :
    pencilSpectrum T S = {μ | ∃ i, T i i = μ * S i i} := by
  ext μ
  rw [mem_pencilSpectrum_iff_isRoot, pencilPoly_of_isUpperTriangular hT hS, IsRoot.def,
    eval_prod, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, eval_sub, eval_C, eval_mul, eval_X, sub_eq_zero,
    Set.mem_ofPred_eq]

end Field

/-! ### The real symmetric-definite pencil `(A, P)` in the preconditioned form `P⁻¹ A` -/

section Real

open scoped ComplexOrder

/-- The complex eigenvalues of the preconditioned matrix `P⁻¹ A` are the generalized eigenvalues
of the pencil `(A, P)`: `μ ∈ σ(P⁻¹ A)` exactly when `A x = μ P x` for some complex `x ≠ 0`
([quarteroni2000numerical] Remark 4.2, display (4.32)). -/
theorem mem_spectrum_inv_mul_iff_exists_mulVec_eq_smul (A : Matrix n n ℝ) {P : Matrix n n ℝ}
    (hP : IsUnit P) (μ : ℂ) :
    μ ∈ spectrum ℂ (complexify (P⁻¹ * A)) ↔
      ∃ x : n → ℂ, x ≠ 0 ∧ complexify A *ᵥ x = μ • (complexify P *ᵥ x) := by
  rw [complexify_mul, complexify_inv,
    ← pencilSpectrum_eq_spectrum_of_isUnit _ ((isUnit_complexify_iff P).mpr hP),
    mem_pencilSpectrum_iff_exists]
  rfl

omit [DecidableEq n] in
/-- The generalized Rayleigh quotient of a complex eigenvector of a real symmetric-definite pencil:
if `A x = μ P x` with `x ≠ 0`, `A` symmetric and `P` positive definite, then `μ` is the real number
`(a₁ + a₂) / (p₁ + p₂)`, where `a₁, a₂` are the real quadratic form of `A` at the real and imaginary
parts of `x` and `p₁, p₂` that of `P`, with `0 < p₁ + p₂`. -/
private theorem eq_ofReal_div_of_mulVec_eq_smul {A P : Matrix n n ℝ} (hA : A.IsHermitian)
    (hP : P.PosDef) {μ : ℂ} {x : n → ℂ} (hx : x ≠ 0)
    (hμ : complexify A *ᵥ x = μ • (complexify P *ᵥ x)) :
    let xr : n → ℝ := fun i => (x i).re
    let xi : n → ℝ := fun i => (x i).im
    0 < xr ⬝ᵥ (P *ᵥ xr) + xi ⬝ᵥ (P *ᵥ xi) ∧
      μ = ((xr ⬝ᵥ (A *ᵥ xr) + xi ⬝ᵥ (A *ᵥ xi)) / (xr ⬝ᵥ (P *ᵥ xr) + xi ⬝ᵥ (P *ᵥ xi)) : ℝ) := by
  intro xr xi
  have hform := congrArg (star x ⬝ᵥ ·) hμ
  simp only [dotProduct_smul, star_dotProduct_complexify_mulVec_of_isHermitian hA,
    star_dotProduct_complexify_mulVec_of_isHermitian hP.1] at hform
  have hpos : (0 : ℂ) < star x ⬝ᵥ (complexify P *ᵥ x) :=
    (posDef_complexify_iff.mpr hP).dotProduct_mulVec_pos hx
  rw [star_dotProduct_complexify_mulVec_of_isHermitian hP.1, Complex.zero_lt_real] at hpos
  refine ⟨hpos, ?_⟩
  rw [Complex.ofReal_div, hform, smul_eq_mul, mul_div_cancel_right₀]
  exact_mod_cast hpos.ne'

/-- **The spectrum of `P⁻¹ A` is real and bounded by the generalized Rayleigh quotient**: for real
symmetric `A` and positive definite `P`, if `lmin (P x, x) ≤ (A x, x) ≤ lmax (P x, x)` for every
real `x`, every complex eigenvalue of `P⁻¹ A` is a real number in `[lmin, lmax]`
([quarteroni2000numerical] Remark 4.2, in the form Theorem 4.9 consumes). An eigenvector equation
`A x = μ P x` over `ℂ` gives `μ = (xᴴ A x)/(xᴴ P x)`, and both Hermitian forms are the sums of the
real quadratic forms at the real and imaginary parts of `x`. -/
theorem spectrum_inv_mul_subset_of_posDef {A P : Matrix n n ℝ} (hA : A.IsHermitian)
    (hP : P.PosDef) {lmin lmax : ℝ}
    (hlo : ∀ x : n → ℝ, lmin * (P *ᵥ x ⬝ᵥ x) ≤ A *ᵥ x ⬝ᵥ x)
    (hhi : ∀ x : n → ℝ, A *ᵥ x ⬝ᵥ x ≤ lmax * (P *ᵥ x ⬝ᵥ x)) :
    spectrum ℂ (complexify (P⁻¹ * A)) ⊆ Complex.ofReal '' Set.Icc lmin lmax := by
  intro μ hμ
  obtain ⟨x, hx, hμ⟩ := (mem_spectrum_inv_mul_iff_exists_mulVec_eq_smul A hP.isUnit μ).mp hμ
  obtain ⟨hpos, rfl⟩ := eq_ofReal_div_of_mulVec_eq_smul hA hP hx hμ
  refine ⟨_, ⟨?_, ?_⟩, rfl⟩
  · rw [le_div_iff₀ hpos, mul_add]
    have h1 := hlo fun i => (x i).re
    have h2 := hlo fun i => (x i).im
    simp only [dotProduct_comm _ (P *ᵥ _), dotProduct_comm _ (A *ᵥ _)] at h1 h2 ⊢
    linarith
  · rw [div_le_iff₀ hpos, mul_add]
    have h1 := hhi fun i => (x i).re
    have h2 := hhi fun i => (x i).im
    simp only [dotProduct_comm _ (P *ᵥ _), dotProduct_comm _ (A *ᵥ _)] at h1 h2 ⊢
    linarith

/-- An attained lower bound of the generalized Rayleigh quotient is an eigenvalue of `P⁻¹ A`: if
`c (P x, x) ≤ (A x, x)` for every real `x`, with equality at some `x₀ ≠ 0`, then `c ∈ σ(P⁻¹ A)`.
The quadratic form of the positive semidefinite `A - c P` vanishes at `x₀`, so `(A - c P) x₀ = 0`.
This is how the endpoint hypotheses of [quarteroni2000numerical] Theorem 4.9 are met. -/
theorem mem_spectrum_inv_mul_of_forall_mul_le_of_eq {A P : Matrix n n ℝ} (hA : A.IsHermitian)
    (hP : P.PosDef) {c : ℝ} (hlo : ∀ x : n → ℝ, c * (P *ᵥ x ⬝ᵥ x) ≤ A *ᵥ x ⬝ᵥ x)
    {x₀ : n → ℝ} (hx₀ : x₀ ≠ 0) (heq : c * (P *ᵥ x₀ ⬝ᵥ x₀) = A *ᵥ x₀ ⬝ᵥ x₀) :
    c ∈ spectrum ℝ (P⁻¹ * A) := by
  have hM : (A - c • P).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg (hA.sub (hP.1.smul (IsSelfAdjoint.all c)))
      fun x => ?_
    have := hlo x
    simp only [star_trivial, sub_mulVec, smul_mulVec, sub_dotProduct, smul_dotProduct,
      smul_eq_mul, dotProduct_comm x] at this ⊢
    linarith
  have h0 : (A - c • P) *ᵥ x₀ = 0 := by
    rw [← hM.dotProduct_mulVec_zero_iff]
    simp only [star_trivial, sub_mulVec, smul_mulVec, sub_dotProduct, smul_dotProduct,
      smul_eq_mul, dotProduct_comm x₀]
    linarith
  rw [← pencilSpectrum_eq_spectrum_of_isUnit _ hP.isUnit, mem_pencilSpectrum_iff_exists]
  refine ⟨x₀, hx₀, ?_⟩
  rwa [sub_mulVec, smul_mulVec, sub_eq_zero] at h0

/-- An attained upper bound of the generalized Rayleigh quotient is an eigenvalue of `P⁻¹ A`: the
twin of `Matrix.mem_spectrum_inv_mul_of_forall_mul_le_of_eq`, through the pencil `(-A, P)`. -/
theorem mem_spectrum_inv_mul_of_forall_le_mul_of_eq {A P : Matrix n n ℝ} (hA : A.IsHermitian)
    (hP : P.PosDef) {c : ℝ} (hhi : ∀ x : n → ℝ, A *ᵥ x ⬝ᵥ x ≤ c * (P *ᵥ x ⬝ᵥ x))
    {x₀ : n → ℝ} (hx₀ : x₀ ≠ 0) (heq : A *ᵥ x₀ ⬝ᵥ x₀ = c * (P *ᵥ x₀ ⬝ᵥ x₀)) :
    c ∈ spectrum ℝ (P⁻¹ * A) := by
  have h := mem_spectrum_inv_mul_of_forall_mul_le_of_eq hA.neg hP (c := -c)
    (fun x => by have := hhi x; simp only [neg_mulVec, neg_dotProduct]; linarith) hx₀
    (by simp only [neg_mulVec, neg_dotProduct]; linarith)
  rw [Matrix.mul_neg, ← spectrum.neg_eq, Set.mem_neg] at h
  simpa using h

/-- **Enclosure of the spectrum of `P⁻¹ A` by the extreme eigenvalues**,
[quarteroni2000numerical] (4.33): for real symmetric `A` and positive definite `P` with
`a ‖x‖² ≤ (A x, x) ≤ a' ‖x‖²` and `p ‖x‖² ≤ (P x, x) ≤ p' ‖x‖²`, `0 ≤ a` and `0 < p`, every
eigenvalue of `P⁻¹ A` is real and lies in `[a / p', a' / p]`. With `a, a'` the extreme eigenvalues
of `A` and `p, p'` those of `P` this is `λ_min(A)/λ_max(P) ≤ λ ≤ λ_max(A)/λ_min(P)`, as printed;
`Matrix.spectrum_inv_mul_subset_Icc_min_div_max_div` is the form without the sign hypothesis. -/
theorem spectrum_inv_mul_subset_Icc_div {A P : Matrix n n ℝ} (hA : A.IsHermitian)
    (hP : P.PosDef) {a a' p p' : ℝ} (ha : 0 ≤ a) (hp : 0 < p) (hp' : 0 < p')
    (hAlo : ∀ x : n → ℝ, a * (x ⬝ᵥ x) ≤ A *ᵥ x ⬝ᵥ x)
    (hAhi : ∀ x : n → ℝ, A *ᵥ x ⬝ᵥ x ≤ a' * (x ⬝ᵥ x))
    (hPlo : ∀ x : n → ℝ, p * (x ⬝ᵥ x) ≤ P *ᵥ x ⬝ᵥ x)
    (hPhi : ∀ x : n → ℝ, P *ᵥ x ⬝ᵥ x ≤ p' * (x ⬝ᵥ x)) :
    spectrum ℂ (complexify (P⁻¹ * A)) ⊆ Complex.ofReal '' Set.Icc (a / p') (a' / p) := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i⟩⟩
  · rw [spectrum.of_subsingleton]
    exact Set.empty_subset _
  have ha' : 0 ≤ a' := by
    have h1 := hAlo (Pi.single i 1)
    have h2 := hAhi (Pi.single i 1)
    have h3 : (Pi.single i (1 : ℝ)) ⬝ᵥ (Pi.single i 1) = 1 := by simp
    rw [h3] at h1 h2
    linarith
  refine spectrum_inv_mul_subset_of_posDef hA hP (fun x => ?_) fun x => ?_
  · calc a / p' * (P *ᵥ x ⬝ᵥ x) ≤ a / p' * (p' * (x ⬝ᵥ x)) := by
          gcongr; exact hPhi x
      _ = a * (x ⬝ᵥ x) := by field_simp
      _ ≤ A *ᵥ x ⬝ᵥ x := hAlo x
  · calc A *ᵥ x ⬝ᵥ x ≤ a' * (x ⬝ᵥ x) := hAhi x
      _ = a' / p * (p * (x ⬝ᵥ x)) := by field_simp
      _ ≤ a' / p * (P *ᵥ x ⬝ᵥ x) := by gcongr; exact hPlo x

/-- The enclosure `Matrix.spectrum_inv_mul_subset_Icc_div` without a sign hypothesis on `a`: the
spectrum of `P⁻¹ A` lies in `[min (a/p) (a/p'), max (a'/p) (a'/p')]`. For `0 ≤ a ≤ a'` and `p ≤ p'`
this is `[a/p', a'/p]`; for `a ≤ 0 ≤ a'` it is `[a/p, a'/p]`, and for `a' ≤ 0` it is
`[a/p, a'/p']`. -/
theorem spectrum_inv_mul_subset_Icc_min_div_max_div {A P : Matrix n n ℝ} (hA : A.IsHermitian)
    (hP : P.PosDef) {a a' p p' : ℝ} (hp : 0 < p) (hp' : 0 < p')
    (hAlo : ∀ x : n → ℝ, a * (x ⬝ᵥ x) ≤ A *ᵥ x ⬝ᵥ x)
    (hAhi : ∀ x : n → ℝ, A *ᵥ x ⬝ᵥ x ≤ a' * (x ⬝ᵥ x))
    (hPlo : ∀ x : n → ℝ, p * (x ⬝ᵥ x) ≤ P *ᵥ x ⬝ᵥ x)
    (hPhi : ∀ x : n → ℝ, P *ᵥ x ⬝ᵥ x ≤ p' * (x ⬝ᵥ x)) :
    spectrum ℂ (complexify (P⁻¹ * A)) ⊆
      Complex.ofReal '' Set.Icc (min (a / p) (a / p')) (max (a' / p) (a' / p')) := by
  have hPnn : ∀ x : n → ℝ, 0 ≤ P *ᵥ x ⬝ᵥ x := fun x => by
    have := hPlo x
    have := dotProduct_self_star_nonneg x
    simp only [star_trivial] at *
    nlinarith
  refine spectrum_inv_mul_subset_of_posDef hA hP (fun x => ?_) fun x => ?_
  · rcases le_or_gt 0 a with ha | ha
    · calc min (a / p) (a / p') * (P *ᵥ x ⬝ᵥ x) ≤ a / p' * (P *ᵥ x ⬝ᵥ x) := by
            gcongr
            · exact hPnn x
            · exact min_le_right _ _
        _ ≤ a / p' * (p' * (x ⬝ᵥ x)) := by gcongr; exact hPhi x
        _ = a * (x ⬝ᵥ x) := by field_simp
        _ ≤ A *ᵥ x ⬝ᵥ x := hAlo x
    · calc min (a / p) (a / p') * (P *ᵥ x ⬝ᵥ x) ≤ a / p * (P *ᵥ x ⬝ᵥ x) := by
            gcongr
            · exact hPnn x
            · exact min_le_left _ _
        _ ≤ a / p * (p * (x ⬝ᵥ x)) := by
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hp]
            exact mul_le_mul_of_nonpos_left (hPlo x) ha.le
        _ = a * (x ⬝ᵥ x) := by field_simp
        _ ≤ A *ᵥ x ⬝ᵥ x := hAlo x
  · rcases le_or_gt 0 a' with ha | ha
    · calc A *ᵥ x ⬝ᵥ x ≤ a' * (x ⬝ᵥ x) := hAhi x
        _ = a' / p * (p * (x ⬝ᵥ x)) := by field_simp
        _ ≤ a' / p * (P *ᵥ x ⬝ᵥ x) := by gcongr; exact hPlo x
        _ ≤ max (a' / p) (a' / p') * (P *ᵥ x ⬝ᵥ x) := by
            gcongr
            · exact hPnn x
            · exact le_max_left _ _
    · calc A *ᵥ x ⬝ᵥ x ≤ a' * (x ⬝ᵥ x) := hAhi x
        _ = a' / p' * (p' * (x ⬝ᵥ x)) := by field_simp
        _ ≤ a' / p' * (P *ᵥ x ⬝ᵥ x) := by
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hp']
            exact mul_le_mul_of_nonpos_left (hPhi x) ha.le
        _ ≤ max (a' / p) (a' / p') * (P *ᵥ x ⬝ᵥ x) := by
            gcongr
            · exact hPnn x
            · exact le_max_right _ _

end Real

/-! ### The generalized Schur decomposition -/

section Schur

variable {𝕜 : Type*} [RCLike 𝕜]

variable [IsAlgClosed 𝕜]

/-- **Generalized Schur decomposition** ([quarteroni2000numerical] Property 5.10;
[golub1989matrix] Theorem 7.7.1): a regular pencil over an algebraically closed `RCLike` field
(that is, over `ℂ`) is simultaneously triangularized by two unitary matrices, `Uᴴ A Z = T` and
`Uᴴ B Z = S` with `T`, `S` upper triangular. The eigenvalues are then read off the diagonals by
`Matrix.pencilSpectrum_eq_of_isUpperTriangular`.

The proof reduces to the Schur form of a single matrix: with `A₀ = A - μ₀ B` invertible,
triangularize `A₀⁻¹ B = Z T₀ Zᴴ` and QR-factor `A₀ Z = U S₀`; then `Uᴴ B Z = S₀ T₀` and
`Uᴴ A Z = S₀ + μ₀ S₀ T₀`. -/
theorem exists_unitary_pencil_isUpperTriangular [LinearOrder n] {A B : Matrix n n 𝕜}
    (h : IsRegularPencil A B) :
    ∃ U ∈ unitaryGroup n 𝕜, ∃ Z ∈ unitaryGroup n 𝕜,
      (star U * A * Z).IsUpperTriangular ∧ (star U * B * Z).IsUpperTriangular := by
  obtain ⟨μ₀, hμ₀⟩ := h.exists_isUnit_sub_smul
  have hd := (isUnit_iff_isUnit_det _).mp hμ₀
  obtain ⟨Z, hZ, hT₀, -⟩ := exists_unitary_conj_upperTriangular ((A - μ₀ • B)⁻¹ * B)
  obtain ⟨U, hU, hS₀⟩ := exists_unitary_mul_isUpperTriangular ((A - μ₀ • B) * Z)
  have hBZ : U * ((A - μ₀ • B) * Z) * (star Z * ((A - μ₀ • B)⁻¹ * B) * Z) = U * B * Z := by
    calc _ = U * (A - μ₀ • B) * (Z * star Z) * (A - μ₀ • B)⁻¹ * B * Z := by
          simp only [Matrix.mul_assoc]
      _ = U * B * Z := by
          rw [mem_unitaryGroup_iff.mp hZ, Matrix.mul_one, mul_nonsing_inv_cancel_right _ _ hd]
  refine ⟨star U, Unitary.star_mem hU, Z, hZ, ?_, ?_⟩
  · have hAZ : U * A * Z = U * ((A - μ₀ • B) * Z) + μ₀ • (U * B * Z) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_assoc]
      abel
    rw [star_star, hAZ, ← hBZ]
    intro i j hij
    simp [hS₀ hij, (hS₀.mul hT₀) hij]
  · rw [star_star, ← hBZ]
    exact hS₀.mul hT₀

end Schur

/-! ### Symmetric-definite pencils -/

section SymmetricDefinite

open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The columns of a congruence that carries `(A, B)` to `(diag d, 1)` are eigenvectors of the
pencil: from `Mᴴ B M = 1` and `Mᴴ A M = diag d` with `M` invertible, `A (M eᵢ) = dᵢ B (M eᵢ)`.
(They are linearly independent by `Matrix.linearIndependent_cols_iff_isUnit`, and `B`-orthonormal
by `Matrix.star_col_dotProduct_mulVec_col_of_conj_eq_one`.) -/
theorem hasPencilEigenvector_col_of_conj_eq_diagonal {A B M : Matrix n n 𝕜} {d : n → 𝕜}
    (hM : IsUnit M) (hB : star M * B * M = 1) (hA : star M * A * M = diagonal d) (i : n) :
    HasPencilEigenvector A B (d i) (M.col i) := by
  have hMs : IsUnit (star M).det := (isUnit_iff_isUnit_det _).mp hM.star
  have hAM : A * M = (star M)⁻¹ * diagonal d := by
    rw [← hA, Matrix.mul_assoc (star M), nonsing_inv_mul_cancel_left _ _ hMs]
  have hBM : B * M = (star M)⁻¹ := by
    rw [Matrix.mul_assoc] at hB
    exact (inv_eq_right_inv hB).symm
  refine ⟨(linearIndependent_cols_iff_isUnit.mpr hM).ne_zero i, ?_⟩
  rw [← mulVec_single_one, mulVec_mulVec, mulVec_mulVec, hAM, ← hBM, ← mulVec_mulVec,
    diagonal_mulVec_single, ← mulVec_smul, ← Pi.single_smul, smul_eq_mul]

/-- The columns of a congruence with `Mᴴ B M = 1` are `B`-orthonormal:
`(M eᵢ)ᴴ B (M eⱼ) = δᵢⱼ`. -/
theorem star_col_dotProduct_mulVec_col_of_conj_eq_one {B M : Matrix n n 𝕜}
    (hB : star M * B * M = 1) (i j : n) :
    star (M.col i) ⬝ᵥ (B *ᵥ M.col j) = if i = j then 1 else 0 := by
  have := congrFun (congrFun hB i) j
  rw [one_apply] at this
  rw [← this, dotProduct_mulVec]
  simp [Matrix.mul_apply, vecMul, dotProduct, col, Finset.sum_mul, mul_assoc]

/-- **Simultaneous diagonalization of a symmetric-definite pencil**
([quarteroni2000numerical] Theorem 5.7; [golub1989matrix] Theorem 8.7.1): for `A` Hermitian and
`B` positive definite there is an invertible `M` with `Mᴴ B M = 1` and `Mᴴ A M = diag d` with `d`
real, and the eigenvalues of the pencil `(A, B)` are exactly the `d i`. In the book `M = H⁻¹ Y`
for the Cholesky factor `H` of `B` and the orthonormal eigenbasis `Y` of `H⁻ᴴ A H⁻¹`; here `H⁻¹`
is replaced by any `W` with `Wᴴ B W = 1` (`Matrix.PosDef.exists_isUnit_conj_eq_one`). The
columns of `M` are `B`-orthonormal eigenvectors of the pencil
(`Matrix.hasPencilEigenvector_col_of_conj_eq_diagonal`,
`Matrix.star_col_dotProduct_mulVec_col_of_conj_eq_one`), linearly independent by
`Matrix.linearIndependent_cols_iff_isUnit`. -/
theorem exists_simultaneous_diagonalization {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.PosDef) :
    ∃ (M : Matrix n n 𝕜) (d : n → ℝ), IsUnit M ∧ star M * B * M = 1 ∧
      star M * A * M = diagonal (fun i => (d i : 𝕜)) ∧
      pencilSpectrum A B = Set.range (fun i => (d i : 𝕜)) := by
  obtain ⟨W, hW, hWB⟩ := hB.exists_isUnit_conj_eq_one
  have hC : (star W * A * W).IsHermitian := by
    rw [star_eq_conjTranspose]
    exact isHermitian_conjTranspose_mul_mul W hA
  set V : Matrix n n 𝕜 := (hC.eigenvectorUnitary : Matrix n n 𝕜) with hVdef
  have hV : star V * (star W * A * W) * V = diagonal (RCLike.ofReal ∘ hC.eigenvalues) := by
    have := hC.conjStarAlgAut_star_eigenvectorUnitary
    rwa [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at this
  have hM : IsUnit (W * V) := hW.mul Unitary.isUnit_coe
  have h1 : star (W * V) * B * (W * V) = 1 := by
    rw [star_mul, show star V * star W * B * (W * V) = star V * (star W * B * W) * V by
      simp only [Matrix.mul_assoc], hWB, Matrix.mul_one, hVdef, Unitary.coe_star_mul_self]
  have h2 : star (W * V) * A * (W * V) = diagonal (fun i => (hC.eigenvalues i : 𝕜)) := by
    rw [star_mul, show star V * star W * A * (W * V) = star V * (star W * A * W) * V by
      simp only [Matrix.mul_assoc], hV]
    rfl
  refine ⟨W * V, hC.eigenvalues, hM, h1, h2, ?_⟩
  rw [← pencilSpectrum_mul_mul_of_isUnit A B hM.star hM, h1, h2, ← diagonal_one,
    pencilSpectrum_diagonal]
  ext μ
  simp [eq_comm]

/-- The eigenvalues of a symmetric-definite pencil are real ([quarteroni2000numerical]
Theorem 5.7). -/
theorem pencilSpectrum_subset_range_ofReal_of_posDef {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.PosDef) : pencilSpectrum A B ⊆ Set.range ((↑) : ℝ → 𝕜) := by
  obtain ⟨M, d, -, -, -, hspec⟩ := exists_simultaneous_diagonalization hA hB
  rw [hspec]
  rintro _ ⟨i, rfl⟩
  exact ⟨d i, rfl⟩

/-- The eigenvalues of a pencil of two positive definite matrices are positive: from `A x = μ B x`,
`μ = (xᴴ A x)/(xᴴ B x)` is a quotient of two positive reals. This is what the stability analysis
of the θ-method for `M u' + A u = f` with `M`, `A` symmetric positive definite needs
([quarteroni2000numerical] §13.3.1). -/
theorem re_pos_of_mem_pencilSpectrum_of_posDef {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosDef) {μ : 𝕜} (hμ : μ ∈ pencilSpectrum A B) : 0 < RCLike.re μ := by
  obtain ⟨x, hx, hμ⟩ := (mem_pencilSpectrum_iff_exists A B μ).mp hμ
  have ha := RCLike.pos_iff.mp (hA.dotProduct_mulVec_pos hx)
  have hb := RCLike.pos_iff.mp (hB.dotProduct_mulVec_pos hx)
  have h := congrArg (fun v => RCLike.re (star x ⬝ᵥ v)) hμ
  simp only [dotProduct_smul, smul_eq_mul, RCLike.mul_re, hb.2, mul_zero, sub_zero] at h
  exact (mul_pos_iff_of_pos_right hb.1).mp (h ▸ ha.1)

end SymmetricDefinite

end Matrix
