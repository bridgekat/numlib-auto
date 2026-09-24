import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Numlib.Analysis.Matrix.OperatorNorm

/-!
# The Sylvester equation and the separation of two matrices

The Sylvester operator `Matrix.sylvesterMap A B : Matrix m n R →ₗ[R] Matrix m n R`,
`X ↦ A * X - X * B`, for square `A : Matrix m m R` and `B : Matrix n n R`, and the separation
`Matrix.sep A B`, the least value of `‖A X - X B‖_F` on the Frobenius unit sphere
([golub2013matrix] §7.1.5, (7.2.5)).

## Unique solvability

Over any field the Sylvester operator is injective, hence bijective, as soon as the characteristic
polynomials of `A` and `B` are coprime (`Matrix.sylvesterMap_injective_of_isCoprime`): from
`A X = X B` follows `p(A) X = X p(B)` for every polynomial `p`
(`Matrix.aeval_mul_eq_mul_aeval_of_mul_eq_mul`); for `p = χ_A` the left side vanishes by
Cayley–Hamilton, and `χ_A(B)` is invertible by a Bézout identity `u χ_A + v χ_B = 1`. Over an
algebraically closed field coprimality is "no common eigenvalue", and conversely a common
eigenvalue `λ`, with `A x = λ x` and `yᵀ B = λ yᵀ`, puts `x yᵀ` in the kernel
(`Matrix.sylvesterMap_vecMulVec_eq_zero`), which gives [golub2013matrix] Lemma 7.1.5 in the form
`Matrix.sylvesterMap_bijective_iff_disjoint_spectrum`. Real matrices go through their
complexifications (`Matrix.isCoprime_charpoly_iff_disjoint_spectrum_complexify`).

## Block diagonalization

`fromBlocks 1 Z 0 1` conjugates `fromBlocks T₁₁ T₁₂ 0 T₂₂` to
`fromBlocks T₁₁ (T₁₁ Z - Z T₂₂ + T₁₂) 0 T₂₂`, so a solution of `T₁₁ Z - Z T₂₂ = -T₁₂` removes the
corner ([golub2013matrix] Lemma 7.1.5, `Matrix.exists_fromBlocks_conj_eq_fromBlocks_zero`).
Iterating over the blocks of a block upper triangular matrix whose diagonal blocks have pairwise
coprime characteristic polynomials (pairwise disjoint spectra over an algebraically closed field)
gives [golub2013matrix] Theorem 7.1.6: the matrix is similar to its block diagonal part
(`Matrix.exists_isUnit_conj_eq_blockDiagonalPart`).

## The separation

`Matrix.sep A B = ⨅ X : {X // ‖X‖_F = 1}, ‖A X - X B‖_F` over `RCLike 𝕜` (the Frobenius norm is
opened locally, `Matrix.Norms.Frobenius`). The infimum is attained (`Matrix.exists_sep_eq`), it is
the best constant in `sep A B ‖X‖_F ≤ ‖A X - X B‖_F` (`Matrix.sep_mul_norm_le`), it is positive
exactly when the Sylvester operator is injective (`Matrix.sep_pos_iff`), it bounds solutions
(`Matrix.frobenius_norm_le_div_sep`, the book's (7.3.20)), it is at most the distance between any
eigenvalue of `A` and any eigenvalue of `B` (`Matrix.sep_le_norm_sub`), it is unitarily invariant
and Lipschitz, and it is symmetric: `Matrix.sep_comm`. The last is the one non-obvious fact. The
operator `P ↦ P A - B P` that the perturbation theory of invariant subspaces inverts is not the
Sylvester operator of `(A, B)` but, read through `P ↦ Pᴴ`, minus the adjoint of the one of
`(Aᴴ, Bᴴ)`; the proof shows that a lower bound `c ‖X‖ ≤ ‖A X - X B‖` passes to the adjoint by
the Frobenius trace pairing (`Matrix.le_norm_sylvesterMap_conjTranspose_of_le`). For Hermitian
`A` and `B` the separation is the distance between the spectra
(`Matrix.IsHermitian.sep_eq_iInf_abs_eigenvalues_sub`, [golub2013matrix] P8.1.9).

## Diagonal coefficients

`sylvesterMap (diagonal ω) (diagonal ν)` acts entrywise by `X k j ↦ (ω k - ν j) X k j`, so the
diagonal equation is solved by division (`Matrix.sylvesterMap_diagonal_eq_iff`); with
`Matrix.sylvesterMap_conj` this is the eigenvector-basis solve behind the fast Poisson solver
([golub2013matrix] §4.8.4) and the generator description of Cauchy-like matrices
([golub2013matrix] (12.1.4), `Matrix.apply_eq_of_sylvesterMap_diagonal_eq`).

## Scope

Everything except `sep` is a statement about the map `X ↦ A ∘ₗ X - X ∘ₗ B` on `F →ₗ[K] E` for
endomorphisms `A` of `E` and `B` of `F`, of which the matrix map is the coordinate form; over `ℂ`
it is Rosenblum's theorem `σ(X ↦ A X - X B) ⊆ σ(A) - σ(B)` in any Banach algebra. The operator
version belongs in `Numlib/LinearAlgebra/` as `LinearMap.sylvesterMap` once a second source needs
it, with these statements as corollaries. `sep` sits here rather than with the invariant-subspace
theory because it is a property of the Sylvester operator alone, and all its consumers (invariant
subspace perturbation, orthogonal iteration, block diagonalization, the conditioning of the
Sylvester equation) import this module.

Mathlib's `Polynomial.sylvester` is the Sylvester *matrix* of two polynomials, an unrelated
object.
-/

open Polynomial

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

section CommRing

variable {R : Type*} [CommRing R]

/-- The **Sylvester operator** `X ↦ A * X - X * B` on `m × n` matrices, for square `A` and `B`
([golub2013matrix] §7.1.5). -/
def sylvesterMap (A : Matrix m m R) (B : Matrix n n R) : Matrix m n R →ₗ[R] Matrix m n R where
  toFun X := A * X - X * B
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

/-- The Sylvester operator, unfolded. -/
@[simp]
theorem sylvesterMap_apply (A : Matrix m m R) (B : Matrix n n R) (X : Matrix m n R) :
    sylvesterMap A B X = A * X - X * B :=
  rfl

/-- **Intertwining passes to polynomials**: if `A * X = X * B` then `p(A) * X = X * p(B)` for every
polynomial `p`. -/
theorem aeval_mul_eq_mul_aeval_of_mul_eq_mul [DecidableEq m] [DecidableEq n]
    {A : Matrix m m R} {B : Matrix n n R} {X : Matrix m n R} (h : A * X = X * B) (p : R[X]) :
    aeval A p * X = X * aeval B p := by
  have hpow : ∀ k : ℕ, A ^ k * X = X * B ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
  simp only [aeval_eq_sum_range, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, hpow]

/-- The Sylvester operator on a rank-one matrix built from eigenvectors: if `A x = α x` and
`yᵀ B = β yᵀ` then `A (x yᵀ) - (x yᵀ) B = (α - β) x yᵀ`. -/
theorem sylvesterMap_vecMulVec {A : Matrix m m R} {B : Matrix n n R} {x : m → R} {y : n → R}
    {α β : R} (hx : A *ᵥ x = α • x) (hy : y ᵥ* B = β • y) :
    sylvesterMap A B (vecMulVec x y) = (α - β) • vecMulVec x y := by
  rw [sylvesterMap_apply, mul_vecMulVec, vecMulVec_mul, hx, hy, smul_vecMulVec, vecMulVec_smul,
    sub_smul]

/-- A common eigenvalue gives a kernel element of the Sylvester operator: if `A x = c x` and
`yᵀ B = c yᵀ` then `A (x yᵀ) - (x yᵀ) B = 0` ([golub2013matrix] proof of Lemma 7.1.5, with `yᵀ` in
place of `yᴴ`). -/
theorem sylvesterMap_vecMulVec_eq_zero {A : Matrix m m R} {B : Matrix n n R} {x : m → R}
    {y : n → R} {c : R} (hx : A *ᵥ x = c • x) (hy : y ᵥ* B = c • y) :
    sylvesterMap A B (vecMulVec x y) = 0 := by
  rw [sylvesterMap_vecMulVec hx hy, sub_self, zero_smul]

/-- **Change of bases** ([golub2013matrix] §12.1.6, §12.1.8): conjugating both coefficients
conjugates the Sylvester operator,
`sylvesterMap (P F P⁻¹) (Q G Q⁻¹) (P A Q⁻¹) = P (sylvesterMap F G A) Q⁻¹` for invertible `P`,
`Q`. -/
theorem sylvesterMap_conj [DecidableEq m] [DecidableEq n] {P : Matrix m m R} {Q : Matrix n n R}
    (hP : IsUnit P) (hQ : IsUnit Q) (F : Matrix m m R) (G : Matrix n n R) (A : Matrix m n R) :
    sylvesterMap (P * F * P⁻¹) (Q * G * Q⁻¹) (P * A * Q⁻¹) = P * sylvesterMap F G A * Q⁻¹ := by
  have hP' : P⁻¹ * P = 1 := nonsing_inv_mul P ((isUnit_iff_isUnit_det P).mp hP)
  have hQ' : Q⁻¹ * Q = 1 := nonsing_inv_mul Q ((isUnit_iff_isUnit_det Q).mp hQ)
  simp only [sylvesterMap_apply, Matrix.mul_sub, Matrix.sub_mul]
  congr 1
  · calc P * F * P⁻¹ * (P * A * Q⁻¹) = P * F * (P⁻¹ * P) * A * Q⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = P * (F * A) * Q⁻¹ := by rw [hP', Matrix.mul_one, Matrix.mul_assoc P]
  · calc P * A * Q⁻¹ * (Q * G * Q⁻¹) = P * A * (Q⁻¹ * Q) * G * Q⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = P * (A * G) * Q⁻¹ := by rw [hQ', Matrix.mul_one, Matrix.mul_assoc P]

/-- **Reindexing** ([golub2013matrix] Algorithm 12.1.2, pivoting of a displacement equation):
permuting rows and columns commutes with the Sylvester operator. -/
theorem sylvesterMap_submatrix {m' n' : Type*} [Fintype m'] [Fintype n'] (σ : m' ≃ m)
    (τ : n' ≃ n) (F : Matrix m m R) (G : Matrix n n R) (A : Matrix m n R) :
    sylvesterMap (F.submatrix σ σ) (G.submatrix τ τ) (A.submatrix σ τ) =
      (sylvesterMap F G A).submatrix σ τ := by
  rw [sylvesterMap_apply, sylvesterMap_apply, submatrix_mul_equiv, submatrix_mul_equiv]
  rfl

/-- The Sylvester operator with diagonal coefficients acts entrywise:
`(diagonal ω X - X diagonal ν) k j = (ω k - ν j) X k j`. -/
theorem sylvesterMap_diagonal_apply [DecidableEq m] [DecidableEq n] (ω : m → R) (ν : n → R)
    (X : Matrix m n R) (k : m) (j : n) :
    sylvesterMap (diagonal ω) (diagonal ν) X k j = (ω k - ν j) * X k j := by
  simp only [sylvesterMap_apply, sub_apply, diagonal_mul, mul_diagonal]
  ring

/-! ### The block computation of Lemma 7.1.5 -/

/-- The block computation behind [golub2013matrix] Lemma 7.1.5:
`[1 -Z; 0 1] [T₁₁ T₁₂; 0 T₂₂] [1 Z; 0 1] = [T₁₁ (T₁₁ Z - Z T₂₂ + T₁₂); 0 T₂₂]`. -/
theorem fromBlocks_one_neg_mul_fromBlocks_mul_fromBlocks_one [DecidableEq m] [DecidableEq n]
    (T₁₁ : Matrix m m R) (T₁₂ : Matrix m n R) (T₂₂ : Matrix n n R) (Z : Matrix m n R) :
    fromBlocks 1 (-Z) 0 1 * fromBlocks T₁₁ T₁₂ 0 T₂₂ * fromBlocks 1 Z 0 1 =
      fromBlocks T₁₁ (T₁₁ * Z - Z * T₂₂ + T₁₂) 0 T₂₂ := by
  simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, Matrix.neg_mul, add_zero, zero_add]
  congr 1
  abel

/-- `[1 -Z; 0 1]` is the inverse of `[1 Z; 0 1]`. -/
theorem fromBlocks_one_neg_mul_fromBlocks_one [DecidableEq m] [DecidableEq n]
    (Z : Matrix m n R) :
    fromBlocks (1 : Matrix m m R) (-Z) (0 : Matrix n m R) (1 : Matrix n n R) *
      fromBlocks 1 Z 0 1 = 1 := by
  simp [fromBlocks_multiply, fromBlocks_one]

/-- [golub2013matrix] Lemma 7.1.5, second half: if the Sylvester operator of the diagonal blocks is
surjective (for instance, if their spectra are disjoint), a solution `Z` of
`T₁₁ Z - Z T₂₂ = -T₁₂` gives the similarity `Y = [1 Z; 0 1]` that removes the off-diagonal
block. -/
theorem exists_fromBlocks_conj_eq_fromBlocks_zero [DecidableEq m] [DecidableEq n]
    {T₁₁ : Matrix m m R} {T₂₂ : Matrix n n R} (h : Function.Surjective (sylvesterMap T₁₁ T₂₂))
    (T₁₂ : Matrix m n R) :
    ∃ Z : Matrix m n R, T₁₁ * Z - Z * T₂₂ = -T₁₂ ∧
      IsUnit (fromBlocks (1 : Matrix m m R) Z (0 : Matrix n m R) (1 : Matrix n n R)) ∧
      (fromBlocks (1 : Matrix m m R) Z (0 : Matrix n m R) (1 : Matrix n n R))⁻¹ *
          fromBlocks T₁₁ T₁₂ 0 T₂₂ * fromBlocks (1 : Matrix m m R) Z 0 1 =
        fromBlocks T₁₁ 0 0 T₂₂ := by
  obtain ⟨Z, hZ⟩ := h (-T₁₂)
  rw [sylvesterMap_apply] at hZ
  have hinv := fromBlocks_one_neg_mul_fromBlocks_one Z
  have hY : (fromBlocks (1 : Matrix m m R) Z (0 : Matrix n m R) (1 : Matrix n n R))⁻¹ =
      fromBlocks 1 (-Z) 0 1 := inv_eq_left_inv hinv
  refine ⟨Z, hZ, (isUnit_iff_isUnit_det _).mpr (isUnit_det_of_left_inverse hinv), ?_⟩
  rw [hY, fromBlocks_one_neg_mul_fromBlocks_mul_fromBlocks_one, hZ, neg_add_cancel]

end CommRing

/-! ### Unique solvability over a field -/

section Field

variable {K : Type*} [Field K] [DecidableEq m] [DecidableEq n]

/-- **Coprime characteristic polynomials make the Sylvester operator injective**, over any field
([golub2013matrix] Lemma 7.1.5 in its field-independent form). -/
theorem sylvesterMap_injective_of_isCoprime {A : Matrix m m K} {B : Matrix n n K}
    (h : IsCoprime A.charpoly B.charpoly) : Function.Injective (sylvesterMap A B) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  rw [sylvesterMap_apply, sub_eq_zero] at hX
  have h0 : X * aeval B A.charpoly = 0 := by
    rw [← aeval_mul_eq_mul_aeval_of_mul_eq_mul hX, aeval_self_charpoly, Matrix.zero_mul]
  obtain ⟨u, v, huv⟩ := h
  have h1 : aeval B A.charpoly * aeval B u = 1 := by
    have := congrArg (aeval B) huv
    rw [map_add, map_mul, map_mul, aeval_self_charpoly, Matrix.mul_zero, add_zero,
      map_one] at this
    rw [← this, ← map_mul, ← map_mul, mul_comm]
  calc X = X * (aeval B A.charpoly * aeval B u) := by rw [h1, Matrix.mul_one]
    _ = 0 := by rw [← Matrix.mul_assoc, h0, Matrix.zero_mul]

/-- **Coprime characteristic polynomials make the Sylvester operator bijective**: an injective
endomorphism of a finite-dimensional space is surjective. -/
theorem sylvesterMap_bijective_of_isCoprime {A : Matrix m m K} {B : Matrix n n K}
    (h : IsCoprime A.charpoly B.charpoly) : Function.Bijective (sylvesterMap A B) :=
  have hi := sylvesterMap_injective_of_isCoprime h
  ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

/-- Under coprime characteristic polynomials the Sylvester equation `A X - X B = C` has exactly one
solution for every `C`, over any field. -/
theorem existsUnique_sylvesterMap_eq_of_isCoprime {A : Matrix m m K} {B : Matrix n n K}
    (h : IsCoprime A.charpoly B.charpoly) (C : Matrix m n K) :
    ∃! X : Matrix m n K, A * X - X * B = C := by
  simpa only [sylvesterMap_apply] using (sylvesterMap_bijective_of_isCoprime h).existsUnique C

/-- A scalar in the spectrum of a square matrix over a field has a left eigenvector:
`yᵀ A = μ yᵀ` with `y ≠ 0`. -/
theorem exists_vecMul_eq_smul_of_mem_spectrum {A : Matrix n n K} {μ : K}
    (hμ : μ ∈ spectrum K A) : ∃ y, y ≠ 0 ∧ y ᵥ* A = μ • y := by
  rw [← spectrum_transpose, mem_spectrum_iff_exists_mulVec_eq_smul] at hμ
  obtain ⟨y, hy, hyA⟩ := hμ
  exact ⟨y, hy, by rw [← mulVec_transpose, hyA]⟩

/-- Over an algebraically closed field, two square matrices have coprime characteristic
polynomials exactly when their spectra are disjoint. -/
theorem isCoprime_charpoly_iff_disjoint_spectrum [IsAlgClosed K] (A : Matrix m m K)
    (B : Matrix n n K) :
    IsCoprime A.charpoly B.charpoly ↔ Disjoint (spectrum K A) (spectrum K B) := by
  rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) K, Set.disjoint_left]
  simp only [coe_aeval_eq_eval, mem_spectrum_iff_isRoot_charpoly, IsRoot.def]
  constructor
  · intro h a ha hb
    rcases h a with h | h <;> contradiction
  · intro h a
    by_cases ha : eval a A.charpoly = 0
    · exact Or.inr (h ha)
    · exact Or.inl ha

/-- [golub2013matrix] Lemma 7.1.5, first half: over an algebraically closed field the Sylvester
operator `X ↦ A X - X B` is bijective exactly when `A` and `B` have no common eigenvalue. -/
theorem sylvesterMap_bijective_iff_disjoint_spectrum [IsAlgClosed K] {A : Matrix m m K}
    {B : Matrix n n K} :
    Function.Bijective (sylvesterMap A B) ↔ Disjoint (spectrum K A) (spectrum K B) := by
  refine ⟨fun h => Set.disjoint_left.mpr fun c hA hB => ?_, fun h =>
    sylvesterMap_bijective_of_isCoprime ((isCoprime_charpoly_iff_disjoint_spectrum A B).mpr h)⟩
  obtain ⟨x, hx, hxA⟩ := (mem_spectrum_iff_exists_mulVec_eq_smul A c).mp hA
  obtain ⟨y, hy, hyB⟩ := exists_vecMul_eq_smul_of_mem_spectrum hB
  have h0 := sylvesterMap_vecMulVec_eq_zero hxA hyB
  rw [← map_zero (sylvesterMap A B)] at h0
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy
  have := congrFun (congrFun (h.1 h0) i) j
  rw [vecMulVec_apply, zero_apply] at this
  exact mul_ne_zero hi hj this

/-- The Sylvester equation `A X - X B = C` has exactly one solution for every `C` when `A` and `B`
have disjoint spectra, over an algebraically closed field. -/
theorem existsUnique_sylvesterMap_eq [IsAlgClosed K] {A : Matrix m m K} {B : Matrix n n K}
    (h : Disjoint (spectrum K A) (spectrum K B)) (C : Matrix m n K) :
    ∃! X : Matrix m n K, A * X - X * B = C := by
  simpa only [sylvesterMap_apply] using
    (sylvesterMap_bijective_iff_disjoint_spectrum.mpr h).existsUnique C

/-- The diagonal Sylvester equation is solved by entrywise division: if `ω k ≠ ν j` for all `k`,
`j`, then `diagonal ω X - X diagonal ν = C` exactly when `X k j = C k j / (ω k - ν j)`
([golub2013matrix] §4.8.4 and (12.1.4)). -/
theorem sylvesterMap_diagonal_eq_iff {ω : m → K} {ν : n → K} (h : ∀ k j, ω k ≠ ν j)
    {X C : Matrix m n K} :
    sylvesterMap (diagonal ω) (diagonal ν) X = C ↔ X = of fun k j => C k j / (ω k - ν j) := by
  simp only [← Matrix.ext_iff, sylvesterMap_diagonal_apply, of_apply]
  refine forall_congr' fun k => forall_congr' fun j => ?_
  rw [eq_div_iff (sub_ne_zero.mpr (h k j)), mul_comm, eq_comm]

/-- **Cauchy-like matrices are determined entrywise by their generators** ([golub2013matrix]
(12.1.4)): if `ω k ≠ ν j` for all `k`, `j`, then `diagonal ω A - A diagonal ν = R Sᵀ` exactly when
`A k j = (R k ⬝ᵥ S j) / (ω k - ν j)` for all `k`, `j`. -/
theorem apply_eq_of_sylvesterMap_diagonal_eq {r : Type*} [Fintype r] {ω : m → K} {ν : n → K}
    (h : ∀ k j, ω k ≠ ν j) {A : Matrix m n K} {R : Matrix m r K} {S : Matrix n r K} :
    sylvesterMap (diagonal ω) (diagonal ν) A = R * Sᵀ ↔
      ∀ k j, A k j = (R k ⬝ᵥ S j) / (ω k - ν j) := by
  rw [sylvesterMap_diagonal_eq_iff h, ← Matrix.ext_iff]
  simp only [of_apply, mul_apply, transpose_apply, dotProduct]

end Field

/-- **Real matrices**: `A` and `B` have coprime characteristic polynomials exactly when their
complexifications have disjoint spectra. Coprimality is preserved and reflected by the field
extension `ℝ → ℂ`, over which it means "no common root". This is how a real Sylvester equation
between real Schur blocks is known to be uniquely solvable. -/
theorem isCoprime_charpoly_iff_disjoint_spectrum_complexify [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix n n ℝ) :
    IsCoprime A.charpoly B.charpoly ↔
      Disjoint (spectrum ℂ A.complexify) (spectrum ℂ B.complexify) := by
  rw [← isCoprime_charpoly_iff_disjoint_spectrum, charpoly_complexify, charpoly_complexify,
    isCoprime_map]

/-! ### Block diagonalization -/

section BlockDiagonal

variable {K : Type*} [Field K]

/-- Conjugation commutes with a simultaneous reindexing of rows and columns. -/
private theorem inv_mul_mul_submatrix_equiv {p : Type*} [Fintype p] [DecidableEq p]
    [DecidableEq n] (e : p ≃ n) (Y T : Matrix n n K) :
    (Y.submatrix e e)⁻¹ * T.submatrix e e * Y.submatrix e e = (Y⁻¹ * T * Y).submatrix e e := by
  rw [inv_submatrix_equiv, submatrix_mul_equiv, submatrix_mul_equiv]

/-- The two-block step of [golub2013matrix] Theorem 7.1.6 on a split `n = {p} ⊕ {¬p}`, combined
with a conjugation `Y₁` of the leading block: if `T` has no entry from the `¬p` rows into the `p`
columns and the Sylvester operator of the two diagonal blocks is surjective, then `T` is similar,
through the split, to `[Y₁⁻¹ T₁₁ Y₁ 0; 0 T₂₂]`. -/
private theorem exists_conj_submatrix_sumCompl [DecidableEq n] (p : n → Prop) [DecidablePred p]
    {T : Matrix n n K} (hT : ∀ i j, ¬p i → p j → T i j = 0)
    (hs : Function.Surjective
      (sylvesterMap (T.toSquareBlockProp p) (T.toSquareBlockProp fun i => ¬p i)))
    {Y₁ : Matrix {i // p i} {i // p i} K} (hY₁ : IsUnit Y₁) :
    ∃ Y : Matrix n n K, IsUnit Y ∧
      (Y⁻¹ * T * Y).submatrix (Equiv.sumCompl p) (Equiv.sumCompl p) =
        fromBlocks (Y₁⁻¹ * T.toSquareBlockProp p * Y₁) 0 0
          (T.toSquareBlockProp fun i => ¬p i) := by
  set e := Equiv.sumCompl p
  set T₁ := T.toSquareBlockProp p
  set T₂ := T.toSquareBlockProp fun i => ¬p i
  have hT' : T.submatrix e e = fromBlocks T₁ (T.toBlock p fun i => ¬p i) 0 T₂ := by
    ext (i | i) (j | j)
    · rfl
    · rfl
    · exact hT _ _ i.2 j.2
    · rfl
  obtain ⟨Z, -, hunit, hconj⟩ := exists_fromBlocks_conj_eq_fromBlocks_zero hs
    (T.toBlock p fun i => ¬p i)
  set V := fromBlocks (1 : Matrix {i // p i} {i // p i} K) Z (0 : Matrix {i // ¬p i} _ K)
    (1 : Matrix {i // ¬p i} {i // ¬p i} K)
  have hY₁' : Y₁⁻¹ * Y₁ = 1 := nonsing_inv_mul Y₁ ((isUnit_iff_isUnit_det Y₁).mp hY₁)
  set W := fromBlocks Y₁ (0 : Matrix {i // p i} {i // ¬p i} K) (0 : Matrix {i // ¬p i} _ K)
    (1 : Matrix {i // ¬p i} {i // ¬p i} K)
  have hWinv : fromBlocks Y₁⁻¹ 0 0 1 * W = 1 := by
    simp [W, fromBlocks_multiply, hY₁', fromBlocks_one]
  have hW : IsUnit W := (isUnit_iff_isUnit_det _).mpr (isUnit_det_of_left_inverse hWinv)
  have hWinv' : W⁻¹ = fromBlocks Y₁⁻¹ 0 0 1 := inv_eq_left_inv hWinv
  refine ⟨(V * W).submatrix e.symm e.symm, (isUnit_submatrix_equiv _ _).mpr (hunit.mul hW), ?_⟩
  have hTe : T = (T.submatrix e e).submatrix e.symm e.symm := by
    simp [submatrix_submatrix]
  rw [hTe, inv_mul_mul_submatrix_equiv, submatrix_submatrix, Equiv.symm_comp_self,
    submatrix_id_id, Matrix.mul_inv_rev, hT']
  calc W⁻¹ * V⁻¹ * fromBlocks T₁ (T.toBlock p fun i => ¬p i) 0 T₂ * (V * W)
      = W⁻¹ * (V⁻¹ * fromBlocks T₁ (T.toBlock p fun i => ¬p i) 0 T₂ * V) * W := by
        simp only [Matrix.mul_assoc]
    _ = fromBlocks (Y₁⁻¹ * T₁ * Y₁) 0 0 T₂ := by
        rw [hconj, hWinv']
        simp [W, fromBlocks_multiply]

/-- [golub2013matrix] Theorem 7.1.6 over any field: a block upper triangular matrix
(`T.BlockTriangular b`) whose diagonal blocks `T.toSquareBlock b k` have pairwise coprime
characteristic polynomials is similar to its block diagonal part. Induction on the size: the last
block is split off by `exists_fromBlocks_conj_eq_fromBlocks_zero` (its characteristic polynomial is
coprime to the product of the others, which is that of the leading part by
`Matrix.BlockTriangular.charpoly`), and the leading part is handled by the induction
hypothesis. -/
theorem exists_isUnit_conj_eq_blockDiagonalPart_of_isCoprime [DecidableEq n] {ι : Type*}
    [LinearOrder ι] {b : n → ι} {T : Matrix n n K} (hT : T.BlockTriangular b)
    (hcop : Pairwise fun k l : ι =>
      IsCoprime (T.toSquareBlock b k).charpoly (T.toSquareBlock b l).charpoly) :
    ∃ Y : Matrix n n K, IsUnit Y ∧
      Y⁻¹ * T * Y = of fun i j => if b i = b j then T i j else 0 := by
  induction hN : Fintype.card n using Nat.strong_induction_on generalizing n with
  | _ N ih =>
  by_cases hall : ∀ i j, b i = b j
  · refine ⟨1, isUnit_one, ?_⟩
    ext i j
    simp [hall i j]
  push Not at hall
  obtain ⟨i₀, j₀, hij⟩ := hall
  have hne : (Finset.univ : Finset n).Nonempty := ⟨i₀, Finset.mem_univ _⟩
  set k₀ := Finset.univ.sup' hne b with hk₀
  have hle : ∀ i, b i ≤ k₀ := fun i => Finset.le_sup' b (Finset.mem_univ i)
  obtain ⟨imax, -, himax⟩ := Finset.exists_mem_eq_sup' hne b
  set p : n → Prop := fun i => b i < k₀ with hp
  have hnp : ∀ i, ¬p i ↔ b i = k₀ := fun i => by
    simp only [hp, not_lt]; exact ⟨fun h => le_antisymm (hle i) h, fun h => h.ge⟩
  -- the leading part is smaller
  have hcard : Fintype.card {i // p i} < N := by
    rw [← hN]
    exact Fintype.card_subtype_lt (x := imax) (by rw [hnp]; exact himax.symm)
  set T₁ := T.toSquareBlockProp p
  set T₂ := T.toSquareBlockProp fun i => ¬p i
  have hT₁ : T₁.BlockTriangular (fun i => b i.1) := hT.submatrix
  -- the blocks of the leading part
  have hblock₁ : ∀ k, k < k₀ →
      (T₁.toSquareBlock (fun i => b i.1) k).charpoly = (T.toSquareBlock b k).charpoly := by
    intro k hk
    let f : {x : {i // p i} // b x.1 = k} ≃ {i // b i = k} :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun x => ⟨⟨x.1, by simp only [hp, x.2, hk]⟩, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← charpoly_reindex f]
    rfl
  have hempty₁ : ∀ k, ¬k < k₀ → (T₁.toSquareBlock (fun i => b i.1) k).charpoly = 1 := by
    intro k hk
    have : IsEmpty {x : {i // p i} // b x.1 = k} :=
      ⟨fun x => hk (x.2 ▸ x.1.2)⟩
    exact charpoly_isEmpty
  have hblock₂ : T₂.charpoly = (T.toSquareBlock b k₀).charpoly := by
    let f : {i // ¬p i} ≃ {i // b i = k₀} := Equiv.subtypeEquivRight hnp
    rw [← charpoly_reindex f]
    rfl
  -- coprimality of the two parts
  have hcop₁₂ : IsCoprime T₁.charpoly T₂.charpoly := by
    rw [hT₁.charpoly, hblock₂]
    refine IsCoprime.prod_left fun k _ => ?_
    by_cases hk : k < k₀
    · rw [hblock₁ k hk]
      exact hcop hk.ne
    · rw [hempty₁ k hk]
      exact isCoprime_one_left
  have hs := (sylvesterMap_bijective_of_isCoprime hcop₁₂).2
  -- the induction hypothesis on the leading part
  have hcop₁ : Pairwise fun k l : ι => IsCoprime (T₁.toSquareBlock (fun i => b i.1) k).charpoly
      (T₁.toSquareBlock (fun i => b i.1) l).charpoly := by
    intro k l hkl
    by_cases hk : k < k₀
    · by_cases hl : l < k₀
      · rw [hblock₁ k hk, hblock₁ l hl]; exact hcop hkl
      · rw [hempty₁ l hl]; exact isCoprime_one_right
    · rw [hempty₁ k hk]; exact isCoprime_one_left
  obtain ⟨Y₁, hY₁, hconj₁⟩ := ih _ hcard hT₁ hcop₁ rfl
  have hTz : ∀ i j, ¬p i → p j → T i j = 0 := fun i j hi hj =>
    hT (show b j < b i by rw [(hnp i).mp hi]; exact hj)
  obtain ⟨Y, hY, hconj⟩ := exists_conj_submatrix_sumCompl p hTz hs hY₁
  refine ⟨Y, hY, ?_⟩
  have key : (Y⁻¹ * T * Y).submatrix (Equiv.sumCompl p) (Equiv.sumCompl p) =
      (of fun i j => if b i = b j then T i j else 0).submatrix (Equiv.sumCompl p)
        (Equiv.sumCompl p) := by
    rw [hconj, hconj₁]
    ext (i | i) (j | j)
    · rfl
    · have hj := (hnp j.1).mp j.2
      simp [(show b i.1 ≠ b j.1 by rw [hj]; exact i.2.ne)]
    · have hi := (hnp i.1).mp i.2
      simp [(show b i.1 ≠ b j.1 by rw [hi]; exact j.2.ne')]
    · have hi := (hnp i.1).mp i.2
      have hj := (hnp j.1).mp j.2
      simp [toSquareBlockProp_def, hi, hj]
  have := congrArg (fun M => M.submatrix (Equiv.sumCompl p).symm (Equiv.sumCompl p).symm) key
  simpa [submatrix_submatrix] using this

/-- [golub2013matrix] Theorem 7.1.6 (block diagonal decomposition): over an algebraically closed
field, a block upper triangular matrix whose diagonal blocks have pairwise disjoint spectra is
similar to its block diagonal part, `Y⁻¹ T Y = diag(T₁₁, …, T_qq)`. -/
theorem exists_isUnit_conj_eq_blockDiagonalPart [DecidableEq n] [IsAlgClosed K] {ι : Type*}
    [LinearOrder ι] {b : n → ι} {T : Matrix n n K} (hT : T.BlockTriangular b)
    (hdisj : Pairwise fun k l : ι =>
      Disjoint (spectrum K (T.toSquareBlock b k)) (spectrum K (T.toSquareBlock b l))) :
    ∃ Y : Matrix n n K, IsUnit Y ∧
      Y⁻¹ * T * Y = of fun i j => if b i = b j then T i j else 0 :=
  exists_isUnit_conj_eq_blockDiagonalPart_of_isCoprime hT fun _ _ hkl =>
    (isCoprime_charpoly_iff_disjoint_spectrum _ _).mpr (hdisj hkl)

end BlockDiagonal

/-! ### The separation -/

section Sep

open scoped Matrix.Norms.Frobenius

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The **separation** of two square matrices ([golub2013matrix] (7.2.5)):
`sep A B = min_{‖X‖_F = 1} ‖A X - X B‖_F`, the least value of the Frobenius norm of the Sylvester
operator on the Frobenius unit sphere of `m × n` matrices. The value is `0` when `m` or `n` is
empty (an infimum over an empty family). -/
noncomputable def sep (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) : ℝ :=
  ⨅ X : {X : Matrix m n 𝕜 // ‖X‖ = 1}, ‖A * X.1 - X.1 * B‖

variable {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}

/-- The separation is nonnegative. -/
theorem sep_nonneg (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) : 0 ≤ sep A B :=
  Real.iInf_nonneg fun _ => norm_nonneg _

private theorem bddBelow_range_sep (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) :
    BddBelow (Set.range fun X : {X : Matrix m n 𝕜 // ‖X‖ = 1} => ‖A * X.1 - X.1 * B‖) :=
  ⟨0, by rintro _ ⟨X, rfl⟩; exact norm_nonneg _⟩

/-- The separation is at most the value at any unit matrix. -/
theorem sep_le_norm {X : Matrix m n 𝕜} (hX : ‖X‖ = 1) : sep A B ≤ ‖A * X - X * B‖ :=
  ciInf_le (bddBelow_range_sep A B) ⟨X, hX⟩

/-- A lower bound of `‖A X - X B‖` on the unit sphere is a lower bound of the separation, when the
sphere is nonempty. -/
theorem le_sep {c : ℝ} [Nonempty m] [Nonempty n]
    (h : ∀ X : Matrix m n 𝕜, ‖X‖ = 1 → c ≤ ‖A * X - X * B‖) : c ≤ sep A B := by
  have : Nonempty {X : Matrix m n 𝕜 // ‖X‖ = 1} :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).elim fun X hX =>
      ⟨⟨X, mem_sphere_zero_iff_norm.mp hX⟩⟩
  exact le_ciInf fun X => h X.1 X.2

/-- On an empty unit sphere (when `m` or `n` is empty) the separation is `0`. -/
theorem sep_of_isEmpty [IsEmpty {X : Matrix m n 𝕜 // ‖X‖ = 1}] : sep A B = 0 :=
  Real.iInf_of_isEmpty _

/-- The unit sphere of `m × n` matrices is empty unless both `m` and `n` are nonempty; this is the
case split behind the statements that need no nonemptiness hypothesis. -/
private theorem isEmpty_or_nonempty_index :
    IsEmpty {X : Matrix m n 𝕜 // ‖X‖ = 1} ∨ (Nonempty m ∧ Nonempty n) := by
  rcases isEmpty_or_nonempty m with hm | hm
  · left
    exact ⟨fun X => by
      have : X.1 = 0 := Matrix.ext fun i _ => (IsEmpty.false i).elim
      simpa [this] using X.2⟩
  rcases isEmpty_or_nonempty n with hn | hn
  · left
    exact ⟨fun X => by
      have : X.1 = 0 := Matrix.ext fun _ j => (IsEmpty.false j).elim
      simpa [this] using X.2⟩
  exact Or.inr ⟨hm, hn⟩

/-- **The separation is the best constant** in `sep A B ‖X‖_F ≤ ‖A X - X B‖_F`, the book's
`min_{X ≠ 0} ‖A X - X B‖_F / ‖X‖_F` form of (7.2.5). -/
theorem sep_mul_norm_le (X : Matrix m n 𝕜) : sep A B * ‖X‖ ≤ ‖A * X - X * B‖ := by
  rcases eq_or_ne X 0 with rfl | hX
  · simp
  have hn : 0 < ‖X‖ := norm_pos_iff.mpr hX
  have hY : ‖((‖X‖⁻¹ : ℝ) : 𝕜) • X‖ = 1 := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have h := sep_le_norm (A := A) (B := B) hY
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, norm_smul, RCLike.norm_ofReal,
    abs_of_pos (inv_pos.mpr hn)] at h
  calc sep A B * ‖X‖ ≤ ‖X‖⁻¹ * ‖A * X - X * B‖ * ‖X‖ := by gcongr
    _ = ‖A * X - X * B‖ := by field_simp

/-- **The minimum is attained**: for nonempty `m`, `n` some unit matrix realizes the separation
(the Frobenius unit sphere is compact). -/
theorem exists_sep_eq [Nonempty m] [Nonempty n] (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) :
    ∃ X : Matrix m n 𝕜, ‖X‖ = 1 ∧ ‖A * X - X * B‖ = sep A B := by
  have hc : Continuous fun X : Matrix m n 𝕜 => ‖A * X - X * B‖ :=
    (sylvesterMap A B).continuous_of_finiteDimensional.norm
  obtain ⟨X, hX, hmin⟩ := (isCompact_sphere (0 : Matrix m n 𝕜) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hc.continuousOn
  rw [mem_sphere_zero_iff_norm] at hX
  refine ⟨X, hX, le_antisymm ?_ (sep_le_norm hX)⟩
  exact le_sep fun Y hY => hmin (mem_sphere_zero_iff_norm.mpr hY)

/-- A matrix `X ≠ 0` on which the Sylvester operator acts as the scalar `c` bounds the separation
by `‖c‖`. -/
theorem sep_le_norm_of_sylvesterMap_eq_smul {X : Matrix m n 𝕜} (hX : X ≠ 0) {c : 𝕜}
    (h : A * X - X * B = c • X) : sep A B ≤ ‖c‖ := by
  have := sep_mul_norm_le (A := A) (B := B) X
  rw [h, norm_smul] at this
  exact le_of_mul_le_mul_right this (norm_pos_iff.mpr hX)

/-- **Positivity**: for nonempty `m`, `n` the separation is positive exactly when the Sylvester
operator is injective. -/
theorem sep_pos_iff [Nonempty m] [Nonempty n] :
    0 < sep A B ↔ Function.Injective (sylvesterMap A B) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  constructor
  · intro h X hX
    have := sep_mul_norm_le (A := A) (B := B) X
    rw [← sylvesterMap_apply, hX, norm_zero] at this
    exact norm_eq_zero.mp (le_antisymm (nonpos_of_mul_nonpos_right this h) (norm_nonneg _))
  · intro h
    obtain ⟨X, hX, hXeq⟩ := exists_sep_eq A B
    refine (sep_nonneg A B).lt_of_ne fun h0 => ?_
    rw [← h0, norm_eq_zero, ← sylvesterMap_apply] at hXeq
    simp [h X hXeq] at hX

/-- Over an algebraically closed `RCLike` field (that is, `ℂ`), the separation is positive exactly
when the spectra are disjoint ([golub2013matrix] §7.2.4). -/
theorem sep_pos_iff_disjoint_spectrum [IsAlgClosed 𝕜] [DecidableEq m] [DecidableEq n]
    [Nonempty m] [Nonempty n] : 0 < sep A B ↔ Disjoint (spectrum 𝕜 A) (spectrum 𝕜 B) := by
  rw [sep_pos_iff, ← sylvesterMap_bijective_iff_disjoint_spectrum]
  exact ⟨fun h => ⟨h, LinearMap.injective_iff_surjective.mp h⟩, fun h => h.1⟩

/-- **The separation bounds solutions** of the Sylvester equation ([golub2013matrix] (7.3.20)):
`‖X‖_F ≤ ‖A X - X B‖_F / sep A B` when `sep A B > 0`. -/
theorem frobenius_norm_le_div_sep (h : 0 < sep A B) (X : Matrix m n 𝕜) :
    ‖X‖ ≤ ‖A * X - X * B‖ / sep A B := by
  rw [le_div_iff₀ h, mul_comm]
  exact sep_mul_norm_le X

/-- **The separation is at most the distance between eigenvalues** ([golub2013matrix] P7.2.10):
for `α ∈ σ(A)` and `β ∈ σ(B)`, `sep A B ≤ |α - β|`; the rank-one `X = x yᵀ` built from a right
eigenvector of `A` and a left eigenvector of `B` has `A X - X B = (α - β) X`. -/
theorem sep_le_norm_sub [DecidableEq m] [DecidableEq n] {α β : 𝕜} (hα : α ∈ spectrum 𝕜 A)
    (hβ : β ∈ spectrum 𝕜 B) : sep A B ≤ ‖α - β‖ := by
  obtain ⟨x, hx, hxA⟩ := (mem_spectrum_iff_exists_mulVec_eq_smul A α).mp hα
  obtain ⟨y, hy, hyB⟩ := exists_vecMul_eq_smul_of_mem_spectrum hβ
  refine sep_le_norm_of_sylvesterMap_eq_smul (X := vecMulVec x y) ?_
    (sylvesterMap_vecMulVec hxA hyB)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy
  intro h0
  have := congrFun (congrFun h0 i) j
  rw [vecMulVec_apply, zero_apply] at this
  exact mul_ne_zero hi hj this

/-- **Unitary invariance** of the separation: `sep (Uᴴ A U) (Vᴴ B V) = sep A B` for unitary `U`,
`V` (`X ↦ U X Vᴴ` is a Frobenius isometry of the unit sphere). -/
theorem sep_unitary_conj [DecidableEq m] [DecidableEq n] {U : Matrix m m 𝕜} {V : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup m 𝕜) (hV : V ∈ unitaryGroup n 𝕜) (A : Matrix m m 𝕜)
    (B : Matrix n n 𝕜) : sep (star U * A * U) (star V * B * V) = sep A B := by
  have hU' : U * star U = 1 := mem_unitaryGroup_iff.mp hU
  have hV' : V * star V = 1 := mem_unitaryGroup_iff.mp hV
  have hsU : star U ∈ unitaryGroup m 𝕜 := Unitary.star_mem hU
  have hsV : star V ∈ unitaryGroup n 𝕜 := Unitary.star_mem hV
  have hsU' : star U * U = 1 := mem_unitaryGroup_iff'.mp hU
  have hsV' : star V * V = 1 := mem_unitaryGroup_iff'.mp hV
  let e : {X : Matrix m n 𝕜 // ‖X‖ = 1} ≃ {X : Matrix m n 𝕜 // ‖X‖ = 1} :=
    { toFun := fun X => ⟨U * X.1 * star V, by
        rw [frobenius_norm_unitary_mul_mul_unitary hU _ hsV, X.2]⟩
      invFun := fun X => ⟨star U * X.1 * V, by
        rw [frobenius_norm_unitary_mul_mul_unitary hsU _ hV, X.2]⟩
      left_inv := fun X => Subtype.ext <| by
        simp only [← Matrix.mul_assoc, hsU', Matrix.one_mul]
        rw [Matrix.mul_assoc, hsV', Matrix.mul_one]
      right_inv := fun X => Subtype.ext <| by
        simp only [← Matrix.mul_assoc, hU', Matrix.one_mul]
        rw [Matrix.mul_assoc, hV', Matrix.mul_one] }
  refine Equiv.iInf_congr e fun X => ?_
  change ‖A * (U * X.1 * star V) - U * X.1 * star V * B‖ = _
  have : A * (U * X.1 * star V) - U * X.1 * star V * B =
      U * (star U * A * U * X.1 - X.1 * (star V * B * V)) * star V := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, hU', Matrix.one_mul]
    rw [Matrix.mul_assoc (U * X.1 * star V * B) V (star V), hV', Matrix.mul_one]
  rw [this, frobenius_norm_unitary_mul_mul_unitary hU _ hsV]

/-- **Perturbation**: `sep A B - ‖E‖_F - ‖F‖_F ≤ sep (A + E) (B + F)` — the separation is
1-Lipschitz in each argument for the Frobenius norm. -/
theorem sep_sub_le_sep_add (A E : Matrix m m 𝕜) (B F : Matrix n n 𝕜) :
    sep A B - ‖E‖ - ‖F‖ ≤ sep (A + E) (B + F) := by
  rcases isEmpty_or_nonempty_index (m := m) (n := n) (𝕜 := 𝕜) with h | ⟨hm, hn⟩
  · rw [sep_of_isEmpty, sep_of_isEmpty]
    linarith [norm_nonneg E, norm_nonneg F]
  refine le_sep fun X hX => ?_
  have h1 := sep_le_norm (A := A) (B := B) hX
  have : A * X - X * B = ((A + E) * X - X * (B + F)) - E * X + X * F := by
    simp only [Matrix.add_mul, Matrix.mul_add]; abel
  rw [this] at h1
  have hEX := frobenius_norm_mul E X
  have hXF := frobenius_norm_mul X F
  rw [hX] at hEX hXF
  linarith [norm_add_le (((A + E) * X - X * (B + F)) - E * X) (X * F),
    norm_sub_le ((A + E) * X - X * (B + F)) (E * X)]

/-! ### Symmetry of the separation -/

/-- **Cauchy–Schwarz for the Frobenius pairing**: `re tr(Yᴴ X) ≤ ‖Y‖_F ‖X‖_F`. The pairing is the
inner product of `PiLp 2 (fun _ : m => EuclideanSpace 𝕜 n)`, whose norm is the Frobenius norm. -/
theorem re_trace_conjTranspose_mul_le (Y X : Matrix m n 𝕜) :
    RCLike.re (trace (Yᴴ * X)) ≤ ‖Y‖ * ‖X‖ := by
  let Φ : Matrix m n 𝕜 → PiLp 2 (fun _ : m => EuclideanSpace 𝕜 n) :=
    fun X => WithLp.toLp 2 fun i => WithLp.toLp 2 (X i)
  have hΦ : ∀ X, ‖Φ X‖ = ‖X‖ := fun X => rfl
  have hinner : inner 𝕜 (Φ Y) (Φ X) = trace (Yᴴ * X) := by
    simp only [Φ, PiLp.inner_apply, RCLike.inner_apply, trace, diag_apply, mul_apply,
      conjTranspose_apply, RCLike.star_def]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [← hinner, ← hΦ Y, ← hΦ X]
  exact re_inner_le_norm _ _

/-- The Frobenius adjoint of the Sylvester operator: `tr(Yᴴ (A X - X B)) = tr((Aᴴ Y - Y Bᴴ)ᴴ X)`. -/
theorem trace_conjTranspose_mul_sylvesterMap (A : Matrix m m 𝕜) (B : Matrix n n 𝕜)
    (X Y : Matrix m n 𝕜) :
    trace (Yᴴ * (A * X - X * B)) = trace ((Aᴴ * Y - Y * Bᴴ)ᴴ * X) := by
  simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_sub,
    Matrix.sub_mul, trace_sub, Matrix.mul_assoc]
  rw [trace_mul_comm B, Matrix.mul_assoc]

/-- **A lower bound passes to the adjoint**: if `c ‖X‖_F ≤ ‖A X - X B‖_F` for every `X`, then
`c ‖Y‖_F ≤ ‖Aᴴ Y - Y Bᴴ‖_F` for every `Y`. For `c > 0` the Sylvester operator is injective, hence
onto; writing `Y = A X - X B`, `‖Y‖² = re tr((Aᴴ Y - Y Bᴴ)ᴴ X) ≤ ‖Aᴴ Y - Y Bᴴ‖ ‖X‖` and
`‖X‖ ≤ ‖Y‖ / c`. -/
theorem le_norm_sylvesterMap_conjTranspose_of_le {c : ℝ}
    (h : ∀ X : Matrix m n 𝕜, c * ‖X‖ ≤ ‖A * X - X * B‖) (Y : Matrix m n 𝕜) :
    c * ‖Y‖ ≤ ‖Aᴴ * Y - Y * Bᴴ‖ := by
  rcases le_or_gt c 0 with hc | hc
  · exact (mul_nonpos_of_nonpos_of_nonneg hc (norm_nonneg _)).trans (norm_nonneg _)
  have hinj : Function.Injective (sylvesterMap A B) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    have := h X
    rw [← sylvesterMap_apply, hX, norm_zero] at this
    exact norm_eq_zero.mp (le_antisymm (nonpos_of_mul_nonpos_right this hc) (norm_nonneg _))
  obtain ⟨X, rfl⟩ := LinearMap.injective_iff_surjective.mp hinj Y
  rw [sylvesterMap_apply]
  set Y := A * X - X * B with hY
  have hsq : ‖Y‖ ^ 2 = RCLike.re (trace (Yᴴ * Y)) := by
    rw [← frobenius_norm_sq_eq_trace, RCLike.ofReal_re]
  have hcs : ‖Y‖ ^ 2 ≤ ‖Aᴴ * Y - Y * Bᴴ‖ * ‖X‖ := by
    rw [hsq]
    conv_lhs => rw [hY, trace_conjTranspose_mul_sylvesterMap, ← hY]
    exact re_trace_conjTranspose_mul_le _ _
  have hX := h X
  rw [← hY] at hX
  rcases (norm_nonneg Y).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  have : c * ‖Y‖ ^ 2 ≤ ‖Aᴴ * Y - Y * Bᴴ‖ * ‖Y‖ := by
    calc c * ‖Y‖ ^ 2 ≤ c * (‖Aᴴ * Y - Y * Bᴴ‖ * ‖X‖) := by gcongr
      _ = ‖Aᴴ * Y - Y * Bᴴ‖ * (c * ‖X‖) := by ring
      _ ≤ ‖Aᴴ * Y - Y * Bᴴ‖ * ‖Y‖ := by gcongr
  nlinarith

/-- `sep Aᴴ Bᴴ = sep B A`: `X ↦ Xᴴ` maps the unit sphere of `m × n` matrices onto that of `n × m`
matrices and `Aᴴ Xᴴ - Xᴴ Bᴴ = -(B X - X A)ᴴ`. -/
theorem sep_conjTranspose (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) : sep Aᴴ Bᴴ = sep B A := by
  let e : {Z : Matrix n m 𝕜 // ‖Z‖ = 1} ≃ {X : Matrix m n 𝕜 // ‖X‖ = 1} :=
    { toFun := fun Z => ⟨Z.1ᴴ, by rw [frobenius_norm_conjTranspose, Z.2]⟩
      invFun := fun X => ⟨X.1ᴴ, by rw [frobenius_norm_conjTranspose, X.2]⟩
      left_inv := fun Z => Subtype.ext (conjTranspose_conjTranspose _)
      right_inv := fun X => Subtype.ext (conjTranspose_conjTranspose _) }
  refine (Equiv.iInf_congr e fun Z => ?_).symm
  change ‖Aᴴ * Z.1ᴴ - Z.1ᴴ * Bᴴ‖ = ‖B * Z.1 - Z.1 * A‖
  rw [← conjTranspose_mul, ← conjTranspose_mul, ← conjTranspose_sub,
    frobenius_norm_conjTranspose, norm_sub_rev]

private theorem sep_le_sep_conjTranspose (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) :
    sep A B ≤ sep Aᴴ Bᴴ := by
  rcases isEmpty_or_nonempty_index (m := m) (n := n) (𝕜 := 𝕜) with h | ⟨hm, hn⟩
  · rw [sep_of_isEmpty, sep_of_isEmpty]
  refine le_sep fun Y hY => ?_
  have := le_norm_sylvesterMap_conjTranspose_of_le (A := A) (B := B) sep_mul_norm_le Y
  rwa [hY, mul_one] at this

/-- **The separation is symmetric**: `sep A B = sep B A`. The operator `P ↦ P A - B P`, whose
inverse the perturbation theory of invariant subspaces bounds, is therefore controlled by the
book's `sep(A, B)` ([golub2013matrix] (7.2.5) and the proof of Theorem 7.2.4). -/
theorem sep_comm (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) : sep A B = sep B A :=
  le_antisymm ((sep_le_sep_conjTranspose A B).trans_eq (sep_conjTranspose A B))
    ((sep_le_sep_conjTranspose B A).trans_eq (sep_conjTranspose B A))

/-! ### Diagonal and Hermitian arguments -/

/-- The separation of two diagonal matrices is the least distance between their diagonal
entries. -/
theorem sep_diagonal [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n] (a : m → 𝕜)
    (b : n → 𝕜) : sep (diagonal a) (diagonal b) = ⨅ i, ⨅ j, ‖a i - b j‖ := by
  have hbdd : ∀ i, BddBelow (Set.range fun j => ‖a i - b j‖) :=
    fun i => ⟨0, by rintro _ ⟨j, rfl⟩; exact norm_nonneg _⟩
  have hbdd' : BddBelow (Set.range fun i => ⨅ j, ‖a i - b j‖) :=
    ⟨0, by rintro _ ⟨i, rfl⟩; exact Real.iInf_nonneg fun _ => norm_nonneg _⟩
  set δ := ⨅ i, ⨅ j, ‖a i - b j‖ with hδ
  have hδle : ∀ i j, δ ≤ ‖a i - b j‖ := fun i j =>
    (ciInf_le hbdd' i).trans (ciInf_le (hbdd i) j)
  have hδ0 : 0 ≤ δ := Real.iInf_nonneg fun _ => Real.iInf_nonneg fun _ => norm_nonneg _
  refine le_antisymm ?_ (le_sep fun X hX => ?_)
  · obtain ⟨i⟩ := ‹Nonempty m›
    refine le_ciInf fun i => le_ciInf fun j => ?_
    refine sep_le_norm_of_sylvesterMap_eq_smul (X := single i j 1) ?_ ?_
    · intro h0
      simpa using congrFun (congrFun h0 i) j
    · ext k l
      rw [← sylvesterMap_apply, sylvesterMap_diagonal_apply, smul_apply, single_apply,
        smul_eq_mul]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        ring
      · simp
  · have hsq : δ ^ 2 ≤ ‖diagonal a * X - X * diagonal b‖ ^ 2 := by
      rw [frobenius_norm_sq_eq_sum_sq]
      calc δ ^ 2 = δ ^ 2 * ‖X‖ ^ 2 := by rw [hX, one_pow, mul_one]
        _ = ∑ i, ∑ j, δ ^ 2 * ‖X i j‖ ^ 2 := by
          rw [frobenius_norm_sq_eq_sum_sq, Finset.mul_sum]
          simp only [Finset.mul_sum]
        _ ≤ _ := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [← sylvesterMap_apply, sylvesterMap_diagonal_apply, norm_mul, mul_pow]
          gcongr
          exact hδle i j
    exact (pow_le_pow_iff_left₀ hδ0 (norm_nonneg _) two_ne_zero).mp hsq

/-- **The separation of two Hermitian matrices is the distance between their spectra**
([golub2013matrix] P8.1.9, the step of Theorem 8.1.10):
`sep A B = min_{i,j} |λ_i(A) - λ_j(B)|`. Both are unitarily diagonalizable
(`Matrix.IsHermitian.spectral_theorem`), the separation is unitarily invariant, and for diagonal
matrices it is the least distance between the diagonal entries. -/
theorem IsHermitian.sep_eq_iInf_abs_eigenvalues_sub [DecidableEq m] [DecidableEq n]
    [Nonempty m] [Nonempty n] (hA : A.IsHermitian) (hB : B.IsHermitian) :
    sep A B = ⨅ i, ⨅ j, |hA.eigenvalues i - hB.eigenvalues j| := by
  have hA' := hA.conjStarAlgAut_star_eigenvectorUnitary
  have hB' := hB.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at hA' hB'
  rw [← sep_unitary_conj hA.eigenvectorUnitary.2 hB.eigenvectorUnitary.2, hA', hB',
    sep_diagonal]
  simp only [Function.comp_apply, ← RCLike.ofReal_sub, RCLike.norm_ofReal]

end Sep

end Matrix
