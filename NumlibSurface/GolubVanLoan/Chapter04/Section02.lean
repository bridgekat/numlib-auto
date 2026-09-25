import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.HermitianPart
import NumlibSurface.GolubVanLoan.Chapter04.Section01

/-!
# Golub–Van Loan §4.2: positive definite systems

Surface file for [golub2013matrix] §4.2: positive definiteness of a general (unsymmetric) matrix
(Theorems 4.2.1–4.2.5 with Corollaries 4.2.2 and 4.2.4), the Cholesky factorization (Theorem
4.2.7) and gaxpy Cholesky (Algorithm 4.2.1) with its rounding bridge, the facts of §4.2.6 on the
stability of the Cholesky process, the pivoted outer-product `L D Lᵀ` (Algorithm 4.2.2, (4.2.10)),
the semidefinite case (Theorem 4.2.8, (4.2.11), (4.2.17)), and the block equations of block
Cholesky ((4.2.18)–(4.2.19)).

## Conventions

Real square matrices, 0-based. "Positive definite" for a general matrix is the surface predicate
`IsPositiveDefinite A` (`xᵀAx > 0` for `x ≠ 0`, no symmetry), which is positive definiteness of
the symmetric part `T = (A + Aᵀ)/2 = Matrix.hermitianPart A` (`isPositiveDefinite_iff`);
"symmetric positive (semi)definite" is Mathlib's `Matrix.PosDef` / `Matrix.PosSemidef`. The book's
lower Cholesky factor `G` is the backbone's `Matrix.cholesky A` (whose transpose is the upper factor
of `Matrix.IsCholesky`). `‖·‖₂` is the scoped `Matrix.Norms.L2Operator` norm and `κ₂` the backbone's
`Matrix.condNumberLp 2`. A permutation `P` acts as `A.submatrix σ σ = P A Pᵀ`.

Algorithm 4.2.1 follows the algorithm conventions of `NumlibSurface/GolubVanLoan`: the gaxpy
`A(j:n, j) − A(j:n, 1:j−1) · A(j, 1:j−1)ᵀ` is a running difference from the entry of `A`
(chapter 4's `runningDiff`), the square root is `Real.sqrt` followed by one rounding, and the
whole column, diagonal included, is divided by the rounded square root, so the computed diagonal
is `fl(t / fl(√t))` — the operation order of the backbone relation
`FloatingPoint.RoundsCholeskyDiv`.

## Sources

Backbone `Numlib/LinearAlgebra/Matrix/{HermitianPart,Cholesky}`,
`Numlib/Analysis/Matrix/OperatorNorm`, `Numlib/FloatingPoint/LU`. The exact semantics of
Algorithm 4.2.1 is the backbone recurrence `Matrix.cholesky` for *every* input (off the positive
definite cone both compute the same junk: `√` of a negative number is `0` and `x / 0 = 0`).

## Not formalized here

§4.2.4 (matrix square roots, chapter 9), §4.2.10 (packed formats), the flop counts, the numerical
example `[ε m; −m ε]`, Wilkinson's completion criterion `q_n u κ₂(A) ≤ 1` and the numerical-rank
threshold (§4.2.8), which the book quotes without derivation.
-/

open FloatingPoint Matrix Finset

namespace GolubVanLoan.Chapter04

variable {n : ℕ}

/-! ### §4.2.1–4.2.2 Positive definiteness of a general matrix -/

/-- **§4.2, positive definite.** "A matrix `A ∈ ℝⁿˣⁿ` is positive definite if `xᵀAx > 0` for all
nonzero `x ∈ ℝⁿ`" — no symmetry is assumed. -/
def IsPositiveDefinite {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)

/-- **§4.2.2**: "the positive definiteness of a general matrix `A` is inherited from its symmetric
part `T = (A + Aᵀ)/2`" (`xᵀSx = 0` for the skew-symmetric part `S`). -/
theorem isPositiveDefinite_iff {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) :
    IsPositiveDefinite A ↔ (hermitianPart A).PosDef := by
  rw [posDef_hermitianPart_iff_forall_dotProduct_mulVec_pos]
  simp [IsPositiveDefinite]

/-- For a symmetric matrix the surface's positive definiteness is Mathlib's `Matrix.PosDef`. -/
theorem isPositiveDefinite_iff_posDef {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ}
    (hA : A.IsSymm) : IsPositiveDefinite A ↔ A.PosDef := by
  have h : hermitianPart A = A := by
    ext i j
    simp only [hermitianPart_apply, starRingEnd_apply, star_trivial, hA.apply i j]
    ring
  rw [isPositiveDefinite_iff, h]

/-- **Theorem 4.2.1.** "If `A ∈ ℝⁿˣⁿ` is positive definite and `X ∈ ℝⁿˣᵏ` has rank `k`, then
`B = XᵀAX ∈ ℝᵏˣᵏ` is also positive definite." -/
theorem theorem_4_2_1 {k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsPositiveDefinite A)
    {X : Matrix (Fin n) (Fin k) ℝ} (hX : X.rank = k) : IsPositiveDefinite (Xᵀ * A * X) := by
  have hinj : Function.Injective X.mulVec := by
    have h1 := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
    rw [Module.finrank_fin_fun] at h1
    have h2 : Module.finrank ℝ (LinearMap.ker X.mulVecLin) = 0 := by
      have : X.rank = Module.finrank ℝ (LinearMap.range X.mulVecLin) := rfl
      omega
    rw [Submodule.finrank_eq_zero, LinearMap.ker_eq_bot, coe_mulVecLin] at h2
    exact h2
  intro z hz
  have hXz : X *ᵥ z ≠ 0 := fun h => hz (hinj (by rw [h, mulVec_zero]))
  have := hA _ hXz
  rwa [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- **Corollary 4.2.2.** "If `A` is positive definite, then all its principal submatrices are
positive definite. In particular, all the diagonal entries are positive." A principal submatrix
`A(v, v)` is `A.submatrix e e` for an injective `e`. -/
theorem corollary_4_2_2 {k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsPositiveDefinite A)
    {e : Fin k → Fin n} (he : Function.Injective e) :
    IsPositiveDefinite (A.submatrix e e) ∧ ∀ i, 0 < A i i := by
  refine ⟨?_, fun i => ?_⟩
  · rw [isPositiveDefinite_iff, hermitianPart_submatrix]
    exact ((isPositiveDefinite_iff A).1 hA).submatrix he
  · have := hA (Pi.single i 1) (by simp)
    simpa [mulVec, dotProduct, Pi.single_apply] using this

/-- **Theorem 4.2.3.** "The matrix `A ∈ ℝⁿˣⁿ` is positive definite if and only if the symmetric
matrix `T = (A + Aᵀ)/2` has positive eigenvalues." -/
theorem theorem_4_2_3 (A : Matrix (Fin n) (Fin n) ℝ) :
    IsPositiveDefinite A ↔ ∀ i, 0 < (hermitianPart_isHermitian A).eigenvalues i :=
  (isPositiveDefinite_iff A).trans (hermitianPart_isHermitian A).posDef_iff_eigenvalues_pos

/-- **Corollary 4.2.4.** "If `A` is positive definite, then it has an LU factorization and the
diagonal entries of `U` are positive." -/
theorem corollary_4_2_4 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsPositiveDefinite A) :
    ∃ L U, IsLU A L U ∧ ∀ i, 0 < U i i := by
  simpa using exists_isLU_of_posDef_hermitianPart ((isPositiveDefinite_iff A).1 hA)

/-- A matrix with `Mᵀ = -M` has a vanishing quadratic form. -/
private theorem dotProduct_mulVec_eq_zero_of_transpose_eq_neg {ι : Type*} [Fintype ι]
    {M : Matrix ι ι ℝ} (hM : Mᵀ = -M) (x : ι → ℝ) : x ⬝ᵥ (M *ᵥ x) = 0 := by
  have h : x ⬝ᵥ (M *ᵥ x) = -(x ⬝ᵥ (M *ᵥ x)) := by
    conv_lhs => rw [dotProduct_mulVec, ← mulVec_transpose, hM, neg_mulVec, neg_dotProduct,
      dotProduct_comm]
  linarith

/-- The quadratic form of a rank-one matrix: `zᵀ (a bᵀ) z = (zᵀa)(bᵀz)`. -/
private theorem dotProduct_vecMulVec_mulVec (a b z : Fin n → ℝ) :
    z ⬝ᵥ (vecMulVec a b *ᵥ z) = (z ⬝ᵥ a) * (b ⬝ᵥ z) := by
  rw [dotProduct, dotProduct, dotProduct, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [vecMulVec_apply]; ring

/-- The matrix `A = [α vᵀ; v B] + [0 −wᵀ; w C]` of Theorem 4.2.5, on `Fin 1 ⊕ Fin n`. -/
abbrev blockPD (α : ℝ) (v w : Fin n → ℝ) (B C : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℝ :=
  fromBlocks (of fun _ _ => α) (replicateRow (Fin 1) v) (replicateCol (Fin 1) v) B +
    fromBlocks 0 (-replicateRow (Fin 1) w) (replicateCol (Fin 1) w) C

/-- The quadratic form of the matrix of Theorem 4.2.5 at `[μ; z]`: the skew-symmetric part
contributes nothing. -/
private theorem quad_blockPD {α μ : ℝ} {v w z : Fin n → ℝ} {B C : Matrix (Fin n) (Fin n) ℝ}
    (hC : Cᵀ = -C) :
    Sum.elim (fun _ : Fin 1 => μ) z ⬝ᵥ (blockPD α v w B C *ᵥ Sum.elim (fun _ => μ) z) =
      μ * μ * α + 2 * μ * (v ⬝ᵥ z) + z ⬝ᵥ (B *ᵥ z) := by
  have hskew : (fromBlocks 0 (-replicateRow (Fin 1) w) (replicateCol (Fin 1) w) C)ᵀ =
      -fromBlocks 0 (-replicateRow (Fin 1) w) (replicateCol (Fin 1) w) C := by
    rw [fromBlocks_transpose, fromBlocks_neg, transpose_replicateCol, transpose_neg,
      transpose_replicateRow, hC]
    simp
  rw [blockPD, add_mulVec, dotProduct_add, dotProduct_mulVec_eq_zero_of_transpose_eq_neg hskew,
    add_zero, fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  have h1 : (replicateRow (Fin 1) v *ᵥ z) = fun _ => v ⬝ᵥ z := rfl
  have h2 : (replicateCol (Fin 1) v *ᵥ fun _ : Fin 1 => μ) = μ • v := by
    ext i; simp [mulVec, dotProduct, mul_comm]
  have e1 : (fun _ : Fin 1 => μ) ⬝ᵥ ((of fun _ _ => α : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
      fun _ => μ) = μ * μ * α := by
    simp [dotProduct, mulVec]; ring
  have e2 : (fun _ : Fin 1 => μ) ⬝ᵥ (fun _ => v ⬝ᵥ z) = μ * (v ⬝ᵥ z) := by simp [dotProduct]
  rw [h1, h2, dotProduct_add, e1, e2]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm z v]
  ring

/-- **Theorem 4.2.5** with (4.2.1)–(4.2.3). "Suppose `A = [α vᵀ; v B] + [0 −wᵀ; w C]` is positive
definite and that `B` is symmetric and `C` is skew-symmetric. Then
`A = [1 0; (v+w)/α I] [α (v−w)ᵀ; 0 B₁ + C₁]` (4.2.1) where `B₁ = B − (vvᵀ − wwᵀ)/α` (4.2.2) is
symmetric positive definite and `C₁ = C − (wvᵀ − vwᵀ)/α` (4.2.3) is skew-symmetric." -/
theorem theorem_4_2_5 {α : ℝ} {v w : Fin n → ℝ} {B C : Matrix (Fin n) (Fin n) ℝ} (hB : Bᵀ = B)
    (hC : Cᵀ = -C) (hA : IsPositiveDefinite (blockPD α v w B C)) :
    blockPD α v w B C =
      fromBlocks 1 0 (replicateCol (Fin 1) (α⁻¹ • (v + w))) 1 *
        fromBlocks (of fun _ _ => α) (replicateRow (Fin 1) (v - w)) 0
          ((B - α⁻¹ • (vecMulVec v v - vecMulVec w w)) +
            (C - α⁻¹ • (vecMulVec w v - vecMulVec v w))) ∧
      (B - α⁻¹ • (vecMulVec v v - vecMulVec w w)).PosDef ∧
      (C - α⁻¹ • (vecMulVec w v - vecMulVec v w))ᵀ =
        -(C - α⁻¹ • (vecMulVec w v - vecMulVec v w)) := by
  -- `α > 0`: the quadratic form at `e₁`
  have hα : 0 < α := by
    have := hA (Sum.elim (fun _ => 1) 0) (fun h => by simpa using congrFun h (Sum.inl 0))
    rw [quad_blockPD hC] at this
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · rw [blockPD, fromBlocks_add, fromBlocks_multiply]
    congr 1
    · ext i j; simp
    · ext i j; simp; ring
    · ext i j
      simp only [Matrix.add_apply, Matrix.mul_zero, Matrix.zero_apply, add_zero, Matrix.mul_apply,
        Fin.sum_univ_one, replicateCol_apply, of_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      field_simp
    · ext i j
      simp [Matrix.mul_apply, vecMulVec_apply]
      field_simp
      ring
  · rw [posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun z hz => ?_⟩
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul,
        transpose_sub, transpose_vecMulVec, transpose_vecMulVec, hB]
    · simp only [star_trivial]
      have hq := hA (Sum.elim (fun _ => -(v ⬝ᵥ z) / α) z)
        (fun h => hz (funext fun i => by simpa using congrFun h (Sum.inr i)))
      rw [quad_blockPD hC] at hq
      have hw : 0 ≤ (w ⬝ᵥ z) * (w ⬝ᵥ z) / α := div_nonneg (mul_self_nonneg _) hα.le
      have key : z ⬝ᵥ ((B - α⁻¹ • (vecMulVec v v - vecMulVec w w)) *ᵥ z) =
          z ⬝ᵥ (B *ᵥ z) - (v ⬝ᵥ z) * (v ⬝ᵥ z) / α + (w ⬝ᵥ z) * (w ⬝ᵥ z) / α := by
        rw [sub_mulVec, smul_mulVec, sub_mulVec, dotProduct_sub, dotProduct_smul, dotProduct_sub,
          dotProduct_vecMulVec_mulVec, dotProduct_vecMulVec_mulVec, smul_eq_mul,
          dotProduct_comm z v, dotProduct_comm z w]
        field_simp
        ring
      rw [key]
      have : -(v ⬝ᵥ z) / α * (-(v ⬝ᵥ z) / α) * α + 2 * (-(v ⬝ᵥ z) / α) * (v ⬝ᵥ z) =
          -((v ⬝ᵥ z) * (v ⬝ᵥ z) / α) := by
        field_simp
        ring
      linarith
  · rw [transpose_sub, transpose_smul, transpose_sub, transpose_vecMulVec, transpose_vecMulVec,
      hC]
    ext i j
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
    ring

/-! ### §4.2.3–4.2.6 The Cholesky factorization -/

/-- `‖T‖₂ ≤ ‖A‖₂` for the symmetric part (§4.2.2, before (4.2.8): "It is easy to show"). -/
theorem l2_opNorm_symmPart_le (A : Matrix (Fin n) (Fin n) ℝ) :
    lpOpNorm 2 (hermitianPart A) ≤ lpOpNorm 2 A := by
  rw [lpOpNorm_two, lpOpNorm_two]
  exact l2_opNorm_hermitianPart_le A

/-- The lower triangular Cholesky factor multiplies to `A`: `A = G Gᵀ` with `G = cholesky A`. -/
theorem cholesky_mul_transpose {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    cholesky A * (cholesky A)ᵀ = A := by
  simpa [conjTranspose_eq_transpose_of_trivial] using
    (isCholesky_cholesky hA).conjTranspose_mul_self

/-- The Cholesky factor has a positive diagonal. -/
theorem cholesky_diag_pos {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (i : Fin n) :
    0 < cholesky A i i := by
  simpa [conjTranspose_eq_transpose_of_trivial] using (isCholesky_cholesky hA).diag_pos i

/-- **Theorem 4.2.7 (Cholesky factorization).** "If `A ∈ ℝⁿˣⁿ` is symmetric positive definite,
then there exists a unique lower triangular `G ∈ ℝⁿˣⁿ` with positive diagonal entries such that
`A = GGᵀ`"; it is the backbone's `Matrix.cholesky A`. -/
theorem theorem_4_2_7 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    (∃! G : Matrix (Fin n) (Fin n) ℝ, G.IsLowerTriangular ∧ (∀ i, 0 < G i i) ∧ A = G * Gᵀ) ∧
      (cholesky A).IsLowerTriangular ∧ (∀ i, 0 < cholesky A i i) ∧
        A = cholesky A * (cholesky A)ᵀ := by
  have hc : (cholesky A).IsLowerTriangular ∧ (∀ i, 0 < cholesky A i i) ∧
      A = cholesky A * (cholesky A)ᵀ :=
    ⟨isLowerTriangular_cholesky A, cholesky_diag_pos hA, (cholesky_mul_transpose hA).symm⟩
  refine ⟨⟨cholesky A, hc, fun G ⟨hG, hd, hGG⟩ => ?_⟩, hc⟩
  have h : IsCholesky A Gᵀ := by
    refine ⟨fun i j hij => hG (OrderDual.toDual_lt_toDual.2 hij), fun i => hd i, ?_⟩
    rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose, hGG]
  rw [cholesky_eq_of_isCholesky h, conjTranspose_eq_transpose_of_trivial, transpose_transpose]

/-- **(4.2.9)**: comparing columns in `A = GGᵀ`,
`G(j,j) G(:,j) = A(:,j) − ∑_{k<j} G(j,k) G(:,k)`. -/
theorem equation_4_2_9 {A G : Matrix (Fin n) (Fin n) ℝ} (hG : G.IsLowerTriangular)
    (hA : A = G * Gᵀ) (j : Fin n) :
    G j j • (fun i => G i j) =
      (fun i => A i j) - ∑ k ∈ univ.filter (· < j), G j k • fun i => G i k := by
  ext i
  have hsum : A i j = ∑ k ∈ univ.filter (· ≤ j), G i k * G j k := by
    rw [hA, mul_apply]
    refine (Finset.sum_subset (filter_subset _ _) fun k _ hk => ?_).symm
    have hjk : j < k := not_le.1 fun h => hk (mem_filter.2 ⟨mem_univ _, h⟩)
    rw [transpose_apply, hG (OrderDual.toDual_lt_toDual.2 hjk), mul_zero]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Finset.sum_apply]
  rw [hsum, sum_filter_le_eq_add]
  have : ∑ k ∈ univ.filter (· < j), G j k * G i k = ∑ k ∈ univ.filter (· < j), G i k * G j k :=
    Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [this]
  ring

/-- **§4.2.6**: "the entries in the Cholesky triangle are nicely bounded",
`g_ij² ≤ ∑_{k ≤ i} g_ik² = a_ii`. -/
theorem cholesky_entry_bound {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (i j : Fin n) :
    cholesky A i j ^ 2 ≤ A i i ∧
      ∑ k ∈ univ.filter (· ≤ i), cholesky A i k ^ 2 = A i i := by
  refine ⟨by simpa [Real.norm_eq_abs, sq_abs] using sq_norm_cholesky_apply_le hA i j, ?_⟩
  conv_rhs => rw [← cholesky_mul_transpose hA]
  rw [mul_apply]
  refine Eq.trans ?_ (Finset.sum_subset (filter_subset (· ≤ i) univ) ?_)
  · exact Finset.sum_congr rfl fun k _ => by rw [transpose_apply, sq]
  · intro k _ hk
    have hik : i < k := not_le.1 fun h => hk (mem_filter.2 ⟨mem_univ _, h⟩)
    rw [isLowerTriangular_cholesky A (OrderDual.toDual_lt_toDual.2 hik), zero_mul]

/-- **§4.2.6**: "the same conclusion can be reached from the equation `‖G‖₂² = ‖A‖₂`". -/
theorem l2_opNorm_cholesky_sq {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    lpOpNorm 2 (cholesky A) ^ 2 = lpOpNorm 2 A := by
  rw [lpOpNorm_two, lpOpNorm_two]
  exact Matrix.l2_opNorm_cholesky_sq hA

open scoped Matrix.Norms.L2Operator in
/-- **§4.2.6**: for a symmetric positive definite `A`, `κ₂(A) = λ_max(A)/λ_min(A)`. -/
theorem condNumber_eq_div_eigenvalues [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) :
    condNumberLp 2 A = (⨆ i, hA.1.eigenvalues i) / ⨅ i, hA.1.eigenvalues i := by
  rw [← hA.condNumber_l2_eq_div_eigenvalues, condNumberLp, lpOpNorm_two, lpOpNorm_two,
    NormedRing.condNumber, nonsing_inv_eq_ringInverse]

/-! ### Algorithm 4.2.1: gaxpy Cholesky -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 4.2.1 (Gaxpy Cholesky).** "Given a symmetric positive definite `A ∈ ℝⁿˣⁿ`, the
following algorithm computes a lower triangular `G` such that `A = GGᵀ`. For all `i ≥ j`, `G(i, j)`
overwrites `A(i, j)`":
```
for j = 1:n
    if j > 1
        A(j:n, j) = A(j:n, j) − A(j:n, 1:j−1) · A(j, 1:j−1)ᵀ
    end
    A(j:n, j) = A(j:n, j) / sqrt(A(j, j))
end
```
The gaxpy is a running difference from each entry of `A(j:n, j)` (`runningDiff`, empty for the
first column), reading the row `A(j, 1:j−1)` of the state at the start of the column (which the
column update does not change); the square root is rounded once and the whole column, diagonal
included, is divided by it. The strict upper triangle keeps the entries of `A`. -/
noncomputable def algorithm_4_2_1 (A : Matrix (Fin n) (Fin n) ℝ) : M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) => do
    let B ← ((List.finRange n).filter (j ≤ ·)).foldlM
      (fun (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
        let t ← runningDiff rnd ((List.finRange n).filter (· < j)) (B i) (A j) (B i j)
        pure (B.updateRow i (Function.update (B i) j t))) A
    let s ← rnd (Real.sqrt (B j j))
    ((List.finRange n).filter (j ≤ ·)).foldlM
      (fun (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
        let g ← rnd (C i j / s)
        pure (C.updateRow i (Function.update (C i) j g))) B) A

end Programs

section Bridge

variable (fp : RoundingModel ℝ)

/-- The indices below `j`, in increasing order. -/
private abbrev below (j : Fin n) : List (Fin n) := (List.finRange n).filter (· < j)

private theorem mem_below {j k : Fin n} : k ∈ below j ↔ k < j := by simp [below]

private theorem nodup_below (j : Fin n) : (below j).Nodup := (List.nodup_finRange n).filter _

/-- Column `j` of the state `S` is a finished column of Algorithm 4.2.1: the pivot `t` is the
running difference of `a_jj` and the products `g_jk g_jk`, `sh` a rounding of `√t`, and the entries
on and below the diagonal are the rounded quotients by `sh` of the running differences. -/
private def CholDone (A S : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : Prop :=
  ∃ t sh : ℝ, IsRunningDiff fp (below j) (S j) (S j) (A j j) t ∧ fp.Rounds (Real.sqrt t) sh ∧
    fp.Rounds (t / sh) (S j j) ∧
    ∀ i, j < i → ∃ r, IsRunningDiff fp (below j) (S i) (S j) (A i j) r ∧ fp.Rounds (r / sh) (S i j)

private theorem CholDone.congr {A S S' : Matrix (Fin n) (Fin n) ℝ} {j : Fin n}
    (h : CholDone fp A S j) (hS : ∀ i k, k ≤ j → S' i k = S i k) : CholDone fp A S' j := by
  obtain ⟨t, sh, hd, hs, hjj, hcol⟩ := h
  have hb : ∀ i, ∀ k ∈ below j, S' i k = S i k := fun i k hk => hS i k (le_of_lt (mem_below.1 hk))
  refine ⟨t, sh, hd.congr (hb j) (hb j), hs, by rw [hS j j le_rfl]; exact hjj, fun i hi => ?_⟩
  obtain ⟨r, hr, hl⟩ := hcol i hi
  exact ⟨r, hr.congr (hb i) (hb j), by rw [hS i j le_rfl]; exact hl⟩

/-- The loop invariant of Algorithm 4.2.1 after `c` columns. -/
private def CholInv (A : Matrix (Fin n) (Fin n) ℝ) (c : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i k : Fin n, c ≤ k.val → S i k = A i k) ∧ ∀ j : Fin n, j.val < c → CholDone fp A S j

/-- One column step of Algorithm 4.2.1 keeps the invariant. -/
private theorem cholInv_step (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : CholInv fp A j S) (S' : Matrix (Fin n) (Fin n) ℝ)
    (hS' : S' ∈ ((do
      let B ← ((List.finRange n).filter (j ≤ ·)).foldlM
        (fun (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
          let t ← runningDiff fp.round (below j) (B i) (S j) (B i j)
          pure (B.updateRow i (Function.update (B i) j t))) S
      let s ← fp.round (Real.sqrt (B j j))
      ((List.finRange n).filter (j ≤ ·)).foldlM
        (fun (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
          let g ← fp.round (C i j / s)
          pure (C.updateRow i (Function.update (C i) j g))) B) : SetM _).run) :
    CholInv fp A (j + 1) S' := by
  obtain ⟨hA, hdone⟩ := hS
  simp only [SetM.mem_run_bind] at hS'
  obtain ⟨B, hB, s, hs, hS'⟩ := hS'
  have hmem : ∀ i, i ∈ (List.finRange n).filter (j ≤ ·) ↔ j ≤ i := fun i => by simp
  have hnd : ((List.finRange n).filter (j ≤ ·)).Nodup := (List.nodup_finRange n).filter _
  obtain ⟨hB1, hB2⟩ := (mem_run_foldlM_updateRow_iff hnd j
    (fun i r => runningDiff fp.round (below j) r (S j) (r j)) S B).1 hB
  obtain ⟨hC1, hC2⟩ := (mem_run_foldlM_updateRow_iff hnd j
    (fun i r => fp.round (r j / s)) B S').1 hS'
  -- entries outside column `j` never change
  have hBo : ∀ i k, k ≠ j → B i k = S i k := fun i k hk => by
    by_cases hi : j ≤ i
    · obtain ⟨x, -, hx⟩ := hB2 i ((hmem i).2 hi)
      rw [hx, Function.update_of_ne hk]
    · rw [hB1 i fun h => hi ((hmem i).1 h)]
  have hSo : ∀ i k, k ≠ j → S' i k = S i k := fun i k hk => by
    by_cases hi : j ≤ i
    · obtain ⟨x, -, hx⟩ := hC2 i ((hmem i).2 hi)
      rw [hx, Function.update_of_ne hk, hBo i k hk]
    · rw [hC1 i fun h => hi ((hmem i).1 h), hBo i k hk]
  -- column `j`, on and below the diagonal
  have hcol : ∀ i, j ≤ i → ∃ t, IsRunningDiff fp (below j) (S' i) (S' j) (A i j) t ∧
      B i j = t ∧ fp.Rounds (t / s) (S' i j) := by
    intro i hi
    obtain ⟨t, ht, hx⟩ := hB2 i ((hmem i).2 hi)
    obtain ⟨g, hg, hy⟩ := hC2 i ((hmem i).2 hi)
    have hBij : B i j = t := by rw [hx, Function.update_self]
    refine ⟨t, ?_, hBij, ?_⟩
    · have ht' := (mem_run_runningDiff_iff (nodup_below j) _ _ _ _).1 ht
      rw [hA i j le_rfl] at ht'
      exact ht'.congr (fun k hk => hSo i k (ne_of_lt (mem_below.1 hk)))
        (fun k hk => hSo j k (ne_of_lt (mem_below.1 hk)))
    · rw [hy, Function.update_self, ← hBij]
      exact hg
  refine ⟨fun i k hk => ?_, fun j' hj' => ?_⟩
  · have hkj : k ≠ j := fun h => by rw [h] at hk; simp at hk
    rw [hSo i k hkj]
    exact hA i k (by omega)
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | hj'
    · refine (hdone j' hj').congr fp fun i k hk => hSo i k ?_
      intro h
      rw [h] at hk
      exact absurd (Fin.lt_def.1 (lt_of_le_of_lt hk (Fin.lt_def.2 hj'))) (lt_irrefl _)
    · have hjj : j' = j := Fin.ext hj'
      subst hjj
      obtain ⟨t, ht, hBt, hjj⟩ := hcol j' le_rfl
      refine ⟨t, s, ht, ?_, hjj, fun i hi => ?_⟩
      · rw [← hBt]; exact hs
      · obtain ⟨r, hr, -, hl⟩ := hcol i hi.le
        exact ⟨r, hr, hl⟩

/-- Every run of Algorithm 4.2.1 has all its columns finished. -/
private theorem cholDone_of_mem_run (A : Matrix (Fin n) (Fin n) ℝ)
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F ∈ (algorithm_4_2_1 fp.round A).run) (j : Fin n) :
    CholDone fp A F j :=
  (SetM.forall_mem_run_foldlM_finRange (CholInv fp A)
    ⟨fun _ _ _ => rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    (fun j S hS S' hS' => cholInv_step fp A j S hS S' hS') F hF).2 j j.isLt

/-- The lower triangle of the packed output agrees with the output on and below the diagonal. -/
private theorem sub_strictUpper_apply_of_le (F : Matrix (Fin n) (Fin n) ℝ) {i k : Fin n}
    (hki : k ≤ i) : (F - F.strictUpper) i k = F i k := by
  simp [strictUpper, not_lt.2 hki]

/-- **The rounding bridge of Algorithm 4.2.1**: every run whose returned diagonal is nonzero is an
admissible Cholesky factorization in the operation order of the algorithm,
`FloatingPoint.RoundsCholeskyDiv`, with `Ĝ` the lower triangle of the output. The hypothesis on
the returned diagonal (convention 9) forces every computed pivot `t_j` positive: a pivot `t_j ≤ 0`
has `√t_j = 0`, whose rounding is `0`, and then `ĝ_jj = fl(t_j / 0) = 0`. -/
theorem algorithm_4_2_1_rounds (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ F ∈ (algorithm_4_2_1 fp.round A).run, (∀ j, F j j ≠ 0) →
      RoundsCholeskyDiv fp A (F - F.strictUpper) := by
  intro F hF hd
  have hG : ∀ i k, k ≤ i → (F - F.strictUpper) i k = F i k :=
    fun i k hki => sub_strictUpper_apply_of_le F hki
  choose t sh hpiv hs hjj hcol using cholDone_of_mem_run fp A hF
  refine ⟨fun i k hik => by simp [strictUpper, hik], t, sh, fun j => ?_, fun j => ?_,
    fun j => ?_, fun i j hji => ?_⟩
  · obtain ⟨p, hp, hsum⟩ := hpiv j
    refine ⟨below j, p, nodup_below j, fun k => mem_below, fun k hk => ?_, hsum⟩
    rw [hG j k (mem_below.1 hk).le]
    exact hp k hk
  · -- the pivot is positive
    have ht : 0 ≤ t j := by
      by_contra hneg
      have h0 : Real.sqrt (t j) = 0 := Real.sqrt_eq_zero'.2 (le_of_lt (not_le.1 hneg))
      have hsh : sh j = 0 := (h0 ▸ hs j).eq_zero_of_zero
      have := hjj j
      rw [hsh, div_zero] at this
      exact hd j this.eq_zero_of_zero
    exact ⟨Real.sqrt (t j), Real.sqrt_nonneg _, Real.mul_self_sqrt ht, hs j⟩
  · rw [hG j j le_rfl]; exact hjj j
  · obtain ⟨r, ⟨p, hp, hsum⟩, hl⟩ := hcol j i hji
    refine ⟨below j, p, r, nodup_below j, fun k => mem_below, fun k hk => ?_, hsum, ?_⟩
    · rw [hG i k (lt_trans (mem_below.1 hk) hji).le, hG j k (mem_below.1 hk).le]
      exact hp k hk
    · rw [hG i j hji.le]; exact hl

/-- The run set of a running difference is nonempty in a total model. -/
private theorem runningDiff_run_nonempty {fp : RoundingModel ℝ} (hfp : fp.IsTotal) {ι : Type}
    (o : List ι) (a b : ι → ℝ) (c : ℝ) : (runningDiff fp.round o a b c).run.Nonempty :=
  SetM.run_foldlM_nonempty (fun _ _ _ => SetM.run_bind_nonempty
    (RoundingModel.run_round_nonempty hfp _) fun _ _ => RoundingModel.run_round_nonempty hfp _) c

/-- **Nonemptiness** (review M8): over a total model the run set of Algorithm 4.2.1 is nonempty, for
every input, so `algorithm_4_2_1_rounds` and the stability statements built on it are not
vacuous. -/
theorem algorithm_4_2_1_run_nonempty {fp : RoundingModel ℝ} (hfp : fp.IsTotal)
    (A : Matrix (Fin n) (Fin n) ℝ) : (algorithm_4_2_1 fp.round A).run.Nonempty :=
  SetM.run_foldlM_nonempty (fun _ _ _ => SetM.run_bind_nonempty
    (SetM.run_foldlM_nonempty (fun _ _ _ => SetM.run_bind_nonempty
      (runningDiff_run_nonempty hfp _ _ _ _) fun _ _ => ⟨_, SetM.mem_run_pure.2 rfl⟩) _)
    fun _ _ => SetM.run_bind_nonempty (RoundingModel.run_round_nonempty hfp _) fun _ _ =>
      SetM.run_foldlM_nonempty (fun _ _ _ => SetM.run_bind_nonempty
        (RoundingModel.run_round_nonempty hfp _) fun _ _ => ⟨_, SetM.mem_run_pure.2 rfl⟩) _) A

end Bridge

/-- The exact semantics of Algorithm 4.2.1 is one of its runs in the exact model. -/
private theorem algorithm_4_2_1_mem_exact (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_4_2_1 pure A) ∈ (algorithm_4_2_1 (RoundingModel.exact ℝ).round A).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_4_2_1, runningDiff, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

/-- An admissible running difference in the exact model is the exact difference. -/
theorem IsRunningDiff.eq_of_exact {ι : Type} [DecidableEq ι] {o : List ι} (ho : o.Nodup)
    {a b : ι → ℝ} {c t : ℝ} (h : IsRunningDiff (RoundingModel.exact ℝ) o a b c t) :
    t = c - ∑ k ∈ o.toFinset, a k * b k := by
  obtain ⟨p, hp, hs⟩ := h
  rw [(roundsSumFrom_exact_map_neg_iff ho).1 hs]
  exact congrArg _ (Finset.sum_congr rfl fun k hk => hp k (List.mem_toFinset.1 hk))

/-- **The exact semantics of Algorithm 4.2.1 is the backbone's Cholesky recurrence**, for every
input: the lower triangle of the exact run is `Matrix.cholesky A` (off the positive definite cone
both compute the same junk, `√` of a negative number being `0` and `x / 0 = 0`). Read off the
relational invariant at the exact model, column by column. -/
theorem algorithm_4_2_1_lower_eq_cholesky (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_4_2_1 pure A) - (Id.run (algorithm_4_2_1 pure A)).strictUpper =
      cholesky A := by
  obtain ⟨F, hF⟩ : ∃ F, Id.run (algorithm_4_2_1 pure A) = F := ⟨_, rfl⟩
  have hdone := cholDone_of_mem_run (RoundingModel.exact ℝ) A (hF ▸ algorithm_4_2_1_mem_exact A)
  rw [hF]
  have hset : ∀ j : Fin n, (below j).toFinset = univ.filter (· < j) := fun j => by
    ext k; simp [below]
  -- column by column, on and below the diagonal
  have key : ∀ j i : Fin n, j ≤ i → F i j = cholesky A i j := by
    intro j
    induction j using WellFoundedLT.induction with
    | _ j ih =>
    obtain ⟨t, sh, hpiv, hs, hjj, hcol⟩ := hdone j
    rw [RoundingModel.exact_rounds_iff] at hs hjj
    have ht := hpiv.eq_of_exact (nodup_below j)
    rw [hset] at ht
    have hsum : ∀ i, j ≤ i → ∑ k ∈ univ.filter (· < j), F i k * F j k =
        ∑ k ∈ univ.filter (· < j), cholesky A i k * cholesky A j k := fun i hi =>
      Finset.sum_congr rfl fun k hk => by
        have hkj := (mem_filter.1 hk).2
        rw [ih k hkj i (hkj.le.trans hi), ih k hkj j hkj.le]
    have hdiag : F j j = cholesky A j j := by
      rw [hjj, hs, Real.div_sqrt, ht, cholesky_apply_self, hsum j le_rfl]
      simp [Real.norm_eq_abs, sq]
    intro i hji
    rcases eq_or_lt_of_le hji with rfl | hji'
    · exact hdiag
    · obtain ⟨r, hr, hl⟩ := hcol i hji'
      rw [RoundingModel.exact_rounds_iff] at hl
      have hr' := hr.eq_of_exact (nodup_below j)
      rw [hset] at hr'
      rw [hl, hr', hs, cholesky_apply_of_lt A hji', ← hdiag, hjj, hs, Real.div_sqrt, ht,
        hsum i hji]
      simp
  ext i k
  rcases le_or_gt k i with hki | hik
  · rw [sub_strictUpper_apply_of_le F hki, key k i hki]
  · simp [strictUpper, hik, cholesky_apply_of_gt A hik]

/-- **Exact correctness of Algorithm 4.2.1**: for a symmetric positive definite `A`, the lower
triangle `G` of the exact run is the Cholesky factor, `G = cholesky A` and `A = GGᵀ`. -/
theorem algorithm_4_2_1_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    Id.run (algorithm_4_2_1 pure A) - (Id.run (algorithm_4_2_1 pure A)).strictUpper =
        cholesky A ∧
      A = (Id.run (algorithm_4_2_1 pure A) - (Id.run (algorithm_4_2_1 pure A)).strictUpper) *
        (Id.run (algorithm_4_2_1 pure A) - (Id.run (algorithm_4_2_1 pure A)).strictUpper)ᵀ := by
  rw [algorithm_4_2_1_lower_eq_cholesky]
  exact ⟨rfl, (cholesky_mul_transpose hA).symm⟩

/-! ### §4.2.7 The `L D Lᵀ` factorization with symmetric pivoting -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The pivot of step `k` of Algorithm 4.2.2: the first index `j ≥ k` with
`a_jj = max {a_kk, …, a_nn}` (exact comparisons of the stored values). -/
noncomputable def diagPivot (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : Fin n :=
  ((List.finRange n).filter (k ≤ ·)).foldl (fun (b i : Fin n) => if A b b < A i i then i else b) k

/-- **Algorithm 4.2.2 (Outer Product `L D Lᵀ` with Pivoting).** "Given a symmetric positive
semidefinite `A ∈ ℝⁿˣⁿ`, the following algorithm computes a permutation `P`, a unit lower
triangular `L`, and a diagonal matrix `D = diag(d₁, …, d_n)` so `PAPᵀ = LDLᵀ` … The matrix element
`a_ij` is overwritten by `d_i` if `i = j` and by `ℓ_ij` if `i > j`":
```
for k = 1:n
    piv(k) = j where a_jj = max{a_kk, …, a_nn}
    A(k, :) ↔ A(j, :)
    A(:, k) ↔ A(:, j)
    α = A(k, k)
    v = A(k+1:n, k)
    A(k+1:n, k) = v/α
    A(k+1:n, k+1:n) = A(k+1:n, k+1:n) − vvᵀ/α
end
```
The state is the matrix and the pivot vector (`piv k = j`, starting from the identity); the
interchanges act on whole rows and columns; `v` is a copy; the update `a_il ← fl(a_il − fl(fl(v_i
v_l)/α))` is in the book's order. No guard on `α = 0` (for a semidefinite input the trailing block
then vanishes, and `x / 0 = 0`). -/
noncomputable def algorithm_4_2_2 (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) :=
  (List.finRange n).foldlM
    (fun (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) (k : Fin n) => do
      let j := diagPivot st.1 k
      let A := st.1.submatrix (Equiv.swap k j) (Equiv.swap k j)
      let α := A k k
      let v : Fin n → ℝ := fun i => A i k
      let B ← ((List.finRange n).filter (k < ·)).foldlM
        (fun (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
          let l ← rnd (v i / α)
          pure (B.updateRow i (Function.update (B i) k l))) A
      let C ← ((List.finRange n).filter (k < ·)).foldlM
        (fun (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
          ((List.finRange n).filter (k < ·)).foldlM
            (fun (C : Matrix (Fin n) (Fin n) ℝ) (l : Fin n) => do
              let p ← rnd (v i * v l)
              let q ← rnd (p / α)
              let c ← rnd (C i l - q)
              pure (C.updateRow i (Function.update (C i) l c))) C) B
      pure (C, Function.update st.2 k j)) (A, fun i => i)

end Programs

/-! ### §4.2.8 The symmetric semidefinite case -/

/-- **(4.2.11)**: a symmetric positive semidefinite `A` of rank `r` has nonnegative eigenvalues,
exactly `r` of them nonzero (Mathlib's eigenvalues are unordered; the book's ordering
`0 = λ_n = ⋯ = λ_{r+1} < λ_r ≤ ⋯ ≤ λ_1` is a relabelling). -/
theorem equation_4_2_11 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    (∀ i, 0 ≤ hA.1.eigenvalues i) ∧ Fintype.card {i // hA.1.eigenvalues i ≠ 0} = A.rank :=
  ⟨hA.eigenvalues_nonneg, hA.1.rank_eq_card_non_zero_eigs.symm⟩

/-- **Theorem 4.2.8, (4.2.12)**: `|a_ij| ≤ (a_ii + a_jj)/2`. -/
theorem theorem_4_2_8_a {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (i j : Fin n) :
    |A i j| ≤ (A i i + A j j) / 2 := by
  simpa using hA.norm_apply_le_add_re_diag_div_two i j

/-- **Theorem 4.2.8, (4.2.13)**: `|a_ij| ≤ √(a_ii a_jj)` (for all `i, j`; the book states it for
`i ≠ j`). -/
theorem theorem_4_2_8_b {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (i j : Fin n) :
    |A i j| ≤ Real.sqrt (A i i * A j j) :=
  Real.abs_le_sqrt (by simpa [sq_abs] using hA.norm_apply_sq_le_mul_re_diag i j)

/-- **Theorem 4.2.8, (4.2.14)**: `max |a_ij| = max a_ii`, entrywise and as a supremum. -/
theorem theorem_4_2_8_c {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    (∀ i j, |A i j| ≤ max (A i i) (A j j)) ∧
      ∀ [NeZero n], (⨆ i, ⨆ j, |A i j|) = ⨆ i, A i i := by
  have h1 : ∀ i j, |A i j| ≤ max (A i i) (A j j) := fun i j => by
    simpa using hA.norm_apply_le_max_re_diag i j
  refine ⟨h1, fun {_} => le_antisymm ?_ ?_⟩
  · have hb : BddAbove (Set.range fun i => A i i) := (Set.finite_range _).bddAbove
    exact ciSup_le fun i => ciSup_le fun j =>
      (h1 i j).trans (max_le (le_ciSup hb i) (le_ciSup hb j))
  · have hb : ∀ i, BddAbove (Set.range fun j => |A i j|) := fun i => (Set.finite_range _).bddAbove
    have hb' : BddAbove (Set.range fun i => ⨆ j, |A i j|) := (Set.finite_range _).bddAbove
    refine ciSup_le fun i => ?_
    calc A i i = |A i i| := (abs_of_nonneg hA.diag_nonneg).symm
      _ ≤ ⨆ j, |A i j| := le_ciSup (hb i) i
      _ ≤ ⨆ i, ⨆ j, |A i j| := le_ciSup hb' i

/-- **Theorem 4.2.8, (4.2.15)**: `a_ii = 0 ⇒ A(i, :) = 0, A(:, i) = 0`. -/
theorem theorem_4_2_8_d {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) {i : Fin n}
    (hi : A i i = 0) : (∀ j, A i j = 0) ∧ ∀ j, A j i = 0 :=
  ⟨fun j => (hA.apply_eq_zero_of_diag_eq_zero hi j).1,
    fun j => (hA.apply_eq_zero_of_diag_eq_zero hi j).2⟩

/-- **Theorem 4.2.8.** "If `A ∈ ℝⁿˣⁿ` is symmetric positive semidefinite, then (4.2.12)–(4.2.15)
hold." -/
theorem theorem_4_2_8 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    (∀ i j, |A i j| ≤ (A i i + A j j) / 2) ∧ (∀ i j, |A i j| ≤ Real.sqrt (A i i * A j j)) ∧
      ((∀ i j, |A i j| ≤ max (A i i) (A j j)) ∧
        ∀ [NeZero n], (⨆ i, ⨆ j, |A i j|) = ⨆ i, A i i) ∧
      ∀ i, A i i = 0 → (∀ j, A i j = 0) ∧ ∀ j, A j i = 0 :=
  ⟨theorem_4_2_8_a hA, theorem_4_2_8_b hA, theorem_4_2_8_c hA, fun _ => theorem_4_2_8_d hA⟩

/-- **(4.2.10)**: a symmetric positive definite `A` has a permutation `P`, a unit lower triangular
`L` and `D = diag(d₁, …, d_n)` with `PAPᵀ = LDLᵀ` and `d₁ ≥ d₂ ≥ ⋯ ≥ d_n > 0` (the diagonal
pivoting strategy). -/
theorem equation_4_2_10 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∃ (σ : Equiv.Perm (Fin n)) (L : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ),
      L.IsUnitLowerTriangular ∧ A.submatrix σ σ = L * diagonal d * Lᵀ ∧ Antitone d ∧
        ∀ i, 0 < d i := by
  obtain ⟨σ, L, d, hL, heq, hanti, hpos, -⟩ := hA.posSemidef.exists_perm_ldl_rank
  have hr : A.rank = n := by rw [rank_of_isUnit A hA.isUnit, Fintype.card_fin]
  refine ⟨σ, L, d, hL, by simpa [conjTranspose_eq_transpose_of_trivial] using heq, hanti,
    fun i => hpos i (by rw [hr]; exact i.isLt)⟩

/-- An entry of `X D Xᵀ` for a diagonal `D`. -/
private theorem mul_diagonal_mul_transpose_apply {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (X : Matrix ι κ ℝ) (d : κ → ℝ) (a b : ι) :
    (X * diagonal d * Xᵀ) a b = ∑ k, X a k * d k * X b k := by
  rw [mul_apply]
  simp only [mul_diagonal, transpose_apply]

/-- **(4.2.17)**: a symmetric positive semidefinite `A` of rank `r` satisfies
`PAPᵀ = [L₁₁; L₂₁] D_r [L₁₁ᵀ L₂₁ᵀ]` with `D_r = diag(d₁, …, d_r)` positive and `L₁₁` (the first
`r` rows of the `n × r` matrix `L = [L₁₁; L₂₁]`) unit lower triangular. -/
theorem equation_4_2_17 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    ∃ (σ : Equiv.Perm (Fin n)) (L : Matrix (Fin n) (Fin A.rank) ℝ) (d : Fin A.rank → ℝ),
      (L.submatrix (Fin.castLE (A.rank_le_width)) id).IsUnitLowerTriangular ∧
        (∀ i, 0 < d i) ∧ A.submatrix σ σ = L * diagonal d * Lᵀ := by
  obtain ⟨σ, Lf, d, hL, heq, -, hpos, hzero⟩ := hA.exists_perm_ldl_rank
  set h := A.rank_le_width
  have key : ∀ f : Fin n → ℝ, (∀ k : Fin n, A.rank ≤ k → f k = 0) →
      ∑ k, f k = ∑ k : Fin A.rank, f (Fin.castLE h k) := by
    intro f hf
    rw [show (∑ k : Fin A.rank, f (Fin.castLE h k)) = ∑ k ∈ univ.map (Fin.castLEEmb h), f k
      from (Finset.sum_map univ (Fin.castLEEmb h) f).symm]
    refine (Finset.sum_subset (subset_univ _) fun k _ hk => hf k ?_).symm
    by_contra hlt
    exact hk (mem_map.2 ⟨⟨k, not_le.1 hlt⟩, mem_univ _, Fin.ext rfl⟩)
  refine ⟨σ, Lf.submatrix id (Fin.castLE h), d ∘ Fin.castLE h, ⟨fun a b hab => ?_, fun a => ?_⟩,
    fun i => hpos _ (by rw [Fin.val_castLE]; exact i.isLt), ?_⟩
  · exact hL.isLowerTriangular (show Fin.castLE h a < Fin.castLE h b from hab)
  · exact hL.diag_eq_one _
  · have heq' : A.submatrix σ σ = Lf * diagonal d * Lfᵀ := by
      simpa [conjTranspose_eq_transpose_of_trivial] using heq
    rw [heq']
    ext i j
    rw [mul_diagonal_mul_transpose_apply, mul_diagonal_mul_transpose_apply]
    simp only [submatrix_apply, id, Function.comp_apply]
    exact key _ fun k hk => by rw [hzero k hk]; ring

/-- **§4.2.8, the rank-one expansion**: `PAPᵀ = ∑_{j=1}^{r} d_j ℓ_j ℓ_jᵀ` with `ℓ_j` the `j`th
column of the `L`-matrix of (4.2.17) — "a relatively cheap alternative to the SVD rank-1
expansion". -/
theorem equation_4_2_17_sum {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    ∃ (σ : Equiv.Perm (Fin n)) (L : Matrix (Fin n) (Fin A.rank) ℝ) (d : Fin A.rank → ℝ),
      (L.submatrix (Fin.castLE (A.rank_le_width)) id).IsUnitLowerTriangular ∧
        (∀ i, 0 < d i) ∧
        A.submatrix σ σ = ∑ j, d j • vecMulVec (fun i => L i j) (fun i => L i j) := by
  obtain ⟨σ, L, d, hL, hd, heq⟩ := equation_4_2_17 hA
  refine ⟨σ, L, d, hL, hd, ?_⟩
  rw [heq]
  ext a b
  rw [mul_diagonal_mul_transpose_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ### §4.2.9 Block Cholesky -/

/-- **(4.2.18)** and the block equations: for a symmetric positive definite `A` blocked as
`[A₁₁ A₂₁ᵀ; A₂₁ A₂₂]` (`A₁₁` of size `r`) and `G = [G₁₁ 0; G₂₁ G₂₂]` its Cholesky factor,
blocked conformably: `A₁₁ = G₁₁G₁₁ᵀ`, `A₂₁ = G₂₁G₁₁ᵀ`, `A₂₂ = G₂₁G₂₁ᵀ + G₂₂G₂₂ᵀ`; `G₁₁` is the
Cholesky factor of `A₁₁` and `G₂₂` that of `A₂₂ − G₂₁G₂₁ᵀ = A₂₂ − A₂₁A₁₁⁻¹A₂₁ᵀ` ("Step 3"). The
blocks are read along `finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s)`. -/
theorem equation_4_2_18 {r s : ℕ} {A : Matrix (Fin (r + s)) (Fin (r + s)) ℝ} (hA : A.PosDef) :
    let A' := A.submatrix finSumFinEquiv finSumFinEquiv
    let G' := (cholesky A).submatrix finSumFinEquiv finSumFinEquiv
    G'.toBlocks₁₂ = 0 ∧ A'.toBlocks₁₁ = G'.toBlocks₁₁ * G'.toBlocks₁₁ᵀ ∧
      A'.toBlocks₂₁ = G'.toBlocks₂₁ * G'.toBlocks₁₁ᵀ ∧
      A'.toBlocks₂₂ = G'.toBlocks₂₁ * G'.toBlocks₂₁ᵀ + G'.toBlocks₂₂ * G'.toBlocks₂₂ᵀ ∧
      A'.toBlocks₂₂ - G'.toBlocks₂₁ * G'.toBlocks₂₁ᵀ =
        A'.toBlocks₂₂ - A'.toBlocks₂₁ * A'.toBlocks₁₁⁻¹ * A'.toBlocks₂₁ᵀ ∧
      G'.toBlocks₁₁ = cholesky A'.toBlocks₁₁ ∧
      G'.toBlocks₂₂ = cholesky (A'.toBlocks₂₂ - A'.toBlocks₂₁ * A'.toBlocks₁₁⁻¹ * A'.toBlocks₂₁ᵀ)
    := by
  intro A' G'
  have hblk : G' = fromBlocks G'.toBlocks₁₁ 0 G'.toBlocks₂₁ G'.toBlocks₂₂ := by
    have := cholesky_finSumFin hA
    simp only [G', this, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  have h12 : G'.toBlocks₁₂ = 0 := by
    have := cholesky_finSumFin hA
    simp only [G', this, toBlocks_fromBlocks₁₂]
  have hAA : A' = G' * G'ᵀ := by
    simp only [A', G']
    conv_lhs => rw [← cholesky_mul_transpose hA]
    rw [← submatrix_mul_equiv _ _ _ finSumFinEquiv, transpose_submatrix]
  have hprod : A' = fromBlocks (G'.toBlocks₁₁ * G'.toBlocks₁₁ᵀ) (G'.toBlocks₁₁ * G'.toBlocks₂₁ᵀ)
      (G'.toBlocks₂₁ * G'.toBlocks₁₁ᵀ)
      (G'.toBlocks₂₁ * G'.toBlocks₂₁ᵀ + G'.toBlocks₂₂ * G'.toBlocks₂₂ᵀ) := by
    rw [hAA, hblk, fromBlocks_transpose, fromBlocks_multiply]
    simp
  have hsym : A'.toBlocks₁₂ = A'.toBlocks₂₁ᵀ := by
    ext i j
    change A (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) =
      A (finSumFinEquiv (Sum.inr j)) (finSumFinEquiv (Sum.inl i))
    have := hA.1.apply (finSumFinEquiv (Sum.inr j)) (finSumFinEquiv (Sum.inl i))
    simpa using this
  have hc := cholesky_finSumFin hA
  have h11 : G'.toBlocks₁₁ = cholesky A'.toBlocks₁₁ := by
    simp only [G', hc, toBlocks_fromBlocks₁₁]
    rfl
  have h22 : G'.toBlocks₂₂ = cholesky A'.schurComplement := by
    simp only [G', hc, toBlocks_fromBlocks₂₂]
    rfl
  have hS : A'.schurComplement =
      A'.toBlocks₂₂ - A'.toBlocks₂₁ * A'.toBlocks₁₁⁻¹ * A'.toBlocks₂₁ᵀ := by
    rw [schurComplement_eq, hsym]
  -- the Schur complement is `A₂₂ − G₂₁ G₂₁ᵀ`
  have hG11 : IsUnit G'.toBlocks₁₁ := by
    rw [h11]
    have hp : A'.toBlocks₁₁.PosDef := (hA.submatrix finSumFinEquiv.injective).submatrix
      Sum.inl_injective
    have := (isCholesky_cholesky hp).isUnit
    simpa [conjTranspose_eq_transpose_of_trivial, isUnit_transpose] using this
  have h11' : A'.toBlocks₁₁ = G'.toBlocks₁₁ * G'.toBlocks₁₁ᵀ := by
    rw [hprod]; simp
  have h21' : A'.toBlocks₂₁ = G'.toBlocks₂₁ * G'.toBlocks₁₁ᵀ := by
    rw [hprod]; simp
  have hschur : A'.toBlocks₂₁ * A'.toBlocks₁₁⁻¹ * A'.toBlocks₂₁ᵀ =
      G'.toBlocks₂₁ * G'.toBlocks₂₁ᵀ := by
    have hdet : IsUnit G'.toBlocks₁₁.det := (isUnit_iff_isUnit_det _).1 hG11
    have hdetT : IsUnit G'.toBlocks₁₁ᵀ.det := by rwa [det_transpose]
    rw [h11', h21', Matrix.mul_inv_rev, transpose_mul, transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G'.toBlocks₁₁ᵀ, mul_nonsing_inv _ hdetT, Matrix.one_mul,
      ← Matrix.mul_assoc G'.toBlocks₁₁⁻¹, nonsing_inv_mul _ hdet, Matrix.one_mul]
  refine ⟨h12, h11', h21', by rw [hprod]; simp, by rw [hschur], h11, by rw [h22, hS]⟩

/-- The `r × r` block `(i, j)` of a matrix on `Fin (N * r)`, the book's `A_ij` in the blocking
(4.2.19), read along `finProdFinEquiv : Fin N × Fin r ≃ Fin (N * r)`. -/
def blockOf {N r : ℕ} (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) (i j : Fin N) :
    Matrix (Fin r) (Fin r) ℝ :=
  of fun p q => A (finProdFinEquiv (i, p)) (finProdFinEquiv (j, q))

/-- The blocking of (4.2.19) is monotone: block row `i` comes before block row `k` when `i < k`. -/
private theorem finProdFinEquiv_lt {N r : ℕ} {i k : Fin N} (hik : i < k) (p s : Fin r) :
    finProdFinEquiv (i, p) < finProdFinEquiv (k, s) := by
  rw [Fin.lt_def, finProdFinEquiv_apply_val, finProdFinEquiv_apply_val]
  dsimp only
  have hik' : (i : ℕ) + 1 ≤ k := hik
  have h2 : r * ((i : ℕ) + 1) ≤ r * k := Nat.mul_le_mul_left r hik'
  rw [Nat.mul_succ] at h2
  have := p.isLt
  omega

/-- **(4.2.19)** and the block equations below it: for `n = N r`, a symmetric positive definite `A`
and its Cholesky factor `G`, both blocked into `r × r` blocks, `G` is block lower triangular,
`A_ij = ∑_{k ≤ j} G_ik G_jkᵀ` for `i ≥ j`, and with `S = A_ij − ∑_{k<j} G_ik G_jkᵀ`: `G_jj` is
the Cholesky factor of `S` if `i = j`, and `G_ij G_jjᵀ = S` if `i > j`. -/
theorem equation_4_2_19 {N r : ℕ} {A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ} (hA : A.PosDef)
    (i j : Fin N) :
    (i < j → blockOf (cholesky A) i j = 0) ∧
    (j ≤ i → blockOf A i j =
      ∑ k ∈ univ.filter (· ≤ j), blockOf (cholesky A) i k * (blockOf (cholesky A) j k)ᵀ) ∧
    blockOf (cholesky A) j j = cholesky (blockOf A j j -
      ∑ k ∈ univ.filter (· < j), blockOf (cholesky A) j k * (blockOf (cholesky A) j k)ᵀ) ∧
    (j < i → blockOf (cholesky A) i j * (blockOf (cholesky A) j j)ᵀ = blockOf A i j -
      ∑ k ∈ univ.filter (· < j), blockOf (cholesky A) i k * (blockOf (cholesky A) j k)ᵀ) := by
  set G := cholesky A with hGdef
  have hGl : ∀ a b : Fin N, a < b → blockOf G a b = 0 := fun a b hab => by
    ext p q
    exact isLowerTriangular_cholesky A
      (OrderDual.toDual_lt_toDual.2 (finProdFinEquiv_lt hab p q))
  -- block multiplication
  have hmul : ∀ a b : Fin N, b ≤ a →
      blockOf A a b = ∑ k ∈ univ.filter (· ≤ b), blockOf G a k * (blockOf G b k)ᵀ := by
    intro a b hba
    ext p q
    have h1 : A (finProdFinEquiv (a, p)) (finProdFinEquiv (b, q)) =
        ∑ x : Fin N × Fin r, G (finProdFinEquiv (a, p)) (finProdFinEquiv x) *
          G (finProdFinEquiv (b, q)) (finProdFinEquiv x) := by
      conv_lhs => rw [← cholesky_mul_transpose hA]
      rw [mul_apply, ← Equiv.sum_comp finProdFinEquiv]
      rfl
    rw [blockOf, of_apply, h1, Fintype.sum_prod_type, Matrix.sum_apply]
    refine (Finset.sum_subset (subset_univ (univ.filter (· ≤ b))) fun k _ hk => ?_).symm.trans
      ?_
    · have hbk : b < k := not_le.1 fun h => hk (mem_filter.2 ⟨mem_univ _, h⟩)
      refine Finset.sum_eq_zero fun s _ => ?_
      have := congrFun (congrFun (hGl b k hbk) q) s
      simp only [blockOf, of_apply, Matrix.zero_apply] at this
      rw [this, mul_zero]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp [blockOf, mul_apply]
  refine ⟨hGl i j, hmul i j, ?_, fun hji => ?_⟩
  · -- the diagonal block is the Cholesky factor of `S`
    have hS : blockOf A j j - ∑ k ∈ univ.filter (· < j), blockOf G j k * (blockOf G j k)ᵀ =
        blockOf G j j * (blockOf G j j)ᵀ := by
      rw [hmul j j le_rfl, sum_filter_le_eq_add, add_sub_cancel_left]
    rw [hS]
    have hc : IsCholesky (blockOf G j j * (blockOf G j j)ᵀ) (blockOf G j j)ᵀ := by
      refine ⟨fun p q hpq => ?_, fun p => ?_, ?_⟩
      · simp only [transpose_apply, blockOf, of_apply]
        exact isLowerTriangular_cholesky A (OrderDual.toDual_lt_toDual.2
          (by rw [Fin.lt_def, finProdFinEquiv_apply_val, finProdFinEquiv_apply_val]
              exact Nat.add_lt_add_right hpq _))
      · simpa [blockOf] using cholesky_diag_pos hA (finProdFinEquiv (j, p))
      · rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]
    rw [cholesky_eq_of_isCholesky hc, conjTranspose_eq_transpose_of_trivial, transpose_transpose]
  · rw [hmul i j hji.le, sum_filter_le_eq_add, add_sub_cancel_left]

end GolubVanLoan.Chapter04
