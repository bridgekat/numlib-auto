import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.HermitianPart
import NumlibSurface.GolubVanLoan.Chapter03.Section04
import NumlibSurface.GolubVanLoan.Chapter04.Section01

/-!
# Golub–Van Loan §4.2: positive definite systems

Surface file for [golub2013matrix] §4.2: positive definiteness of a general (unsymmetric) matrix
(Theorems 4.2.1–4.2.6 with Corollaries 4.2.2 and 4.2.4, and the backward error (4.2.7) of LU
without pivoting that Theorem 4.2.6 supports), the Cholesky factorization (Theorem
4.2.7) and gaxpy Cholesky (Algorithm 4.2.1) with its rounding bridge, the facts of §4.2.6 on the
stability of the Cholesky process (with Wilkinson's backward error bound for the computed factor and
the two triangular solves), the pivoted outer-product `L D Lᵀ` (Algorithm 4.2.2, (4.2.10)), the
semidefinite case (Theorem 4.2.8, (4.2.11), (4.2.17)) with the exact specification of Algorithm
4.2.2 through its invariant (4.2.16), the block equations of block Cholesky
((4.2.18)–(4.2.19)) and the block algorithms, recursive (Algorithm 4.2.3) and nonrecursive
(Algorithm 4.2.4), with their exact specifications.

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
`FloatingPoint.RoundsCholeskyDiv`. The triangular solves call chapter 3's column-oriented
substitutions (Algorithms 3.1.3–3.1.4). The block algorithms store the lower triangle of Algorithm
4.2.1 (`choleskyLower`), solve `X Gᵀ = B` row by row (`solveRowsLower`) and form the updates
`A₂₂ − G₂₁G₂₁ᵀ`, `A_ij − ∑_{k<j} G_ik G_jkᵀ` by running differences (`mulTransposeDiff`); their
exact specifications compare the blocks with (4.2.18) and (4.2.19). The exact specification of
Algorithm 4.2.2 reads the state after `k` steps as `L_k diag(D_k, A_k) L_kᵀ` (`pivotedLower`,
`pivotedMiddle`); one step is a symmetric interchange (which commutes with both, the pivot being at
or after `k`) followed by a congruence with the column operator of the multipliers.

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

/-- The book's `T = (A + Aᵀ)/2` is the backbone's `Matrix.hermitianPart A`. -/
private theorem half_add_transpose_eq_hermitianPart (A : Matrix (Fin n) (Fin n) ℝ) :
    (2 : ℝ)⁻¹ • (A + Aᵀ) = hermitianPart A := by
  rw [hermitianPart, conjTranspose_eq_transpose_of_trivial]

/-- The book's `S = (A − Aᵀ)/2` is `A − T`. -/
private theorem half_sub_transpose_eq_sub_hermitianPart (A : Matrix (Fin n) (Fin n) ℝ) :
    (2 : ℝ)⁻¹ • (A - Aᵀ) = A - hermitianPart A := by
  rw [hermitianPart, conjTranspose_eq_transpose_of_trivial]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  ring

open scoped Matrix.Norms.Frobenius in
/-- **Theorem 4.2.6**, (4.2.5): "Let `A ∈ ℝ^{n×n}` be positive definite and set `T = (A + Aᵀ)/2`
and `S = (A − Aᵀ)/2`. If `A = LU` is the LU factorization, then
`‖|L||U|‖_F ≤ n (‖T‖₂ + ‖S T⁻¹ S‖₂)`." The book refers to Golub and Van Loan (1979) for the proof;
the backbone `Matrix.IsLU.frobenius_norm_abs_mul_abs_le` bounds each rank-one term `|ℓ_k| |u_kᵀ|`
through `A T⁻¹ Aᵀ = T − S T⁻¹ S`. -/
theorem theorem_4_2_6 {A L U T S : Matrix (Fin n) (Fin n) ℝ} (hA : IsPositiveDefinite A)
    (hT : T = (2 : ℝ)⁻¹ • (A + Aᵀ)) (hS : S = (2 : ℝ)⁻¹ • (A - Aᵀ)) (h : IsLU A L U) :
    ‖L.abs * U.abs‖ ≤ n * (lpOpNorm 2 T + lpOpNorm 2 (S * T⁻¹ * S)) := by
  rw [hT, hS, half_add_transpose_eq_hermitianPart, half_sub_transpose_eq_sub_hermitianPart,
    lpOpNorm_two, lpOpNorm_two]
  have := IsLU.frobenius_norm_abs_mul_abs_le ((isPositiveDefinite_iff A).1 hA) h
  rw [Fintype.card_fin] at this
  exact this

open scoped Matrix.Norms.Frobenius in
/-- The Frobenius norm is monotone in the absolute values: `|E| ≤ M` entrywise gives
`‖E‖_F ≤ ‖M‖_F`. -/
private theorem frobenius_norm_le_of_abs_entrywiseLE {E M : Matrix (Fin n) (Fin n) ℝ}
    (h : E.abs ≤ₑ M) : ‖E‖ ≤ ‖M‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) ((h i j).trans (le_abs_self _)) 2

open scoped Matrix.Norms.Frobenius in
/-- **(4.2.7)**, rigorous: "Assume that the computed factors `L̂` and `Û` satisfy
`‖|L̂||Û|‖_F ≤ c ‖|L||U|‖_F` (4.2.6), where `c` is a constant of modest size. It follows from
(4.2.1) and the analysis in §3.3 that if these factors are used to compute a solution to
`Ax = b`, then the computed solution `x̂` satisfies `(A + E) x̂ = b` with
`‖E‖_F ≤ u (2n ‖A‖_F + 4cn² (‖T‖₂ + ‖S T⁻¹ S‖₂)) + O(u²)`." Here the computed factors and the two
triangular solves are the relational rounding models `FloatingPoint.RoundsLU`,
`FloatingPoint.RoundsForwardSubst`, `FloatingPoint.RoundsBackSubst` (primed names for the hats),
with nonzero pivots, and the bound is the stronger, non-asymptotic
`‖E‖_F ≤ γ_{3n} c n (‖T‖₂ + ‖S T⁻¹ S‖₂)` (the term `2n ‖A‖_F` is not needed and `γ_{3n} ≤ 4nu`
when `3nu ≤ 1/4`): `|E| ≤ γ_{3n} |L̂||Û|` (`FloatingPoint.exists_roundsLU_solve_eq`) and
Theorem 4.2.6. -/
theorem equation_4_2_7 {fp : RoundingModel ℝ} {A L U L' U' T S : Matrix (Fin n) (Fin n) ℝ}
    {b y x' : Fin n → ℝ} {c : ℝ} (hA : IsPositiveDefinite A) (hT : T = (2 : ℝ)⁻¹ • (A + Aᵀ))
    (hS : S = (2 : ℝ)⁻¹ • (A - Aᵀ)) (h : IsLU A L U) (hu : fp.u < 1)
    (hn : ((3 * n : ℕ) : ℝ) * fp.u < 1) (hLU : RoundsLU fp A L' U') (hd : ∀ j, U' j j ≠ 0)
    (hy : RoundsForwardSubst fp L' b y) (hx : RoundsBackSubst fp U' y x') (hc0 : 0 ≤ c)
    (hc : ‖L'.abs * U'.abs‖ ≤ c * ‖L.abs * U.abs‖) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ, (A + E) *ᵥ x' = b ∧
      ‖E‖ ≤ gamma fp.u (3 * n) * (c * (n * (lpOpNorm 2 T + lpOpNorm 2 (S * T⁻¹ * S)))) := by
  obtain ⟨E, hE, hEx⟩ := exists_roundsLU_solve_eq hu (by simpa using hn) hLU hd hy hx
  rw [Fintype.card_fin] at hE
  have hγ : 0 ≤ gamma fp.u (3 * n) := gamma_nonneg fp.u_nonneg hn
  refine ⟨E, hEx, ?_⟩
  calc ‖E‖ ≤ ‖gamma fp.u (3 * n) • (L'.abs * U'.abs)‖ := frobenius_norm_le_of_abs_entrywiseLE hE
    _ = gamma fp.u (3 * n) * ‖L'.abs * U'.abs‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ]
    _ ≤ gamma fp.u (3 * n) * (c * ‖L.abs * U.abs‖) := mul_le_mul_of_nonneg_left hc hγ
    _ ≤ _ := by
        gcongr
        exact theorem_4_2_6 hA hT hS h

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

section Solve

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **The solve stage of §4.2.6** on the output `F` of Algorithm 4.2.1: with `Ĝ = F − strictUpper F`
the computed lower triangle, "`Ĝy = b`, `Ĝᵀx = y`" by chapter 3's column-oriented substitutions,
Algorithm 3.1.3 and Algorithm 3.1.4. -/
noncomputable def solveCholesky (F : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    M (Fin n → ℝ) := do
  let y ← Chapter03.algorithm_3_1_3 rnd (F - F.strictUpper) b
  Chapter03.algorithm_3_1_4 rnd (F - F.strictUpper)ᵀ y

end Solve

/-- **§4.2.6, Wilkinson's bound**, rigorous form: "if `x̂` is the computed solution to `Ax = b`,
obtained via the Cholesky process, then `x̂` solves the perturbed system `(A + E)x̂ = b`,
`‖E‖₂ ≤ c_n u ‖A‖₂`, where `c_n` is a small constant that depends upon `n`". For a symmetric `A`, a
run `F` of Algorithm 4.2.1 with nonzero returned diagonal (which forces every computed pivot
positive, `algorithm_4_2_1_rounds`) and a solution `x̂` computed from it by `solveCholesky`:
`‖E‖₂ ≤ n γ_{3n+3} ‖A‖₂ / (1 − n γ_{n+3})`, the constant `c_n ≈ 3n²` made explicit. The
companion claim that the process runs to completion when `q_n u κ₂(A) ≤ 1` is not formalized. -/
theorem cholesky_backward_error {fp : RoundingModel ℝ} (hn : ((3 * n + 3 : ℕ) : ℝ) * fp.u < 1)
    (hγ : n * gamma fp.u (n + 3) < 1) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (b : Fin n → ℝ) :
    ∀ F ∈ (algorithm_4_2_1 fp.round A).run, (∀ j, F j j ≠ 0) →
      ∀ x ∈ (solveCholesky fp.round F b).run,
        ∃ E : Matrix (Fin n) (Fin n) ℝ, (A + E) *ᵥ x = b ∧
          lpOpNorm 2 E ≤ n * gamma fp.u (3 * n + 3) * lpOpNorm 2 A /
            (1 - n * gamma fp.u (n + 3)) := by
  intro F hF hd x hx
  have hu : fp.u < 1 := by
    have h1 : (1 : ℝ) * fp.u ≤ ((3 * n + 3 : ℕ) : ℝ) * fp.u :=
      mul_le_mul_of_nonneg_right (by norm_cast; omega) fp.u_nonneg
    linarith
  simp only [solveCholesky, SetM.mem_run_bind] at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨E, hE, hAx⟩ := l2_opNorm_le_of_roundsCholeskyDiv hu (by simpa using hn)
    (by simpa using hγ) hA (algorithm_4_2_1_rounds fp A F hF hd)
    (fun j => by rw [sub_strictUpper_apply_of_le F le_rfl]; exact hd j)
    (Chapter03.algorithm_3_1_3_rounds fp _ b y hy) (Chapter03.algorithm_3_1_4_rounds fp _ y x hx)
  exact ⟨E, hAx, by simpa using hE⟩

/-! ### §4.2.7 The `L D Lᵀ` factorization with symmetric pivoting -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The pivot of step `k` of Algorithm 4.2.2: the first index `j ≥ k` with
`a_jj = max {a_kk, …, a_nn}` (exact comparisons of the stored values). -/
noncomputable def diagPivot (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : Fin n :=
  ((List.finRange n).filter (k ≤ ·)).foldl (fun (b i : Fin n) => if A b b < A i i then i else b) k

/-- Step `k` of Algorithm 4.2.2, the loop body: the pivot `diagPivot`, the symmetric interchange,
the multipliers `v/α` and the update of the trailing block (see `algorithm_4_2_2`). -/
noncomputable def ldltPivotStep (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) (k : Fin n) :
    M (Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) := do
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
  pure (C, Function.update st.2 k j)

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
  (List.finRange n).foldlM (ldltPivotStep rnd) (A, fun i => i)

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

/-! ### Algorithms 4.2.3–4.2.4: block Cholesky -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **The lower triangle of Algorithm 4.2.1**, the Cholesky factor that the block algorithms store:
`F − strictUpper F` for the output `F` of Algorithm 4.2.1 (zeroing the untouched upper triangle is
exact). -/
noncomputable def choleskyLower {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    M (Matrix (Fin m) (Fin m) ℝ) := do
  let F ← algorithm_4_2_1 rnd A
  pure (F - F.strictUpper)

/-- **The multiple-right-hand-side triangular solve** `X Gᵀ = B` (Step 2 of Algorithm 4.2.3), row
by row: row `i` of `B` is overwritten by the solution of `G xᵀ = B(i, :)ᵀ`, computed by chapter 3's
Algorithm 3.1.3. -/
noncomputable def solveRowsLower {m r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ)
    (B : Matrix (Fin m) (Fin r) ℝ) : M (Matrix (Fin m) (Fin r) ℝ) :=
  (List.finRange m).foldlM (fun (X : Matrix (Fin m) (Fin r) ℝ) (i : Fin m) => do
    let x ← Chapter03.algorithm_3_1_3 rnd G (B i)
    pure (X.updateRow i x)) B

/-- **The block update** `C − X Yᵀ` of block Cholesky (the book's `Ã = A₂₂ − G₂₁G₂₁ᵀ` and
`S = A_ij − ∑_{k<j} G_ik G_jkᵀ`), entry by entry: the entry `(i, j)` is the running difference of
`C i j` and the products `X i k * Y j k`, `k` along `o` (`runningDiff`). -/
noncomputable def mulTransposeDiff {m m' : ℕ} {ι : Type} (o : List ι)
    (C : Matrix (Fin m) (Fin m') ℝ) (X : Matrix (Fin m) ι ℝ) (Y : Matrix (Fin m') ι ℝ) :
    M (Matrix (Fin m) (Fin m') ℝ) :=
  (List.finRange m).foldlM (fun (D : Matrix (Fin m) (Fin m') ℝ) (i : Fin m) =>
    (List.finRange m').foldlM (fun (D : Matrix (Fin m) (Fin m') ℝ) (j : Fin m') => do
      let t ← runningDiff rnd o (X i) (Y j) (C i j)
      pure (D.updateRow i (Function.update (D i) j t))) D) C

/-- **Algorithm 4.2.3 (Recursive Block Cholesky).** "Suppose `A ∈ ℝⁿˣⁿ` is symmetric positive
definite and `r` is a positive integer. The following algorithm computes a lower triangular
`G ∈ ℝⁿˣⁿ` so `A = GGᵀ`":
```
function G = BlockCholesky(A, n, r)
if n ≤ r
    Compute the Cholesky factorization A = GGᵀ.
else
    Compute the Cholesky factorization A(1:r, 1:r) = G₁₁G₁₁ᵀ.
    Solve G₂₁G₁₁ᵀ = A(r+1:n, 1:r) for G₂₁.
    Ã = A(r+1:n, r+1:n) − G₂₁G₂₁ᵀ
    G₂₂ = BlockCholesky(Ã, n − r, r)
    G = [G₁₁ 0; G₂₁ G₂₂]
end
```
The Cholesky factorizations are Algorithm 4.2.1, whose lower triangle is returned
(`choleskyLower`); `G₂₁` is solved row by row by chapter 3's
Algorithm 3.1.3 (`solveRowsLower`); `Ã` is formed by running differences (`mulTransposeDiff`,
without exploiting symmetry). The blocks are read along
`finSumFinEquiv : Fin r ⊕ Fin (n − r) ≃ Fin (r + (n − r))` and `n = r + (n − r)`; the recursion is
on `n`, which decreases since `0 < r`. -/
noncomputable def algorithm_4_2_3 (r : ℕ) (hr : 0 < r) :
    (n : ℕ) → Matrix (Fin n) (Fin n) ℝ → M (Matrix (Fin n) (Fin n) ℝ)
  | n, A =>
    if h : n ≤ r then choleskyLower rnd A
    else do
      let e : Fin r ⊕ Fin (n - r) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
      let B := A.submatrix e e
      let G₁₁ ← choleskyLower rnd B.toBlocks₁₁
      let G₂₁ ← solveRowsLower rnd G₁₁ B.toBlocks₂₁
      let Ã ← mulTransposeDiff rnd (List.finRange r) B.toBlocks₂₂ G₂₁ G₂₁
      let G₂₂ ← algorithm_4_2_3 r hr (n - r) Ã
      pure ((fromBlocks G₁₁ 0 G₂₁ G₂₂).submatrix e.symm e.symm)
  termination_by n => n
  decreasing_by omega

end Programs

/-- In exact arithmetic the stored lower triangle of Algorithm 4.2.1 is the Cholesky factor. -/
theorem choleskyLower_id {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    Id.run (choleskyLower (M := Id) pure A) = cholesky A := by
  rw [choleskyLower, Id.run_bind, Id.run_pure]
  exact algorithm_4_2_1_lower_eq_cholesky A

/-- In exact arithmetic the row-by-row solve computes forward substitution on every row. -/
theorem solveRowsLower_id {m r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ)
    (B : Matrix (Fin m) (Fin r) ℝ) :
    Id.run (solveRowsLower (M := Id) pure G B) = of fun i => G.forwardSubst (B i) := by
  suffices h : ∀ (l : List (Fin m)) (X : Matrix (Fin m) (Fin r) ℝ),
      Id.run (l.foldlM (fun (X : Matrix (Fin m) (Fin r) ℝ) (i : Fin m) => do
        let x ← Chapter03.algorithm_3_1_3 (M := Id) pure G (B i)
        pure (X.updateRow i x)) X) = of fun i => if i ∈ l then G.forwardSubst (B i) else X i by
    rw [solveRowsLower, h]
    ext i j
    simp
  intro l
  induction l with
  | nil => intro X; ext i j; simp
  | cons a l ih =>
    intro X
    rw [List.foldlM_cons, Id.run_bind, Id.run_bind, Id.run_pure, ih,
      Chapter03.algorithm_3_1_3_eq_forwardSubst]
    ext i j
    by_cases hi : i = a
    · subst hi
      by_cases hl : i ∈ l <;> simp [hl]
    · by_cases hl : i ∈ l <;> simp [hl, hi]

/-- In exact arithmetic the block update computes `C − ∑_{k ∈ o} X i k Y j k` in every entry. -/
theorem mulTransposeDiff_id {m m' : ℕ} {ι : Type} (o : List ι) (C : Matrix (Fin m) (Fin m') ℝ)
    (X : Matrix (Fin m) ι ℝ) (Y : Matrix (Fin m') ι ℝ) :
    Id.run (mulTransposeDiff (M := Id) pure o C X Y) =
      of fun i j => C i j - (o.map fun k => X i k * Y j k).sum := by
  have inner : ∀ (i : Fin m) (l : List (Fin m')) (D : Matrix (Fin m) (Fin m') ℝ),
      Id.run (l.foldlM (fun (D : Matrix (Fin m) (Fin m') ℝ) (j : Fin m') => do
        let t ← runningDiff (M := Id) pure o (X i) (Y j) (C i j)
        pure (D.updateRow i (Function.update (D i) j t))) D) =
        of fun a b => if a = i ∧ b ∈ l then C a b - (o.map fun k => X a k * Y b k).sum
          else D a b := by
    intro i l
    induction l with
    | nil => intro D; ext a b; simp
    | cons c l ih =>
      intro D
      rw [List.foldlM_cons, Id.run_bind, Id.run_bind, Id.run_pure, ih, runningDiff_id]
      ext a b
      by_cases ha : a = i
      · subst ha
        by_cases hb : b = c
        · subst hb; by_cases hl : b ∈ l <;> simp [hl]
        · by_cases hl : b ∈ l <;> simp [hl, hb]
      · simp [ha]
  have outer : ∀ (l : List (Fin m)) (D : Matrix (Fin m) (Fin m') ℝ),
      Id.run (l.foldlM (fun (D : Matrix (Fin m) (Fin m') ℝ) (i : Fin m) =>
        (List.finRange m').foldlM (fun (D : Matrix (Fin m) (Fin m') ℝ) (j : Fin m') => do
          let t ← runningDiff (M := Id) pure o (X i) (Y j) (C i j)
          pure (D.updateRow i (Function.update (D i) j t))) D) D) =
        of fun a b => if a ∈ l then C a b - (o.map fun k => X a k * Y b k).sum else D a b := by
    intro l
    induction l with
    | nil => intro D; ext a b; simp
    | cons c l ih =>
      intro D
      rw [List.foldlM_cons, Id.run_bind, inner, ih]
      ext a b
      by_cases ha : a = c
      · subst ha; by_cases hl : a ∈ l <;> simp [hl]
      · by_cases hl : a ∈ l <;> simp [hl, ha]
  rw [mulTransposeDiff, outer]
  ext a b
  simp

/-- Reindexing along a cast of `Fin` commutes with the Cholesky factor. -/
private theorem cholesky_submatrix_finCongr {m k : ℕ} (h : m = k) (A : Matrix (Fin k) (Fin k) ℝ) :
    cholesky (A.submatrix (finCongr h) (finCongr h)) =
      (cholesky A).submatrix (finCongr h) (finCongr h) := by
  subst h
  simp

/-- **Exact correctness of Algorithm 4.2.3**: for a symmetric positive definite `A` and `0 < r`,
the exact run is the Cholesky factor, `G = cholesky A`. By strong induction on `n`: the base case
is `algorithm_4_2_1_lower_eq_cholesky`; the step compares the blocks with (4.2.18): `G₁₁` is the
Cholesky factor of `A₁₁`, the rows of `G₂₁` solve `G₁₁ gᵀ = a` (unique, `G₁₁` lower triangular
with positive diagonal), and `Ã = A₂₂ − G₂₁G₂₁ᵀ` is the positive definite Schur complement. -/
theorem algorithm_4_2_3_spec {r : ℕ} (hr : 0 < r) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) : Id.run (algorithm_4_2_3 pure r hr n A) = cholesky A := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [algorithm_4_2_3]
  split_ifs with h
  · exact choleskyLower_id A
  have hn : r + (n - r) = n := by omega
  set A₀ : Matrix (Fin (r + (n - r))) (Fin (r + (n - r))) ℝ :=
    A.submatrix (finCongr hn) (finCongr hn) with hA₀
  have hA₀pd : A₀.PosDef := hA.submatrix (finCongr hn).injective
  set A' := A₀.submatrix finSumFinEquiv finSumFinEquiv with hA'
  have hA'pd : A'.PosDef := hA₀pd.submatrix finSumFinEquiv.injective
  have hB : A.submatrix (finSumFinEquiv.trans (finCongr hn)) (finSumFinEquiv.trans (finCongr hn)) =
      A' := rfl
  obtain ⟨h12, h11', h21', -, hS, h11, h22⟩ := equation_4_2_18 hA₀pd
  set G' := (cholesky A₀).submatrix finSumFinEquiv finSumFinEquiv with hG'
  simp only [Id.run_bind, Id.run_pure]
  rw [hB, choleskyLower_id, solveRowsLower_id, mulTransposeDiff_id]
  have h11pd : A'.toBlocks₁₁.PosDef := hA'pd.submatrix Sum.inl_injective
  -- the rows of `G₂₁` solve `G₁₁ gᵀ = a`
  have hG21 : (of fun i => (cholesky A'.toBlocks₁₁).forwardSubst (A'.toBlocks₂₁ i)) =
      G'.toBlocks₂₁ := by
    ext i j
    have hx : cholesky A'.toBlocks₁₁ *ᵥ G'.toBlocks₂₁ i = A'.toBlocks₂₁ i := by
      ext k
      rw [h21', ← h11]
      simp only [mulVec, dotProduct, mul_apply, transpose_apply]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [of_apply, forwardSubst_eq_of_mulVec_eq _ (isLowerTriangular_cholesky _)
      (fun k => (cholesky_diag_pos h11pd k).ne') hx]
  -- the updated block is the Schur complement, which is positive definite
  have hÃ : (of fun i j => A'.toBlocks₂₂ i j -
      ((List.finRange r).map fun k => G'.toBlocks₂₁ i k * G'.toBlocks₂₁ j k).sum) =
      A'.toBlocks₂₂ - G'.toBlocks₂₁ * G'.toBlocks₂₁ᵀ := by
    ext i j
    rw [of_apply, ← Fin.sum_univ_def, Matrix.sub_apply, mul_apply]
    rfl
  have hsym : A'.toBlocks₁₂ = A'.toBlocks₂₁ᵀ := by
    ext i j
    have := hA'pd.1.apply (Sum.inl i) (Sum.inr j)
    simpa [toBlocks₁₂, toBlocks₂₁] using this.symm
  have hSpd : (A'.toBlocks₂₂ - A'.toBlocks₂₁ * A'.toBlocks₁₁⁻¹ * A'.toBlocks₂₁ᵀ).PosDef := by
    have := hA'pd.schurComplement
    rwa [schurComplement_eq, hsym] at this
  rw [hG21, hÃ, hS, ih (n - r) (by omega) hSpd, ← h11, ← h22, ← h12, fromBlocks_toBlocks, hG',
    hA₀, cholesky_submatrix_finCongr]
  ext i j
  simp

/-- `updateBlock A i j X` overwrites the `r × r` block `(i, j)` of `A`, in the blocking (4.2.19)
along `finProdFinEquiv`, with `X`. -/
def updateBlock {N r : ℕ} (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) (i j : Fin N)
    (X : Matrix (Fin r) (Fin r) ℝ) : Matrix (Fin (N * r)) (Fin (N * r)) ℝ :=
  of fun a b => if (finProdFinEquiv.symm a).1 = i ∧ (finProdFinEquiv.symm b).1 = j then
    X (finProdFinEquiv.symm a).2 (finProdFinEquiv.symm b).2 else A a b

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One block of Algorithm 4.2.4, the pair `(i, j)` with `i ≥ j`: "Compute
`S = A_ij − ∑_{k=1}^{j−1} G_ik G_jkᵀ`. If `i = j` compute the Cholesky factorization
`S = G_jj G_jjᵀ`, else solve `G_ij G_jjᵀ = S` for `G_ij`. `A_ij = G_ij`". `S` is formed by running
differences over the pairs `(k, s)`, `k < j`, of the block columns already overwritten
(`mulTransposeDiff`); the Cholesky factor is `choleskyLower`, the solve is row by row by
Algorithm 3.1.3 (`solveRowsLower`) with the stored `G_jj`. -/
noncomputable def blockCholeskyStep {N r : ℕ} (j i : Fin N)
    (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) : M (Matrix (Fin (N * r)) (Fin (N * r)) ℝ) := do
  let S ← mulTransposeDiff rnd ((List.finRange N).filter (· < j) ×ˢ List.finRange r)
    (blockOf A i j) (of fun p ks => A (finProdFinEquiv (i, p)) (finProdFinEquiv ks))
    (of fun q ks => A (finProdFinEquiv (j, q)) (finProdFinEquiv ks))
  let G ← (if i = j then choleskyLower rnd S else solveRowsLower rnd (blockOf A j j) S)
  pure (updateBlock A i j G)

/-- **Algorithm 4.2.4 (Nonrecursive Block Cholesky).** "Given a symmetric positive definite
`A ∈ ℝⁿˣⁿ` with `n = Nr` with blocking (4.2.19), the following algorithm computes a lower
triangular `G ∈ ℝⁿˣⁿ` such that `A = GGᵀ`. The lower triangular part of `A` is overwritten by the
lower triangular part of `G`":
```
for j = 1:N
    for i = j:N
        Compute S = A_ij − ∑_{k=1}^{j−1} G_ik G_jkᵀ.
        if i = j
            Compute Cholesky factorization S = G_jj G_jjᵀ.
        else
            Solve G_ij G_jjᵀ = S for G_ij.
        end
        A_ij = G_ij
    end
end
```
The input is `Matrix (Fin (N * r)) (Fin (N * r)) ℝ`, its blocks `blockOf A i j` read along
`finProdFinEquiv`; the loop body is `blockCholeskyStep`. The diagonal blocks store the lower
triangle of the factor, so their strict upper triangles are zeroed. -/
noncomputable def algorithm_4_2_4 (N r : ℕ) (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) :
    M (Matrix (Fin (N * r)) (Fin (N * r)) ℝ) :=
  (List.finRange N).foldlM (fun (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) (j : Fin N) =>
    ((List.finRange N).filter (j ≤ ·)).foldlM
      (fun (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) (i : Fin N) => blockCholeskyStep rnd j i A)
      A) A

end Programs

/-- A fold satisfies a property of the processed prefix, if every step does. -/
private theorem foldl_prefix_induction {α β : Type*} (f : β → α → β) (l : List α)
    (P : List α → β → Prop) {b : β} (h0 : P [] b)
    (hs : ∀ p a q s, l = p ++ a :: q → P p s → P (p ++ [a]) (f s a)) : P l (l.foldl f b) := by
  suffices h : ∀ q p s, l = p ++ q → P p s → P l (q.foldl f s) from h l [] b rfl h0
  intro q
  induction q with
  | nil => intro p s hl hp; simpa [hl] using hp
  | cons a q ih =>
    intro p s hl hp
    exact ih (p ++ [a]) (f s a) (by simp [hl]) (hs p a q s hl hp)

/-- The matrix whose blocks `(i, k)` with `P i k` are those of `G`, the others those of `A`. -/
private def blockMix {N r : ℕ} (A G : Matrix (Fin (N * r)) (Fin (N * r)) ℝ)
    (P : Fin N → Fin N → Bool) : Matrix (Fin (N * r)) (Fin (N * r)) ℝ :=
  of fun a b => if P (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm b).1 then G a b else A a b

private theorem blockMix_apply {N r : ℕ} (A G : Matrix (Fin (N * r)) (Fin (N * r)) ℝ)
    (P : Fin N → Fin N → Bool) (i k : Fin N) (p q : Fin r) :
    blockMix A G P (finProdFinEquiv (i, p)) (finProdFinEquiv (k, q)) =
      if P i k then G (finProdFinEquiv (i, p)) (finProdFinEquiv (k, q))
      else A (finProdFinEquiv (i, p)) (finProdFinEquiv (k, q)) := by
  simp only [blockMix, of_apply, Equiv.symm_apply_apply]

private theorem blockOf_blockMix {N r : ℕ} (A G : Matrix (Fin (N * r)) (Fin (N * r)) ℝ)
    (P : Fin N → Fin N → Bool) (i k : Fin N) :
    blockOf (blockMix A G P) i k = if P i k then blockOf G i k else blockOf A i k := by
  ext p q
  simp only [blockOf, of_apply, blockMix_apply]
  split_ifs <;> rfl

private theorem updateBlock_blockMix {N r : ℕ} (A G : Matrix (Fin (N * r)) (Fin (N * r)) ℝ)
    (P : Fin N → Fin N → Bool) (i j : Fin N) :
    updateBlock (blockMix A G P) i j (blockOf G i j) =
      blockMix A G fun a b => P a b || (a == i && b == j) := by
  ext a b
  obtain ⟨⟨a₁, a₂⟩, rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨b₁, b₂⟩, rfl⟩ := finProdFinEquiv.surjective b
  simp only [updateBlock, of_apply, Equiv.symm_apply_apply, blockMix_apply, blockOf,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  by_cases h : a₁ = i ∧ b₁ = j
  · obtain ⟨rfl, rfl⟩ := h
    rw [ite_eq_left ⟨rfl, rfl⟩, ite_eq_left (Or.inr ⟨rfl, rfl⟩)]
  · rw [ite_eq_right h]
    by_cases hP : P a₁ b₁ = true
    · rw [ite_eq_left hP, ite_eq_left (Or.inl hP)]
    · rw [ite_eq_right hP, ite_eq_right (by tauto)]

/-- One step of Algorithm 4.2.4 in exact arithmetic. -/
private theorem blockCholeskyStep_id {N r : ℕ} (j i : Fin N)
    (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) :
    Id.run (blockCholeskyStep (M := Id) pure j i A) = updateBlock A i j
      (if i = j then cholesky (of fun a b => blockOf A i j a b -
          (((List.finRange N).filter (· < j) ×ˢ List.finRange r).map fun ks =>
            A (finProdFinEquiv (i, a)) (finProdFinEquiv ks) *
              A (finProdFinEquiv (j, b)) (finProdFinEquiv ks)).sum)
        else of fun a => (blockOf A j j).forwardSubst ((of fun a b => blockOf A i j a b -
          (((List.finRange N).filter (· < j) ×ˢ List.finRange r).map fun ks =>
            A (finProdFinEquiv (i, a)) (finProdFinEquiv ks) *
              A (finProdFinEquiv (j, b)) (finProdFinEquiv ks)).sum) a)) := by
  rw [blockCholeskyStep, Id.run_bind, mulTransposeDiff_id, Id.run_bind, Id.run_pure]
  congr 1
  split_ifs
  · exact choleskyLower_id _
  · exact solveRowsLower_id _ _

/-- **Exact correctness of Algorithm 4.2.4**: for a symmetric positive definite `A` with
`n = N r`, the lower triangle of the exact run is the Cholesky factor, `G = cholesky A`. Induction
over the block columns, and within a column over the block rows, with the invariant that the blocks
already visited are those of `G`: the block `S` is then `A_ij − ∑_{k<j} G_ik G_jkᵀ`, whose
Cholesky factor is `G_jj` and for which `G_ij G_jjᵀ = S` (4.2.19), the solution of the triangular
system being unique. -/
theorem algorithm_4_2_4_spec {N r : ℕ} {A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ}
    (hA : A.PosDef) :
    Id.run (algorithm_4_2_4 pure N r A) - (Id.run (algorithm_4_2_4 pure N r A)).strictUpper =
      cholesky A := by
  have h19 := equation_4_2_19 hA
  have hsorted := List.pairwise_lt_finRange N
  -- the invariant of the column loop
  have hcol : ∀ (p : List (Fin N)) (j : Fin N) (q : List (Fin N)), List.finRange N = p ++ j :: q →
      ((List.finRange N).filter (j ≤ ·)).foldl
        (fun s i => Id.run (blockCholeskyStep (M := Id) pure j i s))
        (blockMix A (cholesky A) fun i k => decide (k ∈ p ∧ k ≤ i)) =
        blockMix A (cholesky A) fun i k => decide (k ∈ p ++ [j] ∧ k ≤ i) := by
    intro p j q hpq
    have hp : ∀ k, k ∈ p ↔ k < j := fun k => by
      refine ⟨fun hk => ?_, fun hk => Chapter03.mem_prefix_of_pairwise hsorted hpq
        (List.mem_finRange k) (ne_of_lt hk) (lt_asymm hk)⟩
      have hs := hsorted
      rw [hpq] at hs
      exact (List.pairwise_append.1 hs).2.2 k hk j List.mem_cons_self
    set L := (List.finRange N).filter (j ≤ ·) with hLdef
    have hLmem : ∀ i, i ∈ L ↔ j ≤ i := fun i => by simp [hLdef]
    have hLsorted : L.Pairwise (· < ·) := hsorted.filter _
    have hLnodup : L.Nodup := (List.nodup_finRange N).filter _
    have e0 : (fun i k => decide (k ∈ p ∧ k ≤ i)) =
        fun i k => decide ((k ∈ p ∧ k ≤ i) ∨ (k = j ∧ i ∈ ([] : List (Fin N)))) := by
      funext i k
      simp
    have e1 : (fun i k => decide ((k ∈ p ∧ k ≤ i) ∨ (k = j ∧ i ∈ L))) =
        fun i k => decide (k ∈ p ++ [j] ∧ k ≤ i) := by
      funext i k
      simp only [hLmem, List.mem_append, List.mem_singleton, decide_eq_decide]
      constructor
      · rintro (⟨hk, hki⟩ | ⟨rfl, hki⟩)
        · exact ⟨Or.inl hk, hki⟩
        · exact ⟨Or.inr rfl, hki⟩
      · rintro ⟨hk | rfl, hki⟩
        · exact Or.inl ⟨hk, hki⟩
        · exact Or.inr ⟨rfl, hki⟩
    rw [e0, ← e1]
    refine foldl_prefix_induction _ L (fun p' s => s = blockMix A (cholesky A)
      fun i k => decide ((k ∈ p ∧ k ≤ i) ∨ (k = j ∧ i ∈ p'))) rfl fun p' i q' s hL hs => ?_
    subst hs
    have hiL : j ≤ i := (hLmem i).1 (by rw [hL]; simp)
    have hip' : i ∉ p' := by
      have hn := hLnodup
      rw [hL] at hn
      exact fun h => (List.nodup_append.1 hn).2.2 i h i List.mem_cons_self rfl
    -- the entries read by the step
    have hG : ∀ (a k : Fin N), k < j → j ≤ a → ∀ (x y : Fin r),
        blockMix A (cholesky A) (fun i k => decide ((k ∈ p ∧ k ≤ i) ∨ (k = j ∧ i ∈ p')))
          (finProdFinEquiv (a, x)) (finProdFinEquiv (k, y)) =
          cholesky A (finProdFinEquiv (a, x)) (finProdFinEquiv (k, y)) := by
      intro a k hk hja x y
      rw [blockMix_apply, ite_eq_left]
      simp [(hp k).2 hk, hk.le.trans hja]
    have hij : blockOf (blockMix A (cholesky A)
        fun i k => decide ((k ∈ p ∧ k ≤ i) ∨ (k = j ∧ i ∈ p'))) i j = blockOf A i j := by
      rw [blockOf_blockMix, ite_eq_right]
      simp [hip', hp]
    have hnd : ((List.finRange N).filter (· < j) ×ˢ List.finRange r).Nodup :=
      ((List.nodup_finRange N).filter _).product (List.nodup_finRange r)
    have hfs : ((List.finRange N).filter (· < j) ×ˢ List.finRange r).toFinset =
        Finset.univ.filter (· < j) ×ˢ Finset.univ := by
      ext ⟨k, t⟩
      simp
    have hS : (of fun a b => blockOf (blockMix A (cholesky A)
        fun i k => decide ((k ∈ p ∧ k ≤ i) ∨ (k = j ∧ i ∈ p'))) i j a b -
          (((List.finRange N).filter (· < j) ×ˢ List.finRange r).map fun ks =>
            blockMix A (cholesky A) (fun i k => decide ((k ∈ p ∧ k ≤ i) ∨ (k = j ∧ i ∈ p')))
              (finProdFinEquiv (i, a)) (finProdFinEquiv ks) *
            blockMix A (cholesky A) (fun i k => decide ((k ∈ p ∧ k ≤ i) ∨ (k = j ∧ i ∈ p')))
              (finProdFinEquiv (j, b)) (finProdFinEquiv ks)).sum) =
        blockOf A i j - ∑ k ∈ Finset.univ.filter (· < j),
          blockOf (cholesky A) i k * (blockOf (cholesky A) j k)ᵀ := by
      rw [hij]
      ext a b
      rw [of_apply, ← List.sum_toFinset _ hnd, hfs, Finset.sum_product, Matrix.sub_apply,
        Matrix.sum_apply]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkj : k < j := (Finset.mem_filter.1 hk).2
      rw [mul_apply]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hG i k hkj hiL a y, hG j k hkj le_rfl b y]
      simp [blockOf]
    have e2 : (fun a b => decide ((b ∈ p ∧ b ≤ a) ∨ (b = j ∧ a ∈ p')) || (a == i && b == j)) =
        fun a b => decide ((b ∈ p ∧ b ≤ a) ∨ (b = j ∧ a ∈ p' ++ [i])) := by
      funext a b
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
        List.mem_append, List.mem_singleton]
      tauto
    change _ = blockMix A (cholesky A)
      fun a b => decide ((b ∈ p ∧ b ≤ a) ∨ (b = j ∧ a ∈ p' ++ [i]))
    rw [← e2, ← updateBlock_blockMix, blockCholeskyStep_id, hS]
    congr 1
    by_cases hij' : i = j
    · subst hij'
      rw [ite_eq_left rfl, (h19 i i).2.2.1]
    · have hji : j < i := lt_of_le_of_ne hiL (Ne.symm hij')
      have hjp' : j ∈ p' := Chapter03.mem_prefix_of_pairwise hLsorted hL ((hLmem j).2 le_rfl)
        (Ne.symm hij') (lt_asymm hji)
      rw [ite_eq_right hij', blockOf_blockMix, ite_eq_left (by simp [hjp'])]
      have hlow : (blockOf (cholesky A) j j).IsLowerTriangular := by
        rw [(h19 j j).2.2.1]
        exact isLowerTriangular_cholesky _
      have hdiag : ∀ x, blockOf (cholesky A) j j x x ≠ 0 := fun x =>
        (cholesky_diag_pos hA (finProdFinEquiv (j, x))).ne'
      ext a b
      have hx : blockOf (cholesky A) j j *ᵥ blockOf (cholesky A) i j a = (blockOf A i j -
          ∑ k ∈ Finset.univ.filter (· < j),
            blockOf (cholesky A) i k * (blockOf (cholesky A) j k)ᵀ) a := by
        rw [← (h19 i j).2.2.2 hji]
        ext c
        simp only [mulVec, dotProduct, mul_apply, transpose_apply]
        exact Finset.sum_congr rfl fun l _ => mul_comm _ _
      rw [of_apply, forwardSubst_eq_of_mulVec_eq _ hlow hdiag hx]
  have hfin : (List.finRange N).foldl (fun s j => ((List.finRange N).filter (j ≤ ·)).foldl
      (fun s i => Id.run (blockCholeskyStep (M := Id) pure j i s)) s) A =
      blockMix A (cholesky A) fun i k => decide (k ∈ List.finRange N ∧ k ≤ i) :=
    foldl_prefix_induction _ (List.finRange N)
      (fun p s => s = blockMix A (cholesky A) fun i k => decide (k ∈ p ∧ k ≤ i))
      (by ext a b; simp [blockMix]) fun p j q s hpq hs => by
        subst hs
        exact hcol p j q hpq
  rw [algorithm_4_2_4, List.idRun_foldlM]
  simp only [List.idRun_foldlM]
  rw [hfin]
  ext a b
  obtain ⟨⟨i, p⟩, rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨k, q⟩, rfl⟩ := finProdFinEquiv.surjective b
  rw [Matrix.sub_apply]
  by_cases hlt : finProdFinEquiv (i, p) < finProdFinEquiv (k, q)
  · simp only [strictUpper, of_apply, ite_eq_left hlt, sub_self]
    exact (isLowerTriangular_cholesky A (OrderDual.toDual_lt_toDual.2 hlt)).symm
  · simp only [strictUpper, of_apply, ite_eq_right hlt, sub_zero]
    have hki : k ≤ i := not_lt.1 fun h => hlt (finProdFinEquiv_lt h p q)
    rw [blockMix_apply, ite_eq_left (by simp [hki])]

/-! ### Algorithm 4.2.2: the exact specification ((4.2.16), (4.2.17)) -/

/-- One elimination step of Algorithm 4.2.2 in exact arithmetic: the multipliers
`a_ik / a_kk` below the pivot and the update `a_il − a_ik a_lk / a_kk` of the trailing block. -/
noncomputable def pivotElim (k : Fin n) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i l => if k < i ∧ k < l then A i l - A i k * A l k / A k k
    else if l = k ∧ k < i then A i k / A k k else A i l

/-- A fold writing one entry of a fixed column per row, with values not depending on the state. -/
private theorem foldl_updateRow_col_const (k : Fin n) (w : Fin n → ℝ) (L : List (Fin n))
    (D : Matrix (Fin n) (Fin n) ℝ) :
    L.foldl (fun (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
        B.updateRow i (Function.update (B i) k (w i))) D =
      of fun a b => if b = k ∧ a ∈ L then w a else D a b := by
  induction L generalizing D with
  | nil => ext a b; simp
  | cons c L ih =>
    rw [List.foldl_cons, ih]
    ext a b
    by_cases ha : a = c
    · subst ha
      by_cases hb : b = k <;> simp [hb]
    · by_cases hb : b = k <;> simp [hb, ha]

/-- A fold subtracting from the entries `(i, l)`, `l` along a duplicate-free list. -/
private theorem foldl_updateRow_sub (i : Fin n) (w : Fin n → ℝ) {L : List (Fin n)}
    (hL : L.Nodup) (D : Matrix (Fin n) (Fin n) ℝ) :
    L.foldl (fun (C : Matrix (Fin n) (Fin n) ℝ) (l : Fin n) =>
        C.updateRow i (Function.update (C i) l (C i l - w l))) D =
      of fun a b => if a = i ∧ b ∈ L then D a b - w b else D a b := by
  induction L generalizing D with
  | nil => ext a b; simp
  | cons c L ih =>
    rcases List.nodup_cons.1 hL with ⟨hc, hL'⟩
    rw [List.foldl_cons, ih hL']
    ext a b
    by_cases ha : a = i
    · subst ha
      by_cases hb : b = c
      · subst hb
        simp [hc]
      · by_cases hbL : b ∈ L <;> simp [hb, hbL]
    · simp [ha]

/-- The rank-one update of the trailing block, rows and columns along a duplicate-free list. -/
private theorem foldl_foldl_updateRow_sub (w : Fin n → Fin n → ℝ) {L : List (Fin n)}
    (hL : L.Nodup) (D : Matrix (Fin n) (Fin n) ℝ) :
    L.foldl (fun (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
      L.foldl (fun (C : Matrix (Fin n) (Fin n) ℝ) (l : Fin n) =>
        C.updateRow i (Function.update (C i) l (C i l - w i l))) C) D =
      of fun a b => if a ∈ L ∧ b ∈ L then D a b - w a b else D a b := by
  suffices h : ∀ (L' : List (Fin n)), L'.Nodup → ∀ D : Matrix (Fin n) (Fin n) ℝ,
      L'.foldl (fun (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
        L.foldl (fun (C : Matrix (Fin n) (Fin n) ℝ) (l : Fin n) =>
          C.updateRow i (Function.update (C i) l (C i l - w i l))) C) D =
        of fun a b => if a ∈ L' ∧ b ∈ L then D a b - w a b else D a b from h L hL D
  intro L' hL'
  induction L' with
  | nil => intro D; ext a b; simp
  | cons c L' ih =>
    intro D
    rcases List.nodup_cons.1 hL' with ⟨hc, hL''⟩
    rw [List.foldl_cons, foldl_updateRow_sub c (w c) hL, ih hL'']
    ext a b
    by_cases ha : a = c
    · subst ha
      simp [hc]
    · simp [ha]

/-- **The exact step of Algorithm 4.2.2**: interchange by the diagonal pivot, then eliminate. -/
theorem ldltPivotStep_id (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) (k : Fin n) :
    Id.run (ldltPivotStep (M := Id) pure st k) =
      (pivotElim k (st.1.submatrix (Equiv.swap k (diagPivot st.1 k))
        (Equiv.swap k (diagPivot st.1 k))), Function.update st.2 k (diagPivot st.1 k)) := by
  simp only [ldltPivotStep, Id.run_bind, Id.run_pure, List.idRun_foldlM]
  rw [foldl_updateRow_col_const, foldl_foldl_updateRow_sub _ ((List.nodup_finRange n).filter _)]
  congr 1
  ext a b
  simp only [pivotElim, of_apply, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  by_cases hab : k < a ∧ k < b
  · rw [ite_eq_left hab, ite_eq_left hab, ite_eq_right (fun h => (ne_of_gt hab.2) h.1)]
  · rw [ite_eq_right hab, ite_eq_right hab]


/-- The unit lower triangular `L_k` of the pivoted `L D Lᵀ` after `k` steps ((4.2.16)): the first
`k` columns of the packed state `S` below the diagonal, and the identity elsewhere. -/
def pivotedLower (k : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if (j : ℕ) < k ∧ j < i then S i j else if i = j then 1 else 0

/-- The middle factor `diag(D_k, A_k)` of the pivoted `L D Lᵀ` after `k` steps ((4.2.16)): the
diagonal `d₁, …, d_k` of the packed state `S` and its trailing block `A_k = S(k+1:n, k+1:n)`. -/
def pivotedMiddle (k : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if (i : ℕ) < k ∨ (j : ℕ) < k then (if i = j then S i j else 0) else S i j

/-- `L_k` commutes with a symmetric permutation that fixes the first `k` indices. -/
private theorem pivotedLower_submatrix {k : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv.Perm (Fin n)) (h1 : ∀ m : Fin n, (m : ℕ) < k → σ m = m)
    (h2 : ∀ m : Fin n, k ≤ (m : ℕ) → k ≤ (σ m : ℕ)) :
    pivotedLower k (S.submatrix σ σ) = (pivotedLower k S).submatrix σ σ := by
  ext i l
  simp only [pivotedLower, of_apply, submatrix_apply, σ.injective.eq_iff]
  by_cases hl : (l : ℕ) < k
  · have hli : l < i ↔ l < σ i := by
      by_cases hi : (i : ℕ) < k
      · rw [h1 i hi]
      · have := h2 i (not_lt.1 hi)
        simp only [Fin.lt_def]
        omega
    rw [h1 l hl]
    simp only [hli]
  · have hσl : ¬ ((σ l : ℕ) < k) := not_lt.2 (h2 l (not_lt.1 hl))
    simp [hl, hσl]

/-- `diag(D_k, A_k)` commutes with a symmetric permutation that fixes the first `k` indices. -/
private theorem pivotedMiddle_submatrix {k : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv.Perm (Fin n)) (h1 : ∀ m : Fin n, (m : ℕ) < k → σ m = m)
    (h2 : ∀ m : Fin n, k ≤ (m : ℕ) → k ≤ (σ m : ℕ)) :
    pivotedMiddle k (S.submatrix σ σ) = (pivotedMiddle k S).submatrix σ σ := by
  have hk : ∀ m : Fin n, (σ m : ℕ) < k ↔ (m : ℕ) < k := fun m =>
    ⟨fun h => by_contra fun h' => absurd h (not_lt.2 (h2 m (not_lt.1 h'))),
      fun h => by rw [h1 m h]; exact h⟩
  ext i l
  simp only [pivotedMiddle, of_apply, submatrix_apply, σ.injective.eq_iff, hk]

/-- The interchange of step `k` fixes the indices below `k` and keeps the others at or above `k`. -/
private theorem swap_fixes {k j : Fin n} (hkj : k ≤ j) :
    (∀ m : Fin n, (m : ℕ) < k → Equiv.swap k j m = m) ∧
      ∀ m : Fin n, (k : ℕ) ≤ m → (k : ℕ) ≤ (Equiv.swap k j m : ℕ) := by
  refine ⟨fun m hm => Equiv.swap_apply_of_ne_of_ne (fun h => by subst h; omega)
    (fun h => by subst h; exact absurd (Fin.le_def.1 hkj) (by omega)), fun m hm => ?_⟩
  rw [Equiv.swap_apply_def]
  split_ifs
  · exact Fin.le_def.1 hkj
  · exact le_rfl
  · exact hm

/-- The column operator of step `k`: the identity plus `w` below the diagonal of column `k`. -/
private def colOp (k : Fin n) (w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i l => if l = k ∧ k < i then w i else if i = l then 1 else 0

private theorem colOp_mul_apply (k : Fin n) (w : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (i b : Fin n) : (colOp k w * X) i b = X i b + if k < i then w i * X k b else 0 := by
  have h : ∀ a, colOp k w i a * X a b =
      (if i = a then X a b else 0) + (if a = k then (if k < i then w i * X a b else 0) else 0) := by
    intro a
    simp only [colOp, of_apply]
    by_cases hak : a = k
    · subst hak
      by_cases hi : a < i
      · simp [hi, (ne_of_gt hi)]
      · by_cases hia : i = a <;> simp [hi, hia]
    · by_cases hia : i = a <;> simp [hak, hia]
  rw [mul_apply, Finset.sum_congr rfl fun a _ => h a, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq']
  simp

private theorem mul_colOp_transpose_apply (k : Fin n) (w : Fin n → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) (i l : Fin n) :
    (X * (colOp k w)ᵀ) i l = X i l + if k < l then X i k * w l else 0 := by
  have h := colOp_mul_apply k w Xᵀ l i
  rw [← transpose_apply (X * (colOp k w)ᵀ), transpose_mul, transpose_transpose, h]
  simp [transpose_apply, mul_comm]

/-- The inverse of the column operator. -/
private theorem colOp_neg_mul_colOp (k : Fin n) (w : Fin n → ℝ) :
    colOp k (-w) * colOp k w = 1 := by
  ext i l
  rw [colOp_mul_apply]
  by_cases hl : l = k
  · subst hl
    by_cases hi : l < i
    · simp [colOp, hi, (ne_of_gt hi), one_apply]
    · simp [colOp, hi, one_apply]
  · simp [colOp, hl, Ne.symm hl, one_apply]

/-- The multipliers of step `k`. -/
private noncomputable def multipliers (k : Fin n) (A : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  fun i => A i k / A k k

/-- (4.2.16), the unit lower factor: `L_{k+1} = L_k E_k` with `E_k` the column operator of the
multipliers of step `k`. -/
private theorem pivotedLower_succ (k : Fin n) (A : Matrix (Fin n) (Fin n) ℝ) :
    pivotedLower ((k : ℕ) + 1) (pivotElim k A) =
      pivotedLower k A * colOp k (multipliers k A) := by
  ext i l
  rw [mul_apply]
  by_cases hl : l = k
  · subst hl
    rw [Finset.sum_eq_single i]
    · by_cases hi : l < i
      · simp only [pivotedLower, pivotElim, colOp, multipliers, of_apply, lt_irrefl, hi,
          Nat.lt_succ_self, and_self, and_false, ite_true, ite_false, one_mul]
      · simp only [pivotedLower, pivotElim, colOp, of_apply, lt_irrefl, hi, and_false,
          ite_true, ite_false, one_mul]
    · intro a _ hai
      by_cases ha : a < l
      · simp only [colOp, of_apply, lt_asymm ha, ne_of_lt ha, and_false, ite_false, mul_zero]
      · have ha' : ¬ ((a : ℕ) < l) := fun h => ha (Fin.lt_def.2 h)
        simp only [pivotedLower, of_apply, ha', false_and, ite_false, Ne.symm hai, zero_mul]
    · simp
  · rw [Finset.sum_eq_single l]
    · have hkl' : (l : ℕ) ≠ k := fun h => hl (Fin.ext h)
      by_cases hlk : (l : ℕ) < k
      · have hkl : ¬ k < l := fun h => absurd (Fin.lt_def.1 h) (by omega)
        have hl1 : (l : ℕ) < k + 1 := by omega
        simp only [pivotedLower, pivotElim, colOp, of_apply, hl, hlk, hl1, hkl, true_and,
          false_and, and_false, ite_false, ite_true, mul_one]
      · have hkl : ¬ (l : ℕ) < k + 1 := by omega
        simp only [pivotedLower, colOp, of_apply, hl, hlk, hkl, false_and, ite_false, ite_true,
          mul_one]
    · intro a _ hal
      simp only [colOp, of_apply, hl, hal, false_and, ite_false, mul_zero]
    · simp

/-- (4.2.16), the middle factor: `diag(D_k, A_k) = E_k diag(D_{k+1}, A_{k+1}) E_kᵀ`, provided a zero
pivot has a zero column below it and the trailing block is symmetric in its first row. -/
private theorem pivotedMiddle_eq (k : Fin n) (A : Matrix (Fin n) (Fin n) ℝ)
    (h0 : A k k = 0 → ∀ i, k < i → A i k = 0) (hsym : ∀ i, k < i → A k i = A i k) :
    pivotedMiddle k A = colOp k (multipliers k A) * pivotedMiddle ((k : ℕ) + 1) (pivotElim k A) *
      (colOp k (multipliers k A))ᵀ := by
  ext i l
  rw [mul_colOp_transpose_apply, colOp_mul_apply, colOp_mul_apply]
  have hk1 : ¬ (k : ℕ) < k := lt_irrefl _
  have hk2 : (k : ℕ) < k + 1 := Nat.lt_succ_self _
  rcases lt_trichotomy i k with hi | rfl | hi
  · have hi' : (i : ℕ) < k := Fin.lt_def.1 hi
    have hik : ¬ k < i := lt_asymm hi
    have hne : i ≠ k := ne_of_lt hi
    simp [pivotedMiddle, pivotElim, hi, hi.le, hik, hne]
  · rcases lt_trichotomy l i with hl | rfl | hl
    · have hl' : (l : ℕ) < i := Fin.lt_def.1 hl
      simp [pivotedMiddle, pivotElim, hl, lt_asymm hl, ne_of_gt hl]
    · simp [pivotedMiddle, pivotElim]
    · have hl' : ¬ (l : ℕ) < i + 1 := by have := Fin.lt_def.1 hl; omega
      have hl'' : ¬ (l : ℕ) < i := by have := Fin.lt_def.1 hl; omega
      simp only [pivotedMiddle, pivotElim, multipliers, of_apply, hl, hl', hl'', hk1, hk2,
        lt_irrefl, ne_of_lt hl, and_false, or_false, ↓reduceIte, or_true, zero_add, add_zero]
      by_cases h : A i i = 0
      · rw [h, hsym l hl, h0 h l hl]
        simp
      · rw [hsym l hl]
        field_simp
  · have hi' : ¬ (i : ℕ) < k := by have := Fin.lt_def.1 hi; omega
    have hi'' : ¬ (i : ℕ) < k + 1 := by have := Fin.lt_def.1 hi; omega
    rcases lt_trichotomy l k with hl | rfl | hl
    · have hl' : (l : ℕ) < k := Fin.lt_def.1 hl
      simp [pivotedMiddle, pivotElim, hl, hl.le, lt_asymm hl, ne_of_gt hl,
        ne_of_gt (hl.trans hi)]
    · simp only [pivotedMiddle, pivotElim, multipliers, of_apply, hi, hi', hi'', hk1, hk2,
        lt_irrefl, ne_of_gt hi, and_false, or_false, ↓reduceIte, or_true, zero_add, add_zero,
        and_self]
      by_cases h : A l l = 0
      · rw [h, h0 h i hi]
        simp
      · field_simp
    · have hl' : ¬ (l : ℕ) < k := by have := Fin.lt_def.1 hl; omega
      have hl'' : ¬ (l : ℕ) < k + 1 := by have := Fin.lt_def.1 hl; omega
      simp only [pivotedMiddle, pivotElim, multipliers, of_apply, hi, hl, hi', hi'', hl', hl'',
        hk2, lt_irrefl, ne_of_gt hi, ne_of_lt hl, and_false, or_false, ↓reduceIte, or_true,
        zero_add, mul_zero, add_zero, and_self]
      by_cases h : A k k = 0
      · simp [h]
      · field_simp
        ring

/-- The pivot of step `k` lies at or after `k` and carries the largest diagonal entry there. -/
private theorem diagPivot_spec (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    k ≤ diagPivot A k ∧ ∀ i, k ≤ i → A i i ≤ A (diagPivot A k) (diagPivot A k) := by
  have key : ∀ (l : List (Fin n)) (b : Fin n), k ≤ b → (∀ i ∈ l, k ≤ i) →
      k ≤ l.foldl (fun (b i : Fin n) => if A b b < A i i then i else b) b ∧
        A b b ≤ A (l.foldl (fun (b i : Fin n) => if A b b < A i i then i else b) b)
          (l.foldl (fun (b i : Fin n) => if A b b < A i i then i else b) b) ∧
        ∀ i ∈ l, A i i ≤ A (l.foldl (fun (b i : Fin n) => if A b b < A i i then i else b) b)
          (l.foldl (fun (b i : Fin n) => if A b b < A i i then i else b) b) := by
    intro l
    induction l with
    | nil => intro b hb _; exact ⟨hb, le_rfl, by simp⟩
    | cons c l ih =>
      intro b hb hl
      rw [List.foldl_cons]
      by_cases h : A b b < A c c
      · rw [ite_eq_left h]
        obtain ⟨h1, h2, h3⟩ := ih c (hl c List.mem_cons_self)
          fun i hi => hl i (List.mem_cons_of_mem _ hi)
        refine ⟨h1, h.le.trans h2, fun i hi => ?_⟩
        rcases List.mem_cons.1 hi with rfl | hi
        · exact h2
        · exact h3 i hi
      · rw [ite_eq_right h]
        obtain ⟨h1, h2, h3⟩ := ih b hb fun i hi => hl i (List.mem_cons_of_mem _ hi)
        refine ⟨h1, h2, fun i hi => ?_⟩
        rcases List.mem_cons.1 hi with rfl | hi
        · exact (not_lt.1 h).trans h2
        · exact h3 i hi
  obtain ⟨h1, -, h3⟩ := key ((List.finRange n).filter (k ≤ ·)) k le_rfl
    fun i hi => by simpa using hi
  exact ⟨h1, fun i hi => h3 i (by simp [hi])⟩

/-- The invariant (4.2.16) of Algorithm 4.2.2 after the steps of a prefix of `0, …, n − 1`. -/
private theorem ldltPivot_invariant {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (l : List (Fin n)) (hl : l <+: List.finRange n) :
    A.submatrix
        (Chapter03.pivPermUpTo
          (l.foldl (fun st i => Id.run (ldltPivotStep (M := Id) pure st i)) (A, fun i => i)).2
          l.length)
        (Chapter03.pivPermUpTo
          (l.foldl (fun st i => Id.run (ldltPivotStep (M := Id) pure st i)) (A, fun i => i)).2
          l.length) =
      pivotedLower l.length (l.foldl (fun st i => Id.run (ldltPivotStep (M := Id) pure st i))
          (A, fun i => i)).1 *
        pivotedMiddle l.length (l.foldl (fun st i => Id.run (ldltPivotStep (M := Id) pure st i))
          (A, fun i => i)).1 *
        (pivotedLower l.length (l.foldl (fun st i => Id.run (ldltPivotStep (M := Id) pure st i))
          (A, fun i => i)).1)ᵀ ∧
      (pivotedMiddle l.length (l.foldl (fun st i => Id.run (ldltPivotStep (M := Id) pure st i))
          (A, fun i => i)).1).PosSemidef ∧
      ∀ i j : Fin n, (i : ℕ) < l.length → i ≤ j →
        (l.foldl (fun st i => Id.run (ldltPivotStep (M := Id) pure st i))
            (A, fun i => i)).1 j j ≤
          (l.foldl (fun st i => Id.run (ldltPivotStep (M := Id) pure st i))
            (A, fun i => i)).1 i i := by
  obtain ⟨rest₀, hrest₀⟩ := hl
  refine foldl_prefix_induction _ l
    (fun pre (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) =>
    A.submatrix (Chapter03.pivPermUpTo st.2 pre.length) (Chapter03.pivPermUpTo st.2 pre.length) =
      pivotedLower pre.length st.1 * pivotedMiddle pre.length st.1 *
        (pivotedLower pre.length st.1)ᵀ ∧
      (pivotedMiddle pre.length st.1).PosSemidef ∧
      ∀ i j : Fin n, (i : ℕ) < pre.length → i ≤ j → st.1 j j ≤ st.1 i i) ?_ ?_
  · refine ⟨?_, ?_, fun i j hi => absurd hi (Nat.not_lt_zero _)⟩
    · have hL : pivotedLower 0 A = 1 := by
        ext i j
        simp [pivotedLower, one_apply]
      have hM : pivotedMiddle 0 A = A := by
        ext i j
        simp [pivotedMiddle]
      simp [Chapter03.pivPermUpTo, hL, hM]
    · have hM : pivotedMiddle 0 A = A := by
        ext i j
        simp [pivotedMiddle]
      simpa [hM] using hA
  · intro pre a rest st hpre ⟨hfac, hpsd, hdom⟩
    -- the step index is the length of the prefix
    have ha : (a : ℕ) = pre.length := by
      have hlt : pre.length < (List.finRange n).length := by
        rw [← hrest₀, hpre]
        simp
      have h1 : (List.finRange n)[pre.length]'hlt = a := by
        simp [← hrest₀, hpre]
      rw [← h1]
      simp
    rw [ldltPivotStep_id, List.length_append, List.length_singleton]
    obtain ⟨hkj, hmax⟩ := diagPivot_spec st.1 a
    set j := diagPivot st.1 a with hj
    set sw := Equiv.swap a j with hsw
    set A' := st.1.submatrix sw sw with hA'
    obtain ⟨hfix, hge⟩ := swap_fixes hkj
    rw [← ha] at hfac hpsd hdom ⊢
    -- the new permutation
    have hperm : Chapter03.pivPermUpTo (Function.update st.2 a j) ((a : ℕ) + 1) =
        Chapter03.pivPermUpTo st.2 a * sw := by
      rw [Chapter03.pivPermUpTo_succ, Function.update_self,
        Chapter03.pivPermUpTo_congr (piv' := st.2) fun m hm =>
          Function.update_of_ne (fun h => by subst h; omega) _ _]
    -- the factorization, after the interchange
    have hL' : pivotedLower a A' = (pivotedLower a st.1).submatrix sw sw :=
      pivotedLower_submatrix st.1 sw hfix hge
    have hM' : pivotedMiddle a A' = (pivotedMiddle a st.1).submatrix sw sw :=
      pivotedMiddle_submatrix st.1 sw hfix hge
    have hpsd' : (pivotedMiddle a A').PosSemidef := by
      rw [hM']
      exact hpsd.submatrix sw
    have hfac' : A.submatrix (Chapter03.pivPermUpTo st.2 a * sw)
        (Chapter03.pivPermUpTo st.2 a * sw) =
        pivotedLower a A' * pivotedMiddle a A' * (pivotedLower a A')ᵀ := by
      rw [Equiv.Perm.coe_mul, ← submatrix_submatrix, hfac, hL', hM', transpose_submatrix,
        submatrix_mul_equiv _ _ _ sw _, submatrix_mul_equiv _ _ _ sw _]
    -- the entries of the middle factor at and after the pivot
    have hmid : ∀ i l : Fin n, a ≤ i → a ≤ l → pivotedMiddle a A' i l = A' i l := by
      intro i l hi hl
      have hi' : ¬ (i : ℕ) < a := not_lt.2 (Fin.le_def.1 hi)
      have hl' : ¬ (l : ℕ) < a := not_lt.2 (Fin.le_def.1 hl)
      simp [pivotedMiddle, not_lt.2 hi, not_lt.2 hl]
    have h0 : A' a a = 0 → ∀ i, a < i → A' i a = 0 := by
      intro h i hi
      rw [← hmid a a le_rfl le_rfl] at h
      have := (hpsd'.apply_eq_zero_of_diag_eq_zero h i).2
      rwa [hmid i a hi.le le_rfl] at this
    have hsym : ∀ i, a < i → A' a i = A' i a := by
      intro i hi
      have := hpsd'.1.apply i a
      rw [hmid a i le_rfl hi.le, hmid i a hi.le le_rfl] at this
      simpa using this
    have hE := pivotedMiddle_eq a A' h0 hsym
    have hα : 0 ≤ A' a a := by
      rw [← hmid a a le_rfl le_rfl]
      exact hpsd'.diag_nonneg
    refine ⟨?_, ?_, ?_⟩
    · rw [hperm, hfac', pivotedLower_succ, hE, transpose_mul]
      simp only [Matrix.mul_assoc]
    · -- the new middle factor is congruent to the old one
      have hinv : pivotedMiddle ((a : ℕ) + 1) (pivotElim a A') =
          colOp a (-multipliers a A') * pivotedMiddle a A' *
            (colOp a (-multipliers a A'))ᵀ := by
        rw [hE, ← Matrix.mul_assoc, ← Matrix.mul_assoc, colOp_neg_mul_colOp, Matrix.one_mul,
          Matrix.mul_assoc, ← transpose_mul, colOp_neg_mul_colOp, transpose_one, Matrix.mul_one]
      rw [hinv]
      simpa [conjTranspose_eq_transpose_of_trivial] using
        hpsd'.mul_mul_conjTranspose_same (colOp a (-multipliers a A'))
    · -- the pivots dominate the later diagonal
      have hCdiag : ∀ m : Fin n, pivotElim a A' m m ≤ A' m m := by
        intro m
        simp only [pivotElim, of_apply]
        split_ifs with h1 h2
        · have : 0 ≤ A' m a * A' m a / A' a a := div_nonneg (mul_self_nonneg _) hα
          linarith
        · exact absurd h2.1 (ne_of_gt h2.2)
        · exact le_rfl
      have hCle : ∀ m : Fin n, ¬ a < m → pivotElim a A' m m = A' m m := by
        intro m hm
        simp [pivotElim, hm]
      intro i l hi hil
      dsimp only
      refine (hCdiag l).trans ?_
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · -- an earlier pivot
        have hia : i < a := Fin.lt_def.2 hi
        rw [hCle i (lt_asymm hia)]
        change st.1 (sw l) (sw l) ≤ st.1 (sw i) (sw i)
        rw [hfix i hi]
        refine hdom i (sw l) hi ?_
        by_cases hl : (l : ℕ) < a
        · rw [hfix l hl]
          exact hil
        · exact Fin.le_def.2 (le_trans (le_of_lt hi) (hge l (not_lt.1 hl)))
      · -- the pivot just chosen
        have hia : i = a := Fin.ext hi
        subst hia
        rw [hCle i (lt_irrefl i)]
        change st.1 (sw l) (sw l) ≤ st.1 (sw i) (sw i)
        rw [hsw, Equiv.swap_apply_left]
        exact hmax _ (Fin.le_def.2 (hge l (Fin.le_def.1 hil)))


/-- **(4.2.16)**: after `k` steps of Algorithm 4.2.2 on a symmetric positive semidefinite `A` (the
exact run of the first `k` iterations), with `P̃` the product of the interchanges so far,
`P̃ A P̃ᵀ = [L₁₁ 0; L₂₁ I] [D_k 0; 0 A_k] [L₁₁ 0; L₂₁ I]ᵀ` (`pivotedLower`, `pivotedMiddle`), where
`diag(D_k, A_k)` is positive semidefinite (so `d₁, …, d_k ≥ 0` and `A_k` is positive semidefinite),
each pivot dominates every later diagonal entry (so `d₁ ≥ ⋯ ≥ d_k` and `A_k`'s diagonal is at most
`d_k`), and "`A_k = 0` as soon as `d_k = 0`" (by (4.2.15), since the pivot is the largest diagonal
entry). -/
theorem equation_4_2_16 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) {k : ℕ} (hk : k ≤ n) :
    let st := ((List.finRange n).take k).foldl
      (fun st i => Id.run (ldltPivotStep (M := Id) pure st i)) (A, fun i => i)
    A.submatrix (Chapter03.pivPermUpTo st.2 k) (Chapter03.pivPermUpTo st.2 k) =
        pivotedLower k st.1 * pivotedMiddle k st.1 * (pivotedLower k st.1)ᵀ ∧
      (pivotedMiddle k st.1).PosSemidef ∧
      (∀ i j : Fin n, (i : ℕ) < k → i ≤ j → st.1 j j ≤ st.1 i i) ∧
      ∀ m : Fin n, (m : ℕ) < k → st.1 m m = 0 →
        ∀ i l : Fin n, k ≤ (i : ℕ) → k ≤ (l : ℕ) → st.1 i l = 0 := by
  intro st
  have hlen : ((List.finRange n).take k).length = k := by simp [hk]
  have h := ldltPivot_invariant hA _ (List.take_prefix k _)
  rw [hlen] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, h3, fun m hm hm0 i l hi hl => ?_⟩
  have hmid : ∀ i l : Fin n, k ≤ (i : ℕ) → k ≤ (l : ℕ) → pivotedMiddle k st.1 i l = st.1 i l := by
    intro i l hi hl
    simp [pivotedMiddle, not_lt.2 hi, not_lt.2 hl]
  have hii : st.1 i i = 0 := by
    refine le_antisymm ?_ ?_
    · have := h3 m i hm (Fin.le_def.2 (by omega))
      rwa [hm0] at this
    · rw [← hmid i i hi hi]
      exact h2.diag_nonneg
  have := (h2.apply_eq_zero_of_diag_eq_zero (i := i) (by rw [hmid i i hi hi]; exact hii) l).1
  rwa [hmid i l hi hl] at this

/-- The exact run of Algorithm 4.2.2 is the fold of its exact steps. -/
private theorem algorithm_4_2_2_id (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_4_2_2 pure A) = (List.finRange n).foldl
      (fun st i => Id.run (ldltPivotStep (M := Id) pure st i)) (A, fun i => i) := by
  rw [algorithm_4_2_2, List.idRun_foldlM]

/-- After all `n` steps, `L_n` is the unit lower triangle of the packed state. -/
private theorem pivotedLower_self (S : Matrix (Fin n) (Fin n) ℝ) :
    pivotedLower n S = Chapter03.packedL S := by
  ext i j
  by_cases hji : j < i
  · simp [pivotedLower, Chapter03.packedL_apply_of_lt S hji, hji]
  · rcases eq_or_lt_of_le (not_lt.1 hji) with rfl | hij
    · simp [pivotedLower, Chapter03.packedL_apply_self]
    · simp [pivotedLower, Chapter03.packedL_apply_of_lt' S hij, hji, ne_of_lt hij]

/-- After all `n` steps, `diag(D_n, A_n)` is the diagonal of the packed state. -/
private theorem pivotedMiddle_self (S : Matrix (Fin n) (Fin n) ℝ) :
    pivotedMiddle n S = diagonal S.diag := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [pivotedMiddle]
  · simp [pivotedMiddle, hij]

/-- **Exact correctness of Algorithm 4.2.2**: for a symmetric positive semidefinite `A`, the exact
run `(F, piv)` gives, with `σ = Chapter03.pivPerm piv` (the product of the interchanges in the order
applied), `L = Chapter03.packedL F` and `d = diag(F)`: `A(σ, σ) = L diag(d) Lᵀ` with `L` unit lower
triangular, `d ≥ 0`, `d₁ ≥ d₂ ≥ ⋯ ≥ d_n`, and `d > 0` when `A` is positive definite. (The book
writes `P = P₁ ⋯ P_n` and `d_n > 0` for a semidefinite input; the permutation is the product in the
order applied and `d_n = 0` when `A` is singular.) By the invariant (4.2.16) of
`equation_4_2_16`. -/
theorem algorithm_4_2_2_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    IsLDM (A.submatrix (Chapter03.pivPerm (Id.run (algorithm_4_2_2 pure A)).2)
        (Chapter03.pivPerm (Id.run (algorithm_4_2_2 pure A)).2))
      (Chapter03.packedL (Id.run (algorithm_4_2_2 pure A)).1)
      (diagonal (Id.run (algorithm_4_2_2 pure A)).1.diag)
      (Chapter03.packedL (Id.run (algorithm_4_2_2 pure A)).1) ∧
    (∀ i, 0 ≤ (Id.run (algorithm_4_2_2 pure A)).1 i i) ∧
    (∀ i j, i ≤ j → (Id.run (algorithm_4_2_2 pure A)).1 j j ≤
      (Id.run (algorithm_4_2_2 pure A)).1 i i) ∧
    (A.PosDef → ∀ i, 0 < (Id.run (algorithm_4_2_2 pure A)).1 i i) := by
  have h := ldltPivot_invariant hA (List.finRange n) (List.prefix_refl _)
  rw [List.length_finRange] at h
  rw [algorithm_4_2_2_id]
  generalize (List.finRange n).foldl
    (fun st i => Id.run (ldltPivotStep (M := Id) pure st i)) (A, fun i => i) = st at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  rw [pivotedLower_self, pivotedMiddle_self] at h1
  rw [pivotedMiddle_self] at h2
  have hLu : (Chapter03.packedL st.1).IsUnitLowerTriangular :=
    ⟨fun i j hij => Chapter03.packedL_apply_of_lt' st.1 (OrderDual.toDual_lt_toDual.1 hij),
      Chapter03.packedL_apply_self st.1⟩
  refine ⟨⟨hLu, isDiag_diagonal _, hLu, h1.symm⟩, fun i => ?_,
    fun i j hij => h3 i j i.isLt hij, fun hPD i => ?_⟩
  · simpa using h2.diag_nonneg (i := i)
  · -- the middle factor is congruent to `P A Pᵀ`, positive definite
    set L := Chapter03.packedL st.1 with hL
    have hdet : IsUnit L.det := by rw [hLu.det_eq_one]; exact isUnit_one
    have hX : (A.submatrix (Chapter03.pivPermUpTo st.2 n)
        (Chapter03.pivPermUpTo st.2 n)).PosDef :=
      hPD.submatrix (Chapter03.pivPermUpTo st.2 n).injective
    have hD : diagonal st.1.diag = L⁻¹ * A.submatrix (Chapter03.pivPermUpTo st.2 n)
        (Chapter03.pivPermUpTo st.2 n) * L⁻¹ᵀ := by
      rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.one_mul,
        Matrix.mul_assoc, ← transpose_mul, nonsing_inv_mul _ hdet, transpose_one, Matrix.mul_one]
    have hinj : Function.Injective L⁻¹.vecMul :=
      vecMul_injective_iff_isUnit.2 ((isUnit_nonsing_inv_iff).2 ((isUnit_iff_isUnit_det L).2 hdet))
    have hPDD := hX.mul_mul_conjTranspose_same hinj
    rw [conjTranspose_eq_transpose_of_trivial, ← hD] at hPDD
    simpa using hPDD.diag_pos (i := i)

/-- **(4.2.17) for the output of Algorithm 4.2.2**: for a symmetric positive semidefinite `A` of
rank `r`, the exact run returns `d_i > 0` for `i < r` and `d_i = 0` for `i ≥ r`, so that its `P`,
`L(:, 1:r)` and `D_r = diag(d₁, …, d_r)` realize (4.2.17): `P A Pᵀ = L(:, 1:r) D_r L(:, 1:r)ᵀ`
(`algorithm_4_2_2_spec`). The rank of `P A Pᵀ = L D Lᵀ` is that of `D`, the number of nonzero
pivots, and the pivots are nonincreasing and nonnegative. -/
theorem equation_4_2_17_algorithm {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (i : Fin n) :
    ((i : ℕ) < A.rank → 0 < (Id.run (algorithm_4_2_2 pure A)).1 i i) ∧
      (A.rank ≤ i → (Id.run (algorithm_4_2_2 pure A)).1 i i = 0) := by
  obtain ⟨hLDM, hnn, hanti, -⟩ := algorithm_4_2_2_spec hA
  set F := (Id.run (algorithm_4_2_2 pure A)).1
  set σ := Chapter03.pivPerm (Id.run (algorithm_4_2_2 pure A)).2
  set L := Chapter03.packedL F
  have hdet : IsUnit L.det := by
    rw [hLDM.isUnitLowerTriangular_left.det_eq_one]
    exact isUnit_one
  have hdetT : IsUnit Lᵀ.det := by rwa [det_transpose]
  -- the rank is the number of nonzero pivots
  have hrank : A.rank = Fintype.card {j // F j j ≠ 0} := by
    rw [← rank_submatrix A σ σ, ← hLDM.mul_eq, rank_mul_eq_left_of_isUnit_det _ _ hdetT,
      rank_mul_eq_right_of_isUnit_det _ _ hdet, rank_diagonal]
    rfl
  rw [hrank, Fintype.card_subtype]
  constructor
  · intro hi
    refine lt_of_le_of_ne (hnn i) fun h0 => ?_
    have hsub : Finset.univ.filter (fun j : Fin n => F j j ≠ 0) ⊆
        Finset.univ.filter (fun j : Fin n => (j : ℕ) < i) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      by_contra hji
      exact hj (le_antisymm (h0 ▸ hanti i j (Fin.le_def.2 (not_lt.1 hji))) (hnn j))
    have := Finset.card_le_card hsub
    rw [Fin.card_filter_val_lt, min_eq_right (Nat.le_of_lt i.isLt)] at this
    omega
  · intro hi
    by_contra h0
    have hpos : 0 < F i i := lt_of_le_of_ne (hnn i) (Ne.symm h0)
    have hsub : Finset.univ.filter (fun j : Fin n => (j : ℕ) < i + 1) ⊆
        Finset.univ.filter (fun j : Fin n => F j j ≠ 0) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact (lt_of_lt_of_le hpos (hanti j i (Fin.le_def.2 (by omega)))).ne'
    have := Finset.card_le_card hsub
    rw [Fin.card_filter_val_lt, min_eq_right (Nat.succ_le_of_lt i.isLt)] at this
    omega

end GolubVanLoan.Chapter04
