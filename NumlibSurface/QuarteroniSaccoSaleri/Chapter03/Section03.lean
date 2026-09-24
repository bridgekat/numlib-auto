import Numlib.FloatingPoint.LU
import Numlib.LinearAlgebra.Matrix.Cauchy
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section02

/-!
# Quarteroni–Sacco–Saleri §3.3: the Gaussian elimination method and the LU factorization

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §3.3, over the backbone `Numlib/LinearAlgebra/Matrix/LU/Elimination`
(one elimination step, the Gaussian transformations, the stages `A^{(k)}` of the Gaussian
elimination method on `Fin n`, the multiplier matrix, the Doolittle and Crout recurrences),
`Numlib/LinearAlgebra/Matrix/LU` (the specification `Matrix.IsLU`, Theorem 3.4, the leading
principal minors, Property 3.2), `Numlib/LinearAlgebra/Matrix/Cauchy` (the Hilbert matrix) and
`Numlib/FloatingPoint/LU` (the rounding-error bounds (3.40)–(3.41)).

## Conventions

The stages `A^{(k)}`, `k = 1, …, n`, of the Gaussian elimination method (3.29) are
`Matrix.gemStage A (k - 1)`: the stage index is `0`-based, `gemStage A 0 = A` and
`gemStage A n = U`. The multipliers `m_ik = a^{(k)}_ik / a^{(k)}_kk` of stage `k` are the vector
`gemMultipliers A k` (the book's `m_k`, zero in the positions `≤ k`), the Gaussian transformation
`M_k = I - m_k e_kᵀ` is the backbone's `Matrix.gaussTransform (gemStage A k) k`, and the
right-hand sides `b^{(k)}` are `gemRhs A b (k - 1)`, defined here by the book's recurrence. The
pivots are `gemStage A k k k`, and "the pivots `a^{(k)}_kk`, `k = 1, …, n - 1`, are nonzero" is
`∀ k : Fin n, (k : ℕ) + 1 < n → gemStage A k k k ≠ 0` — the last pivot is never a divisor and
vanishes for a singular matrix with nonsingular strict leading minors (Example 3.3's `B`).

"The LU factorization of `A` with `l_ii = 1`" is the backbone's specification
`Matrix.IsLU A L U` (`L` unit lower triangular, `U` upper triangular, `L U = A`). The leading
principal submatrix `A_i` of order `i` is `Matrix.leadingPrincipalSubmatrix A k` with
`k = i - 1 : Fin n`, indexed by `{j // j ≤ k}`, the strict one `A(< k)` of order `k` is
`Matrix.strictLeadingPrincipalSubmatrix A k`, and the leading minors `d_i` are
`Matrix.leadingPrincipalMinor A k`; on `Fin n` the strict leading blocks are exactly the `A_i`
with `i = 0, …, n - 1` (the order `0` block is the empty matrix, a unit), which is how the
hypothesis "`A_i` nonsingular for `i = 1, …, n - 1`" of Theorem 3.4 reads. The computed factors
of §3.3.2 are an admissible `FloatingPoint.RoundsLU m A L̂ Û` of the relational model, the
Doolittle recurrence with every product rounded, the subtractions rounded one at a time and the
divisions rounded (`Numlib/FloatingPoint/LU`); this covers every loop order of Programs 4–6.

## Contents

* `gemMultipliers`, `gemRhs`, `equation_3_31`, `equation_3_29` — the elimination stages and
  the equivalent systems `A^{(k)} x = b^{(k)}`.
* `remark_3_2`, `equation_3_33` — the Hilbert matrix and the zero-pivot example.
* `equation_3_35`, `equation_3_36`, `equation_3_37` — GEM as a factorization method.
* `theorem_3_4`, `equation_3_39`, `example_3_3_b`, `example_3_3_c`, `example_3_3_d`,
  `property_3_2_row`, `property_3_2_col` — existence and uniqueness of the factorization.
* `equation_3_40`, `equation_3_41` — the effect of rounding errors.
* `equation_3_42`, `equation_3_43`, `crout` — the compact forms.

Example 3.2 (the run of GEM on `H₃`, a computation in exact rationals) and Programs 4–6 are
not nodes; the operation counts are prose.

## Readings and errata

After (3.36) the book says that `(m_i e_iᵀ)(m_j e_jᵀ)` is the null matrix "if `i ≠ j`"; it is
null for `i < j` (the case the product (3.37) needs), while for `i > j` it is `m_ij m_i e_jᵀ`,
which is nonzero as soon as the multiplier `m_ij` is; `equation_3_36` states the case `i < j`.
Property 3.2 needs `A` nonsingular under the book's (weak) Definition 1.24 of diagonal
dominance: `!![0, 0; 1, 1]` is weakly dominant by rows and has no unit-lower LU factorization
(its `(1, 0)` entry would be `l₂₁ u₁₁ = 0`); the theorem it cites ([higham2002accuracy] Theorem
9.9) assumes nonsingularity, and so do `property_3_2_row` and `property_3_2_col`.
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ}

/-! ### The stages of Gaussian elimination, (3.29)–(3.31) -/

section Stages

variable (A : Matrix (Fin n) (Fin n) ℝ)

/-- **The multipliers of stage `k`**, (3.30): the vector
`m_k = (0, …, 0, m_{k+1,k}, …, m_{n,k})ᵀ` with `m_ik = a^{(k)}_ik / a^{(k)}_kk` for `i > k`, read
on the stage `A^{(k)} = gemStage A k` (`0`-based `k`). -/
noncomputable def gemMultipliers (k : Fin n) : Fin n → ℝ :=
  fun i => if k < i then gemStage A k i k / gemStage A k k k else 0

/-- **The right-hand sides `b^{(k)}`** of the systems (3.29), by the book's recurrence
`b^{(k+1)}_i = b^{(k)}_i - m_ik b^{(k)}_k` for `i > k` (and unchanged for `i ≤ k`), `0`-based:
`gemRhs A b 0 = b`, and past `n` nothing happens, as for `Matrix.gemStage`. -/
noncomputable def gemRhs (b : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => b
  | k + 1 =>
    if h : k < n then
      fun i => gemRhs b k i - gemMultipliers A ⟨k, h⟩ i * gemRhs b k ⟨k, h⟩
    else gemRhs b k

/-- A stage index `k : Fin n` is `⟨k, k.2⟩`. -/
private theorem fin_mk_val (k : Fin n) : (⟨k, k.2⟩ : Fin n) = k := Fin.eta k k.2

/-- The multiplier matrix of a stage applied to a vector: `(N v)_i = m_ik v_k` for `i > k`. -/
private theorem elimMultipliers_mulVec_apply (M : Matrix (Fin n) (Fin n) ℝ) (p : Fin n)
    (v : Fin n → ℝ) (i : Fin n) :
    (elimMultipliers M p *ᵥ v) i = if p < i then M i p * (M p p)⁻¹ * v p else 0 := by
  rw [mulVec, dotProduct, Finset.sum_eq_single p (fun c _ hc => by simp [hc]) (by simp)]
  by_cases hi : p < i <;> simp [hi]

/-- **(3.30)–(3.31), one stage of Gaussian elimination.** For `k < n` (the stage `k + 1` in the
book's `1`-based numbering) and the multipliers `m_ik = a^{(k)}_ik / a^{(k)}_kk`,
`a^{(k+1)}_ij = a^{(k)}_ij - m_ik a^{(k)}_kj` and `b^{(k+1)}_i = b^{(k)}_i - m_ik b^{(k)}_k` for
`i > k` (and every `j`), while the rows `i ≤ k` are unchanged (backbone
`Matrix.gemStage_succ_of_lt`, `Matrix.elimStep_apply_of_lt`, `Matrix.elimStep_apply_of_not_lt`).
-/
theorem equation_3_31 (b : Fin n → ℝ) (k : Fin n) :
    (∀ i j, k < i →
      gemStage A (k + 1) i j = gemStage A k i j - gemMultipliers A k i * gemStage A k k j) ∧
    (∀ i j, i ≤ k → gemStage A (k + 1) i j = gemStage A k i j) ∧
    (∀ i, k < i → gemRhs A b (k + 1) i = gemRhs A b k i - gemMultipliers A k i * gemRhs A b k k) ∧
    (∀ i, i ≤ k → gemRhs A b (k + 1) i = gemRhs A b k i) := by
  have hstep : gemStage A (k + 1) = elimStep (gemStage A k) k := by
    rw [gemStage_succ_of_lt A k.2, fin_mk_val]
  have hrhs : gemRhs A b (k + 1) =
      fun i => gemRhs A b k i - gemMultipliers A k i * gemRhs A b k k := by
    simp only [gemRhs, k.2, dite_true, fin_mk_val]
  refine ⟨fun i j hi => ?_, fun i j hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hstep, elimStep_apply_of_lt _ hi]
    simp [gemMultipliers, hi, div_eq_mul_inv]
  · rw [hstep, elimStep_apply_of_not_lt _ (not_lt.2 hi)]
  · rw [hrhs]
  · rw [hrhs]
    simp [gemMultipliers, not_lt.2 hi]

/-- **(3.29), the equivalent systems.** Every system `A^{(k)} x = b^{(k)}` produced by Gaussian
elimination has the same solutions as the original `A x = b`, because
`b^{(k+1)} = M_k b^{(k)}` for the invertible Gaussian transformation `M_k` of (3.35) (backbone
`Matrix.gemStage_succ_eq_gaussTransform_mul`, `Matrix.gaussTransform_mul_elimMul`). -/
theorem equation_3_29 (b : Fin n → ℝ) (k : ℕ) (x : Fin n → ℝ) :
    gemStage A k *ᵥ x = gemRhs A b k ↔ A *ᵥ x = b := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases h : k < n
    · have hrhs : gemRhs A b (k + 1) = gaussTransform (gemStage A k) ⟨k, h⟩ *ᵥ gemRhs A b k := by
        ext i
        simp only [gemRhs, h, dite_true, gaussTransform, sub_mulVec, one_mulVec, Pi.sub_apply,
          elimMultipliers_mulVec_apply, gemMultipliers]
        split_ifs <;> simp [div_eq_mul_inv]
      have hu : IsUnit (gaussTransform (gemStage A k) ⟨k, h⟩) :=
        IsUnit.of_mul_eq_one _ (gaussTransform_mul_elimMul _ _)
      rw [gemStage_succ_eq_gaussTransform_mul A h, hrhs, ← mulVec_mulVec,
        (mulVec_injective_iff_isUnit.2 hu).eq_iff, ih]
    · have hrhs : gemRhs A b (k + 1) = gemRhs A b k := by
        simp only [gemRhs, h, dite_false]
      rw [gemStage_succ_of_le A (not_lt.1 h), hrhs, ih]

end Stages

/-! ### Remark 3.2 and (3.33): the Hilbert matrix and a zero pivot -/

/-- **Remark 3.2, (3.32).** The Hilbert matrix of order `n`, `h_ij = 1 / (i + j - 1)` for
`i, j = 1, …, n` (with the `0`-based indices of `Fin n`, `1 / ((i + 1) + (j + 1) - 1)`), is the
backbone's `Matrix.hilbert ℝ n`; it is nonsingular and symmetric positive definite (backbone
`Matrix.isUnit_hilbert`, `Matrix.posDef_hilbert`), so that Gaussian elimination without pivoting
applies to it (Example 3.2, Theorem 3.6). That it is "the paradigm of an ill-conditioned matrix"
is prose. -/
theorem remark_3_2 (n : ℕ) :
    (∀ i j : Fin n, hilbert ℝ n i j = 1 / (((i : ℕ) + 1 : ℝ) + ((j : ℕ) + 1) - 1)) ∧
      IsUnit (hilbert ℝ n) ∧ (hilbert ℝ n).PosDef := by
  refine ⟨fun i j => ?_, isUnit_hilbert ℝ n, posDef_hilbert n⟩
  rw [hilbert_apply]
  ring_nf

/-- **(3.33), a zero pivot from a nonsingular matrix with nonzero diagonal.** The matrix
`A = [1, 2, 3; 2, 4, 5; 7, 8, 9]` is nonsingular and has nonzero diagonal entries, yet its second
stage is `A^{(2)} = [1, 2, 3; 0, 0, -1; 0, -6, -12]`, whose pivot `a^{(2)}_22` vanishes, so that
GEM is interrupted at the second step; its leading minors are `d₁ = 1` and `d₂ = 0`. -/
theorem equation_3_33 :
    IsUnit !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9] ∧
      (∀ i, !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9] i i ≠ 0) ∧
      gemStage !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9] 1 = !![1, 2, 3; 0, 0, -1; 0, -6, -12] ∧
      gemStage !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9] 1 1 1 = 0 ∧
      !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9].leadingPrincipalMinor 0 = 1 ∧
      !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9].leadingPrincipalMinor 1 = 0 := by
  have hstage : gemStage !![(1 : ℝ), 2, 3; 2, 4, 5; 7, 8, 9] 1 =
      !![1, 2, 3; 0, 0, -1; 0, -6, -12] := by
    rw [gemStage_succ_of_lt _ (by norm_num : 0 < 3), gemStage_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [elimStep_apply, Fin.lt_def]
  refine ⟨?_, fun i => ?_, hstage, by rw [hstage]; rfl, ?_, ?_⟩
  · rw [isUnit_iff_isUnit_det, det_fin_three]
    simp
    norm_num
  · fin_cases i <;> norm_num
  · rw [leadingPrincipalMinor, det_leadingPrincipalSubmatrix_fin, det_fin_one]
    simp
  · rw [leadingPrincipalMinor, det_leadingPrincipalSubmatrix_fin, det_fin_two]
    simp
    norm_num

/-! ### GEM as a factorization method, (3.34)–(3.37) -/

section Factorization

variable (A : Matrix (Fin n) (Fin n) ℝ)

/-- **(3.35).** `A^{(k+1)} = M_k A^{(k)}`, where the `k`-th Gaussian transformation matrix is
`M_k = I_n - m_k e_kᵀ`, the identity with the negated multipliers of stage `k` in column `k`
below the diagonal (backbone `Matrix.gemStage_succ_eq_gaussTransform_mul`,
`Matrix.gaussTransform`). -/
theorem equation_3_35 (k : Fin n) :
    gemStage A (k + 1) = gaussTransform (gemStage A k) k * gemStage A k ∧
      gaussTransform (gemStage A k) k = 1 - vecMulVec (gemMultipliers A k) (Pi.single k 1) := by
  refine ⟨by rw [gemStage_succ_eq_gaussTransform_mul A k.2, fin_mk_val], ?_⟩
  ext i j
  simp only [gaussTransform, Matrix.sub_apply, elimMultipliers_apply, vecMulVec_apply,
    gemMultipliers, Pi.single_apply]
  split_ifs <;> simp_all [div_eq_mul_inv]

/-- The rank-one product `(m_i e_iᵀ)(m_j e_jᵀ)` vanishes when the vector `m_j` vanishes in
position `i`. -/
private theorem vecMulVec_single_mul_vecMulVec_single {mi mj : Fin n → ℝ} {i j : Fin n}
    (h : mj i = 0) : vecMulVec mi (Pi.single i 1) * vecMulVec mj (Pi.single j 1) = 0 := by
  rw [vecMulVec_mul_vecMulVec, single_dotProduct, one_mul, h, zero_smul, vecMulVec_zero]

/-- **(3.36).** The Gaussian transformations are unit lower triangular with inverse
`M_k⁻¹ = 2 I_n - M_k = I_n + m_k e_kᵀ`, and `(m_i e_iᵀ)(m_j e_jᵀ) = 0` for `i < j` — the book says
"if `i ≠ j`", but for `i > j` the product is `m_ij m_i e_jᵀ`; the case `i < j` is the one the
product (3.37) needs (backbone `Matrix.gaussTransform_mul_elimMul`, `Matrix.elimMul`). -/
theorem equation_3_36 (k : Fin n) :
    (gaussTransform (gemStage A k) k).IsUnitLowerTriangular ∧
      (gaussTransform (gemStage A k) k)⁻¹ = 2 • (1 : Matrix (Fin n) (Fin n) ℝ) -
        gaussTransform (gemStage A k) k ∧
      (gaussTransform (gemStage A k) k)⁻¹ = 1 + vecMulVec (gemMultipliers A k) (Pi.single k 1) ∧
      ∀ i j : Fin n, i < j →
        vecMulVec (gemMultipliers A i) (Pi.single i 1) *
          vecMulVec (gemMultipliers A j) (Pi.single j 1) = 0 := by
  have hM := (equation_3_35 A k).2
  have hinv : (gaussTransform (gemStage A k) k)⁻¹ =
      1 + vecMulVec (gemMultipliers A k) (Pi.single k 1) := by
    refine inv_eq_right_inv ?_
    rw [hM, sub_mul, one_mul, mul_add, mul_one, vecMulVec_single_mul_vecMulVec_single
      (by simp [gemMultipliers])]
    abel
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ?_, hinv, fun i j hij => ?_⟩
  · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    rw [hM, Matrix.sub_apply, one_apply_ne hij'.ne, vecMulVec_apply]
    by_cases hki : k < i
    · rw [Pi.single_eq_of_ne (hki.trans hij').ne']
      simp
    · simp [gemMultipliers, hki]
  · rw [hM, Matrix.sub_apply, one_apply_eq, vecMulVec_apply]
    by_cases hki : k < i
    · rw [Pi.single_eq_of_ne hki.ne']
      simp
    · simp [gemMultipliers, hki]
  · rw [hinv, hM, two_smul]
    abel
  · exact vecMulVec_single_mul_vecMulVec_single (by simp [gemMultipliers, hij.not_gt])

/-- The partial multiplier matrix after `k` stages is the ordered product of the unipotent
factors `M_0⁻¹ ⋯ M_{k-1}⁻¹`. -/
private theorem gemLowerStage_eq_prod (k : ℕ) (hk : k ≤ n) :
    gemLowerStage A k =
      (List.ofFn fun i : Fin k => elimMul (gemStage A i) (Fin.castLE hk i)).prod := by
  induction k with
  | zero => rw [gemLowerStage_zero, List.ofFn_zero, List.prod_nil]
  | succ k ih =>
    rw [gemLowerStage_succ A (by omega), ih (by omega), List.ofFn_succ', List.concat_eq_append,
      List.prod_append, List.prod_singleton]
    rfl

/-- **(3.37), GEM as a factorization method.** If the pivots `a^{(k)}_kk`, `k = 1, …, n - 1`, are
nonzero then `A = M_1⁻¹ M_2⁻¹ ⋯ M_{n-1}⁻¹ U = (I_n + ∑_{i} m_i e_iᵀ) U = L U`, where `U = A^{(n)}`
is the last stage and `L = (M_{n-1} ⋯ M_1)⁻¹ = M_1⁻¹ ⋯ M_{n-1}⁻¹` is the unit lower triangular
matrix whose subdiagonal entries are the multipliers `m_ik` produced by GEM (backbone
`Matrix.gemLower`, `Matrix.isLU_gemLower_gemStage`). The last pivot is never used, so it need not
be nonzero. -/
theorem equation_3_37 (hpiv : ∀ k : Fin n, (k : ℕ) + 1 < n → gemStage A k k k ≠ 0) :
    IsLU A (gemLower A) (gemStage A n) ∧
      gemLower A = 1 + ∑ i : Fin n, vecMulVec (gemMultipliers A i) (Pi.single i 1) ∧
      gemLower A = (List.ofFn fun k : Fin n => (gaussTransform (gemStage A k) k)⁻¹).prod ∧
      ∀ i k : Fin n, k < i → gemLower A i k = gemMultipliers A k i := by
  refine ⟨isLU_gemLower_gemStage A fun m hm hm1 => hpiv ⟨m, hm⟩ hm1, ?_, ?_, fun i k hki => ?_⟩
  · ext i j
    simp only [gemLower, of_apply, Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, mem_univ, ite_true,
      gemMultipliers]
    split_ifs with h1 h2
    · simp [one_apply, h1.ne']
    · simp [one_apply, h2]
    · simp [one_apply, h2]
  · rw [← gemLowerStage_of_le A le_rfl, gemLowerStage_eq_prod A n le_rfl]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    rw [inv_eq_right_inv (gaussTransform_mul_elimMul _ _)]
    rfl
  · simp [gemLower, gemMultipliers, hki]

end Factorization

/-! ### Theorem 3.4, (3.39), Example 3.3, Property 3.2 -/

section Existence

variable {A L U : Matrix (Fin n) (Fin n) ℝ}

/-- **Theorem 3.4.** Let `A ∈ ℝ^{n×n}`. The LU factorization of `A` with `l_ii = 1` for
`i = 1, …, n` exists and is unique iff the leading principal submatrices `A_i` of `A` of order
`i = 1, …, n - 1` are nonsingular — on `Fin n`, iff every strict leading principal submatrix
`A(< k)` is (backbone `Matrix.existsUnique_isLU_iff`). -/
theorem theorem_3_4 (A : Matrix (Fin n) (Fin n) ℝ) :
    (∃! LU : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ, IsLU A LU.1 LU.2) ↔
      ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k) :=
  existsUnique_isLU_iff A

/-- **(3.38)–(3.39) and the determinant.** If `A = L U` with `L` unit lower triangular then
`A_i = L^{(i)} U^{(i)}` for every leading principal block, `det A_i = u_11 ⋯ u_ii`, hence
`det A = u_11 ⋯ u_nn`; and when `det A_{i-1} ≠ 0` the pivot is the ratio of consecutive minors,
`u_ii = d_i / d_{i-1}` (backbone `Matrix.IsLU.toBlock_le`,
`Matrix.IsLU.det_leadingPrincipalSubmatrix`, `Matrix.IsLU.det_eq_prod_diag`,
`Matrix.IsLU.diag_upper_eq_div_leadingPrincipalMinor`). -/
theorem equation_3_39 (h : IsLU A L U) :
    (∀ k, IsLU (A.leadingPrincipalSubmatrix k) (L.leadingPrincipalSubmatrix k)
      (U.leadingPrincipalSubmatrix k)) ∧
    (∀ k, A.leadingPrincipalMinor k = ∏ i with i ≤ k, U i i) ∧
    A.det = ∏ i, U i i ∧
    ∀ k, (A.strictLeadingPrincipalSubmatrix k).det ≠ 0 →
      U k k = A.leadingPrincipalMinor k / (A.strictLeadingPrincipalSubmatrix k).det :=
  ⟨h.toBlock_le, h.det_leadingPrincipalSubmatrix, h.det_eq_prod_diag,
    fun _ hk => h.diag_upper_eq_div_leadingPrincipalMinor hk⟩

/-- A `2 × 2` product of a unit lower and an upper triangular matrix is an LU factorization. -/
private theorem isLU_fin_two (a u v w : ℝ) :
    IsLU (!![1, 0; a, 1] * !![u, v; 0, w]) !![1, 0; a, 1] !![u, v; 0, w] where
  isUnitLowerTriangular := ⟨fun i j hij => by
      have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      fin_cases i <;> fin_cases j <;> simp_all, fun i => by fin_cases i <;> simp⟩
  isUpperTriangular := fun i j hij => by
    fin_cases i <;> fin_cases j <;> simp_all
  mul_eq := rfl

/-- The strict leading principal submatrices of a `2 × 2` matrix with `a₁₁ ≠ 0` are nonsingular:
the only pivot that matters is `a₁₁` (backbone `Matrix.gemStage_pivots_ne_zero_iff`). -/
private theorem forall_isUnit_strict_fin_two {M : Matrix (Fin 2) (Fin 2) ℝ} (h : M 0 0 ≠ 0) :
    ∀ k, IsUnit (M.strictLeadingPrincipalSubmatrix k) :=
  (gemStage_pivots_ne_zero_iff M).1 fun m hm hm1 => by
    interval_cases m
    · simpa using h
    · exact absurd hm1 (by norm_num)

/-- **Example 3.3, the matrix `B`.** The singular `B = [1, 2; 1, 2]` has the nonsingular leading
minor `B₁ = 1`, hence, by Theorem 3.4, a unique LU factorization: `L = [1, 0; 1, 1]`,
`U = [1, 2; 0, 0]`. -/
theorem example_3_3_b :
    ¬ IsUnit !![(1 : ℝ), 2; 1, 2] ∧ !![(1 : ℝ), 2; 1, 2].leadingPrincipalMinor 0 = 1 ∧
      IsLU !![(1 : ℝ), 2; 1, 2] !![1, 0; 1, 1] !![1, 2; 0, 0] ∧
      ∀ L U, IsLU !![(1 : ℝ), 2; 1, 2] L U → L = !![1, 0; 1, 1] ∧ U = !![1, 2; 0, 0] := by
  have hB : !![(1 : ℝ), 2; 1, 2] = !![1, 0; 1, 1] * !![1, 2; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have hLU : IsLU !![(1 : ℝ), 2; 1, 2] !![1, 0; 1, 1] !![1, 2; 0, 0] := by
    rw [hB]
    exact isLU_fin_two 1 1 2 0
  refine ⟨?_, ?_, hLU, fun L U h => h.unique hLU (forall_isUnit_strict_fin_two (by norm_num))⟩
  · rw [isUnit_iff_isUnit_det, det_fin_two]
    norm_num
  · rw [leadingPrincipalMinor, det_leadingPrincipalSubmatrix_fin, det_fin_one]
    simp

/-- **Example 3.3, the matrix `C`.** The nonsingular `C = [0, 1; 1, 0]`, whose leading minor
`C₁ = 0` is singular, admits no LU factorization with unit lower `L`: the `(1, 1)` entry forces
`u₁₁ = 0` and then the `(2, 1)` entry would be `l₂₁ u₁₁ = 0 ≠ 1`. -/
theorem example_3_3_c :
    IsUnit !![(0 : ℝ), 1; 1, 0] ∧ !![(0 : ℝ), 1; 1, 0].leadingPrincipalMinor 0 = 0 ∧
      ¬ ∃ L U, IsLU !![(0 : ℝ), 1; 1, 0] L U := by
  refine ⟨?_, ?_, ?_⟩
  · rw [isUnit_iff_isUnit_det, det_fin_two]
    norm_num
  · rw [leadingPrincipalMinor, det_leadingPrincipalSubmatrix_fin, det_fin_one]
    simp
  · rintro ⟨L, U, h⟩
    have hL00 := h.isUnitLowerTriangular.diag_eq_one 0
    have hL11 := h.isUnitLowerTriangular.diag_eq_one 1
    have hL01 : L 0 1 = 0 :=
      h.isUnitLowerTriangular.isLowerTriangular (OrderDual.toDual_lt_toDual.2 (by decide))
    have hU10 : U 1 0 = 0 := h.isUpperTriangular (by decide)
    have h00 : U 0 0 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hL00, hL01] using
        congrFun (congrFun h.mul_eq 0) 0
    have h10 : L 1 0 * U 0 0 = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hL11, hU10] using
        congrFun (congrFun h.mul_eq 1) 0
    rw [h00, mul_zero] at h10
    exact zero_ne_one h10

/-- **Example 3.3, the matrix `D`.** The singular `D = [0, 1; 0, 2]`, whose leading minor
`D₁ = 0` is singular, admits infinitely many LU factorizations `D = L_β U_β` with
`L_β = [1, 0; β, 1]`, `U_β = [0, 1; 0, 2 - β]`, one for every `β ∈ ℝ`. -/
theorem example_3_3_d :
    ¬ IsUnit !![(0 : ℝ), 1; 0, 2] ∧ !![(0 : ℝ), 1; 0, 2].leadingPrincipalMinor 0 = 0 ∧
      ∀ β : ℝ, IsLU !![(0 : ℝ), 1; 0, 2] !![1, 0; β, 1] !![0, 1; 0, 2 - β] := by
  refine ⟨?_, ?_, fun β => ?_⟩
  · rw [isUnit_iff_isUnit_det, det_fin_two]
    norm_num
  · rw [leadingPrincipalMinor, det_leadingPrincipalSubmatrix_fin, det_fin_one]
    simp
  · have hD : !![(0 : ℝ), 1; 0, 2] = !![1, 0; β, 1] * !![0, 1; 0, 2 - β] := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hD]
    exact isLU_fin_two β 0 1 (2 - β)

/-- **Property 3.2, rows.** If the *nonsingular* matrix `A` is diagonally dominant by rows
(Definition 1.24, `∑_{j ≠ i} |a_ij| ≤ |a_ii|`), then the LU factorization of `A` exists (backbone
`Matrix.exists_isLU_of_isDiagDominant`, [higham2002accuracy] Theorem 9.9). The book omits the
nonsingularity, without which the statement is false (`!![0, 0; 1, 1]`). -/
theorem property_3_2_row (hA : IsUnit A) (hdom : A.IsDiagDominant) : ∃ L U, IsLU A L U :=
  exists_isLU_of_isDiagDominant hA hdom

/-- **Property 3.2, columns.** If the *nonsingular* matrix `A` is diagonally dominant by columns
(`∑_{i ≠ j} |a_ij| ≤ |a_jj|`), then the LU factorization of `A` exists and its multipliers
satisfy `|l_ij| ≤ 1` for all `i, j` (backbone `Matrix.exists_isLU_of_isColDiagDominant`). -/
theorem property_3_2_col (hA : IsUnit A) (hdom : A.IsColDiagDominant) :
    ∃ L U, IsLU A L U ∧ ∀ i j, |L i j| ≤ 1 := by
  obtain ⟨L, U, h, hL⟩ := exists_isLU_of_isColDiagDominant hA hdom
  exact ⟨L, U, h, fun i j => by simpa [Real.norm_eq_abs] using hL i j⟩

end Existence

/-! ### §3.3.2: the effect of rounding errors -/

section Rounding

open FloatingPoint

variable {m : RoundingModel ℝ} {A L U : Matrix (Fin n) (Fin n) ℝ}

/-- **(3.40).** The factors `L̂`, `Û` computed by GEM in floating-point arithmetic with unit
roundoff `u`, `n u < 1` (an admissible `FloatingPoint.RoundsLU m A L̂ Û`, with the computed
pivots `û_jj` nonzero), satisfy `L̂ Û = A + δA` with `|δA| ≤ (n u / (1 - n u)) |L̂| |Û|` entrywise
(backbone `FloatingPoint.exists_roundsLU_mul_eq_add`, [higham2002accuracy] Theorem 9.3). -/
theorem equation_3_40 [NeZero n] (hn : (n : ℝ) * m.u < 1) (h : RoundsLU m A L U)
    (hd : ∀ j, U j j ≠ 0) :
    ∃ δA : Matrix (Fin n) (Fin n) ℝ,
      δA.abs ≤ₑ (n * m.u / (1 - n * m.u)) • (L.abs * U.abs) ∧ L * U = A + δA := by
  have hu : m.u < 1 := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
    nlinarith [m.u_nonneg]
  obtain ⟨δA, hδA, hLU⟩ := exists_roundsLU_mul_eq_add hu (by rwa [Fintype.card_fin]) h
    fun j _ _ => hd j
  refine ⟨δA, ?_, hLU⟩
  rwa [Fintype.card_fin, gamma_def] at hδA

/-- **(3.41).** If the computed factors `L̂`, `Û` have nonnegative entries and `2 n u < 1`, then
`|L̂| |Û| = |L̂ Û| = |A + δA| ≤ |A| + |δA|` turns (3.40) into a bound in terms of `A` alone:
`|δA| ≤ g(u) |A|` with `g(u) = n u / (1 - 2 n u)` (backbone
`FloatingPoint.abs_le_of_roundsLU_of_entrywiseNonneg`). -/
theorem equation_3_41 [NeZero n] (hn : 2 * ((n : ℝ) * m.u) < 1) (h : RoundsLU m A L U)
    (hd : ∀ j, U j j ≠ 0) (hL : L.EntrywiseNonneg) (hU : U.EntrywiseNonneg) :
    ∃ δA : Matrix (Fin n) (Fin n) ℝ,
      δA.abs ≤ₑ (n * m.u / (1 - 2 * (n * m.u))) • A.abs ∧ L * U = A + δA := by
  have hu : m.u < 1 := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
    nlinarith [m.u_nonneg]
  obtain ⟨δA, hδA, hLU⟩ := abs_le_of_roundsLU_of_entrywiseNonneg hu (by rwa [Fintype.card_fin])
    h (fun j _ _ => hd j) hL hU
  refine ⟨δA, ?_, hLU⟩
  rwa [Fintype.card_fin] at hδA

end Rounding

/-! ### §3.3.4: compact forms, (3.42)–(3.43) and Crout -/

section Compact

variable (A : Matrix (Fin n) (Fin n) ℝ)

/-- **(3.42).** For a unit lower triangular `L` and an upper triangular `U`, `A = L U` iff the
`n²` equations `a_ij = ∑_{r=1}^{min(i,j)} l_ir u_rj` hold: computing the LU factorization is
solving this system for the `n² + n` entries of the triangular factors (backbone
`Matrix.IsLU.apply_eq_sum`; conversely the sum is `(L U)_ij` by triangularity). -/
theorem equation_3_42 {L U : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsUnitLowerTriangular)
    (hU : U.IsUpperTriangular) :
    IsLU A L U ↔ ∀ i j, A i j = ∑ r with r ≤ min i j, L i r * U r j := by
  have hprod : IsLU (L * U) L U := ⟨hL, hU, rfl⟩
  constructor
  · exact fun h => h.apply_eq_sum
  · intro h
    refine ⟨hL, hU, ?_⟩
    ext i j
    rw [hprod.apply_eq_sum, h]

/-- **(3.43), the Doolittle method.** Setting `l_kk = 1`, the `k`-th row of `U` and then the
`k`-th column of `L` are obtained from (3.42) as `u_kj = a_kj - ∑_{r<k} l_kr u_rj` for `j ≥ k`
and `l_ik = (a_ik - ∑_{r<k} l_ir u_rk) / u_kk` for `i > k`, `k = 1, …, n` — the backbone's
`Matrix.luUpper A`, `Matrix.luLower A`, read off the packed recurrence `Matrix.luPacked A`. Under
the hypothesis of Theorem 3.4 the recurrence produces the LU factorization
(`Matrix.isLU_luLower_luUpper`), and it is the factorization GEM produces — "the Doolittle
factorization is nothing but the `ijk` version of GEM" (`Matrix.luLower_eq_gemLower`). -/
theorem equation_3_43 :
    (∀ k j, k ≤ j → luUpper A k j = A k j - ∑ r with r < k, luLower A k r * luUpper A r j) ∧
    (∀ i k, k < i →
      luLower A i k = (A i k - ∑ r with r < k, luLower A i r * luUpper A r k) / luUpper A k k) ∧
    ((∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) → IsLU A (luLower A) (luUpper A)) ∧
    ((∀ k : Fin n, (k : ℕ) + 1 < n → gemStage A k k k ≠ 0) →
      luLower A = gemLower A ∧ luUpper A = gemStage A n) := by
  refine ⟨fun k j hkj => ?_, fun i k hki => ?_, isLU_luLower_luUpper A,
    fun hpiv => luLower_eq_gemLower A fun m hm hm1 => hpiv ⟨m, hm⟩ hm1⟩
  · rw [luUpper, of_apply, ite_eq_left hkj, luPacked_of_le A hkj]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrk : r < k := (mem_filter.1 hr).2
    simp [luLower, hrk, hrk.le.trans hkj]
  · rw [luLower, of_apply, ite_eq_left hki, luPacked_of_lt A hki, luUpper, of_apply,
      ite_eq_left le_rfl]
    congr 2
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrk : r < k := (mem_filter.1 hr).2
    simp [hrk.trans hki, hrk.le]

/-- **§3.3.4, the Crout factorization.** Setting `u_kk = 1`, the `k`-th column of `L` and then the
`k`-th row of `U` are `l_ik = a_ik - ∑_{r<k} l_ir u_rk` for `i ≥ k` and
`u_kj = (a_kj - ∑_{r<k} l_kr u_rj) / l_kk` for `j > k`, `k = 1, …, n` — the backbone's
`Matrix.croutLower A`, `Matrix.croutUpper A`, which are the Doolittle factors of `Aᵀ` transposed.
Under the hypothesis of Theorem 3.4 (for `Aᵀ`, which is the same hypothesis) they satisfy
`A = L U` with `L` lower triangular and `U` unit upper triangular (backbone
`Matrix.croutLower_mul_croutUpper`). -/
theorem crout :
    (∀ i k, k ≤ i →
      croutLower A i k = A i k - ∑ r with r < k, croutLower A i r * croutUpper A r k) ∧
    (∀ k j, k < j → croutUpper A k j =
      (A k j - ∑ r with r < k, croutLower A k r * croutUpper A r j) / croutLower A k k) ∧
    (∀ k, croutUpper A k k = 1) ∧
    ((∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) →
      croutLower A * croutUpper A = A ∧ (croutLower A).IsLowerTriangular ∧
        (croutUpper A)ᵀ.IsUnitLowerTriangular) := by
  refine ⟨fun i k hki => ?_, fun k j hkj => ?_, fun k => ?_, croutLower_mul_croutUpper A⟩
  · rw [croutLower, transpose_apply, luUpper, of_apply, ite_eq_left hki, luPacked_of_le _ hki,
      transpose_apply]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrk : r < k := (mem_filter.1 hr).2
    simp [croutUpper, luLower, hrk, hrk.le.trans hki, mul_comm]
  · rw [croutUpper, transpose_apply, luLower, of_apply, ite_eq_left hkj, luPacked_of_lt _ hkj,
      transpose_apply, croutLower, transpose_apply, luUpper, of_apply, ite_eq_left le_rfl]
    congr 2
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrk : r < k := (mem_filter.1 hr).2
    simp [hrk.trans hkj, hrk.le, mul_comm]
  · simp [croutUpper, luLower]

end Compact

end QuarteroniSaccoSaleri.Chapter03
