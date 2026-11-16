/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.LU`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Numlib.LinearAlgebra.Matrix.LU.Elimination
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.Rank

/-!
# Pivoting and the growth factor of Gaussian elimination

This module treats pivoting in Gaussian elimination at two levels. The first level states what
pivoting achieves. Every square matrix $A$ over a normed field has a row permutation $\sigma$ with
$P_\sigma A = LU$ and all multipliers of modulus at most one (partial pivoting, equation (3.52) of
[quarteroni2000numerical]). It also has a row permutation and a column permutation with
$P A Q = LU$, where in addition every row of $U$ is dominated by its diagonal entry (complete
pivoting, [quarteroni2000numerical], §3.5). Neither statement needs $A$ to be nonsingular: a zero
pivot column is skipped with a zero column of multipliers. The second level is the algorithm: the
stages of Gaussian elimination of `Numlib.LinearAlgebra.Matrix.LU.Elimination` with a choice of the
pivot row before each step. A strategy chooses the pivot; partial pivoting takes the first row of
maximal modulus in the current column, and complete pivoting takes an entry of maximal modulus in
the trailing block, with a row and a column interchange ([golub2013matrix], §3.4;
[higham2002accuracy], §9.3–9.5). Rook pivoting ([golub2013matrix], §3.4.7) is also defined. The
module also proves partial pivoting on a tall block column ([golub2013matrix], §3.6) and the band
structure of the factors of partial pivoting ([golub2013matrix], §4.3).

The growth factor of Gaussian elimination on $A \in \mathbb{R}^{N \times N}$ is
$$\rho(A) = \frac{\max_{i, j, k} |a^{(k)}_{ij}|}{\max_{i, j} |a_{ij}|}$$
(equation (3.66) of [quarteroni2000numerical]). It is defined here with the exact stages $A^{(k)}$.
Of the bounds in §3.10 of [quarteroni2000numerical], this module proves $\rho \le 2^{N-1}$ when the
multipliers are bounded by one (so for partial pivoting), $\rho = 1$ for symmetric positive definite
matrices, $\rho \le 2$ for nonsingular column diagonally dominant matrices, $\rho \le 2$ for
tridiagonal matrices and $\rho \le N$ for upper Hessenberg matrices under partial pivoting,
$\rho \le 2^{p+q}$ for band matrices of lower bandwidth $p$ and upper bandwidth $q$ under partial
pivoting, and Wilkinson's bound
$$\rho \le N^{1/2} \big( 2 \cdot 3^{1/2} \cdot 4^{1/3} \cdots N^{1/(N-1)} \big)^{1/2}$$
for complete pivoting ([higham2002accuracy], (9.14)).

## Main definitions

* `Matrix.IsPartialPivot`: a strategy that chooses a row $r \ge k$ that maximizes $|m_{rk}|$.
* `Matrix.partialPivotRow`: the first such row, the strategy of partial pivoting.
* `Matrix.IsCompletePivot`: a strategy that chooses an entry of maximal modulus in the trailing
  block from $k$ on.
* `Matrix.completePivotEntry`: one such entry, the strategy of complete pivoting.
* `Matrix.IsRookPivot`: a strategy that chooses an entry of the trailing block that is maximal in
  modulus in both its row and its column; complete pivoting is one
  (`Matrix.IsCompletePivot.isRookPivot`).
* `Matrix.gemPivotStage`: $k$ stages of Gaussian elimination with a row-pivoting strategy, as the
  pair of the current matrix and the accumulated row permutation.
* `Matrix.gemFullPivotStage`: the same for a strategy that chooses an entry, as the triple of the
  current matrix and the accumulated row and column permutations.
* `Matrix.supAbs`: the largest absolute value $\mu(A)$ of an entry of a real matrix.
* `Matrix.growthFactor`: the growth factor $\rho(A)$ of Gaussian elimination without pivoting.
* `Matrix.HasDominantPivots`: at every stage the pivot dominates the trailing block.
* `Matrix.absGemPivot`: the modulus of the $k$-th pivot.
* `Matrix.wilkinsonGrowthBound`: Wilkinson's bound $W(n) = n^{1/2} (2 \cdot 3^{1/2} \cdots
  n^{1/(n-1)})^{1/2}$.

## Main results

* `Matrix.exists_permMatrix_mul_isLU`: every square matrix has $P_\sigma A = LU$ with
  $|l_{ij}| \le 1$.
* `Matrix.exists_permMatrix_mul_mul_permMatrix_isLU`: every square matrix has $P A Q = LU$ with
  $|l_{ij}| \le 1$ and $|u_{ij}| \le |u_{ii}|$.
* `Matrix.gemStage_permMatrix_mul_eq_submatrix_gemPivotStage`: the stages of Gaussian elimination
  without pivoting on $P_\sigma A$ are the pivoted stages, with their rows permuted by the later
  interchanges.
* `Matrix.gemPivotStage_permMatrix_mul_isLU`: the pivoted recurrence computes $P_\sigma A = LU$ when
  the chosen pivots are nonzero.
* `Matrix.gemPivotStage_norm_gemLower_le_one`,
  `Matrix.gemPivotStage_partialPivotRow_norm_gemLower_le_one`: the multipliers of partial pivoting
  have modulus at most one.
* `Matrix.gemPivotStage_permMatrix_mul_isLU_of_isPartialPivot`: partial pivoting factors
  $P_\sigma A = LU$ for every square matrix.
* `Matrix.gemStage_submatrix_eq_submatrix_gemFullPivotStage`: the two-sided analogue for complete
  pivoting.
* `Matrix.gemFullPivotStage_permMatrix_mul_mul_permMatrix_isLU`: rook pivoting, and so complete
  pivoting, factors $P A Q = LU$ for every square matrix, with $|l_{ij}| \le 1$ and
  $|u_{ij}| \le |u_{ii}|$.
* `Matrix.gemFullPivotStage_trailing_eq_zero_of_rank`: complete pivoting reveals the rank
  ([golub2013matrix], §3.4.6).
* `Matrix.exists_permMatrix_mul_isRectLU`: partial pivoting on a tall block column
  ([golub2013matrix], (3.6.2)).
* `Matrix.growthFactor_le_two_pow`: $\rho \le 2^{N-1}$ when the multipliers have modulus at most
  one.
* `Matrix.growthFactor_eq_one_of_posDef`: $\rho = 1$ for a symmetric positive definite matrix.
* `Matrix.growthFactor_le_two_of_isColDiagDominant`: $\rho \le 2$ for a nonsingular column
  diagonally dominant matrix.
* `Matrix.growthFactor_le_card_of_isUpperHessenberg`: $\rho \le N$ for partial pivoting on an upper
  Hessenberg matrix.
* `Matrix.growthFactor_le_two_of_isTridiagonal`: $\rho \le 2$ for partial pivoting on a tridiagonal
  matrix.
* `Matrix.growthFactor_le_two_pow_of_hasBandwidth`: $\rho \le 2^{p+q}$ for partial pivoting on a
  band matrix.
* `Matrix.gemPivotStage_partialPivotRow_hasUpperBandwidth`,
  `Matrix.gemPivotStage_partialPivotRow_multiplier_eq_zero`: the band structure of the factors of
  partial pivoting, Theorem 4.3.2 of [golub2013matrix].
* `Matrix.abs_gemFullPivotStage_le_wilkinson`: Wilkinson's bound stage by stage ([golub2013matrix],
  (3.4.10)).
* `Matrix.growthFactor_le_of_completePivoting`,
  `Matrix.growthFactor_le_wilkinson_of_isCompletePivot`: Wilkinson's bound $\rho \le W(N)$ under
  dominant pivots, and for complete pivoting.

## Proof outline

The existence theorems are proved by strong induction on the number of indices, as in
`Numlib.LinearAlgebra.Matrix.LU`: the pivot is moved to the first index by a transposition, one step
of elimination is taken, and the permutation of the trailing block is extended. For the recurrence,
the key fact is that the interchanges after stage $k$ fix the indices below $k$, so they commute
with the elimination steps up to stage $k$. Wilkinson's bound uses Hadamard's determinant inequality
(`Matrix.norm_det_le_of_forall_norm_le`) on the leading blocks of the reduced matrices, followed by
a telescoping induction over the pivots.

## Notation

* $P_\sigma$ is the permutation matrix `σ.permMatrix 𝕜`, with $(P_\sigma A)_{ij} = a_{\sigma(i) j}$.
* $B^{(k)}$ is the stage `Matrix.gemStage B k` of Gaussian elimination *without* pivoting on $B$,
  with $B^{(0)} = B$.
* $(\hat A^{(k)}, \sigma_k)$ is `Matrix.gemPivotStage A piv k`, and
  $(\hat A^{(k)}, \sigma_k, \tau_k)$ is `Matrix.gemFullPivotStage A piv k`.
* $\mu(A) = \max_{i, j} |a_{ij}|$ is `Matrix.supAbs A`.
* $\rho(A)$ is `Matrix.growthFactor A`.
* $W(n)$ is `Matrix.wilkinsonGrowthBound n`.

## Implementation notes

* Indices and stages are numbered from $0$, and the sources number them from $1$.
* A row permutation is applied as `A.submatrix σ id`, whose entries are $a_{\sigma(i) j}$ by
  definition. The form `σ.permMatrix K * A` of the statements is the same matrix, by
  `PEquiv.toMatrix_toPEquiv_mul`. A two-sided permutation `A.submatrix σ τ` is
  $P_\sigma A P_{\tau^{-1}}$ (`Matrix.permMatrix_mul_mul_permMatrix`).
* The recurrence is on `Fin N`, as `Matrix.gemStage` is. The accumulated permutation is
  $\sigma_{k+1} = \sigma_k s_k$, with $s_k$ the transposition of $k$ and the pivot row, so that
  $P_{\sigma_k} = P_{s_{k-1}} \cdots P_{s_0}$, and the later interchanges $\sigma_k^{-1} \sigma_N$
  fix the indices below $k$. The complete-pivoting recurrence carries a second permutation with the
  same bookkeeping. The only new fact that it needs is that an elimination step commutes with a
  permutation of the *columns* that fixes the pivot (`Matrix.elimStep_submatrix_id_of_apply_self`).
* The growth factor is defined with the exact stages and over $\mathbb{R}$. The source defines it
  with the computed stages; [higham2002accuracy] (after Theorem 9.5) explains that the exact growth
  factor is the one that can be bounded. For partial pivoting the growth factor is
  $\rho(P_\sigma A)$, because the pivoted stages are the stages of elimination without pivoting on
  $P_\sigma A$ up to the order of the rows.
* Bohte's band bound is not proved. Section 3.10 (1) of [quarteroni2000numerical] and Theorem 9.11
  of [higham2002accuracy] state that a matrix with upper and lower bandwidth $p$ has
  $\rho \le 2^{2p-1} - (p-1) 2^{p-2}$ under partial pivoting. This module proves instead
  $\rho \le 2^{p+q}$ for lower bandwidth $p$ and upper bandwidth $q$
  (`Matrix.growthFactor_le_two_pow_of_hasBandwidth`). That bound carries the content of the source's
  item, namely that the growth factor of a band matrix is bounded independently of the order, and
  `Matrix.growthFactor_le_two_of_isTridiagonal` gives the sharp tridiagonal bound $2$. Bohte's
  constant is about a factor two better for $p = q$. Neither source proves it:
  [quarteroni2000numerical] states it without proof, and [higham2002accuracy] refers to Z. Bohte,
  *Bounds for rounding errors in the Gaussian elimination for band systems*, J. Inst. Maths.
  Applics. 16 (1975), 133–142, and records the sharp bound for $p \neq q$ as an open problem
  (Problem 9.15). A proof of the printed constant would need Bohte's finer analysis of how the
  entries of one band row grow along a sweep, a second-order recursion in the pair (column offset,
  number of updates), in place of the argument here that each update at most doubles the column. No
  other result of the library depends on it.
-/

open Finset

universe u

namespace Matrix

/-! ### Row and column permutations of a one-step Schur complement -/

section Perm

variable {n : Type*} {K : Type*} [Field K]

/-- Let $p$ be an index, and let $\sigma$ and $\rho$ be permutations of the indices other than $p$,
extended to all indices by $p \mapsto p$. Then the one-step Schur complement at $p$ of the
matrix with the entries $a_{\sigma(i) \rho(j)}$ is the Schur complement of $A$ at $p$ with its
rows permuted by $\sigma$ and its columns permuted by $\rho$. -/
theorem schurComplementSingle_submatrix_ofSubtype [DecidableEq n] (A : Matrix n n K) (p : n)
    (σ ρ : Equiv.Perm {i : n // i ≠ p}) :
    (A.submatrix (Equiv.Perm.ofSubtype σ) (Equiv.Perm.ofSubtype ρ)).schurComplementSingle p =
      (A.schurComplementSingle p).submatrix σ ρ := by
  ext i j
  simp only [schurComplementSingle_apply, submatrix_apply, Equiv.Perm.ofSubtype_apply_coe,
    Equiv.Perm.ofSubtype_apply_of_not_mem (p := fun i => i ≠ p) _ (not_not.2 rfl)]

/-- A permutation of the indices other than $p$, extended by `Equiv.Perm.ofSubtype`, fixes $p$. -/
theorem ofSubtype_ne_apply_self [DecidableEq n] (p : n) (σ : Equiv.Perm {i : n // i ≠ p}) :
    Equiv.Perm.ofSubtype σ p = p :=
  Equiv.Perm.ofSubtype_apply_of_not_mem (p := fun i => i ≠ p) _ (not_not.2 rfl)

end Perm

/-! ### Existence of $PA = LU$ and $PAQ = LU$ -/

section Existence

variable {n : Type u} [LinearOrder n] {𝕜 : Type*} [NormedField 𝕜]

/-- Let $p$ be an index with $|a_{ip}| \le |a_{pp}|$ for every $i$, and let $L'$ be a matrix on the
indices other than $p$ with $|l'_{ij}| \le 1$ for all $i, j$. Then every entry of the bordered
lower factor `Matrix.luLowerOfSchur A p L'` has modulus at most $1$.

The entries in the column $p$ are the multipliers $a_{ip} / a_{pp}$, and these are $0$ if
$a_{pp} = 0$. -/
theorem norm_luLowerOfSchur_apply_le_one {A : Matrix n n 𝕜} {p : n}
    (hpiv : ∀ i, ‖A i p‖ ≤ ‖A p p‖) {L' : Matrix {i // i ≠ p} {i // i ≠ p} 𝕜}
    (hL' : ∀ i j, ‖L' i j‖ ≤ 1) (i j : n) : ‖luLowerOfSchur A p L' i j‖ ≤ 1 := by
  simp only [luLowerOfSchur, of_apply]
  split_ifs with hi hj hj
  · simp
  · simp
  · rcases eq_or_ne (A p p) 0 with h0 | h0
    · simp [h0]
    · rw [norm_div, div_le_one (norm_pos_iff.2 h0)]
      exact hpiv i
  · exact hL' _ _

/-- Let $p$ be an index with $|a_{pj}| \le |a_{pp}|$ for every $j$, and let $U'$ be a matrix on the
indices other than $p$ with $|u'_{ij}| \le |u'_{ii}|$ for all $i, j$. Then the bordered upper
factor $U$ = `Matrix.luUpperOfSchur A p U'` satisfies $|u_{ij}| \le |u_{ii}|$ for all $i, j$:
every row of $U$ is dominated by its diagonal entry. -/
theorem norm_luUpperOfSchur_apply_le {A : Matrix n n 𝕜} {p : n}
    (hpiv : ∀ j, ‖A p j‖ ≤ ‖A p p‖) {U' : Matrix {i // i ≠ p} {i // i ≠ p} 𝕜}
    (hU' : ∀ i j, ‖U' i j‖ ≤ ‖U' i i‖) (i j : n) :
    ‖luUpperOfSchur A p U' i j‖ ≤ ‖luUpperOfSchur A p U' i i‖ := by
  simp only [luUpperOfSchur, of_apply]
  rcases eq_or_ne i p with rfl | hi
  · simpa using hpiv j
  · simp only [hi, dite_false]
    rcases eq_or_ne j p with rfl | hj
    · simp
    · simpa [hj] using hU' ⟨i, hi⟩ ⟨j, hj⟩

variable [Fintype n]

omit [LinearOrder n] [Fintype n] in
/-- **Partial pivoting**, for a fixed number of indices: for every finite linear order $n$ with $N$
elements and every $A \in \mathbb{K}^{n \times n}$ over a normed field $\mathbb{K}$, there are a
permutation $\sigma$ of $n$ and an LU factorization of the matrix $(a_{\sigma(i) j})_{i, j}$
whose lower factor satisfies $|l_{ij}| \le 1$ for all $i, j$.

The proof is a strong induction on $N$. A row of maximal modulus in the first column is moved to
the first index by a transposition, one step of elimination is taken, and the permutation of the
trailing block is extended by `Equiv.Perm.ofSubtype`. -/
theorem exists_submatrix_isLU_of_card (N : ℕ) :
    ∀ {n : Type u} [Fintype n] [LinearOrder n] (A : Matrix n n 𝕜), Fintype.card n = N →
      ∃ (σ : Equiv.Perm n) (L U : Matrix n n 𝕜), IsLU (A.submatrix σ id) L U ∧
        ∀ i j, ‖L i j‖ ≤ 1 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n _ _ A hN
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, 1, 1, ⟨isUnitLowerTriangular_one, blockTriangular_one,
      Matrix.ext fun i => isEmptyElim i⟩, fun i => isEmptyElim i⟩
  set p := univ.min' (univ_nonempty : (univ : Finset n).Nonempty)
  have hp : ∀ i, p ≤ i := fun i => min'_le _ _ (mem_univ i)
  obtain ⟨r, -, hr⟩ := Finset.exists_max_image univ (fun r => ‖A r p‖) univ_nonempty
  set A' := A.submatrix (Equiv.swap p r) id with hA'
  have hpiv : ∀ i, ‖A' i p‖ ≤ ‖A' p p‖ := fun i => by
    simp only [hA', submatrix_apply, id, Equiv.swap_apply_left]
    exact hr _ (mem_univ _)
  have hcard : Fintype.card {i // i ≠ p} < N :=
    hN ▸ Fintype.card_subtype_lt (x := p) (not_not.2 rfl)
  obtain ⟨σ', L', U', h', hL'⟩ := ih _ hcard (A'.schurComplementSingle p) rfl
  set A'' := A'.submatrix (Equiv.Perm.ofSubtype σ') id with hA''
  have hA''p : ∀ i, ‖A'' i p‖ ≤ ‖A'' p p‖ := fun i => by
    simp only [hA'', submatrix_apply, id, ofSubtype_ne_apply_self]
    exact hpiv _
  have hS : A''.schurComplementSingle p = (A'.schurComplementSingle p).submatrix σ' id := by
    simpa using schurComplementSingle_submatrix_ofSubtype A' p σ' 1
  refine ⟨Equiv.swap p r * Equiv.Perm.ofSubtype σ', luLowerOfSchur A'' p L',
    luUpperOfSchur A'' p U', ?_, norm_luLowerOfSchur_apply_le_one hA''p hL'⟩
  have : A.submatrix (Equiv.swap p r * Equiv.Perm.ofSubtype σ') id = A'' := by
    rw [hA'', hA', submatrix_submatrix]
    rfl
  rw [this]
  refine isLU_luLowerOfSchur_luUpperOfSchur' hp (fun h0 i => ?_) (by rwa [hS])
  have := hA''p i
  rw [h0, norm_zero] at this
  exact norm_le_zero_iff.1 this

omit [LinearOrder n] [Fintype n] in
/-- **Complete pivoting**, for a fixed number of indices: for every finite linear order $n$ with $N$
elements and every $A \in \mathbb{K}^{n \times n}$ over a normed field $\mathbb{K}$, there are
permutations $\sigma$ and $\rho$ of $n$ and an LU factorization $LU$ of the matrix
$(a_{\sigma(i) \rho(j)})_{i, j}$ with $|l_{ij}| \le 1$ and $|u_{ij}| \le |u_{ii}|$ for all
$i, j$.

The proof is the induction of `Matrix.exists_submatrix_isLU_of_card`, with the pivot chosen in
the whole matrix. -/
theorem exists_submatrix_submatrix_isLU_of_card (N : ℕ) :
    ∀ {n : Type u} [Fintype n] [LinearOrder n] (A : Matrix n n 𝕜), Fintype.card n = N →
      ∃ (σ ρ : Equiv.Perm n) (L U : Matrix n n 𝕜), IsLU (A.submatrix σ ρ) L U ∧
        (∀ i j, ‖L i j‖ ≤ 1) ∧ ∀ i j, ‖U i j‖ ≤ ‖U i i‖ := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n _ _ A hN
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, 1, 1, 1, ⟨isUnitLowerTriangular_one, blockTriangular_one,
      Matrix.ext fun i => isEmptyElim i⟩, fun i => isEmptyElim i, fun i => isEmptyElim i⟩
  set p := univ.min' (univ_nonempty : (univ : Finset n).Nonempty)
  have hp : ∀ i, p ≤ i := fun i => min'_le _ _ (mem_univ i)
  obtain ⟨⟨q, r⟩, -, hqr⟩ :=
    Finset.exists_max_image univ (fun qr : n × n => ‖A qr.1 qr.2‖) univ_nonempty
  set A' := A.submatrix (Equiv.swap p q) (Equiv.swap p r) with hA'
  have hpiv : ∀ i j, ‖A' i j‖ ≤ ‖A' p p‖ := fun i j => by
    simp only [hA', submatrix_apply, Equiv.swap_apply_left]
    exact hqr (Equiv.swap p q i, Equiv.swap p r j) (mem_univ _)
  have hcard : Fintype.card {i // i ≠ p} < N :=
    hN ▸ Fintype.card_subtype_lt (x := p) (not_not.2 rfl)
  obtain ⟨σ', ρ', L', U', h', hL', hU'⟩ := ih _ hcard (A'.schurComplementSingle p) rfl
  set A'' := A'.submatrix (Equiv.Perm.ofSubtype σ') (Equiv.Perm.ofSubtype ρ') with hA''
  have hA''pp : ∀ i j, ‖A'' i j‖ ≤ ‖A'' p p‖ := fun i j => by
    simp only [hA'', submatrix_apply, ofSubtype_ne_apply_self]
    exact hpiv _ _
  have hS : A''.schurComplementSingle p = (A'.schurComplementSingle p).submatrix σ' ρ' :=
    schurComplementSingle_submatrix_ofSubtype A' p σ' ρ'
  refine ⟨Equiv.swap p q * Equiv.Perm.ofSubtype σ', Equiv.swap p r * Equiv.Perm.ofSubtype ρ',
    luLowerOfSchur A'' p L', luUpperOfSchur A'' p U', ?_,
    norm_luLowerOfSchur_apply_le_one (fun i => hA''pp i p) hL',
    norm_luUpperOfSchur_apply_le (fun j => hA''pp p j) hU'⟩
  have : A.submatrix (Equiv.swap p q * Equiv.Perm.ofSubtype σ')
      (Equiv.swap p r * Equiv.Perm.ofSubtype ρ') = A'' := by
    rw [hA'', hA', submatrix_submatrix]
    rfl
  rw [this]
  refine isLU_luLowerOfSchur_luUpperOfSchur' hp (fun h0 i => ?_) (by rwa [hS])
  have := hA''pp i p
  rw [h0, norm_zero] at this
  exact norm_le_zero_iff.1 this

/-- **Gaussian elimination with partial pivoting exists.** Let $\mathbb{K}$ be a normed field and
$A \in \mathbb{K}^{n \times n}$. Then there are a permutation $\sigma$ and matrices $L$ and $U$
with
$$P_\sigma A = LU,$$
$L$ unit lower triangular, $U$ upper triangular, and $|l_{ij}| \le 1$ for all $i, j$.

This is equation (3.52) of [quarteroni2000numerical] (see also [higham2002accuracy], §9.3). The
source proves it for a nonsingular $A$. No nonsingularity is needed here, because a zero pivot
column is skipped with a zero column of multipliers. -/
theorem exists_permMatrix_mul_isLU (A : Matrix n n 𝕜) :
    ∃ (σ : Equiv.Perm n) (L U : Matrix n n 𝕜),
      IsLU (σ.permMatrix 𝕜 * A) L U ∧ ∀ i j, ‖L i j‖ ≤ 1 := by
  obtain ⟨σ, L, U, h, hL⟩ := exists_submatrix_isLU_of_card _ A rfl
  exact ⟨σ, L, U, by rwa [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul], hL⟩

/-- **Gaussian elimination with complete pivoting exists.** Let $\mathbb{K}$ be a normed field and
$A \in \mathbb{K}^{n \times n}$. Then there are permutations $\sigma$ and $\tau$ and matrices
$L$ and $U$ with
$$P_\sigma A P_\tau = LU,$$
$L$ unit lower triangular, $U$ upper triangular, $|l_{ij}| \le 1$ and $|u_{ij}| \le |u_{ii}|$
for all $i, j$.

This is complete pivoting of [quarteroni2000numerical], §3.5. The pivot is the largest entry of
the trailing block, so every row of $U$ is dominated by its diagonal entry; this is what
complete pivoting gives in addition to partial pivoting. -/
theorem exists_permMatrix_mul_mul_permMatrix_isLU (A : Matrix n n 𝕜) :
    ∃ (σ τ : Equiv.Perm n) (L U : Matrix n n 𝕜),
      IsLU (σ.permMatrix 𝕜 * A * τ.permMatrix 𝕜) L U ∧ (∀ i j, ‖L i j‖ ≤ 1) ∧
        ∀ i j, ‖U i j‖ ≤ ‖U i i‖ := by
  obtain ⟨σ, ρ, L, U, h, hL, hU⟩ := exists_submatrix_submatrix_isLU_of_card _ A rfl
  refine ⟨σ, ρ⁻¹, L, U, ?_, hL, hU⟩
  rwa [Equiv.Perm.permMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, submatrix_submatrix, Function.id_comp, Function.comp_id,
    Equiv.Perm.inv_def, Equiv.symm_symm]

end Existence

/-! ### The partial-pivoting strategy -/

section PartialPivot

variable {n : Type*} [LinearOrder n] {𝕜 : Type*} [NormedField 𝕜]

/-- A **partial-pivoting strategy**: a function `piv` that maps a matrix $M$ and an index $k$ to a
row $r = $ `piv M k` with $r \ge k$ and
$$|m_{r' k}| \le |m_{rk}| \quad \text{for every } r' \ge k.$$

This is the choice of the pivot row of [quarteroni2000numerical], §3.5, and [golub2013matrix],
§3.4.3. The strategy `Matrix.partialPivotRow` is one (`Matrix.isPartialPivot_partialPivotRow`),
and `Matrix.gemPivotStage` runs the interchanges that a strategy produces.
`Matrix.IsCompletePivot` is the analogue for complete pivoting. -/
def IsPartialPivot (piv : Matrix n n 𝕜 → n → n) : Prop :=
  ∀ (M : Matrix n n 𝕜) (k : n), k ≤ piv M k ∧ ∀ r, k ≤ r → ‖M r k‖ ≤ ‖M (piv M k) k‖

/-- Under a partial-pivoting strategy, a zero pivot comes with a zero column: if the chosen entry
$m_{rk}$ is $0$, then $m_{r' k} = 0$ for every $r' \ge k$. -/
theorem IsPartialPivot.apply_eq_zero {piv : Matrix n n 𝕜 → n → n} (hpiv : IsPartialPivot piv)
    {M : Matrix n n 𝕜} {k : n} (h : M (piv M k) k = 0) {r : n} (hr : k ≤ r) : M r k = 0 := by
  have := (hpiv M k).2 r hr
  rwa [h, norm_zero, norm_le_zero_iff] at this

variable [Fintype n]

/-- Some row $r \ge k$ maximizes $|m_{rk}|$ among the rows $r \ge k$. -/
theorem exists_partialPivotRow (M : Matrix n n 𝕜) (k : n) :
    (univ.filter fun r => k ≤ r ∧ ∀ r', k ≤ r' → ‖M r' k‖ ≤ ‖M r k‖).Nonempty := by
  obtain ⟨r, hr, hmax⟩ := Finset.exists_max_image (univ.filter (k ≤ ·)) (fun r => ‖M r k‖)
    ⟨k, by simp⟩
  refine ⟨r, mem_filter.2 ⟨mem_univ _, (mem_filter.1 hr).2, fun r' hr' => ?_⟩⟩
  exact hmax r' (mem_filter.2 ⟨mem_univ _, hr'⟩)

/-- The **partial-pivoting strategy**: `partialPivotRow M k` is the first row $r \ge k$ at which
$|m_{rk}|$ is maximal among the rows $r \ge k$.

This is the pivot row of [quarteroni2000numerical], §3.5. The choice of the *first* maximizing
row makes the strategy deterministic. If the column vanishes from the row $k$ downwards, it
chooses $k$ itself, so no interchange is made at a zero pivot column. -/
noncomputable def partialPivotRow (M : Matrix n n 𝕜) (k : n) : n :=
  (univ.filter fun r => k ≤ r ∧ ∀ r', k ≤ r' → ‖M r' k‖ ≤ ‖M r k‖).min'
    (exists_partialPivotRow M k)

variable (M : Matrix n n 𝕜) (k : n)

/-- The row `Matrix.partialPivotRow M k` satisfies $r \ge k$ and maximizes $|m_{rk}|$ among the rows
$r \ge k$. -/
theorem partialPivotRow_mem :
    partialPivotRow M k ∈
      univ.filter fun r => k ≤ r ∧ ∀ r', k ≤ r' → ‖M r' k‖ ≤ ‖M r k‖ :=
  Finset.min'_mem _ _

/-- The pivot row lies at or below the current index: $k \le r$ for $r$ =
`Matrix.partialPivotRow M k`. -/
theorem le_partialPivotRow : k ≤ partialPivotRow M k :=
  (mem_filter.1 (partialPivotRow_mem M k)).2.1

/-- The pivot dominates its column from the current index downwards: for $r$ =
`Matrix.partialPivotRow M k` and every $r' \ge k$,
$$|m_{r' k}| \le |m_{rk}|.$$
-/
theorem norm_apply_le_partialPivotRow {r : n} (hr : k ≤ r) :
    ‖M r k‖ ≤ ‖M (partialPivotRow M k) k‖ :=
  (mem_filter.1 (partialPivotRow_mem M k)).2.2 r hr

/-- The pivot row is the *first* maximizing row: if $r' \ge k$ and $|m_{r'' k}| \le |m_{r' k}|$ for
every $r'' \ge k$, then `Matrix.partialPivotRow M k` $\le r'$. -/
theorem partialPivotRow_le {r : n} (hr : k ≤ r) (hmax : ∀ r', k ≤ r' → ‖M r' k‖ ≤ ‖M r k‖) :
    partialPivotRow M k ≤ r :=
  Finset.min'_le _ _ (mem_filter.2 ⟨mem_univ _, hr, hmax⟩)

/-- If the pivot chosen by `Matrix.partialPivotRow` is $0$, then $m_{rk} = 0$ for every $r \ge k$.
-/
theorem apply_eq_zero_of_partialPivotRow_eq_zero (h : M (partialPivotRow M k) k = 0) {r : n}
    (hr : k ≤ r) : M r k = 0 := by
  have := norm_apply_le_partialPivotRow M k hr
  rw [h, norm_zero] at this
  exact norm_le_zero_iff.1 this

/-- At a zero pivot column no interchange is made: if $m_{rk} = 0$ for every $r \ge k$, then
`Matrix.partialPivotRow M k` $= k$. -/
theorem partialPivotRow_eq_self_of_forall_eq_zero (h : ∀ r, k ≤ r → M r k = 0) :
    partialPivotRow M k = k :=
  le_antisymm (partialPivotRow_le M k le_rfl fun r' hr' => by rw [h r' hr', h k le_rfl])
    (le_partialPivotRow M k)

/-- `Matrix.partialPivotRow` is a partial-pivoting strategy in the sense of `Matrix.IsPartialPivot`.
-/
theorem isPartialPivot_partialPivotRow :
    IsPartialPivot (partialPivotRow : Matrix n n 𝕜 → n → n) :=
  fun M k => ⟨le_partialPivotRow M k, fun _ hr => norm_apply_le_partialPivotRow M k hr⟩

end PartialPivot

/-! ### The complete-pivoting strategy -/

section CompletePivot

variable {n : Type*} [LinearOrder n] {𝕜 : Type*} [NormedField 𝕜]

/-- A **complete-pivoting strategy**: a function `piv` that maps a matrix $M$ and an index $k$ to a
pair $(r, c)$ = `piv M k` with $r \ge k$, $c \ge k$ and
$$|m_{ij}| \le |m_{rc}| \quad \text{for all } i \ge k, \ j \ge k.$$
So $m_{rc}$ is an entry of maximal modulus in the trailing block from $k$ on.

This is the choice of the pivot of [quarteroni2000numerical], §3.5, and [higham2002accuracy],
§9.3. `Matrix.gemFullPivotStage` runs the interchanges that such a strategy produces. -/
def IsCompletePivot (piv : Matrix n n 𝕜 → n → n × n) : Prop :=
  ∀ (M : Matrix n n 𝕜) (k : n), k ≤ (piv M k).1 ∧ k ≤ (piv M k).2 ∧
    ∀ i j, k ≤ i → k ≤ j → ‖M i j‖ ≤ ‖M (piv M k).1 (piv M k).2‖

variable [Finite n]

/-- Some entry of the trailing block from $k$ on has maximal modulus in that block: there are
$r \ge k$ and $c \ge k$ with $|m_{ij}| \le |m_{rc}|$ for all $i, j \ge k$. -/
theorem exists_completePivotEntry (M : Matrix n n 𝕜) (k : n) :
    ∃ rc : n × n, k ≤ rc.1 ∧ k ≤ rc.2 ∧
      ∀ i j, k ≤ i → k ≤ j → ‖M i j‖ ≤ ‖M rc.1 rc.2‖ := by
  have : Fintype n := Fintype.ofFinite n
  obtain ⟨rc, hrc, hmax⟩ := Finset.exists_max_image
    (univ.filter fun rc : n × n => k ≤ rc.1 ∧ k ≤ rc.2) (fun rc => ‖M rc.1 rc.2‖)
    ⟨(k, k), by simp⟩
  obtain ⟨-, h1, h2⟩ := mem_filter.1 hrc
  exact ⟨rc, h1, h2, fun i j hi hj => hmax (i, j) (mem_filter.2 ⟨mem_univ _, hi, hj⟩)⟩

/-- The **complete-pivoting strategy** `completePivotEntry M k`: an entry $(r, c)$ of maximal
modulus in the trailing block of $M$ from $k$ on.

Unlike `Matrix.partialPivotRow`, it makes no canonical choice among the maximizing entries; it
is an arbitrary choice, made with `Exists.choose`. A canonical choice is not needed, because
every complete-pivoting strategy satisfies the same growth bound
(`Matrix.growthFactor_le_wilkinson_of_isCompletePivot`). -/
noncomputable def completePivotEntry (M : Matrix n n 𝕜) (k : n) : n × n :=
  (exists_completePivotEntry M k).choose

/-- `Matrix.completePivotEntry` is a complete-pivoting strategy in the sense of
`Matrix.IsCompletePivot`. -/
theorem isCompletePivot_completePivotEntry :
    IsCompletePivot (completePivotEntry : Matrix n n 𝕜 → n → n × n) :=
  fun M k => (exists_completePivotEntry M k).choose_spec

end CompletePivot

/-! ### The rook-pivoting strategy -/

section Rook

variable {n : Type*} [LinearOrder n] {𝕜 : Type*} [NormedField 𝕜]

/-- A **rook-pivoting strategy**: a function `piv` that maps a matrix $M$ and an index $k$ to a pair
$(r, c)$ = `piv M k` with $r \ge k$, $c \ge k$, and
$$|m_{ic}| \le |m_{rc}| \ \text{ for every } i \ge k, \qquad |m_{rj}| \le |m_{rc}| \ \text{ for
  every } j \ge k.$$
So $m_{rc}$ is maximal in modulus both in its column and in its row of the trailing block from
$k$ on.

This is rook pivoting of [golub2013matrix], §3.4.7 (see also [higham2002accuracy], §9.1). The
column condition is the condition of partial pivoting. Complete pivoting is a rook-pivoting
strategy (`Matrix.IsCompletePivot.isRookPivot`). -/
def IsRookPivot (piv : Matrix n n 𝕜 → n → n × n) : Prop :=
  ∀ (M : Matrix n n 𝕜) (k : n), k ≤ (piv M k).1 ∧ k ≤ (piv M k).2 ∧
    (∀ i, k ≤ i → ‖M i (piv M k).2‖ ≤ ‖M (piv M k).1 (piv M k).2‖) ∧
    ∀ j, k ≤ j → ‖M (piv M k).1 j‖ ≤ ‖M (piv M k).1 (piv M k).2‖

/-- A complete-pivoting strategy is a rook-pivoting strategy: the largest entry of the trailing
block is the largest entry of its row and of its column in that block.

With `Matrix.isCompletePivot_completePivotEntry`, this shows that rook-pivoting strategies
exist. -/
theorem IsCompletePivot.isRookPivot {piv : Matrix n n 𝕜 → n → n × n} (h : IsCompletePivot piv) :
    IsRookPivot piv := fun M k =>
  ⟨(h M k).1, (h M k).2.1, fun i hi => (h M k).2.2 i _ hi (h M k).2.1,
    fun j hj => (h M k).2.2 _ j (h M k).1 hj⟩

end Rook

/-! ### Gaussian elimination with a pivoting strategy, on `Fin N` -/

section Stages

variable {K : Type*} [Field K] {N : ℕ}

/-- **Gaussian elimination with a pivoting strategy** `piv`. Let $A \in K^{N \times N}$. The pair
$(\hat A^{(k)}, \sigma_k)$ = `gemPivotStage A piv k` consists of the matrix after $k$ stages and
the accumulated row permutation. It is defined by $(\hat A^{(0)}, \sigma_0) = (A, 1)$ and the
following rule. For $k < N$, let $r_k$ be the row that `piv` chooses for the matrix
$\hat A^{(k)}$ and the index $k$, and let $s_k$ be the transposition of $k$ and $r_k$. Then
$\hat A^{(k+1)}$ is the elimination step at $k$ of $\hat A^{(k)}$ with the rows $k$ and $r_k$
interchanged, and $\sigma_{k+1} = \sigma_k s_k$. For $k \ge N$, nothing changes.

This is Gaussian elimination with pivoting of [quarteroni2000numerical], §3.5. Since
$P_{\sigma s} = P_s P_\sigma$ (`Matrix.permMatrix_mul`),
$P_{\sigma_k} = P_{s_{k-1}} \cdots P_{s_0}$. The strategy `Matrix.partialPivotRow` gives
Gaussian elimination with partial pivoting, and the strategy `fun _ k => k` makes no
interchange. -/
noncomputable def gemPivotStage (A : Matrix (Fin N) (Fin N) K)
    (piv : Matrix (Fin N) (Fin N) K → Fin N → Fin N) :
    ℕ → Matrix (Fin N) (Fin N) K × Equiv.Perm (Fin N)
  | 0 => (A, 1)
  | k + 1 =>
    if h : k < N then
      (elimStep ((gemPivotStage A piv k).1.submatrix
          (Equiv.swap ⟨k, h⟩ (piv (gemPivotStage A piv k).1 ⟨k, h⟩)) id) ⟨k, h⟩,
        (gemPivotStage A piv k).2 * Equiv.swap ⟨k, h⟩ (piv (gemPivotStage A piv k).1 ⟨k, h⟩))
    else gemPivotStage A piv k

variable (A : Matrix (Fin N) (Fin N) K) (piv : Matrix (Fin N) (Fin N) K → Fin N → Fin N)

/-- The interchange $s_k$ of the stage $k < N$: the transposition of $k$ and the pivot row $r_k$
that `piv` chooses for $\hat A^{(k)}$ and $k$. -/
noncomputable def gemPivotSwap (k : ℕ) (h : k < N) : Equiv.Perm (Fin N) :=
  Equiv.swap ⟨k, h⟩ (piv (gemPivotStage A piv k).1 ⟨k, h⟩)

/-- $(\hat A^{(0)}, \sigma_0) = (A, 1)$. -/
@[simp]
theorem gemPivotStage_zero : gemPivotStage A piv 0 = (A, 1) := rfl

/-- For $k < N$, the stage $k + 1$ interchanges, eliminates, and records the interchange:
$\hat A^{(k+1)}$ is the elimination step at $k$ of $\hat A^{(k)}$ with its rows permuted by
$s_k$, and $\sigma_{k+1} = \sigma_k s_k$, where $s_k$ is `Matrix.gemPivotSwap A piv k`. -/
theorem gemPivotStage_succ_of_lt {k : ℕ} (h : k < N) :
    gemPivotStage A piv (k + 1) =
      (elimStep ((gemPivotStage A piv k).1.submatrix (gemPivotSwap A piv k h) id) ⟨k, h⟩,
        (gemPivotStage A piv k).2 * gemPivotSwap A piv k h) := by
  simp only [gemPivotStage, h, dite_true, gemPivotSwap]

/-- For $k \ge N$, the pivoted stages do not change: stage $k + 1$ equals stage $k$. -/
theorem gemPivotStage_succ_of_le {k : ℕ} (h : N ≤ k) :
    gemPivotStage A piv (k + 1) = gemPivotStage A piv k := by
  simp only [gemPivotStage, not_lt.2 h, dite_false]

/-- For $k \ge N$, stage $k$ of `Matrix.gemPivotStage` equals stage $N$. -/
theorem gemPivotStage_of_le {k : ℕ} (h : N ≤ k) :
    gemPivotStage A piv k = gemPivotStage A piv N := by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [gemPivotStage_succ_of_le A piv hk, ih]

/-- One stage of pivoted elimination as a product: for $k < N$,
$$\hat A^{(k+1)} = M_k P_{s_k} \hat A^{(k)},$$
with $P_{s_k}$ the permutation matrix of the interchange and $M_k$ the Gaussian transformation
matrix of $P_{s_k} \hat A^{(k)}$ at the pivot $k$.

This is one stage of equation (3.51) of [quarteroni2000numerical], with the stages numbered from
$0$. -/
theorem gemPivotStage_succ_fst_eq_gaussTransform_mul {k : ℕ} (h : k < N) :
    (gemPivotStage A piv (k + 1)).1 =
      gaussTransform ((gemPivotSwap A piv k h).permMatrix K * (gemPivotStage A piv k).1) ⟨k, h⟩ *
        ((gemPivotSwap A piv k h).permMatrix K * (gemPivotStage A piv k).1) := by
  rw [gemPivotStage_succ_of_lt A piv h, gaussTransform_mul, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul]

/-- If the strategy always chooses a row at or below the current index, then the interchange $s_k$
fixes every index $i < k$. -/
theorem gemPivotSwap_apply_of_lt (hpiv : ∀ M k, k ≤ piv M k) {k : ℕ} (h : k < N) {i : Fin N}
    (hi : (i : ℕ) < k) : gemPivotSwap A piv k h i = i := by
  refine Equiv.swap_apply_of_ne_of_ne (fun hik => ?_) fun hir => ?_
  · rw [hik] at hi
    exact lt_irrefl _ hi
  · have := hpiv (gemPivotStage A piv k).1 ⟨k, h⟩
    rw [← hir, Fin.le_def] at this
    exact absurd (this.trans_lt hi) (lt_irrefl _)

/-- Suppose that the strategy always chooses a row at or below the current index. Then for
$m \le m'$ the interchanges after stage $m$, the permutation $\sigma_m^{-1} \sigma_{m'}$, fix
every index $i < m$. -/
theorem gemPivotStage_snd_inv_mul_apply (hpiv : ∀ M k, k ≤ piv M k) {m m' : ℕ} (hmm' : m ≤ m')
    {i : Fin N} (hi : (i : ℕ) < m) :
    ((gemPivotStage A piv m).2⁻¹ * (gemPivotStage A piv m').2) i = i := by
  induction m', hmm' using Nat.le_induction with
  | base => simp
  | succ m' hm ih =>
    by_cases h : m' < N
    · rw [gemPivotStage_succ_of_lt A piv h]
      dsimp only
      rw [← mul_assoc, Equiv.Perm.mul_apply, gemPivotSwap_apply_of_lt A piv hpiv h (hi.trans_le hm),
        ih]
    · rw [gemPivotStage_succ_of_le A piv (not_lt.1 h), ih]

/-- Let $\rho$ be a permutation with $\rho(i) = i$ for every $i \le p$. Then one elimination step at
$p$ commutes with the permutation of the rows by $\rho$: the step of the matrix with the entries
$m_{\rho(i) j}$ is the matrix with the entries $m'_{\rho(i) j}$, where $M'$ is the step of $M$
at $p$. -/
theorem elimStep_submatrix_of_forall_le {n : Type*} [LinearOrder n] [Fintype n]
    (M : Matrix n n K) {p : n} {ρ : Equiv.Perm n} (hρ : ∀ i, i ≤ p → ρ i = i) :
    elimStep (M.submatrix ρ id) p = (elimStep M p).submatrix ρ id := by
  have hp : ρ p = p := hρ p le_rfl
  have hlt : ∀ i, p < ρ i ↔ p < i := fun i => by
    rcases le_or_gt i p with hi | hi
    · rw [hρ i hi]
    · refine ⟨fun _ => hi, fun _ => lt_of_not_ge fun h => ?_⟩
      have := hρ _ h
      rw [ρ.injective.eq_iff] at this
      rw [this] at h
      exact absurd hi (not_lt.2 h)
  ext i j
  simp only [elimStep_apply, submatrix_apply, id, hp, hlt]

/-- **The stages of Gaussian elimination on $P_\sigma A$ are the pivoted stages, with their rows
permuted by the later interchanges.** Suppose that the strategy always chooses a row at or below
the current index, and let $\sigma = \sigma_N$ be the final permutation. Let $B$ be the matrix
with the entries $b_{ij} = a_{\sigma(i) j}$. Then for every $k$,
$$b^{(k)}_{ij} = \hat a^{(k)}_{\pi_k(i) j}, \qquad \pi_k = \sigma_k^{-1} \sigma.$$

This is the content of the relation $L = P M^{-1}$ in [quarteroni2000numerical], §3.5. -/
theorem gemStage_submatrix_eq_submatrix_gemPivotStage (hpiv : ∀ M k, k ≤ piv M k) (k : ℕ) :
    gemStage (A.submatrix (gemPivotStage A piv N).2 id) k =
      (gemPivotStage A piv k).1.submatrix
        ((gemPivotStage A piv k).2⁻¹ * (gemPivotStage A piv N).2) id := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases h : k < N
    · rw [gemStage_succ_of_lt _ h, ih, gemPivotStage_succ_of_lt A piv h]
      dsimp only
      have hρ : (gemPivotStage A piv k).2⁻¹ * (gemPivotStage A piv N).2 =
          gemPivotSwap A piv k h *
            (((gemPivotStage A piv k).2 * gemPivotSwap A piv k h)⁻¹ *
              (gemPivotStage A piv N).2) := by
        rw [_root_.mul_inv_rev, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
      rw [hρ, Equiv.Perm.coe_mul, ← Function.id_comp id, ← submatrix_submatrix,
        Function.id_comp]
      refine elimStep_submatrix_of_forall_le _ fun i hi => ?_
      have hk : (gemPivotStage A piv (k + 1)).2 =
          (gemPivotStage A piv k).2 * gemPivotSwap A piv k h := by
        rw [gemPivotStage_succ_of_lt A piv h]
      rw [← hk]
      exact gemPivotStage_snd_inv_mul_apply A piv hpiv h (Nat.lt_succ_of_le (Fin.le_def.1 hi))
    · rw [gemStage_succ_of_le _ (not_lt.1 h), ih, gemPivotStage_succ_of_le A piv (not_lt.1 h)]

/-- The permutation-matrix form of `Matrix.gemStage_submatrix_eq_submatrix_gemPivotStage`: if the
strategy always chooses a row at or below the current index, then for every $k$ the stage
$(P_\sigma A)^{(k)}$, with $\sigma = \sigma_N$, is $\hat A^{(k)}$ with its rows permuted by
$\sigma_k^{-1} \sigma$. -/
theorem gemStage_permMatrix_mul_eq_submatrix_gemPivotStage (hpiv : ∀ M k, k ≤ piv M k)
    (k : ℕ) :
    gemStage ((gemPivotStage A piv N).2.permMatrix K * A) k =
      (gemPivotStage A piv k).1.submatrix
        ((gemPivotStage A piv k).2⁻¹ * (gemPivotStage A piv N).2) id := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  exact gemStage_submatrix_eq_submatrix_gemPivotStage A piv hpiv k

/-- If the strategy always chooses a row at or below the current index, then the last stage of
Gaussian elimination without pivoting on $P_{\sigma_N} A$ is the last pivoted stage:
$(P_{\sigma_N} A)^{(N)} = \hat A^{(N)}$. -/
theorem gemStage_permMatrix_mul_card (hpiv : ∀ M k, k ≤ piv M k) :
    gemStage ((gemPivotStage A piv N).2.permMatrix K * A) N = (gemPivotStage A piv N).1 := by
  rw [gemStage_permMatrix_mul_eq_submatrix_gemPivotStage A piv hpiv, inv_mul_cancel]
  rfl

/-- Suppose that the strategy always chooses a row at or below the current index. Then for $k < N$,
the pivot of stage $k$ of Gaussian elimination without pivoting on $P_{\sigma_N} A$ is the entry
chosen by the strategy:
$$(P_{\sigma_N} A)^{(k)}_{kk} = \hat a^{(k)}_{r_k k},$$
where $r_k$ is the row that `piv` chooses for $\hat A^{(k)}$ and $k$. -/
theorem gemStage_permMatrix_mul_apply_self (hpiv : ∀ M k, k ≤ piv M k) {k : ℕ} (h : k < N) :
    gemStage ((gemPivotStage A piv N).2.permMatrix K * A) k ⟨k, h⟩ ⟨k, h⟩ =
      (gemPivotStage A piv k).1 (piv (gemPivotStage A piv k).1 ⟨k, h⟩) ⟨k, h⟩ := by
  rw [gemStage_permMatrix_mul_eq_submatrix_gemPivotStage A piv hpiv, submatrix_apply, id]
  have hρ : (gemPivotStage A piv k).2⁻¹ * (gemPivotStage A piv N).2 =
      gemPivotSwap A piv k h * ((gemPivotStage A piv (k + 1)).2⁻¹ * (gemPivotStage A piv N).2) := by
    rw [gemPivotStage_succ_of_lt A piv h]
    dsimp only
    rw [_root_.mul_inv_rev, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hρ, Equiv.Perm.mul_apply, gemPivotStage_snd_inv_mul_apply A piv hpiv h (Nat.lt_succ_self k),
    gemPivotSwap, Equiv.swap_apply_left]

/-- Suppose that the strategy always chooses a row at or below the current index. Then for
$m \le m'$ the later interchanges $\sigma_m^{-1} \sigma_{m'}$ map each index $i \ge m$ to an
index $\ge m$. -/
theorem le_gemPivotStage_snd_inv_mul_apply (hpiv : ∀ M k, k ≤ piv M k) {m m' : ℕ} (hmm' : m ≤ m')
    {i : Fin N} (hi : m ≤ (i : ℕ)) :
    m ≤ (((gemPivotStage A piv m).2⁻¹ * (gemPivotStage A piv m').2) i : ℕ) := by
  by_contra hcon
  have h := gemPivotStage_snd_inv_mul_apply A piv hpiv hmm' (not_le.1 hcon)
  rw [Equiv.apply_eq_iff_eq] at h
  rw [h] at hcon
  exact hcon hi

/-- **Pivoted elimination computes $P_\sigma A = LU$.** Let $A \in K^{N \times N}$. Suppose that the
strategy always chooses a row at or below the current index, and that the chosen pivot
$\hat a^{(k)}_{r_k k}$ is nonzero for every $k$ with $k + 1 < N$. Then, with
$\sigma = \sigma_N$,
$$P_\sigma A = LU,$$
where $U = \hat A^{(N)}$ is the last pivoted stage and $L$ is the multiplier matrix
`Matrix.gemLower` of Gaussian elimination *without* pivoting on $P_\sigma A$.

This is equation (3.52) of [quarteroni2000numerical] for the recurrence. It expresses the remark
there that "the entries of $L$ coincide with the multipliers computed by LU factorization,
without pivoting, when applied to the matrix $PA$". The last pivot is never used as a divisor,
so it may be zero. -/
theorem gemPivotStage_permMatrix_mul_isLU (hpiv : ∀ M k, k ≤ piv M k)
    (hnz : ∀ k (hk : k < N), k + 1 < N →
      (gemPivotStage A piv k).1 (piv (gemPivotStage A piv k).1 ⟨k, hk⟩) ⟨k, hk⟩ ≠ 0) :
    IsLU ((gemPivotStage A piv N).2.permMatrix K * A)
      (gemLower ((gemPivotStage A piv N).2.permMatrix K * A)) (gemPivotStage A piv N).1 := by
  rw [← gemStage_permMatrix_mul_card A piv hpiv]
  refine isLU_gemLower_gemStage _ fun m hm hmN => ?_
  rw [gemStage_permMatrix_mul_apply_self A piv hpiv hm]
  exact hnz m hm hmN

/-- **The multipliers of partial pivoting have modulus at most one.** Let $\mathbb{K}$ be a normed
field, let `piv` be a partial-pivoting strategy, and let $A \in \mathbb{K}^{N \times N}$. Then
every entry of the multiplier matrix $L$ of Gaussian elimination without pivoting on
$P_{\sigma_N} A$ satisfies $|l_{ij}| \le 1$.

The multiplier $l_{ij}$ is $\hat a^{(j)}_{rj} / \hat a^{(j)}_{r_j j}$ for some row $r \ge j$,
and the pivot row $r_j$ maximizes the modulus in the column. -/
theorem gemPivotStage_norm_gemLower_le_one {𝕜 : Type*} [NormedField 𝕜]
    {piv : Matrix (Fin N) (Fin N) 𝕜 → Fin N → Fin N} (hpiv : IsPartialPivot piv)
    (A : Matrix (Fin N) (Fin N) 𝕜) (i j : Fin N) :
    ‖gemLower ((gemPivotStage A piv N).2.permMatrix 𝕜 * A) i j‖ ≤ 1 := by
  have hle : ∀ (M : Matrix (Fin N) (Fin N) 𝕜) k, k ≤ piv M k := fun M k => (hpiv M k).1
  simp only [gemLower, of_apply]
  split_ifs with hij hij'
  · set M := (gemPivotStage A piv j).1
    set ρ := (gemPivotStage A piv j).2⁻¹ * (gemPivotStage A piv N).2
    have hden : gemStage ((gemPivotStage A piv N).2.permMatrix 𝕜 * A) j j j = M (piv M j) j :=
      gemStage_permMatrix_mul_apply_self A piv hle j.2
    have hnum : gemStage ((gemPivotStage A piv N).2.permMatrix 𝕜 * A) j i j = M (ρ i) j := by
      rw [gemStage_permMatrix_mul_eq_submatrix_gemPivotStage A piv hle j, submatrix_apply]
      rfl
    rw [norm_div, hnum, hden]
    rcases eq_or_ne (M (piv M j) j) 0 with h0 | h0
    · rw [h0, norm_zero, div_zero]
      exact zero_le_one
    · rw [div_le_one (norm_pos_iff.2 h0)]
      exact (hpiv M j).2 _ (Fin.le_def.2
        (le_gemPivotStage_snd_inv_mul_apply A piv hle j.2.le (Fin.le_def.1 hij.le)))
  · simp
  · simp

/-- The multipliers of `Matrix.partialPivotRow` have modulus at most one: for
$A \in \mathbb{K}^{N \times N}$ over a normed field, every entry of the multiplier matrix $L$ of
Gaussian elimination without pivoting on $P_{\sigma_N} A$, with $\sigma_N$ the permutation of
partial pivoting, satisfies $|l_{ij}| \le 1$.

This is `Matrix.gemPivotStage_norm_gemLower_le_one` for the strategy `Matrix.partialPivotRow`. -/
theorem gemPivotStage_partialPivotRow_norm_gemLower_le_one {𝕜 : Type*} [NormedField 𝕜]
    (A : Matrix (Fin N) (Fin N) 𝕜) (i j : Fin N) :
    ‖gemLower ((gemPivotStage A partialPivotRow N).2.permMatrix 𝕜 * A) i j‖ ≤ 1 :=
  gemPivotStage_norm_gemLower_le_one isPartialPivot_partialPivotRow A i j

end Stages

/-! ### Zero pivots with zero columns -/

section ZeroPivot

variable {K : Type*} [Field K] {N : ℕ} (A : Matrix (Fin N) (Fin N) K)

/-- The shape of the stages when every zero pivot comes with a zero column. Suppose that for every
$m < N$ with $a^{(m)}_{mm} = 0$, also $a^{(m)}_{im} = 0$ for every $i > m$. Then $A^{(k)}$
vanishes below the diagonal in its first $k$ columns: $a^{(k)}_{ij} = 0$ whenever $j < k$ and
$j < i$.

This is `Matrix.gemStage_apply_eq_zero_of_lt` with the hypothesis of nonzero pivots weakened. At
a zero pivot the multipliers are $0$, so the step does not change the column, which is already
zero. -/
theorem gemStage_apply_eq_zero_of_lt'
    (hz : ∀ (m : ℕ) (hm : m < N) (i : Fin N), m < (i : ℕ) →
      gemStage A m ⟨m, hm⟩ ⟨m, hm⟩ = 0 → gemStage A m i ⟨m, hm⟩ = 0)
    {k : ℕ} {i j : Fin N} (hjk : (j : ℕ) < k) (hji : j < i) : gemStage A k i j = 0 := by
  induction k generalizing i j with
  | zero => exact absurd hjk (Nat.not_lt_zero _)
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with hjk | hjk
    · by_cases hkN : k < N
      · rw [gemStage_succ_of_lt A hkN,
          elimStep_apply_of_pivot_row_eq_zero _ _ _ (ih hjk (Fin.mk_lt_of_lt_val hjk))]
        exact ih hjk hji
      · rw [gemStage_succ_of_le A (not_lt.1 hkN)]
        exact ih hjk hji
    · have hkN : k < N := hjk ▸ j.isLt
      have hj : j = (⟨k, hkN⟩ : Fin N) := Fin.ext hjk
      subst hj
      rw [gemStage_succ_of_lt A hkN, elimStep_apply_of_lt _ hji]
      rcases eq_or_ne (gemStage A k ⟨k, hkN⟩ ⟨k, hkN⟩) 0 with h0 | h0
      · rw [hz k hkN i (Fin.lt_def.1 hji) h0, h0]
        ring
      · rw [mul_assoc, inv_mul_cancel₀ h0, mul_one, sub_self]

/-- **Gaussian elimination factors when every zero pivot comes with a zero column.** Let
$A \in K^{N \times N}$, and suppose that for every $m < N$ with $a^{(m)}_{mm} = 0$, also
$a^{(m)}_{im} = 0$ for every $i > m$. Then $A = LU$ with $L$ the multiplier matrix
`Matrix.gemLower A` and $U = A^{(N)}$.

This is `Matrix.isLU_gemLower_gemStage` with the hypothesis of nonzero pivots replaced. Partial,
rook and complete pivoting give this property, so the algorithmic factorizations
$P_\sigma A = LU$ and $P A Q = LU$ hold for every matrix ([golub2013matrix], §3.4.3: "Algorithm
3.4.1 always runs to completion"). -/
theorem isLU_gemLower_gemStage'
    (hz : ∀ (m : ℕ) (hm : m < N) (i : Fin N), m < (i : ℕ) →
      gemStage A m ⟨m, hm⟩ ⟨m, hm⟩ = 0 → gemStage A m i ⟨m, hm⟩ = 0) :
    IsLU A (gemLower A) (gemStage A N) where
  isUnitLowerTriangular := isUnitLowerTriangular_gemLower A
  isUpperTriangular := fun _ j hij => gemStage_apply_eq_zero_of_lt' A hz j.2 hij
  mul_eq := by rw [← gemLowerStage_of_le A le_rfl, gemLowerStage_mul_gemStage]

/-- **Gaussian elimination with partial pivoting always factors.** Let $\mathbb{K}$ be a normed
field, let `piv` be a partial-pivoting strategy, and let $A \in \mathbb{K}^{N \times N}$. Then,
with $\sigma = \sigma_N$,
$$P_\sigma A = LU,$$
where $U = \hat A^{(N)}$ is the last pivoted stage and $L$ is the multiplier matrix of Gaussian
elimination without pivoting on $P_\sigma A$.

This is `Matrix.gemPivotStage_permMatrix_mul_isLU` with no hypothesis on the pivots, because a
zero pivot of partial pivoting comes with a zero column (`Matrix.IsPartialPivot.apply_eq_zero`).
It is the statement of [golub2013matrix], §3.4.3: "Algorithm 3.4.1 always runs to completion. If
$A(k{:}n, k) = 0$ in step $k$, then $M_k = I_n$" (see also [quarteroni2000numerical], §3.5). The
analogue for rook pivoting is `Matrix.gemFullPivotStage_permMatrix_mul_mul_permMatrix_isLU`. -/
theorem gemPivotStage_permMatrix_mul_isLU_of_isPartialPivot {𝕜 : Type*} [NormedField 𝕜]
    {piv : Matrix (Fin N) (Fin N) 𝕜 → Fin N → Fin N} (hpiv : IsPartialPivot piv)
    (A : Matrix (Fin N) (Fin N) 𝕜) :
    IsLU ((gemPivotStage A piv N).2.permMatrix 𝕜 * A)
      (gemLower ((gemPivotStage A piv N).2.permMatrix 𝕜 * A)) (gemPivotStage A piv N).1 := by
  have hle : ∀ (M : Matrix (Fin N) (Fin N) 𝕜) k, k ≤ piv M k := fun M k => (hpiv M k).1
  rw [← gemStage_permMatrix_mul_card A piv hle]
  refine isLU_gemLower_gemStage' _ fun m hm i hi h0 => ?_
  rw [gemStage_permMatrix_mul_apply_self A piv hle hm] at h0
  rw [gemStage_permMatrix_mul_eq_submatrix_gemPivotStage A piv hle m, submatrix_apply]
  exact hpiv.apply_eq_zero h0 (Fin.le_def.2
    (le_gemPivotStage_snd_inv_mul_apply A piv hle hm.le hi.le))

/-- Gaussian elimination with the strategy `Matrix.partialPivotRow` factors every square matrix: for
$A \in \mathbb{K}^{N \times N}$ over a normed field, $P_{\sigma_N} A = LU$ with
$U = \hat A^{(N)}$ and $L$ the multiplier matrix of Gaussian elimination without pivoting on
$P_{\sigma_N} A$.

This is `Matrix.gemPivotStage_permMatrix_mul_isLU_of_isPartialPivot` for
`Matrix.partialPivotRow`. -/
theorem gemPivotStage_partialPivotRow_permMatrix_mul_isLU {𝕜 : Type*} [NormedField 𝕜]
    (A : Matrix (Fin N) (Fin N) 𝕜) :
    IsLU ((gemPivotStage A partialPivotRow N).2.permMatrix 𝕜 * A)
      (gemLower ((gemPivotStage A partialPivotRow N).2.permMatrix 𝕜 * A))
      (gemPivotStage A partialPivotRow N).1 :=
  gemPivotStage_permMatrix_mul_isLU_of_isPartialPivot isPartialPivot_partialPivotRow A

end ZeroPivot

/-! ### Gaussian elimination with complete pivoting, on `Fin N` -/

section FullPivotStages

variable {K : Type*} [Field K] {N : ℕ}

/-- **Gaussian elimination with complete pivoting**, for a strategy `piv` that chooses a pair of
indices. Let $A \in K^{N \times N}$. The triple $(\hat A^{(k)}, \sigma_k, \tau_k)$ =
`gemFullPivotStage A piv k` consists of the matrix after $k$ stages, the accumulated row
permutation and the accumulated column permutation. It is defined by
$(\hat A^{(0)}, \sigma_0, \tau_0) = (A, 1, 1)$ and the following rule. For $k < N$, let $(r, c)$
be the pair that `piv` chooses for $\hat A^{(k)}$ and $k$; interchange the rows $k$ and $r$ and
the columns $k$ and $c$ of $\hat A^{(k)}$, take the elimination step at $k$, and set
$\sigma_{k+1} = \sigma_k s$ and $\tau_{k+1} = \tau_k t$, with $s$ the transposition of $k$ and
$r$ and $t$ the transposition of $k$ and $c$. For $k \ge N$, nothing changes.

This is complete pivoting of [quarteroni2000numerical], §3.5. It is the two-sided analogue of
`Matrix.gemPivotStage`, which permutes the rows only. -/
noncomputable def gemFullPivotStage (A : Matrix (Fin N) (Fin N) K)
    (piv : Matrix (Fin N) (Fin N) K → Fin N → Fin N × Fin N) :
    ℕ → Matrix (Fin N) (Fin N) K × Equiv.Perm (Fin N) × Equiv.Perm (Fin N)
  | 0 => (A, 1, 1)
  | k + 1 =>
    if h : k < N then
      (elimStep ((gemFullPivotStage A piv k).1.submatrix
          (Equiv.swap ⟨k, h⟩ (piv (gemFullPivotStage A piv k).1 ⟨k, h⟩).1)
          (Equiv.swap ⟨k, h⟩ (piv (gemFullPivotStage A piv k).1 ⟨k, h⟩).2)) ⟨k, h⟩,
        (gemFullPivotStage A piv k).2.1 *
          Equiv.swap ⟨k, h⟩ (piv (gemFullPivotStage A piv k).1 ⟨k, h⟩).1,
        (gemFullPivotStage A piv k).2.2 *
          Equiv.swap ⟨k, h⟩ (piv (gemFullPivotStage A piv k).1 ⟨k, h⟩).2)
    else gemFullPivotStage A piv k

variable (A : Matrix (Fin N) (Fin N) K) (piv : Matrix (Fin N) (Fin N) K → Fin N → Fin N × Fin N)

/-- The row interchange of the stage $k < N$ of complete pivoting: the transposition of $k$ and the
pivot row chosen at stage $k$. -/
noncomputable def gemFullPivotRowSwap (k : ℕ) (h : k < N) : Equiv.Perm (Fin N) :=
  Equiv.swap ⟨k, h⟩ (piv (gemFullPivotStage A piv k).1 ⟨k, h⟩).1

/-- The column interchange of the stage $k < N$ of complete pivoting: the transposition of $k$ and
the pivot column chosen at stage $k$. -/
noncomputable def gemFullPivotColSwap (k : ℕ) (h : k < N) : Equiv.Perm (Fin N) :=
  Equiv.swap ⟨k, h⟩ (piv (gemFullPivotStage A piv k).1 ⟨k, h⟩).2

/-- $(\hat A^{(0)}, \sigma_0, \tau_0) = (A, 1, 1)$. -/
@[simp]
theorem gemFullPivotStage_zero : gemFullPivotStage A piv 0 = (A, 1, 1) := rfl

/-- For $k < N$, the stage $k + 1$ of complete pivoting interchanges, eliminates, and records both
interchanges: $\hat A^{(k+1)}$ is the elimination step at $k$ of $\hat A^{(k)}$ with its rows
permuted by the row interchange $s$ and its columns permuted by the column interchange $t$, and
$\sigma_{k+1} = \sigma_k s$, $\tau_{k+1} = \tau_k t$. -/
theorem gemFullPivotStage_succ_of_lt {k : ℕ} (h : k < N) :
    gemFullPivotStage A piv (k + 1) =
      (elimStep ((gemFullPivotStage A piv k).1.submatrix (gemFullPivotRowSwap A piv k h)
          (gemFullPivotColSwap A piv k h)) ⟨k, h⟩,
        (gemFullPivotStage A piv k).2.1 * gemFullPivotRowSwap A piv k h,
        (gemFullPivotStage A piv k).2.2 * gemFullPivotColSwap A piv k h) := by
  simp only [gemFullPivotStage, h, dite_true, gemFullPivotRowSwap, gemFullPivotColSwap]

/-- For $k \ge N$, the stages of complete pivoting do not change: stage $k + 1$ equals stage $k$. -/
theorem gemFullPivotStage_succ_of_le {k : ℕ} (h : N ≤ k) :
    gemFullPivotStage A piv (k + 1) = gemFullPivotStage A piv k := by
  simp only [gemFullPivotStage, not_lt.2 h, dite_false]

omit [Field K] in
/-- Let $(\sigma_k)_{k \in \mathbb{N}}$ be permutations of $\{0, \dots, N - 1\}$ with
$\sigma_{k+1} = \sigma_k \pi_k$ for permutations $\pi_k$ that fix every index $i < k$. Then for
$m \le m'$, the permutation $\sigma_m^{-1} \sigma_{m'}$ fixes every index $i < m$.

Both the row and the column permutations of `Matrix.gemFullPivotStage` have this form. -/
theorem perm_inv_mul_apply_of_step {σ : ℕ → Equiv.Perm (Fin N)}
    (hstep : ∀ k, ∃ τ : Equiv.Perm (Fin N),
      σ (k + 1) = σ k * τ ∧ ∀ i : Fin N, (i : ℕ) < k → τ i = i)
    {m m' : ℕ} (hmm' : m ≤ m') {i : Fin N} (hi : (i : ℕ) < m) :
    ((σ m)⁻¹ * σ m') i = i := by
  induction m', hmm' using Nat.le_induction with
  | base => simp
  | succ m' hm ih =>
    obtain ⟨τ, hτ, hfix⟩ := hstep m'
    rw [hτ, ← mul_assoc, Equiv.Perm.mul_apply, hfix i (hi.trans_le hm), ih]

omit [Field K] in
/-- A permutation of $\{0, \dots, N - 1\}$ that fixes every index $i < m$ maps every index $i \ge m$
to an index $\ge m$. -/
theorem le_apply_of_forall_lt_apply_eq {ρ : Equiv.Perm (Fin N)} {m : ℕ}
    (h : ∀ i : Fin N, (i : ℕ) < m → ρ i = i) {i : Fin N} (hi : m ≤ (i : ℕ)) : m ≤ (ρ i : ℕ) := by
  by_contra hcon
  have h1 := h _ (not_le.1 hcon)
  rw [ρ.injective.eq_iff] at h1
  rw [h1] at hcon
  exact hcon hi

/-- The submatrix of $M$ along products of permutations is an iterated submatrix:
`M.submatrix (s * t) (s' * t')` is `(M.submatrix s s').submatrix t t'`. -/
theorem submatrix_perm_mul {m α : Type*} (M : Matrix m m α) (s t s' t' : Equiv.Perm m) :
    M.submatrix (s * t) (s' * t') = (M.submatrix s s').submatrix t t' := rfl

/-- Let $\sigma$ be a permutation with $\sigma(i) = i$ for every $i \le p$, and let $\rho$ be a
permutation with $\rho(p) = p$. Then one elimination step at $p$ commutes with the permutation
of the rows by $\sigma$ and of the columns by $\rho$: the step of the matrix with the entries
$m_{\sigma(i) \rho(j)}$ is the matrix with the entries $m'_{\sigma(i) \rho(j)}$, where $M'$ is
the step of $M$ at $p$. -/
theorem elimStep_submatrix_submatrix_of_forall_le {m : Type*} [LinearOrder m] [Fintype m]
    (M : Matrix m m K) {p : m} {σ ρ : Equiv.Perm m} (hσ : ∀ i, i ≤ p → σ i = i) (hρ : ρ p = p) :
    elimStep (M.submatrix σ ρ) p = (elimStep M p).submatrix σ ρ := by
  have h1 : M.submatrix (σ : m → m) (ρ : m → m) = (M.submatrix id ρ).submatrix σ id := by
    rw [submatrix_submatrix]
    rfl
  rw [h1, elimStep_submatrix_of_forall_le _ hσ, elimStep_submatrix_id_of_apply_self _ hρ,
    submatrix_submatrix]
  rfl

/-- If the strategy always chooses a row at or below the current index, then the row interchange of
stage $k$ fixes every index $i < k$. -/
theorem gemFullPivotRowSwap_apply_of_lt (hrow : ∀ M k, k ≤ (piv M k).1) {k : ℕ} (h : k < N)
    {i : Fin N} (hi : (i : ℕ) < k) : gemFullPivotRowSwap A piv k h i = i := by
  refine Equiv.swap_apply_of_ne_of_ne (fun hik => ?_) fun hir => ?_
  · rw [hik] at hi
    exact lt_irrefl _ hi
  · have := hrow (gemFullPivotStage A piv k).1 ⟨k, h⟩
    rw [← hir, Fin.le_def] at this
    exact absurd (this.trans_lt hi) (lt_irrefl _)

/-- If the strategy always chooses a column at or after the current index, then the column
interchange of stage $k$ fixes every index $i < k$. -/
theorem gemFullPivotColSwap_apply_of_lt (hcol : ∀ M k, k ≤ (piv M k).2) {k : ℕ} (h : k < N)
    {i : Fin N} (hi : (i : ℕ) < k) : gemFullPivotColSwap A piv k h i = i := by
  refine Equiv.swap_apply_of_ne_of_ne (fun hik => ?_) fun hir => ?_
  · rw [hik] at hi
    exact lt_irrefl _ hi
  · have := hcol (gemFullPivotStage A piv k).1 ⟨k, h⟩
    rw [← hir, Fin.le_def] at this
    exact absurd (this.trans_lt hi) (lt_irrefl _)

/-- If the strategy always chooses a row at or below the current index, then for $m \le m'$ the
later row interchanges $\sigma_m^{-1} \sigma_{m'}$ fix every index $i < m$. -/
theorem gemFullPivotStage_rowPerm_inv_mul_apply (hrow : ∀ M k, k ≤ (piv M k).1) {m m' : ℕ}
    (hmm' : m ≤ m') {i : Fin N} (hi : (i : ℕ) < m) :
    ((gemFullPivotStage A piv m).2.1⁻¹ * (gemFullPivotStage A piv m').2.1) i = i := by
  refine perm_inv_mul_apply_of_step (σ := fun k => (gemFullPivotStage A piv k).2.1)
    (fun k => ?_) hmm' hi
  by_cases h : k < N
  · exact ⟨gemFullPivotRowSwap A piv k h, by rw [gemFullPivotStage_succ_of_lt A piv h],
      fun _ hj => gemFullPivotRowSwap_apply_of_lt A piv hrow h hj⟩
  · exact ⟨1, by rw [gemFullPivotStage_succ_of_le A piv (not_lt.1 h), mul_one], fun _ _ => rfl⟩

/-- If the strategy always chooses a column at or after the current index, then for $m \le m'$ the
later column interchanges $\tau_m^{-1} \tau_{m'}$ fix every index $i < m$. -/
theorem gemFullPivotStage_colPerm_inv_mul_apply (hcol : ∀ M k, k ≤ (piv M k).2) {m m' : ℕ}
    (hmm' : m ≤ m') {i : Fin N} (hi : (i : ℕ) < m) :
    ((gemFullPivotStage A piv m).2.2⁻¹ * (gemFullPivotStage A piv m').2.2) i = i := by
  refine perm_inv_mul_apply_of_step (σ := fun k => (gemFullPivotStage A piv k).2.2)
    (fun k => ?_) hmm' hi
  by_cases h : k < N
  · exact ⟨gemFullPivotColSwap A piv k h, by rw [gemFullPivotStage_succ_of_lt A piv h],
      fun _ hj => gemFullPivotColSwap_apply_of_lt A piv hcol h hj⟩
  · exact ⟨1, by rw [gemFullPivotStage_succ_of_le A piv (not_lt.1 h), mul_one], fun _ _ => rfl⟩

/-- **The stages of Gaussian elimination on $P A Q$ are the completely pivoted stages, with their
rows and columns permuted by the later interchanges.** Suppose that the strategy always chooses
a row and a column at or after the current index, and let $\sigma = \sigma_N$ and
$\tau = \tau_N$ be the final permutations. Let $B$ be the matrix with the entries
$b_{ij} = a_{\sigma(i) \tau(j)}$. Then for every $k$,
$$b^{(k)}_{ij} = \hat a^{(k)}_{\pi_k(i) \kappa_k(j)}, \qquad \pi_k = \sigma_k^{-1} \sigma, \quad
  \kappa_k = \tau_k^{-1} \tau.$$

This is the two-sided form of `Matrix.gemStage_submatrix_eq_submatrix_gemPivotStage`. -/
theorem gemStage_submatrix_eq_submatrix_gemFullPivotStage (hrow : ∀ M k, k ≤ (piv M k).1)
    (hcol : ∀ M k, k ≤ (piv M k).2) (k : ℕ) :
    gemStage (A.submatrix (gemFullPivotStage A piv N).2.1 (gemFullPivotStage A piv N).2.2) k =
      (gemFullPivotStage A piv k).1.submatrix
        ((gemFullPivotStage A piv k).2.1⁻¹ * (gemFullPivotStage A piv N).2.1)
        ((gemFullPivotStage A piv k).2.2⁻¹ * (gemFullPivotStage A piv N).2.2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases h : k < N
    · rw [gemStage_succ_of_lt _ h, ih, gemFullPivotStage_succ_of_lt A piv h]
      dsimp only
      have hk1 : (gemFullPivotStage A piv (k + 1)).2.1 =
          (gemFullPivotStage A piv k).2.1 * gemFullPivotRowSwap A piv k h := by
        rw [gemFullPivotStage_succ_of_lt A piv h]
      have hk2 : (gemFullPivotStage A piv (k + 1)).2.2 =
          (gemFullPivotStage A piv k).2.2 * gemFullPivotColSwap A piv k h := by
        rw [gemFullPivotStage_succ_of_lt A piv h]
      have hs : (gemFullPivotStage A piv k).2.1⁻¹ * (gemFullPivotStage A piv N).2.1 =
          gemFullPivotRowSwap A piv k h *
            ((gemFullPivotStage A piv (k + 1)).2.1⁻¹ * (gemFullPivotStage A piv N).2.1) := by
        rw [hk1, _root_.mul_inv_rev, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
      have hr : (gemFullPivotStage A piv k).2.2⁻¹ * (gemFullPivotStage A piv N).2.2 =
          gemFullPivotColSwap A piv k h *
            ((gemFullPivotStage A piv (k + 1)).2.2⁻¹ * (gemFullPivotStage A piv N).2.2) := by
        rw [hk2, _root_.mul_inv_rev, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
      rw [← hk1, ← hk2, hs, hr, submatrix_perm_mul]
      refine elimStep_submatrix_submatrix_of_forall_le _ (fun i hi => ?_) ?_
      · exact gemFullPivotStage_rowPerm_inv_mul_apply A piv hrow h
          (Nat.lt_succ_of_le (Fin.le_def.1 hi))
      · exact gemFullPivotStage_colPerm_inv_mul_apply A piv hcol h (Nat.lt_succ_self k)
    · rw [gemStage_succ_of_le _ (not_lt.1 h), ih, gemFullPivotStage_succ_of_le A piv (not_lt.1 h)]

/-- If the strategy always chooses a row at or below the current index, then for $k < N$ the later
row interchanges $\sigma_k^{-1} \sigma_N$ map $k$ to the pivot row chosen at stage $k$. -/
theorem gemFullPivotStage_rowPerm_inv_mul_apply_self (hrow : ∀ M k, k ≤ (piv M k).1) {k : ℕ}
    (h : k < N) :
    ((gemFullPivotStage A piv k).2.1⁻¹ * (gemFullPivotStage A piv N).2.1) ⟨k, h⟩ =
      (piv (gemFullPivotStage A piv k).1 ⟨k, h⟩).1 := by
  have hk1 : (gemFullPivotStage A piv (k + 1)).2.1 =
      (gemFullPivotStage A piv k).2.1 * gemFullPivotRowSwap A piv k h := by
    rw [gemFullPivotStage_succ_of_lt A piv h]
  have hs : (gemFullPivotStage A piv k).2.1⁻¹ * (gemFullPivotStage A piv N).2.1 =
      gemFullPivotRowSwap A piv k h *
        ((gemFullPivotStage A piv (k + 1)).2.1⁻¹ * (gemFullPivotStage A piv N).2.1) := by
    rw [hk1, _root_.mul_inv_rev, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hs, Equiv.Perm.mul_apply,
    gemFullPivotStage_rowPerm_inv_mul_apply A piv hrow h (Nat.lt_succ_self k),
    gemFullPivotRowSwap, Equiv.swap_apply_left]

/-- If the strategy always chooses a column at or after the current index, then for $k < N$ the
later column interchanges $\tau_k^{-1} \tau_N$ map $k$ to the pivot column chosen at stage $k$. -/
theorem gemFullPivotStage_colPerm_inv_mul_apply_self (hcol : ∀ M k, k ≤ (piv M k).2) {k : ℕ}
    (h : k < N) :
    ((gemFullPivotStage A piv k).2.2⁻¹ * (gemFullPivotStage A piv N).2.2) ⟨k, h⟩ =
      (piv (gemFullPivotStage A piv k).1 ⟨k, h⟩).2 := by
  have hk2 : (gemFullPivotStage A piv (k + 1)).2.2 =
      (gemFullPivotStage A piv k).2.2 * gemFullPivotColSwap A piv k h := by
    rw [gemFullPivotStage_succ_of_lt A piv h]
  have hr : (gemFullPivotStage A piv k).2.2⁻¹ * (gemFullPivotStage A piv N).2.2 =
      gemFullPivotColSwap A piv k h *
        ((gemFullPivotStage A piv (k + 1)).2.2⁻¹ * (gemFullPivotStage A piv N).2.2) := by
    rw [hk2, _root_.mul_inv_rev, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hr, Equiv.Perm.mul_apply,
    gemFullPivotStage_colPerm_inv_mul_apply A piv hcol h (Nat.lt_succ_self k),
    gemFullPivotColSwap, Equiv.swap_apply_left]

/-- If the strategy always chooses a row and a column at or after the current index, then the last
stage of Gaussian elimination without pivoting on the matrix $(a_{\sigma_N(i) \tau_N(j)})$ is
the last completely pivoted stage $\hat A^{(N)}$. -/
theorem gemStage_submatrix_gemFullPivotStage_card (hrow : ∀ M k, k ≤ (piv M k).1)
    (hcol : ∀ M k, k ≤ (piv M k).2) :
    gemStage (A.submatrix (gemFullPivotStage A piv N).2.1 (gemFullPivotStage A piv N).2.2) N =
      (gemFullPivotStage A piv N).1 := by
  rw [gemStage_submatrix_eq_submatrix_gemFullPivotStage A piv hrow hcol, inv_mul_cancel,
    inv_mul_cancel]
  rfl

/-- Suppose that the strategy always chooses a row and a column at or after the current index, and
let $B = (a_{\sigma_N(i) \tau_N(j)})$. Then for $k < N$, the pivot of stage $k$ of Gaussian
elimination without pivoting on $B$ is the entry chosen by the strategy:
$$b^{(k)}_{kk} = \hat a^{(k)}_{rc},$$
where $(r, c)$ is the pair that `piv` chooses for $\hat A^{(k)}$ and $k$. -/
theorem gemStage_submatrix_apply_self (hrow : ∀ M k, k ≤ (piv M k).1)
    (hcol : ∀ M k, k ≤ (piv M k).2) {k : ℕ} (h : k < N) :
    gemStage (A.submatrix (gemFullPivotStage A piv N).2.1 (gemFullPivotStage A piv N).2.2) k
        ⟨k, h⟩ ⟨k, h⟩ =
      (gemFullPivotStage A piv k).1 (piv (gemFullPivotStage A piv k).1 ⟨k, h⟩).1
        (piv (gemFullPivotStage A piv k).1 ⟨k, h⟩).2 := by
  rw [gemStage_submatrix_eq_submatrix_gemFullPivotStage A piv hrow hcol, submatrix_apply,
    gemFullPivotStage_rowPerm_inv_mul_apply_self A piv hrow h,
    gemFullPivotStage_colPerm_inv_mul_apply_self A piv hcol h]

/-- If the strategy always chooses a row at or below the current index, then for $m \le m'$ the
later row interchanges $\sigma_m^{-1} \sigma_{m'}$ map each index $i \ge m$ to an index $\ge m$. -/
theorem le_gemFullPivotStage_rowPerm_inv_mul_apply (hrow : ∀ M k, k ≤ (piv M k).1) {m m' : ℕ}
    (hmm' : m ≤ m') {i : Fin N} (hi : m ≤ (i : ℕ)) :
    m ≤ ((((gemFullPivotStage A piv m).2.1⁻¹ * (gemFullPivotStage A piv m').2.1) i : Fin N) : ℕ) :=
  le_apply_of_forall_lt_apply_eq
    (fun _ hj => gemFullPivotStage_rowPerm_inv_mul_apply A piv hrow hmm' hj) hi

/-- If the strategy always chooses a column at or after the current index, then for $m \le m'$ the
later column interchanges $\tau_m^{-1} \tau_{m'}$ map each index $i \ge m$ to an index $\ge m$. -/
theorem le_gemFullPivotStage_colPerm_inv_mul_apply (hcol : ∀ M k, k ≤ (piv M k).2) {m m' : ℕ}
    (hmm' : m ≤ m') {i : Fin N} (hi : m ≤ (i : ℕ)) :
    m ≤ ((((gemFullPivotStage A piv m).2.2⁻¹ * (gemFullPivotStage A piv m').2.2) i : Fin N) : ℕ) :=
  le_apply_of_forall_lt_apply_eq
    (fun _ hj => gemFullPivotStage_colPerm_inv_mul_apply A piv hcol hmm' hj) hi

/-- The permutation-matrix form of a two-sided permutation: for permutations $\sigma$ and $\rho$,
$$P_\sigma A P_{\rho^{-1}} = (a_{\sigma(i) \rho(j)})_{i, j}.$$
-/
theorem permMatrix_mul_mul_permMatrix (σ ρ : Equiv.Perm (Fin N)) :
    σ.permMatrix K * A * (ρ⁻¹).permMatrix K = A.submatrix σ ρ := by
  rw [Equiv.Perm.permMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, submatrix_submatrix, Function.id_comp, Function.comp_id,
    Equiv.Perm.inv_def, Equiv.symm_symm]

/-- Conjugation of an elementary matrix by a permutation that fixes its index. Let $\rho$ be a
permutation with $\rho(k) = k$, and let $v$ be a vector. Then
$$P_\rho (I - v e_k^T) P_\rho^T = I - (P_\rho v) e_k^T.$$

This is how the Gauss transformations of partial pivoting are carried past the later row
interchanges ([golub2013matrix], (3.4.5)). -/
theorem permMatrix_mul_one_sub_vecMulVec_single_mul_transpose {ρ : Equiv.Perm (Fin N)} {k : Fin N}
    (hk : ρ k = k) (τ : Fin N → K) :
    ρ.permMatrix K * (1 - vecMulVec τ (Pi.single k 1)) * (ρ.permMatrix K)ᵀ =
      1 - vecMulVec (ρ.permMatrix K *ᵥ τ) (Pi.single k 1) := by
  have hk' : ∀ j, ρ j = k ↔ j = k := fun j =>
    ⟨fun h => ρ.injective (h.trans hk.symm), fun h => h ▸ hk⟩
  rw [transpose_permMatrix, permMatrix_mul_mul_permMatrix, permMatrix_mulVec]
  ext i j
  simp only [submatrix_apply, Matrix.sub_apply, vecMulVec_apply, Pi.single_apply, Matrix.one_apply,
    EmbeddingLike.apply_eq_iff_eq, hk' j, Function.comp_apply]

end FullPivotStages

/-- Let $e \colon m \sqcup n \to p$ be a bijection, and let $\sigma$ and $\tau$ be permutations of
$m$ and $n$. The permutation matrix of the permutation $\sigma \sqcup \tau$, transported to $p$
along $e$, is the block diagonal matrix
$$\begin{bmatrix} P_\sigma & 0 \\ 0 & P_\tau \end{bmatrix}$$
reindexed along $e$.

This gives the permutation $\begin{bmatrix} I & 0 \\ 0 & P \end{bmatrix}$ of a pivoted block LU
factorization ([golub2013matrix], §3.6.1). -/
theorem permMatrix_permCongr_sumCongr {R m n p : Type*} [DecidableEq m] [DecidableEq n]
    [DecidableEq p] [Zero R] [One R] (e : m ⊕ n ≃ p) (σ : Equiv.Perm m) (τ : Equiv.Perm n) :
    (e.permCongr (Equiv.sumCongr σ τ)).permMatrix R =
      reindex e e (fromBlocks (σ.permMatrix R) 0 0 (τ.permMatrix R)) := by
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Equiv.permCongr_apply, Equiv.symm_apply_apply, Option.mem_def, Option.some.injEq,
    EmbeddingLike.apply_eq_iff_eq]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      PEquiv.toMatrix_apply]

/-! ### Nonsingular matrices have nonzero pivots under partial pivoting -/

section Nonsingular

/-- Let $R$ be a commutative ring, let $n$ be a finite linear order, let $M \in R^{n \times n}$, and
let $k \in n$. Suppose that $m_{ij} = 0$ whenever $j < k$ and $j < i$, and that $m_{ik} = 0$ for
every $i \ge k$. Then $\det M = 0$.

The matrix is block upper triangular for the split of the indices into $i \le k$ and $i > k$,
and its leading block is upper triangular with the zero diagonal entry $m_{kk}$. -/
theorem det_eq_zero_of_apply_eq_zero_of_lt {n : Type*} [LinearOrder n] [Fintype n] {R : Type*}
    [CommRing R] (M : Matrix n n R) (k : n) (h1 : ∀ i j, j < k → j < i → M i j = 0)
    (h2 : ∀ i, k ≤ i → M i k = 0) : M.det = 0 := by
  rw [twoBlockTriangular_det M (· ≤ k) fun i hi j hj => ?_]
  · refine mul_eq_zero_of_left ?_ _
    rw [det_of_isUpperTriangular (M := toSquareBlockProp M (· ≤ k)) fun i j hij =>
      h1 i.1 j.1 ((Subtype.coe_lt_coe.2 hij).trans_le i.2) hij]
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨k, le_rfl⟩ : {a // a ≤ k})) (h2 k le_rfl)
  · rcases hj.lt_or_eq with hjk | rfl
    · exact h1 i j hjk (hjk.trans (not_le.1 hi))
    · exact h2 i (not_le.1 hi).le

variable {N : ℕ} {𝕜 : Type*} [NormedField 𝕜]

/-- **A nonsingular matrix has nonzero pivots under partial pivoting.** Let $\mathbb{K}$ be a normed
field, let `piv` be a partial-pivoting strategy, and let $A \in \mathbb{K}^{N \times N}$ be
invertible. Then for every $k < N$, the pivot $\hat a^{(k)}_{r_k k}$ chosen at stage $k$ is
nonzero.

Otherwise the pivot column of some stage vanishes from the diagonal downwards. Then the
corresponding stage of Gaussian elimination on $P_{\sigma_N} A$ is singular
(`Matrix.det_eq_zero_of_apply_eq_zero_of_lt`), but every stage has the determinant
$\det (P_{\sigma_N} A) = \pm \det A$. -/
theorem gemPivotStage_pivot_ne_zero_of_isUnit {piv : Matrix (Fin N) (Fin N) 𝕜 → Fin N → Fin N}
    (hpiv' : IsPartialPivot piv) (A : Matrix (Fin N) (Fin N) 𝕜)
    (hA : IsUnit A) (k : ℕ) (hk : k < N) :
    (gemPivotStage A piv k).1 (piv (gemPivotStage A piv k).1 ⟨k, hk⟩) ⟨k, hk⟩ ≠ 0 := by
  have hpiv : ∀ (M : Matrix (Fin N) (Fin N) 𝕜) k, k ≤ piv M k := fun M k => (hpiv' M k).1
  set B := (gemPivotStage A piv N).2.permMatrix 𝕜 * A with hB
  have hdetB : B.det ≠ 0 := by
    rw [hB, det_mul, det_permutation]
    refine mul_ne_zero ?_ (isUnit_iff_ne_zero.1 ((isUnit_iff_isUnit_det A).1 hA))
    rcases Int.units_eq_one_or (Equiv.Perm.sign (gemPivotStage A piv N).2)
      with h | h <;> simp [h]
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro h0
  have hprev : ∀ m (hm : m < N), m < k → m + 1 < N → gemStage B m ⟨m, hm⟩ ⟨m, hm⟩ ≠ 0 :=
    fun m hm hmk _ => by
      rw [hB, gemStage_permMatrix_mul_apply_self A piv hpiv hm]
      exact ih m hmk hm
  have hz : ∀ i : Fin N, k ≤ (i : ℕ) → gemStage B k i ⟨k, hk⟩ = 0 := fun i hi => by
    rw [hB, gemStage_permMatrix_mul_eq_submatrix_gemPivotStage A piv hpiv k,
      submatrix_apply]
    exact hpiv'.apply_eq_zero h0 (Fin.le_def.2
      (le_gemPivotStage_snd_inv_mul_apply A piv hpiv hk.le hi))
  have hdet : (gemStage B k).det = 0 :=
    det_eq_zero_of_apply_eq_zero_of_lt _ ⟨k, hk⟩
      (fun i j hj hji => gemStage_apply_eq_zero_of_lt B hprev (Fin.lt_def.1 hj) hji)
      fun i hi => hz i (Fin.le_def.1 hi)
  have := gemLowerStage_mul_gemStage B k
  rw [← this, det_mul, (isUnitLowerTriangular_gemLowerStage B k).det_eq_one, one_mul, hdet]
    at hdetB
  exact hdetB rfl

/-- If $A \in \mathbb{K}^{N \times N}$ is invertible, then for every $k < N$ the pivot chosen by
`Matrix.partialPivotRow` at stage $k$ is nonzero.

This is `Matrix.gemPivotStage_pivot_ne_zero_of_isUnit` for `Matrix.partialPivotRow`. -/
theorem gemPivotStage_partialPivotRow_pivot_ne_zero_of_isUnit (A : Matrix (Fin N) (Fin N) 𝕜)
    (hA : IsUnit A) (k : ℕ) (hk : k < N) :
    (gemPivotStage A partialPivotRow k).1
      (partialPivotRow (gemPivotStage A partialPivotRow k).1 ⟨k, hk⟩) ⟨k, hk⟩ ≠ 0 :=
  gemPivotStage_pivot_ne_zero_of_isUnit isPartialPivot_partialPivotRow A hA k hk

/-- **The factors of $P_\sigma A = LU$ are the factors of Gaussian elimination without pivoting on
$P_\sigma A$.** Let $A, L, U \in K^{N \times N}$ and let $\sigma$ be a permutation. If
$P_\sigma A = LU$ is an LU factorization and every strict leading principal submatrix of
$P_\sigma A$ is nonsingular, then $L$ is the multiplier matrix `Matrix.gemLower` of $P_\sigma A$
and $U = (P_\sigma A)^{(N)}$.

This is the sentence before Program 9 in [quarteroni2000numerical], §3.5. The proof uses the
uniqueness of the LU factorization. -/
theorem IsLU.eq_of_permMatrix_mul {K : Type*} [Field K] {σ : Equiv.Perm (Fin N)}
    {A L U : Matrix (Fin N) (Fin N) K} (h : IsLU (σ.permMatrix K * A) L U)
    (hA : (σ.permMatrix K * A).HasUnitStrictLeadingPrincipalSubmatrices) :
    L = gemLower (σ.permMatrix K * A) ∧ U = gemStage (σ.permMatrix K * A) N :=
  h.unique (isLU_gemLower_gemStage _ ((gemStage_pivots_ne_zero_iff _).2 hA)) hA

end Nonsingular

/-! ### Rook and complete pivoting as factorizations -/

section RookStages

variable {N : ℕ} {𝕜 : Type*} [NormedField 𝕜]

/-- **Gaussian elimination with rook pivoting, and so with complete pivoting, factors
$P A Q = LU$.** Let $\mathbb{K}$ be a normed field, let `piv` be a rook-pivoting strategy, and
let $A \in \mathbb{K}^{N \times N}$. Let $\sigma = \sigma_N$ and $\tau = \tau_N$ be the
accumulated permutations, $P = P_\sigma$ and $Q = P_{\tau^{-1}}$. Then
$$P A Q = LU,$$
where $U = \hat A^{(N)}$ is the last pivoted stage and $L$ is the multiplier matrix of Gaussian
elimination without pivoting on $P A Q$. Moreover $|l_{ij}| \le 1$ and $|u_{ij}| \le |u_{ii}|$
for all $i, j$.

This is Algorithm 3.4.3 and §3.4.7 of [golub2013matrix], and the algorithmic counterpart of
`Matrix.exists_permMatrix_mul_mul_permMatrix_isLU`. No hypothesis on the pivots is needed. The
column condition of rook pivoting makes a zero pivot come with a zero column, and the row
condition gives $|u_{kj}| \le |u_{kk}|$, since the rows of $U$ are the pivot rows of the stages.
The source writes $P A Q^T = LU$ in Algorithm 3.4.3 and $P A Q = LU$ in §3.4.7; here
$Q = P_{\tau^{-1}}$. -/
theorem gemFullPivotStage_permMatrix_mul_mul_permMatrix_isLU (A : Matrix (Fin N) (Fin N) 𝕜)
    {piv : Matrix (Fin N) (Fin N) 𝕜 → Fin N → Fin N × Fin N} (hpiv : IsRookPivot piv) :
    IsLU ((gemFullPivotStage A piv N).2.1.permMatrix 𝕜 * A *
          ((gemFullPivotStage A piv N).2.2)⁻¹.permMatrix 𝕜)
        (gemLower ((gemFullPivotStage A piv N).2.1.permMatrix 𝕜 * A *
          ((gemFullPivotStage A piv N).2.2)⁻¹.permMatrix 𝕜))
        (gemFullPivotStage A piv N).1 ∧
      (∀ i j, ‖gemLower ((gemFullPivotStage A piv N).2.1.permMatrix 𝕜 * A *
          ((gemFullPivotStage A piv N).2.2)⁻¹.permMatrix 𝕜) i j‖ ≤ 1) ∧
      ∀ i j, ‖(gemFullPivotStage A piv N).1 i j‖ ≤ ‖(gemFullPivotStage A piv N).1 i i‖ := by
  have hrow : ∀ M k, k ≤ (piv M k).1 := fun M k => (hpiv M k).1
  have hcol : ∀ M k, k ≤ (piv M k).2 := fun M k => (hpiv M k).2.1
  rw [permMatrix_mul_mul_permMatrix]
  set B := A.submatrix (gemFullPivotStage A piv N).2.1 (gemFullPivotStage A piv N).2.2 with hB
  have hstage := gemStage_submatrix_eq_submatrix_gemFullPivotStage A piv hrow hcol
  have hle : ∀ (k : ℕ) (hk : k < N) (i : Fin N), k ≤ (i : ℕ) →
      ‖gemStage B k i ⟨k, hk⟩‖ ≤ ‖gemStage B k ⟨k, hk⟩ ⟨k, hk⟩‖ := by
    intro k hk i hi
    rw [gemStage_submatrix_apply_self A piv hrow hcol hk, hstage, submatrix_apply,
      gemFullPivotStage_colPerm_inv_mul_apply_self A piv hcol hk]
    exact (hpiv _ _).2.2.1 _
      (Fin.le_def.2 (le_gemFullPivotStage_rowPerm_inv_mul_apply A piv hrow hk.le hi))
  have hU : gemStage B N = (gemFullPivotStage A piv N).1 :=
    gemStage_submatrix_gemFullPivotStage_card A piv hrow hcol
  have hLU : IsLU B (gemLower B) (gemStage B N) :=
    isLU_gemLower_gemStage' B fun m hm i hi h0 => by
      have := hle m hm i hi.le
      rw [h0, norm_zero] at this
      exact norm_le_zero_iff.1 this
  refine ⟨hU ▸ hLU, fun i j => ?_, fun i j => ?_⟩
  · simp only [gemLower, of_apply]
    split_ifs with hij hij'
    · rw [norm_div]
      rcases eq_or_ne (gemStage B j j j) 0 with h0 | h0
      · rw [h0, norm_zero, div_zero]
        exact zero_le_one
      · rw [div_le_one (norm_pos_iff.2 h0)]
        exact hle j j.2 i (Fin.le_def.1 hij.le)
    · simp
    · simp
  · rw [← hU]
    rcases lt_or_ge j i with hji | hij
    · rw [hLU.isUpperTriangular hji, norm_zero]
      exact norm_nonneg _
    · obtain ⟨k, hk⟩ := i
      rw [gemStage_apply_of_le B (le_refl k) hk.le j, gemStage_apply_of_le B (le_refl k) hk.le,
        gemStage_submatrix_apply_self A piv hrow hcol hk, hstage, submatrix_apply,
        gemFullPivotStage_rowPerm_inv_mul_apply_self A piv hrow hk]
      exact (hpiv _ _).2.2.2 _
        (Fin.le_def.2 (le_gemFullPivotStage_colPerm_inv_mul_apply A piv hcol hk.le hij))

/-- **Complete pivoting reveals the rank.** Let $\mathbb{K}$ be a normed field, let `piv` be a
complete-pivoting strategy, and let $A \in \mathbb{K}^{N \times N}$ have rank $r$. Then the
trailing block of the stage $\hat A^{(r)}$ vanishes, $\hat a^{(r)}_{ij} = 0$ for all
$i, j \ge r$, and the pivots chosen at the stages $k < r$ are nonzero.

This is [golub2013matrix], §3.4.6. The stages of elimination on $P A Q$ have the rank of $A$.
While the pivots are nonzero, the leading block of a stage is upper triangular with a nonzero
diagonal, and a zero pivot makes the whole trailing block zero. So the first zero pivot is at
the stage $r$. -/
theorem gemFullPivotStage_trailing_eq_zero_of_rank (A : Matrix (Fin N) (Fin N) 𝕜)
    {piv : Matrix (Fin N) (Fin N) 𝕜 → Fin N → Fin N × Fin N} (hpiv : IsCompletePivot piv)
    {r : ℕ} (hr : A.rank = r) :
    (∀ i j : Fin N, r ≤ (i : ℕ) → r ≤ (j : ℕ) → (gemFullPivotStage A piv r).1 i j = 0) ∧
      ∀ (k : ℕ) (hk : k < N), k < r →
        (gemFullPivotStage A piv k).1 (piv (gemFullPivotStage A piv k).1 ⟨k, hk⟩).1
          (piv (gemFullPivotStage A piv k).1 ⟨k, hk⟩).2 ≠ 0 := by
  have hrow : ∀ M k, k ≤ (piv M k).1 := fun M k => (hpiv M k).1
  have hcol : ∀ M k, k ≤ (piv M k).2 := fun M k => (hpiv M k).2.1
  set B := A.submatrix (gemFullPivotStage A piv N).2.1 (gemFullPivotStage A piv N).2.2 with hB
  have hstage := gemStage_submatrix_eq_submatrix_gemFullPivotStage A piv hrow hcol
  -- the trailing block of a stage with a zero pivot vanishes
  have htrail : ∀ (k : ℕ) (hk : k < N),
      (gemFullPivotStage A piv k).1 (piv (gemFullPivotStage A piv k).1 ⟨k, hk⟩).1
        (piv (gemFullPivotStage A piv k).1 ⟨k, hk⟩).2 = 0 →
      ∀ i j : Fin N, k ≤ (i : ℕ) → k ≤ (j : ℕ) → (gemFullPivotStage A piv k).1 i j = 0 := by
    intro k hk h0 i j hi hj
    have := (hpiv (gemFullPivotStage A piv k).1 ⟨k, hk⟩).2.2 i j (Fin.le_def.2 hi)
      (Fin.le_def.2 hj)
    rw [h0, norm_zero] at this
    exact norm_le_zero_iff.1 this
  have hBtrail : ∀ (k : ℕ) (hk : k < N), gemStage B k ⟨k, hk⟩ ⟨k, hk⟩ = 0 →
      ∀ i j : Fin N, k ≤ (i : ℕ) → k ≤ (j : ℕ) → gemStage B k i j = 0 := by
    intro k hk h0 i j hi hj
    rw [gemStage_submatrix_apply_self A piv hrow hcol hk] at h0
    rw [hstage, submatrix_apply]
    exact htrail k hk h0 _ _ (le_gemFullPivotStage_rowPerm_inv_mul_apply A piv hrow hk.le hi)
      (le_gemFullPivotStage_colPerm_inv_mul_apply A piv hcol hk.le hj)
  have hz : ∀ (m : ℕ) (hm : m < N) (i : Fin N), m < (i : ℕ) →
      gemStage B m ⟨m, hm⟩ ⟨m, hm⟩ = 0 → gemStage B m i ⟨m, hm⟩ = 0 :=
    fun m hm i hi h0 => hBtrail m hm h0 i _ hi.le le_rfl
  have hshape : ∀ (k : ℕ) {i j : Fin N}, (j : ℕ) < k → j < i → gemStage B k i j = 0 :=
    fun k _ _ hjk hji => gemStage_apply_eq_zero_of_lt' B hz hjk hji
  -- every stage has the rank of `A`
  have hrank : ∀ k, (gemStage B k).rank = r := by
    intro k
    have h1 := gemLowerStage_mul_gemStage B k
    have hdet : IsUnit (gemLowerStage B k).det := by
      rw [(isUnitLowerTriangular_gemLowerStage B k).det_eq_one]
      exact isUnit_one
    rw [← rank_mul_eq_right_of_isUnit_det _ _ hdet, h1, hB, rank_submatrix, hr]
  -- the first zero pivot
  have hex : ∃ k, k = N ∨ ∃ hk : k < N, gemStage B k ⟨k, hk⟩ ⟨k, hk⟩ = 0 := ⟨N, Or.inl rfl⟩
  classical
  set k₀ := Nat.find hex with hk₀
  have hk₀spec := Nat.find_spec hex
  have hk₀min : ∀ m (hm : m < N), m < k₀ → gemStage B m ⟨m, hm⟩ ⟨m, hm⟩ ≠ 0 :=
    fun m hm hmk h0 => Nat.find_min hex hmk (Or.inr ⟨hm, h0⟩)
  have hk₀N : k₀ ≤ N := Nat.find_min' hex (Or.inl rfl)
  -- `k₀ ≤ r`: the leading block of order `k₀` of stage `k₀` is nonsingular
  have hle : k₀ ≤ r := by
    rw [← hrank k₀]
    refine card_le_rank_of_det_submatrix_ne_zero _ (r := Fin.castLE hk₀N)
      (c := Fin.castLE hk₀N) ?_
    rw [det_of_isUpperTriangular (M := (gemStage B k₀).submatrix (Fin.castLE hk₀N)
      (Fin.castLE hk₀N)) fun i j hij => hshape k₀ (by simp only [Fin.val_castLE]; omega)
        ((Fin.castLE_lt_castLE_iff _).2 hij)]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    simp only [submatrix_apply]
    have hi : ((Fin.castLE hk₀N i : Fin N) : ℕ) = i := Fin.val_castLE _ _
    rw [gemStage_apply_of_le B (le_refl ((Fin.castLE hk₀N i : Fin N) : ℕ))
      (by rw [hi]; exact i.2.le)]
    exact hk₀min _ (Fin.castLE hk₀N i).2 (by rw [hi]; exact i.2)
  -- `r ≤ k₀`: the rows from `k₀` on of stage `k₀` vanish
  have hge : r ≤ k₀ := by
    rcases hk₀spec with h | ⟨hk, h0⟩
    · rw [← hr]
      calc A.rank ≤ N := rank_le_height A
        _ = k₀ := h.symm
    · rw [← hrank k₀]
      refine (rank_le_card_of_support_subset _ (univ.filter fun i : Fin N => (i : ℕ) < k₀)
        fun i hi => ?_).trans ?_
      · by_contra hcon
        simp only [Finset.mem_coe, Finset.mem_filter, mem_univ, true_and, not_lt] at hcon
        refine hi (funext fun j => ?_)
        rcases lt_or_ge (j : ℕ) k₀ with hj | hj
        · exact hshape k₀ hj (Fin.lt_def.2 (by omega))
        · exact hBtrail k₀ hk h0 i j hcon hj
      · rw [Fin.card_filter_val_lt]
        exact min_le_right _ _
  have hk₀r : k₀ = r := le_antisymm hle hge
  refine ⟨fun i j hi hj => ?_, fun k hk hkr h0 => ?_⟩
  · rcases hk₀spec with h | ⟨hk, h0⟩
    · exact absurd i.2 (by omega)
    · rw [← hk₀r]
      rw [gemStage_submatrix_apply_self A piv hrow hcol hk] at h0
      exact htrail k₀ hk h0 i j (by omega) (by omega)
  · refine hk₀min k hk (by omega) ?_
    rw [gemStage_submatrix_apply_self A piv hrow hcol hk]
    exact h0

/-- **Partial pivoting on a tall block column.** Let $\mathbb{K}$ be a normed field, $r \le m$, and
$W \in \mathbb{K}^{m \times r}$. Then there are a permutation $\sigma$ of $\{0, \dots, m - 1\}$,
a unit lower trapezoidal $L \in \mathbb{K}^{m \times r}$ and an upper triangular
$U \in \mathbb{K}^{r \times r}$ with
$$P_\sigma W = LU$$
and $|l_{ij}| \le 1$ for all $i, j$.

This is equation (3.6.2) of [golub2013matrix]. The proof applies the square factorization
`Matrix.exists_permMatrix_mul_isLU` to $W$ padded with zero columns, and keeps the first $r$
columns of $L$ and the leading block of $U$. -/
theorem exists_permMatrix_mul_isRectLU {m r : ℕ} (W : Matrix (Fin m) (Fin r) 𝕜) (hrm : r ≤ m) :
    ∃ (σ : Equiv.Perm (Fin m)) (L : Matrix (Fin m) (Fin r) 𝕜) (U : Matrix (Fin r) (Fin r) 𝕜),
      IsRectLU (σ.permMatrix 𝕜 * W) L U ∧ ∀ i j, ‖L i j‖ ≤ 1 := by
  obtain ⟨σ, L, U, h, hL⟩ := exists_permMatrix_mul_isLU
    (of fun i (j : Fin m) => if hj : (j : ℕ) < r then W i ⟨j, hj⟩ else 0)
  refine ⟨σ, _, _, isRectLU_submatrix_of_mul_eq h.mul_eq le_rfl hrm hrm (fun i j => ?_)
    (fun i j hij => ?_) (fun i j hij => ?_) (fun i j hij => ?_) (fun i j s hs => ?_),
    fun i j => hL _ _⟩
  · rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.toMatrix_toPEquiv_mul]
    simp only [submatrix_apply, id, of_apply, Fin.val_castLE, Fin.is_lt, ↓reduceDIte]
    rfl
  · exact h.isUnitLowerTriangular.isLowerTriangular
      (OrderDual.toDual_lt_toDual.2 (Fin.lt_def.2 (by simpa using hij)))
  · change L i ⟨j, _⟩ = 1
    rw [show (⟨j, _⟩ : Fin m) = i from Fin.ext hij.symm]
    exact h.isUnitLowerTriangular.diag_eq_one i
  · exact h.isUpperTriangular (Fin.lt_def.2 (by simpa using hij))
  · exact mul_eq_zero_of_right _ (h.isUpperTriangular (show Fin.castLE hrm j < s from
      Fin.lt_def.2 (show (j : ℕ) < (s : ℕ) by omega)))

end RookStages

/-! ### The growth factor -/

section SupAbs

variable {m n : Type*} [Finite m] [Finite n]

/-- The **largest absolute value of an entry** of a real matrix:
$$\mu(A) = \max_{i, j} |a_{ij}|,$$
defined as a supremum, with the value $0$ for an empty matrix. -/
noncomputable def supAbs (A : Matrix m n ℝ) : ℝ := ⨆ p : m × n, |A p.1 p.2|

/-- Every entry is bounded by the largest one: $|a_{ij}| \le \mu(A)$. -/
theorem abs_apply_le_supAbs (A : Matrix m n ℝ) (i : m) (j : n) : |A i j| ≤ A.supAbs :=
  le_ciSup (f := fun p : m × n => |A p.1 p.2|) (Set.finite_range _).bddAbove (i, j)

/-- $\mu(A) \ge 0$. -/
theorem supAbs_nonneg (A : Matrix m n ℝ) : 0 ≤ A.supAbs := by
  rcases isEmpty_or_nonempty (m × n) with h | ⟨⟨i, j⟩⟩
  · simp [supAbs]
  · exact (abs_nonneg _).trans (abs_apply_le_supAbs A i j)

omit [Finite m] [Finite n] in
/-- $\mu(A)$ is the least nonnegative bound on the entries: if $c \ge 0$ and $|a_{ij}| \le c$ for
all $i, j$, then $\mu(A) \le c$. -/
theorem supAbs_le {A : Matrix m n ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, |A i j| ≤ c) :
    A.supAbs ≤ c := by
  rcases isEmpty_or_nonempty (m × n) with hmn | hmn
  · simp [supAbs, hc]
  · exact ciSup_le fun p => h p.1 p.2

/-- On a matrix with at least one row and one column, $\mu(A)$ is attained: $|a_{ij}| = \mu(A)$ for
some $i, j$. -/
theorem exists_abs_apply_eq_supAbs [Nonempty m] [Nonempty n] (A : Matrix m n ℝ) :
    ∃ i j, |A i j| = A.supAbs := by
  obtain ⟨⟨i, j⟩, hij⟩ := Finite.exists_max fun p : m × n => |A p.1 p.2|
  exact ⟨i, j, le_antisymm (abs_apply_le_supAbs A i j) (ciSup_le fun p => hij p)⟩

/-- $\mu(A) = 0$ if and only if $A = 0$. -/
theorem supAbs_eq_zero_iff {A : Matrix m n ℝ} : A.supAbs = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have := abs_apply_le_supAbs A i j
    rw [h] at this
    exact abs_nonpos_iff.1 this
  · rintro rfl
    exact le_antisymm (supAbs_le le_rfl fun i j => by simp) (supAbs_nonneg _)

omit [Finite m] [Finite n] in
/-- If the matrix has no rows, then $\mu(A) = 0$. -/
theorem supAbs_of_isEmpty [IsEmpty m] (A : Matrix m n ℝ) : A.supAbs = 0 := by
  simp [supAbs]

end SupAbs

section GrowthFactor

variable {N : ℕ}

/-- The **growth factor** of Gaussian elimination without pivoting on
$A \in \mathbb{R}^{N \times N}$:
$$\rho(A) = \frac{\max_{0 \le k < N} \max_{i, j} |a^{(k)}_{ij}|}{\mu(A)},$$
over the exact stages $A^{(0)} = A, \dots, A^{(N-1)}$, with the value $0$ if $A = 0$.

This is equation (3.66) of [quarteroni2000numerical] (see also [higham2002accuracy], §9.3),
where the stages are numbered from $1$ to $n$. The source defines the growth factor with the
computed stages; the exact one is the one that can be bounded ([higham2002accuracy], after
Theorem 9.5). For Gaussian elimination with partial pivoting the growth factor is
$\rho(P_\sigma A)$, because the pivoted stages are the stages of elimination without pivoting on
$P_\sigma A$ up to the order of the rows
(`Matrix.gemStage_permMatrix_mul_eq_submatrix_gemPivotStage`). -/
noncomputable def growthFactor (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  (⨆ p : Fin N × Fin N × Fin N, |gemStage A p.1 p.2.1 p.2.2|) / A.supAbs

variable (A : Matrix (Fin N) (Fin N) ℝ)

/-- Every stage of Gaussian elimination on the zero matrix is zero. -/
theorem gemStage_zero_matrix {K : Type*} [Field K] (k : ℕ) :
    gemStage (0 : Matrix (Fin N) (Fin N) K) k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases h : k < N
    · rw [gemStage_succ_of_lt _ h, ih]
      ext i j
      simp [elimStep_apply]
    · rw [gemStage_succ_of_le _ (not_lt.1 h), ih]

/-- $\rho(A) \ge 0$. -/
theorem growthFactor_nonneg : 0 ≤ growthFactor A := by
  unfold growthFactor
  refine div_nonneg ?_ (supAbs_nonneg A)
  rcases isEmpty_or_nonempty (Fin N × Fin N × Fin N) with h | ⟨⟨k, i, j⟩⟩
  · simp
  · exact (abs_nonneg _).trans (le_ciSup (f := fun p : Fin N × Fin N × Fin N =>
      |gemStage A p.1 p.2.1 p.2.2|) (Set.finite_range _).bddAbove (k, i, j))

/-- Every entry of every stage, the last stage $U$ included, is bounded by the growth factor times
the largest entry of $A$: for every $k$ and all $i, j$,
$$|a^{(k)}_{ij}| \le \rho(A) \, \mu(A).$$

This is the inequality $|u_{ij}| \le \rho_n \max |a_{ij}|$ of [quarteroni2000numerical], §3.10. -/
theorem abs_gemStage_le_growthFactor_mul_supAbs (k : ℕ) (i j : Fin N) :
    |gemStage A k i j| ≤ growthFactor A * A.supAbs := by
  rcases eq_or_ne A.supAbs 0 with h0 | h0
  · rw [supAbs_eq_zero_iff.1 h0, gemStage_zero_matrix]
    simp only [Matrix.zero_apply, abs_zero]
    exact mul_nonneg (growthFactor_nonneg _) (supAbs_nonneg _)
  have hbdd : BddAbove (Set.range fun p : Fin N × Fin N × Fin N =>
      |gemStage A p.1 p.2.1 p.2.2|) := (Set.finite_range _).bddAbove
  rw [growthFactor, div_mul_cancel₀ _ h0]
  rcases lt_or_ge k N with hk | hk
  · exact le_ciSup hbdd (⟨k, hk⟩, i, j)
  · rw [gemStage_apply_of_le A (le_refl (i : ℕ)) (i.2.le.trans hk)]
    exact le_ciSup hbdd (i, i, j)

/-- A uniform bound on the stages bounds the growth factor: if $c \ge 0$ and
$|a^{(k)}_{ij}| \le c \, \mu(A)$ for all $k < N$ and all $i, j$, then
$$\rho(A) \le c.$$
-/
theorem growthFactor_le_of_forall_abs_le {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ (k : ℕ) (i j : Fin N), k < N → |gemStage A k i j| ≤ c * A.supAbs) :
    growthFactor A ≤ c := by
  rcases eq_or_ne A.supAbs 0 with h0 | h0
  · rw [growthFactor, h0, div_zero]
    exact hc
  have hpos : 0 < A.supAbs := lt_of_le_of_ne (supAbs_nonneg A) (Ne.symm h0)
  have hN : Nonempty (Fin N) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact h0 (supAbs_of_isEmpty A)
  rw [growthFactor, div_le_iff₀ hpos]
  exact ciSup_le fun p => h p.1 p.2.1 p.2.2 p.1.2

/-- If $A \neq 0$, then $\rho(A) \ge 1$, because the first stage is $A$. -/
theorem one_le_growthFactor (hA : A ≠ 0) : 1 ≤ growthFactor A := by
  have h0 : A.supAbs ≠ 0 := fun h => hA (supAbs_eq_zero_iff.1 h)
  have hpos : 0 < A.supAbs := lt_of_le_of_ne (supAbs_nonneg A) (Ne.symm h0)
  have hN : Nonempty (Fin N) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact h0 (supAbs_of_isEmpty A)
  obtain ⟨i, j, hij⟩ := exists_abs_apply_eq_supAbs A
  rw [growthFactor, le_div_iff₀ hpos, one_mul, ← hij]
  have hN0 : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact hN.elim fun i => i.elim0)
  exact le_ciSup (f := fun p : Fin N × Fin N × Fin N => |gemStage A p.1 p.2.1 p.2.2|)
    (Set.finite_range _).bddAbove (⟨0, hN0⟩, i, j)

/-- Suppose that every multiplier of Gaussian elimination on $A$ has modulus at most one:
$|a^{(k)}_{ik} / a^{(k)}_{kk}| \le 1$ for all $k < N$ and $i > k$. Then for every $k$ and all
$i, j$, $|a^{(k)}_{ij}| \le 2^k \mu(A)$.

Each stage at most doubles the largest entry, since $|a^{(k+1)}_{ij}| \le |a^{(k)}_{ij}| +
|a^{(k)}_{ik} / a^{(k)}_{kk}| \, |a^{(k)}_{kj}|$.
-/
theorem abs_gemStage_le_two_pow_mul_supAbs
    (hmul : ∀ (k : ℕ) (hk : k < N) (i : Fin N), ⟨k, hk⟩ < i →
      |gemStage A k i ⟨k, hk⟩ / gemStage A k ⟨k, hk⟩ ⟨k, hk⟩| ≤ 1) (k : ℕ) (i j : Fin N) :
    |gemStage A k i j| ≤ 2 ^ k * A.supAbs := by
  induction k generalizing i j with
  | zero => simpa using abs_apply_le_supAbs A i j
  | succ k ih =>
    have hS : 0 ≤ A.supAbs := supAbs_nonneg A
    have h2 : (2 : ℝ) ^ k * A.supAbs ≤ 2 ^ (k + 1) * A.supAbs := by
      rw [pow_succ]
      nlinarith [pow_pos (two_pos (α := ℝ)) k]
    by_cases hk : k < N
    · rw [gemStage_succ_of_lt A hk, elimStep_apply]
      split_ifs with hki
      · have hm := hmul k hk i hki
        rw [← div_eq_mul_inv]
        calc |gemStage A k i j - gemStage A k i ⟨k, hk⟩ / gemStage A k ⟨k, hk⟩ ⟨k, hk⟩ *
              gemStage A k ⟨k, hk⟩ j|
            ≤ |gemStage A k i j| + |gemStage A k i ⟨k, hk⟩ / gemStage A k ⟨k, hk⟩ ⟨k, hk⟩| *
              |gemStage A k ⟨k, hk⟩ j| := by
              rw [← abs_mul]
              exact abs_sub _ _
          _ ≤ 2 ^ k * A.supAbs + 1 * (2 ^ k * A.supAbs) := by
              gcongr
              · exact ih i j
              · exact ih _ j
          _ = 2 ^ (k + 1) * A.supAbs := by ring
      · rw [sub_zero]
        exact (ih i j).trans h2
    · rw [gemStage_succ_of_le A (not_lt.1 hk)]
      exact (ih i j).trans h2

/-- **The growth factor is at most $2^{N-1}$ when the multipliers are bounded by one.** Let
$A \in \mathbb{R}^{N \times N}$, and suppose that $|a^{(k)}_{ik} / a^{(k)}_{kk}| \le 1$ for all
$k < N$ and $i > k$. Then
$$\rho(A) \le 2^{N-1}.$$

This is the statement "the growth factor can be bounded by $2^{n-1}$" of
[quarteroni2000numerical], §3.10. Each stage at most doubles the largest entry. With
`Matrix.gemPivotStage_partialPivotRow_norm_gemLower_le_one` this gives the bound for partial
pivoting (`Matrix.growthFactor_le_two_pow_of_partialPivotRow`). -/
theorem growthFactor_le_two_pow
    (hmul : ∀ (k : ℕ) (hk : k < N) (i : Fin N), ⟨k, hk⟩ < i →
      |gemStage A k i ⟨k, hk⟩ / gemStage A k ⟨k, hk⟩ ⟨k, hk⟩| ≤ 1) :
    growthFactor A ≤ 2 ^ (N - 1) := by
  refine growthFactor_le_of_forall_abs_le A (by positivity) fun k i j hk => ?_
  refine (abs_gemStage_le_two_pow_mul_supAbs A hmul k i j).trans ?_
  refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (by omega)) (supAbs_nonneg A)

/-- **The growth factor of partial pivoting is at most $2^{N-1}$.** For every
$A \in \mathbb{R}^{N \times N}$, with $\sigma_N$ the permutation of Gaussian elimination with
the strategy `Matrix.partialPivotRow`,
$$\rho(P_{\sigma_N} A) \le 2^{N-1}.$$

This is [quarteroni2000numerical], §3.10, and [higham2002accuracy], §9.3. The multipliers of
$P_{\sigma_N} A = LU$ have modulus at most one. -/
theorem growthFactor_le_two_pow_of_partialPivotRow :
    growthFactor ((gemPivotStage A partialPivotRow N).2.permMatrix ℝ * A) ≤ 2 ^ (N - 1) := by
  refine growthFactor_le_two_pow _ fun k hk i hki => ?_
  have := gemPivotStage_partialPivotRow_norm_gemLower_le_one A i ⟨k, hk⟩
  rwa [Real.norm_eq_abs, gemLower, of_apply, ite_eq_left hki] at this

end GrowthFactor

/-! ### Symmetric positive definite matrices: no growth -/

section PosDef

variable {N : ℕ}

/-- A real matrix $M \in \mathbb{R}^{N \times N}$ is **positive definite from $k$** if its trailing
block on the indices $i \ge k$ is symmetric positive definite: $m_{ij} = m_{ji}$ for all
$i, j \ge k$, and
$$y^T M y > 0$$
for every nonzero $y$ with $y_i = 0$ for all $i < k$.

The condition is stated with vectors supported on the indices $i \ge k$, so no reindexing is
needed. It is the invariant of the stages of Gaussian elimination on a positive definite matrix
([higham2002accuracy], §10.1.1). -/
def IsPosDefFrom (M : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) : Prop :=
  (∀ i j : Fin N, k ≤ (i : ℕ) → k ≤ (j : ℕ) → M i j = M j i) ∧
    ∀ y : Fin N → ℝ, (∀ i : Fin N, (i : ℕ) < k → y i = 0) → y ≠ 0 → 0 < y ⬝ᵥ M *ᵥ y

/-- A positive definite matrix is positive definite from $0$. -/
theorem PosDef.isPosDefFrom_zero {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef) :
    IsPosDefFrom A 0 :=
  ⟨fun i j _ _ => by simpa using (hA.isHermitian.apply i j).symm,
    fun y _ hy => by simpa using hA.dotProduct_mulVec_pos hy⟩

/-- If $M$ is positive definite from $k$ and $k \le k'$, then $M$ is positive definite from $k'$. -/
theorem IsPosDefFrom.mono {M : Matrix (Fin N) (Fin N) ℝ} {k k' : ℕ} (h : IsPosDefFrom M k)
    (hkk' : k ≤ k') : IsPosDefFrom M k' :=
  ⟨fun i j hi hj => h.1 i j (hkk'.trans hi) (hkk'.trans hj),
    fun y hy hy0 => h.2 y (fun i hi => hy i (hi.trans_le hkk')) hy0⟩

/-- The quadratic form at $y = a e_i + b e_j$:
$$y^T M y = a m_{ii} a + a m_{ij} b + (b m_{ji} a + b m_{jj} b).$$
-/
theorem dotProduct_mulVec_single_add_single (M : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N)
    (a b : ℝ) :
    (Pi.single i a + Pi.single j b) ⬝ᵥ M *ᵥ (Pi.single i a + Pi.single j b) =
      a * M i i * a + a * M i j * b + (b * M j i * a + b * M j j * b) := by
  simp only [mulVec_add, mulVec_single, add_dotProduct, dotProduct_add, single_dotProduct,
    Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring

/-- If $M$ is positive definite from $k$, then $m_{ii} > 0$ for every $i \ge k$. -/
theorem IsPosDefFrom.diag_pos {M : Matrix (Fin N) (Fin N) ℝ} {k : ℕ} (h : IsPosDefFrom M k)
    {i : Fin N} (hi : k ≤ (i : ℕ)) : 0 < M i i := by
  have := h.2 (Pi.single i 1) (fun l hl => Pi.single_eq_of_ne (fun hli => by
    rw [hli] at hl; exact absurd hi (not_le.2 hl)) 1) (by simp)
  simpa using this

/-- If $M$ is positive definite from $k$, then the entries of the trailing block are bounded by its
diagonal: $|m_{ij}| \le \max(m_{ii}, m_{jj})$ for all $i, j \ge k$, since
$m_{ii} \pm 2 m_{ij} + m_{jj} > 0$. -/
theorem IsPosDefFrom.abs_apply_le_max {M : Matrix (Fin N) (Fin N) ℝ} {k : ℕ}
    (h : IsPosDefFrom M k) {i j : Fin N} (hi : k ≤ (i : ℕ)) (hj : k ≤ (j : ℕ)) :
    |M i j| ≤ max (M i i) (M j j) := by
  rcases eq_or_ne i j with rfl | hij
  · rw [abs_of_pos (h.diag_pos hi)]
    exact le_max_left _ _
  have hsymm := h.1 i j hi hj
  have hsupp : ∀ b : ℝ, ∀ l : Fin N, (l : ℕ) < k →
      (Pi.single i 1 + Pi.single j b : Fin N → ℝ) l = 0 := by
    intro b l hl
    have hli : l ≠ i := fun e => by rw [e] at hl; exact absurd hi (not_le.2 hl)
    have hlj : l ≠ j := fun e => by rw [e] at hl; exact absurd hj (not_le.2 hl)
    simp [Pi.single_eq_of_ne hli, Pi.single_eq_of_ne hlj]
  have hne : ∀ b : ℝ, Pi.single i 1 + Pi.single j b ≠ (0 : Fin N → ℝ) := fun b h0 => by
    have := congrFun h0 i
    rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.zero_apply] at this
    linarith
  have h1 := h.2 _ (hsupp 1) (hne 1)
  have h2 := h.2 _ (hsupp (-1)) (hne (-1))
  rw [dotProduct_mulVec_single_add_single] at h1 h2
  rw [abs_le]
  constructor
  · nlinarith [le_max_left (M i i) (M j j), le_max_right (M i i) (M j j)]
  · nlinarith [le_max_left (M i i) (M j j), le_max_right (M i i) (M j j)]

/-- Let $M$ be positive definite from $k$, with $k < N$, and let $y$ satisfy $y_i = 0$ for all
$i \le k$. Then the quadratic form of the elimination step $M'$ at $k$ is the quadratic form of
$M$ at a corrected vector:
$$y^T M' y = z^T M z, \qquad z = y - \frac{(My)_k}{m_{kk}} e_k.$$

This is the Schur-complement identity for one step. -/
theorem dotProduct_elimStep_mulVec {M : Matrix (Fin N) (Fin N) ℝ} {k : ℕ} (h : IsPosDefFrom M k)
    (hk : k < N) {y : Fin N → ℝ} (hy : ∀ i : Fin N, (i : ℕ) < k + 1 → y i = 0) :
    y ⬝ᵥ elimStep M ⟨k, hk⟩ *ᵥ y =
      (y + Pi.single ⟨k, hk⟩ (-((M *ᵥ y) ⟨k, hk⟩ / M ⟨k, hk⟩ ⟨k, hk⟩))) ⬝ᵥ
        M *ᵥ (y + Pi.single ⟨k, hk⟩ (-((M *ᵥ y) ⟨k, hk⟩ / M ⟨k, hk⟩ ⟨k, hk⟩))) := by
  set p : Fin N := ⟨k, hk⟩ with hp
  have hpp : M p p ≠ 0 := (h.diag_pos le_rfl).ne'
  set s := (M *ᵥ y) p with hs
  set c := -(s / M p p) with hc
  -- the column sum against `y` is `s`, by symmetry of the trailing block
  have hcol : ∑ i, y i * M i p = s := by
    rw [hs, mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_ne (y i) 0 with h0 | h0
    · rw [h0, zero_mul, mul_zero]
    · have hi : k ≤ (i : ℕ) := le_of_not_gt fun hlt => h0 (hy i (hlt.trans (Nat.lt_succ_self k)))
      rw [h.1 i p hi le_rfl, mul_comm]
  -- the left-hand side
  have hL : y ⬝ᵥ elimStep M p *ᵥ y = y ⬝ᵥ M *ᵥ y - s * (M p p)⁻¹ * s := by
    rw [elimStep, sub_mulVec, dotProduct_sub, ← mulVec_mulVec]
    congr 1
    have hterm : ∀ i, y i * (elimMultipliers M p *ᵥ (M *ᵥ y)) i =
        y i * M i p * (M p p)⁻¹ * s := by
      intro i
      rw [mulVec, dotProduct, Finset.sum_eq_single p (fun j _ hj => by simp [hj]) (by simp)]
      simp only [elimMultipliers_apply, and_true, ← hs]
      split_ifs with hpi
      · ring
      · rw [hy i (Nat.lt_succ_of_le (Fin.le_def.1 (not_lt.1 hpi)))]
        ring
    rw [dotProduct]
    simp_rw [hterm]
    rw [← Finset.sum_mul, ← Finset.sum_mul, hcol]
  -- the right-hand side
  have hR : (y + Pi.single p c) ⬝ᵥ M *ᵥ (y + Pi.single p c) =
      y ⬝ᵥ M *ᵥ y + c * s + c * s + c * (M p p * c) := by
    simp only [mulVec_add, mulVec_single, add_dotProduct, dotProduct_add, single_dotProduct]
    have h1 : y ⬝ᵥ (MulOpposite.op c • M.col p) = c * s := by
      rw [← hcol, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring
    rw [h1]
    simp only [Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, ← hs]
    ring
  rw [hL, hR, hc]
  field_simp
  ring

/-- If $M$ is positive definite from $k$ and $k < N$, then the elimination step of $M$ at $k$ is
positive definite from $k + 1$: its trailing block is a Schur complement. -/
theorem IsPosDefFrom.elimStep {M : Matrix (Fin N) (Fin N) ℝ} {k : ℕ} (h : IsPosDefFrom M k)
    (hk : k < N) : IsPosDefFrom (elimStep M ⟨k, hk⟩) (k + 1) := by
  set p : Fin N := ⟨k, hk⟩ with hp
  refine ⟨fun i j hi hj => ?_, fun y hy hy0 => ?_⟩
  · have hi' : p < i := Fin.lt_def.2 (Nat.lt_of_succ_le hi)
    have hj' : p < j := Fin.lt_def.2 (Nat.lt_of_succ_le hj)
    rw [elimStep_apply_of_lt _ hi', elimStep_apply_of_lt _ hj',
      h.1 i j (Nat.le_of_succ_le hi) (Nat.le_of_succ_le hj), h.1 i p (Nat.le_of_succ_le hi) le_rfl,
      h.1 j p (Nat.le_of_succ_le hj) le_rfl]
    ring
  · rw [dotProduct_elimStep_mulVec h hk hy]
    refine h.2 _ (fun i hi => ?_) fun h0 => hy0 ?_
    · have hip : i ≠ p := fun e => by rw [e] at hi; exact lt_irrefl _ hi
      rw [Pi.add_apply, hy i (hi.trans (Nat.lt_succ_self k)), Pi.single_eq_of_ne hip, add_zero]
    · ext i
      have := congrFun h0 i
      rcases eq_or_ne i p with hip | hip
      · rw [hip]
        exact hy p (Nat.lt_succ_self k)
      · rwa [Pi.add_apply, Pi.single_eq_of_ne hip, add_zero] at this

/-- If $M$ is positive definite from $k$ and $k < N$, then the elimination step at $k$ does not
increase the diagonal entries $i \ge k + 1$: $m_{ii} - m_{ik}^2 / m_{kk} \le m_{ii}$. -/
theorem IsPosDefFrom.elimStep_apply_self_le {M : Matrix (Fin N) (Fin N) ℝ} {k : ℕ}
    (h : IsPosDefFrom M k) (hk : k < N) {i : Fin N} (hi : k + 1 ≤ (i : ℕ)) :
    Matrix.elimStep M ⟨k, hk⟩ i i ≤ M i i := by
  set p : Fin N := ⟨k, hk⟩ with hp
  rw [elimStep_apply_of_lt _ (Fin.lt_def.2 (Nat.lt_of_succ_le hi)),
    h.1 p i le_rfl (Nat.le_of_succ_le hi), mul_right_comm]
  have : 0 ≤ M i p * M i p * (M p p)⁻¹ :=
    mul_nonneg (mul_self_nonneg _) (inv_nonneg.2 (h.diag_pos le_rfl).le)
  linarith

variable {A : Matrix (Fin N) (Fin N) ℝ}

/-- If $A$ is positive definite, then every stage $A^{(k)}$ of Gaussian elimination is positive
definite from $k$.

The trailing blocks are Schur complements ([higham2002accuracy], §10.1.1). -/
theorem PosDef.isPosDefFrom_gemStage (hA : A.PosDef) (k : ℕ) :
    IsPosDefFrom (gemStage A k) k := by
  induction k with
  | zero => exact hA.isPosDefFrom_zero
  | succ k ih =>
    by_cases hk : k < N
    · rw [gemStage_succ_of_lt A hk]
      exact ih.elimStep hk
    · rw [gemStage_succ_of_le A (not_lt.1 hk)]
      exact ih.mono (Nat.le_succ k)

/-- If $A$ is positive definite, then every pivot of Gaussian elimination is positive:
$a^{(k)}_{kk} > 0$ for $k < N$. -/
theorem PosDef.gemStage_pivot_pos (hA : A.PosDef) {k : ℕ} (hk : k < N) :
    0 < gemStage A k ⟨k, hk⟩ ⟨k, hk⟩ :=
  (hA.isPosDefFrom_gemStage k).diag_pos le_rfl

/-- If $A$ is positive definite, then the diagonal entries of the stages never exceed those of $A$:
$a^{(k)}_{ii} \le a_{ii}$ for $i \ge k$. -/
theorem PosDef.gemStage_apply_self_le (hA : A.PosDef) (k : ℕ) {i : Fin N} (hi : k ≤ (i : ℕ)) :
    gemStage A k i i ≤ A i i := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    by_cases hk : k < N
    · rw [gemStage_succ_of_lt A hk]
      exact ((hA.isPosDefFrom_gemStage k).elimStep_apply_self_le hk hi).trans
        (ih (Nat.le_of_succ_le hi))
    · rw [gemStage_succ_of_le A (not_lt.1 hk)]
      exact ih (Nat.le_of_succ_le hi)

/-- If $A$ is positive definite, then $|a^{(k)}_{ij}| \le \mu(A)$ for every $k$, every row $i \ge k$
and every column $j$. -/
theorem PosDef.abs_gemStage_le_supAbs_of_le (hA : A.PosDef) {k : ℕ} {i : Fin N}
    (hki : k ≤ (i : ℕ)) (j : Fin N) : |gemStage A k i j| ≤ A.supAbs := by
  rcases le_or_gt k j with hkj | hjk
  · calc |gemStage A k i j|
        ≤ max (gemStage A k i i) (gemStage A k j j) :=
          (hA.isPosDefFrom_gemStage k).abs_apply_le_max hki hkj
      _ ≤ max (A i i) (A j j) :=
          max_le_max (hA.gemStage_apply_self_le k hki) (hA.gemStage_apply_self_le k hkj)
      _ ≤ A.supAbs :=
          max_le ((le_abs_self _).trans (abs_apply_le_supAbs A i i))
            ((le_abs_self _).trans (abs_apply_le_supAbs A j j))
  · rw [gemStage_apply_eq_zero_of_lt A (fun m hm _ _ => (hA.gemStage_pivot_pos hm).ne') hjk
      (Fin.lt_def.2 (hjk.trans_le hki)), abs_zero]
    exact supAbs_nonneg A

/-- If $A$ is positive definite, then $|a^{(k)}_{ij}| \le \mu(A)$ for every $k$ and all $i, j$. -/
theorem PosDef.abs_gemStage_le_supAbs (hA : A.PosDef) (k : ℕ) (i j : Fin N) :
    |gemStage A k i j| ≤ A.supAbs := by
  rcases le_or_gt k i with hki | hik
  · exact hA.abs_gemStage_le_supAbs_of_le hki j
  · rw [gemStage_apply_of_le A (le_refl (i : ℕ)) hik.le]
    exact hA.abs_gemStage_le_supAbs_of_le le_rfl j

/-- **No growth on positive definite matrices.** If $A \in \mathbb{R}^{N \times N}$ is symmetric
positive definite, then the growth factor of Gaussian elimination without pivoting satisfies
$$\rho(A) \le 1.$$
-/
theorem growthFactor_le_one_of_posDef (hA : A.PosDef) : growthFactor A ≤ 1 :=
  growthFactor_le_of_forall_abs_le A zero_le_one fun k i j _ => by
    simpa using hA.abs_gemStage_le_supAbs k i j

/-- **The growth factor of a positive definite matrix is one.** If $A \in \mathbb{R}^{N \times N}$
is symmetric positive definite and $N \ge 1$, then the growth factor of Gaussian elimination
without pivoting is
$$\rho(A) = 1.$$

This is [quarteroni2000numerical], §3.10 (3), and [higham2002accuracy], §10.1.1. The trailing
block of every stage is again positive definite, so its entries are bounded by its diagonal, and
the diagonal entries decrease from stage to stage. The hypothesis $N \ge 1$ is necessary,
because the growth factor of the empty matrix is $0$. -/
theorem growthFactor_eq_one_of_posDef (hA : A.PosDef) (hN : 0 < N) : growthFactor A = 1 := by
  refine le_antisymm (growthFactor_le_one_of_posDef hA) (one_le_growthFactor A fun h0 => ?_)
  have := hA.diag_pos (i := ⟨0, hN⟩)
  rw [h0] at this
  simp at this

end PosDef

/-! ### Column diagonally dominant matrices: growth at most two -/

section ColDiagDominant

variable {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}

/-- If $A \in \mathbb{R}^{N \times N}$ is invertible and column diagonally dominant, then every
pivot of Gaussian elimination is nonzero: $a^{(k)}_{kk} \neq 0$ for $k < N$.

The LU factorization exists (`Matrix.exists_isLU_of_isColDiagDominant`), and
$\det A = \prod_i u_{ii}$. -/
theorem gemStage_pivot_ne_zero_of_isColDiagDominant (hu : IsUnit A) (hA : A.IsColDiagDominant)
    {k : ℕ} (hk : k < N) : gemStage A k ⟨k, hk⟩ ⟨k, hk⟩ ≠ 0 := by
  obtain ⟨L, U, hLU, -⟩ := exists_isLU_of_isColDiagDominant hu hA
  have hdet : A.det ≠ 0 := isUnit_iff_ne_zero.1 ((isUnit_iff_isUnit_det A).1 hu)
  have hA' : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k) := by
    intro k
    rw [isUnit_iff_isUnit_det, hLU.det_strictLeadingPrincipalSubmatrix, isUnit_iff_ne_zero]
    have hU := hdet
    rw [hLU.det_eq_prod_diag] at hU
    exact Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.1 hU i (mem_univ _)
  have hpiv := (gemStage_pivots_ne_zero_iff A).2 hA'
  have hdet' := hdet
  rw [(isLU_gemLower_gemStage A hpiv).det_eq_prod_diag] at hdet'
  have := Finset.prod_ne_zero_iff.1 hdet' ⟨k, hk⟩ (mem_univ _)
  rwa [gemStage_apply_of_le A (le_refl k) hk.le] at this

/-- The indices $i \ge k$ are the index $k$ together with the indices $i \ge k + 1$. -/
theorem filter_le_eq_insert_filter_succ_le {k : ℕ} (hk : k < N) :
    (univ.filter fun i : Fin N => k ≤ (i : ℕ)) =
      insert ⟨k, hk⟩ (univ.filter fun i : Fin N => k + 1 ≤ (i : ℕ)) := by
  ext i
  simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
  omega

/-- The indices $i \ge k$ other than $k$ are the indices $i \ge k + 1$. -/
theorem filter_le_erase_eq_filter_succ_le {k : ℕ} (hk : k < N) :
    (univ.filter fun i : Fin N => k ≤ (i : ℕ)).erase ⟨k, hk⟩ =
      univ.filter fun i : Fin N => k + 1 ≤ (i : ℕ) := by
  ext i
  simp only [mem_erase, mem_filter, mem_univ, true_and, ne_eq, Fin.ext_iff]
  omega

/-- **The invariant of Gaussian elimination on a column diagonally dominant matrix.** Let
$A \in \mathbb{R}^{N \times N}$ be invertible and column diagonally dominant. Then for every
stage $k$:

* the trailing block is column diagonally dominant: $\sum_{i \ge k, i \neq j} |a^{(k)}_{ij}| \le
  |a^{(k)}_{jj}|$ for every $j \ge k$;
* for every column $j$, the part of the column in the rows $i \ge k$ has at most the column sum
  of $A$: $\sum_{i \ge k} |a^{(k)}_{ij}| \le \sum_i |a_{ij}|$.

This is the invariant of the proof of Theorem 9.9 of [higham2002accuracy], after Wilkinson. The
dominance of the trailing block is the Schur-complement lemma
`Matrix.IsColDiagDominant.sum_norm_sub_le`, applied to the stage with its finished rows replaced
by zeros. -/
theorem gemStage_isColDiagDominant_invariant (hu : IsUnit A) (hA : A.IsColDiagDominant) (k : ℕ) :
    (∀ j : Fin N, k ≤ (j : ℕ) →
      ∑ i ∈ (univ.filter fun i : Fin N => k ≤ (i : ℕ)).erase j, |gemStage A k i j| ≤
        |gemStage A k j j|) ∧
    ∀ j : Fin N, ∑ i ∈ univ.filter (fun i : Fin N => k ≤ (i : ℕ)), |gemStage A k i j| ≤
      ∑ i, |A i j| := by
  induction k with
  | zero =>
    refine ⟨fun j _ => ?_, fun j => le_of_eq ?_⟩
    · have := hA j
      simpa [Real.norm_eq_abs] using this
    · simp
  | succ k ih =>
    by_cases hk : k < N
    swap
    · have hempty : (univ.filter fun i : Fin N => k + 1 ≤ (i : ℕ)) = ∅ := by
        ext i
        simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_le]
        exact i.2.trans_le (Nat.le_succ_of_le (not_lt.1 hk))
      refine ⟨fun j hj => absurd (hj.trans_lt j.2) (by omega), fun j => ?_⟩
      rw [hempty, Finset.sum_empty]
      exact Finset.sum_nonneg fun i _ => abs_nonneg _
    obtain ⟨ha, hb⟩ := ih
    set p : Fin N := ⟨k, hk⟩ with hp
    set M := gemStage A k with hM
    have hpp : M p p ≠ 0 := gemStage_pivot_ne_zero_of_isColDiagDominant hu hA hk
    have hstep : gemStage A (k + 1) = elimStep M p := gemStage_succ_of_lt A hk
    have hcolp : ∑ i ∈ univ.filter (fun i : Fin N => k + 1 ≤ (i : ℕ)), |M i p| ≤ |M p p| := by
      rw [← filter_le_erase_eq_filter_succ_le hk]
      exact ha p le_rfl
    have hlt : ∀ i : Fin N, k + 1 ≤ (i : ℕ) → p < i := fun i hi => Fin.lt_def.2 hi
    refine ⟨fun j hj => ?_, fun j => ?_⟩
    · -- column dominance of the trailing block, through the padded matrix `T`
      set T : Matrix (Fin N) (Fin N) ℝ := of fun i j => if k ≤ (i : ℕ) then M i j else 0 with hT
      have hTz : ∀ i j : Fin N, (i : ℕ) < k → T i j = 0 := fun i j hi => by
        simp [hT, not_le.2 hi]
      have hTe : ∀ i j : Fin N, k ≤ (i : ℕ) → T i j = M i j := fun i j hi => by
        simp [hT, hi]
      have hTdom : T.IsColDiagDominant := by
        intro j
        simp only [Real.norm_eq_abs]
        rcases le_or_gt k j with hkj | hjk
        · rw [hTe j j hkj, ← Finset.sum_filter_of_ne (p := fun i : Fin N => k ≤ (i : ℕ))
            (fun i _ hi => by
              by_contra hik
              exact hi (by rw [hTz i j (not_le.1 hik), abs_zero])),
            Finset.filter_erase]
          refine (Finset.sum_le_sum fun i hi => ?_).trans (ha j hkj)
          rw [hTe i j (mem_filter.1 (mem_erase.1 hi).2).2]
        · rw [hTz j j hjk, abs_zero]
          refine le_of_eq (Finset.sum_eq_zero fun i _ => ?_)
          by_cases hik : k ≤ (i : ℕ)
          · have h0 : M i j = 0 := gemStage_apply_eq_zero_of_lt A
              (fun m hm _ _ => gemStage_pivot_ne_zero_of_isColDiagDominant hu hA hm) hjk
              (Fin.lt_def.2 (hjk.trans_le hik))
            rw [hTe i j hik, h0, abs_zero]
          · rw [hTz i j (not_le.1 hik), abs_zero]
      have key := hTdom.sum_norm_sub_le (p := p) (j := j) (by rwa [hTe p p le_rfl])
        (hlt j hj).ne'
      simp only [Real.norm_eq_abs, hTe j j (Nat.le_of_succ_le hj), hTe j p (Nat.le_of_succ_le hj),
        hTe p p le_rfl, hTe p j le_rfl] at key
      rw [hstep, elimStep_apply_of_lt _ (hlt j hj)]
      refine le_trans (le_of_eq ?_) key
      rw [← Finset.sum_filter_of_ne (s := (univ.erase p).erase j)
        (p := fun i : Fin N => k ≤ (i : ℕ)) fun i _ hi => ?_]
      · have hset : ((univ.erase p).erase j).filter (fun i : Fin N => k ≤ (i : ℕ)) =
            (univ.filter fun i : Fin N => k + 1 ≤ (i : ℕ)).erase j := by
          ext i
          simp only [mem_filter, mem_erase, mem_univ, true_and, and_true]
          constructor
          · rintro ⟨⟨hij, hip⟩, hki⟩
            exact ⟨hij, Nat.lt_of_le_of_ne hki fun e => hip (Fin.ext e.symm)⟩
          · rintro ⟨hij, hki⟩
            exact ⟨⟨hij, fun e => by
              rw [e] at hki; exact absurd hki (by rw [hp]; exact Nat.not_succ_le_self k)⟩,
              Nat.le_of_succ_le hki⟩
        rw [hset]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' := (mem_filter.1 (mem_erase.1 hi).2).2
        rw [elimStep_apply_of_lt _ (hlt i hi'), hTe i j (Nat.le_of_succ_le hi'),
          hTe i p (Nat.le_of_succ_le hi')]
      · by_contra hik
        rw [hTz i j (not_le.1 hik), hTz i p (not_le.1 hik)] at hi
        simp at hi
    · -- the column sums of the trailing block do not increase
      have hb' := hb j
      rw [filter_le_eq_insert_filter_succ_le hk, Finset.sum_insert (by simp)] at hb'
      rw [hstep]
      refine le_trans ?_ hb'
      calc ∑ i ∈ univ.filter (fun i : Fin N => k + 1 ≤ (i : ℕ)), |elimStep M p i j|
          ≤ ∑ i ∈ univ.filter (fun i : Fin N => k + 1 ≤ (i : ℕ)),
              (|M i j| + |M i p| * |M p p|⁻¹ * |M p j|) := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [elimStep_apply_of_lt _ (hlt i (mem_filter.1 hi).2)]
            refine (abs_sub _ _).trans (le_of_eq ?_)
            rw [abs_mul, abs_mul, abs_inv]
        _ = ∑ i ∈ univ.filter (fun i : Fin N => k + 1 ≤ (i : ℕ)), |M i j| +
              (∑ i ∈ univ.filter (fun i : Fin N => k + 1 ≤ (i : ℕ)), |M i p|) * |M p p|⁻¹ *
                |M p j| := by
            rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
        _ ≤ ∑ i ∈ univ.filter (fun i : Fin N => k + 1 ≤ (i : ℕ)), |M i j| +
              |M p p| * |M p p|⁻¹ * |M p j| := by gcongr
        _ = |M p j| + ∑ i ∈ univ.filter (fun i : Fin N => k + 1 ≤ (i : ℕ)), |M i j| := by
            rw [mul_inv_cancel₀ (abs_ne_zero.2 hpp), one_mul, add_comm]

/-- If $A \in \mathbb{R}^{N \times N}$ is invertible and column diagonally dominant, then every
entry of every stage of Gaussian elimination is at most twice the largest entry of $A$:
$$|a^{(k)}_{ij}| \le 2 \mu(A).$$

The part of a column in the trailing rows is at most the column sum of $A$, which is at most
$2 |a_{jj}|$ by dominance. -/
theorem abs_gemStage_le_two_mul_supAbs_of_isColDiagDominant (hu : IsUnit A)
    (hA : A.IsColDiagDominant) (k : ℕ) (i j : Fin N) :
    |gemStage A k i j| ≤ 2 * A.supAbs := by
  have hcol : ∀ k, ∀ i : Fin N, k ≤ (i : ℕ) → |gemStage A k i j| ≤ 2 * A.supAbs := by
    intro k i hki
    have h1 : |gemStage A k i j| ≤ ∑ i' ∈ univ.filter (fun i : Fin N => k ≤ (i : ℕ)),
        |gemStage A k i' j| :=
      Finset.single_le_sum (f := fun i' => |gemStage A k i' j|) (fun _ _ => abs_nonneg _)
        (mem_filter.2 ⟨mem_univ _, hki⟩)
    have h2 := (gemStage_isColDiagDominant_invariant hu hA k).2 j
    have h3 : ∑ i', |A i' j| ≤ 2 * A.supAbs := by
      rw [← Finset.add_sum_erase _ _ (mem_univ j), two_mul]
      have := hA j
      simp only [Real.norm_eq_abs] at this
      exact add_le_add (abs_apply_le_supAbs A j j) (this.trans (abs_apply_le_supAbs A j j))
    exact h1.trans (h2.trans h3)
  rcases le_or_gt k i with hki | hik
  · exact hcol k i hki
  · rw [gemStage_apply_of_le A (le_refl (i : ℕ)) hik.le]
    exact hcol i i le_rfl

/-- **The growth factor of a column diagonally dominant matrix is at most two.** If
$A \in \mathbb{R}^{N \times N}$ is invertible and diagonally dominant by columns,
$\sum_{i \neq j} |a_{ij}| \le |a_{jj}|$ for every $j$, then the growth factor of Gaussian
elimination without pivoting satisfies
$$\rho(A) \le 2.$$

This is [quarteroni2000numerical], §3.10 (4), and Theorem 9.9 of [higham2002accuracy]
(Wilkinson). The source asks for strict dominance; weak dominance suffices. Partial pivoting
would make no interchange, because the multipliers are bounded by one
(`Matrix.exists_isLU_of_isColDiagDominant`). -/
theorem growthFactor_le_two_of_isColDiagDominant (hu : IsUnit A) (hA : A.IsColDiagDominant) :
    growthFactor A ≤ 2 :=
  growthFactor_le_of_forall_abs_le A zero_le_two fun k i j _ =>
    abs_gemStage_le_two_mul_supAbs_of_isColDiagDominant hu hA k i j

end ColDiagDominant

/-! ### Partial pivoting on Hessenberg and tridiagonal matrices -/

section Hessenberg

variable {N : ℕ}

/-- The largest entry does not change under a permutation of the rows: $\mu$ of the matrix
$(a_{\sigma(i) j})$ is $\mu(A)$. -/
theorem supAbs_submatrix_equiv {m : Type*} [Finite m] (A : Matrix m m ℝ) (σ : Equiv.Perm m) :
    (A.submatrix σ id).supAbs = A.supAbs := by
  refine le_antisymm (supAbs_le (supAbs_nonneg A) fun i j => abs_apply_le_supAbs A (σ i) j)
    (supAbs_le (supAbs_nonneg _) fun i j => ?_)
  have := abs_apply_le_supAbs (A.submatrix σ id) (σ.symm i) j
  simpa using this

/-- For real numbers $a$ and $b$ with $|a| \le |b|$, $|a / b| \le 1$. The case $b = 0$ is included,
since division by zero is $0$. -/
theorem abs_div_le_one_of_abs_le {a b : ℝ} (h : |a| ≤ |b|) : |a / b| ≤ 1 := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  · rw [abs_div, div_le_one (abs_pos.2 hb)]
    exact h

/-- Let $M \in \mathbb{K}^{N \times N}$, let $p$ be an index and $b \in \mathbb{N}$, and suppose
that $m_{ip} = 0$ for every $i > p + b$. Then the row chosen by `Matrix.partialPivotRow M p` is
at most $p + b$.

A pivot further down would be zero, so the whole column below $p$ would vanish, and the first
maximal row would be $p$ itself. -/
theorem partialPivotRow_le_add {𝕜 : Type*} [NormedField 𝕜] (M : Matrix (Fin N) (Fin N) 𝕜)
    (p : Fin N) (b : ℕ) (h : ∀ i : Fin N, (p : ℕ) + b < i → M i p = 0) :
    ((partialPivotRow M p : Fin N) : ℕ) ≤ (p : ℕ) + b := by
  by_contra hlt
  push Not at hlt
  have h0 : M (partialPivotRow M p) p = 0 := h _ hlt
  have hself := partialPivotRow_eq_self_of_forall_eq_zero M p fun r hr =>
    apply_eq_zero_of_partialPivotRow_eq_zero M p h0 hr
  rw [hself] at hlt
  omega

/-- Let $M \in \mathbb{K}^{N \times N}$ and let $p$ be an index with $m_{ip} = 0$ for every
$i > p + 1$. Then the row chosen by `Matrix.partialPivotRow M p` is $p$ or $p + 1$.

This is the case $b = 1$ of `Matrix.partialPivotRow_le_add`. -/
theorem partialPivotRow_le_succ {𝕜 : Type*} [NormedField 𝕜] (M : Matrix (Fin N) (Fin N) 𝕜)
    (p : Fin N) (h : ∀ i : Fin N, (p : ℕ) + 1 < i → M i p = 0) :
    ((partialPivotRow M p : Fin N) : ℕ) ≤ (p : ℕ) + 1 :=
  partialPivotRow_le_add M p 1 h

variable {A : Matrix (Fin N) (Fin N) ℝ}

/-- **The shape invariant of partial pivoting on an upper Hessenberg matrix.** Let
$A \in \mathbb{R}^{N \times N}$ be upper Hessenberg, and let $\hat A^{(k)}$ be the stages of
Gaussian elimination with the strategy `Matrix.partialPivotRow`. Then for every $k$:

* the rows below $k$ are the rows of $A$: $\hat a^{(k)}_{ij} = a_{ij}$ for $i > k$;
* the entries of the rows $i \le k$ satisfy $|\hat a^{(k)}_{ij}| \le (i + 1) \mu(A)$.

This is the invariant of the proof of Theorem 9.10 of [higham2002accuracy]. Each stage
interchanges at most the rows $k$ and $k + 1$, and adds to the row $k + 1$ a multiple of modulus
at most one of the pivot row. -/
theorem gemPivotStage_partialPivotRow_isUpperHessenberg_invariant (hA : A.IsUpperHessenberg)
    (k : ℕ) :
    (∀ i j : Fin N, k < (i : ℕ) → (gemPivotStage A partialPivotRow k).1 i j = A i j) ∧
      ∀ i j : Fin N, (i : ℕ) ≤ k →
        |(gemPivotStage A partialPivotRow k).1 i j| ≤ ((i : ℕ) + 1) * A.supAbs := by
  have hμ := supAbs_nonneg A
  induction k with
  | zero =>
    refine ⟨fun i j _ => rfl, fun i j hi => ?_⟩
    have : (i : ℕ) = 0 := by omega
    rw [gemPivotStage_zero]
    simp only [this, Nat.cast_zero, zero_add, one_mul]
    exact abs_apply_le_supAbs A i j
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    by_cases hk : k < N
    swap
    · rw [gemPivotStage_succ_of_le A _ (not_lt.1 hk)]
      exact ⟨fun i j hi => h1 i j (by omega), fun i j _ => h2 i j (by omega)⟩
    set p : Fin N := ⟨k, hk⟩ with hp
    have hpk : (p : ℕ) = k := rfl
    set M := (gemPivotStage A partialPivotRow k).1 with hM
    set r := partialPivotRow M p with hrdef
    have hM1 : (gemPivotStage A partialPivotRow (k + 1)).1 =
        elimStep (M.submatrix (Equiv.swap p r) id) p := by
      rw [gemPivotStage_succ_of_lt A partialPivotRow hk]
      rfl
    set M' := M.submatrix (Equiv.swap p r) id with hM'
    -- the rows more than one below `p` vanish in column `p`, so `r ∈ {k, k + 1}`
    have hcol : ∀ i : Fin N, (p : ℕ) + 1 < i → M i p = 0 := fun i hi => by
      rw [h1 i p (by omega)]
      exact hA i p ⟨⟨k + 1, by omega⟩, Fin.lt_def.2 (by rw [hpk]; simp),
        Fin.lt_def.2 (by simp only; omega)⟩
    have hr : (r : ℕ) ≤ k + 1 := partialPivotRow_le_succ M p hcol
    have hkr : k ≤ (r : ℕ) := le_partialPivotRow M p
    -- the rows of the swapped matrix
    have hM'_of : ∀ i : Fin N, i ≠ p → i ≠ r → ∀ j, M' i j = M i j := fun i hip hir j => by
      simp [hM', Equiv.swap_apply_of_ne_of_ne hip hir]
    have hM'p : ∀ j, M' p j = M r j := fun j => by simp [hM']
    have hrow_p : ∀ j, |M r j| ≤ ((k : ℕ) + 1) * A.supAbs := fun j => by
      rcases hkr.eq_or_lt with hrk | hrk
      · have : r = p := Fin.ext hrk.symm
        rw [this]
        exact h2 p j le_rfl
      · rw [h1 r j hrk]
        calc |A r j| ≤ A.supAbs := abs_apply_le_supAbs A r j
          _ ≤ ((k : ℕ) + 1) * A.supAbs := le_mul_of_one_le_left hμ (by linarith)
    refine ⟨fun i j hi => ?_, fun i j hi => ?_⟩
    · -- rows below `k + 1` are untouched
      have hip : i ≠ p := fun e => by rw [e] at hi; omega
      have hir : i ≠ r := fun e => by rw [e] at hi; omega
      rw [hM1, elimStep_apply_of_lt _ (Fin.lt_def.2 (by omega)),
        hM'_of i hip hir, hM'_of i hip hir, h1 i p (by omega), h1 i j (by omega),
        hA i p ⟨⟨k + 1, by omega⟩, Fin.lt_def.2 (by rw [hpk]; simp),
          Fin.lt_def.2 (by simp only; omega)⟩]
      ring
    · rcases Nat.lt_or_ge (i : ℕ) (k + 1) with hik | hik
      · -- rows at or above the pivot: unchanged by the elimination
        have hnlt : ¬ p < i := by simp only [Fin.lt_def]; omega
        rw [hM1, elimStep_apply_of_not_lt _ hnlt]
        rcases Nat.lt_or_ge (i : ℕ) k with hik' | hik'
        · have hip : i ≠ p := fun e => by rw [e] at hik'; omega
          have hir : i ≠ r := fun e => by rw [e] at hik'; omega
          rw [hM'_of i hip hir]
          exact h2 i j hik'.le
        · have hip : i = p := Fin.ext (by omega)
          rw [hip, hM'p, hpk]
          exact hrow_p j
      · -- the new working row `k + 1`
        have hiq : (i : ℕ) = k + 1 := by omega
        have hpi : p < i := Fin.lt_def.2 (by omega)
        rw [hM1, elimStep_apply_of_lt _ hpi, ← div_eq_mul_inv]
        -- the multiplier has modulus at most one
        have hτi : (p : ℕ) ≤ (Equiv.swap p r i : ℕ) := by
          rcases eq_or_ne r p with hrp | hrp
          · rw [hrp, Equiv.swap_self]
            simp only [Equiv.refl_apply]
            omega
          · have hir : i = r := Fin.ext (by omega)
            rw [hir, Equiv.swap_apply_right]
        have hmul : |M' i p / M' p p| ≤ 1 := by
          refine abs_div_le_one_of_abs_le ?_
          rw [hM'p]
          simp only [hM', submatrix_apply, id]
          have := norm_apply_le_partialPivotRow M p (Fin.le_def.2 hτi)
          simpa [Real.norm_eq_abs] using this
        -- the two rows involved are the working row and the original row `k + 1`
        have hsum : |M' i j| + |M' p j| ≤ ((k : ℕ) + 1) * A.supAbs + A.supAbs := by
          have hpk' : ((p : ℕ) : ℝ) = k := by rw [hpk]
          rcases eq_or_ne r p with hrp | hrp
          · have hip : i ≠ p := fun e => by rw [e] at hiq; omega
            have hir : i ≠ r := fun e => by rw [hrp] at e; exact hip e
            rw [hM'_of i hip hir, hM'p, h1 i j (by omega), hrp]
            have := h2 p j le_rfl
            rw [hpk'] at this
            linarith [abs_apply_le_supAbs A i j]
          · have hir : i = r := Fin.ext (by omega)
            rw [hM'p, hir]
            simp only [hM', submatrix_apply, Equiv.swap_apply_right, id]
            rw [h1 r j (by omega)]
            have := h2 p j le_rfl
            rw [hpk'] at this
            linarith [abs_apply_le_supAbs A r j]
        calc |M' i j - M' i p / M' p p * M' p j|
            ≤ |M' i j| + |M' i p / M' p p| * |M' p j| := by
              rw [← abs_mul]
              exact abs_sub _ _
          _ ≤ |M' i j| + 1 * |M' p j| :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_right hmul (abs_nonneg _))
          _ ≤ ((k : ℕ) + 1) * A.supAbs + A.supAbs := by rw [one_mul]; exact hsum
          _ = ((i : ℕ) + 1) * A.supAbs := by rw [hiq]; push_cast; ring

/-- **The growth factor of partial pivoting on an upper Hessenberg matrix is at most $N$.** If
$A \in \mathbb{R}^{N \times N}$ is upper Hessenberg and $\sigma_N$ is the permutation of
Gaussian elimination with the strategy `Matrix.partialPivotRow`, then
$$\rho(P_{\sigma_N} A) \le N.$$

This is [quarteroni2000numerical], §3.10 (2), and Theorem 9.10 of [higham2002accuracy]
(Wilkinson). By the shape invariant
`Matrix.gemPivotStage_partialPivotRow_isUpperHessenberg_invariant`, every entry of every stage
is at most $N \mu(A)$. The pivoted stages are the stages of elimination without pivoting on
$P_{\sigma_N} A$ up to the order of the rows. -/
theorem growthFactor_le_card_of_isUpperHessenberg (hA : A.IsUpperHessenberg) :
    growthFactor ((gemPivotStage A partialPivotRow N).2.permMatrix ℝ * A) ≤ N := by
  have hpiv : ∀ (M : Matrix (Fin N) (Fin N) ℝ) k, k ≤ partialPivotRow M k := fun M k =>
    le_partialPivotRow M k
  have hμ := supAbs_nonneg A
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  refine growthFactor_le_of_forall_abs_le _ (Nat.cast_nonneg N) fun k i j hk => ?_
  rw [supAbs_submatrix_equiv, gemStage_submatrix_eq_submatrix_gemPivotStage A partialPivotRow
    hpiv k, submatrix_apply, id_eq]
  obtain ⟨h1, h2⟩ := gemPivotStage_partialPivotRow_isUpperHessenberg_invariant hA k
  set i' := ((gemPivotStage A partialPivotRow k).2⁻¹ * (gemPivotStage A partialPivotRow N).2) i
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact i.elim0)
  rcases le_or_gt (i' : ℕ) k with hi | hi
  · refine (h2 i' j hi).trans (mul_le_mul_of_nonneg_right ?_ hμ)
    exact_mod_cast i'.2
  · rw [h1 i' j hi]
    exact (abs_apply_le_supAbs A i' j).trans (le_mul_of_one_le_left hμ hN)

end Hessenberg

section Tridiagonal

variable {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}

/-- After a stage of partial pivoting, the pivot column vanishes below the pivot, whether the pivot
is zero or not: for $A \in \mathbb{R}^{N \times N}$, $k < N$ and $i > k$,
$\hat a^{(k+1)}_{ik} = 0$. A zero pivot comes with a zero column. -/
theorem gemPivotStage_partialPivotRow_succ_apply_pivot {k : ℕ} (hk : k < N) {i : Fin N}
    (hi : (⟨k, hk⟩ : Fin N) < i) :
    (gemPivotStage A partialPivotRow (k + 1)).1 i ⟨k, hk⟩ = 0 := by
  set p : Fin N := ⟨k, hk⟩ with hp
  set M := (gemPivotStage A partialPivotRow k).1 with hM
  set r := partialPivotRow M p with hrdef
  rw [gemPivotStage_succ_of_lt A partialPivotRow hk]
  change elimStep (M.submatrix (Equiv.swap p r) id) p i p = 0
  rcases eq_or_ne (M.submatrix (Equiv.swap p r) id p p) 0 with h0 | h0
  · have hcol : ∀ i : Fin N, p ≤ i → M i p = 0 := fun i hi => by
      refine apply_eq_zero_of_partialPivotRow_eq_zero M p ?_ hi
      simpa using h0
    rw [elimStep_apply_of_lt _ hi, h0, submatrix_apply, id_eq, hcol _ ?_]
    · ring
    · rcases eq_or_ne r p with hrp | hrp
      · rw [hrp, Equiv.swap_self, Equiv.refl_apply]
        exact hi.le
      · rcases eq_or_ne i r with hir | hir
        · rw [hir, Equiv.swap_apply_right]
        · rw [Equiv.swap_apply_of_ne_of_ne hi.ne' hir]
          exact hi.le
  · exact elimStep_apply_pivot _ hi h0

/-- **The shape invariant of partial pivoting on a tridiagonal matrix.** Let
$A \in \mathbb{R}^{N \times N}$ be tridiagonal, let $\mu = \mu(A)$, and let $\hat A^{(k)}$ be
the stages of Gaussian elimination with the strategy `Matrix.partialPivotRow`. Then for every
$k$:

* if $k < N$, the working row $k$ of $\hat A^{(k)}$ is supported in the columns $k$ and $k + 1$,
  with $|\hat a^{(k)}_{kk}| \le 2\mu$ and $|\hat a^{(k)}_{kj}| \le \mu$ for $j \neq k$;
* the finished rows are bounded by $2\mu$: $|\hat a^{(k)}_{ij}| \le 2\mu$ for $i < k$.

This is the "easily verified result that for a tridiagonal matrix $\rho_n^p \le 2$" of
[higham2002accuracy], §9.5. The rows below $k$ are the rows of $A$, by
`Matrix.gemPivotStage_partialPivotRow_isUpperHessenberg_invariant`. -/
theorem gemPivotStage_partialPivotRow_isTridiagonal_invariant (hA : A.IsTridiagonal) (k : ℕ) :
    (∀ hk : k < N,
      |(gemPivotStage A partialPivotRow k).1 ⟨k, hk⟩ ⟨k, hk⟩| ≤ 2 * A.supAbs ∧
      (∀ j, j ≠ ⟨k, hk⟩ → |(gemPivotStage A partialPivotRow k).1 ⟨k, hk⟩ j| ≤ A.supAbs) ∧
      ∀ j : Fin N, (j : ℕ) ≠ k → (j : ℕ) ≠ k + 1 →
        (gemPivotStage A partialPivotRow k).1 ⟨k, hk⟩ j = 0) ∧
    ∀ i j : Fin N, (i : ℕ) < k → |(gemPivotStage A partialPivotRow k).1 i j| ≤ 2 * A.supAbs := by
  have hμ := supAbs_nonneg A
  induction k with
  | zero =>
    refine ⟨fun hk => ⟨?_, fun j _ => ?_, fun j hj0 hj1 => ?_⟩, fun i j hi => absurd hi (by omega)⟩
    · rw [gemPivotStage_zero]
      exact (abs_apply_le_supAbs A _ _).trans (le_mul_of_one_le_left hμ one_le_two)
    · rw [gemPivotStage_zero]
      exact abs_apply_le_supAbs A _ _
    · rw [gemPivotStage_zero]
      exact hA _ j (Or.inr ⟨⟨1, by omega⟩, Fin.lt_def.2 (by simp), Fin.lt_def.2 (by simp; omega)⟩)
  | succ k ih =>
    obtain ⟨hT2, hT3⟩ := ih
    by_cases hk : k < N
    swap
    · rw [gemPivotStage_succ_of_le A _ (not_lt.1 hk)]
      exact ⟨fun hk' => absurd hk' (by omega), fun i j _ => hT3 i j (by omega)⟩
    obtain ⟨h2a, h2b, h2c⟩ := hT2 hk
    have h1 := (gemPivotStage_partialPivotRow_isUpperHessenberg_invariant hA.isUpperHessenberg k).1
    set p : Fin N := ⟨k, hk⟩ with hp
    have hpk : (p : ℕ) = k := rfl
    set M := (gemPivotStage A partialPivotRow k).1 with hM
    set r := partialPivotRow M p with hrdef
    have hM1 : (gemPivotStage A partialPivotRow (k + 1)).1 =
        elimStep (M.submatrix (Equiv.swap p r) id) p := by
      rw [gemPivotStage_succ_of_lt A partialPivotRow hk]
      rfl
    set M' := M.submatrix (Equiv.swap p r) id with hM'
    have hcol : ∀ i : Fin N, (p : ℕ) + 1 < i → M i p = 0 := fun i hi => by
      rw [h1 i p (by omega)]
      exact hA.isUpperHessenberg i p ⟨⟨k + 1, by omega⟩, Fin.lt_def.2 (by rw [hpk]; simp),
        Fin.lt_def.2 (by simp only; omega)⟩
    have hr : (r : ℕ) ≤ k + 1 := partialPivotRow_le_succ M p hcol
    have hkr : k ≤ (r : ℕ) := le_partialPivotRow M p
    have hM'_of : ∀ i : Fin N, i ≠ p → i ≠ r → ∀ j, M' i j = M i j := fun i hip hir j => by
      simp [hM', Equiv.swap_apply_of_ne_of_ne hip hir]
    have hM'p : ∀ j, M' p j = M r j := fun j => by simp [hM']
    -- the working row is bounded by `2μ`
    have hrow_p : ∀ j, |M p j| ≤ 2 * A.supAbs := fun j => by
      rcases eq_or_ne j p with rfl | hj
      · exact h2a
      · exact (h2b j hj).trans (le_mul_of_one_le_left hμ one_le_two)
    have hrow_r : ∀ j, |M r j| ≤ 2 * A.supAbs := fun j => by
      rcases hkr.eq_or_lt with hrk | hrk
      · have : r = p := Fin.ext hrk.symm
        rw [this]
        exact hrow_p j
      · rw [h1 r j hrk]
        exact (abs_apply_le_supAbs A r j).trans (le_mul_of_one_le_left hμ one_le_two)
    refine ⟨fun hk1 => ?_, fun i j hi => ?_⟩
    swap
    · -- the finished rows
      have hnlt : ¬ p < i := by simp only [Fin.lt_def]; omega
      rw [hM1, elimStep_apply_of_not_lt _ hnlt]
      rcases Nat.lt_or_ge (i : ℕ) k with hik' | hik'
      · have hip : i ≠ p := fun e => by rw [e] at hik'; omega
        have hir : i ≠ r := fun e => by rw [e] at hik'; omega
        rw [hM'_of i hip hir]
        exact hT3 i j hik'
      · have hip : i = p := Fin.ext (by omega)
        rw [hip, hM'p]
        exact hrow_r j
    -- the new working row `q = k + 1`
    set q : Fin N := ⟨k + 1, hk1⟩ with hq
    have hqk : (q : ℕ) = k + 1 := rfl
    have hpq : p < q := Fin.lt_def.2 (by omega)
    have hqp : q ≠ p := fun e => by rw [Fin.ext_iff] at e; omega
    -- the pair of rows involved, in either order
    have hpair : ∀ j, |M' q j| + |M' p j| = |M p j| + |A q j| := fun j => by
      rcases eq_or_ne r p with hrp | hrp
      · have hqr : q ≠ r := by rw [hrp]; exact hqp
        rw [hM'_of q hqp hqr, hM'p, hrp, h1 q j (by omega), add_comm]
      · have hqr : q = r := Fin.ext (by omega)
        rw [hM'p, ← hqr]
        simp only [hM', submatrix_apply, hqr, Equiv.swap_apply_right, id_eq]
        rw [← hqr, h1 q j (by omega)]
    have hmul : |M' q p / M' p p| ≤ 1 := by
      refine abs_div_le_one_of_abs_le ?_
      rw [hM'p]
      simp only [hM', submatrix_apply, id_eq]
      have hτq : p ≤ Equiv.swap p r q := by
        rcases eq_or_ne r p with hrp | hrp
        · rw [hrp, Equiv.swap_self, Equiv.refl_apply]
          exact hpq.le
        · have hqr : q = r := Fin.ext (by omega)
          rw [hqr, Equiv.swap_apply_right]
      have := norm_apply_le_partialPivotRow M p hτq
      simpa [Real.norm_eq_abs] using this
    have hentry : ∀ j, |(gemPivotStage A partialPivotRow (k + 1)).1 q j| ≤ |M p j| + |A q j| := by
      intro j
      rw [hM1, elimStep_apply_of_lt _ hpq, ← div_eq_mul_inv]
      calc |M' q j - M' q p / M' p p * M' p j|
          ≤ |M' q j| + |M' q p / M' p p| * |M' p j| := by
            rw [← abs_mul]
            exact abs_sub _ _
        _ ≤ |M' q j| + 1 * |M' p j| :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right hmul (abs_nonneg _))
        _ = |M p j| + |A q j| := by rw [one_mul, hpair]
    have hpiv0 : (gemPivotStage A partialPivotRow (k + 1)).1 q p = 0 :=
      gemPivotStage_partialPivotRow_succ_apply_pivot hk hpq
    refine ⟨?_, fun j hjq => ?_, fun j hj1 hj2 => ?_⟩
    · -- the diagonal entry
      refine (hentry q).trans ?_
      have := h2b q hqp
      linarith [abs_apply_le_supAbs A q q]
    · -- the other entries of the working row
      rcases eq_or_ne j p with rfl | hjp
      · rw [hpiv0, abs_zero]
        exact hμ
      · have hw : M p j = 0 := h2c j (fun e => hjp (Fin.ext e)) fun e => hjq (Fin.ext e)
        refine (hentry j).trans ?_
        rw [hw, abs_zero, zero_add]
        exact abs_apply_le_supAbs A q j
    · -- the support of the working row
      rcases eq_or_ne j p with rfl | hjp
      · exact hpiv0
      · have hw : M p j = 0 := h2c j (fun e => hjp (Fin.ext e)) hj1
        have hAqj : A q j = 0 := by
          refine hA q j ?_
          rcases Nat.lt_or_ge (j : ℕ) k with hjk | hjk
          · exact Or.inl ⟨p, Fin.lt_def.2 (by omega), hpq⟩
          · exact Or.inr ⟨⟨k + 2, by omega⟩, Fin.lt_def.2 (by simp only; omega),
              Fin.lt_def.2 (by simp only; omega)⟩
        have := hentry j
        rw [hw, hAqj, abs_zero, add_zero] at this
        exact abs_nonpos_iff.1 this

/-- **The growth factor of partial pivoting on a tridiagonal matrix is at most two.** If
$A \in \mathbb{R}^{N \times N}$ is tridiagonal and $\sigma_N$ is the permutation of Gaussian
elimination with the strategy `Matrix.partialPivotRow`, then
$$\rho(P_{\sigma_N} A) \le 2.$$

This is the tridiagonal case of [quarteroni2000numerical], §3.10 (1), and of
[higham2002accuracy], §9.5: the case $p = 1$ of Bohte's Theorem 9.11. By the shape invariant
`Matrix.gemPivotStage_partialPivotRow_isTridiagonal_invariant`, every entry of every stage is at
most $2 \mu(A)$. -/
theorem growthFactor_le_two_of_isTridiagonal (hA : A.IsTridiagonal) :
    growthFactor ((gemPivotStage A partialPivotRow N).2.permMatrix ℝ * A) ≤ 2 := by
  have hpiv : ∀ (M : Matrix (Fin N) (Fin N) ℝ) k, k ≤ partialPivotRow M k := fun M k =>
    le_partialPivotRow M k
  have hμ := supAbs_nonneg A
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  refine growthFactor_le_of_forall_abs_le _ zero_le_two fun k i j hk => ?_
  rw [supAbs_submatrix_equiv, gemStage_submatrix_eq_submatrix_gemPivotStage A partialPivotRow
    hpiv k, submatrix_apply, id_eq]
  obtain ⟨hT2, hT3⟩ := gemPivotStage_partialPivotRow_isTridiagonal_invariant hA k
  obtain ⟨h2a, h2b, -⟩ := hT2 hk
  have h1 := (gemPivotStage_partialPivotRow_isUpperHessenberg_invariant hA.isUpperHessenberg k).1
  set i' := ((gemPivotStage A partialPivotRow k).2⁻¹ * (gemPivotStage A partialPivotRow N).2) i
  rcases lt_trichotomy (i' : ℕ) k with hi | hi | hi
  · exact hT3 i' j hi
  · have : i' = ⟨k, hk⟩ := Fin.ext hi
    rw [this]
    rcases eq_or_ne j ⟨k, hk⟩ with rfl | hj
    · exact h2a
    · exact (h2b j hj).trans (le_mul_of_one_le_left hμ one_le_two)
  · rw [h1 i' j hi]
    exact (abs_apply_le_supAbs A i' j).trans (le_mul_of_one_le_left hμ one_le_two)

end Tridiagonal

section Band

variable {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {p q : ℕ}

/-- Under partial pivoting, a column stays zero below its diagonal entry once it has been
eliminated, whether its pivot was zero or not: for $A \in \mathbb{R}^{N \times N}$ and every
$k$, $\hat a^{(k)}_{ij} = 0$ whenever $j < k$ and $j < i$.

A zero pivot of partial pivoting comes with a zero column, so no hypothesis on the pivots is
needed, unlike in `Matrix.gemStage_apply_eq_zero_of_lt`. -/
theorem gemPivotStage_partialPivotRow_apply_eq_zero_of_lt (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) :
    ∀ i j : Fin N, (j : ℕ) < k → j < i → (gemPivotStage A partialPivotRow k).1 i j = 0 := by
  induction k with
  | zero => exact fun i j hj _ => absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    intro i j hj hji
    by_cases hk : k < N
    swap
    · rw [gemPivotStage_succ_of_le A _ (not_lt.1 hk)]
      exact ih i j (by omega) hji
    set P : Fin N := ⟨k, hk⟩ with hP
    set M := (gemPivotStage A partialPivotRow k).1 with hM
    set r := partialPivotRow M P with hr
    have hMk : (gemPivotStage A partialPivotRow (k + 1)).1 =
        elimStep (M.submatrix (Equiv.swap P r) id) P := by
      rw [gemPivotStage_succ_of_lt A partialPivotRow hk]
      rfl
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjk | hjk
    · -- an earlier column: the pivot row is already zero there, so nothing changes
      have hPr : (P : ℕ) ≤ (r : ℕ) := le_partialPivotRow M P
      have hswap : ∀ i : Fin N, j < i → j < Equiv.swap P r i := by
        intro i hi
        rcases eq_or_ne i P with rfl | hiP
        · rw [Equiv.swap_apply_left]
          exact Fin.lt_def.2 (by omega)
        rcases eq_or_ne i r with rfl | hir
        · rw [Equiv.swap_apply_right]
          exact Fin.lt_def.2 (by omega)
        · rwa [Equiv.swap_apply_of_ne_of_ne hiP hir]
      have hrow : (M.submatrix (Equiv.swap P r) id) P j = 0 := by
        simp only [submatrix_apply, id_eq]
        exact ih _ j hjk (hswap P (Fin.lt_def.2 (by omega)))
      rw [hMk, elimStep_apply_of_pivot_row_eq_zero _ _ _ hrow, submatrix_apply, id_eq]
      exact ih _ j hjk (hswap i hji)
    · -- the column just eliminated
      have hjP : j = P := Fin.ext hjk
      subst hjP
      exact gemPivotStage_partialPivotRow_succ_apply_pivot hk hji

/-- **The shape invariant of partial pivoting on a band matrix.** Let
$A \in \mathbb{R}^{N \times N}$ have lower bandwidth $p$ and upper bandwidth $q$, and let
$\hat A^{(k)}$ be the stages of Gaussian elimination with the strategy `Matrix.partialPivotRow`.
Then for every $k$:

* the rows $i \ge k + p$ are still the rows of $A$: $\hat a^{(k)}_{ij} = a_{ij}$;
* every row $i < k + p$ vanishes after the column $k + p + q$: $\hat a^{(k)}_{ij} = 0$ for
  $j > k + p + q$.

The rows $i \ge k + p$ have not met a pivot yet. The interchanges widen the upper band from $q$
to $p + q$ and no further, because a pivot row is at most $p$ below the pivot index
([higham2002accuracy], §9.5; [quarteroni2000numerical], §3.10 (1)). -/
theorem gemPivotStage_partialPivotRow_hasBandwidth_invariant (hp : A.HasLowerBandwidth p)
    (hq : A.HasUpperBandwidth q) (k : ℕ) :
    (∀ i j : Fin N, k + p ≤ (i : ℕ) → (gemPivotStage A partialPivotRow k).1 i j = A i j) ∧
      (∀ i j : Fin N, (i : ℕ) < k + p → k + p + q < (j : ℕ) →
        (gemPivotStage A partialPivotRow k).1 i j = 0) := by
  rw [hasLowerBandwidth_iff_fin] at hp
  rw [hasUpperBandwidth_iff_fin] at hq
  induction k with
  | zero =>
    refine ⟨fun i j _ => rfl, fun i j hi hj => ?_⟩
    rw [gemPivotStage_zero]
    exact hq i j (by omega)
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    by_cases hk : k < N
    swap
    · rw [gemPivotStage_succ_of_le A _ (not_lt.1 hk)]
      exact ⟨fun i j hi => h1 i j (by omega), fun i j hi hj => h2 i j (by omega) (by omega)⟩
    set P : Fin N := ⟨k, hk⟩ with hP
    have hPk : (P : ℕ) = k := rfl
    set M := (gemPivotStage A partialPivotRow k).1 with hM
    set r := partialPivotRow M P with hr
    have hMk : (gemPivotStage A partialPivotRow (k + 1)).1 =
        elimStep (M.submatrix (Equiv.swap P r) id) P := by
      rw [gemPivotStage_succ_of_lt A partialPivotRow hk]
      rfl
    set M' := M.submatrix (Equiv.swap P r) id with hM'
    -- the pivot row lies at most `p` below the pivot index
    have hcol : ∀ i : Fin N, (P : ℕ) + p < i → M i P = 0 := fun i hi => by
      rw [h1 i P (by omega)]
      exact hp i P (by omega)
    have hrp : (r : ℕ) ≤ k + p := partialPivotRow_le_add M P p hcol
    have hM'_of : ∀ i : Fin N, i ≠ P → i ≠ r → ∀ j, M' i j = M i j := fun i hiP hir j => by
      simp [hM', Equiv.swap_apply_of_ne_of_ne hiP hir]
    have hM'P : ∀ j, M' P j = M r j := fun j => by simp [hM']
    -- the pivot row vanishes past the column `k + p + q`
    have hpivrow : ∀ j : Fin N, k + p + q < (j : ℕ) → M' P j = 0 := by
      intro j hj
      rw [hM'P]
      rcases Nat.lt_or_ge (r : ℕ) (k + p) with hrk | hrk
      · exact h2 r j hrk hj
      · rw [h1 r j (by omega)]
        exact hq r j (by omega)
    refine ⟨fun i j hi => ?_, fun i j hi hj => ?_⟩
    · -- the rows `k + 1 + p` and below are untouched
      have hiP : i ≠ P := fun e => by rw [e] at hi; omega
      have hir : i ≠ r := fun e => by rw [e] at hi; omega
      rw [hMk, elimStep_apply_of_lt _ (Fin.lt_def.2 (by omega)), hM'_of i hiP hir,
        hM'_of i hiP hir, h1 i P (by omega), hp i P (by omega)]
      simp [h1 i j (by omega)]
    · -- the support of the rows above them
      have hrow : ∀ i : Fin N, (i : ℕ) < k + 1 + p → M' i j = 0 := by
        intro i hi
        rcases eq_or_ne i P with rfl | hiP
        · exact hpivrow j (by omega)
        rcases eq_or_ne i r with rfl | hir
        · simp only [hM', submatrix_apply, Equiv.swap_apply_right, id_eq]
          rcases Nat.lt_or_ge (k : ℕ) (k + p) with hkp | hkp
          · exact h2 P j hkp (by omega)
          · rw [h1 P j (by omega)]
            exact hq P j (by omega)
        · rw [hM'_of i hiP hir]
          rcases Nat.lt_or_ge (i : ℕ) (k + p) with hik | hik
          · exact h2 i j hik (by omega)
          · rw [h1 i j (by omega)]
            exact hq i j (by omega)
      rw [hMk, elimStep_apply, hrow P (by omega), mul_zero, ite_self, sub_zero]
      exact hrow i hi

/-- **The band bound on the stages of partial pivoting.** Let $A \in \mathbb{R}^{N \times N}$ have
lower bandwidth $p$ and upper bandwidth $q$, and let $\hat A^{(k)}$ be the stages of Gaussian
elimination with the strategy `Matrix.partialPivotRow`. Then for every $k$ and all $i, j$,
$$|\hat a^{(k)}_{ij}| \le 2^{m} \mu(A), \qquad m = \min(k, j) - (j - (p + q)),$$
with truncated subtraction of natural numbers.

The number $m$ counts the stages before $k$ that change the column $j$. A stage changes a column
only if the pivot row reaches it, and the pivot row of stage $k$ is supported in the columns $k$
to $k + p + q$ (`Matrix.gemPivotStage_partialPivotRow_hasBandwidth_invariant`). Each such stage
at most doubles the column, because the multipliers are bounded by one. -/
theorem abs_gemPivotStage_le_of_hasBandwidth (hp : A.HasLowerBandwidth p)
    (hq : A.HasUpperBandwidth q) (k : ℕ) (i j : Fin N) :
    |(gemPivotStage A partialPivotRow k).1 i j| ≤
      2 ^ (min k (j : ℕ) - ((j : ℕ) - (p + q))) * A.supAbs := by
  have hμ := supAbs_nonneg A
  induction k generalizing i with
  | zero => simpa using abs_apply_le_supAbs A i j
  | succ k ih =>
    have hmono : (2 : ℝ) ^ (min k (j : ℕ) - ((j : ℕ) - (p + q))) ≤
        2 ^ (min (k + 1) (j : ℕ) - ((j : ℕ) - (p + q))) :=
      pow_le_pow_right₀ one_le_two (by omega)
    by_cases hk : k < N
    swap
    · rw [gemPivotStage_succ_of_le A _ (not_lt.1 hk)]
      exact (ih i).trans (mul_le_mul_of_nonneg_right hmono hμ)
    set P : Fin N := ⟨k, hk⟩ with hP
    have hPk : (P : ℕ) = k := rfl
    set M := (gemPivotStage A partialPivotRow k).1 with hM
    set r := partialPivotRow M P with hr
    have hMk : (gemPivotStage A partialPivotRow (k + 1)).1 =
        elimStep (M.submatrix (Equiv.swap P r) id) P := by
      rw [gemPivotStage_succ_of_lt A partialPivotRow hk]
      rfl
    set M' := M.submatrix (Equiv.swap P r) id with hM'
    have hih' : ∀ i : Fin N, |M' i j| ≤ 2 ^ (min k (j : ℕ) - ((j : ℕ) - (p + q))) * A.supAbs :=
      fun i => ih _
    have hPr : P ≤ r := le_partialPivotRow M P
    have hkr : k ≤ (r : ℕ) := hPr
    have hband := gemPivotStage_partialPivotRow_hasBandwidth_invariant hp hq k
    have hb1 : ∀ i j : Fin N, k + p ≤ (i : ℕ) → M i j = A i j := hband.1
    have hb2 : ∀ i j : Fin N, (i : ℕ) < k + p → k + p + q < (j : ℕ) → M i j = 0 := hband.2
    have hcol : ∀ i : Fin N, (P : ℕ) + p < i → M i P = 0 := fun i hi => by
      rw [hb1 i P (by omega)]
      exact hasLowerBandwidth_iff_fin.1 hp i P (by omega)
    have hrp : (r : ℕ) ≤ k + p := partialPivotRow_le_add M P p hcol
    rcases Nat.lt_or_ge (j : ℕ) k with hjk | hjk
    · -- an earlier column: the pivot row vanishes there
      have hjr : j < r := lt_of_lt_of_le (show j < P from Fin.lt_def.2 (by omega)) hPr
      have hrow : M' P j = 0 := by
        simp only [hM', submatrix_apply, Equiv.swap_apply_left, id_eq]
        exact gemPivotStage_partialPivotRow_apply_eq_zero_of_lt A k r j hjk hjr
      rw [hMk, elimStep_apply_of_pivot_row_eq_zero _ _ _ hrow]
      exact (hih' i).trans (mul_le_mul_of_nonneg_right hmono hμ)
    rcases Nat.lt_or_ge (k : ℕ) (j : ℕ) with hjk' | hjk'
    swap
    · -- the column just eliminated
      have hjP : j = P := Fin.ext (by omega)
      by_cases hi : P < i
      · rw [hjP, gemPivotStage_partialPivotRow_succ_apply_pivot hk hi, abs_zero]
        exact mul_nonneg (by positivity) hμ
      · rw [hMk, elimStep_apply_of_not_lt _ hi]
        exact (hih' i).trans (mul_le_mul_of_nonneg_right hmono hμ)
    rcases Nat.lt_or_ge (k + p + q) (j : ℕ) with hjq | hjq
    · -- past the band of the pivot row
      have hrow : M' P j = 0 := by
        simp only [hM', submatrix_apply, Equiv.swap_apply_left, id_eq]
        rcases Nat.lt_or_ge (r : ℕ) (k + p) with hrk | hrk
        · exact hb2 r j hrk hjq
        · rw [hb1 r j (by omega)]
          exact hasUpperBandwidth_iff_fin.1 hq r j (by omega)
      rw [hMk, elimStep_apply_of_pivot_row_eq_zero _ _ _ hrow]
      exact (hih' i).trans (mul_le_mul_of_nonneg_right hmono hμ)
    · -- inside the band: one more doubling, which the counter allows
      have hpow : (2 : ℝ) ^ (min k (j : ℕ) - ((j : ℕ) - (p + q))) * 2 ≤
          2 ^ (min (k + 1) (j : ℕ) - ((j : ℕ) - (p + q))) := by
        rw [← pow_succ]
        exact pow_le_pow_right₀ one_le_two (by omega)
      by_cases hi : P < i
      · rw [hMk, elimStep_apply_of_lt _ hi, ← div_eq_mul_inv]
        have hmul : |M' i P / M' P P| ≤ 1 := by
          refine abs_div_le_one_of_abs_le ?_
          simp only [hM', submatrix_apply, Equiv.swap_apply_left, id_eq]
          have hτ : P ≤ Equiv.swap P r i := by
            rcases eq_or_ne i P with rfl | hiP
            · rwa [Equiv.swap_apply_left]
            rcases eq_or_ne i r with rfl | hir
            · rw [Equiv.swap_apply_right]
            · rw [Equiv.swap_apply_of_ne_of_ne hiP hir]
              exact hi.le
          simpa [Real.norm_eq_abs] using norm_apply_le_partialPivotRow M P hτ
        calc |M' i j - M' i P / M' P P * M' P j|
            ≤ |M' i j| + |M' i P / M' P P| * |M' P j| := by
              rw [← abs_mul]; exact abs_sub _ _
          _ ≤ |M' i j| + 1 * |M' P j| :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_right hmul (abs_nonneg _))
          _ ≤ 2 ^ (min k (j : ℕ) - ((j : ℕ) - (p + q))) * A.supAbs +
                2 ^ (min k (j : ℕ) - ((j : ℕ) - (p + q))) * A.supAbs := by
              rw [one_mul]; exact add_le_add (hih' i) (hih' P)
          _ = 2 ^ (min k (j : ℕ) - ((j : ℕ) - (p + q))) * 2 * A.supAbs := by ring
          _ ≤ 2 ^ (min (k + 1) (j : ℕ) - ((j : ℕ) - (p + q))) * A.supAbs :=
              mul_le_mul_of_nonneg_right hpow hμ
      · rw [hMk, elimStep_apply_of_not_lt _ hi]
        exact (hih' i).trans (mul_le_mul_of_nonneg_right hmono hμ)

/-- **A band bound for the growth factor of partial pivoting.** If $A \in \mathbb{R}^{N \times N}$
has lower bandwidth $p$ and upper bandwidth $q$, and $\sigma_N$ is the permutation of Gaussian
elimination with the strategy `Matrix.partialPivotRow`, then
$$\rho(P_{\sigma_N} A) \le 2^{p+q},$$
a bound that does not depend on the order $N$.

Section 3.10 (1) of [quarteroni2000numerical] and Theorem 9.11 of [higham2002accuracy] quote
Bohte's sharper bound $2^{2p-1} - (p-1) 2^{p-2}$ for $p = q$. This theorem does not reach it:
for $p = q$ it gives $2^{2p}$. The tridiagonal case $p = q = 1$ is sharpened to $2$ by
`Matrix.growthFactor_le_two_of_isTridiagonal`. -/
theorem growthFactor_le_two_pow_of_hasBandwidth (hp : A.HasLowerBandwidth p)
    (hq : A.HasUpperBandwidth q) :
    growthFactor ((gemPivotStage A partialPivotRow N).2.permMatrix ℝ * A) ≤ 2 ^ (p + q) := by
  have hpiv : ∀ (M : Matrix (Fin N) (Fin N) ℝ) k, k ≤ partialPivotRow M k := fun M k =>
    le_partialPivotRow M k
  have hμ := supAbs_nonneg A
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  refine growthFactor_le_of_forall_abs_le _ (by positivity) fun k i j hk => ?_
  rw [supAbs_submatrix_equiv, gemStage_submatrix_eq_submatrix_gemPivotStage A partialPivotRow
    hpiv k, submatrix_apply, id_eq]
  refine (abs_gemPivotStage_le_of_hasBandwidth hp hq k _ j).trans
    (mul_le_mul_of_nonneg_right ?_ hμ)
  exact pow_le_pow_right₀ one_le_two (by omega)

end Band

/-! ### The factors of partial pivoting on a band matrix -/

section BandStages

variable {N : ℕ}

/-- Suppose that the strategy always chooses a row at or below the current index. Then the row $i$
of the pivoted stages does not change after the stage $k + 1$, for every $k \ge i$: if
$k + 1 \le m$, then $\hat a^{(m)}_{ij} = \hat a^{(k+1)}_{ij}$. The later interchanges and
elimination steps only change the rows below. -/
theorem gemPivotStage_fst_apply_of_le {K : Type*} [Field K] (A : Matrix (Fin N) (Fin N) K)
    (piv : Matrix (Fin N) (Fin N) K → Fin N → Fin N) (hpiv : ∀ M k, k ≤ piv M k) {i : Fin N}
    {k m : ℕ} (hi : (i : ℕ) ≤ k) (hkm : k + 1 ≤ m) (j : Fin N) :
    (gemPivotStage A piv m).1 i j = (gemPivotStage A piv (k + 1)).1 i j := by
  induction m, hkm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    by_cases h : m < N
    · rw [gemPivotStage_succ_of_lt A piv h]
      dsimp only
      rw [elimStep_apply_of_not_lt _ (fun hlt => Nat.not_lt.2 (by omega : (i : ℕ) ≤ m)
          (Fin.lt_def.1 hlt)), submatrix_apply, id,
        gemPivotSwap_apply_of_lt A piv hpiv h (by omega), ih]
    · rw [gemPivotStage_succ_of_le A piv (not_lt.1 h), ih]

variable {A : Matrix (Fin N) (Fin N) ℝ} {p q : ℕ}

/-- Let $A \in \mathbb{R}^{N \times N}$ have lower bandwidth $p$ and upper bandwidth $q$. Then the
upper factor $U = \hat A^{(N)}$ of Gaussian elimination with the strategy
`Matrix.partialPivotRow` has upper bandwidth $p + q$. No nonsingularity is needed. This is
Theorem 4.3.2 of [golub2013matrix], the statement on the upper factor.

The row $k$ of $U$ is the pivot row of stage $k$. It lies at most $p$ below $k$ and, by
`Matrix.gemPivotStage_partialPivotRow_hasBandwidth_invariant`, vanishes after the column
$k + p + q$. -/
theorem gemPivotStage_partialPivotRow_hasUpperBandwidth (hp : A.HasLowerBandwidth p)
    (hq : A.HasUpperBandwidth q) :
    (gemPivotStage A partialPivotRow N).1.HasUpperBandwidth (p + q) := by
  have hpiv : ∀ (M : Matrix (Fin N) (Fin N) ℝ) k, k ≤ partialPivotRow M k := fun M k =>
    le_partialPivotRow M k
  have hp' := hasLowerBandwidth_iff_fin.1 hp
  have hq' := hasUpperBandwidth_iff_fin.1 hq
  rw [hasUpperBandwidth_iff_fin]
  rintro ⟨k, hk⟩ j (hij : k + (p + q) < (j : ℕ))
  rw [gemPivotStage_fst_apply_of_le A partialPivotRow hpiv (i := ⟨k, hk⟩) (le_refl k) hk j,
    gemPivotStage_succ_of_lt A partialPivotRow hk]
  dsimp only
  rw [elimStep_apply_of_not_lt _ (lt_irrefl _), submatrix_apply, id, gemPivotSwap,
    Equiv.swap_apply_left]
  have hcol : ∀ i : Fin N, k + p < (i : ℕ) →
      (gemPivotStage A partialPivotRow k).1 i ⟨k, hk⟩ = 0 := fun i hi => by
    rw [(gemPivotStage_partialPivotRow_hasBandwidth_invariant hp hq k).1 i _ (by omega)]
    exact hp' i _ hi
  have hrp : ((partialPivotRow (gemPivotStage A partialPivotRow k).1 ⟨k, hk⟩ : Fin N) : ℕ) ≤
      k + p := partialPivotRow_le_add _ ⟨k, hk⟩ p hcol
  rcases Nat.lt_or_ge ((partialPivotRow (gemPivotStage A partialPivotRow k).1 ⟨k, hk⟩ : Fin N) : ℕ)
    (k + p) with hrk | hrk
  · exact (gemPivotStage_partialPivotRow_hasBandwidth_invariant hp hq k).2 _ j hrk (by omega)
  · rw [(gemPivotStage_partialPivotRow_hasBandwidth_invariant hp hq k).1 _ j hrk]
    exact hq' _ j (by omega)

/-- Let $A \in \mathbb{R}^{N \times N}$ have lower bandwidth $p$ and upper bandwidth $q$, and let
$k < N$. The multiplier matrix `Matrix.elimMultipliers` of stage $k$ of Gaussian elimination
with the strategy `Matrix.partialPivotRow`, that is, of $\hat A^{(k)}$ after its interchange,
vanishes in the rows $i \le k$ and $i > k + p$. This is Theorem 4.3.2 of [golub2013matrix], the
statement on the Gauss vectors.

So each column of the lower factor has at most $p + 1$ nonzero entries. Below the row $k + p$
the column $k$ still holds entries of $A$, and these vanish by the lower bandwidth. -/
theorem gemPivotStage_partialPivotRow_multiplier_eq_zero (hp : A.HasLowerBandwidth p)
    (hq : A.HasUpperBandwidth q) {k : ℕ} (hk : k < N) {i : Fin N}
    (hi : (i : ℕ) ≤ k ∨ k + p < (i : ℕ)) (j : Fin N) :
    elimMultipliers ((gemPivotStage A partialPivotRow k).1.submatrix
      (gemPivotSwap A partialPivotRow k hk) id) ⟨k, hk⟩ i j = 0 := by
  have hp' := hasLowerBandwidth_iff_fin.1 hp
  rw [elimMultipliers_apply]
  split_ifs with h
  · rcases hi with hi | hi
    · exact absurd (Fin.lt_def.1 h.1) (Nat.not_lt.2 hi)
    have hcol : ∀ i : Fin N, k + p < (i : ℕ) →
        (gemPivotStage A partialPivotRow k).1 i ⟨k, hk⟩ = 0 := fun i hi => by
      rw [(gemPivotStage_partialPivotRow_hasBandwidth_invariant hp hq k).1 i _ (by omega)]
      exact hp' i _ hi
    have hrp : ((partialPivotRow (gemPivotStage A partialPivotRow k).1 ⟨k, hk⟩ : Fin N) : ℕ) ≤
        k + p := partialPivotRow_le_add _ ⟨k, hk⟩ p hcol
    have hne1 : i ≠ ⟨k, hk⟩ := fun e => by
      omega
    have hne2 : i ≠ partialPivotRow (gemPivotStage A partialPivotRow k).1 ⟨k, hk⟩ := fun e => by
      rw [e] at hi
      omega
    rw [submatrix_apply, gemPivotSwap, Equiv.swap_apply_of_ne_of_ne hne1 hne2, id, hcol i hi,
      zero_mul]
  · rfl

end BandStages

/-! ### Complete pivoting: Wilkinson's growth bound -/

section Wilkinson

variable {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}

/-- $A \in \mathbb{R}^{N \times N}$ **has dominant pivots** if at every stage of Gaussian
elimination *without* pivoting the pivot dominates the trailing block:
$$|a^{(k)}_{ij}| \le |a^{(k)}_{kk}| \quad \text{for all } k < N \text{ and } i, j \ge k.$$

This is what complete pivoting gives (`Matrix.hasDominantPivots_submatrix_gemFullPivotStage`),
and it is the hypothesis of Wilkinson's bound of [quarteroni2000numerical], §3.10. It is
strictly stronger than the condition $|u_{ij}| \le |u_{ii}|$ of
`Matrix.exists_permMatrix_mul_mul_permMatrix_isLU`, which concerns the final factor only. -/
def HasDominantPivots (A : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ (k : ℕ) (hk : k < N) (i j : Fin N), k ≤ (i : ℕ) → k ≤ (j : ℕ) →
    |gemStage A k i j| ≤ |gemStage A k ⟨k, hk⟩ ⟨k, hk⟩|

/-- The modulus $|a^{(k)}_{kk}|$ of the $k$-th pivot of Gaussian elimination without pivoting, as a
function of $k \in \mathbb{N}$, with the value $0$ for $k \ge N$. -/
noncomputable def absGemPivot (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) : ℝ :=
  if h : k < N then |gemStage A k ⟨k, h⟩ ⟨k, h⟩| else 0

/-- For $k < N$, `Matrix.absGemPivot A k` is $|a^{(k)}_{kk}|$. -/
theorem absGemPivot_of_lt (A : Matrix (Fin N) (Fin N) ℝ) {k : ℕ} (h : k < N) :
    absGemPivot A k = |gemStage A k ⟨k, h⟩ ⟨k, h⟩| := by simp [absGemPivot, h]

/-- `Matrix.absGemPivot A k` is nonnegative. -/
theorem absGemPivot_nonneg (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) : 0 ≤ absGemPivot A k := by
  rw [absGemPivot]
  split_ifs
  · exact abs_nonneg _
  · exact le_rfl

/-- If $A$ has dominant pivots, then $|a^{(k)}_{ij}| \le$ `Matrix.absGemPivot A k` for every $k < N$
and all $i, j \ge k$. -/
theorem HasDominantPivots.abs_gemStage_le (hA : A.HasDominantPivots) {k : ℕ} (hk : k < N)
    {i j : Fin N} (hi : k ≤ (i : ℕ)) (hj : k ≤ (j : ℕ)) :
    |gemStage A k i j| ≤ absGemPivot A k := by
  rw [absGemPivot_of_lt A hk]
  exact hA k hk i j hi hj

/-- **The shape of $A^{(k)}$ under dominant pivots.** If $A$ has dominant pivots, then for every $k$
the stage $A^{(k)}$ vanishes below the diagonal in its first $k$ columns: $a^{(k)}_{ij} = 0$
whenever $j < k$ and $j < i$.

This is `Matrix.gemStage_apply_eq_zero_of_lt` with the hypothesis of nonzero pivots replaced by
dominance. Dominance also covers a zero pivot: then the whole trailing block is zero, and the
elimination step does not change the matrix. -/
theorem HasDominantPivots.gemStage_apply_eq_zero (hA : A.HasDominantPivots) (k : ℕ) {i j : Fin N}
    (hjk : (j : ℕ) < k) (hji : j < i) : gemStage A k i j = 0 := by
  induction k generalizing i j with
  | zero => exact absurd hjk (Nat.not_lt_zero _)
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with hjk' | hjk'
    · by_cases hkN : k < N
      · rw [gemStage_succ_of_lt A hkN,
          elimStep_apply_of_pivot_row_eq_zero _ _ _ (ih hjk' (Fin.mk_lt_of_lt_val hjk'))]
        exact ih hjk' hji
      · rw [gemStage_succ_of_le A (not_lt.1 hkN)]
        exact ih hjk' hji
    · have hkN : k < N := hjk' ▸ j.isLt
      have hj : j = (⟨k, hkN⟩ : Fin N) := Fin.ext hjk'
      subst hj
      rw [gemStage_succ_of_lt A hkN, elimStep_apply_of_lt _ hji]
      rcases eq_or_ne (gemStage A k ⟨k, hkN⟩ ⟨k, hkN⟩) 0 with h0 | h0
      · have := hA k hkN i ⟨k, hkN⟩ (le_of_lt (Fin.lt_def.1 hji)) le_rfl
        rw [h0, abs_zero, abs_nonpos_iff] at this
        rw [this, h0]
        ring
      · rw [mul_assoc, inv_mul_cancel₀ h0, mul_one, sub_self]

/-- **A zero pivot stops the elimination.** Let $A$ have dominant pivots, and let $m < N$ with
$a^{(m)}_{mm} = 0$. Then $A^{(k)} = A^{(m)}$ for every $k \ge m$.

By dominance, the whole trailing block of $A^{(m)}$ vanishes, so the later elimination steps do
not change the matrix. -/
theorem HasDominantPivots.gemStage_eq_of_pivot_eq_zero (hA : A.HasDominantPivots) {m : ℕ}
    (hm : m < N) (h0 : gemStage A m ⟨m, hm⟩ ⟨m, hm⟩ = 0) {k : ℕ} (hk : m ≤ k) :
    gemStage A k = gemStage A m := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    by_cases hkN : k < N
    · rw [gemStage_succ_of_lt A hkN, ih]
      have hrow : ∀ j : Fin N, gemStage A m ⟨k, hkN⟩ j = 0 := by
        intro j
        rcases lt_or_ge (j : ℕ) m with hj | hj
        · exact hA.gemStage_apply_eq_zero m hj (Fin.lt_def.2 (lt_of_lt_of_le hj hk))
        · have := hA m hm ⟨k, hkN⟩ j hk hj
          rw [h0, abs_zero, abs_nonpos_iff] at this
          exact this
      ext i j
      exact elimStep_apply_of_pivot_row_eq_zero _ _ _ (hrow j)
    · rw [gemStage_succ_of_le A (not_lt.1 hkN), ih]

/-- If $A$ has dominant pivots, $m \le k < N$ and the $m$-th pivot is zero, then the $k$-th pivot is
zero. -/
theorem HasDominantPivots.absGemPivot_eq_zero_of_le (hA : A.HasDominantPivots) {m k : ℕ}
    (hm : m < N) (hk : k < N) (hmk : m ≤ k) (h0 : absGemPivot A m = 0) : absGemPivot A k = 0 := by
  rw [absGemPivot_of_lt A hm, abs_eq_zero] at h0
  rw [absGemPivot_of_lt A hk, hA.gemStage_eq_of_pivot_eq_zero hm h0 hmk, abs_eq_zero]
  have := hA m hm ⟨k, hk⟩ ⟨k, hk⟩ hmk hmk
  rw [h0, abs_zero, abs_nonpos_iff] at this
  exact this

/-- **Hadamard's inequality on the reduced matrices.** Let $A$ have dominant pivots, let
$k + j \le N$ with $j \ge 1$, and suppose that the pivots $\mu_{k+t} = |a^{(k+t)}_{k+t,k+t}|$
are nonzero for $t < j$. Then
$$\prod_{t < j} \mu_{k+t} \le \big( \sqrt{j} \, \mu_k \big)^j.$$

This is the first half of Wilkinson's argument for (9.14) of [higham2002accuracy]. The block of
$A^{(k)}$ on the indices $k, \dots, k + j - 1$ has these pivots as the pivots of its own
elimination, so its determinant is their product. Its entries are bounded by $\mu_k$, and
`Matrix.norm_det_le_of_forall_norm_le` applies. -/
theorem prod_absGemPivot_le (hA : A.HasDominantPivots) {k j : ℕ} (h : k + j ≤ N) (hj : 0 < j)
    (hne : ∀ t, t < j → absGemPivot A (k + t) ≠ 0) :
    ∏ t ∈ Finset.range j, absGemPivot A (k + t) ≤ (Real.sqrt j * absGemPivot A k) ^ j := by
  have hkN : k < N := by omega
  set e := blockEmb k j N h with he
  set B := (gemStage A k).submatrix e e with hB
  have hpivB : ∀ (m : ℕ) (hm : m < j), m + 1 < j → gemStage B m ⟨m, hm⟩ ⟨m, hm⟩ ≠ 0 := by
    intro m hm _
    have hkm : k + m < N := by omega
    rw [hB, gemStage_submatrix_blockEmb A h m hm.le, submatrix_apply]
    have := hne m hm
    rw [absGemPivot_of_lt A hkm, ne_eq, abs_eq_zero] at this
    exact this
  have hupper : (gemStage B j).IsUpperTriangular := fun i j' hij =>
    gemStage_apply_eq_zero_of_lt B (fun m hm _ hmj => hpivB m hm hmj) j'.isLt hij
  have hdetB : B.det = ∏ i : Fin j, gemStage A (k + (i : ℕ)) (e i) (e i) := by
    have h1 : gemLowerStage B j * gemStage B j = B := gemLowerStage_mul_gemStage B j
    rw [← h1, det_mul, (isUnitLowerTriangular_gemLowerStage B j).det_eq_one, one_mul,
      det_of_isUpperTriangular hupper]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [gemStage_submatrix_blockEmb A h j le_rfl, submatrix_apply]
    exact gemStage_apply_of_le A (le_refl (k + (i : ℕ))) (by omega) _
  have hentry : ∀ i i' : Fin j, ‖B i i'‖ ≤ absGemPivot A k := by
    intro i i'
    rw [hB, submatrix_apply, Real.norm_eq_abs]
    exact hA.abs_gemStage_le hkN (Nat.le_add_right k _) (Nat.le_add_right k _)
  have hHad := norm_det_le_of_forall_norm_le (absGemPivot_nonneg A k) hentry
  rw [Fintype.card_fin] at hHad
  rw [Real.norm_eq_abs, hdetB, abs_prod] at hHad
  refine le_trans (le_of_eq ?_) hHad
  rw [← Fin.prod_univ_eq_prod_range (fun t => absGemPivot A (k + t)) j]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hki : k + (i : ℕ) < N := by omega
  rw [absGemPivot_of_lt A hki]
  rfl

/-- **Wilkinson's growth bound**
$$W(n) = n^{1/2} \big( 2 \cdot 3^{1/2} \cdot 4^{1/3} \cdots n^{1/(n-1)} \big)^{1/2} = \sqrt{n}
  \, \Big( \prod_{t=0}^{n-2} (t + 2)^{1/(t+1)} \Big)^{1/2},$$
the bound on the growth factor of Gaussian elimination with complete pivoting on a matrix of
order $n$ ([quarteroni2000numerical], §3.10; [higham2002accuracy], (9.14)).

The product is empty for $n \le 1$, so $W(0) = 0$ and $W(1) = 1$. -/
noncomputable def wilkinsonGrowthBound (n : ℕ) : ℝ :=
  Real.sqrt n * Real.sqrt (∏ t ∈ Finset.range (n - 1), ((t : ℝ) + 2) ^ ((t : ℝ) + 1)⁻¹)

/-- Every factor of Wilkinson's product is at least one: $(t + 2)^{1/(t+1)} \ge 1$. -/
theorem one_le_wilkinsonFactor (t : ℕ) : (1 : ℝ) ≤ ((t : ℝ) + 2) ^ ((t : ℝ) + 1)⁻¹ := by
  calc (1 : ℝ) = (1 : ℝ) ^ ((t : ℝ) + 1)⁻¹ := (Real.one_rpow _).symm
    _ ≤ ((t : ℝ) + 2) ^ ((t : ℝ) + 1)⁻¹ :=
        Real.rpow_le_rpow zero_le_one (by linarith) (by positivity)

/-- Wilkinson's product is at least one: $\prod_{t < n} (t + 2)^{1/(t+1)} \ge 1$. -/
theorem one_le_wilkinsonProd (n : ℕ) :
    (1 : ℝ) ≤ ∏ t ∈ Finset.range n, ((t : ℝ) + 2) ^ ((t : ℝ) + 1)⁻¹ := by
  have h1 : (∏ _t ∈ Finset.range n, (1 : ℝ)) ≤
      ∏ t ∈ Finset.range n, ((t : ℝ) + 2) ^ ((t : ℝ) + 1)⁻¹ :=
    Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun t _ => one_le_wilkinsonFactor t
  simpa using h1

/-- Wilkinson's product $\prod_{t < n} (t + 2)^{1/(t+1)}$ is positive. -/
theorem wilkinsonProd_pos (n : ℕ) :
    (0 : ℝ) < ∏ t ∈ Finset.range n, ((t : ℝ) + 2) ^ ((t : ℝ) + 1)⁻¹ :=
  lt_of_lt_of_le zero_lt_one (one_le_wilkinsonProd n)

/-- Wilkinson's product is monotone in the number of factors: if $a \le b$, then $\prod_{t < a} (t +
2)^{1/(t+1)} \le \prod_{t < b} (t + 2)^{1/(t+1)}$. -/
theorem wilkinsonProd_mono {a b : ℕ} (h : a ≤ b) :
    (∏ t ∈ Finset.range a, ((t : ℝ) + 2) ^ ((t : ℝ) + 1)⁻¹) ≤
      ∏ t ∈ Finset.range b, ((t : ℝ) + 2) ^ ((t : ℝ) + 1)⁻¹ := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ b hb ih =>
    rw [Finset.prod_range_succ]
    exact ih.trans (by nlinarith [wilkinsonProd_pos b, one_le_wilkinsonFactor b])

/-- $W(n) \ge 0$. -/
theorem wilkinsonGrowthBound_nonneg (n : ℕ) : 0 ≤ wilkinsonGrowthBound n := by
  unfold wilkinsonGrowthBound
  positivity

/-- If $n \ge 1$, then $W(n) > 0$. -/
theorem wilkinsonGrowthBound_pos {n : ℕ} (hn : 0 < n) : 0 < wilkinsonGrowthBound n :=
  mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hn)) (Real.sqrt_pos.2 (wilkinsonProd_pos _))

/-- Wilkinson's bound is monotone in the order: if $m \le n$, then $W(m) \le W(n)$. -/
theorem wilkinsonGrowthBound_mono {m n : ℕ} (h : m ≤ n) :
    wilkinsonGrowthBound m ≤ wilkinsonGrowthBound n := by
  have hmn : ((m : ℝ)) ≤ (n : ℝ) := by exact_mod_cast h
  refine (_root_.mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmn)
    (Real.sqrt_nonneg _)).trans ?_
  exact _root_.mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (wilkinsonProd_mono (by omega))) (Real.sqrt_nonneg _)

/-- The logarithm of Wilkinson's bound: for $n \ge 1$,
$$\log W(n) = \frac{\log n}{2} + \sum_{t < n - 1} \frac{\log (t + 2)}{2 (t + 1)}.$$
-/
theorem log_wilkinsonGrowthBound {n : ℕ} (hn : 0 < n) :
    Real.log (wilkinsonGrowthBound n) = Real.log n / 2 +
      ∑ t ∈ Finset.range (n - 1), Real.log ((t : ℝ) + 2) / (2 * ((t : ℝ) + 1)) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [wilkinsonGrowthBound, Real.log_mul (Real.sqrt_pos.2 hn').ne'
      (Real.sqrt_pos.2 (wilkinsonProd_pos _)).ne',
    Real.log_sqrt hn'.le, Real.log_sqrt (wilkinsonProd_pos _).le,
    Real.log_prod (fun t _ => by positivity), Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have ht1 : ((t : ℝ) + 1) ≠ 0 := by positivity
  rw [Real.log_rpow (by positivity)]
  field_simp

/-- **Wilkinson's telescoping estimate, in logarithmic form.** Let $A$ have dominant pivots, let
$r < N$, and suppose that the pivots $\mu_m = |a^{(m)}_{mm}|$ are nonzero for $m \le r$. Then
$$\log \mu_r \le \log \mu_0 + \frac{\log (r + 1)}{2} + \sum_{t < r} \frac{\log (t + 2)}{2 (t +
  1)}.$$

Neither [quarteroni2000numerical] nor [higham2002accuracy] proves (9.14); both refer to a paper
of Wilkinson of 1961. The proof here goes as follows. Let $L_s$ be the sum of the logarithms of
the last $s + 1$ pivots up to $\mu_r$. Then `Matrix.prod_absGemPivot_le`, on the run of $s + 2$
pivots that ends at $r$, gives $L_{s+1} \ge \frac{s+2}{s+1} \big( L_s - \frac{1}{2} \log (s + 2)
\big)$. By induction, $L_s \ge (s + 1) \log \mu_r - (s + 1) \sum_{t < s} \frac{\log (t + 2)}{2
(t + 1)}$. With $s = r$, `Matrix.prod_absGemPivot_le` on the whole run gives the statement. -/
theorem log_absGemPivot_le (hA : A.HasDominantPivots) {r : ℕ} (hr : r < N)
    (hne : ∀ m, m ≤ r → absGemPivot A m ≠ 0) :
    Real.log (absGemPivot A r) ≤ Real.log (absGemPivot A 0) + Real.log ((r : ℝ) + 1) / 2 +
      ∑ t ∈ Finset.range r, Real.log ((t : ℝ) + 2) / (2 * ((t : ℝ) + 1)) := by
  have hpos : ∀ m, m ≤ r → 0 < absGemPivot A m := fun m hm =>
    lt_of_le_of_ne (absGemPivot_nonneg A m) (Ne.symm (hne m hm))
  have hP : ∀ k j : ℕ, k + j ≤ r + 1 → 0 < j →
      ∑ i ∈ Finset.range j, Real.log (absGemPivot A (k + i)) ≤
        (j : ℝ) / 2 * Real.log j + j * Real.log (absGemPivot A k) := by
    intro k j hkj hj
    have hkN : k + j ≤ N := by omega
    have hnz : ∀ t, t < j → absGemPivot A (k + t) ≠ 0 := fun t ht => hne _ (by omega)
    have hprodpos : (0 : ℝ) < ∏ t ∈ Finset.range j, absGemPivot A (k + t) :=
      Finset.prod_pos fun t ht => hpos _ (by simp only [Finset.mem_range] at ht; omega)
    have hsq : (0 : ℝ) < Real.sqrt j := Real.sqrt_pos.2 (by exact_mod_cast hj)
    have hlog := Real.log_le_log hprodpos (prod_absGemPivot_le hA hkN hj hnz)
    rw [Real.log_prod (fun t ht => (hpos _ (by simp only [Finset.mem_range] at ht; omega)).ne'),
      Real.log_pow, Real.log_mul hsq.ne' (hne k (by omega)),
      Real.log_sqrt (by positivity)] at hlog
    linarith
  have hclaim : ∀ s k : ℕ, k + s = r →
      ((s : ℝ) + 1) * Real.log (absGemPivot A r) -
          ((s : ℝ) + 1) * ∑ t ∈ Finset.range s, Real.log ((t : ℝ) + 2) / (2 * ((t : ℝ) + 1)) ≤
        ∑ i ∈ Finset.range (s + 1), Real.log (absGemPivot A (k + i)) := by
    intro s
    induction s with
    | zero =>
      intro k hk
      have hkr : k = r := by omega
      subst hkr
      simp
    | succ s ih =>
      intro k hk
      have hS1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
      have hS2 : (0 : ℝ) < (s : ℝ) + 2 := by positivity
      have IH := ih (k + 1) (by omega)
      have hPk := hP k (s + 1 + 1) (by omega) (by omega)
      have hcast : ((s + 1 + 1 : ℕ) : ℝ) = (s : ℝ) + 2 := by push_cast; ring
      rw [hcast] at hPk
      have hsplit : (∑ i ∈ Finset.range (s + 1 + 1), Real.log (absGemPivot A (k + i))) =
          (∑ i ∈ Finset.range (s + 1), Real.log (absGemPivot A (k + 1 + i))) +
            Real.log (absGemPivot A k) := by
        rw [Finset.sum_range_succ' (fun i => Real.log (absGemPivot A (k + i))) (s + 1)]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by rw [show k + (i + 1) = k + 1 + i by omega]
      rw [Finset.sum_range_succ]
      push_cast
      set G := ∑ i ∈ Finset.range (s + 1 + 1), Real.log (absGemPivot A (k + i)) with hGd
      set G' := ∑ i ∈ Finset.range (s + 1), Real.log (absGemPivot A (k + 1 + i)) with hG'd
      set m := Real.log (absGemPivot A k) with hmd
      set L := Real.log (absGemPivot A r) with hLd
      set Ts := ∑ t ∈ Finset.range s, Real.log ((t : ℝ) + 2) / (2 * ((t : ℝ) + 1)) with hTd
      set c := Real.log ((s : ℝ) + 2) with hcd
      have hGm : ((s : ℝ) + 2) * m = ((s : ℝ) + 2) * (G - G') := by rw [hsplit]; ring
      have step2 := _root_.mul_le_mul_of_nonneg_left IH hS2.le
      have hcdiv : ((s : ℝ) + 1) * (((s : ℝ) + 1 + 1) * (c / (2 * ((s : ℝ) + 1)))) =
          ((s : ℝ) + 2) * c / 2 := by
        field_simp
        ring
      refine le_of_mul_le_mul_left ?_ hS1
      nlinarith [step2, hcdiv]
  have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hcast : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
  have hfin := hclaim r 0 (by omega)
  have hP0 := hP 0 (r + 1) (by omega) (by omega)
  rw [hcast] at hP0
  simp only [Nat.zero_add] at hfin hP0
  refine le_of_mul_le_mul_left ?_ hr1
  nlinarith [hfin, hP0]

/-- **Wilkinson's estimate for one pivot.** If $A$ has dominant pivots and $r < N$, then
$$|a^{(r)}_{rr}| \le W(r + 1) \, |a^{(0)}_{00}|.$$
-/
theorem absGemPivot_le_wilkinson (hA : A.HasDominantPivots) {r : ℕ} (hr : r < N) :
    absGemPivot A r ≤ wilkinsonGrowthBound (r + 1) * absGemPivot A 0 := by
  rcases eq_or_ne (absGemPivot A r) 0 with h0 | h0
  · rw [h0]
    exact mul_nonneg (wilkinsonGrowthBound_nonneg _) (absGemPivot_nonneg A 0)
  have hne : ∀ m, m ≤ r → absGemPivot A m ≠ 0 := fun m hm hzero =>
    h0 (hA.absGemPivot_eq_zero_of_le (by omega) hr hm hzero)
  have hposr : 0 < absGemPivot A r := lt_of_le_of_ne (absGemPivot_nonneg A r) (Ne.symm h0)
  have hpos0 : 0 < absGemPivot A 0 :=
    lt_of_le_of_ne (absGemPivot_nonneg A 0) (Ne.symm (hne 0 (Nat.zero_le r)))
  have hB : 0 < wilkinsonGrowthBound (r + 1) := wilkinsonGrowthBound_pos (by omega)
  have hcast : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
  rw [← Real.log_le_log_iff hposr (by positivity), Real.log_mul hB.ne' hpos0.ne',
    log_wilkinsonGrowthBound (n := r + 1) (by omega), hcast, Nat.add_sub_cancel]
  have := log_absGemPivot_le hA hr hne
  linarith

/-- **Wilkinson's bound on the growth factor under dominant pivots.** If
$A \in \mathbb{R}^{N \times N}$ has dominant pivots, which is what complete pivoting gives, then
$$\rho(A) \le W(N) = N^{1/2} \big( 2 \cdot 3^{1/2} \cdots N^{1/(N-1)} \big)^{1/2}.$$

This is Wilkinson's bound of [quarteroni2000numerical], §3.10, and (9.14) of
[higham2002accuracy]. By dominance at stage $0$, the largest entry of $A$ is the first pivot.
Every entry of every stage is either zero, by the shape of the reduced matrices, or bounded by
the pivot of an earlier stage, and `Matrix.absGemPivot_le_wilkinson` bounds each pivot in terms
of the first. -/
theorem growthFactor_le_of_completePivoting {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.HasDominantPivots) : growthFactor A ≤ wilkinsonGrowthBound N := by
  refine growthFactor_le_of_forall_abs_le A (wilkinsonGrowthBound_nonneg N) fun k i j hk => ?_
  have hN : 0 < N := by omega
  have hsup : A.supAbs = absGemPivot A 0 := by
    refine le_antisymm (supAbs_le (absGemPivot_nonneg A 0) fun i' j' =>
      hA.abs_gemStage_le hN (Nat.zero_le _) (Nat.zero_le _)) ?_
    rw [absGemPivot_of_lt A hN]
    exact abs_apply_le_supAbs A _ _
  have main : ∀ m : ℕ, m < N → ∀ i' j' : Fin N, m ≤ (i' : ℕ) → m ≤ (j' : ℕ) →
      |gemStage A m i' j'| ≤ wilkinsonGrowthBound N * A.supAbs := by
    intro m hm i' j' hi' hj'
    rw [hsup]
    calc |gemStage A m i' j'| ≤ absGemPivot A m := hA.abs_gemStage_le hm hi' hj'
      _ ≤ wilkinsonGrowthBound (m + 1) * absGemPivot A 0 := absGemPivot_le_wilkinson hA hm
      _ ≤ wilkinsonGrowthBound N * absGemPivot A 0 :=
          _root_.mul_le_mul_of_nonneg_right (wilkinsonGrowthBound_mono (by omega))
            (absGemPivot_nonneg A 0)
  have hzero : (0 : ℝ) ≤ wilkinsonGrowthBound N * A.supAbs :=
    mul_nonneg (wilkinsonGrowthBound_nonneg N) (supAbs_nonneg A)
  rcases le_or_gt k (i : ℕ) with hi | hi
  · rcases le_or_gt k (j : ℕ) with hj | hj
    · exact main k hk i j hi hj
    · rw [hA.gemStage_apply_eq_zero k hj (Fin.lt_def.2 (lt_of_lt_of_le hj hi)), abs_zero]
      exact hzero
  · rw [gemStage_apply_of_le A (le_refl (i : ℕ)) hi.le j]
    rcases le_or_gt (i : ℕ) (j : ℕ) with hij | hij
    · exact main (i : ℕ) i.isLt i j le_rfl hij
    · rw [hA.gemStage_apply_eq_zero (i : ℕ) hij (Fin.lt_def.2 hij), abs_zero]
      exact hzero

/-- **Complete pivoting gives dominant pivots.** Let `piv` be a complete-pivoting strategy, let
$A \in \mathbb{R}^{N \times N}$, and let $\sigma_N$ and $\tau_N$ be the permutations accumulated
by `Matrix.gemFullPivotStage`. Then the matrix $(a_{\sigma_N(i) \tau_N(j)})$, which is $P A Q$,
has dominant pivots. -/
theorem hasDominantPivots_submatrix_gemFullPivotStage (A : Matrix (Fin N) (Fin N) ℝ)
    {piv : Matrix (Fin N) (Fin N) ℝ → Fin N → Fin N × Fin N} (hpiv : IsCompletePivot piv) :
    (A.submatrix (gemFullPivotStage A piv N).2.1
      (gemFullPivotStage A piv N).2.2).HasDominantPivots := by
  have hrow : ∀ M k, k ≤ (piv M k).1 := fun M k => (hpiv M k).1
  have hcol : ∀ M k, k ≤ (piv M k).2 := fun M k => (hpiv M k).2.1
  intro k hk i j hi hj
  rw [gemStage_submatrix_apply_self A piv hrow hcol hk,
    gemStage_submatrix_eq_submatrix_gemFullPivotStage A piv hrow hcol, submatrix_apply]
  have hbound := (hpiv (gemFullPivotStage A piv k).1 ⟨k, hk⟩).2.2
    (((gemFullPivotStage A piv k).2.1⁻¹ * (gemFullPivotStage A piv N).2.1) i)
    (((gemFullPivotStage A piv k).2.2⁻¹ * (gemFullPivotStage A piv N).2.2) j)
    (Fin.le_def.2 (le_gemFullPivotStage_rowPerm_inv_mul_apply A piv hrow hk.le hi))
    (Fin.le_def.2 (le_gemFullPivotStage_colPerm_inv_mul_apply A piv hcol hk.le hj))
  simpa only [Real.norm_eq_abs] using hbound

/-- **The growth factor of complete pivoting satisfies Wilkinson's bound.** Let `piv` be a
complete-pivoting strategy, let $A \in \mathbb{R}^{N \times N}$, and let $\sigma_N$ and $\tau_N$
be the permutations accumulated by `Matrix.gemFullPivotStage`. Then the growth factor of
Gaussian elimination without pivoting on $B = (a_{\sigma_N(i) \tau_N(j)})$, which is $P A Q$,
satisfies
$$\rho(B) \le W(N) = N^{1/2} \big( 2 \cdot 3^{1/2} \cdots N^{1/(N-1)} \big)^{1/2}.$$

This is [quarteroni2000numerical], §3.10, and (9.14) of [higham2002accuracy]. The stages of
elimination on $B$ are the completely pivoted stages up to the order of the rows and of the
columns (`Matrix.gemStage_submatrix_eq_submatrix_gemFullPivotStage`). The bound grows more
slowly than the bound $2^{N-1}$ of partial pivoting. -/
theorem growthFactor_le_wilkinson_of_isCompletePivot (A : Matrix (Fin N) (Fin N) ℝ)
    {piv : Matrix (Fin N) (Fin N) ℝ → Fin N → Fin N × Fin N} (hpiv : IsCompletePivot piv) :
    growthFactor (A.submatrix (gemFullPivotStage A piv N).2.1
      (gemFullPivotStage A piv N).2.2) ≤ wilkinsonGrowthBound N :=
  growthFactor_le_of_completePivoting (hasDominantPivots_submatrix_gemFullPivotStage A hpiv)

end Wilkinson

/-! ### Wilkinson's bound on each stage -/

section WilkinsonStages

variable {N : ℕ}

/-- **Wilkinson's bound, stage by stage.** Let `piv` be a complete-pivoting strategy, let
$A \in \mathbb{R}^{N \times N}$, and let $k < N$. Then every entry of the trailing block of the
stage $\hat A^{(k)}$ after $k$ steps satisfies
$$|\hat a^{(k)}_{ij}| \le W(k + 1) \, \mu(A) \quad \text{for all } i, j \ge k.$$

This is (3.4.10) of [golub2013matrix] with the index corrected. The source prints the bound
$f(k)$, which is $W(k)$ in the notation here, in place of $W(k + 1)$. That bound is false at
$k = 1$: one step of complete pivoting on $\begin{bmatrix} 1 & 1 \\ 1 & -1 \end{bmatrix}$
produces the entry $-2$, but $f(1) = 1$. -/
theorem abs_gemFullPivotStage_le_wilkinson (A : Matrix (Fin N) (Fin N) ℝ)
    {piv : Matrix (Fin N) (Fin N) ℝ → Fin N → Fin N × Fin N} (hpiv : IsCompletePivot piv)
    {k : ℕ} (hk : k < N) {i j : Fin N} (hi : k ≤ (i : ℕ)) (hj : k ≤ (j : ℕ)) :
    |(gemFullPivotStage A piv k).1 i j| ≤ wilkinsonGrowthBound (k + 1) * A.supAbs := by
  have hrow : ∀ M k, k ≤ (piv M k).1 := fun M k => (hpiv M k).1
  have hcol : ∀ M k, k ≤ (piv M k).2 := fun M k => (hpiv M k).2.1
  set B := A.submatrix (gemFullPivotStage A piv N).2.1 (gemFullPivotStage A piv N).2.2 with hB
  set σ := (gemFullPivotStage A piv k).2.1⁻¹ * (gemFullPivotStage A piv N).2.1 with hσ
  set ρ := (gemFullPivotStage A piv k).2.2⁻¹ * (gemFullPivotStage A piv N).2.2 with hρ
  have hD := hasDominantPivots_submatrix_gemFullPivotStage A hpiv
  have hi' : k ≤ ((σ⁻¹ i : Fin N) : ℕ) := le_apply_of_forall_lt_apply_eq (fun x hx => by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (gemFullPivotStage_rowPerm_inv_mul_apply A piv hrow hk.le hx).symm) hi
  have hj' : k ≤ ((ρ⁻¹ j : Fin N) : ℕ) := le_apply_of_forall_lt_apply_eq (fun x hx => by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (gemFullPivotStage_colPerm_inv_mul_apply A piv hcol hk.le hx).symm) hj
  have heq : gemStage B k (σ⁻¹ i) (ρ⁻¹ j) = (gemFullPivotStage A piv k).1 i j := by
    rw [hB, gemStage_submatrix_eq_submatrix_gemFullPivotStage A piv hrow hcol, submatrix_apply,
      ← hσ, ← hρ, Equiv.Perm.inv_def, Equiv.Perm.inv_def, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  rw [← heq]
  calc |gemStage B k (σ⁻¹ i) (ρ⁻¹ j)| ≤ absGemPivot B k := hD.abs_gemStage_le hk hi' hj'
    _ ≤ wilkinsonGrowthBound (k + 1) * absGemPivot B 0 := absGemPivot_le_wilkinson hD hk
    _ ≤ wilkinsonGrowthBound (k + 1) * A.supAbs := by
      refine mul_le_mul_of_nonneg_left ?_ (wilkinsonGrowthBound_nonneg _)
      rw [absGemPivot_of_lt B (by omega)]
      exact abs_apply_le_supAbs A _ _

end WilkinsonStages

end Matrix
