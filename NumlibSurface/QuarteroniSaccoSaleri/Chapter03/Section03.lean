/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.FloatingPoint.LU
import Numlib.LinearAlgebra.Matrix.Cauchy
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section02

/-!
# Quarteroni, Sacco and Saleri, Section 3.3: Gaussian elimination and the LU factorization

This module formalizes Section 3.3 of [quarteroni2000numerical]. The Gaussian elimination method
(GEM) transforms a system $Ax = b$ with $A \in \mathbb{R}^{n \times n}$ into an equivalent upper
triangular system $Ux = b^{(n)}$ through stages $A^{(k+1)} = M_k A^{(k)}$, where the Gaussian
transformation $M_k = I_n - m_k e_k^T$ holds the multipliers $m_{ik} = a^{(k)}_{ik} / a^{(k)}_{kk}$.
When the pivots $a^{(k)}_{kk}$ are nonzero, the product of the inverse transformations is a unit
lower triangular matrix $L$ with $A = LU$. The module states the elimination step (3.30)–(3.31), the
equivalence (3.29) of the systems, GEM as a factorization (3.35)–(3.37), the existence and
uniqueness criterion of Theorem 3.4 and its examples, Property 3.2 on diagonally dominant matrices,
the rounding-error bounds (3.40)–(3.41), and the compact Doolittle and Crout forms (3.42)–(3.43).

The proofs specialize the backbone modules `Numlib.LinearAlgebra.Matrix.LU.Elimination` (the
elimination stages, the Gaussian transformations, the multiplier matrix, the Doolittle and Crout
recurrences), `Numlib.LinearAlgebra.Matrix.LU` (the specification `Matrix.IsLU`, the leading
principal minors, Theorem 3.4, Property 3.2), `Numlib.LinearAlgebra.Matrix.Cauchy` (the Hilbert
matrix) and `Numlib.FloatingPoint.LU` (the bounds (3.40)–(3.41)).

## Main definitions

* (3.30), `QuarteroniSaccoSaleri.Chapter03.gemMultipliers`: the vector $m_k$ of the multipliers of
  stage $k$.
* (3.29), `QuarteroniSaccoSaleri.Chapter03.gemRhs`: the right-hand sides $b^{(k)}$ of the equivalent
  systems.

## Main results

* (3.30)–(3.31), `QuarteroniSaccoSaleri.Chapter03.equation_3_31`: one stage of GEM changes the rows
  below the pivot by $a^{(k+1)}_{ij} = a^{(k)}_{ij} - m_{ik} a^{(k)}_{kj}$ and keeps the other rows.
* (3.29), `QuarteroniSaccoSaleri.Chapter03.equation_3_29`: every system $A^{(k)} x = b^{(k)}$ has
  the same solutions as $Ax = b$.
* Remark 3.2, `QuarteroniSaccoSaleri.Chapter03.remark_3_2`: the Hilbert matrix
  $h_{ij} = 1/(i + j - 1)$ is nonsingular and symmetric positive definite.
* (3.33), `QuarteroniSaccoSaleri.Chapter03.equation_3_33`: a nonsingular matrix with nonzero
  diagonal can produce a zero pivot.
* (3.35), `QuarteroniSaccoSaleri.Chapter03.equation_3_35`: $A^{(k+1)} = M_k A^{(k)}$ with
  $M_k = I_n - m_k e_k^T$.
* (3.36), `QuarteroniSaccoSaleri.Chapter03.equation_3_36`: $M_k$ is unit lower triangular,
  $M_k^{-1} = 2 I_n - M_k = I_n + m_k e_k^T$, and $(m_i e_i^T)(m_j e_j^T) = 0$ for $i < j$.
* (3.37), `QuarteroniSaccoSaleri.Chapter03.equation_3_37`: if the pivots are nonzero, GEM gives the
  LU factorization $A = LU$, with the multipliers below the diagonal of $L$.
* Theorem 3.4, `QuarteroniSaccoSaleri.Chapter03.theorem_3_4`: the LU factorization with $l_{ii} = 1$
  exists and is unique if and only if the leading principal submatrices of orders $1, \ldots, n - 1$
  are nonsingular.
* (3.38)–(3.39), `QuarteroniSaccoSaleri.Chapter03.equation_3_39`: the LU factorization restricts to
  the leading principal submatrices, $\det A = u_{11} \cdots u_{nn}$, and $u_{ii} = d_i / d_{i-1}$.
* Example 3.3, `QuarteroniSaccoSaleri.Chapter03.example_3_3_b`: a singular matrix with a unique LU
  factorization.
* Example 3.3, `QuarteroniSaccoSaleri.Chapter03.example_3_3_c`: a nonsingular matrix with no LU
  factorization.
* Example 3.3, `QuarteroniSaccoSaleri.Chapter03.example_3_3_d`: a singular matrix with infinitely
  many LU factorizations.
* Property 3.2, `QuarteroniSaccoSaleri.Chapter03.property_3_2_row`: a nonsingular matrix that is
  diagonally dominant by rows has an LU factorization.
* Property 3.2, `QuarteroniSaccoSaleri.Chapter03.property_3_2_col`: a nonsingular matrix that is
  diagonally dominant by columns has an LU factorization with $|l_{ij}| \le 1$.
* (3.40), `QuarteroniSaccoSaleri.Chapter03.equation_3_40`: the computed factors satisfy
  $\hat L \hat U = A + \delta A$ with $|\delta A| \le \frac{nu}{1 - nu} |\hat L| |\hat U|$.
* (3.41), `QuarteroniSaccoSaleri.Chapter03.equation_3_41`: for nonnegative computed factors,
  $|\delta A| \le \frac{nu}{1 - 2nu} |A|$.
* (3.42), `QuarteroniSaccoSaleri.Chapter03.equation_3_42`: $A = LU$ if and only if
  $a_{ij} = \sum_{r \le \min(i, j)} l_{ir} u_{rj}$ for all $i, j$.
* (3.43), `QuarteroniSaccoSaleri.Chapter03.equation_3_43`: the Doolittle recurrence, which gives the
  LU factorization of GEM.
* Section 3.3.4, `QuarteroniSaccoSaleri.Chapter03.crout`: the Crout recurrence, which gives $A = LU$
  with $U$ unit upper triangular.

## Conventions

* Indices are $0$-based. The rows and columns of $A$ are $0, \ldots, n - 1$, and the stage $A^{(k)}$
  is `Matrix.gemStage A k`, so $A^{(0)} = A$ and $A^{(n)} = U$. The book's stage $A^{(k)}$,
  $k = 1, \ldots, n$, is the stage $A^{(k-1)}$ here.
* The multipliers $m_{ik}$ of stage $k$ form the vector
  `QuarteroniSaccoSaleri.Chapter03.gemMultipliers A k`, the book's $m_k$, which is zero in the
  positions $i \le k$. The Gaussian transformation $M_k = I_n - m_k e_k^T$ is
  `Matrix.gaussTransform (gemStage A k) k`. The right-hand sides $b^{(k)}$ are
  `QuarteroniSaccoSaleri.Chapter03.gemRhs A b k`.
* The pivots are `gemStage A k k k`. The condition "the pivots $a^{(k)}_{kk}$,
  $k = 1, \ldots, n - 1$, are nonzero" is `∀ k : Fin n, (k : ℕ) + 1 < n → gemStage A k k k ≠ 0`. The
  last pivot is never a divisor, and it vanishes for a singular matrix whose strict leading
  principal submatrices are nonsingular (the matrix $B$ of Example 3.3).
* "The LU factorization of $A$ with $l_{ii} = 1$" is the specification `Matrix.IsLU A L U`: $L$ is
  unit lower triangular, $U$ is upper triangular, and $LU = A$.
* The leading principal submatrix $A_i$ of order $i$ is `Matrix.leadingPrincipalSubmatrix A k` with
  $k = i - 1$, indexed by `{j // j ≤ k}`. The leading principal minor $d_i = \det A_i$ is
  `Matrix.leadingPrincipalMinor A k`. The strict leading principal submatrix of order $k$ is
  `Matrix.strictLeadingPrincipalSubmatrix A k`. As $k$ ranges over `Fin n`, the strict submatrices
  are exactly the $A_i$ with $i = 0, \ldots, n - 1$, and the block of order $0$ is the empty matrix,
  which is invertible. This is how the hypothesis "$A_i$ nonsingular for $i = 1, \ldots, n - 1$" of
  Theorem 3.4 reads.
* The factors $\hat L$, $\hat U$ computed in floating-point arithmetic (Section 3.3.2) are an
  admissible `FloatingPoint.RoundsLU m A L̂ Û` of the relational rounding model
  `FloatingPoint.RoundingModel`: the Doolittle recurrence with every product, every subtraction and
  every division rounded. This covers every loop order of Programs 4–6 of the book.

## Deviations from the source

* **The remark after (3.36)** (correction). The source says that $(m_i e_i^T)(m_j e_j^T) = 0$ if
  $i \neq j$. For distinct indices, only $i < j$ guarantees a zero product. See
  `QuarteroniSaccoSaleri.Chapter03.equation_3_36`.
* **Property 3.2** (correction and reading). The row-dominance theorem adds the necessary
  nonsingularity hypothesis. The column-dominance theorem uses the same sufficient hypothesis
  for elimination with nonzero pivots. See `QuarteroniSaccoSaleri.Chapter03.property_3_2_row`
  and `QuarteroniSaccoSaleri.Chapter03.property_3_2_col`.
* **Elimination, rounding and compact recurrences** (reading). The algebraic recurrences
  are total even at zero pivots. The factorization and rounding theorems specify their
  nonzero-pivot and roundoff assumptions separately.

## Not formalized

* **Example 3.2**, the run of GEM on the Hilbert matrix $H_3$ in exact rational arithmetic.
* **Programs 4–6.**
* **The operation counts of GEM**, which the book gives in prose.
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ}

/-! ### The stages of Gaussian elimination, (3.29)–(3.31) -/

section Stages

variable (A : Matrix (Fin n) (Fin n) ℝ)

/-- **Equation (3.30)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ and let
$k \in \{0, \ldots, n - 1\}$. The **multipliers of stage $k$** form the vector $m_k = (0,
\ldots, 0, m_{k+1,k}, \ldots, m_{n-1,k})^T$ with
$$m_{ik} = \frac{a^{(k)}_{ik}}{a^{(k)}_{kk}} \quad (i > k), \qquad m_{ik} = 0 \quad (i \le k),$$
where $a^{(k)}_{ij}$ are the entries of the stage $A^{(k)}$ of Gaussian elimination.

The stage $A^{(k)}$ is `Matrix.gemStage A k`, with $0$-based $k$. If the pivot $a^{(k)}_{kk}$ is
zero, the division in Lean gives $m_{ik} = 0$.

**Reading.** The multipliers use Lean's total division. They are zero when the pivot is
zero, where the book's elimination stops. -/
noncomputable def gemMultipliers (k : Fin n) : Fin n → ℝ :=
  fun i => if k < i then gemStage A k i k / gemStage A k k k else 0

/-- **Equation (3.29)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ and
$b \in \mathbb{R}^n$. The **right-hand sides** $b^{(k)}$ of the systems of Gaussian elimination
are defined by $b^{(0)} = b$ and, for $k < n$,
$$b^{(k+1)}_i = b^{(k)}_i - m_{ik} b^{(k)}_k \quad (i > k), \qquad b^{(k+1)}_i = b^{(k)}_i \quad
  (i \le k),$$
with the multipliers $m_{ik}$ of `QuarteroniSaccoSaleri.Chapter03.gemMultipliers`. For
$k \ge n$, $b^{(k+1)} = b^{(k)}$.

The index $k$ is $0$-based. As for `Matrix.gemStage`, nothing happens after the stage $n$.

**Reading.** The recurrence uses the totalized elimination stages. Once no row remains,
further stages leave the right-hand side unchanged. -/
noncomputable def gemRhs (b : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => b
  | k + 1 =>
    if h : k < n then
      fun i => gemRhs b k i - gemMultipliers A ⟨k, h⟩ i * gemRhs b k ⟨k, h⟩
    else gemRhs b k

/-- A stage index `k : Fin n` equals `⟨k, k.2⟩`. -/
private theorem fin_mk_val (k : Fin n) : (⟨k, k.2⟩ : Fin n) = k := Fin.eta k k.2

/-- The multiplier matrix $N$ of a stage at the pivot $p$ acts on a vector $v$ by
$(Nv)_i = a_{ip} a_{pp}^{-1} v_p$ for $i > p$, and $(Nv)_i = 0$ otherwise. -/
private theorem elimMultipliers_mulVec_apply (M : Matrix (Fin n) (Fin n) ℝ) (p : Fin n)
    (v : Fin n → ℝ) (i : Fin n) :
    (elimMultipliers M p *ᵥ v) i = if p < i then M i p * (M p p)⁻¹ * v p else 0 := by
  rw [mulVec, dotProduct, Finset.sum_eq_single p (fun c _ hc => by simp [hc]) (by simp)]
  by_cases hi : p < i <;> simp [hi]

/-- **Equations (3.30)–(3.31)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$,
$b \in \mathbb{R}^n$ and $k \in \{0, \ldots, n - 1\}$. One stage of Gaussian elimination changes
the rows below the pivot and keeps the other rows: for all $j$,
$$a^{(k+1)}_{ij} = a^{(k)}_{ij} - m_{ik} a^{(k)}_{kj}, \qquad b^{(k+1)}_i = b^{(k)}_i - m_{ik}
  b^{(k)}_k \qquad (i > k),$$
and $a^{(k+1)}_{ij} = a^{(k)}_{ij}$, $b^{(k+1)}_i = b^{(k)}_i$ for $i \le k$.

The index $k$ is $0$-based, so the stage $k + 1$ here is the stage $k + 2$ of the book. The
proof uses `Matrix.gemStage_succ_of_lt`, `Matrix.elimStep_apply_of_lt` and
`Matrix.elimStep_apply_of_not_lt`.

**Reading.** The same update is stated for all columns and every indexed stage, with zero
pivots totalized. In the book the proper elimination step needs a nonzero pivot, and the
earlier columns have already been eliminated. -/
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

/-- **Equation (3.29)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ and
$b \in \mathbb{R}^n$. For every $k \ge 0$ and every $x \in \mathbb{R}^n$,
$$A^{(k)} x = b^{(k)} \iff Ax = b.$$
So all the systems that Gaussian elimination produces are equivalent to the original system.

No hypothesis on the pivots is needed: a zero pivot gives zero multipliers, and the stage is
then unchanged. The proof uses $b^{(k+1)} = M_k b^{(k)}$ for the invertible Gaussian
transformation $M_k$ of (3.35), with `Matrix.gemStage_succ_eq_gaussTransform_mul` and
`Matrix.gaussTransform_mul_elimMul`.

**Reading.** Every formal stage preserves the solution set. With a zero pivot the formal
update does nothing, while the book stops the algorithm. -/
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

/-- **Remark 3.2** of [quarteroni2000numerical], equation (3.32). For every $n$, the Hilbert matrix
$H_n$ of order $n$ has the entries
$$h_{ij} = \frac{1}{i + j - 1}, \qquad i, j = 1, \ldots, n,$$
and it is nonsingular and symmetric positive definite.

The Hilbert matrix is `Matrix.hilbert ℝ n`. With the $0$-based indices of `Fin n` the entry is
$1/((i + 1) + (j + 1) - 1)$. The proof uses `Matrix.isUnit_hilbert` and `Matrix.posDef_hilbert`.
By positive definiteness, Gaussian elimination without pivoting applies to $H_n$ (Example 3.2,
Theorem 3.6). The remark that $H_n$ is the paradigm of an ill-conditioned matrix is not
formalized. -/
theorem remark_3_2 (n : ℕ) :
    (∀ i j : Fin n, hilbert ℝ n i j = 1 / (((i : ℕ) + 1 : ℝ) + ((j : ℕ) + 1) - 1)) ∧
      IsUnit (hilbert ℝ n) ∧ (hilbert ℝ n).PosDef := by
  refine ⟨fun i j => ?_, isUnit_hilbert ℝ n, posDef_hilbert n⟩
  rw [hilbert_apply]
  ring_nf

/-- **Equation (3.33)** of [quarteroni2000numerical]. The matrix
$$A = \begin{bmatrix} 1 & 2 & 3 \\ 2 & 4 & 5 \\ 7 & 8 & 9 \end{bmatrix}$$
is nonsingular and has nonzero diagonal entries. Its second stage of Gaussian elimination is
$$A^{(2)} = \begin{bmatrix} 1 & 2 & 3 \\ 0 & 0 & -1 \\ 0 & -6 & -12 \end{bmatrix},$$
whose pivot $a^{(2)}_{22}$ is zero, so that GEM stops at the second step. The leading principal
minors are $d_1 = 1$ and $d_2 = 0$.

The second stage of the book is `Matrix.gemStage A 1`, and its pivot is the entry at the
$0$-based position $(1, 1)$. -/
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

/-- **Equation (3.35)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ and
$k \in \{0, \ldots, n - 1\}$. Then $A^{(k+1)} = M_k A^{(k)}$, where the Gaussian transformation
of stage $k$ is
$$M_k = I_n - m_k e_k^T,$$
the identity matrix with the negated multipliers of stage $k$ in column $k$ below the diagonal.

The matrix $M_k$ is `Matrix.gaussTransform (gemStage A k) k`, and $m_k e_k^T$ is
`vecMulVec (gemMultipliers A k) (Pi.single k 1)`. The proof uses
`Matrix.gemStage_succ_eq_gaussTransform_mul`.

**Reading.** The identity applies to totalized stages, including the identity transformation
at a zero pivot. -/
theorem equation_3_35 (k : Fin n) :
    gemStage A (k + 1) = gaussTransform (gemStage A k) k * gemStage A k ∧
      gaussTransform (gemStage A k) k = 1 - vecMulVec (gemMultipliers A k) (Pi.single k 1) := by
  refine ⟨by rw [gemStage_succ_eq_gaussTransform_mul A k.2, fin_mk_val], ?_⟩
  ext i j
  simp only [gaussTransform, Matrix.sub_apply, elimMultipliers_apply, vecMulVec_apply,
    gemMultipliers, Pi.single_apply]
  split_ifs <;> simp_all [div_eq_mul_inv]

/-- The rank-one product $(m_i e_i^T)(m_j e_j^T)$ is zero when the $i$-th entry of $m_j$ is zero. -/
private theorem vecMulVec_single_mul_vecMulVec_single {mi mj : Fin n → ℝ} {i j : Fin n}
    (h : mj i = 0) : vecMulVec mi (Pi.single i 1) * vecMulVec mj (Pi.single j 1) = 0 := by
  rw [vecMulVec_mul_vecMulVec, single_dotProduct, one_mul, h, zero_smul, vecMulVec_zero]

/-- **Equation (3.36)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ and
$k \in \{0, \ldots, n - 1\}$. The Gaussian transformation $M_k$ is unit lower triangular, and
$$M_k^{-1} = 2 I_n - M_k = I_n + m_k e_k^T.$$
Moreover, $(m_i e_i^T)(m_j e_j^T) = 0$ for all $i < j$.

**Correction.** After (3.36) the source says that $(m_i e_i^T)(m_j e_j^T)$ is the null matrix if
$i \neq j$. This holds only for $i < j$. For $i > j$ the product is $m_{ij} m_i e_j^T$, which is
nonzero as soon as the multiplier $m_{ij}$ is nonzero. The case $i < j$ is the one that the
product (3.37) needs.

The proof uses `Matrix.gaussTransform_mul_elimMul` and `Matrix.elimMul`. -/
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

/-- After $k$ stages, the partial multiplier matrix is the ordered product
$M_0^{-1} \cdots M_{k-1}^{-1}$ of the inverse Gaussian transformations. -/
private theorem gemLowerStage_eq_prod (k : ℕ) (hk : k ≤ n) :
    gemLowerStage A k =
      (List.ofFn fun i : Fin k => elimMul (gemStage A i) (Fin.castLE hk i)).prod := by
  induction k with
  | zero => rw [gemLowerStage_zero, List.ofFn_zero, List.prod_nil]
  | succ k ih =>
    rw [gemLowerStage_succ A (by omega), ih (by omega), List.ofFn_succ', List.concat_eq_append,
      List.prod_append, List.prod_singleton]
    rfl

/-- **Equation (3.37)** of [quarteroni2000numerical] (GEM as a factorization method). Let
$A \in \mathbb{R}^{n \times n}$, and assume that the pivots $a^{(k)}_{kk}$ are nonzero for
$k = 0, \ldots, n - 2$. Let $U = A^{(n)}$ be the last stage, and let $L$ be the multiplier
matrix of GEM. Then $A = LU$ is an LU factorization of $A$, with $L$ unit lower triangular and
$U$ upper triangular, and
$$L = I_n + \sum_{i=0}^{n-1} m_i e_i^T = M_0^{-1} M_1^{-1} \cdots M_{n-1}^{-1}.$$
The subdiagonal entries of $L$ are the multipliers: $l_{ik} = m_{ik}$ for $i > k$.

The last pivot is never a divisor, so it need not be nonzero. The matrix $L$ is
`Matrix.gemLower A`. The product runs over all $k \in \{0, \ldots, n - 1\}$; its last factor
$M_{n-1}^{-1}$ is the identity, because $m_{n-1} = 0$. The proof uses
`Matrix.isLU_gemLower_gemStage`. -/
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
    · simp [h1.ne']
    · simp [Matrix.one_apply, h2]
    · simp [h2]
  · rw [← gemLowerStage_of_le A le_rfl, gemLowerStage_eq_prod A n le_rfl]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    rw [inv_eq_right_inv (gaussTransform_mul_elimMul _ _)]
    rfl
  · simp [gemLower, gemMultipliers, hki]

end Factorization

/-! ### Theorem 3.4, (3.39), Example 3.3, Property 3.2 -/

section Existence

variable {A L U : Matrix (Fin n) (Fin n) ℝ}

/-- **Theorem 3.4** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$. The LU
factorization of $A$ with $l_{ii} = 1$ for $i = 1, \ldots, n$ exists and is unique if and only
if the leading principal submatrices $A_i$ of $A$ of order $i = 1, \ldots, n - 1$ are
nonsingular.

The LU factorization is a pair $(L, U)$ with `Matrix.IsLU A L U`. The hypothesis is stated for
the strict leading principal submatrices `Matrix.strictLeadingPrincipalSubmatrix A k`,
$k \in \{0, \ldots, n - 1\}$, which are the $A_i$ of orders $i = 0, \ldots, n - 1$; the block of
order $0$ is the empty matrix, which is always invertible. The proof specializes
`Matrix.existsUnique_isLU_iff`. -/
theorem theorem_3_4 (A : Matrix (Fin n) (Fin n) ℝ) :
    (∃! LU : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ, IsLU A LU.1 LU.2) ↔
      ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k) :=
  existsUnique_isLU_iff A

/-- **Equations (3.38)–(3.39)** of [quarteroni2000numerical]. Let
$A, L, U \in \mathbb{R}^{n \times n}$, and let $A = LU$ be an LU factorization with $L$ unit
lower triangular and $U$ upper triangular. Then, for every $k \in \{0, \ldots, n - 1\}$:

* the leading principal submatrices of order $k + 1$ satisfy $A_{k+1} = L_{k+1} U_{k+1}$, and
  this is again an LU factorization;
* the leading principal minor is $d_{k+1} = \det A_{k+1} = u_{00} u_{11} \cdots u_{kk}$;
* if the strict leading principal submatrix of order $k$ has nonzero determinant $d_k$, then the
  pivot is the ratio of consecutive minors, $u_{kk} = d_{k+1} / d_k$.

In particular $\det A = \prod_i u_{ii}$.

The indices are $0$-based, so $u_{kk}$ here is the book's $u_{k+1,k+1}$. The proof uses
`Matrix.IsLU.toBlock_le`, `Matrix.IsLU.det_leadingPrincipalSubmatrix`,
`Matrix.IsLU.det_eq_prod_diag` and `Matrix.IsLU.diag_upper_eq_div_leadingPrincipalMinor`. -/
theorem equation_3_39 (h : IsLU A L U) :
    (∀ k, IsLU (A.leadingPrincipalSubmatrix k) (L.leadingPrincipalSubmatrix k)
      (U.leadingPrincipalSubmatrix k)) ∧
    (∀ k, A.leadingPrincipalMinor k = ∏ i with i ≤ k, U i i) ∧
    A.det = ∏ i, U i i ∧
    ∀ k, (A.strictLeadingPrincipalSubmatrix k).det ≠ 0 →
      U k k = A.leadingPrincipalMinor k / (A.strictLeadingPrincipalSubmatrix k).det :=
  ⟨h.toBlock_le, h.det_leadingPrincipalSubmatrix, h.det_eq_prod_diag,
    fun _ hk => h.diag_upper_eq_div_leadingPrincipalMinor hk⟩

/-- For all $a, u, v, w \in \mathbb{R}$, the product $\begin{bmatrix} 1 & 0 \\ a & 1 \end{bmatrix}
\begin{bmatrix} u & v \\ 0 & w \end{bmatrix}$ has this LU factorization. -/
private theorem isLU_fin_two (a u v w : ℝ) :
    IsLU (!![1, 0; a, 1] * !![u, v; 0, w]) !![1, 0; a, 1] !![u, v; 0, w] where
  isUnitLowerTriangular := ⟨fun i j hij => by
      have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      fin_cases i <;> fin_cases j <;> simp_all, fun i => by fin_cases i <;> simp⟩
  isUpperTriangular := fun i j hij => by
    fin_cases i <;> fin_cases j <;> simp_all
  mul_eq := rfl

/-- If $M \in \mathbb{R}^{2 \times 2}$ has $m_{11} \neq 0$, then all strict leading principal
submatrices of $M$ are nonsingular. -/
private theorem forall_isUnit_strict_fin_two {M : Matrix (Fin 2) (Fin 2) ℝ} (h : M 0 0 ≠ 0) :
    ∀ k, IsUnit (M.strictLeadingPrincipalSubmatrix k) :=
  (gemStage_pivots_ne_zero_iff M).1 fun m hm hm1 => by
    interval_cases m
    · simpa using h
    · exact absurd hm1 (by norm_num)

/-- **Example 3.3** of [quarteroni2000numerical], the matrix $B$. The singular matrix
$$B = \begin{bmatrix} 1 & 2 \\ 1 & 2 \end{bmatrix}$$
has the leading principal minor $d_1 = 1 \neq 0$, and it has a unique LU factorization with unit
lower triangular factor:
$$L = \begin{bmatrix} 1 & 0 \\ 1 & 1 \end{bmatrix}, \qquad U = \begin{bmatrix} 1 & 2 \\ 0 & 0
  \end{bmatrix}.$$
This agrees with Theorem 3.4. -/
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

/-- **Example 3.3** of [quarteroni2000numerical], the matrix $C$. The nonsingular matrix
$$C = \begin{bmatrix} 0 & 1 \\ 1 & 0 \end{bmatrix}$$
has the leading principal minor $d_1 = 0$, and it has no LU factorization with unit lower
triangular factor.

The reason is that the $(1, 1)$ entry forces $u_{11} = 0$, and then the $(2, 1)$ entry would be
$l_{21} u_{11} = 0 \neq 1$. -/
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

/-- **Example 3.3** of [quarteroni2000numerical], the matrix $D$. The singular matrix
$$D = \begin{bmatrix} 0 & 1 \\ 0 & 2 \end{bmatrix}$$
has the leading principal minor $d_1 = 0$, and it has infinitely many LU factorizations: for
every $\beta \in \mathbb{R}$,
$$D = L_\beta U_\beta, \qquad L_\beta = \begin{bmatrix} 1 & 0 \\ \beta & 1 \end{bmatrix}, \quad
  U_\beta = \begin{bmatrix} 0 & 1 \\ 0 & 2 - \beta \end{bmatrix}.$$
-/
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

/-- **Property 3.2** of [quarteroni2000numerical], rows. Let $A \in \mathbb{R}^{n \times n}$ be
nonsingular and diagonally dominant by rows, that is, $\sum_{j \neq i} |a_{ij}| \le |a_{ii}|$
for every $i$. Then $A$ has an LU factorization with unit lower triangular factor.

**Correction.** The source does not assume that $A$ is nonsingular. With the weak diagonal
dominance of Definition 1.24, the statement is false without this hypothesis: the matrix
$\begin{bmatrix} 0 & 0 \\ 1 & 1 \end{bmatrix}$ is diagonally dominant by rows, and it has no LU
factorization, since its $(2, 1)$ entry would be $l_{21} u_{11} = 0$. The theorem that the
source cites, Theorem 9.9 of [higham2002accuracy], assumes nonsingularity.

Diagonal dominance by rows is `Matrix.IsDiagDominant`. The proof specializes
`Matrix.exists_isLU_of_isDiagDominant`. -/
theorem property_3_2_row (hA : IsUnit A) (hdom : A.IsDiagDominant) : ∃ L U, IsLU A L U :=
  exists_isLU_of_isDiagDominant hA hdom

/-- **Property 3.2** of [quarteroni2000numerical], columns. Let $A \in \mathbb{R}^{n \times n}$ be
nonsingular and diagonally dominant by columns, that is, $\sum_{i \neq j} |a_{ij}| \le |a_{jj}|$
for every $j$. Then $A$ has an LU factorization $A = LU$ with unit lower triangular factor, and
$|l_{ij}| \le 1$ for all $i, j$.

**Reading.** The source does not assume nonsingularity in the column case. The declaration
includes it to use ordinary elimination with nonzero pivots. With weak column dominance, a
zero pivot forces its remaining column to vanish, so the broader existence assertion can
instead proceed by choosing zero multipliers there.

Diagonal dominance by columns is `Matrix.IsColDiagDominant`. The proof specializes
`Matrix.exists_isLU_of_isColDiagDominant`. -/
theorem property_3_2_col (hA : IsUnit A) (hdom : A.IsColDiagDominant) :
    ∃ L U, IsLU A L U ∧ ∀ i j, |L i j| ≤ 1 := by
  obtain ⟨L, U, h, hL⟩ := exists_isLU_of_isColDiagDominant hA hdom
  exact ⟨L, U, h, fun i j => by simpa [Real.norm_eq_abs] using hL i j⟩

end Existence

/-! ### §3.3.2: the effect of rounding errors -/

section Rounding

open FloatingPoint

variable {m : RoundingModel ℝ} {A L U : Matrix (Fin n) (Fin n) ℝ}

/-- **Equation (3.40)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ with
$n \ge 1$, let $u$ be the unit roundoff of a rounding model with $nu < 1$, and let $\hat L$,
$\hat U$ be the factors that GEM computes in floating-point arithmetic, with nonzero computed
pivots $\hat u_{jj}$. Then there is a matrix $\delta A$ with
$$\hat L \hat U = A + \delta A, \qquad |\delta A| \le \frac{nu}{1 - nu} |\hat L| |\hat U|,$$
where the absolute values and the inequality are entrywise.

The computed factors are an admissible `FloatingPoint.RoundsLU m A L U` for the rounding model
`m`, whose unit roundoff is `m.u`. The entrywise absolute value is `Matrix.abs`, and the
entrywise order is `≤ₑ`. The proof uses `FloatingPoint.exists_roundsLU_mul_eq_add`, which is
Theorem 9.3 of [higham2002accuracy].

**Reading.** The theorem states the exact bound under $nu<1$ for factors admitted by the
rounding model, with nonzero computed pivots. -/
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

/-- **Equation (3.41)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ with
$n \ge 1$, let $u$ be the unit roundoff of a rounding model with $2nu < 1$, and let $\hat L$,
$\hat U$ be the factors that GEM computes in floating-point arithmetic, with nonzero computed
pivots and with nonnegative entries. Then there is a matrix $\delta A$ with
$$\hat L \hat U = A + \delta A, \qquad |\delta A| \le \frac{nu}{1 - 2nu} |A|$$
entrywise.

For nonnegative factors, $|\hat L| |\hat U| = |\hat L \hat U| = |A + \delta A| \le |A| + |\delta
A|$, and this turns (3.40) into a bound in terms of $A$ alone. The proof uses
`FloatingPoint.abs_le_of_roundsLU_of_entrywiseNonneg`.

**Reading.** The bound in terms of $|A|$ makes the sufficient condition $2nu<1$ explicit. -/
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

/-- **Equation (3.42)** of [quarteroni2000numerical]. Let $A, L, U \in \mathbb{R}^{n \times n}$ with
$L$ unit lower triangular and $U$ upper triangular. Then $A = LU$ if and only if the $n^2$
equations
$$a_{ij} = \sum_{r \le \min(i, j)} l_{ir} u_{rj}$$
hold for all $i, j$.

So computing the LU factorization means solving this system for the $n^2 + n$ entries of the
triangular factors. The proof uses `Matrix.IsLU.apply_eq_sum`; conversely, the sum is
$(LU)_{ij}$ by triangularity. -/
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

/-- **Equation (3.43)** of [quarteroni2000numerical] (the Doolittle method). Let
$A \in \mathbb{R}^{n \times n}$, and let $L$ and $U$ be the Doolittle factors of $A$. With
$l_{kk} = 1$, the $k$-th row of $U$ and then the $k$-th column of $L$ satisfy
$$u_{kj} = a_{kj} - \sum_{r < k} l_{kr} u_{rj} \quad (j \ge k), \qquad l_{ik} = \frac{1}{u_{kk}}
  \Big( a_{ik} - \sum_{r < k} l_{ir} u_{rk} \Big) \quad (i > k).$$
If the leading principal submatrices of orders $0, \ldots, n - 1$ are nonsingular, then $A = LU$
is an LU factorization. If the pivots $a^{(k)}_{kk}$ of GEM are nonzero for
$k = 0, \ldots, n - 2$, then $L$ and $U$ are the factors that GEM produces: $L$ is the
multiplier matrix and $U = A^{(n)}$.

The last statement is the remark of the source that the Doolittle factorization is the $ijk$
version of GEM. The factors are `Matrix.luLower A` and `Matrix.luUpper A`, read off the packed
recurrence `Matrix.luPacked A`. If $u_{kk} = 0$, the division in Lean gives $l_{ik} = 0$. The
proof uses `Matrix.isLU_luLower_luUpper` and `Matrix.luLower_eq_gemLower`.

**Reading.** The recurrence is total, with zero division giving zero below a zero pivot.
The statement separately supplies hypotheses ensuring an LU factorization. -/
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

/-- **Section 3.3.4** of [quarteroni2000numerical], the Crout factorization. Let
$A \in \mathbb{R}^{n \times n}$, and let $L$ and $U$ be the Crout factors of $A$. With
$u_{kk} = 1$, the $k$-th column of $L$ and then the $k$-th row of $U$ satisfy
$$l_{ik} = a_{ik} - \sum_{r < k} l_{ir} u_{rk} \quad (i \ge k), \qquad u_{kj} = \frac{1}{l_{kk}}
  \Big( a_{kj} - \sum_{r < k} l_{kr} u_{rj} \Big) \quad (j > k).$$
If the leading principal submatrices of orders $0, \ldots, n - 1$ are nonsingular, then $A = LU$
with $L$ lower triangular and $U$ unit upper triangular.

The factors are `Matrix.croutLower A` and `Matrix.croutUpper A`, which are the transposed
Doolittle factors of $A^T$. The hypothesis of Theorem 3.4 for $A^T$ is the same as for $A$. That
$U$ is unit upper triangular is stated as `(croutUpper A)ᵀ.IsUnitLowerTriangular`. The proof
uses `Matrix.croutLower_mul_croutUpper`.

**Reading.** The recurrence uses total division, and the factorization theorem makes the
leading-minor condition explicit. -/
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
