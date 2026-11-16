/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Numlib.Preconditioner.ILU
import Numlib.Preconditioner.LevelOfFill
import NumlibSurface.SaadSparse.Chapter03.Section02

/-!
# Saad, Section 10.3: Incomplete LU factorization preconditioners

This module formalizes Section 10.3 of [saad2003iterative]. An incomplete $LU$ factorization of
$A \in \mathbb{R}^{n \times n}$ for a zero pattern $P$, a set of off-diagonal positions as in
(10.11), is a pair of a unit lower triangular $L$ and an upper triangular $U$ that both vanish on
$P$ and whose product agrees with $A$ off $P$; then $A = LU - R$ with $R$ zero off $P$ (Proposition
10.4). For an M-matrix, one step of Gaussian elimination gives again an M-matrix (Theorem 10.1), and
so the factorization exists for every zero pattern, no pivot vanishes, and $A = LU - R$ is a regular
splitting (Theorem 10.2). The module also states ILU(0), whose zero pattern is the off-diagonal zero
pattern of $A$; the level of fill (Definition 10.5, recurrence (10.17)) and the pattern $P_p$ of
ILU($p$); the characterization of the level of fill by fill-paths (Theorems 10.6 and 10.7); the
modified factorization MILU of Section 10.3.5; and the agreement of the two loop orders of
Algorithms 10.1 and 10.3 (Proposition 10.3).

The incomplete factorization is stated as a set of constraints, `Matrix.IsILU` of
`Numlib.Preconditioner.ILU`, and not as the output of a loop. The constraints do not determine the
factors (`SaadSparse.Chapter10.not_unique_isILU0`), so the two loop orders are written out as
functions for Proposition 10.3. The level of fill is `Matrix.levelOfFill` of
`Numlib.Preconditioner.LevelOfFill`, and the fill-path theorems are proved there over the level of
fill itself.

## Main definitions

* Equation (10.11), `SaadSparse.Chapter10.IsZeroPattern`: a zero pattern is a set of off-diagonal
  positions.
* Algorithms 10.1 and 10.3, `SaadSparse.Chapter10.iluRowOp`: the common row operation
  $\mathrm{ope}(\mathrm{row}(i), \mathrm{row}(k))$.
* Algorithm 10.1, `SaadSparse.Chapter10.kijSweep`: the KIJ variant of the incomplete factorization.
* Algorithm 10.3, `SaadSparse.Chapter10.rowOps`: the $k$-loop of Algorithm 10.3 on one row.
* Algorithm 10.3, `SaadSparse.Chapter10.ikjSweep`: the IKJ variant of the incomplete factorization.
* Definition 10.5, `SaadSparse.Chapter10.initialLevel`: the initial level of fill is $0$ at a
  nonzero entry and on the diagonal, and $\infty$ elsewhere.
* Equation (10.17), `SaadSparse.Chapter10.levelOfFill`: the level of fill after $k$ elimination
  steps.
* Section 10.3.3, `SaadSparse.Chapter10.levelPattern`: the zero pattern $P_p$ of ILU($p$).
* Section 10.3.3, `SaadSparse.Chapter10.IsFillPath`: a fill-path between $i$ and $j$.

## Main results

* Section 10.3.1, `SaadSparse.Chapter10.isILU_iff`: the constraints of an incomplete $LU$
  factorization, written out.
* Section 10.3.1, `SaadSparse.Chapter10.pivot_ne_zero`: if $LU$ is nonsingular, no pivot $u_{ii}$
  vanishes.
* Equation (10.10), `SaadSparse.Chapter10.equation_10_10`: one step of Gaussian elimination factors
  $A = L_1 A_1$.
* Theorem 10.1, `SaadSparse.Chapter10.theorem_10_1`: one step of Gaussian elimination maps an
  M-matrix to an M-matrix.
* Theorem 10.1, `SaadSparse.Chapter10.theorem_10_1_schur`: the Schur complement of one pivot of an
  M-matrix is an M-matrix.
* Theorem 10.2, `SaadSparse.Chapter10.theorem_10_2`: an M-matrix has an incomplete factorization for
  every zero pattern, with nonzero pivots and a regular splitting.
* Section 10.3.1, `SaadSparse.Chapter10.ikjSweep_row`: each row produced by Algorithm 10.3 is
  obtained from the final earlier rows.
* Section 10.3.1, `SaadSparse.Chapter10.kijSweep_row`: the invariant of Algorithm 10.1.
* Proposition 10.3, `SaadSparse.Chapter10.proposition_10_3`: the KIJ and IKJ loop orders produce the
  same result.
* Proposition 10.4, `SaadSparse.Chapter10.proposition_10_4`: $A = LU - R$ with $R$ zero off the zero
  pattern.
* Theorem 10.2, `SaadSparse.Chapter10.theorem_10_2_ilu0`: Theorem 10.2 for ILU(0).
* Section 10.3.2, `SaadSparse.Chapter10.not_unique_isILU0`: the ILU(0) constraints do not determine
  the factors.
* Section 10.3.3, `SaadSparse.Chapter10.levelPattern_zero`: the pattern $P_0$ is the zero pattern of
  ILU(0).
* Theorem 10.6, `SaadSparse.Chapter10.theorem_10_6`: a position is filled at the end of Gaussian
  elimination if and only if a fill-path exists.
* Theorem 10.7, `SaadSparse.Chapter10.theorem_10_7`: the level of fill is $p$ if and only if the
  shortest fill-path has length $p + 1$.
* Equation (10.21), `SaadSparse.Chapter10.milu_mulVec_one`: MILU is exact on the vector of ones.
* Section 10.3.5, `SaadSparse.Chapter10.milu_residual_diag`: the diagonal compensation of MILU.

## Conventions

* Indices are $0$-based: the rows and columns of $A$ are `Fin n`, and the pivot $k$ of the $k$-th
  elimination step is the index $k$.
* $A_1$, "the matrix obtained from the first step of Gaussian elimination", is `Matrix.elimStep`.
  The $(n-1) \times (n-1)$ matrix obtained from $A_1$ by deleting the pivot row and column is
  `Matrix.schurComplementSingle`.

## Implementation notes

* The level of fill takes values in `ℕ∞`, whose top element is $\infty$. The final level of fill,
  after all updates (10.17), is `SaadSparse.Chapter10.levelOfFill A n`.
* The adjacency graph is `Matrix.adjGraph` of Section 3.2.1, the symmetrized graph without loops of
  the nonzero pattern. The level of fill is computed from the directed pattern, so the fill-path
  theorems assume that the pattern of $A$ is symmetric; `SaadSparse.Chapter03.adjDigraph_eq` relates
  the two graphs.

## Deviations from the source

* **Theorem 10.1** (generalization). The book states the first elimination step; the formal
  statement holds at every pivot. See `SaadSparse.Chapter10.theorem_10_1`.
* **Theorem 10.2** (reading). "Algorithm 10.1 does not break down" is read as the existence of the
  factors together with $u_{ii} \neq 0$ for all $i$. See `SaadSparse.Chapter10.theorem_10_2`.
* **Proposition 10.3** (generalization). Line 1 of both algorithms, which sets $a_{ij} = 0$ for
  $(i, j) \in P$, is omitted, so the statement holds for every starting matrix. See
  `SaadSparse.Chapter10.proposition_10_3`.

## Not formalized

* **Algorithms 10.4 and 10.5.** They are listings.
-/

open Matrix Stationary
open scoped Matrix

namespace SaadSparse.Chapter10

variable {n : ℕ}

/-! ### The zero pattern (10.11) and the factorization $ILU_P$ -/

/-- **Equation (10.11)** of [saad2003iterative]. A set $P \subseteq \{0, \dots, n-1\}^2$ of
positions is a **zero pattern** if it contains no diagonal position:
$$P \subseteq \{(i, j) : i \neq j\}.$$

This is the only restriction that the book places on the entries that an incomplete
factorization may discard. Theorem 10.2 needs it: its proof divides by the pivots, so the pivots
are never dropped. -/
def IsZeroPattern (P : Set (Fin n × Fin n)) : Prop := ∀ p ∈ P, p.1 ≠ p.2

/-- If $P$ is a zero pattern, then $(i, i) \notin P$ for every index $i$. -/
theorem IsZeroPattern.diag_notMem {P : Set (Fin n × Fin n)} (hP : IsZeroPattern P) (i : Fin n) :
    (i, i) ∉ P := fun h => hP _ h rfl

/-- For $A \in \mathbb{R}^{n \times n}$, the off-diagonal zero pattern
$\{(i, j) : a_{ij} = 0, \ i \neq j\}$ of $A$, which is the pattern of ILU(0), is a zero pattern. -/
theorem isZeroPattern_zeroPattern (A : Matrix (Fin n) (Fin n) ℝ) : IsZeroPattern A.zeroPattern :=
  fun _ hp => hp.2

/-- **Section 10.3.1** of [saad2003iterative], the incomplete factorization $ILU_P$. Let $P$ be a
set of positions and let $A, L, U \in \mathbb{R}^{n \times n}$. Then $(L, U)$ is an **incomplete
$LU$ factorization** of $A$ for $P$ if and only if

* $L$ is unit lower triangular: $l_{ii} = 1$ for all $i$ and $l_{ij} = 0$ for $i < j$;
* $U$ is upper triangular: $u_{ij} = 0$ for $j < i$;
* $l_{ij} = 0$ and $u_{ij} = 0$ for $(i, j) \in P$;
* $(LU)_{ij} = a_{ij}$ for $(i, j) \notin P$.

The book defines the factors by Algorithm 10.1 and then proves with Proposition 10.3 that a
second loop order gives the same factors. The constraints are `Matrix.IsILU`, which all of
Sections 10.3–10.5 use. Either loop order satisfies them, but they do not determine the factors,
as `SaadSparse.Chapter10.not_unique_isILU0` shows. -/
theorem isILU_iff (P : Set (Fin n × Fin n)) (A L U : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.IsILU P A L U ↔
      ((∀ i, L i i = 1) ∧ ∀ i j, i < j → L i j = 0) ∧ (∀ i j, j < i → U i j = 0) ∧
        (∀ i j, (i, j) ∈ P → L i j = 0 ∧ U i j = 0) ∧
        ∀ i j, (i, j) ∉ P → (L * U) i j = A i j := by
  constructor
  · intro h
    exact ⟨⟨h.l_diag, h.l_eq_zero_of_lt⟩, h.u_eq_zero_of_gt,
      fun i j hij => ⟨h.l_eq_zero_of_mem i j hij, h.u_eq_zero_of_mem i j hij⟩, h.agree⟩
  · rintro ⟨⟨hd, hl⟩, hu, hmem, hag⟩
    exact ⟨⟨hd, hl, hu, fun i j hij => (hmem i j hij).1, fun i j hij => (hmem i j hij).2⟩, hag⟩

/-- **Section 10.3.1** of [saad2003iterative], no pivot vanishes. Let $P$ be a set of positions, let
$(L, U)$ be an incomplete $LU$ factorization of $A \in \mathbb{R}^{n \times n}$ for $P$, and let
$LU$ be nonsingular. Then $u_{ii} \neq 0$ for every $i$.

This is the sense in which the elimination "does not break down": $L$ is unit lower triangular,
so $\det(LU) = \prod_i u_{ii}$, and a zero pivot would make the product singular. -/
theorem pivot_ne_zero {P : Set (Fin n × Fin n)} {A L U : Matrix (Fin n) (Fin n) ℝ}
    (h : Matrix.IsILU P A L U) (hu : IsUnit (L * U)) (i : Fin n) : U i i ≠ 0 := by
  have hdet : IsUnit (L * U).det := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have hL : L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular L fun i j hij => h.l_eq_zero_of_lt i j hij]
    simp [h.l_diag]
  rw [Matrix.det_mul, hL, one_mul,
    Matrix.det_of_isUpperTriangular fun i j hij => h.u_eq_zero_of_gt i j hij] at hdet
  exact Finset.prod_ne_zero_iff.1 hdet.ne_zero i (Finset.mem_univ i)

/-! ### Theorem 10.1 (Ky Fan) -/

/-- **Equation (10.10)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ and let $p$ be
a pivot index. One step of Gaussian elimination at the pivot $p$ factors
$$A = L_1 A_1,$$
where $L_1$ is the identity matrix with the multipliers $a_{ip} / a_{pp}$, for $i > p$, written
into column $p$ below the diagonal, and $A_1$ is obtained from $A$ by subtracting
$a_{ip} / a_{pp}$ times row $p$ from each row $i > p$.

The factors are `Matrix.elimMul A p` and `Matrix.elimStep A p`. If $a_{pp} = 0$, the multipliers
are $0$, because Lean's inverse of $0$ is $0$; then $L_1 = I$ and $A_1 = A$, and the identity
still holds. -/
theorem equation_10_10 (A : Matrix (Fin n) (Fin n) ℝ) (p : Fin n) :
    A = Matrix.elimMul A p * Matrix.elimStep A p := (Matrix.elimMul_mul_elimStep A p).symm

/-- **Theorem 10.1** of [saad2003iterative] (Ky Fan). Let $A \in \mathbb{R}^{n \times n}$ be an
M-matrix and let $p$ be any pivot index. Then the matrix $A_1$ obtained from $A$ by one step of
Gaussian elimination at the pivot $p$ is an M-matrix.

**Generalization.** The book states the result for the first step of the elimination. The formal
statement holds at every pivot $p$, which is the form that the rest of the section uses: the
elimination restarts on the trailing block at every step.

The matrix $A_1$ is `Matrix.elimStep A p`, and an M-matrix is `Matrix.IsMMatrix`. -/
theorem theorem_10_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsMMatrix) (p : Fin n) :
    (Matrix.elimStep A p).IsMMatrix := hA.isMMatrix_elimStep p

/-- **Theorem 10.1** of [saad2003iterative], the remark after the theorem. Let
$A \in \mathbb{R}^{n \times n}$ be an M-matrix and let $p$ be a pivot index. Then the matrix
obtained from $A_1$ by deleting row $p$ and column $p$ is an M-matrix. This matrix is the Schur
complement of the $1 \times 1$ pivot block,
$$\bigl(a_{ij} - a_{ip} a_{pp}^{-1} a_{pj}\bigr)_{i, j \neq p}.$$

The elimination argument is iterated in this form. The Schur complement is
`Matrix.schurComplementSingle`. -/
theorem theorem_10_1_schur {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsMMatrix) (p : Fin n) :
    (A.schurComplementSingle p).IsMMatrix := hA.schurComplementSingle p

/-! ### Theorem 10.2 and Proposition 10.4 -/

/-- **Theorem 10.2** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be an M-matrix and
let $P$ be a zero pattern as in (10.11). Then there are $L, U \in \mathbb{R}^{n \times n}$ such
that $LU$ is nonsingular, $(L, U)$ is an incomplete $LU$ factorization of $A$ for $P$,
$u_{ii} \neq 0$ for every $i$, and
$$A = LU - R, \qquad R = LU - A,$$
is a regular splitting of $A$: $(LU)^{-1} \ge 0$ and $R \ge 0$ entrywise.

**Reading.** The book states that Algorithm 10.1 does not break down and produces such a
splitting. "Does not break down" is read as the existence of the factors together with the
condition $u_{ii} \neq 0$ for all $i$: no pivot vanishes.

The splitting is $A = M - N$ with $M = LU$ and $N = R$. A regular splitting is
`Stationary.Splitting.IsRegular`, Definition 4.3 of the book, so the iteration that the
splitting defines converges (`Matrix.IsILU.complexSpectralRadius_lt_one`). -/
theorem theorem_10_2 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsMMatrix) {P : Set (Fin n × Fin n)}
    (hP : IsZeroPattern P) :
    ∃ (L U : Matrix (Fin n) (Fin n) ℝ) (hu : IsUnit (L * U)),
      Matrix.IsILU P A L U ∧ (∀ i, U i i ≠ 0) ∧ A = L * U - (L * U - A) ∧
        (⟨L * U, hu⟩ : Splitting A).IsRegular := by
  obtain ⟨L, U, hILU, hu, hinv, hres⟩ := hA.exists_isILU P hP.diag_notMem
  exact ⟨L, U, hu, hILU, pivot_ne_zero hILU hu, (sub_sub_cancel _ _).symm,
    hILU.isRegular hu hinv fun i j _ => hres.apply i j⟩

/-- **Proposition 10.4** of [saad2003iterative]. Let $P$ be a set of positions and let $(L, U)$ be
an incomplete $LU$ factorization of $A \in \mathbb{R}^{n \times n}$ for $P$. Then
$$A = LU - R, \qquad R = LU - A,$$
and $r_{ij} = 0$ for every $(i, j) \notin P$. So $-R$ consists of the entries dropped during the
elimination. -/
theorem proposition_10_4 {P : Set (Fin n × Fin n)} {A L U : Matrix (Fin n) (Fin n) ℝ}
    (h : Matrix.IsILU P A L U) :
    A = L * U - (L * U - A) ∧ ∀ i j, (i, j) ∉ P → (L * U - A) i j = 0 :=
  ⟨(sub_sub_cancel _ _).symm, fun _ _ hij => h.sub_eq_zero_of_notMem hij⟩

/-! ### Section 10.3.2: ILU(0) -/

/-- **Theorem 10.2** of [saad2003iterative] for ILU(0), Section 10.3.2. Let
$A \in \mathbb{R}^{n \times n}$ be an M-matrix. Then there are
$L, U \in \mathbb{R}^{n \times n}$ such that $LU$ is nonsingular, $(L, U)$ is an ILU(0)
factorization of $A$, $u_{ii} \neq 0$ for every $i$, and $A = LU - R$ with $R = LU - A$ is a
regular splitting of $A$.

ILU(0) is `Matrix.IsILU0`, the incomplete factorization for the off-diagonal zero pattern of
$A$, so $L$ and $U$ have the sparsity patterns of the lower and upper parts of $A$. -/
theorem theorem_10_2_ilu0 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsMMatrix) :
    ∃ (L U : Matrix (Fin n) (Fin n) ℝ) (hu : IsUnit (L * U)),
      Matrix.IsILU0 A L U ∧ (∀ i, U i i ≠ 0) ∧ A = L * U - (L * U - A) ∧
        (⟨L * U, hu⟩ : Splitting A).IsRegular :=
  theorem_10_2 hA (isZeroPattern_zeroPattern A)

/-- The matrix $\begin{bmatrix} 1 & 1 & 0 \\ 0 & 0 & 0 \\ 1 & 1 & 1 \end{bmatrix}$ of the example of
non-unique ILU(0) factors. Its middle row is zero. -/
def exampleA : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1, 0; 0, 0, 0; 1, 1, 1]

/-- The upper factor $\begin{bmatrix} 1 & 1 & 0 \\ 0 & 0 & 0 \\ 0 & 0 & 1 \end{bmatrix}$ of the
example of non-unique ILU(0) factors. -/
def exampleU : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1, 0; 0, 0, 0; 0, 0, 1]

/-- The lower factors $\begin{bmatrix} 1 & 0 & 0 \\ 0 & 1 & 0 \\ 1 & t & 1 \end{bmatrix}$,
$t \in \mathbb{R}$, of the example of non-unique ILU(0) factors. The entry $t$ multiplies only
the middle row of `SaadSparse.Chapter10.exampleU`, which is zero, so no constraint determines
it. -/
def exampleL (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0; 1, t, 1]

/-- For every $t \in \mathbb{R}$, the product of `SaadSparse.Chapter10.exampleL t` and
`SaadSparse.Chapter10.exampleU` is `SaadSparse.Chapter10.exampleA`. -/
theorem exampleL_mul_exampleU (t : ℝ) : exampleL t * exampleU = exampleA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exampleL, exampleU, exampleA, Matrix.mul_apply, Fin.sum_univ_three]

/-- For every $t \in \mathbb{R}$, the pair `SaadSparse.Chapter10.exampleL t`,
`SaadSparse.Chapter10.exampleU` is an ILU(0) factorization of `SaadSparse.Chapter10.exampleA`. -/
theorem isILU0_example (t : ℝ) : Matrix.IsILU0 exampleA (exampleL t) exampleU := by
  refine ⟨⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_, fun i j hij => ?_,
    fun i j hij => ?_⟩, fun i j _ => ?_⟩
  · fin_cases i <;> simp [exampleL]
  · fin_cases i <;> fin_cases j <;> simp_all [exampleL]
  · fin_cases i <;> fin_cases j <;> simp_all [exampleU]
  · fin_cases i <;> fin_cases j <;> simp_all [exampleL, exampleA]
  · fin_cases i <;> fin_cases j <;> simp_all [exampleU, exampleA]
  · rw [exampleL_mul_exampleU]

/-- The family `SaadSparse.Chapter10.exampleL` is injective: if `exampleL s = exampleL t`, then
$s = t$. -/
theorem exampleL_injective {s t : ℝ} (h : exampleL s = exampleL t) : s = t := by
  have h21 : exampleL s 2 1 = exampleL t 2 1 := by rw [h]
  simpa [exampleL] using h21

/-- **Section 10.3.2** of [saad2003iterative], the remark before Algorithm 10.4. The ILU(0)
constraints do not determine the factors: there are $A, L, L', U \in \mathbb{R}^{3 \times 3}$
such that $(L, U)$ and $(L', U)$ are both ILU(0) factorizations of $A$ and $L \neq L'$.

The witness is `SaadSparse.Chapter10.exampleA`, which has a zero row, so its ILU(0) factors
satisfy $LU = A$ exactly. The entry of $L$ in the last row and the middle column multiplies only
that zero row, so it is free, and `SaadSparse.Chapter10.exampleL` gives infinitely many
factorizations. The standard ILU(0) of Algorithm 10.4 picks one member of the family, which is
why the book defines it by an algorithm. -/
theorem not_unique_isILU0 :
    ∃ A L L' U : Matrix (Fin 3) (Fin 3) ℝ,
      Matrix.IsILU0 A L U ∧ Matrix.IsILU0 A L' U ∧ L ≠ L' :=
  ⟨exampleA, exampleL 0, exampleL 1, exampleU, isILU0_example 0, isILU0_example 1,
    fun h => by simpa using exampleL_injective h⟩

/-! ### Section 10.3.3, Definition 10.5: the level of fill and ILU(p) -/

/-- **Definition 10.5** of [saad2003iterative], the initial level of fill. For
$A \in \mathbb{R}^{n \times n}$, the **initial level of fill** of the position $(i, j)$ is $0$
if $a_{ij} \neq 0$ or $i = j$, and $\infty$ otherwise.

The value is in `ℕ∞`. The definition is `Matrix.initialLevel`. -/
noncomputable abbrev initialLevel (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ℕ∞ :=
  Matrix.initialLevel A i j

/-- **Equation (10.17)** of [saad2003iterative], the level of fill after $k$ elimination steps. For
$A \in \mathbb{R}^{n \times n}$, $\mathrm{lev}_0$ is the initial level of fill, and the
elimination of the pivot $k$ updates the level of every position $(i, j)$ with $i > k$ and
$j > k$ by
$$\mathrm{lev}_{k+1}(i, j) = \min\{\mathrm{lev}_k(i, j), \ \mathrm{lev}_k(i, k) +
  \mathrm{lev}_k(k, j) + 1\},$$
and leaves the other positions unchanged. The range $i, j > k$ is that of the two loops of line
5 of Algorithm 10.2.

`levelOfFill A n` is "the level of fill value after all the updates (10.17) have been
performed". The definition is `Matrix.levelOfFill`, whose documentation explains why the
restriction to $i, j > k$ is needed. -/
noncomputable abbrev levelOfFill (A : Matrix (Fin n) (Fin n) ℝ) : ℕ → Fin n → Fin n → ℕ∞ :=
  Matrix.levelOfFill A

/-- **Section 10.3.3** of [saad2003iterative], Algorithm 10.5, the pattern $P_p$. For
$A \in \mathbb{R}^{n \times n}$ and $p \in \mathbb{N}$, the zero pattern of **ILU($p$)** is the
set of positions whose level of fill, after all the updates (10.17), exceeds $p$:
$$P_p = \{(i, j) : p < \mathrm{lev}_n(i, j)\}.$$

The definition is `Matrix.levelPattern`. -/
noncomputable abbrev levelPattern (A : Matrix (Fin n) (Fin n) ℝ) (p : ℕ) : Set (Fin n × Fin n) :=
  Matrix.levelPattern A p

/-- For every $p \in \mathbb{N}$, the ILU($p$) pattern $P_p$ is a zero pattern in the sense of
(10.11): a diagonal position has level of fill $0$, so it is never in $P_p$. Hence Theorem 10.2
applies to ILU($p$) for every $p$. -/
theorem isZeroPattern_levelPattern (A : Matrix (Fin n) (Fin n) ℝ) (p : ℕ) :
    IsZeroPattern (levelPattern A p) := by
  rintro ⟨i, j⟩ hq (rfl : i = j)
  exact Matrix.diag_notMem_levelPattern A p i hq

/-- **Section 10.3.3** of [saad2003iterative], the remark that $p = 0$ gives ILU(0). For
$A \in \mathbb{R}^{n \times n}$, the pattern $P_0$ is the off-diagonal zero pattern
$\{(i, j) : a_{ij} = 0, \ i \neq j\}$ of $A$, which is the pattern of `Matrix.IsILU0`. -/
theorem levelPattern_zero (A : Matrix (Fin n) (Fin n) ℝ) : levelPattern A 0 = A.zeroPattern :=
  Matrix.levelPattern_zero A

/-! ### Section 10.3.3, Theorems 10.6 and 10.7: fill-paths -/

section FillPath

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- **Section 10.3.3** of [saad2003iterative], fill-paths. Let $A \in \mathbb{R}^{n \times n}$. A
walk $w$ between $i$ and $j$ in the adjacency graph of $A$ is a **fill-path** if it is a path
and every vertex of $w$ other than $i$ and $j$ is less than both $i$ and $j$.

The definition is `Matrix.IsFillPath`. The graph is `Matrix.adjGraph` of Section 3.2.1, the
symmetrized graph without loops of the nonzero pattern of $A$; by
`SaadSparse.Chapter03.adjDigraph_eq`, a symmetric pattern loses nothing off the diagonal in this
graph. The symmetry of the pattern is a necessary hypothesis of Theorems 10.6 and 10.7 below:
the level of fill (10.17) is computed from the directed pattern, so without symmetry the
fill-path would have to be directed too. -/
abbrev IsFillPath {i j : Fin n} (w : A.adjGraph.Walk i j) : Prop :=
  Matrix.IsFillPath w

/-- **Theorem 10.7** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ have a symmetric
nonzero pattern, $a_{ij} \neq 0 \iff a_{ji} \neq 0$ for all $i, j$. Let $i \neq j$ and
$p \in \mathbb{N}$. Then the level of fill of $(i, j)$ at the end of the ILU process is $p$ if
and only if $p + 1$ is the least length of a fill-path between $i$ and $j$:
$$\mathrm{lev}_n(i, j) = p \iff p + 1 = \min\{\text{length of } w : w \text{ a fill-path between
  } i \text{ and } j\}.$$

The book's statement is that a fill-in at $(i, j)$ has level $p$ exactly when there is a
fill-path of length $p + 1$. Its proof uses the minimality: $\mathrm{lev}(a_{ij})$ "cannot be
$< p$, otherwise at some step $k$ we would have a path between $i$ and $j$ that is of length
$< p$". The formal statement makes the minimality explicit.

The level of fill is the result of the updates (10.17), not of the alternative rule (10.18),
whose characterization differs. The diagonal is excluded because a diagonal position has level
$0$ throughout. The proof is `Matrix.levelOfFill_eq_iff_isLeast`. -/
theorem theorem_10_7 (hsymm : ∀ i j, A i j ≠ 0 ↔ A j i ≠ 0) {i j : Fin n} (hij : i ≠ j) (p : ℕ) :
    levelOfFill A n i j = (p : ℕ∞) ↔
      IsLeast {ℓ : ℕ | ∃ w : A.adjGraph.Walk i j, IsFillPath w ∧ w.length = ℓ} (p + 1) :=
  Matrix.levelOfFill_eq_iff_isLeast hsymm hij p

/-- **Theorem 10.6** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ have a symmetric
nonzero pattern, $a_{ij} \neq 0 \iff a_{ji} \neq 0$ for all $i, j$, and let $i \neq j$. Then
there is a fill-in in the position $(i, j)$ at the end of Gaussian elimination if and only if
there is a fill-path between $i$ and $j$. Precisely, each of the following conditions is
equivalent to the existence of a fill-path between $i$ and $j$:

* the final level of fill $\mathrm{lev}_n(i, j)$ is finite;
* $(i, j) \notin P_p$ for some $p \in \mathbb{N}$.

The book quotes the result from Rose–Tarjan and George–Liu without proof. Here it follows from
Theorem 10.7 (`Matrix.levelOfFill_ne_top_iff`, `Matrix.exists_notMem_levelPattern_iff`). A
fill-in at the end of Gaussian elimination is a structural notion, and the recurrence (10.17)
read for finiteness describes it: $\mathrm{lev}(i, j)$ becomes finite at the pivot $k$ exactly
when $\mathrm{lev}(i, k)$ and $\mathrm{lev}(k, j)$ are both finite, which is the rule "$a_{ij}$
becomes nonzero when $a_{ik}$ and $a_{kj}$ are", and complete Gaussian elimination is the
ILU($p$) process with nothing dropped. Positions with an original nonzero entry are included, as
the fill-paths of length one. -/
theorem theorem_10_6 (hsymm : ∀ i j, A i j ≠ 0 ↔ A j i ≠ 0) {i j : Fin n} (hij : i ≠ j) :
    (levelOfFill A n i j ≠ ⊤ ↔ ∃ w : A.adjGraph.Walk i j, IsFillPath w) ∧
      ((∃ p : ℕ, (i, j) ∉ levelPattern A p) ↔ ∃ w : A.adjGraph.Walk i j, IsFillPath w) :=
  ⟨Matrix.levelOfFill_ne_top_iff hsymm hij,
    (Matrix.exists_notMem_levelPattern_iff A i j).trans (Matrix.levelOfFill_ne_top_iff hsymm hij)⟩

end FillPath

/-! ### Section 10.3.5: the modified factorization MILU -/

/-- **Equation (10.21)** of [saad2003iterative]. Let $P$ be a set of positions and let $(L, U)$ be a
modified incomplete factorization (MILU) of $A \in \mathbb{R}^{n \times n}$ for $P$. Then the
factorization is exact on the vector of ones $e$:
$$Ae = LUe.$$

In MILU the dropped entries of a row are subtracted from the diagonal entry of $U$ in that row,
and this is the constraint `Matrix.IsMILU.mulVec_one`. For a discretized partial differential
equation, $e$ is a constant function, so MILU is exact on constants. -/
theorem milu_mulVec_one {P : Set (Fin n × Fin n)} {A L U : Matrix (Fin n) (Fin n) ℝ}
    (h : Matrix.IsMILU P A L U) : A *ᵥ (1 : Fin n → ℝ) = (L * U) *ᵥ 1 := h.mulVec_one.symm

/-- Let $P$ be a set of positions and let $(L, U)$ be a modified incomplete factorization of
$A \in \mathbb{R}^{n \times n}$ for $P$. Then the residual $R = LU - A$ has zero row sums,
$Re = 0$. This is the property of the modified residual rows
$r^{new}_{i,*} = (r_{i,*} e) e_i^T - r_{i,*}$ of Section 10.3.5 of [saad2003iterative] (Example
10.3). -/
theorem milu_residual_mulVec_one {P : Set (Fin n × Fin n)} {A L U : Matrix (Fin n) (Fin n) ℝ}
    (h : Matrix.IsMILU P A L U) : (L * U - A) *ᵥ (1 : Fin n → ℝ) = 0 := h.residual_mulVec_one

/-- **Section 10.3.5** of [saad2003iterative], the diagonal compensation. Let $P$ be a set of
positions and let $(L, U)$ be a modified incomplete factorization of
$A \in \mathbb{R}^{n \times n}$ for $P$, with residual $R = LU - A$. Then for every $i$
$$r_{ii} = -\sum_{j \neq i} r_{ij}.$$
So the diagonal entry of the residual is minus the sum of the entries dropped in that row, which
is the modification $u_{ii} := u_{ii} - r_{i,*} e$. -/
theorem milu_residual_diag {P : Set (Fin n × Fin n)} {A L U : Matrix (Fin n) (Fin n) ℝ}
    (h : Matrix.IsMILU P A L U) (i : Fin n) :
    (L * U - A) i i = -∑ j ∈ Finset.univ.erase i, (L * U - A) i j := by
  have hrow : ∑ j, (L * U - A) i j = 0 := by
    have := congrFun h.residual_mulVec_one i
    simpa [Matrix.mulVec, dotProduct] using this
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => (L * U - A) i j) (Finset.mem_univ i)
  linarith [hrow, hsplit]

/-! ### Section 10.3.1: the two loop orders and Proposition 10.3 -/

section LoopOrder

variable (P : Set (Fin n × Fin n)) [DecidablePred (· ∈ P)]

/-- **Algorithms 10.1 and 10.3** of [saad2003iterative], lines 3–6, the operation
$\mathrm{ope}(\mathrm{row}(i), \mathrm{row}(k))$. Let $P$ be a set of positions, let $p$ be the
pivot row $k$ and let $r$ be the current row $i$. If $(i, k) \in P$, the operation leaves $r$
unchanged. Otherwise it sets $r_k := r_k / p_k$ and then, for every $j > k$ with
$(i, j) \notin P$,
$$r_j := r_j - r_k p_j,$$
with the new value of $r_k$; the other entries are unchanged. -/
noncomputable def iluRowOp (i k : Fin n) (p r : Fin n → ℝ) : Fin n → ℝ :=
  if (i, k) ∈ P then r
  else fun j =>
    if j = k then r k / p k
    else if k < j ∧ (i, j) ∉ P then r j - r k / p k * p j
    else r j

/-- **Algorithm 10.3** of [saad2003iterative], the $k$-loop on one row. For a matrix $\rho$ of pivot
rows, a row index $i$ and a starting row $a$, `rowOps P ρ i a m` applies
$\mathrm{ope}(\mathrm{row}(i), \mathrm{row}(k))$ for $k = 0, \dots, m - 1$ in this order, with
row $k$ of $\rho$ as the pivot row. Steps with $k \ge n$ do nothing. -/
noncomputable def rowOps (ρ : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (a : Fin n → ℝ) :
    ℕ → (Fin n → ℝ)
  | 0 => a
  | m + 1 => if h : m < n then
      iluRowOp P i ⟨m, h⟩ (fun j => ρ ⟨m, h⟩ j) (rowOps ρ i a m) else rowOps ρ i a m

/-- **Algorithm 10.3** of [saad2003iterative], the IKJ variant, after the outer steps
$i = 0, \dots, I - 1$. Step $i$ replaces row $i$ by the result of the $k$-loop for
$k = 0, \dots, i - 1$, with the current rows $0, \dots, i - 1$ as pivot rows; these rows are
already final, and the step does not change them or any other row. -/
noncomputable def ikjSweep (A : Matrix (Fin n) (Fin n) ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => A
  | I + 1 => Matrix.of fun i j =>
      if (i : ℕ) = I then rowOps P (ikjSweep A I) i (fun j' => ikjSweep A I i j') I j
      else ikjSweep A I i j

/-- **Algorithm 10.1** of [saad2003iterative], the KIJ variant, after the outer steps
$k = 0, \dots, K - 1$. Step $k$ applies $\mathrm{ope}(\mathrm{row}(i), \mathrm{row}(k))$ to
every row $i > k$, with the current row $k$ as pivot row, and leaves the rows $i \le k$
unchanged. Steps with $k \ge n$ do nothing.

The rows are updated independently: each reads only its own entries and the pivot row $k$, which
the step does not change. So this is exactly the $i$-loop of the algorithm. -/
noncomputable def kijSweep (A : Matrix (Fin n) (Fin n) ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => A
  | K + 1 =>
      if h : K < n then Matrix.of fun i j =>
        if K < (i : ℕ) then
          iluRowOp P i ⟨K, h⟩ (fun j' => kijSweep A K ⟨K, h⟩ j') (fun j' => kijSweep A K i j') j
        else kijSweep A K i j
      else kijSweep A K

/-- One step of Algorithm 10.3, entry by entry: step $I$ replaces row $I$ by the $k$-loop for
$k < I$ and leaves the other rows unchanged. -/
theorem ikjSweep_succ_apply (A : Matrix (Fin n) (Fin n) ℝ) (I : ℕ) (i j : Fin n) :
    ikjSweep P A (I + 1) i j
      = if (i : ℕ) = I then rowOps P (ikjSweep P A I) i (fun j' => ikjSweep P A I i j') I j
        else ikjSweep P A I i j := rfl

/-- One step of Algorithm 10.1, entry by entry: for $K < n$, step $K$ applies
$\mathrm{ope}(\mathrm{row}(i), \mathrm{row}(K))$ to each row $i > K$ and leaves the other rows
unchanged. -/
theorem kijSweep_succ_apply (A : Matrix (Fin n) (Fin n) ℝ) {K : ℕ} (h : K < n) (i j : Fin n) :
    kijSweep P A (K + 1) i j
      = if K < (i : ℕ) then
          iluRowOp P i ⟨K, h⟩ (fun j' => kijSweep P A K ⟨K, h⟩ j')
            (fun j' => kijSweep P A K i j') j
        else kijSweep P A K i j := by
  rw [kijSweep, dite_eq_left h]
  rfl

variable {P}

/-- The $k$-loop `SaadSparse.Chapter10.rowOps` with $m$ steps reads only the rows $0, \dots, m - 1$
of the pivot matrix: two pivot matrices that agree on these rows give the same result. -/
theorem rowOps_congr {ρ σ : Matrix (Fin n) (Fin n) ℝ} (i : Fin n) (a : Fin n → ℝ) {m : ℕ}
    (h : ∀ k : Fin n, (k : ℕ) < m → (fun j => ρ k j) = fun j => σ k j) :
    rowOps P ρ i a m = rowOps P σ i a m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [rowOps, rowOps, ih fun k hk => h k (by omega)]
      by_cases hm : m < n
      · rw [dite_eq_left hm, dite_eq_left hm, h ⟨m, hm⟩ (by simp)]
      · rw [dite_eq_right hm, dite_eq_right hm]

variable (P)

/-- After $I$ steps of Algorithm 10.3, the rows $i \ge I$ are still the rows of $A$. -/
theorem ikjSweep_apply_of_le (A : Matrix (Fin n) (Fin n) ℝ) {I : ℕ} {i : Fin n}
    (h : I ≤ (i : ℕ)) (j : Fin n) : ikjSweep P A I i j = A i j := by
  induction I with
  | zero => rfl
  | succ I ih =>
      rw [ikjSweep_succ_apply, ite_eq_right (by omega : ¬(i : ℕ) = I)]
      exact ih (by omega)

/-- If $i < I \le J$, then row $i$ after $J$ steps of Algorithm 10.3 is the same as after $I$ steps:
row $i$ is final after step $i$. -/
theorem ikjSweep_apply_of_lt (A : Matrix (Fin n) (Fin n) ℝ) {I : ℕ} {i : Fin n}
    (h : (i : ℕ) < I) : ∀ {J : ℕ}, I ≤ J → ∀ j, ikjSweep P A J i j = ikjSweep P A I i j := by
  intro J
  induction J with
  | zero => exact fun hIJ _ => absurd h (by omega)
  | succ J ih =>
      intro hIJ j
      rcases Nat.eq_or_lt_of_le hIJ with heq | hlt
      · rw [← heq]
      · rw [ikjSweep_succ_apply, ite_eq_right (by omega : ¬(i : ℕ) = J)]
        exact ih (by omega) j

/-- **Algorithm 10.3** of [saad2003iterative], the rows of the output. Let $P$ be a set of positions
and let $A \in \mathbb{R}^{n \times n}$. Then row $i$ of the output of Algorithm 10.3 is
obtained from row $i$ of $A$ by $\mathrm{ope}(\mathrm{row}(i), \mathrm{row}(k))$ for
$k = 0, \dots, i - 1$, with the final row $k$ of the output as pivot row each time. -/
theorem ikjSweep_row (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (fun j => ikjSweep P A n i j)
      = rowOps P (ikjSweep P A n) i (fun j => A i j) (i : ℕ) := by
  have hstep : ∀ j, ikjSweep P A n i j
      = rowOps P (ikjSweep P A (i : ℕ)) i (fun j' => ikjSweep P A (i : ℕ) i j') (i : ℕ) j := by
    intro j
    rw [ikjSweep_apply_of_lt P A (Nat.lt_succ_self _) i.isLt j, ikjSweep_succ_apply,
      ite_eq_left rfl]
  have hstart : (fun j' => ikjSweep P A (i : ℕ) i j') = fun j' => A i j' :=
    funext fun j' => ikjSweep_apply_of_le P A (le_refl _) j'
  have hrows : rowOps P (ikjSweep P A (i : ℕ)) i (fun j' => ikjSweep P A (i : ℕ) i j') (i : ℕ)
      = rowOps P (ikjSweep P A n) i (fun j => A i j) (i : ℕ) := by
    rw [hstart]
    exact rowOps_congr i _ fun k hk =>
      funext fun j => (ikjSweep_apply_of_lt P A hk (le_of_lt i.isLt) j).symm
  exact funext fun j => (hstep j).trans (congrFun hrows j)

/-- **Algorithm 10.1** of [saad2003iterative], the invariant. Let $P$ be a set of positions, let
$A \in \mathbb{R}^{n \times n}$ and let $K \in \mathbb{N}$. Then after $K$ outer steps of
Algorithm 10.1, row $i$ is obtained from row $i$ of $A$ by
$\mathrm{ope}(\mathrm{row}(i), \mathrm{row}(k))$ for $k = 0, \dots, \min(K, i) - 1$, with the
final row $k$ of Algorithm 10.3 as pivot row each time.

The reason is that the pivot row $k$ is final when step $k$ uses it, and no later step changes
it. -/
theorem kijSweep_row (A : Matrix (Fin n) (Fin n) ℝ) (K : ℕ) : ∀ i : Fin n,
    (fun j => kijSweep P A K i j)
      = rowOps P (ikjSweep P A n) i (fun j => A i j) (min K (i : ℕ)) := by
  induction K with
  | zero => exact fun i => by rw [Nat.zero_min]; rfl
  | succ K ih =>
      intro i
      by_cases hn : K < n
      · by_cases hKi : K < (i : ℕ)
        · have hpivot : (fun j => kijSweep P A K (⟨K, hn⟩ : Fin n) j)
              = fun j => ikjSweep P A n (⟨K, hn⟩ : Fin n) j := by
            rw [ih ⟨K, hn⟩, ikjSweep_row P A ⟨K, hn⟩]
            simp
          have hrow : (fun j => kijSweep P A K i j)
              = rowOps P (ikjSweep P A n) i (fun j => A i j) K := by
            rw [ih i, min_eq_left (le_of_lt hKi)]
          refine funext fun j => ?_
          rw [kijSweep_succ_apply P A hn, ite_eq_left hKi, hpivot, hrow,
            min_eq_left (by omega : K + 1 ≤ (i : ℕ)), rowOps, dite_eq_left hn]
        · refine funext fun j => ?_
          rw [kijSweep_succ_apply P A hn, ite_eq_right hKi, congrFun (ih i) j,
            min_eq_right (by omega : (i : ℕ) ≤ K), min_eq_right (by omega : (i : ℕ) ≤ K + 1)]
      · have hik : (i : ℕ) ≤ K := by omega
        refine funext fun j => ?_
        rw [kijSweep, dite_eq_right hn, congrFun (ih i) j, min_eq_right hik,
          min_eq_right (by omega : (i : ℕ) ≤ K + 1)]

/-- **Proposition 10.3** of [saad2003iterative]. Let $P$ be a static set of positions and let
$A \in \mathbb{R}^{n \times n}$. Then the KIJ variant, Algorithm 10.1, and the IKJ variant,
Algorithm 10.3, produce the same matrix, and hence the same factors.

**Generalization.** Neither algorithm here performs line 1 of the book, "for each $(i, j) \in P$
set $a_{ij} = 0$". This line is common to both algorithms, so the formal statement, for an
arbitrary starting matrix, implies the printed one.

The book's proof writes the first two loops of Algorithm 10.1 as a double loop over $k$ and $i$
with body $\mathrm{ope}(\mathrm{row}(i), \mathrm{row}(k))$ and permutes the two loops. The
invariant `SaadSparse.Chapter10.kijSweep_row` justifies this: in both orders, row $i$ receives
$\mathrm{ope}(\mathrm{row}(i), \mathrm{row}(k))$ for $k = 0, \dots, i - 1$ in increasing order
of $k$, each time with the final row $k$. The pattern must be static, as the book warns: both
algorithms read the same $P$ throughout, and a pattern determined during the elimination would
not have this property. -/
theorem proposition_10_3 (A : Matrix (Fin n) (Fin n) ℝ) :
    kijSweep P A n = ikjSweep P A n := by
  ext i j
  rw [congrFun (kijSweep_row P A n i) j, min_eq_right (le_of_lt i.isLt),
    ← congrFun (ikjSweep_row P A i) j]

end LoopOrder

end SaadSparse.Chapter10
