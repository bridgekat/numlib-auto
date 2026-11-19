/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.MMatrix
import Numlib.LinearAlgebra.Matrix.PerronFrobenius
import Numlib.Stationary.Splitting
import NumlibSurface.SaadSparse.Common

/-!
# Saad, Section 1.10: Nonnegative matrices, M-matrices

This module formalizes §1.10 of [saad2003iterative]: the entrywise order on real matrices
(Definition 1.23) and its calculus (Proposition 1.24, Proposition 1.26 and Corollary 1.27), the
Perron–Frobenius theorem (Theorem 1.25), the monotonicity of the spectral radius (Theorem 1.28), the
criterion for the Neumann series of a nonnegative matrix (Theorem 1.29), and M-matrices (Definition
1.30 and Theorems 1.31–1.33). For real matrices, $A \le B$ means $a_{ij} \le b_{ij}$ for all $i, j$.
A matrix $A$ is an M-matrix when $a_{ii} > 0$, $a_{ij} \le 0$ for $i \neq j$, $A$ is nonsingular and
$A^{-1} \ge 0$.

The main results are: an irreducible nonnegative matrix has the eigenvalue $\rho(A)$ with a positive
eigenvector, and this eigenvalue is simple; $0 \le A \le B$ implies $\rho(A) \le \rho(B)$; for
$B \ge 0$, $\rho(B) < 1$ if and only if $I - B$ is nonsingular with $(I - B)^{-1} \ge 0$; a matrix
with positive diagonal and nonpositive off-diagonal entries is an M-matrix exactly when its Jacobi
iteration matrix $I - D^{-1} A$ has spectral radius less than $1$; and an M-matrix stays an M-matrix
when its entries increase and its off-diagonal entries stay nonpositive. The proofs specialize the
backbone modules `Numlib.LinearAlgebra.Matrix.Order`, `Numlib.LinearAlgebra.Matrix.PerronFrobenius`,
`Numlib.LinearAlgebra.Matrix.MMatrix` and `Numlib.Stationary.Splitting`.

## Main definitions

* Definition 1.23, `SaadSparse.Chapter01.definition_1_23`: the entrywise order and nonnegative and
  negative matrices.
* Definition 1.30, `SaadSparse.Chapter01.definition_1_30`: `Matrix.IsMMatrix` is equivalent to the
  four clauses of the book's definition of an M-matrix.

## Main results

* Proposition 1.24, `SaadSparse.Chapter01.proposition_1_24`: the entrywise order is a partial order,
  nonnegative matrices are closed under sums, products and powers, the order is preserved by
  transposition, and $\|\cdot\|_1$ and $\|\cdot\|_\infty$ are monotone on nonnegative matrices.
* Problem P-1.28, `SaadSparse.Chapter01.problem_1_28`: $\|\cdot\|_2$ is monotone on nonnegative
  matrices.
* Theorem 1.25, `SaadSparse.Chapter01.theorem_1_25`: an irreducible nonnegative matrix has the
  eigenvalue $\rho(A)$ with a positive eigenvector (Perron–Frobenius theorem).
* Theorem 1.25, `SaadSparse.Chapter01.theorem_1_25_simple`: the eigenspace for $\rho(A)$ has
  dimension $1$.
* Theorem 1.25, `SaadSparse.Chapter01.theorem_1_25_algSimple`: $\rho(A)$ is a simple root of the
  characteristic polynomial.
* Theorem 1.25, `SaadSparse.Chapter01.theorem_1_25_pos`: $\rho(A) > 0$ for an irreducible matrix of
  order $n \ge 2$.
* Proposition 1.26, `SaadSparse.Chapter01.proposition_1_26`: multiplication by a nonnegative matrix
  on either side preserves the entrywise order.
* Corollary 1.27, `SaadSparse.Chapter01.corollary_1_27`: $0 \le A \le B$ implies $A^k \le B^k$.
* Theorem 1.28, `SaadSparse.Chapter01.theorem_1_28`: $0 \le A \le B$ implies $\rho(A) \le \rho(B)$.
* Theorem 1.29, `SaadSparse.Chapter01.theorem_1_29`: for $B \ge 0$, $\rho(B) < 1$ if and only if
  $I - B$ is nonsingular with $(I - B)^{-1} \ge 0$.
* Theorem 1.31, `SaadSparse.Chapter01.theorem_1_31`: a matrix with positive diagonal and nonpositive
  off-diagonal entries is an M-matrix if and only if $\rho(I - D^{-1} A) < 1$.
* Theorem 1.31, `SaadSparse.Chapter01.theorem_1_31_jacobi`: $I - D^{-1} A$ is the iteration operator
  of the Jacobi splitting.
* Theorem 1.32, `SaadSparse.Chapter01.theorem_1_32`: clause (1) of Definition 1.30 follows from the
  other three.
* Theorem 1.33, `SaadSparse.Chapter01.theorem_1_33`: if $A$ is an M-matrix, $A \le B$ and
  $b_{ij} \le 0$ for $i \neq j$, then $B$ is an M-matrix.

## Conventions

* The book's $A \ge O$ and $B \ge A$ are the entrywise order, `Matrix.EntrywiseNonneg` and
  `Matrix.EntrywiseLE` (notation `≤ₑ`) of `Numlib.LinearAlgebra.Matrix.Order`. Mathlib's `≤` on
  matrices is the Loewner order, which is a different relation.
* The book's $\rho(A)$ for a real matrix is `Matrix.complexSpectralRadius A`, the spectral radius of
  the complexification. The real spectrum `spectrum ℝ` of a real matrix does not give the spectral
  radius.

## Implementation notes

* Definition 1.30 is `Matrix.IsMMatrix` of `Numlib.LinearAlgebra.Matrix.MMatrix`, which has only the
  clauses (2)–(4) of the book. Clause (1) follows from them; this is Theorem 1.32 of the book,
  `Matrix.IsMMatrix.diag_pos`.
* Theorem 1.25 calls the Perron eigenvalue *simple*, and both readings of the word are proved:
  `SaadSparse.Chapter01.theorem_1_25_simple` states that the eigenspace has dimension one, and
  `SaadSparse.Chapter01.theorem_1_25_algSimple` states that $\rho(A)$ is a simple root of the
  characteristic polynomial, which is what the book means. `SaadSparse.Chapter01.theorem_1_25_pos`
  adds the positivity of $\rho(A)$ for $n \ge 2$, which the book does not state.
* Theorems 1.31–1.33 write the Jacobi iteration matrix out as $I - D^{-1} A$.
  `SaadSparse.Chapter01.theorem_1_31_jacobi` identifies it with the iteration operator of the Jacobi
  splitting of `Numlib.Stationary.Splitting`, which is the form that §4.1 uses.

## Deviations from the source

* **Problem P-1.28** (reading). The theorem gives the norm conclusion of the exercise. See
  `SaadSparse.Chapter01.problem_1_28`.
* **Theorem 1.25** (reading). The existence and simplicity clauses require a positive matrix
  dimension. See `SaadSparse.Chapter01.theorem_1_25` and
  `SaadSparse.Chapter01.theorem_1_25_algSimple`.
* **Proposition 1.26** (generalization). Only the multiplying matrix $C$ needs to be entrywise
  nonnegative. See `SaadSparse.Chapter01.proposition_1_26`.

## Not formalized

* **Definition 1.23, strict positivity and negativity.** The declaration gives the weak order
  and the corresponding weak sign conditions.
* **Problem P-1.28, the entrywise comparison of the Gram matrices.** The surface states the
  norm comparison.
* **Equation (1.47).** The Neumann series identity is available as
  `Matrix.hasSum_pow_inv_one_sub_of_complexSpectralRadius_lt_one`.
* **Problem P-1.33.** The problem asks whether clause (4) of Definition 1.30, the nonnegativity of
  the inverse, is redundant in the way that Theorem 1.32 shows clause (1) to be. It is not, and the
  answer is a counterexample rather than a theorem, so it has no declaration: the matrix
  $\begin{bmatrix} 1 & -2 \\ -2 & 1 \end{bmatrix}$ has positive diagonal entries, nonpositive
  off-diagonal entries and determinant $-3$, and its inverse $\begin{bmatrix} -1/3 & -2/3 \\ -2/3 &
  -1/3 \end{bmatrix}$ is entrywise negative.
-/

open Matrix

open scoped SaadSparse Matrix

namespace SaadSparse.Chapter01

variable {n : ℕ}

/-! ### The entrywise order (Definition 1.23, Propositions 1.24 and 1.26, Corollary 1.27) -/

/-- **Definition 1.23** of [saad2003iterative]. Let $A, B \in \mathbb{R}^{m \times k}$. Then
$A \le B$ means $a_{ij} \le b_{ij}$ for all $i, j$; the matrix $A$ is **nonnegative** when
$O \le A$, that is $a_{ij} \ge 0$ for all $i, j$; and $A$ is **nonpositive** when $A \le O$,
that is $-A$ is nonnegative. Moreover, $A \le B$ if and only if
$-B \le -A$.

The order is the entrywise order `Matrix.EntrywiseLE` (notation `≤ₑ`) of
`Numlib.LinearAlgebra.Matrix.Order`. Nonnegativity is `Matrix.EntrywiseNonneg`. Mathlib's `≤` on
matrices is the Loewner order. The five clauses of the statement are, in order: the order
unfolded; nonnegativity as $O \le A$; nonnegativity unfolded; nonpositivity; and
the reversal of the order under negation. The book remarks that $\le$ is a partial order and not
a total one; the axioms of a partial order are clause 1 of
`SaadSparse.Chapter01.proposition_1_24`.

The remaining word of the book, *positive* for $A > O$, is not defined here and is never used in
that form. What §1.10 and Theorem 1.25 need is entrywise strict positivity, $a_{ij} > 0$ for all
$i, j$, which is written out where it occurs. -/
theorem definition_1_23 {m k : ℕ} (A B : Matrix (Fin m) (Fin k) ℝ) :
    (A ≤ₑ B ↔ ∀ i j, A i j ≤ B i j) ∧
      (A.EntrywiseNonneg ↔ (0 : Matrix (Fin m) (Fin k) ℝ) ≤ₑ A) ∧
      (A.EntrywiseNonneg ↔ ∀ i j, 0 ≤ A i j) ∧
      ((-A).EntrywiseNonneg ↔ A ≤ₑ (0 : Matrix (Fin m) (Fin k) ℝ)) ∧
      (A ≤ₑ B ↔ (-B) ≤ₑ (-A)) := by
  refine ⟨Iff.rfl, Iff.rfl, Iff.rfl, ?_, ?_⟩
  · exact forall_congr' fun i => forall_congr' fun j => by
      rw [Matrix.zero_apply, Matrix.neg_apply, neg_nonneg]
  · exact forall_congr' fun i => forall_congr' fun j => by
      rw [Matrix.neg_apply, Matrix.neg_apply, neg_le_neg_iff]

open scoped Matrix.Norms.Operator in
/-- **Proposition 1.24** of [saad2003iterative]. For matrices in $\mathbb{R}^{n \times n}$ and the
entrywise order:

1. the order is reflexive, antisymmetric and transitive;
2. if $A, B \ge O$, then $A + B \ge O$ and $AB \ge O$;
3. if $A \ge O$, then $A^k \ge O$ for every $k \ge 0$;
4. if $A \le B$, then $A^T \le B^T$;
5. if $O \le A \le B$, then $\|A\|_1 \le \|B\|_1$ and $\|A\|_\infty \le \|B\|_\infty$.

The norm $\|\cdot\|_\infty$, the maximum absolute row sum, is the scoped instance
`Matrix.Norms.Operator`, and $\|A\|_1$, the maximum absolute column sum, is written as
$\|A^T\|_\infty$. Every clause restates a result of `Numlib.LinearAlgebra.Matrix.Order` or
`Numlib.LinearAlgebra.Matrix.PerronFrobenius`, except clause 4, which has a one-line proof. The
$2$-norm form of clause 5 is Problem P-1.28, `SaadSparse.Chapter01.problem_1_28`, stated
separately because the Euclidean operator norm is a different scoped instance on the same type. -/
theorem proposition_1_24 :
    (∀ A : Matrix (Fin n) (Fin n) ℝ, A ≤ₑ A) ∧
      (∀ A B : Matrix (Fin n) (Fin n) ℝ, A ≤ₑ B → B ≤ₑ A → A = B) ∧
      (∀ A B C : Matrix (Fin n) (Fin n) ℝ, A ≤ₑ B → B ≤ₑ C → A ≤ₑ C) ∧
      (∀ A B : Matrix (Fin n) (Fin n) ℝ, A.EntrywiseNonneg → B.EntrywiseNonneg →
        (A + B).EntrywiseNonneg ∧ (A * B).EntrywiseNonneg) ∧
      (∀ (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ), A.EntrywiseNonneg → (A ^ k).EntrywiseNonneg) ∧
      (∀ A B : Matrix (Fin n) (Fin n) ℝ, A ≤ₑ B → Aᵀ ≤ₑ Bᵀ) ∧
      (∀ A B : Matrix (Fin n) (Fin n) ℝ, A.EntrywiseNonneg → A ≤ₑ B →
        ‖Aᵀ‖ ≤ ‖Bᵀ‖ ∧ ‖A‖ ≤ ‖B‖) :=
  ⟨EntrywiseLE.refl,
    fun _ _ hAB hBA => hAB.antisymm hBA,
    fun _ _ _ hAB hBC => hAB.trans hBC,
    fun _ _ hA hB => ⟨hA.add hB, hA.mul hB⟩,
    fun _ k hA => hA.pow k,
    fun _ _ hAB i j => hAB j i,
    fun _ _ hA hAB => ⟨EntrywiseLE.linfty_opNorm_transpose_le hA hAB,
      EntrywiseLE.linfty_opNorm_le hA hAB⟩⟩

open scoped Matrix.Norms.L2Operator in
/-- **Problem P-1.28** of [saad2003iterative]. Let $A, B \in \mathbb{R}^{n \times n}$ with
$O \le A \le B$ entrywise. Then $\|A\|_2 \le \|B\|_2$.

**Reading.** The exercise first asks for $O \le A^T A \le B^T B$ entrywise and then asks for
the norm conclusion. This declaration gives the norm conclusion.

This is the $2$-norm form of clause 5 of Proposition 1.24. The norm is the scoped instance
`Matrix.Norms.L2Operator`, and the proof is `Matrix.EntrywiseLE.l2_opNorm_le` of
`Numlib.LinearAlgebra.Matrix.PerronFrobenius`. -/
theorem problem_1_28 {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.EntrywiseNonneg) (hAB : A ≤ₑ B) :
    ‖A‖ ≤ ‖B‖ :=
  EntrywiseLE.l2_opNorm_le hA hAB

/-- **Proposition 1.26** of [saad2003iterative]. Let $A, B, C \in \mathbb{R}^{n \times n}$ with
$C \ge O$ and $A \le B$ entrywise. Then
$$CA \le CB \quad \text{and} \quad AC \le BC.$$

**Generalization.** The book assumes that $A$, $B$ and $C$ are all nonnegative. Each comparison
uses entrywise monotonicity of multiplication by $C$, so $A$ and $B$ only need to be ordered.

The proof uses `Matrix.EntrywiseLE.mul_of_entrywiseNonneg_left` and its counterpart for the
right side. -/
theorem proposition_1_26 {A B C : Matrix (Fin n) (Fin n) ℝ} (hC : C.EntrywiseNonneg)
    (hAB : A ≤ₑ B) : C * A ≤ₑ C * B ∧ A * C ≤ₑ B * C :=
  ⟨EntrywiseLE.mul_of_entrywiseNonneg_left hC hAB,
    EntrywiseLE.mul_of_entrywiseNonneg_right hC hAB⟩

/-- **Corollary 1.27** of [saad2003iterative], equation (1.42). Let
$A, B \in \mathbb{R}^{n \times n}$ with $O \le A \le B$ entrywise. Then $A^k \le B^k$ for every
$k \ge 0$.

The proof is `Matrix.EntrywiseLE.pow`, which is the induction (1.43)–(1.44) of the book. -/
theorem corollary_1_27 {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.EntrywiseNonneg) (hAB : A ≤ₑ B)
    (k : ℕ) : A ^ k ≤ₑ B ^ k :=
  EntrywiseLE.pow hA hAB k

/-! ### The Perron–Frobenius theorem (Theorem 1.25) -/

/-- **Theorem 1.25** of [saad2003iterative] (Perron–Frobenius theorem). Let
$A \in \mathbb{R}^{n \times n}$ with $n \ge 1$ be nonnegative and irreducible. Then $\rho(A)$ is
an eigenvalue of $A$, with an eigenvector $x \in \mathbb{R}^n$ all of whose entries are
positive:
$$Ax = \rho(A) x, \qquad x_i > 0 \text{ for all } i.$$

**Reading.** The text leaves the dimension implicit. The declaration requires $n \ge 1$, since
the eigenvector must be nonzero and the zero-dimensional space has none.

The book states the theorem without proof. The proof is
`Matrix.IsIrreducible.exists_pos_hasEigenvector_complexSpectralRadius` of
`Numlib.LinearAlgebra.Matrix.PerronFrobenius`. Irreducibility is Mathlib's
`Matrix.IsIrreducible`: the matrix is entrywise nonnegative and the directed graph of its
positive entries is strongly connected. This is the notion of the book in §1.10, read through
the adjacency graph of §3.3.4. The simplicity clause is
`SaadSparse.Chapter01.theorem_1_25_simple`. -/
theorem theorem_1_25 [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsIrreducible) :
    Module.End.HasEigenvalue A.mulVecLin A.complexSpectralRadius.toReal ∧
      ∃ x : Fin n → ℝ, (∀ i, 0 < x i) ∧ A *ᵥ x = A.complexSpectralRadius.toReal • x := by
  obtain ⟨x, hpos, hx⟩ := hA.exists_pos_hasEigenvector_complexSpectralRadius
  refine ⟨Module.End.hasEigenvalue_of_hasEigenvector (x := x) ⟨?_, ?_⟩, x, hpos, hx⟩
  · rw [Module.End.mem_eigenspace_iff, mulVecLin_apply]
    exact hx
  · intro h
    exact absurd (congrFun h (Classical.arbitrary (Fin n))) (hpos _).ne'

/-- **Theorem 1.25** of [saad2003iterative], simplicity in the geometric sense. Let
$A \in \mathbb{R}^{n \times n}$ with $n \ge 1$ be nonnegative and irreducible. Then the
eigenspace of $A$ for the eigenvalue $\rho(A)$ has dimension $1$.

**Reading.** The dimension is positive, as in `SaadSparse.Chapter01.theorem_1_25`. In dimension
zero every eigenspace has dimension zero.

The proof is `Matrix.IsIrreducible.finrank_eigenspace_complexSpectralRadius_eq_one`. -/
theorem theorem_1_25_simple [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsIrreducible) :
    Module.finrank ℝ
        (Module.End.eigenspace A.mulVecLin A.complexSpectralRadius.toReal) = 1 :=
  hA.finrank_eigenspace_complexSpectralRadius_eq_one

/-- **Theorem 1.25** of [saad2003iterative], simplicity in the algebraic sense, which is the sense
of the word in the book. Let $A \in \mathbb{R}^{n \times n}$ with $n \ge 1$ be nonnegative and
irreducible. Then $\rho(A)$ is a simple root of the characteristic polynomial of $A$.

**Reading.** The dimension is positive, as in `SaadSparse.Chapter01.theorem_1_25`. The
characteristic polynomial in dimension zero is constant and has no roots.

The proof is `Matrix.IsIrreducible.rootMultiplicity_charpoly_complexSpectralRadius`. It derives
the statement from the geometric simplicity: the positive left Perron eigenvector rules out a
Jordan chain of length two. -/
theorem theorem_1_25_algSimple [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsIrreducible) :
    A.charpoly.rootMultiplicity A.complexSpectralRadius.toReal = 1 :=
  hA.rootMultiplicity_charpoly_complexSpectralRadius

/-- **Theorem 1.25** of [saad2003iterative], positivity. Let $A \in \mathbb{R}^{n \times n}$ with
$n \ge 2$ be nonnegative and irreducible. Then $\rho(A) > 0$.

The book does not print this clause in Theorem 1.25. It is what makes the theorem useful for an
irreducible matrix with a zero diagonal, and the applications of §1.10 to M-matrices use it. The
proof is `Matrix.IsIrreducible.complexSpectralRadius_pos`: if $\rho(A) = 0$, the positive Perron
vector would be a null vector of $A$, which forces $A = O$, and $O$ is reducible for $n \ge 2$. -/
theorem theorem_1_25_pos {A : Matrix (Fin n) (Fin n) ℝ} (hn : 2 ≤ n) (hA : A.IsIrreducible) :
    0 < A.complexSpectralRadius.toReal :=
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  hA.complexSpectralRadius_pos

/-! ### The spectral radius of a nonnegative matrix (Theorems 1.28 and 1.29) -/

/-- **Theorem 1.28** of [saad2003iterative], equations (1.45)–(1.46). Let
$A, B \in \mathbb{R}^{n \times n}$ with $O \le A \le B$ entrywise. Then $\rho(A) \le \rho(B)$.

The proof is `Matrix.complexSpectralRadius_le_of_entrywiseLE`, which is the proof of the book:
Gelfand's formula applied to Corollary 1.27 and clause 5 of Proposition 1.24. -/
theorem theorem_1_28 {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.EntrywiseNonneg) (hAB : A ≤ₑ B) :
    A.complexSpectralRadius ≤ B.complexSpectralRadius :=
  complexSpectralRadius_le_of_entrywiseLE hA hAB

/-- **Theorem 1.29** of [saad2003iterative]. Let $B \in \mathbb{R}^{n \times n}$ be
nonnegative. Then $\rho(B) < 1$ if and only if $I - B$ is nonsingular and $(I - B)^{-1}$ is
nonnegative.

The proof is `Matrix.EntrywiseNonneg.complexSpectralRadius_lt_one_iff`. Theorem 4.4 and the
characterizations of M-matrices below rest on this theorem. -/
theorem theorem_1_29 {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.EntrywiseNonneg) :
    B.complexSpectralRadius < 1 ↔ IsUnit (1 - B) ∧ (1 - B)⁻¹.EntrywiseNonneg :=
  hB.complexSpectralRadius_lt_one_iff

/-! ### M-matrices (Definition 1.30, Theorems 1.31–1.33) -/

section MMatrix

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- **Definition 1.30** of [saad2003iterative]. A matrix $A \in \mathbb{R}^{n \times n}$ is an
**M-matrix** if (1) $a_{ii} > 0$ for all $i$, (2) $a_{ij} \le 0$ for $i \neq j$, (3) $A$ is
nonsingular, and (4) $A^{-1} \ge O$ entrywise. The theorem states that `Matrix.IsMMatrix` holds
for $A$ if and only if these four clauses hold.

`Matrix.IsMMatrix` of `Numlib.LinearAlgebra.Matrix.MMatrix` has only the clauses (2)–(4). Clause
(1) follows from them; this is Theorem 1.32 of the book, `Matrix.IsMMatrix.diag_pos`. So the
four clauses of the book and the three of `Matrix.IsMMatrix` define the same class. -/
theorem definition_1_30 : A.IsMMatrix ↔
    (∀ i, 0 < A i i) ∧ (∀ i j, i ≠ j → A i j ≤ 0) ∧ IsUnit A ∧ A⁻¹.EntrywiseNonneg :=
  ⟨fun hA => ⟨hA.diag_pos, hA.offDiag_nonpos, hA.isUnit, hA.inv_entrywiseNonneg⟩,
    fun ⟨_, h2, h3, h4⟩ => ⟨h2, h3, h4⟩⟩

/-- A diagonal matrix with nonnegative diagonal entries is entrywise nonnegative. -/
private theorem entrywiseNonneg_diagonal {d : Fin n → ℝ} (hd : ∀ i, 0 ≤ d i) :
    (diagonal d).EntrywiseNonneg := by
  refine entrywiseNonneg_iff.2 fun i j => ?_
  by_cases h : i = j
  · subst h; rw [diagonal_apply_eq]; exact hd i
  · rw [diagonal_apply_ne _ h]

/-- If every diagonal entry of $A$ is nonzero, the inverse of the diagonal part $D$ of $A$ is the
diagonal matrix with entries $a_{ii}^{-1}$. -/
private theorem inv_diagPart_eq (hd : ∀ i, A i i ≠ 0) :
    (diagPart A)⁻¹ = diagonal fun i => (A i i)⁻¹ := by
  have hD : diagPart A = diagonal A.diag := rfl
  refine inv_eq_right_inv ?_
  rw [hD, diagonal_mul_diagonal, ← diagonal_one]
  refine congrArg diagonal (funext fun i => ?_)
  simpa only [Pi.mul_apply, Pi.one_apply, diag_apply] using mul_inv_cancel₀ (hd i)

/-- If every diagonal entry of $A$ is nonzero, the entries of the Jacobi iteration matrix
$I - D^{-1} A$ are $\delta_{ij} - a_{ij} / a_{ii}$. -/
private theorem jacobiMatrix_apply (hd : ∀ i, A i i ≠ 0) (i j : Fin n) :
    (1 - (diagPart A)⁻¹ * A) i j = (if i = j then 1 else 0) - (A i i)⁻¹ * A i j := by
  rw [Matrix.sub_apply, Matrix.one_apply, inv_diagPart_eq hd, diagonal_mul]

/-- If $A$ has positive diagonal and nonpositive off-diagonal entries, its Jacobi iteration matrix
$I - D^{-1} A$ is entrywise nonnegative, so Theorem 1.29 applies to it. -/
private theorem entrywiseNonneg_jacobiMatrix (hd : ∀ i, 0 < A i i)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) : (1 - (diagPart A)⁻¹ * A).EntrywiseNonneg := by
  refine entrywiseNonneg_iff.2 fun i j => ?_
  rw [jacobiMatrix_apply (fun i => (hd i).ne') i j]
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl, inv_mul_cancel₀ (hd i).ne', sub_self]
  · rw [ite_eq_right h, zero_sub, neg_nonneg]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (hd i).le) (hoff i j h)

/-- **Theorem 1.31** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ with $a_{ii} > 0$
for all $i$ and $a_{ij} \le 0$ for $i \neq j$, and let $D$ be the diagonal part of $A$. Then $A$
is an M-matrix if and only if the Jacobi iteration matrix $B = I - D^{-1} A$ satisfies
$$\rho(B) < 1.$$

The proof is the proof of the book. The two sign conditions make $B$ entrywise nonnegative, so
Theorem 1.29 applies to it. The relation $I - B = D^{-1} A$ gives $A = D(I - B)$ with $D$ and
$D^{-1}$ nonnegative, so $A$ is nonsingular with a nonnegative inverse if and only if $I - B$
is. -/
theorem theorem_1_31 (hd : ∀ i, 0 < A i i) (hoff : ∀ i j, i ≠ j → A i j ≤ 0) :
    A.IsMMatrix ↔ (1 - (diagPart A)⁻¹ * A).complexSpectralRadius < 1 := by
  have hdne : ∀ i, A i i ≠ 0 := fun i => (hd i).ne'
  have hDunit : IsUnit (diagPart A) := (isUnit_diagPart_iff A).2 hdne
  have hDdet : IsUnit (diagPart A).det := (isUnit_iff_isUnit_det _).1 hDunit
  have hDnn : (diagPart A).EntrywiseNonneg :=
    entrywiseNonneg_diagonal (d := A.diag) fun i => (hd i).le
  have hDinvnn : ((diagPart A)⁻¹).EntrywiseNonneg := by
    rw [inv_diagPart_eq hdne]
    exact entrywiseNonneg_diagonal fun i => inv_nonneg.2 (hd i).le
  have hsub : 1 - (1 - (diagPart A)⁻¹ * A) = (diagPart A)⁻¹ * A := sub_sub_cancel _ _
  rw [theorem_1_29 (entrywiseNonneg_jacobiMatrix hd hoff), hsub]
  constructor
  · intro hA
    refine ⟨(isUnit_nonsing_inv_iff.2 hDunit).mul hA.isUnit, ?_⟩
    have hinv : ((diagPart A)⁻¹ * A)⁻¹ = A⁻¹ * diagPart A := by
      rw [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hDdet]
    rw [hinv]
    exact hA.inv_entrywiseNonneg.mul hDnn
  · rintro ⟨hu, hnn⟩
    have hAeq : A = diagPart A * ((diagPart A)⁻¹ * A) := by
      rw [← Matrix.mul_assoc, mul_nonsing_inv _ hDdet, Matrix.one_mul]
    refine ⟨hoff, hAeq ▸ hDunit.mul hu, ?_⟩
    have hAinv : A⁻¹ = ((diagPart A)⁻¹ * A)⁻¹ * (diagPart A)⁻¹ := by
      conv_lhs => rw [hAeq]
      rw [Matrix.mul_inv_rev]
    rw [hAinv]
    exact hnn.mul hDinvnn

/-- **Theorem 1.31** of [saad2003iterative], the Jacobi splitting. Let
$A \in \mathbb{R}^{n \times n}$ have a nonsingular diagonal part $D$. Then the iteration
operator of the Jacobi splitting $A = D - (E + F)$ of `Numlib.Stationary.Splitting` is
$I - D^{-1} A$, the matrix of Theorem 1.31.

This is the form that §4.1 uses. With `Matrix.jacobiSplitting_iterationOperator`, it makes the
M-matrix hypothesis of Chapter 4 checkable from the sign pattern of $A$ alone. -/
theorem theorem_1_31_jacobi (h : IsUnit (diagPart A)) :
    (jacobiSplitting A h).iterationOperator = 1 - (diagPart A)⁻¹ * A := by
  have hm : (jacobiSplitting A h).m = diagPart A := rfl
  rw [Stationary.Splitting.iterationOperator, hm, ← nonsing_inv_eq_ringInverse]

/-- **Theorem 1.32** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be nonsingular,
with $a_{ij} \le 0$ for $i \neq j$ and $A^{-1} \ge O$ entrywise. Then $a_{ii} > 0$ for all $i$,
so $A$ is an M-matrix, and the Jacobi iteration matrix satisfies $\rho(I - D^{-1} A) < 1$, where
$D$ is the diagonal part of $A$. Thus clause (1) of Definition 1.30 follows from the other three
clauses.

The diagonal clause is `Matrix.IsMMatrix.diag_pos`, whose proof is the proof of the book: in the
entry $(AA^{-1})_{ii} = 1$ every off-diagonal term is nonpositive, so
$a_{ii} (A^{-1})_{ii} \ge 1$ and both factors are positive. -/
theorem theorem_1_32 (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hu : IsUnit A)
    (hinv : A⁻¹.EntrywiseNonneg) :
    (∀ i, 0 < A i i) ∧ A.IsMMatrix ∧ (1 - (diagPart A)⁻¹ * A).complexSpectralRadius < 1 :=
  have hA : A.IsMMatrix := ⟨hoff, hu, hinv⟩
  ⟨hA.diag_pos, hA, (theorem_1_31 hA.diag_pos hoff).1 hA⟩

/-- **Theorem 1.33** of [saad2003iterative]. Let $A, B \in \mathbb{R}^{n \times n}$, let $A$ be an
M-matrix, let $A \le B$ entrywise, and let $b_{ij} \le 0$ for $i \neq j$. Then $B$ is an
M-matrix.

The chain of entrywise inequalities of the book between the two Jacobi matrices,
$I - D_B^{-1} B \le I - D_A^{-1} A$, holds entry by entry: off the diagonal
$a_{ij} \le b_{ij} \le 0$, and on the diagonal $0 < a_{ii} \le b_{ii}$, so the reciprocals are
in the opposite order. Theorem 1.28 then compares the spectral radii, and Theorem 1.31 is
applied twice. -/
theorem theorem_1_33 {B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsMMatrix) (hAB : A ≤ₑ B)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) : B.IsMMatrix := by
  have hdA : ∀ i, 0 < A i i := hA.diag_pos
  have hdB : ∀ i, 0 < B i i := fun i => lt_of_lt_of_le (hdA i) (hAB i i)
  refine (theorem_1_31 hdB hoff).2 (lt_of_le_of_lt (theorem_1_28
    (entrywiseNonneg_jacobiMatrix hdB hoff) ?_) ((theorem_1_31 hdA hA.offDiag_nonpos).1 hA))
  intro i j
  rw [jacobiMatrix_apply (fun i => (hdB i).ne') i j, jacobiMatrix_apply (fun i => (hdA i).ne') i j]
  by_cases h : i = j
  · subst h
    rw [inv_mul_cancel₀ (hdA i).ne', inv_mul_cancel₀ (hdB i).ne']
  · rw [ite_eq_right h, zero_sub, zero_sub, neg_le_neg_iff]
    calc (A i i)⁻¹ * A i j
        ≤ (A i i)⁻¹ * B i j := mul_le_mul_of_nonneg_left (hAB i j) (inv_nonneg.2 (hdA i).le)
      _ ≤ (B i i)⁻¹ * B i j :=
          mul_le_mul_of_nonpos_right (inv_anti₀ (hdA i) (hAB i i)) (hoff i j h)

end MMatrix

end SaadSparse.Chapter01
