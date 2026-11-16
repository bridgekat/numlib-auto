/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.LeastSquares
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section03

/-!
# Quarteroni, Sacco and Saleri, Section 3.4: Other types of factorization

This module formalizes Section 3.4 of [quarteroni2000numerical]. A matrix
$A \in \mathbb{R}^{n \times n}$ whose leading principal minors are nonzero has a unique
factorization $A = LDM^T$ with $L$, $M$ unit lower triangular and $D$ diagonal (Theorem 3.5). For
symmetric $A$ this is $A = LDL^T$, and for symmetric positive definite $A$ it gives the Cholesky
factorization $A = H^T H$ with $H$ upper triangular and positive diagonal (Theorem 3.6), computed by
the recurrence (3.45). A matrix $A \in \mathbb{R}^{m \times n}$ has a QR factorization $A = QR$ with
$Q$ orthogonal and $R$ upper trapezoidal (Definition 3.1), and its first $n$ columns and rows give
the reduced factorization $A = \tilde Q \tilde R$ of Property 3.3, which the Gram–Schmidt process
(3.49) and its modified form compute.

The proofs specialize the backbone modules `Numlib.LinearAlgebra.Matrix.LU` (the specification
`Matrix.IsLDM`), `Numlib.LinearAlgebra.Matrix.Cholesky` (the specification `Matrix.IsCholesky`, its
uniqueness and the recurrence `Matrix.cholesky`), `Numlib.FloatingPoint.LU` (the backward error of
the Cholesky recurrence), `Numlib.LinearAlgebra.Matrix.QR` and
`Numlib.LinearAlgebra.Matrix.LeastSquares` (the full and the reduced QR factorizations), and
Mathlib's Gram–Schmidt process with `Numlib.Analysis.InnerProductSpace.GramSchmidt`.

## Main definitions

* Definition 3.1, `QuarteroniSaccoSaleri.Chapter03.definition_3_1`: $A$ admits a QR factorization
  $A = QR$.
* (3.49), `QuarteroniSaccoSaleri.Chapter03.columns`: the columns $a_1, \ldots, a_n$ of $A$ as
  vectors of $\mathbb{R}^m$.

## Main results

* Theorem 3.5, `QuarteroniSaccoSaleri.Chapter03.theorem_3_5`: if the leading principal minors of $A$
  are nonzero, $A = LDM^T$ for unique $L$, $D$, $M$.
* Section 3.4.2, `QuarteroniSaccoSaleri.Chapter03.ldl_of_isSymm`: for symmetric $A$ the
  factorization is $A = LDL^T$, and $D$ is positive for positive definite $A$.
* Section 3.4.2, `QuarteroniSaccoSaleri.Chapter03.ldl_hilbert_three`: the $LDL^T$ factorization of
  the Hilbert matrix $H_3$.
* Theorem 3.6, `QuarteroniSaccoSaleri.Chapter03.theorem_3_6_iff`: the specification
  `Matrix.IsCholesky` over $\mathbb{R}$ is the factorization (3.44).
* Theorem 3.6, `QuarteroniSaccoSaleri.Chapter03.theorem_3_6`: a symmetric positive definite matrix
  has a unique Cholesky factorization $A = H^T H$.
* (3.45), `QuarteroniSaccoSaleri.Chapter03.equation_3_45`: the Cholesky recurrence computes the
  factor $H^T$.
* Section 3.4.2, `QuarteroniSaccoSaleri.Chapter03.cholesky_backward_error`: the computed Cholesky
  factor $\tilde H$ satisfies $\tilde H^T \tilde H = A + \delta A$ with $|\delta A| \le \gamma_{n+1}
  |\tilde H^T| |\tilde H|$.
* Definition 3.1, `QuarteroniSaccoSaleri.Chapter03.definition_3_1_iff`: the definition spelled out,
  and every matrix admits a QR factorization.
* Property 3.3, `QuarteroniSaccoSaleri.Chapter03.property_3_3`: a QR factorization gives the reduced
  factorization $A = \tilde Q \tilde R$.
* Property 3.3, `QuarteroniSaccoSaleri.Chapter03.property_3_3_unique`: the reduced factorization
  with positive diagonal of $\tilde R$ is unique.
* Property 3.3, `QuarteroniSaccoSaleri.Chapter03.property_3_3_cholesky`: for $A$ of full rank,
  $\tilde R$ is the Cholesky factor of $A^T A$.
* Section 3.4.3, `QuarteroniSaccoSaleri.Chapter03.property_3_3_diag_ne_zero_iff`: the diagonal of
  $\tilde R$ is nonzero if and only if $A$ has full rank.
* Property 3.3, `QuarteroniSaccoSaleri.Chapter03.property_3_3_range`: for $A$ of full rank, the
  columns of $\tilde Q$ are an orthonormal basis of the range of $A$.
* (3.49), `QuarteroniSaccoSaleri.Chapter03.equation_3_49`: the Gram–Schmidt process gives
  orthonormal vectors and the reduced factorization.
* Section 3.4.3, `QuarteroniSaccoSaleri.Chapter03.modifiedGramSchmidt_eq`: the modified Gram–Schmidt
  method gives the same vectors as the standard one.

## Conventions

* The $LDM^T$ factorization is `Matrix.IsLDM A L D M`: $L$ and $M$ are unit lower triangular (so
  $M^T$ is unit upper triangular), $D$ is diagonal, and $LDM^T = A$. The $LDL^T$ factorization is
  `Matrix.IsLDM A L D L`.
* The Cholesky factorization $A = H^T H$ of Theorem 3.6 is `Matrix.IsCholesky A H`: $H$ is upper
  triangular with positive diagonal and $H^H H = A$, which over $\mathbb{R}$ is $H^T H = A$
  (`QuarteroniSaccoSaleri.Chapter03.theorem_3_6_iff`). The recurrence (3.45) computes the lower
  factor $H^T$, as `Matrix.cholesky A`.
* "Symmetric positive definite" is Mathlib's `Matrix.PosDef` over $\mathbb{R}$, which includes the
  symmetry.
* A matrix $A \in \mathbb{R}^{m \times n}$ is `Matrix (Fin m) (Fin n) ℝ`. Its columns, as vectors of
  $\mathbb{R}^m$ with the Euclidean norm, are `QuarteroniSaccoSaleri.Chapter03.columns A j`. "$A$
  has rank $n$" (full column rank) is `LinearIndependent ℝ Aᵀ`.
* The full QR factorization of Definition 3.1 is `Matrix.IsQR A Q R`: $Q$ is orthogonal and $R$ is
  upper trapezoidal. For $n \le m$ the reduced factors $\tilde Q = Q(1{:}m, 1{:}n)$ and
  $\tilde R = R(1{:}n, 1{:}n)$ of (3.48) are `Matrix.firstColumns Q h` and `Matrix.firstRows R h`,
  where `h : n ≤ m`. A reduced factorization is a pair $\tilde Q$, $\tilde R$ with
  $A = \tilde Q \tilde R$, $\tilde Q^T \tilde Q = I$ and $\tilde R$ upper triangular.
* The Gram–Schmidt vectors $q_k$ of (3.49) are Mathlib's `gramSchmidt ℝ x k`, and the normalized
  vectors $\tilde q_k$ are `gramSchmidtNormed ℝ x k`. The reduced factors that they give are
  `Matrix.gramSchmidtQ A` and `Matrix.gramSchmidtR A`. The modified sweep is
  `InnerProductSpace.modifiedGramSchmidtSweep`.
* The book's scalar product $(x, y)$ is `inner ℝ y x`. Over the reals this equals `inner ℝ x y`.
  Indices are $0$-based.
* Rounding-error statements use the relational rounding model `m : FloatingPoint.RoundingModel ℝ`
  with unit roundoff `m.u`. The computed Cholesky factor is an admissible
  `FloatingPoint.RoundsCholesky m A H̃`: the recurrence (3.45) with every product, every running
  difference, every square root and every division rounded once.

## Deviations from the source

* **Theorem 3.5** (reading). The source asks that "all the principal minors" of $A$ are nonzero. Its
  proof uses the leading principal minors of orders $1, \ldots, n$, and this is the hypothesis
  stated. See `QuarteroniSaccoSaleri.Chapter03.theorem_3_5`.
* **Property 3.3, uniqueness** (reading). The source calls the reduced factorization unique. It is
  unique only up to a diagonal matrix of signs; the statement normalizes the diagonal of $\tilde R$
  to be positive, as the last clause of the property presupposes. See
  `QuarteroniSaccoSaleri.Chapter03.property_3_3_unique`.

## Not formalized

* **Wilkinson's bound** $\|\delta A\|_2 \le 8n(n + 1)u\|A\|_2$ for the computed Cholesky factor,
  which the book quotes. The module states the componentwise bound of [higham2002accuracy], Theorem
  10.3, instead.
* **Example 3.4**, a numerical comparison of the two Gram–Schmidt variants.
* **Programs 7–8.**
* **The operation counts**, which the book gives in prose.
-/

open Finset Matrix InnerProductSpace WithLp

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ}

/-! ### Section 3.4.1: the $LDM^T$ factorization, Theorem 3.5 -/

/-- **Theorem 3.5** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$, and assume
that the leading principal minors of $A$ of orders $1, \ldots, n$ are nonzero. Then there exist
a unique diagonal matrix $D$, a unique unit lower triangular matrix $L$ and a unique unit upper
triangular matrix $M^T$ such that
$$A = L D M^T.$$

**Reading.** The source asks that "all the principal minors" of $A$ are nonzero. Its proof uses
only the leading principal minors, of orders $1, \ldots, n$; the minor of order $n$ makes $D$
invertible. The theorem states this hypothesis.

The factorization is `Matrix.IsLDM A L D M`, with $M$ unit lower triangular. The proof
specializes `Matrix.existsUnique_isLDM`. -/
theorem theorem_3_5 {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ k, (A.leadingPrincipalSubmatrix k).det ≠ 0) :
    ∃! LDM : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ,
      IsLDM A LDM.1 LDM.2.1 LDM.2.2 :=
  existsUnique_isLDM <| isUnit_strictLeadingPrincipalSubmatrix_of_forall_isUnit fun k =>
    (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hA k))

/-- **Section 3.4.2** of [quarteroni2000numerical], the $LDL^T$ factorization. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric with nonzero leading principal minors of orders
$1, \ldots, n$. Then every factorization $A = LDM^T$ of Theorem 3.5 has $M = L$, and $A$ has a
factorization $A = LDL^T$. If $A$ is also positive definite, then every factorization
$A = LDL^T$ has $d_{ii} > 0$ for all $i$.

The proof uses `Matrix.IsLDM.eq_of_isSymm` and `Matrix.IsLDM.diag_pos_of_posDef`. -/
theorem ldl_of_isSymm {A : Matrix (Fin n) (Fin n) ℝ} (hs : A.IsSymm)
    (hA : ∀ k, (A.leadingPrincipalSubmatrix k).det ≠ 0) :
    (∀ L D M, IsLDM A L D M → M = L) ∧ (∃ L D, IsLDM A L D L) ∧
      (A.PosDef → ∀ L D, IsLDM A L D L → ∀ i, 0 < D i i) := by
  have hA' : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k) :=
    isUnit_strictLeadingPrincipalSubmatrix_of_forall_isUnit fun k =>
      (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hA k))
  refine ⟨fun L D M h => h.eq_of_isSymm hs hA', ?_, fun hpd L D h i => h.diag_pos_of_posDef hpd i⟩
  obtain ⟨⟨L, D, M⟩, h, -⟩ := existsUnique_isLDM hA'
  have h' : IsLDM A L D M := h
  exact ⟨L, D, h'.eq_of_isSymm hs hA' ▸ h'⟩

/-- **Section 3.4.2** of [quarteroni2000numerical], the $LDL^T$ factorization of $H_3$. The Hilbert
matrix of order $3$ has the factorization
$$H_3 = \begin{bmatrix} 1 & 0 & 0 \\ 1/2 & 1 & 0 \\ 1/3 & 1 & 1 \end{bmatrix} \begin{bmatrix} 1
  & 0 & 0 \\ 0 & 1/12 & 0 \\ 0 & 0 & 1/180 \end{bmatrix} \begin{bmatrix} 1 & 1/2 & 1/3 \\ 0 & 1
  & 1 \\ 0 & 0 & 1 \end{bmatrix}.$$
-/
theorem ldl_hilbert_three :
    hilbert ℝ 3 = !![1, 0, 0; 1/2, 1, 0; 1/3, 1, 1] * diagonal ![1, 1/12, 1/180] *
      !![1, 1/2, 1/3; 0, 1, 1; 0, 0, 1] := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [hilbert] <;> norm_num

/-! ### Section 3.4.2: the Cholesky factorization, Theorem 3.6 -/

section Cholesky

variable {A H : Matrix (Fin n) (Fin n) ℝ}

/-- **Theorem 3.6** of [quarteroni2000numerical], the form of the factorization (3.44). Let
$A, H \in \mathbb{R}^{n \times n}$. Then `Matrix.IsCholesky A H` holds if and only if $H$ is
upper triangular, $h_{ii} > 0$ for all $i$, and $A = H^T H$. -/
theorem theorem_3_6_iff :
    IsCholesky A H ↔ H.IsUpperTriangular ∧ (∀ i, 0 < H i i) ∧ Hᵀ * H = A := by
  constructor
  · intro h
    refine ⟨h.isUpperTriangular, h.diag_pos, ?_⟩
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact h.conjTranspose_mul_self
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rw [conjTranspose_eq_transpose_of_trivial]; exact h3⟩

/-- **Theorem 3.6** of [quarteroni2000numerical], equation (3.44). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric and positive definite. Then there exists a unique
upper triangular matrix $H$ with positive diagonal entries such that
$$A = H^T H.$$
This is the **Cholesky factorization** of $A$.

"Symmetric positive definite" is `Matrix.PosDef`. The proof specializes
`Matrix.existsUnique_isCholesky`. -/
theorem theorem_3_6 (hA : A.PosDef) :
    ∃! H : Matrix (Fin n) (Fin n) ℝ, H.IsUpperTriangular ∧ (∀ i, 0 < H i i) ∧ Hᵀ * H = A := by
  simpa only [theorem_3_6_iff] using existsUnique_isCholesky hA

/-- **Equation (3.45)** of [quarteroni2000numerical] (the Cholesky recurrence). Let
$A \in \mathbb{R}^{n \times n}$ with $n \ge 1$, and let $h_{ij}$ be the entries of the lower
triangular matrix `Matrix.cholesky A`. Then $h_{00} = \sqrt{a_{00}}$,
$$h_{ij} = \frac{1}{h_{jj}} \Big( a_{ij} - \sum_{k < j} h_{ik} h_{jk} \Big) \quad (j < i),
  \qquad h_{ii} = \Big( a_{ii} - \sum_{k < i} h_{ik}^2 \Big)^{1/2},$$
and $h_{ij} = 0$ for $i < j$. If $A$ is symmetric positive definite, then the transpose of this
matrix is the Cholesky factor $H$ of Theorem 3.6.

The indices are $0$-based; the book starts at $h_{11} = \sqrt{a_{11}}$. The function
`Matrix.cholesky` is total: Lean's square root is $0$ at a negative argument, and a division by
zero gives $0$. The proof uses `Matrix.cholesky_apply_of_lt`, `Matrix.cholesky_apply_self` and
`Matrix.isCholesky_cholesky`. -/
theorem equation_3_45 [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) :
    cholesky A 0 0 = √(A 0 0) ∧
    (∀ i j, j < i →
      cholesky A i j = (A i j - ∑ k with k < j, cholesky A i k * cholesky A j k) / cholesky A j j) ∧
    (∀ i, cholesky A i i = √(A i i - ∑ k with k < i, cholesky A i k ^ 2)) ∧
    (∀ i j, i < j → cholesky A i j = 0) ∧
    (A.PosDef → IsCholesky A (cholesky A)ᵀ) := by
  have hself : ∀ i, cholesky A i i = √(A i i - ∑ k with k < i, cholesky A i k ^ 2) := by
    intro i
    rw [cholesky_apply_self]
    simp [Real.norm_eq_abs, sq_abs]
  refine ⟨?_, fun i j hij => ?_, hself, fun i j hij => cholesky_apply_of_gt A hij, fun hA => ?_⟩
  · rw [hself, Finset.sum_eq_zero fun k hk =>
      absurd (mem_filter.1 hk).2 (not_lt.2 (Fin.zero_le k)), sub_zero]
  · rw [cholesky_apply_of_lt A hij]
    simp
  · rw [← conjTranspose_eq_transpose_of_trivial]
    exact isCholesky_cholesky hA

open FloatingPoint in
/-- **Section 3.4.2** of [quarteroni2000numerical], stability of the Cholesky recurrence. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric, let $u$ be the unit roundoff of a rounding model
with $(n + 1)u < 1$, and let $\tilde H$ be the Cholesky factor that the recurrence (3.45)
computes in floating-point arithmetic, with nonzero computed diagonal entries. Then there is a
matrix $\delta A$ with
$$\tilde H^T \tilde H = A + \delta A, \qquad |\delta A| \le \frac{(n + 1)u}{1 - (n + 1)u}
  |\tilde H^T| |\tilde H|,$$
where the absolute values and the inequality are entrywise.

The book quotes Wilkinson's normwise bound $\|\delta A\|_2 \le 8n(n + 1)u\|A\|_2$. This bound is
not formalized; the theorem states instead the componentwise bound of Theorem 10.3 of
[higham2002accuracy].

The computed factor is an admissible `FloatingPoint.RoundsCholesky m A Ht`. The proof uses
`FloatingPoint.exists_roundsCholesky_eq_add`. -/
theorem cholesky_backward_error {m : RoundingModel ℝ} (hn : ((n + 1 : ℕ) : ℝ) * m.u < 1)
    (hA : A.IsSymm) {Ht : Matrix (Fin n) (Fin n) ℝ} (h : RoundsCholesky m A Ht)
    (hd : ∀ i, Ht i i ≠ 0) :
    ∃ δA : Matrix (Fin n) (Fin n) ℝ,
      δA.abs ≤ₑ ((n + 1 : ℕ) * m.u / (1 - (n + 1 : ℕ) * m.u)) • (Htᵀ.abs * Ht.abs) ∧
        Htᵀ * Ht = A + δA := by
  have hu : m.u < 1 := by
    have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    nlinarith [m.u_nonneg]
  obtain ⟨δA, hδA, hLU⟩ := exists_roundsCholesky_eq_add hu (by rwa [Fintype.card_fin]) hA h hd
  refine ⟨δA, ?_, hLU⟩
  rwa [Fintype.card_fin, gamma_def] at hδA

end Cholesky

/-! ### Section 3.4.3: the QR factorization, Definition 3.1 and Property 3.3 -/

section QR

variable {m : ℕ}

/-- **Definition 3.1** of [quarteroni2000numerical], equation (3.46). A matrix
$A \in \mathbb{R}^{m \times n}$ **admits a QR factorization** if there exist an orthogonal
matrix $Q \in \mathbb{R}^{m \times m}$ and an upper trapezoidal matrix
$R \in \mathbb{R}^{m \times n}$, with null rows from the $(n + 1)$-th on, such that
$$A = QR.$$

The definition is `Matrix.IsQR A Q R` for some $Q$ and $R$. It is spelled out in
`QuarteroniSaccoSaleri.Chapter03.definition_3_1_iff`. The book assumes $m \ge n$; the Lean
definition does not need it. -/
def definition_3_1 (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∃ Q R, IsQR A Q R

/-- **Definition 3.1** of [quarteroni2000numerical], spelled out. Let
$A \in \mathbb{R}^{m \times n}$. Then $A$ admits a QR factorization if and only if there exist
an orthogonal $Q \in \mathbb{R}^{m \times m}$ and $R \in \mathbb{R}^{m \times n}$ with
$r_{ij} = 0$ for $j < i$ and for $i \ge n$, such that $A = QR$. Moreover, every $A$ admits a QR
factorization.

Existence follows from Householder triangularization, by `Matrix.exists_isQR` and
`Matrix.exists_unitary_mul_upperTriangular`. -/
theorem definition_3_1_iff (A : Matrix (Fin m) (Fin n) ℝ) :
    (definition_3_1 A ↔ ∃ Q ∈ orthogonalGroup (Fin m) ℝ, ∃ R : Matrix (Fin m) (Fin n) ℝ,
      (∀ (i : Fin m) (j : Fin n), (j : ℕ) < i → R i j = 0) ∧
        (∀ i : Fin m, n ≤ i → ∀ j, R i j = 0) ∧ A = Q * R) ∧
      definition_3_1 A := by
  refine ⟨⟨?_, ?_⟩, exists_isQR A⟩
  · rintro ⟨Q, R, h⟩
    exact ⟨Q, h.mem_unitaryGroup, R, h.apply_eq_zero, fun i hi j => h.apply_eq_zero_of_le hi j,
      h.mul_eq.symm⟩
  · rintro ⟨Q, hQ, R, hR, -, hA⟩
    exact ⟨Q, R, hQ, hR, hA.symm⟩

variable {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
variable {R : Matrix (Fin m) (Fin n) ℝ}

/-- **Property 3.3** of [quarteroni2000numerical], existence, equations (3.47)–(3.48). Let
$A \in \mathbb{R}^{m \times n}$ with $n \le m$, and let $A = QR$ be a QR factorization. Let
$\tilde Q = Q(1{:}m, 1{:}n)$ and $\tilde R = R(1{:}n, 1{:}n)$. Then
$$A = \tilde Q \tilde R, \qquad \tilde Q^T \tilde Q = I_n,$$
and $\tilde R$ is upper triangular.

The book assumes that $A$ has rank $n$; this part does not need it. The matrices $\tilde Q$ and
$\tilde R$ are `Matrix.firstColumns Q hnm` and `Matrix.firstRows R hnm`. The proof uses
`Matrix.IsQR.isThinQR`. -/
theorem property_3_3 (h : IsQR A Q R) (hnm : n ≤ m) :
    A = firstColumns Q hnm * firstRows R hnm ∧
      (firstColumns Q hnm)ᵀ * firstColumns Q hnm = 1 ∧ (firstRows R hnm).IsUpperTriangular := by
  obtain ⟨h1, h2, h3⟩ := h.isThinQR hnm
  refine ⟨h1.symm, ?_, h3⟩
  rwa [conjTranspose_eq_transpose_of_trivial] at h2

/-- **Property 3.3** of [quarteroni2000numerical], uniqueness. Let $A \in \mathbb{R}^{m \times n}$,
and let $A = Q_1 R_1 = Q_2 R_2$ with $Q_1, Q_2 \in \mathbb{R}^{m \times n}$,
$Q_1^T Q_1 = Q_2^T Q_2 = I_n$, and $R_1, R_2 \in \mathbb{R}^{n \times n}$ upper triangular with
positive diagonal entries. Then $Q_1 = Q_2$ and $R_1 = R_2$.

**Reading.** The source says that the reduced factorization $A = \tilde Q \tilde R$ is unique.
Without a sign condition it is unique only up to a diagonal matrix $D$ of signs, since
$(\tilde Q D)(D \tilde R)$ is another one. The source leaves the normalization implicit: its
last clause says that $\tilde R$ coincides with the Cholesky factor of $A^T A$, which has
positive diagonal. The theorem asks for a positive diagonal.

The proof specializes `Matrix.IsThinQR.unique`. -/
theorem property_3_3_unique {Q₁ Q₂ : Matrix (Fin m) (Fin n) ℝ} {R₁ R₂ : Matrix (Fin n) (Fin n) ℝ}
    (h₁ : A = Q₁ * R₁) (h₂ : A = Q₂ * R₂) (hQ₁ : Q₁ᵀ * Q₁ = 1) (hQ₂ : Q₂ᵀ * Q₂ = 1)
    (hR₁ : R₁.IsUpperTriangular) (hR₂ : R₂.IsUpperTriangular) (hd₁ : ∀ j, 0 < R₁ j j)
    (hd₂ : ∀ j, 0 < R₂ j j) : Q₁ = Q₂ ∧ R₁ = R₂ :=
  IsThinQR.unique ⟨h₁.symm, by rwa [conjTranspose_eq_transpose_of_trivial], hR₁⟩
    ⟨h₂.symm, by rwa [conjTranspose_eq_transpose_of_trivial], hR₂⟩ hd₁ hd₂

/-- **Property 3.3** of [quarteroni2000numerical], the Cholesky factor. Let
$A \in \mathbb{R}^{m \times n}$ have rank $n$, and let $A = \tilde Q \tilde R$ with
$\tilde Q^T \tilde Q = I_n$ and $\tilde R$ upper triangular with positive diagonal entries. Then
$A^T A$ is symmetric positive definite, and $\tilde R$ is its Cholesky factor:
$$A^T A = \tilde R^T \tilde Q^T \tilde Q \tilde R = \tilde R^T \tilde R.$$
Hence also `Matrix.cholesky (Aᵀ * A)` equals $\tilde R^T$.

The proof uses `Matrix.posDef_conjTranspose_mul_self_of_linearIndependent` and
`Matrix.cholesky_conjTranspose_mul_self_of_qr`. -/
theorem property_3_3_cholesky (hA : LinearIndependent ℝ Aᵀ) {Qt : Matrix (Fin m) (Fin n) ℝ}
    {Rt : Matrix (Fin n) (Fin n) ℝ} (h : A = Qt * Rt) (hQ : Qtᵀ * Qt = 1)
    (hR : Rt.IsUpperTriangular) (hd : ∀ j, 0 < Rt j j) :
    (Aᵀ * A).PosDef ∧ IsCholesky (Aᵀ * A) Rt ∧ cholesky (Aᵀ * A) = Rtᵀ := by
  have hQ' : Qtᴴ * Qt = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  refine ⟨?_, ?_, ?_⟩
  · rw [← conjTranspose_eq_transpose_of_trivial]
    exact posDef_conjTranspose_mul_self_of_linearIndependent hA
  · rw [← conjTranspose_eq_transpose_of_trivial]
    exact isCholesky_conjTranspose_mul_self_of_qr h hQ' hR hd
  · rw [← conjTranspose_eq_transpose_of_trivial, ← conjTranspose_eq_transpose_of_trivial]
    exact cholesky_conjTranspose_mul_self_of_qr h hQ' hR hd

/-- **Section 3.4.3** of [quarteroni2000numerical], the remark after (3.49) on the diagonal of
$\tilde R$. Let $A \in \mathbb{R}^{m \times n}$ with $n \le m$, let $A = QR$ be a QR
factorization, and let $\tilde R = R(1{:}n, 1{:}n)$. Then all diagonal entries of $\tilde R$ are
nonzero if and only if $A$ has rank $n$.

The book states only that the diagonal entries are nonzero only if $A$ has full rank; the
converse is also proved. One direction is
`Matrix.IsQR.firstRows_diag_ne_zero_of_linearIndependent`. For the other, $\tilde R$ is then
nonsingular, so $A = \tilde Q \tilde R$ is injective. -/
theorem property_3_3_diag_ne_zero_iff (h : IsQR A Q R) (hnm : n ≤ m) :
    (∀ j, firstRows R hnm j j ≠ 0) ↔ LinearIndependent ℝ Aᵀ := by
  refine ⟨fun hd => ?_, h.firstRows_diag_ne_zero_of_linearIndependent hnm⟩
  have hR : IsUnit (firstRows R hnm) :=
    (h.isUpperTriangular_firstRows hnm).isUnit_iff.2 hd
  have hQ : Function.Injective (firstColumns Q hnm).mulVec := by
    intro x y hxy
    have := congrArg ((firstColumns Q hnm)ᵀ *ᵥ ·) hxy
    simpa [mulVec_mulVec, (property_3_3 h hnm).2.1] using this
  rw [show Aᵀ = A.col from rfl, ← mulVec_injective_iff, ← h.firstColumns_mul_firstRows hnm]
  intro x y hxy
  simp only [← mulVec_mulVec] at hxy
  exact mulVec_injective_iff_isUnit.2 hR (hQ hxy)

/-- **Property 3.3** of [quarteroni2000numerical], the range. Let $A \in \mathbb{R}^{m \times n}$
have rank $n$ with $n \le m$, and let $A = QR$ be a QR factorization. Then the columns of
$\tilde Q = Q(1{:}m, 1{:}n)$ are an orthonormal basis of the range of $A$:
$\tilde Q^T \tilde Q = I_n$, and the columns of $\tilde Q$ span the same subspace as the columns
of $A$.

The proof uses `Matrix.IsQR.span_firstColumns_eq`. -/
theorem property_3_3_range (h : IsQR A Q R) (hnm : n ≤ m) (hA : LinearIndependent ℝ Aᵀ) :
    (firstColumns Q hnm)ᵀ * firstColumns Q hnm = 1 ∧
      Submodule.span ℝ (Set.range (firstColumns Q hnm)ᵀ) = Submodule.span ℝ (Set.range Aᵀ) :=
  ⟨(property_3_3 h hnm).2.1, h.span_firstColumns_eq hnm hA⟩

end QR

/-! ### Section 3.4.3: Gram–Schmidt orthogonalization, (3.49), and its modified form -/

section GramSchmidt

variable {m : ℕ}

/-- The **columns** $a_1, \ldots, a_n$ of $A \in \mathbb{R}^{m \times n}$, as vectors of
$\mathbb{R}^m$ with the Euclidean norm. -/
noncomputable def columns (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) : EuclideanSpace ℝ (Fin m) :=
  toLp 2 (Aᵀ j)

/-- **Equation (3.49)** of [quarteroni2000numerical] (the Gram–Schmidt orthogonalization). Let
$x_0, \ldots, x_{n-1} \in \mathbb{R}^m$ be linearly independent, with $n \ge 1$. The
Gram–Schmidt vectors $q_k$ satisfy $q_0 = x_0$ and
$$q_k = x_k - \sum_{i < k} \frac{(q_i, x_k)}{(q_i, q_i)} q_i.$$
They are nonzero and mutually orthogonal. The normalized vectors $\tilde q_k = q_k / \|q_k\|_2$
are orthonormal, and $q_k = x_k - \sum_{j < k} (\tilde q_j, x_k) \tilde q_j$. Moreover, let
$A \in \mathbb{R}^{m \times n}$ have rank $n$, and let $\tilde Q$ be the matrix whose columns
are the normalized Gram–Schmidt vectors of the columns of $A$, and $\tilde R = \tilde Q^T A$.
Then
$$A = \tilde Q \tilde R, \qquad \tilde Q^T \tilde Q = I_n,$$
and $\tilde R$ is upper triangular with positive diagonal entries.

By `QuarteroniSaccoSaleri.Chapter03.property_3_3_unique`, $\tilde Q \tilde R$ is therefore the
reduced factorization with positive diagonal. The vectors $q_k$ and $\tilde q_k$ are Mathlib's
`gramSchmidt ℝ x k` and `gramSchmidtNormed ℝ x k`, and $\tilde Q$, $\tilde R$ are
`Matrix.gramSchmidtQ A` and `Matrix.gramSchmidtR A`. The indices are $0$-based. The proof uses
`Matrix.isThinQR_gramSchmidtQ` and Mathlib's `gramSchmidt_def''`, `gramSchmidt_orthogonal` and
`gramSchmidtNormed_orthonormal`. -/
theorem equation_3_49 [NeZero n] (x : Fin n → EuclideanSpace ℝ (Fin m))
    (hx : LinearIndependent ℝ x) (A : Matrix (Fin m) (Fin n) ℝ) (hA : LinearIndependent ℝ Aᵀ) :
    gramSchmidt ℝ x 0 = x 0 ∧
    (∀ k, gramSchmidt ℝ x k = x k - ∑ i ∈ Iio k,
      (inner ℝ (gramSchmidt ℝ x i) (x k) / inner ℝ (gramSchmidt ℝ x i) (gramSchmidt ℝ x i)) •
        gramSchmidt ℝ x i) ∧
    (∀ i j, i ≠ j → inner ℝ (gramSchmidt ℝ x i) (gramSchmidt ℝ x j) = 0) ∧
    (∀ k, gramSchmidt ℝ x k ≠ 0) ∧
    (∀ k, gramSchmidtNormed ℝ x k = ‖gramSchmidt ℝ x k‖⁻¹ • gramSchmidt ℝ x k) ∧
    Orthonormal ℝ (gramSchmidtNormed ℝ x) ∧
    (∀ k, gramSchmidt ℝ x k = x k - ∑ j ∈ Iio k,
      inner ℝ (gramSchmidtNormed ℝ x j) (x k) • gramSchmidtNormed ℝ x j) ∧
    (∀ j, (gramSchmidtQ A).col j = ofLp (gramSchmidtNormed ℝ (columns A) j)) ∧
    gramSchmidtR A = (gramSchmidtQ A)ᵀ * A ∧
    A = gramSchmidtQ A * gramSchmidtR A ∧ (gramSchmidtQ A)ᵀ * gramSchmidtQ A = 1 ∧
      (gramSchmidtR A).IsUpperTriangular ∧ ∀ j, 0 < gramSchmidtR A j j := by
  have hdef : ∀ k, gramSchmidt ℝ x k = x k - ∑ i ∈ Iio k,
      (inner ℝ (gramSchmidt ℝ x i) (x k) / inner ℝ (gramSchmidt ℝ x i) (gramSchmidt ℝ x i)) •
        gramSchmidt ℝ x i := by
    intro k
    have := gramSchmidt_def'' ℝ x k
    simp only [RCLike.ofReal_real_eq_id, id, ← real_inner_self_eq_norm_sq] at this
    exact eq_sub_iff_add_eq.2 this.symm
  have hne : ∀ k, gramSchmidt ℝ x k ≠ 0 := fun k => gramSchmidt_ne_zero k hx
  have hqr : A = gramSchmidtQ A * gramSchmidtR A ∧ (gramSchmidtQ A)ᵀ * gramSchmidtQ A = 1 ∧
      (gramSchmidtR A).IsUpperTriangular ∧ ∀ j, 0 < gramSchmidtR A j j := by
    have h := isThinQR_gramSchmidtQ hA
    exact ⟨h.mul_eq.symm, by simpa using h.conjTranspose_mul_self, h.isUpperTriangular,
      gramSchmidtR_apply_self_pos hA⟩
  refine ⟨?_, hdef, fun i j hij => gramSchmidt_orthogonal ℝ x hij, hne, fun k => ?_,
    gramSchmidtNormed_orthonormal hx, fun k => ?_, fun j => rfl, ?_, hqr⟩
  · rw [hdef, Finset.sum_eq_zero fun i hi =>
      absurd (Finset.mem_Iio.1 hi) (not_lt.2 (Fin.zero_le i)), sub_zero]
  · rw [gramSchmidtNormed]
    simp
  · rw [hdef k]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gramSchmidtNormed, inner_smul_left, smul_smul, real_inner_self_eq_norm_sq]
    simp only [RCLike.ofReal_real_eq_id, id, conj_trivial]
    congr 1
    field_simp [hne i]
  · ext i j
    rw [gramSchmidtR, of_apply, Matrix.mul_apply, EuclideanSpace.inner_eq_star_dotProduct,
        dotProduct]
    exact Finset.sum_congr rfl fun r _ => by simp [gramSchmidtQ, mul_comm]

/-- **Section 3.4.3** of [quarteroni2000numerical], the modified Gram–Schmidt method. Let
$x_0, x_1, \ldots \in \mathbb{R}^m$, and let $\tilde q_j$ be their normalized Gram–Schmidt
vectors. At step $k$, the modified method subtracts the projections along
$\tilde q_0, \ldots, \tilde q_{k-1}$ one after the other, each computed on the current vector:
$$a^{(0)} = x_k, \qquad a^{(j+1)} = a^{(j)} - (\tilde q_j, a^{(j)}) \tilde q_j \quad (j < k).$$
Then the result $a^{(k)}$ equals the Gram–Schmidt vector $q_k$ of the standard process.

The reason is that, by the orthogonality of $\tilde q_0, \ldots, \tilde q_{k-1}$, $a^{(k)} =
x_k - \sum_{j < k} (\tilde q_j, x_k) \tilde q_j$, which is (3.49). The vectors are a sequence
`x : ℕ → EuclideanSpace ℝ (Fin m)`; a finite family is padded arbitrarily, because the statement
at step $k$ reads only $x_0, \ldots, x_k$. No linear independence is needed. The sweep is
`InnerProductSpace.modifiedGramSchmidtSweep`. The proof uses
`InnerProductSpace.modifiedGramSchmidt_eq_gramSchmidt` and
`InnerProductSpace.modifiedGramSchmidtSweep_eq_sub_sum`. -/
theorem modifiedGramSchmidt_eq (x : ℕ → EuclideanSpace ℝ (Fin m)) (k : ℕ) :
    modifiedGramSchmidtSweep ℝ (gramSchmidtNormed ℝ x) (x k) k = gramSchmidt ℝ x k :=
  modifiedGramSchmidt_eq_gramSchmidt ℝ x k

end GramSchmidt

end QuarteroniSaccoSaleri.Chapter03
