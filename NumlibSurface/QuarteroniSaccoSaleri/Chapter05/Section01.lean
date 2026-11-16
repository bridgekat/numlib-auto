/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.Perturbation
import Numlib.LinearAlgebra.Matrix.DiagDominant
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Section11

/-!
# Quarteroni, Sacco and Saleri, Section 5.1: Geometrical Location of the Eigenvalues

This module formalizes Section 5.1 of [quarteroni2000numerical], which locates the eigenvalues of
$A \in \mathbb{C}^{n \times n}$ in the complex plane. Every eigenvalue lies in the disc of radius
$\|A\|$ about the origin for a consistent matrix norm (5.1). Hirsch's theorem (Theorem 5.1) bounds
the real and imaginary parts of the eigenvalues by the extreme eigenvalues of the Hermitian matrices
$H = (A + A^H)/2$ and $S = (A - A^H)/(2i)$. Gershgorin's theorems use the row circles $R_i = \{z :
|z - a_{ii}| \le \sum_{j \neq i} |a_{ij}|\}$ and the column circles $C_j = \{z : |z - a_{jj}| \le
\sum_{i \neq j} |a_{ij}|\}$: the spectrum lies in the union of the row circles (Theorem 5.2), in the
union of the column circles (5.6), and in the intersection of the two unions (Property 5.1). A union
of $m$ row circles that is disjoint from the other row circles contains exactly $m$ eigenvalues
(Property 5.2). For an irreducible matrix (Definition 5.1, Property 5.3), an eigenvalue on the
boundary of the union of the row circles lies on the boundary of every row circle (Property 5.4).

The proofs specialize the backbone modules `Numlib.Eigen.Perturbation` (Hirsch's bounds, the
Gershgorin circles and the counting theorem), `Numlib.LinearAlgebra.Matrix.HermitianPart` (the
Hermitian and skew-Hermitian parts), `Numlib.LinearAlgebra.Sparse.Pattern` (irreducibility as strong
connectivity of the adjacency quiver) and `Numlib.LinearAlgebra.Matrix.DiagDominant` (the third
Gershgorin theorem), and Theorem 1.4 of Chapter 1 for (5.1).

## Main definitions

* Definition 5.1, `QuarteroniSaccoSaleri.Chapter05.definition_5_1`: a matrix is reducible if a
  symmetric permutation of it is block upper triangular with two square diagonal blocks.

## Main results

* Equation (5.1), `QuarteroniSaccoSaleri.Chapter05.equation_5_1`: $|\lambda| \le \|A\|$ for every
  eigenvalue $\lambda$ and every consistent matrix norm.
* Theorem 5.1, `QuarteroniSaccoSaleri.Chapter05.theorem_5_1_re`: $\lambda_{\min}(H) \le
  \operatorname{Re} \lambda \le \lambda_{\max}(H)$.
* Theorem 5.1, `QuarteroniSaccoSaleri.Chapter05.theorem_5_1_im`: $\lambda_{\min}(S) \le
  \operatorname{Im} \lambda \le \lambda_{\max}(S)$.
* Theorem 5.2, `QuarteroniSaccoSaleri.Chapter05.theorem_5_2`: the spectrum lies in the union of the
  row circles.
* Equation (5.6), `QuarteroniSaccoSaleri.Chapter05.equation_5_6`: the spectrum lies in the union of
  the column circles.
* Property 5.1, `QuarteroniSaccoSaleri.Chapter05.property_5_1`: the spectrum lies in the
  intersection of the two unions.
* Property 5.2, `QuarteroniSaccoSaleri.Chapter05.property_5_2`: a union of $m$ row circles that is
  disjoint from the union of the others contains exactly $m$ eigenvalues.
* Definition 5.1, `QuarteroniSaccoSaleri.Chapter05.definition_5_1_iff`: for $n \ge 2$, reducibility
  is the negation of the backbone's pattern irreducibility.
* Property 5.3, `QuarteroniSaccoSaleri.Chapter05.property_5_3`: for $n \ge 2$, a real matrix is
  irreducible if and only if its oriented graph is strongly connected.
* Property 5.4, `QuarteroniSaccoSaleri.Chapter05.property_5_4`: for an irreducible matrix, an
  eigenvalue on the boundary of the union of the row circles lies on the boundary of every row
  circle.

## Conventions

* The book works in $\mathbb{C}^{n \times n}$, which is `Matrix (Fin n) (Fin n) ℂ`. The spectrum
  $\sigma(A)$ is `spectrum ℂ A`.
* The row circle $R_i$ is `Metric.closedBall (A i i) (∑ j ∈ univ.erase i, ‖A i j‖)`, and the column
  circle $C_j$ is `Metric.closedBall (A j j) (∑ i ∈ univ.erase j, ‖A i j‖)`. They are written out in
  every statement, so that each statement is the backbone's statement word for word.
* The Hermitian part $H = (A + A^H)/2$ is `Matrix.hermitianPart A`, and the matrix
  $S = (A - A^H)/(2i)$ of Theorem 5.1 is `Matrix.skewHermitianPart A`. The numbers $\lambda_{\min}$
  and $\lambda_{\max}$ are the infimum and the supremum of Mathlib's eigenvalue function
  `Matrix.IsHermitian.eigenvalues`.
* "Exactly $m$ eigenvalues, each counted with its algebraic multiplicity, in $S$" is
  `Polynomial.countRootsIn S A.charpoly = m`.
* A matrix is irreducible if it is not reducible, `¬ definition_5_1 A`.

## Implementation notes

* Definition 5.1 depends only on the zero pattern, so it is stated for any entry type with a zero.
  The book's $P A P^T$ is `A.submatrix σ σ` for the permutation $\sigma$, and the index set of the
  leading block $B_{11}$ is a proper nonempty `Finset`.

## Deviations from the source

* **Definition 5.1, Properties 5.3 and 5.4** (reading). Definition 5.1 and the backbone's
  `Matrix.IsPatternIrreducible` differ for $n = 1$: the $1 \times 1$ zero matrix is
  pattern-reducible (it has no path of positive length) but not reducible in the sense of the book
  (it has no proper nonempty block). The three results are stated for $n \ge 2$. See
  `QuarteroniSaccoSaleri.Chapter05.definition_5_1_iff`.

## Not formalized

* **Example 5.1.** It is a numerical table.
* **Remark 5.1.** It is prose.
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter05

variable {n : ℕ}

/-! ### Equation (5.1) and Theorem 5.1 -/

/-- **Equation (5.1)** of [quarteroni2000numerical]. Let $A \in \mathbb{C}^{n \times n}$, let $p$ be
a norm on $\mathbb{C}^n$, and let $N$ be a seminorm on $\mathbb{C}^{n \times n}$ that is
consistent with $p$, that is, $p(Bx) \le N(B) \, p(x)$ for all $B$ and $x$. Then every
eigenvalue $\lambda \in \sigma(A)$ satisfies
$$|\lambda| \le N(A).$$
So all the eigenvalues of $A$ lie in the disc of radius $N(A)$ about the origin.

The vector norm $p$ is a seminorm with $p(x) = 0 \Rightarrow x = 0$, and consistency is
Definition 1.20, `Matrix.IsConsistent N p p`. The result is Theorem 1.4, $\rho(A) \le \|A\|$,
read at one eigenvalue. -/
theorem equation_5_1 {N : Seminorm ℂ (Matrix (Fin n) (Fin n) ℂ)} {p : Seminorm ℂ (Fin n → ℂ)}
    (hp : ∀ x, p x = 0 → x = 0) (hN : IsConsistent N p p) (A : Matrix (Fin n) (Fin n) ℂ) :
    ∀ μ ∈ spectrum ℂ A, ‖μ‖ ≤ N A := by
  intro μ hμ
  have h : (‖μ‖₊ : ENNReal) ≤ ENNReal.ofReal (N A) := by
    refine le_trans ?_ (Chapter01.theorem_1_4 hp hN A)
    rw [spectralRadius_eq_of_unital]
    exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ A) => (‖k‖₊ : ENNReal)) μ hμ
  rwa [← enorm_eq_nnnorm, ← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (apply_nonneg N A)] at h

/-- **Theorem 5.1** of [quarteroni2000numerical] (Hirsch), real part, (5.2). Let
$A \in \mathbb{C}^{n \times n}$, and let $H = (A + A^H)/2$ be its Hermitian part. Then every
$\lambda \in \sigma(A)$ satisfies
$$\lambda_{\min}(H) \le \operatorname{Re} \lambda \le \lambda_{\max}(H).$$

The proof specializes the backbone's `Matrix.hirsch_re`, which is Bendixson's theorem read
through `Matrix.toEuclideanLin`. -/
theorem theorem_5_1_re (A : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    (⨅ i, (hermitianPart_isHermitian A).eigenvalues i) ≤ μ.re ∧
      μ.re ≤ ⨆ i, (hermitianPart_isHermitian A).eigenvalues i :=
  hirsch_re A hμ

/-- **Theorem 5.1** of [quarteroni2000numerical] (Hirsch), imaginary part, (5.2). Let
$A \in \mathbb{C}^{n \times n}$, and let $S = (A - A^H)/(2i)$, so that $iS$ is the
skew-Hermitian part of $A$ and $S$ is Hermitian. Then every $\lambda \in \sigma(A)$ satisfies
$$\lambda_{\min}(S) \le \operatorname{Im} \lambda \le \lambda_{\max}(S).$$

The proof specializes the backbone's `Matrix.hirsch_im`, which applies the real part to $-iA$. -/
theorem theorem_5_1_im (A : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    (⨅ i, (skewHermitianPart_isHermitian A).eigenvalues i) ≤ μ.im ∧
      μ.im ≤ ⨆ i, (skewHermitianPart_isHermitian A).eigenvalues i :=
  hirsch_im A hμ

/-! ### Theorem 5.2 and the first two Gershgorin theorems -/

/-- **Theorem 5.2** of [quarteroni2000numerical] (Gershgorin circles), (5.4). Let
$A \in \mathbb{C}^{n \times n}$. Then
$$\sigma(A) \subseteq S_R = \bigcup_{i=1}^n R_i, \qquad R_i = \Big\{z \in \mathbb{C} : |z -
  a_{ii}| \le \sum_{j \neq i} |a_{ij}|\Big\}.$$

The proof specializes the backbone's `Matrix.spectrum_subset_iUnion_closedBall`. -/
theorem theorem_5_2 (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ A ⊆ ⋃ i, Metric.closedBall (A i i) (∑ j ∈ univ.erase i, ‖A i j‖) :=
  spectrum_subset_iUnion_closedBall A

/-- **Equation (5.6)** of [quarteroni2000numerical]. Let $A \in \mathbb{C}^{n \times n}$. Then the
spectrum lies in the union of the column circles:
$$\sigma(A) \subseteq S_C = \bigcup_{j=1}^n C_j, \qquad C_j = \Big\{z \in \mathbb{C} : |z -
  a_{jj}| \le \sum_{i \neq j} |a_{ij}|\Big\}.$$

This is Theorem 5.2 for $A^T$, which has the same spectrum as $A$. The proof specializes the
backbone's `Matrix.spectrum_subset_iUnion_closedBall_col`. -/
theorem equation_5_6 (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ A ⊆ ⋃ j, Metric.closedBall (A j j) (∑ i ∈ univ.erase j, ‖A i j‖) :=
  spectrum_subset_iUnion_closedBall_col A

/-- **Property 5.1** of [quarteroni2000numerical] (first Gershgorin theorem), (5.7). Let
$A \in \mathbb{C}^{n \times n}$. Then every eigenvalue of $A$ lies in the intersection of the
union of the row circles with the union of the column circles:
$$\sigma(A) \subseteq S_R \cap S_C.$$

This is (5.4) and (5.6) together. -/
theorem property_5_1 (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ A ⊆
      (⋃ i, Metric.closedBall (A i i) (∑ j ∈ univ.erase i, ‖A i j‖)) ∩
        ⋃ j, Metric.closedBall (A j j) (∑ i ∈ univ.erase j, ‖A i j‖) :=
  Set.subset_inter (theorem_5_2 A) (equation_5_6 A)

/-- **Property 5.2** of [quarteroni2000numerical] (second Gershgorin theorem). Let
$A \in \mathbb{C}^{n \times n}$, let $\tau$ be a set of $m$ indices, let
$S_1 = \bigcup_{i \in \tau} R_i$ be the union of the row circles with index in $\tau$, and let
$S_2 = \bigcup_{i \notin \tau} R_i$ be the union of the other row circles. If
$S_1 \cap S_2 = \emptyset$, then $S_1$ contains exactly $m$ eigenvalues of $A$ and $S_2$
contains exactly $n - m$ eigenvalues of $A$, each counted with its algebraic multiplicity, and
every eigenvalue of $A$ that is not in $S_1$ lies in $S_2$.

The book takes $\tau = \{1, \dots, m\}$. The counts are `Polynomial.countRootsIn` of the
characteristic polynomial. The proof applies the backbone's
`Matrix.card_spectrum_of_disjoint_gershgorin` to $\tau$ and to its complement, and Theorem 5.2
to the last clause. -/
theorem property_5_2 (A : Matrix (Fin n) (Fin n) ℂ) (τ : Finset (Fin n)) {S₁ S₂ : Set ℂ}
    (hS₁ : S₁ = ⋃ i ∈ τ, Metric.closedBall (A i i) (∑ j ∈ univ.erase i, ‖A i j‖))
    (hS₂ : S₂ = ⋃ i ∈ τᶜ, Metric.closedBall (A i i) (∑ j ∈ univ.erase i, ‖A i j‖))
    (hdisj : Disjoint S₁ S₂) :
    A.charpoly.countRootsIn S₁ = τ.card ∧ A.charpoly.countRootsIn S₂ = n - τ.card ∧
      ∀ μ ∈ spectrum ℂ A, μ ∉ S₁ → μ ∈ S₂ := by
  refine ⟨card_spectrum_of_disjoint_gershgorin A τ hS₁ hS₂ hdisj, ?_, fun μ hμ hμ₁ => ?_⟩
  · rw [card_spectrum_of_disjoint_gershgorin A τᶜ hS₂ (by rw [compl_compl]; exact hS₁) hdisj.symm,
      card_compl, Fintype.card_fin]
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (theorem_5_2 A hμ)
    by_cases hiτ : i ∈ τ
    · exact absurd (hS₁ ▸ Set.mem_iUnion₂.mpr ⟨i, hiτ, hi⟩) hμ₁
    · exact hS₂ ▸ Set.mem_iUnion₂.mpr ⟨i, Finset.mem_compl.mpr hiτ, hi⟩

/-! ### Definition 5.1 and the third Gershgorin theorem -/

/-- **Definition 5.1** of [quarteroni2000numerical]. A matrix $A \in \mathbb{C}^{n \times n}$ is
**reducible** if there is a permutation matrix $P$ such that
$$P A P^T = \begin{bmatrix} B_{11} & B_{12} \\ 0 & B_{22} \end{bmatrix}$$
with $B_{11}$ and $B_{22}$ square. A matrix is **irreducible** if it is not reducible.

Here $P A P^T$ is `A.submatrix σ σ` for a permutation $\sigma$ of the indices, $s$ is the index
set of the leading block $B_{11}$, which is proper and nonempty, and the zero block is the
condition that the entries in the rows outside $s$ and the columns in $s$ vanish. The definition
depends only on the zero pattern, so it is stated for any entry type with a zero. The book
states it over $\mathbb{C}$ and uses it over $\mathbb{R}$ in Property 5.3. -/
def definition_5_1 {R : Type*} [Zero R] (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (s : Finset (Fin n)), s.Nonempty ∧ s ≠ univ ∧
    ∀ i ∉ s, ∀ j ∈ s, A.submatrix σ σ i j = 0

/-- Definition 5.1 of [quarteroni2000numerical] agrees with the backbone. Let $n \ge 2$ and let $A$
be an $n \times n$ matrix over a normed group. Then $A$ is reducible in the sense of Definition
5.1 if and only if it is not pattern-irreducible (`Matrix.IsPatternIrreducible`, strong
connectivity of the adjacency quiver).

The proof is `Matrix.not_isPatternIrreducible_iff_exists_submatrix_blockTriangular` with the
index set of the block replaced by its complement: the backbone sets the entries from $s$ to its
complement to zero, and the book the entries from the complement to $s$. For $n = 1$ the two
notions differ: the $1 \times 1$ zero matrix is pattern-reducible but not reducible. This is the
reason for the hypothesis $n \ge 2$. -/
theorem definition_5_1_iff {R : Type*} [NormedAddCommGroup R] (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) R) : definition_5_1 A ↔ ¬ A.IsPatternIrreducible := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [not_isPatternIrreducible_iff_exists_submatrix_blockTriangular]
  constructor
  · rintro ⟨σ, s, hs, hsu, hz⟩
    exact ⟨σ, sᶜ, Finset.nonempty_iff_ne_empty.mpr (mt s.compl_eq_empty_iff.mp hsu),
      s.compl_ne_univ_iff_nonempty.mpr hs,
      fun i hi j hj => hz i (Finset.mem_compl.mp hi) j (by simpa using hj)⟩
  · rintro ⟨σ, s, hs, hsu, hz⟩
    exact ⟨σ, sᶜ, Finset.nonempty_iff_ne_empty.mpr (mt s.compl_eq_empty_iff.mp hsu),
      s.compl_ne_univ_iff_nonempty.mpr hs,
      fun i hi j hj => hz i (by simpa using hi) j (Finset.mem_compl.mp hj)⟩

/-- **Property 5.3** of [quarteroni2000numerical]. Let $n \ge 2$ and
$A \in \mathbb{R}^{n \times n}$. The oriented graph of $A$ has the vertices $P_1, \dots, P_n$
and a line oriented from $P_i$ to $P_j$ if and only if $a_{ij} \neq 0$. Then $A$ is irreducible
if and only if its oriented graph is strongly connected, that is, for every two distinct
vertices $P_i$ and $P_j$ there is an oriented path from $P_i$ to $P_j$.

**Reading.** The hypothesis $n \ge 2$ comes from the comparison with the backbone in
`QuarteroniSaccoSaleri.Chapter05.definition_5_1_iff`.

The oriented graph is Mathlib's `Matrix.adjQuiver A`, whose arrows $i \to j$ are exactly the
nonzero entries (`Matrix.nonempty_adjQuiver_hom_iff`). The proof specializes the backbone's
`Matrix.isPatternIrreducible_iff_nonempty_path` through
`QuarteroniSaccoSaleri.Chapter05.definition_5_1_iff`. The book cites Varga (1962) for the proof. -/
theorem property_5_3 (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) :
    ¬ definition_5_1 A ↔
      letI := A.adjQuiver; ∀ i j : Fin n, i ≠ j → Nonempty (Quiver.Path i j) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  let _ : Quiver (Fin n) := A.adjQuiver
  rw [definition_5_1_iff hn, not_not, isPatternIrreducible_iff_nonempty_path]
  refine ⟨fun h i j _ => h i j, fun h i j => ?_⟩
  by_cases hij : i = j
  · subst hij
    exact ⟨Quiver.Path.nil⟩
  · exact h i j hij

/-- **Property 5.4** of [quarteroni2000numerical] (third Gershgorin theorem). Let $n \ge 2$, and let
$A \in \mathbb{C}^{n \times n}$ be irreducible. An eigenvalue $\lambda \in \sigma(A)$ cannot lie
on the boundary of $S_R$ unless it lies on the boundary of every circle $R_i$: if $\lambda$ is
in the boundary of $S_R$, then
$$|\lambda - a_{ii}| = \sum_{j \neq i} |a_{ij}|, \qquad i = 1, \dots, n.$$

**Reading.** The hypothesis $n \ge 2$ comes from the comparison with the backbone in
`QuarteroniSaccoSaleri.Chapter05.definition_5_1_iff`.

The proof specializes the backbone's `Matrix.IsPatternIrreducible.norm_sub_eq_of_mem_frontier`
through `QuarteroniSaccoSaleri.Chapter05.definition_5_1_iff`. -/
theorem property_5_4 (hn : 2 ≤ n) {A : Matrix (Fin n) (Fin n) ℂ} (hA : ¬ definition_5_1 A)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ A)
    (hfr : μ ∈ frontier (⋃ i, Metric.closedBall (A i i) (∑ j ∈ univ.erase i, ‖A i j‖)))
    (i : Fin n) : ‖μ - A i i‖ = ∑ j ∈ univ.erase i, ‖A i j‖ :=
  (not_not.mp ((definition_5_1_iff hn A).not.mp hA)).norm_sub_eq_of_mem_frontier hμ hfr i

end QuarteroniSaccoSaleri.Chapter05
