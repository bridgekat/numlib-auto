/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Order
import Numlib.Eigen.InvariantSubspace
import Numlib.Eigen.Perturbation
import NumlibSurface.GolubVanLoan.Chapter07.Section01

/-!
# Golub and Van Loan, Section 7.2: Perturbation Theory

This module formalizes §7.2 of [golub2013matrix], which studies how the eigenvalues and the
invariant subspaces of a complex matrix $A \in \mathbb{C}^{n \times n}$ change under a perturbation
$A + E$. It covers the Gershgorin theorem (Theorem 7.2.1) and its isolated discs, the Bauer–Fike
theorem (Theorem 7.2.2) in every $p$-norm, the step (7.2.1) that the proofs of Theorems 7.2.1–7.2.3
share, the bound of Theorem 7.2.3 through a Schur decomposition $Q^H A Q = D + N$, the quantity
$s(\lambda) = |y^H x|$ whose reciprocal is the condition of a simple eigenvalue (7.2.2), the
$2 \times 2$ example of a repeated eigenvalue, the separation $\operatorname{sep}(T_{11}, T_{22})$
of (7.2.5), Stewart's theorem on the perturbation of an invariant subspace (Theorem 7.2.4) with
(7.2.6) and Corollary 7.2.5, and the sensitivity of an eigenvector (Corollary 7.2.6), where
$\operatorname{sep}(\lambda, T_{22}) = \sigma_{\min}(T_{22} - \lambda I)$.

The proofs specialize the backbone: `Numlib.Eigen.Perturbation` supplies the Gershgorin and
Bauer–Fike theorems, the resolvent step, Theorem 7.2.3, the eigenvalue condition number and the
differentiable eigenvalue branch; `Numlib.LinearAlgebra.Matrix.Sylvester` supplies the separation
`Matrix.sep`; and `Numlib.Eigen.InvariantSubspace` supplies Stewart's invariant graph
`Matrix.exists_invariant_graph_of_sep` and the gap bound `Matrix.gap_range_fromRows_le`.

## Main definitions

* §7.2.2, `GolubVanLoan.Chapter07.eigenvalueSensitivity`: the quantity $s(\lambda) = |y^H x|$ of
  (7.2.2).
* Theorem 7.2.4, `GolubVanLoan.Chapter07.stewartBasis`: the matrix
  $\tilde Q_1 = (Q_1 + Q_2 P)(I + P^H P)^{-1/2}$.
* Corollary 7.2.6, `GolubVanLoan.Chapter07.stewartVector`: the vector
  $\tilde q_1 = (q_1 + Q_2 p)/\sqrt{1 + p^H p}$.

## Main results

* Theorem 7.2.1, `GolubVanLoan.Chapter07.theorem_7_2_1`: if $X^{-1} A X = D + F$ with $F$ of zero
  diagonal, the eigenvalues of $A$ lie in the union of the Gershgorin discs.
* §7.2.1, `GolubVanLoan.Chapter07.gershgorin_isolated`: a Gershgorin disc disjoint from the others
  contains exactly one eigenvalue, counted with multiplicity.
* Theorem 7.2.2, `GolubVanLoan.Chapter07.theorem_7_2_2`: the Bauer–Fike bound $\min_{\lambda \in
  \lambda(A)} |\lambda - \mu| \le \kappa_p(X) \|E\|_p$ for a diagonalizable $A$.
* (7.2.1), `GolubVanLoan.Chapter07.equation_7_2_1`: if
  $\mu \in \lambda(A + E) \setminus \lambda(A)$, then $1 \le \|(\mu I - A)^{-1} E\|_2 \le \|(\mu I -
  A)^{-1}\|_2 \|E\|_2$.
* Theorem 7.2.3, `GolubVanLoan.Chapter07.theorem_7_2_3`: the bound $\max(\theta, \theta^{1/p})$ on
  the distance from an eigenvalue of $A + E$ to $\lambda(A)$.
* §7.2.2, `GolubVanLoan.Chapter07.inner_ne_zero_of_simple`: $y^H x \neq 0$ for a simple eigenvalue.
* (7.2.2), `GolubVanLoan.Chapter07.equation_7_2_2`: a simple eigenvalue has a differentiable branch
  with $|\lambda'(0)| \le \|F\|_2 / s(\lambda)$, and the bound is attained.
* §7.2.3, `GolubVanLoan.Chapter07.repeated_eigenvalue_example`: for $A = \begin{bmatrix} 1 & a \\ 0
  & 1 \end{bmatrix}$ with $a \neq 0$, no eigenvalue branch of $A + \varepsilon F$ is differentiable
  at $0$.
* (7.2.5), `GolubVanLoan.Chapter07.equation_7_2_5`: $\operatorname{sep}(T_{11}, T_{22})$ is the
  minimum of $\|T_{11} X - X T_{22}\|_F / \|X\|_F$ over $X \neq 0$.
* Theorem 7.2.4, `GolubVanLoan.Chapter07.theorem_7_2_4`: Stewart's theorem, the existence of a
  nearby invariant subspace of $A + E$ with an orthonormal basis $\tilde Q_1$.
* (7.2.6), `GolubVanLoan.Chapter07.equation_7_2_6`: $\|P (I + P^H P)^{-1/2}\|_2 \le \|P\|_2 \le
  \|P\|_F$.
* Corollary 7.2.5, `GolubVanLoan.Chapter07.corollary_7_2_5`:
  $\operatorname{dist}(\operatorname{ran}(Q_1), \operatorname{ran}(\tilde Q_1)) \le 4 \|E_{21}\|_F /
  \operatorname{sep}(T_{11}, T_{22})$.
* §7.2.5, `GolubVanLoan.Chapter07.sep_one_eq_sigmaMin`: $\operatorname{sep}(\lambda, T_{22}) =
  \sigma_{\min}(T_{22} - \lambda I) \le \min_{\mu \in \lambda(T_{22})} |\mu - \lambda|$.
* Corollary 7.2.6, `GolubVanLoan.Chapter07.corollary_7_2_6`: the perturbation bound for an
  eigenvector.

## Conventions

* The matrices of this section are complex, `A : Matrix (Fin n) (Fin n) ℂ`, as in §7.1.
* A right eigenvector satisfies $Ax = \lambda x$, which is `A *ᵥ x = λ • x`. A left eigenvector
  satisfies $y^H A = \lambda y^H$, which is `star y ᵥ* A = λ • star y`. A unit vector $x$ has
  `‖WithLp.toLp 2 x‖ = 1`.
* $\|\cdot\|_2$ is the scoped norm `Matrix.Norms.L2Operator`, and $\|\cdot\|_F$ is the scoped norm
  `Matrix.Norms.Frobenius`; each is opened in its own section. Where both norms occur in one
  statement, the 2-norm is `Matrix.lpOpNorm 2`.
* The separation $\operatorname{sep}(T_{11}, T_{22})$ is `Matrix.sep`. The distance
  $\operatorname{dist}$ of two subspaces is the gap `Submodule.gap`. For a square matrix $B$,
  $\sigma_{\min}(B)$ is the least singular value `⨅ i, B.colSingularValues i`.

## Implementation notes

* In Theorem 7.2.4 and Corollary 7.2.5 the index type is `Fin r ⊕ Fin s` with $s = n - r$, so that
  $Q = [Q_1\ Q_2]$ and the blocks of $Q^H A Q$ are given by `Matrix.fromBlocks`. In Corollary 7.2.6
  the index type is `Unit ⊕ Fin s`.
* The inverse square root $(I + P^H P)^{-1/2}$ is `(CFC.sqrt (1 + Pᴴ * P))⁻¹`, with the scoped order
  `MatrixOrder`.

## Deviations from the source

* **§7.2.2** (typo). The source interchanges $x$ and $y$ when assigning them to columns of the
  right and left Jordan bases. See `GolubVanLoan.Chapter07.inner_ne_zero_of_simple`.
* **Equation (7.2.2), derivative argument** (reading). The assertion states differentiability at
  the origin and bounds the derivative for an arbitrary perturbation direction, scaled by its
  norm. See `GolubVanLoan.Chapter07.equation_7_2_2`.
* **Theorem 7.2.4 and Corollary 7.2.5** (generalization). The separation and invariant-subspace
  bounds apply to upper block triangular matrices with arbitrary diagonal blocks. See
  `GolubVanLoan.Chapter07.theorem_7_2_4` and `GolubVanLoan.Chapter07.corollary_7_2_5`.
* **Theorem 7.2.3** (generalization). The source takes a Schur decomposition, with $N$ strictly
  upper triangular, and the least $p$ with $|N|^p = 0$. The theorem holds for every $p \ge 1$ with
  $|N|^p = 0$ and every such $N$. See `GolubVanLoan.Chapter07.theorem_7_2_3`.
* **§7.2.3** (reading). The source says that the rate of change of the eigenvalues at the origin is
  infinite. The statement reads this as: no branch of eigenvalues is differentiable at
  $\varepsilon = 0$. See `GolubVanLoan.Chapter07.repeated_eigenvalue_example`.

## Not formalized

* **Wilkinson's bound on the distance to a matrix with a multiple eigenvalue**, $\|E\|_2 / \|A\|_2
  \le s(\lambda) / \sqrt{1 - s(\lambda)^2}$. The source quotes it from Wilkinson (1972) without a
  proof or a construction of $E$.
* **The heuristic that perturbations of size $O(\varepsilon)$ can move a defective eigenvalue by
  $O(\varepsilon^{1/p})$.** Its rigorous content is the term $\theta^{1/p}$ of Theorem 7.2.3.
* **The discussion of "wobbly" eigenvectors.**
-/

open Matrix Polynomial Filter Topology Metric

namespace GolubVanLoan.Chapter07

variable {n : ℕ}

/-! ### §7.2.1 Eigenvalue sensitivity -/

/-- The diagonal of $\operatorname{diag}(d) + F$ is $d$ when $F$ has zero diagonal. -/
private theorem diagonal_add_apply_self {d : Fin n → ℂ} {F : Matrix (Fin n) (Fin n) ℂ}
    (hF : ∀ i, F i i = 0) (i : Fin n) : (diagonal d + F) i i = d i := by
  simp [hF i]

/-- When $F$ has zero diagonal, the off-diagonal absolute row sums of $\operatorname{diag}(d) + F$
are the absolute row sums of $F$. -/
private theorem sum_erase_norm_diagonal_add {d : Fin n → ℂ} {F : Matrix (Fin n) (Fin n) ℂ}
    (hF : ∀ i, F i i = 0) (i : Fin n) :
    ∑ j ∈ Finset.univ.erase i, ‖(diagonal d + F) i j‖ = ∑ j, ‖F i j‖ := by
  rw [← Finset.add_sum_erase _ (fun j => ‖F i j‖) (Finset.mem_univ i), hF i, norm_zero,
    zero_add]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Matrix.add_apply, diagonal_apply_ne _ (Finset.ne_of_mem_erase hj).symm, zero_add]

/-- **Theorem 7.2.1** of [golub2013matrix] (Gershgorin circle theorem). Let
$A, X, F \in \mathbb{C}^{n \times n}$ with $X$ nonsingular, and let $d \in \mathbb{C}^n$. If
$X^{-1} A X = D + F$ with $D = \operatorname{diag}(d_1, \dots, d_n)$ and $F$ has zero diagonal,
then
$$\lambda(A) \subseteq \bigcup_{i=1}^n D_i, \qquad D_i = \Big\{ z \in \mathbb{C} : |z - d_i| \le
  \sum_{j=1}^n |f_{ij}| \Big\}.$$

The set $\lambda(A)$ is `spectrum ℂ A`, and the disc $D_i$ is
`Metric.closedBall (d i) (∑ j, ‖F i j‖)`. -/
theorem theorem_7_2_1 {A X F : Matrix (Fin n) (Fin n) ℂ} {d : Fin n → ℂ} (hX : IsUnit X)
    (h : X⁻¹ * A * X = diagonal d + F) (hF : ∀ i, F i i = 0) :
    spectrum ℂ A ⊆ ⋃ i, closedBall (d i) (∑ j, ‖F i j‖) := by
  rw [IsSimilar.spectrum_eq (A := A) ⟨X, hX, rfl⟩, h]
  intro μ hμ
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (spectrum_subset_iUnion_closedBall _ hμ)
  rw [diagonal_add_apply_self hF, sum_erase_norm_diagonal_add hF] at hi
  exact Set.mem_iUnion.2 ⟨i, hi⟩

/-- **Section 7.2.1** of [golub2013matrix], isolated Gershgorin discs. Let
$A, X, F \in \mathbb{C}^{n \times n}$ and $d \in \mathbb{C}^n$ with $X$ nonsingular,
$X^{-1} A X = \operatorname{diag}(d) + F$ and $F$ of zero diagonal, and let $D_1, \dots, D_n$ be
the Gershgorin discs of Theorem 7.2.1. If $D_i$ is disjoint from the union of the discs $D_k$
with $k \neq i$, then $D_i$ contains exactly one eigenvalue of $A$, counted with algebraic
multiplicity.

The source says that such a disc "contains precisely one eigenvalue of $A$". The count is
`Polynomial.countRootsIn` of the characteristic polynomial of $A$, which counts roots with
multiplicity. -/
theorem gershgorin_isolated {A X F : Matrix (Fin n) (Fin n) ℂ} {d : Fin n → ℂ} (hX : IsUnit X)
    (h : X⁻¹ * A * X = diagonal d + F) (hF : ∀ i, F i i = 0) (i : Fin n)
    (hdisj : Disjoint (closedBall (d i) (∑ j, ‖F i j‖))
      (⋃ k ∈ ({i} : Finset (Fin n))ᶜ, closedBall (d k) (∑ j, ‖F k j‖))) :
    A.charpoly.countRootsIn (closedBall (d i) (∑ j, ‖F i j‖)) = 1 := by
  have hsim : IsSimilar A (diagonal d + F) := ⟨X, hX, h.symm⟩
  rw [hsim.charpoly_eq]
  refine card_spectrum_of_isolated_gershgorin (diagonal d + F) i
    (S' := ⋃ k ∈ ({i} : Finset (Fin n))ᶜ, closedBall (d k) (∑ j, ‖F k j‖)) ?_ ?_ ?_
  · rw [diagonal_add_apply_self hF, sum_erase_norm_diagonal_add hF]
  · simp only [diagonal_add_apply_self hF, sum_erase_norm_diagonal_add hF]
  · exact hdisj

/-- **Theorem 7.2.2** of [golub2013matrix] (Bauer–Fike theorem). Let
$A, X, E \in \mathbb{C}^{n \times n}$ with $X$ nonsingular and $X^{-1} A X = D =
\operatorname{diag}(\lambda_1, \dots, \lambda_n)$, and let $1 \le p \le \infty$. If $\mu$ is an
eigenvalue of $A + E$, then
$$\min_{\lambda \in \lambda(A)} |\lambda - \mu| \le \kappa_p(X) \|E\|_p.$$

The diagonal of $D$ is `d`, and the minimum is stated as the existence of an index $i$ with
$|d_i - \mu| \le \kappa_p(X) \|E\|_p$. The exponent is `p : ENNReal` with `1 ≤ p`, $\kappa_p(X)$
is `Matrix.condNumberLp p X`, and $\|E\|_p$ is `Matrix.lpOpNorm p E`. The proof applies
`Matrix.bauer_fike_lpOpNorm` to $A = X D X^{-1}$. -/
theorem theorem_7_2_2 (p : ENNReal) [Fact (1 ≤ p)] {A X E : Matrix (Fin n) (Fin n) ℂ}
    {d : Fin n → ℂ} (hX : IsUnit X) (hXA : X⁻¹ * A * X = diagonal d) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (A + E)) :
    ∃ i, ‖d i - μ‖ ≤ condNumberLp p X * lpOpNorm p E := by
  have hdet := (isUnit_iff_isUnit_det X).1 hX
  have hA : A = X * diagonal d * X⁻¹ := by
    rw [← hXA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.one_mul,
      Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.mul_one]
  obtain ⟨i, hi⟩ := bauer_fike_lpOpNorm p X d hX E (hA ▸ hμ)
  exact ⟨i, by rwa [norm_sub_rev]⟩

section L2

open scoped Matrix.Norms.L2Operator

/-- **Equation (7.2.1)** of [golub2013matrix]. Let $A, E \in \mathbb{C}^{n \times n}$. If $\mu$ is
an eigenvalue of $A + E$ and not an eigenvalue of $A$, then
$$1 \le \|(\mu I - A)^{-1} E\|_2 \le \|(\mu I - A)^{-1}\|_2 \|E\|_2.$$

This is the step that the proofs of Theorems 7.2.1–7.2.3 share; the source derives it from its
Lemma 2.3.3. The norm is the scoped 2-norm `Matrix.Norms.L2Operator`. -/
theorem equation_7_2_1 {A E : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ} (hμ : μ ∈ spectrum ℂ (A + E))
    (hA : μ ∉ spectrum ℂ A) :
    1 ≤ ‖(μ • 1 - A)⁻¹ * E‖ ∧ ‖(μ • 1 - A)⁻¹ * E‖ ≤ ‖(μ • 1 - A)⁻¹‖ * ‖E‖ :=
  ⟨one_le_norm_mul_of_mem_spectrum_add hμ hA, norm_mul_le _ _⟩

/-- **Theorem 7.2.3** of [golub2013matrix]. Let $A, Q, N, E \in \mathbb{C}^{n \times n}$ and
$d \in \mathbb{C}^n$, with $Q$ unitary and $Q^H A Q = D + N$, where
$D = \operatorname{diag}(d_1, \dots, d_n)$. Let $p \ge 1$ be an integer with $|N|^p = 0$, where
$|N|$ is the matrix of the absolute values of the entries of $N$. If $\mu$ is an eigenvalue of
$A + E$, then
$$\min_{1 \le i \le n} |d_i - \mu| \le \max(\theta, \theta^{1/p}), \qquad \theta = \|E\|_2
  \sum_{k=0}^{p-1} \|N\|_2^k.$$

**Generalization.** The source takes a Schur decomposition, so that $N$ is strictly upper
triangular, and the least $p$ with $|N|^p = 0$. The theorem needs neither: it holds for every
$N$ and every $p \ge 1$ with $|N|^p = 0$. The least such $p$ gives the best bound.

The matrix $|N|$ is `N.map (‖·‖)`, the minimum is stated as the existence of an index $i$, and
the norm is the scoped 2-norm `Matrix.Norms.L2Operator`. -/
theorem theorem_7_2_3 {A Q N E : Matrix (Fin n) (Fin n) ℂ} {d : Fin n → ℂ}
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) (hQA : star Q * A * Q = diagonal d + N) {p : ℕ}
    (hp : 1 ≤ p) (hN : (N.map (‖·‖)) ^ p = 0) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (A + E)) :
    ∃ i, ‖d i - μ‖ ≤
      max (‖E‖ * ∑ k ∈ Finset.range p, ‖N‖ ^ k)
        ((‖E‖ * ∑ k ∈ Finset.range p, ‖N‖ ^ k) ^ (1 / p : ℝ)) := by
  obtain ⟨i, hi⟩ := exists_norm_sub_le_of_schur hQ hQA hp hN E hμ
  exact ⟨i, by rwa [norm_sub_rev]⟩

end L2

/-! ### §7.2.2 The condition of a simple eigenvalue -/

/-- **Section 7.2.2** of [golub2013matrix], the quantity $s(\lambda)$ of (7.2.2). For
$x, y \in \mathbb{C}^n$,
$$s(\lambda) = |y^H x|.$$
When $x$ and $y$ are unit right and left eigenvectors of a simple eigenvalue $\lambda$, the
condition of $\lambda$ is $1/s(\lambda)$.

The definition takes only the two vectors. For unit vectors it is the reciprocal of the
backbone's eigenvalue condition number `Module.End.eigenvalueCondNumber`; see
`GolubVanLoan.Chapter07.eigenvalueSensitivity_eq_inv_eigenvalueCondNumber`. -/
noncomputable def eigenvalueSensitivity (x y : Fin n → ℂ) : ℝ :=
  ‖star y ⬝ᵥ x‖

/-- For unit vectors $x, y \in \mathbb{C}^n$, $s(\lambda) = |y^H x|$ is the reciprocal of the
backbone's condition number $\|x\| \|y\| / |\langle y, x \rangle|$,
`Module.End.eigenvalueCondNumber`. Both sides are $0$ when $y^H x = 0$. -/
theorem eigenvalueSensitivity_eq_inv_eigenvalueCondNumber {x y : Fin n → ℂ}
    (hx : ‖WithLp.toLp 2 x‖ = 1) (hy : ‖WithLp.toLp 2 y‖ = 1) :
    eigenvalueSensitivity x y =
      (Module.End.eigenvalueCondNumber ℂ (WithLp.toLp 2 x) (WithLp.toLp 2 y))⁻¹ := by
  rw [Module.End.eigenvalueCondNumber, hx, hy, EuclideanSpace.inner_toLp_toLp, dotProduct_comm,
    eigenvalueSensitivity]
  simp

/-- If $y^H A = \mu y^H$, then $\langle y, A z \rangle = \mu \langle y, z \rangle$ for every $z$. -/
private theorem inner_toEuclideanLin_of_left {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ}
    {y : Fin n → ℂ} (hy : star y ᵥ* A = μ • star y) (z : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ (WithLp.toLp 2 y) (toEuclideanLin A z) : ℂ) = μ * inner ℂ (WithLp.toLp 2 y) z := by
  obtain ⟨z, rfl⟩ : ∃ z', z = WithLp.toLp 2 z' := ⟨WithLp.ofLp z, (WithLp.toLp_ofLp _ _).symm⟩
  rw [toLpLin_toLp, toLin'_apply, EuclideanSpace.inner_toLp_toLp,
    EuclideanSpace.inner_toLp_toLp, dotProduct_comm, dotProduct_mulVec, hy, smul_dotProduct,
    smul_eq_mul, dotProduct_comm]

/-- The right eigenvector equation $A x = \mu x$, transferred to `EuclideanSpace ℂ (Fin n)` with
`Matrix.toEuclideanLin`. -/
private theorem toEuclideanLin_of_right {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ} {x : Fin n → ℂ}
    (hx : A *ᵥ x = μ • x) : toEuclideanLin A (WithLp.toLp 2 x) = μ • WithLp.toLp 2 x := by
  rw [toLpLin_toLp, toLin'_apply, hx, WithLp.toLp_smul]

/-- The generalized eigenspace of a simple eigenvalue has dimension one. -/
private theorem finrank_maxGenEigenspace_of_simple {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ}
    (hμ : IsSimpleEigenvalue A μ) :
    Module.finrank ℂ (Module.End.maxGenEigenspace (toEuclideanLin A) μ) = 1 := by
  rw [finrank_maxGenEigenspace_toEuclideanLin]
  exact hμ

/-- **Section 7.2.2** of [golub2013matrix], $y^H x \neq 0$ for a simple eigenvalue. Let
$A \in \mathbb{C}^{n \times n}$ and let $\lambda$ be a simple eigenvalue of $A$. If $x \neq 0$
satisfies $A x = \lambda x$ and $y \neq 0$ satisfies $y^H A = \lambda y^H$, then $y^H x \neq 0$.
Hence $s(\lambda) > 0$.

The source argues through the Jordan form. The proof here uses instead that the generalized
eigenspace of a simple eigenvalue is a line.

**Typo.** In the Jordan-basis explanation, the source pairs $y$ with the column of $X$ and $x$
with the column of $Y$. The right eigenvector $x$ belongs to the column of $X$ and the left
eigenvector $y$ belongs to the column of $Y$. -/
theorem inner_ne_zero_of_simple {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ}
    (hμ : IsSimpleEigenvalue A μ) {x y : Fin n → ℂ} (hx : A *ᵥ x = μ • x) (hx0 : x ≠ 0)
    (hy : star y ᵥ* A = μ • star y) (hy0 : y ≠ 0) : star y ⬝ᵥ x ≠ 0 := by
  have h := Module.End.inner_ne_zero_of_finrank_maxGenEigenspace_eq_one
    (toEuclideanLin_of_right hx) (by simpa using hx0) (inner_toEuclideanLin_of_left hy)
    (by simpa using hy0) (finrank_maxGenEigenspace_of_simple hμ)
  rwa [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at h

section L2

open scoped Matrix.Norms.L2Operator

/-- **Equation (7.2.2)** of [golub2013matrix], with its derivation. Let
$A, F \in \mathbb{C}^{n \times n}$, let $\lambda$ be a simple eigenvalue of $A$, and let $x$ and
$y$ be unit vectors with $A x = \lambda x$ and $y^H A = \lambda y^H$. Then there are functions
$\varepsilon \mapsto \lambda(\varepsilon) \in \mathbb{C}$ and $\varepsilon \mapsto
x(\varepsilon) \in \mathbb{C}^n$ with $\lambda(0) = \lambda$ and $x(0) = x$ such that $(A +
\varepsilon F) x(\varepsilon) = \lambda(\varepsilon) x(\varepsilon)$ for all $\varepsilon$ near
$0$, $x(\varepsilon)$ is differentiable at $0$, and $\lambda(\varepsilon)$ has at $0$ the
derivative
$$\lambda'(0) = \frac{y^H F x}{y^H x}, \qquad |\lambda'(0)| \le \frac{\|F\|_2}{s(\lambda)}.$$
The bound is attained: $F = y x^H$ has $\|F\|_2 = 1$ and $|y^H F x / y^H x| = 1/s(\lambda)$.

The source derives (7.2.2) by a first-order argument; here the existence of the differentiable
branches is part of the conclusion. For $\|F\|_2 = 1$ the bound is the condition $1/s(\lambda)$.
The parameter $\varepsilon$ is complex, the vectors $x(\varepsilon)$ are in
`EuclideanSpace ℂ (Fin n)`, $y x^H$ is `Matrix.vecMulVec y (star x)`, and the norm is the scoped
2-norm `Matrix.Norms.L2Operator`.

**Reading.** The theorem allows any direction $F$ and gives the bound scaled by $\|F\|_2$. It
states differentiability at the origin for branches satisfying the eigenvector equation
locally. The source assumes a unit direction and describes differentiable branches in a
neighborhood. -/
theorem equation_7_2_2 {A F : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ} (hμ : IsSimpleEigenvalue A μ)
    {x y : Fin n → ℂ} (hx : A *ᵥ x = μ • x) (hxn : ‖WithLp.toLp 2 x‖ = 1)
    (hy : star y ᵥ* A = μ • star y) (hyn : ‖WithLp.toLp 2 y‖ = 1) :
    (∃ (lam : ℂ → ℂ) (v : ℂ → EuclideanSpace ℂ (Fin n)) (lam' : ℂ), lam 0 = μ ∧
      v 0 = WithLp.toLp 2 x ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), toEuclideanLin (A + t • F) (v t) = lam t • v t) ∧
      DifferentiableAt ℂ v 0 ∧ HasDerivAt lam lam' 0 ∧
      lam' = (star y ⬝ᵥ (F *ᵥ x)) / (star y ⬝ᵥ x) ∧
      ‖lam'‖ ≤ ‖F‖ / eigenvalueSensitivity x y) ∧
    ‖vecMulVec y (star x)‖ = 1 ∧
      ‖(star y ⬝ᵥ (vecMulVec y (star x) *ᵥ x)) / (star y ⬝ᵥ x)‖ =
        1 / eigenvalueSensitivity x y := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxn
  have hy0 : y ≠ 0 := by rintro rfl; simp at hyn
  have hne := inner_ne_zero_of_simple hμ hx hx0 hy hy0
  set A' := toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A
  set B' := toEuclideanCLM (n := Fin n) (𝕜 := ℂ) F
  have hAu : A' (WithLp.toLp 2 x) = μ • WithLp.toLp 2 x := toEuclideanLin_of_right hx
  have hw : ∀ z, (inner ℂ (WithLp.toLp 2 y) (A' z) : ℂ) = μ * inner ℂ (WithLp.toLp 2 y) z :=
    inner_toEuclideanLin_of_left hy
  have hinner : (inner ℂ (WithLp.toLp 2 y) (WithLp.toLp 2 x) : ℂ) = star y ⬝ᵥ x := by
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  have hinnerF : (inner ℂ (WithLp.toLp 2 y) (B' (WithLp.toLp 2 x)) : ℂ) =
      star y ⬝ᵥ (F *ᵥ x) := by
    rw [toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  -- the norm of the rank-one `y xᴴ`
  have hrank : ‖vecMulVec y (star x)‖ = 1 := by
    rw [← l2_opNorm_toEuclideanCLM]
    refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_) ?_
    · obtain ⟨z, rfl⟩ : ∃ z', z = WithLp.toLp 2 z' := ⟨WithLp.ofLp z, (WithLp.toLp_ofLp _ _).symm⟩
      rw [toEuclideanCLM_toLp, vecMulVec_mulVec, op_smul_eq_smul, WithLp.toLp_smul, norm_smul,
        hyn, mul_one, one_mul]
      have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 x) (WithLp.toLp 2 z)
      rw [hxn, one_mul, EuclideanSpace.inner_toLp_toLp] at h
      simpa [dotProduct_comm] using h
    · have h := (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (vecMulVec y (star x))).le_opNorm
        (WithLp.toLp 2 x)
      rw [toEuclideanCLM_toLp, vecMulVec_mulVec, op_smul_eq_smul, WithLp.toLp_smul, norm_smul,
        hyn, mul_one, hxn, mul_one] at h
      have hxx : star x ⬝ᵥ x = 1 := by
        have h' := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 x)
        rw [hxn, EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at h'
        simpa using h'
      rwa [hxx, norm_one] at h
  refine ⟨?_, hrank, ?_⟩
  · obtain ⟨lam, v, v', h0, hv0, hev, hv, hlam⟩ :=
      Module.End.hasDerivAt_eigenvalue_perturbation_of_finrank_eq_one (A := A') (B := B') hAu
        (by simpa using hx0) hw (by simpa using hy0) (finrank_maxGenEigenspace_of_simple hμ)
    refine ⟨lam, v, _, h0, hv0, ?_, hv.differentiableAt, hlam, by rw [hinnerF, hinner], ?_⟩
    · filter_upwards [hev] with t ht
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
      exact ht
    · rw [hinnerF, hinner, norm_div, eigenvalueSensitivity, ← l2_opNorm_toEuclideanCLM]
      have hpos : 0 < ‖star y ⬝ᵥ x‖ := norm_pos_iff.2 hne
      rw [div_le_div_iff_of_pos_right hpos]
      calc ‖star y ⬝ᵥ (F *ᵥ x)‖ = ‖(inner ℂ (WithLp.toLp 2 y) (B' (WithLp.toLp 2 x)) : ℂ)‖ := by
            rw [hinnerF]
        _ ≤ ‖WithLp.toLp 2 y‖ * ‖B' (WithLp.toLp 2 x)‖ := norm_inner_le_norm _ _
        _ ≤ ‖WithLp.toLp 2 y‖ * (‖B'‖ * ‖WithLp.toLp 2 x‖) := by
            gcongr
            exact B'.le_opNorm _
        _ = ‖B'‖ := by rw [hxn, hyn, one_mul, mul_one]
  · have hxx : star x ⬝ᵥ x = 1 := by
      have h' := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 x)
      rw [hxn, EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at h'
      simpa using h'
    have hyy : star y ⬝ᵥ y = 1 := by
      have h' := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 y)
      rw [hyn, EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at h'
      simpa using h'
    rw [vecMulVec_mulVec, op_smul_eq_smul, hxx, one_smul, hyy, norm_div, norm_one,
      eigenvalueSensitivity]

end L2

/-! ### §7.2.3 Sensitivity of repeated eigenvalues -/

/-- **Section 7.2.3** of [golub2013matrix], the $2 \times 2$ example. Let $a \in \mathbb{C}$,
$$A = \begin{bmatrix} 1 & a \\ 0 & 1 \end{bmatrix}, \qquad F = \begin{bmatrix} 0 & 0 \\ 1 & 0
  \end{bmatrix}.$$
For every $\varepsilon \in \mathbb{C}$, $\lambda(A + \varepsilon F) = \{ z \in \mathbb{C} : (z -
1)^2 = \varepsilon a \}$, which is the source's $\{1 \pm \sqrt{\varepsilon a}\}$. If $a \neq 0$,
then no function $f$ with $f(\varepsilon) \in \lambda(A + \varepsilon F)$ for all $\varepsilon$
near $0$ is differentiable at $\varepsilon = 0$.

**Reading.** The source says that "their rate of change at the origin is infinite". The
statement reads this as the nonexistence of a branch of eigenvalues that is differentiable at
$0$.

A differentiable branch $z(\varepsilon)$ with $(z(\varepsilon) - 1)^2 = \varepsilon a$ would
give $a = 2 (z(0) - 1) z'(0) = 0$. -/
theorem repeated_eigenvalue_example (a : ℂ) :
    (∀ ε : ℂ, spectrum ℂ (!![1, a; 0, 1] + ε • !![0, 0; 1, 0]) = {z | (z - 1) ^ 2 = ε * a}) ∧
    (a ≠ 0 → ∀ f : ℂ → ℂ,
      (∀ᶠ ε in 𝓝 (0 : ℂ), f ε ∈ spectrum ℂ (!![1, a; 0, 1] + ε • !![0, 0; 1, 0])) →
        ¬ DifferentiableAt ℂ f 0) := by
  have hspec : ∀ ε : ℂ,
      spectrum ℂ (!![1, a; 0, 1] + ε • !![0, 0; 1, 0]) = {z | (z - 1) ^ 2 = ε * a} := by
    intro ε
    ext z
    rw [spectrum.mem_iff, Set.mem_ofPred_eq, Algebra.algebraMap_eq_smul_one,
      isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not, det_fin_two]
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, one_apply_eq,
      one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
      of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
      smul_eq_mul]
    constructor <;> intro h <;> linear_combination h
  refine ⟨hspec, fun ha f hf hd => ha ?_⟩
  have hev : (fun ε => (f ε - 1) ^ 2) =ᶠ[𝓝 (0 : ℂ)] fun ε => ε * a :=
    hf.mono fun ε hε => by rw [hspec] at hε; exact hε
  have h0 : f 0 - 1 = 0 := by
    have := hev.eq_of_nhds
    simpa using this
  have h1 : HasDerivAt (fun ε => (f ε - 1) ^ 2) (↑2 * (f 0 - 1) ^ (2 - 1) * deriv f 0) 0 :=
    (hd.hasDerivAt.sub_const 1).pow 2
  have h2 : HasDerivAt (fun ε => (f ε - 1) ^ 2) a 0 := by
    have h3 : HasDerivAt (fun ε : ℂ => ε * a) a 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).mul_const a
    exact h3.congr_of_eventuallyEq hev
  have := h1.unique h2
  rw [h0] at this
  simpa using this.symm

/-! ### §7.2.4 Invariant subspace sensitivity -/

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Equation (7.2.5)** of [golub2013matrix]. Let $p, q \ge 1$,
$T_{11} \in \mathbb{C}^{p \times p}$ and $T_{22} \in \mathbb{C}^{q \times q}$. Then
$$\operatorname{sep}(T_{11}, T_{22}) = \min_{X \neq 0} \frac{\|T_{11} X - X
  T_{22}\|_F}{\|X\|_F},$$
where $X$ ranges over $\mathbb{C}^{p \times q}$, and the minimum is attained.

The backbone defines `Matrix.sep` as the least value of $\|T_{11} X - X T_{22}\|_F$ on the
Frobenius unit sphere. The statement says that `Matrix.sep T₁₁ T₂₂` is the least element of the
set of the quotients. -/
theorem equation_7_2_5 {p q : ℕ} [NeZero p] [NeZero q] (T₁₁ : Matrix (Fin p) (Fin p) ℂ)
    (T₂₂ : Matrix (Fin q) (Fin q) ℂ) :
    IsLeast {r | ∃ X : Matrix (Fin p) (Fin q) ℂ, X ≠ 0 ∧ ‖T₁₁ * X - X * T₂₂‖ / ‖X‖ = r}
      (sep T₁₁ T₂₂) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨X, hX, hXs⟩ := exists_sep_eq T₁₁ T₂₂
    refine ⟨X, fun h0 => by simp [h0] at hX, ?_⟩
    rw [hX, div_one, hXs]
  · rintro r ⟨X, hX, rfl⟩
    rw [le_div_iff₀ (norm_pos_iff.2 hX)]
    exact sep_mul_norm_le X

end Frobenius

/-! ### §7.2.4–7.2.5 Invariant subspace and eigenvector sensitivity -/

/-- **Section 7.2.5** of [golub2013matrix], the separation from a $1 \times 1$ block. Let
$\lambda \in \mathbb{C}$ and $T_{22} \in \mathbb{C}^{q \times q}$. Then
$$\operatorname{sep}(\lambda, T_{22}) = \sigma_{\min}(T_{22} - \lambda I),$$
and $\operatorname{sep}(\lambda, T_{22}) \le |\mu - \lambda|$ for every eigenvalue $\mu$ of
$T_{22}$.

The source makes the first observation in the proof of Corollary 7.2.6. Here $\sigma_{\min}$ is
the least column singular value, and for $q = 0$ both sides of the identity are $0$. In Lean the
scalar is `c` and the block is `of fun _ _ => c` on `Unit`. The proof uses
`Matrix.sep_eq_iInf_colSingularValues` and `Matrix.sep_le_norm_sub`. -/
theorem sep_one_eq_sigmaMin {q : ℕ} (c : ℂ) (T₂₂ : Matrix (Fin q) (Fin q) ℂ) :
    sep (of fun _ _ => c : Matrix Unit Unit ℂ) T₂₂ = ⨅ i, (T₂₂ - c • 1).colSingularValues i ∧
      ∀ μ ∈ spectrum ℂ T₂₂, sep (of fun _ _ => c : Matrix Unit Unit ℂ) T₂₂ ≤ ‖μ - c‖ := by
  refine ⟨sep_eq_iInf_colSingularValues c T₂₂, fun μ hμ => ?_⟩
  have hc : c ∈ spectrum ℂ (of fun _ _ => c : Matrix Unit Unit ℂ) := by
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
    have h0 : c • (1 : Matrix Unit Unit ℂ) - of (fun _ _ => c) = 0 := by
      ext i j
      simp
    rw [h0]
    exact not_isUnit_zero
  rw [norm_sub_rev]
  exact sep_le_norm_sub hc hμ

section Stewart

open scoped ComplexOrder MatrixOrder

variable {r s : ℕ}

/-- Let $P \in \mathbb{C}^{k \times r}$ and let $S = (I + P^H P)^{1/2}$ be the positive square root.
Then $S^2 = I + P^H P$, $S$ is Hermitian, and $S$ is nonsingular. These are the facts about $S$
that Theorem 7.2.4 uses. -/
theorem sqrt_one_add_conjTranspose_mul_self {k : ℕ} (P : Matrix (Fin k) (Fin r) ℂ) :
    CFC.sqrt (1 + Pᴴ * P) * CFC.sqrt (1 + Pᴴ * P) = 1 + Pᴴ * P ∧
      (CFC.sqrt (1 + Pᴴ * P))ᴴ = CFC.sqrt (1 + Pᴴ * P) ∧
      IsUnit (CFC.sqrt (1 + Pᴴ * P)).det := by
  have hpd : (1 + Pᴴ * P).PosDef :=
    PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self P)
  have hnn : 0 ≤ 1 + Pᴴ * P := nonneg_iff_posSemidef.2 hpd.posSemidef
  have hSS := CFC.sqrt_mul_sqrt_self _ hnn
  refine ⟨hSS, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (1 + Pᴴ * P))).star_eq, ?_⟩
  have h : IsUnit (CFC.sqrt (1 + Pᴴ * P) * CFC.sqrt (1 + Pᴴ * P)).det := by
    rw [hSS]
    exact (isUnit_iff_isUnit_det _).1 hpd.isUnit
  rw [det_mul] at h
  exact isUnit_of_mul_isUnit_left h

/-- For $S = (I + P^H P)^{1/2}$ and every $y$, $\|y\| \le \|S y\|$, because
$\|S y\|^2 = \|y\|^2 + \|P y\|^2$. -/
private theorem norm_le_norm_sqrt_apply {k : ℕ} (P : Matrix (Fin k) (Fin r) ℂ)
    (y : EuclideanSpace ℂ (Fin r)) :
    ‖y‖ ≤ ‖toEuclideanLin (CFC.sqrt (1 + Pᴴ * P)) y‖ := by
  obtain ⟨hSS, hSh, -⟩ := sqrt_one_add_conjTranspose_mul_self P
  set S := CFC.sqrt (1 + Pᴴ * P) with hS
  have h1 : (inner ℂ (toEuclideanLin S y) (toEuclideanLin S y) : ℂ) =
      inner ℂ y y + inner ℂ (toEuclideanLin P y) (toEuclideanLin P y) := by
    rw [← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint, hSh,
      ← toEuclideanLin_mul_apply, hSS, map_add, LinearMap.add_apply, toEuclideanLin_one_apply,
      inner_add_right, toEuclideanLin_mul_apply, toEuclideanLin_conjTranspose_eq_adjoint,
      LinearMap.adjoint_inner_right]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K] at h1
  have h2 : ‖toEuclideanLin S y‖ ^ 2 = ‖y‖ ^ 2 + ‖toEuclideanLin P y‖ ^ 2 := by
    exact_mod_cast h1
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _)
    (by nlinarith [sq_nonneg ‖toEuclideanLin P y‖])

open scoped Matrix.Norms.Frobenius in
/-- **Equation (7.2.6)** of [golub2013matrix]. For every $P \in \mathbb{C}^{k \times r}$,
$$\|P (I + P^H P)^{-1/2}\|_2 \le \|P\|_2 \le \|P\|_F.$$

The source says that the first inequality can be shown with the SVD of $P$. The proof here does
not use the SVD: with $S = (I + P^H P)^{1/2}$, $\|S y\|^2 = \|y\|^2 + \|P y\|^2$, so $S^{-1}$
does not increase norms. The 2-norm is `Matrix.lpOpNorm 2`, and the Frobenius norm is the scoped
norm `Matrix.Norms.Frobenius`. -/
theorem equation_7_2_6 {k : ℕ} (P : Matrix (Fin k) (Fin r) ℂ) :
    lpOpNorm 2 (P * (CFC.sqrt (1 + Pᴴ * P))⁻¹) ≤ lpOpNorm 2 P ∧ lpOpNorm 2 P ≤ ‖P‖ := by
  refine ⟨ContinuousLinearMap.opNorm_le_bound _ (lpOpNorm_nonneg 2 P) fun x => ?_,
    l2_opNorm_le_frobenius_norm P⟩
  obtain ⟨-, -, hSdet⟩ := sqrt_one_add_conjTranspose_mul_self P
  set S := CFC.sqrt (1 + Pᴴ * P) with hS
  set y : EuclideanSpace ℂ (Fin r) := toEuclideanLin S⁻¹ x with hy
  have hx : toEuclideanLin S y = x := by
    rw [hy, ← toEuclideanLin_mul_apply, mul_nonsing_inv _ hSdet, toEuclideanLin_one_apply]
  have happ : lpCLM 2 (P * S⁻¹) x = lpCLM 2 P y := by
    rw [lpCLM_apply, lpCLM_apply, ← mulVec_mulVec]
    rfl
  rw [happ]
  calc ‖lpCLM 2 P y‖ ≤ lpOpNorm 2 P * ‖y‖ := (lpCLM 2 P).le_opNorm y
    _ ≤ lpOpNorm 2 P * ‖x‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (lpOpNorm_nonneg 2 P)
        conv_rhs => rw [← hx]
        exact norm_le_norm_sqrt_apply P y

/-- **Theorem 7.2.4** of [golub2013matrix], the matrix $\tilde Q_1$. Let
$Q \in \mathbb{C}^{n \times n}$ with $n = r + s$, partitioned as $Q = [Q_1\ Q_2]$ with
$Q_1 \in \mathbb{C}^{n \times r}$, and let $P \in \mathbb{C}^{s \times r}$. Then
$$\tilde Q_1 = (Q_1 + Q_2 P)(I + P^H P)^{-1/2} \in \mathbb{C}^{n \times r}.$$

The index type is `Fin r ⊕ Fin s`. The block $Q_1$ is $Q \begin{bmatrix} I \\ 0 \end{bmatrix}$
and $Q_2$ is $Q \begin{bmatrix} 0 \\ I \end{bmatrix}$. The inverse square root is
`(CFC.sqrt (1 + Pᴴ * P))⁻¹`. -/
noncomputable def stewartBasis (Q : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ)
    (P : Matrix (Fin s) (Fin r) ℂ) : Matrix (Fin r ⊕ Fin s) (Fin r) ℂ :=
  (Q * fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (0 : Matrix (Fin s) (Fin r) ℂ) +
    Q * fromRows (0 : Matrix (Fin r) (Fin s) ℂ) (1 : Matrix (Fin s) (Fin s) ℂ) * P) *
      (CFC.sqrt (1 + Pᴴ * P))⁻¹

/-- The matrix $\tilde Q_1$ of `GolubVanLoan.Chapter07.stewartBasis` is $Q \begin{bmatrix} I \\ P
\end{bmatrix} (I + P^H P)^{-1/2}$. -/
theorem stewartBasis_eq (Q : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ)
    (P : Matrix (Fin s) (Fin r) ℂ) :
    stewartBasis Q P = Q * fromRows 1 P * (CFC.sqrt (1 + Pᴴ * P))⁻¹ := by
  rw [stewartBasis, Matrix.mul_assoc Q (fromRows 0 1), ← Matrix.mul_add, fromRows_mul,
    Matrix.zero_mul, Matrix.one_mul]
  congr 2
  ext (i | i) j <;> simp

/-- If $Q$ is unitary, the range of $Q M$ is the image of the range of $M$ under $Q$. -/
private theorem range_unitary_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {Q : Matrix ι ι ℂ} (hQ : Q ∈ unitaryGroup ι ℂ) (M : Matrix ι κ ℂ) :
    LinearMap.range (toEuclideanLin (Q * M)) = (LinearMap.range (toEuclideanLin M)).map
      ((unitaryLinearIsometryEquiv hQ).toLinearEquiv : EuclideanSpace ℂ ι →ₗ[ℂ] _) := by
  rw [← LinearMap.range_comp]
  congr 1
  exact LinearMap.ext fun y => by
    rw [toEuclideanLin_mul_apply, LinearMap.comp_apply]
    rfl

/-- If $Q$ is unitary, the gap between the ranges of $Q \begin{bmatrix} I \\ 0 \end{bmatrix}$ and
$Q \begin{bmatrix} I \\ P \end{bmatrix}$ is at most $\|P\|_2$, which is the estimate of
Corollary 7.2.5 in the coordinates of $Q$. -/
private theorem gap_range_unitary_mul_fromRows_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {Q : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ} (hQ : Q ∈ unitaryGroup (ι ⊕ κ) ℂ)
    (P : Matrix κ ι ℂ) :
    (LinearMap.range (toEuclideanLin (Q * fromRows (1 : Matrix ι ι ℂ) (0 : Matrix κ ι ℂ)))).gap
      (LinearMap.range (toEuclideanLin (Q * fromRows 1 P))) ≤ lpOpNorm 2 P := by
  simp only [range_unitary_mul hQ]
  rw [Submodule.gap_map_linearIsometryEquiv]
  exact gap_range_fromRows_le P

/-- If $Q$ is unitary, $Q^H A Q = B$ and $(B + Q^H E Q) X = X M$, then $(A + E)(Q X) = (Q X) M$. -/
private theorem mul_unitary_mul_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {A E Q B : Matrix ι ι ℂ} (hQ : Q ∈ unitaryGroup ι ℂ) (hT : star Q * A * Q = B)
    {X : Matrix ι κ ℂ} {M : Matrix κ κ ℂ} (hX : (B + star Q * E * Q) * X = X * M) :
    (A + E) * (Q * X) = Q * X * M := by
  have hQQ' : star Q * Q = 1 := mem_unitaryGroup_iff'.1 hQ
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.1 hQ
  have hAE : A + E = Q * (B + star Q * E * Q) * star Q := by
    rw [← hT, ← Matrix.add_mul, ← Matrix.mul_add]
    simp only [← Matrix.mul_assoc]
    rw [hQQ, Matrix.one_mul, Matrix.mul_assoc, hQQ, Matrix.mul_one]
  rw [hAE, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (star Q) Q, hQQ',
    Matrix.one_mul, ← Matrix.mul_assoc, Matrix.mul_assoc Q, hX, ← Matrix.mul_assoc]

open scoped Matrix.Norms.Frobenius

/-- **Theorem 7.2.4** of [golub2013matrix] (Stewart). Let $A, E \in \mathbb{C}^{n \times n}$ with
$n = r + s$, and let $Q \in \mathbb{C}^{n \times n}$ be unitary with
$$Q^H A Q = \begin{bmatrix} T_{11} & T_{12} \\ 0 & T_{22} \end{bmatrix}, \qquad Q^H E Q =
  \begin{bmatrix} E_{11} & E_{12} \\ E_{21} & E_{22} \end{bmatrix},$$
where $T_{11}, E_{11} \in \mathbb{C}^{r \times r}$. Assume that
$\operatorname{sep}(T_{11}, T_{22}) > 0$ and
$$\|E\|_F \left( 1 + \frac{5 \|T_{12}\|_F}{\operatorname{sep}(T_{11}, T_{22})} \right) \le
  \frac{\operatorname{sep}(T_{11}, T_{22})}{5}.$$
Then there is $P \in \mathbb{C}^{s \times r}$ with
$$\|P\|_F \le \frac{4 \|E_{21}\|_F}{\operatorname{sep}(T_{11}, T_{22})}$$
such that the columns of $\tilde Q_1 = (Q_1 + Q_2 P)(I + P^H P)^{-1/2}$ are an orthonormal basis
of a subspace that is invariant for $A + E$.

"Orthonormal" is $\tilde Q_1^H \tilde Q_1 = I$, and "invariant" is
$(A + E) \tilde Q_1 = \tilde Q_1 M$ for some $M \in \mathbb{C}^{r \times r}$. A Schur form is
not needed: $T_{11}$ and $T_{22}$ can be any square blocks. In Lean the index type is
`Fin r ⊕ Fin s`, the lower left block of `star Q * E * Q` is `(star Q * E * Q).toBlocks₂₁`, and
the basis is `GolubVanLoan.Chapter07.stewartBasis Q P`. The proof applies
`Matrix.exists_invariant_graph_of_sep` in the coordinates of the unitary matrix, where the
Frobenius norm is unitarily invariant.

**Generalization.** The diagonal blocks $T_{11}$ and $T_{22}$ can be arbitrary square matrices.
The source introduces the block partition as a Schur decomposition. -/
theorem theorem_7_2_4 {A E Q : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin r ⊕ Fin s) ℂ) {T₁₁ : Matrix (Fin r) (Fin r) ℂ}
    {T₁₂ : Matrix (Fin r) (Fin s) ℂ} {T₂₂ : Matrix (Fin s) (Fin s) ℂ}
    (hT : star Q * A * Q = fromBlocks T₁₁ T₁₂ 0 T₂₂) (hs : 0 < sep T₁₁ T₂₂)
    (hE : ‖E‖ * (1 + 5 * ‖T₁₂‖ / sep T₁₁ T₂₂) ≤ sep T₁₁ T₂₂ / 5) :
    ∃ P : Matrix (Fin s) (Fin r) ℂ,
      ‖P‖ ≤ 4 * ‖(star Q * E * Q).toBlocks₂₁‖ / sep T₁₁ T₂₂ ∧
      (stewartBasis Q P)ᴴ * stewartBasis Q P = 1 ∧
      ∃ M : Matrix (Fin r) (Fin r) ℂ, (A + E) * stewartBasis Q P = stewartBasis Q P * M := by
  have hQQ' : star Q * Q = 1 := mem_unitaryGroup_iff'.1 hQ
  have hnE : ‖star Q * E * Q‖ = ‖E‖ :=
    frobenius_norm_unitary_mul_mul_unitary (Unitary.star_mem hQ) E hQ
  obtain ⟨P, hP, hinv⟩ := exists_invariant_graph_of_sep hs (E := star Q * E * Q) (by rwa [hnE])
  obtain ⟨hSS, hSh, hSdet⟩ := sqrt_one_add_conjTranspose_mul_self P
  set S := CFC.sqrt (1 + Pᴴ * P) with hS
  set F : Matrix (Fin r ⊕ Fin s) (Fin r) ℂ := Q * fromRows 1 P with hFdef
  have hbasis : stewartBasis Q P = F * S⁻¹ := stewartBasis_eq Q P
  refine ⟨P, hP, ?_, ?_⟩
  · have hF : Fᴴ * F = S * S := by
      rw [hFdef, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ Q,
        ← star_eq_conjTranspose, hQQ', Matrix.one_mul,
        conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows,
        conjTranspose_one, Matrix.one_mul, hSS]
    rw [hbasis, conjTranspose_mul, conjTranspose_nonsing_inv, hSh, Matrix.mul_assoc,
      ← Matrix.mul_assoc Fᴴ, hF, Matrix.mul_assoc S, mul_nonsing_inv _ hSdet, Matrix.mul_one,
      nonsing_inv_mul _ hSdet]
  · set M₀ := T₁₁ + (star Q * E * Q).toBlocks₁₁ + (T₁₂ + (star Q * E * Q).toBlocks₁₂) * P
      with hM₀
    refine ⟨S * M₀ * S⁻¹, ?_⟩
    have hAF : (A + E) * F = F * M₀ := mul_unitary_mul_eq hQ hT hinv
    rw [hbasis, ← Matrix.mul_assoc, hAF]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S⁻¹ S, nonsing_inv_mul _ hSdet, Matrix.one_mul]

/-- **Corollary 7.2.5** of [golub2013matrix]. Let $A$, $E$, $Q$, $T_{11}$, $T_{12}$, $T_{22}$ and
$E_{21}$ satisfy the hypotheses of Theorem 7.2.4. Then there is $P \in \mathbb{C}^{s \times r}$
such that the columns of $\tilde Q_1 = (Q_1 + Q_2 P)(I + P^H P)^{-1/2}$ are an orthonormal basis
of a subspace that is invariant for $A + E$, and
$$\operatorname{dist}(\operatorname{ran}(Q_1), \operatorname{ran}(\tilde Q_1)) \le \frac{4
  \|E_{21}\|_F}{\operatorname{sep}(T_{11}, T_{22})}.$$

The distance is the gap `Submodule.gap` of the column spaces. The proof uses
$\operatorname{ran}(\tilde Q_1) = \operatorname{ran}(Q \begin{bmatrix} I \\ P \end{bmatrix})$.
In the coordinates of $Q$ the gap between $\operatorname{ran} \begin{bmatrix} I \\ 0
\end{bmatrix}$ and $\operatorname{ran} \begin{bmatrix} I \\ P \end{bmatrix}$ is at most
$\|P\|_2 \le \|P\|_F$, by `Matrix.gap_range_fromRows_le` and (7.2.6). The route of the source
through $\|Q_2^H \tilde Q_1\|_2$ is not needed.

**Reading.** Same gap bound in arbitrary upper block triangular representations.
-/
theorem corollary_7_2_5 {A E Q : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin r ⊕ Fin s) ℂ) {T₁₁ : Matrix (Fin r) (Fin r) ℂ}
    {T₁₂ : Matrix (Fin r) (Fin s) ℂ} {T₂₂ : Matrix (Fin s) (Fin s) ℂ}
    (hT : star Q * A * Q = fromBlocks T₁₁ T₁₂ 0 T₂₂) (hs : 0 < sep T₁₁ T₂₂)
    (hE : ‖E‖ * (1 + 5 * ‖T₁₂‖ / sep T₁₁ T₂₂) ≤ sep T₁₁ T₂₂ / 5) :
    ∃ P : Matrix (Fin s) (Fin r) ℂ,
      (stewartBasis Q P)ᴴ * stewartBasis Q P = 1 ∧
      (∃ M : Matrix (Fin r) (Fin r) ℂ, (A + E) * stewartBasis Q P = stewartBasis Q P * M) ∧
      (LinearMap.range (toEuclideanLin (Q * fromRows (1 : Matrix (Fin r) (Fin r) ℂ)
          (0 : Matrix (Fin s) (Fin r) ℂ)))).gap
        (LinearMap.range (toEuclideanLin (stewartBasis Q P))) ≤
          4 * ‖(star Q * E * Q).toBlocks₂₁‖ / sep T₁₁ T₂₂ := by
  obtain ⟨P, hP, horth, hinv⟩ := theorem_7_2_4 hQ hT hs hE
  refine ⟨P, horth, hinv, ?_⟩
  obtain ⟨-, -, hSdet⟩ := sqrt_one_add_conjTranspose_mul_self P
  have hrange : LinearMap.range (toEuclideanLin (stewartBasis Q P)) =
      LinearMap.range (toEuclideanLin (Q * fromRows 1 P)) := by
    rw [stewartBasis_eq, toEuclideanLin_mul]
    refine LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 fun y => ?_)
    refine ⟨toEuclideanLin (CFC.sqrt (1 + Pᴴ * P)) y, ?_⟩
    rw [← toEuclideanLin_mul_apply, nonsing_inv_mul _ hSdet, toEuclideanLin_one_apply]
  simp only [hrange]
  exact (gap_range_unitary_mul_fromRows_le hQ P).trans
    ((equation_7_2_6 P).2.trans hP)

/-- If a one-column matrix $w$ satisfies $X w = w M$ with $M \in \mathbb{C}^{1 \times 1}$, then $w$
satisfies $X w = M_{11} w$. -/
private theorem mulVec_eq_smul_of_mul_replicateCol {κ : Type*} [Fintype κ] {X : Matrix κ κ ℂ}
    {w : κ → ℂ} {M : Matrix Unit Unit ℂ} (h : X * replicateCol Unit w = replicateCol Unit w * M) :
    X *ᵥ w = M () () • w := by
  ext i
  have := congrFun (congrFun h i) ()
  simpa [Matrix.mul_apply, replicateCol_apply, mulVec, dotProduct, mul_comm] using this

/-- **Corollary 7.2.6** of [golub2013matrix], the vector $\tilde q_1$. Let
$Q = [q_1 \mid Q_2] \in \mathbb{C}^{n \times n}$ with $n = 1 + s$, and let $p \in \mathbb{C}^s$.
Then
$$\tilde q_1 = \frac{q_1 + Q_2 p}{\sqrt{1 + p^H p}}.$$

The index type is `Unit ⊕ Fin s`, and $q_1 + Q_2 p$ is $Q \begin{bmatrix} 1 \\ p \end{bmatrix}$. -/
noncomputable def stewartVector (Q : Matrix (Unit ⊕ Fin s) (Unit ⊕ Fin s) ℂ) (p : Fin s → ℂ) :
    Unit ⊕ Fin s → ℂ :=
  (((√(1 + ‖WithLp.toLp 2 p‖ ^ 2) : ℝ) : ℂ))⁻¹ • (Q *ᵥ Sum.elim (fun _ => 1) p)

/-- **Corollary 7.2.6** of [golub2013matrix]. Let $A, E \in \mathbb{C}^{n \times n}$ with
$n = 1 + s$, and let $Q = [q_1 \mid Q_2]$ be unitary with
$$Q^H A Q = \begin{bmatrix} \lambda & v^H \\ 0 & T_{22} \end{bmatrix}, \qquad Q^H E Q =
  \begin{bmatrix} \epsilon & \gamma^H \\ \delta & E_{22} \end{bmatrix}.$$
If $\sigma = \sigma_{\min}(T_{22} - \lambda I) > 0$ and
$$\|E\|_F \left( 1 + \frac{5 \|v\|_2}{\sigma} \right) \le \frac{\sigma}{5},$$
then there is $p \in \mathbb{C}^s$ with $\|p\|_2 \le 4 \|\delta\|_2 / \sigma$ such that
$\tilde q_1 = (q_1 + Q_2 p)/\sqrt{1 + p^H p}$ is a unit 2-norm eigenvector of $A + E$. Moreover,
$$\operatorname{dist}(\operatorname{span}\{q_1\}, \operatorname{span}\{\tilde q_1\}) \le \frac{4
  \|\delta\|_2}{\sigma}.$$

Here $\sigma$ is the least column singular value of $T_{22} - \lambda I$, and $\delta$ is the
first column of $Q^H E Q$ below the corner entry. The statement is the case $r = 1$ of Theorem
7.2.4 and Corollary 7.2.5, with $\operatorname{sep}(\lambda, T_{22}) = \sigma$. For $r = 1$ the
inverse square root is the scalar $1/\sqrt{1 + p^H p}$, and a one-dimensional invariant subspace
is spanned by an eigenvector. In Lean the index type is `Unit ⊕ Fin s`, the scalar is `μ`, the
vector is `GolubVanLoan.Chapter07.stewartVector Q p`, and the distance is `Submodule.gap`. The
proof uses `GolubVanLoan.Chapter07.sep_one_eq_sigmaMin` and applies
`Matrix.exists_invariant_graph_of_sep` directly. -/
theorem corollary_7_2_6 {A E Q : Matrix (Unit ⊕ Fin s) (Unit ⊕ Fin s) ℂ}
    (hQ : Q ∈ unitaryGroup (Unit ⊕ Fin s) ℂ) {μ : ℂ} {v : Fin s → ℂ}
    {T₂₂ : Matrix (Fin s) (Fin s) ℂ}
    (hT : star Q * A * Q = fromBlocks (of fun _ _ => μ) (replicateCol Unit v)ᴴ 0 T₂₂)
    (hσ : 0 < ⨅ i, (T₂₂ - μ • 1).colSingularValues i)
    (hE : ‖E‖ * (1 + 5 * ‖WithLp.toLp 2 v‖ / ⨅ i, (T₂₂ - μ • 1).colSingularValues i) ≤
      (⨅ i, (T₂₂ - μ • 1).colSingularValues i) / 5) :
    ∃ p : Fin s → ℂ,
      ‖WithLp.toLp 2 p‖ ≤ 4 * ‖WithLp.toLp 2 fun i => (star Q * E * Q) (Sum.inr i) (Sum.inl ())‖ /
        (⨅ i, (T₂₂ - μ • 1).colSingularValues i) ∧
      ‖WithLp.toLp 2 (stewartVector Q p)‖ = 1 ∧
      (∃ μ' : ℂ, (A + E) *ᵥ stewartVector Q p = μ' • stewartVector Q p) ∧
      (ℂ ∙ WithLp.toLp 2 fun i => Q i (Sum.inl ())).gap (ℂ ∙ WithLp.toLp 2 (stewartVector Q p)) ≤
        4 * ‖WithLp.toLp 2 fun i => (star Q * E * Q) (Sum.inr i) (Sum.inl ())‖ /
          (⨅ i, (T₂₂ - μ • 1).colSingularValues i) := by
  set σ := ⨅ i, (T₂₂ - μ • 1).colSingularValues i with hσdef
  set δ : Fin s → ℂ := fun i => (star Q * E * Q) (Sum.inr i) (Sum.inl ()) with hδdef
  have hsep : sep (of fun _ _ => μ : Matrix Unit Unit ℂ) T₂₂ = σ := (sep_one_eq_sigmaMin μ T₂₂).1
  have hnE : ‖star Q * E * Q‖ = ‖E‖ :=
    frobenius_norm_unitary_mul_mul_unitary (Unitary.star_mem hQ) E hQ
  have hv : ‖(replicateCol Unit v)ᴴ‖ = ‖WithLp.toLp 2 v‖ := by
    rw [frobenius_norm_conjTranspose, frobenius_norm_replicateCol]
  obtain ⟨P, hP, hinv⟩ := exists_invariant_graph_of_sep (T₁₁ := of fun _ _ => μ)
    (T₁₂ := (replicateCol Unit v)ᴴ) (T₂₂ := T₂₂) (E := star Q * E * Q) (by rw [hsep]; exact hσ)
    (by rw [hnE, hv, hsep]; exact hE)
  set p : Fin s → ℂ := fun i => P i () with hpdef
  have hPp : P = replicateCol Unit p := by
    ext i j
    rfl
  have hδ : (star Q * E * Q).toBlocks₂₁ = replicateCol Unit δ := by
    ext i j
    rfl
  have hpb : ‖WithLp.toLp 2 p‖ ≤ 4 * ‖WithLp.toLp 2 δ‖ / σ := by
    rw [← frobenius_norm_replicateCol (ι := Unit), ← hPp, ← frobenius_norm_replicateCol (ι := Unit),
      ← hδ, ← hsep]
    exact hP
  set w : Unit ⊕ Fin s → ℂ := Q *ᵥ Sum.elim (fun _ => 1) p with hwdef
  have hQw : Q * fromRows (1 : Matrix Unit Unit ℂ) P = replicateCol Unit w := by
    ext i u
    rw [replicateCol_apply, hwdef, mulVec, dotProduct, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases j with j | j
    · simp
    · simp [hpdef]
  have hq₁ : Q * fromRows (1 : Matrix Unit Unit ℂ) (0 : Matrix (Fin s) Unit ℂ) =
      replicateCol Unit fun i => Q i (Sum.inl ()) := by
    ext i u
    rw [replicateCol_apply, Matrix.mul_apply, Fintype.sum_sum_type]
    simp
  -- the norm of `w`
  have hwn : ‖WithLp.toLp 2 w‖ = √(1 + ‖WithLp.toLp 2 p‖ ^ 2) := by
    have h1 : WithLp.toLp 2 w = unitaryLinearIsometryEquiv hQ
        (WithLp.toLp 2 (Sum.elim (fun _ => 1) p)) := by
      rw [unitaryLinearIsometryEquiv_apply, toEuclideanLin_apply]
    rw [h1, LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq, Fintype.sum_sum_type,
      EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
    simp
  have hc : 0 < √(1 + ‖WithLp.toLp 2 p‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hq : stewartVector Q p = (((√(1 + ‖WithLp.toLp 2 p‖ ^ 2) : ℝ) : ℂ))⁻¹ • w := rfl
  refine ⟨p, hpb, ?_, ?_, ?_⟩
  · rw [hq, WithLp.toLp_smul, norm_smul, hwn, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc, inv_mul_cancel₀ hc.ne']
  · -- the eigenvector
    have hAQ := mul_unitary_mul_eq hQ hT hinv
    rw [hQw] at hAQ
    have hw := mulVec_eq_smul_of_mul_replicateCol hAQ
    exact ⟨_, by rw [hq, mulVec_smul, hw, smul_comm]⟩
  · -- the distance
    have hspan : (ℂ ∙ WithLp.toLp 2 (stewartVector Q p)) =
        LinearMap.range (toEuclideanLin (Q * fromRows (1 : Matrix Unit Unit ℂ) P)) := by
      rw [hQw, range_toEuclideanLin_replicateCol, hq, WithLp.toLp_smul,
        Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero (by exact_mod_cast hc.ne')))]
    have hspan₁ : (ℂ ∙ WithLp.toLp 2 fun i => Q i (Sum.inl ())) =
        LinearMap.range (toEuclideanLin (Q * fromRows (1 : Matrix Unit Unit ℂ)
          (0 : Matrix (Fin s) Unit ℂ))) := by
      rw [hq₁, range_toEuclideanLin_replicateCol]
    simp only [hspan, hspan₁]
    refine (gap_range_unitary_mul_fromRows_le hQ P).trans ((l2_opNorm_le_frobenius_norm P).trans ?_)
    rw [hPp, frobenius_norm_replicateCol]
    exact hpb

end Stewart

end GolubVanLoan.Chapter07
