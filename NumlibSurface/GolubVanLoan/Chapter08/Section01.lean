/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.SingularValues
import Numlib.Analysis.Matrix.SpectralNorm
import Mathlib.Algebra.Order.Star.Real
import Numlib.Eigen.DivideConquer
import Numlib.Eigen.Inertia
import Numlib.Eigen.InvariantSubspace
import Numlib.Eigen.MinMax
import Numlib.Eigen.Perturbation
import Numlib.Eigen.RayleighRitz
import Numlib.LinearAlgebra.Matrix.SVD
import Numlib.LinearAlgebra.Matrix.Polar
import Numlib.LinearAlgebra.Matrix.Schur
import Numlib.LinearAlgebra.Matrix.Symmetric
import Numlib.LinearAlgebra.Matrix.Sylvester
import NumlibSurface.GolubVanLoan.Chapter02.Section05
import NumlibSurface.GolubVanLoan.Chapter07.Section02

/-!
# Golub and Van Loan, Section 8.1: Properties and decompositions of symmetric matrices

This module formalizes §8.1 of [golub2013matrix], the basic theory of the symmetric eigenvalue
problem. For a symmetric $A \in \mathbb{R}^{n \times n}$ the eigenvalues are real, and the source
writes them in decreasing order as $\lambda_1(A) \ge \lambda_2(A) \ge \dots \ge \lambda_n(A)$. The
module proves the symmetric Schur decomposition $Q^T A Q = \operatorname{diag}(\lambda_1, \dots,
\lambda_n)$ with $Q$ orthogonal, the Courant–Fischer characterization of $\lambda_k(A)$ by the
Rayleigh quotient $r(x) = x^T A x / x^T x$, and the perturbation results for eigenvalues: Gershgorin
intervals, the Wielandt–Hoffman theorem, Weyl's inequality, interlacing for leading principal
submatrices and for rank-one updates. It then treats invariant subspaces and their perturbation
through the separation $\operatorname{sep}(D_1, D_2)$ of (8.1.2), approximate invariant subspaces
and Ritz pairs (§8.1.4), and Sylvester's law of inertia (§8.1.5).

The proofs specialize the backbone modules `Numlib.Eigen.MinMax`, `Numlib.Eigen.Perturbation`,
`Numlib.Eigen.RayleighRitz`, `Numlib.Eigen.InvariantSubspace`, `Numlib.Eigen.Inertia`,
`Numlib.LinearAlgebra.Matrix.Schur`, `Numlib.LinearAlgebra.Matrix.Sylvester`,
`Numlib.LinearAlgebra.Matrix.Polar`, `Numlib.LinearAlgebra.Matrix.SVD`,
`Numlib.Analysis.Matrix.SingularValues` and `Numlib.Analysis.Matrix.SpectralNorm`. Theorem 8.1.3
uses Theorem 7.2.1 (`GolubVanLoan.Chapter07.theorem_7_2_1`), and Corollary 8.1.11 and Theorem 8.1.12
use the distance between subspaces `GolubVanLoan.Chapter02.subspaceDist` of §2.5.

## Main definitions

* §8.1.1, `GolubVanLoan.Chapter08.symmEigenvalue`: the eigenvalues $\lambda_k(A)$ of a symmetric
  matrix in decreasing order.
* §8.1.1, `GolubVanLoan.Chapter08.rayleighQuotient`: the Rayleigh quotient $r(x) = x^T A x / x^T x$.
* (8.1.2), `GolubVanLoan.Chapter08.sepSymm`: the separation $\min |\lambda - \mu|$ over
  $\lambda \in \lambda(B)$ and $\mu \in \lambda(C)$.
* §8.1.5, `GolubVanLoan.Chapter08.inertia`: the inertia $(m, z, p)$ of a symmetric matrix.

## Main results

* Theorem 8.1.1, `GolubVanLoan.Chapter08.theorem_8_1_1`: the symmetric Schur decomposition $Q^T A
  Q = \operatorname{diag}(\lambda_1(A), \dots, \lambda_n(A))$.
* §8.1.1, `GolubVanLoan.Chapter08.l2_opNorm_eq_max_abs_symmEigenvalue`: the singular values of a
  symmetric $A$ are the $|\lambda_k(A)|$, and $\|A\|_2 = \max\{|\lambda_1(A)|, |\lambda_n(A)|\}$.
* Theorem 8.1.2, `GolubVanLoan.Chapter08.theorem_8_1_2` and
  `GolubVanLoan.Chapter08.theorem_8_1_2_minmax`: the Courant–Fischer max–min and min–max
  characterizations of $\lambda_k(A)$.
* §8.1.1, `GolubVanLoan.Chapter08.symmEigenvalue_pos_of_posDef`: a symmetric positive definite
  matrix has positive eigenvalues.
* Theorem 8.1.3, `GolubVanLoan.Chapter08.theorem_8_1_3`: the eigenvalues lie in the union of the
  Gershgorin intervals of $Q^T A Q$.
* Theorem 8.1.4, `GolubVanLoan.Chapter08.theorem_8_1_4`: the Wielandt–Hoffman bound $\sum_k
  (\lambda_k(A + E) - \lambda_k(A))^2 \le \|E\|_F^2$.
* Theorem 8.1.5, `GolubVanLoan.Chapter08.theorem_8_1_5`: $\lambda_k(A) + \lambda_n(E) \le
  \lambda_k(A + E) \le \lambda_k(A) + \lambda_1(E)$.
* Corollary 8.1.6, `GolubVanLoan.Chapter08.corollary_8_1_6`: Weyl's inequality
  $|\lambda_k(A + E) - \lambda_k(A)| \le \|E\|_2$.
* Theorem 8.1.7, `GolubVanLoan.Chapter08.theorem_8_1_7`: the eigenvalues of $A(1{:}r, 1{:}r)$
  interlace those of $A(1{:}r{+}1, 1{:}r{+}1)$.
* Theorem 8.1.8, `GolubVanLoan.Chapter08.theorem_8_1_8` and
  `GolubVanLoan.Chapter08.theorem_8_1_8_b`: interlacing for the rank-one update $A + \tau c c^T$,
  and the shifts $\lambda_i(A + \tau c c^T) = \lambda_i(A) + m_i \tau$ with $m_i \ge 0$ and
  $\sum m_i = 1$.
* Theorem 8.1.9, `GolubVanLoan.Chapter08.theorem_8_1_9`: an invariant subspace block-diagonalizes
  $A$ and splits its spectrum.
* (8.1.2), `GolubVanLoan.Chapter08.sepSymm_eq_sep`: for symmetric matrices the separation of (7.2.5)
  is the eigenvalue gap.
* Theorem 8.1.10, `GolubVanLoan.Chapter08.theorem_8_1_10`: a perturbed invariant subspace
  $\operatorname{ran}((Q_1 + Q_2 P)(I + P^T P)^{-1/2})$ of $A + E$ with $\|P\|_F \le
  (4/\operatorname{sep}(D_1, D_2)) \|E_{21}\|_F$.
* (8.1.3), `GolubVanLoan.Chapter08.equation_8_1_3`: $\|P (I + P^T P)^{-1/2}\|_2 \le \|P\|_2 \le
  \|P\|_F$.
* Corollary 8.1.11, `GolubVanLoan.Chapter08.corollary_8_1_11`: the distance between the unperturbed
  and the perturbed invariant subspace is at most $(4/\operatorname{sep}(D_1, D_2)) \|E_{21}\|_F$.
* Theorem 8.1.12, `GolubVanLoan.Chapter08.theorem_8_1_12`: the perturbation of a single eigenvector.
* Theorem 8.1.13, `GolubVanLoan.Chapter08.theorem_8_1_13` and
  `GolubVanLoan.Chapter08.theorem_8_1_13_weak`: the eigenvalues of $S$ are within
  $\sqrt{2}\|A Q_1 - Q_1 S\|_2$ of distinct eigenvalues of $A$, and each is within
  $\|A Q_1 - Q_1 S\|_2$ of some eigenvalue of $A$.
* Theorem 8.1.14, `GolubVanLoan.Chapter08.theorem_8_1_14`: $S = Q_1^T A Q_1$ minimizes
  $\|A Q_1 - Q_1 S\|_F$.
* Theorem 8.1.15, `GolubVanLoan.Chapter08.theorem_8_1_15`: the residual of a Ritz pair is bounded by
  $\|(I - Q_1 Q_1^T) A Q_1\|_2$.
* §8.1.4, `GolubVanLoan.Chapter08.ritzPair_isRitzPair`: the Ritz pairs of $A$ on
  $\operatorname{ran}(Q_1)$ are the pairs $(\theta_k, Q_1 z_k)$ from the Schur decomposition of
  $Q_1^T A Q_1$.
* (8.1.5), (8.1.6) and (8.1.7), `GolubVanLoan.Chapter08.equation_8_1_5`,
  `GolubVanLoan.Chapter08.equation_8_1_6` and `GolubVanLoan.Chapter08.equation_8_1_7`: the three
  estimates in the proof of Theorem 8.1.16.
* Theorem 8.1.16, `GolubVanLoan.Chapter08.theorem_8_1_16`: the eigenvalue bound of Theorem 8.1.13
  for a basis $X_1$ that is only nearly orthonormal.
* Theorem 8.1.17, `GolubVanLoan.Chapter08.theorem_8_1_17`: Sylvester's law of inertia.

## Proof outline

Corollary 8.1.11 and Theorem 8.1.12 bound the distance between the two subspaces in the coordinates
of $Q$, where the subspaces are the ranges of $\begin{bmatrix} I \\ 0 \end{bmatrix}$ and
$\begin{bmatrix} I \\ P \end{bmatrix}$, by `Matrix.gap_range_fromRows_le`. The route of the source
through $\operatorname{dist} = \|Q_2^T \hat Q_1\|_2$ is not used. The proof of Theorem 8.1.16 in the
source asserts $1 - \sigma_r^2 = \tau$, which is not true in general; the conclusion of (8.1.7) is
true and is proved through the polar factor of $X_1$. The proofs do not use Problem P8.1.5.

## Conventions

* The eigenvalue $\lambda_k(A)$ of a symmetric $A$ is `GolubVanLoan.Chapter08.symmEigenvalue hA ⟨k -
  1, _⟩` for `hA : A.IsSymm`. It is the backbone's `Matrix.IsHermitian.sortedEigenvalues`, a
  reindexing to `Fin n` of Mathlib's sorted `Matrix.IsHermitian.eigenvalues₀`. Over $\mathbb{R}$,
  `A.IsSymm` and `A.IsHermitian` are the same condition (`Matrix.isHermitian_iff_isSymm`).
* Orthogonal matrices are the elements of `Matrix.orthogonalGroup (Fin n) ℝ`. The norm $\|\cdot\|_2$
  is `Matrix.lpOpNorm 2`, and $\|\cdot\|_F$ is the norm of the scoped instance
  `Matrix.Norms.Frobenius`.
* A partition $Q = [Q_1 \; Q_2]$ is `Matrix.fromCols Q₁ Q₂`, and a block matrix $\begin{bmatrix} D_1
  & 0 \\ 0 & D_2 \end{bmatrix}$ is `Matrix.fromBlocks D₁ 0 0 D₂`, both indexed by `Fin r ⊕ Fin s`.

## Deviations from the source

* **§8.1.1, the Rayleigh quotient and Theorem 8.1.2** (reading).
  `GolubVanLoan.Chapter08.rayleighQuotient` has a total value at the zero vector, and
  `GolubVanLoan.Chapter08.theorem_8_1_2_minmax` gives the dual of the source’s max–min
  statement.
* **Equation (8.1.2) and Problem P8.1.9** (correction). `GolubVanLoan.Chapter08.sepSymm_eq_sep`
  compares spectral separation to the Sylvester-operator minimum on the Frobenius unit sphere.
  The printed unconstrained minimum includes $X=0$.
* **Theorems 8.1.13–8.1.14** (reading). `GolubVanLoan.Chapter08.theorem_8_1_13_weak` bounds one
  projected eigenvalue with factor one. `GolubVanLoan.Chapter08.theorem_8_1_14` gives the
  Frobenius residual minimum for arbitrary real $A$.
* **Equations (8.1.5)–(8.1.7)** (correction). The intermediate norms use $Q-X_1$ and
  $X_1^TX_1-I_r$. `GolubVanLoan.Chapter08.equation_8_1_7` uses the full singular-value deviation
  from one, correcting the printed equality with the smallest singular value alone.
* **Theorem 8.1.3** (generalization). The source assumes that $A$ is symmetric. The inclusion holds
  for the real eigenvalues of every real $A$. See `GolubVanLoan.Chapter08.theorem_8_1_3`.
* **Theorem 8.1.7** (generalization). The source assumes that $A$ is symmetric. Only the leading
  principal submatrices $A(1{:}r, 1{:}r)$ and $A(1{:}r{+}1, 1{:}r{+}1)$ need to be symmetric. See
  `GolubVanLoan.Chapter08.theorem_8_1_7`.
* **Theorem 8.1.8** (generalization). The source normalizes $\|c\|_2 = 1$. The interlacing holds for
  every $c$. See `GolubVanLoan.Chapter08.theorem_8_1_8`.
* **Theorem 8.1.10 and Corollary 8.1.11** (generalization). The theorems do not need $E$ to be
  symmetric, and they hold for every symmetric square root of $I + P^T P$. See
  `GolubVanLoan.Chapter08.theorem_8_1_10`.
* **Theorem 8.1.12** (generalization). The source assumes that $A + E$ is symmetric. Only $A$ needs
  to be symmetric. See `GolubVanLoan.Chapter08.theorem_8_1_12`.
* **Theorem 8.1.13** (reading). The source says that there exist
  $\mu_1, \dots, \mu_r \in \lambda(A)$. The theorem gives $\mu_k = \lambda_{\sigma(k)}(A)$ for an
  injective $\sigma$, as the proof of the source produces them. See
  `GolubVanLoan.Chapter08.theorem_8_1_13`.
* **Theorem 8.1.15** (generalization). The source takes $Q_1$ with orthonormal columns. The identity
  and the bound hold for every $Q_1$. See `GolubVanLoan.Chapter08.theorem_8_1_15`.
* **Equation (8.1.5)** (generalization). The source takes $Q$ with orthonormal columns. The bound
  holds for every $Q$. See `GolubVanLoan.Chapter08.equation_8_1_5`.
* **Theorem 8.1.16** (reading). As in Theorem 8.1.13, the eigenvalues $\mu_k$ are
  $\lambda_{\sigma(k)}(A)$ for an injective $\sigma$. See `GolubVanLoan.Chapter08.theorem_8_1_16`.
-/

open Matrix

namespace GolubVanLoan.Chapter08

variable {n : ℕ}

/-! ### Eigenvalue and eigenvector properties (§8.1.1) -/

/-- **Section 8.1.1** of [golub2013matrix], the eigenvalues $\lambda_k(A)$. For a symmetric
$A \in \mathbb{R}^{n \times n}$, `symmEigenvalue hA` lists the eigenvalues of $A$, counted with
multiplicity, in decreasing order: $\lambda_1(A) \ge \lambda_2(A) \ge \dots \ge \lambda_n(A)$.

The index is 0-based: $\lambda_k(A)$ is `symmEigenvalue hA ⟨k - 1, _⟩`. The definition is
`Matrix.IsHermitian.sortedEigenvalues` for the Hermitian matrix that
`Matrix.isHermitian_iff_isSymm` gives. -/
noncomputable def symmEigenvalue {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (k : Fin n) : ℝ :=
  (isHermitian_iff_isSymm.2 hA).sortedEigenvalues k

/-- For every proof `hH` that $A$ is Hermitian, `GolubVanLoan.Chapter08.symmEigenvalue hA` is
`hH.sortedEigenvalues`. -/
theorem symmEigenvalue_eq_sortedEigenvalues {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hH : A.IsHermitian) : symmEigenvalue hA = hH.sortedEigenvalues :=
  rfl

/-- The eigenvalues are in decreasing order: $\lambda_1(A) \ge \lambda_2(A) \ge \dots \ge
\lambda_n(A)$. -/
theorem antitone_symmEigenvalue {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    Antitone (symmEigenvalue hA) :=
  (isHermitian_iff_isSymm.2 hA).sortedEigenvalues_antitone

/-- The roots of the characteristic polynomial of a symmetric $A$, counted with multiplicity, are
$\lambda_1(A), \dots, \lambda_n(A)$. -/
theorem roots_charpoly_eq_symmEigenvalue {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    A.charpoly.roots = Multiset.map (symmEigenvalue hA) Finset.univ.val := by
  rw [(isHermitian_iff_isSymm.2 hA).roots_charpoly_eq_sortedEigenvalues]
  congr 1

/-- The real spectrum of a symmetric $A$ is the set $\{\lambda_1(A), \dots, \lambda_n(A)\}$. -/
theorem spectrum_eq_range_symmEigenvalue {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    spectrum ℝ A = Set.range (symmEigenvalue hA) := by
  rw [(isHermitian_iff_isSymm.2 hA).spectrum_real_eq_range_eigenvalues]
  ext x
  simp only [Set.mem_range, IsHermitian.eigenvalues, symmEigenvalue,
    IsHermitian.sortedEigenvalues_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.cast (Fintype.card_fin n) ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i),
      by simp⟩
  · rintro ⟨k, rfl⟩
    exact ⟨Fintype.equivOfCardEq (Fintype.card_fin _) (Fin.cast (Fintype.card_fin n).symm k),
      by simp⟩

/-- Each $\lambda_k(A)$ is an eigenvalue of the symmetric matrix $A$. -/
theorem symmEigenvalue_mem_spectrum {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (k : Fin n) :
    symmEigenvalue hA k ∈ spectrum ℝ A := by
  rw [spectrum_eq_range_symmEigenvalue hA]
  exact ⟨k, rfl⟩

/-- The sorted eigenvalues of a symmetric operator do not depend on the name of the dimension. -/
private theorem eigenvalues_cast {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {a b : ℕ}
    (ha : Module.finrank ℝ E = a) (hb : Module.finrank ℝ E = b) (h : a = b) (i : Fin a) :
    hT.eigenvalues ha i = hT.eigenvalues hb (Fin.cast h i) := by
  subst h
  rfl

/-- $\lambda_k(A)$ is the $k$-th sorted eigenvalue of every symmetric operator that equals
`Matrix.toEuclideanLin A`. -/
private theorem symmEigenvalue_eq_eigenvalues {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)} (hT : T.IsSymmetric)
    (h : toEuclideanLin A = T) (hm : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n)
    (k : Fin n) : symmEigenvalue hA k = hT.eigenvalues hm k := by
  subst h
  change hT.eigenvalues finrank_euclideanSpace (Fin.cast (Fintype.card_fin n).symm k) = _
  rw [eigenvalues_cast hT finrank_euclideanSpace hm (Fintype.card_fin n)]
  rfl

/-- The operator `Matrix.toEuclideanLin A` of a symmetric matrix $A$ is symmetric. -/
private theorem isSymmetric_toEuclideanLin {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    (toEuclideanLin A).IsSymmetric :=
  isSymmetric_toEuclideanLin_iff.mpr (isHermitian_iff_isSymm.2 hA)

/-- **Section 8.1.1** of [golub2013matrix], the Rayleigh quotient. For
$A \in \mathbb{R}^{n \times n}$ and $x \in \mathbb{R}^n$, the **Rayleigh quotient** is
$$r(x) = \frac{x^T A x}{x^T x}.$$

The same quotient is (8.2.6). At $x = 0$ the value is $0$, because division by zero gives $0$ in
Lean.

**Reading.** The source uses the quotient for nonzero vectors. The Lean definition is total,
with value zero at the zero vector. -/
noncomputable def rayleighQuotient (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  (x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ x)

/-- The Rayleigh quotient $r(x)$ of $A$ is Mathlib's `LinearMap.rayleighQuotient` of the operator
`Matrix.toEuclideanLin A` at $x$, that is $\langle Ax, x \rangle / \|x\|^2$. -/
theorem rayleighQuotient_eq (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    rayleighQuotient A x = (toEuclideanLin A).rayleighQuotient (WithLp.toLp 2 x) := by
  rw [rayleighQuotient, LinearMap.rayleighQuotient, ← real_inner_self_eq_norm_sq,
    toEuclideanLin_toLp]
  simp only [EuclideanSpace.inner_toLp_toLp, RCLike.re_to_real, star_trivial]

/-- **Theorem 8.1.1** of [golub2013matrix] (symmetric Schur decomposition). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric. Then there is an orthogonal
$Q \in \mathbb{R}^{n \times n}$ with
$$Q^T A Q = \Lambda = \operatorname{diag}(\lambda_1(A), \dots, \lambda_n(A)),$$
and $A Q(:, k) = \lambda_k(A) Q(:, k)$ for $k = 1, \dots, n$. -/
theorem theorem_8_1_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    ∃ Q ∈ orthogonalGroup (Fin n) ℝ, Qᵀ * A * Q = diagonal (symmEigenvalue hA) ∧
      ∀ k, A *ᵥ Q.col k = symmEigenvalue hA k • Q.col k := by
  obtain ⟨U, hU, h1, h2⟩ :=
    (isHermitian_iff_isSymm.2 hA).exists_unitary_conj_eq_diagonal_sortedEigenvalues
  refine ⟨U, hU, ?_, fun k => ?_⟩
  · rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h1
    convert h1 using 2
    funext k
    simp [symmEigenvalue]
  · convert h2 k using 2
    simp [symmEigenvalue]

/-- **Section 8.1.1** of [golub2013matrix], the remark after Theorem 8.1.1. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric with $n \ge 1$. Then the singular values of $A$ are
$|\lambda_1(A)|, \dots, |\lambda_n(A)|$ in some order, and
$$\|A\|_2 = \max\{|\lambda_1(A)|, |\lambda_n(A)|\}.$$

The singular values are the column-indexed `Matrix.colSingularValues`, and "in some order" is a
permutation $e$ of the indices with `A.colSingularValues (e k)` $= |\lambda_k(A)|$. -/
theorem l2_opNorm_eq_max_abs_symmEigenvalue {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hn : 0 < n) :
    (∃ e : Fin n ≃ Fin n, ∀ k, A.colSingularValues (e k) = |symmEigenvalue hA k|) ∧
      lpOpNorm 2 A = max |symmEigenvalue hA ⟨0, hn⟩| |symmEigenvalue hA ⟨n - 1, by omega⟩| := by
  have hH := isHermitian_iff_isSymm.2 hA
  refine ⟨?_, ?_⟩
  · obtain ⟨e, he⟩ := hH.exists_equiv_colSingularValues_eq_abs_eigenvalues
    refine ⟨((finCongr (Fintype.card_fin n).symm).trans
      (Fintype.equivOfCardEq (Fintype.card_fin _))).trans e, fun k => ?_⟩
    rw [Equiv.trans_apply, he]
    simp [IsHermitian.eigenvalues, symmEigenvalue, IsHermitian.sortedEigenvalues_apply]
  · set M := max |symmEigenvalue hA ⟨0, hn⟩| |symmEigenvalue hA ⟨n - 1, by omega⟩|
    have hbound : ∀ k, |symmEigenvalue hA k| ≤ M := fun k => by
      have h0 := antitone_symmEigenvalue hA
        (show (⟨0, hn⟩ : Fin n) ≤ k from Fin.le_def.2 (Nat.zero_le _))
      have h1 := antitone_symmEigenvalue hA
        (show k ≤ (⟨n - 1, by omega⟩ : Fin n) from Fin.le_def.2 (by simp; omega))
      exact (abs_le_max_abs_abs h1 h0).trans_eq (max_comm _ _)
    have hspec : ∀ μ : ℝ, Module.End.HasEigenvalue (toEuclideanLin A) μ ↔
        μ ∈ spectrum ℝ A := fun μ => by
      rw [Module.End.hasEigenvalue_iff_mem_spectrum]
      exact Iff.of_eq (congrArg (μ ∈ ·) (spectrum_toLpLin (A := A) 2))
    rw [lpOpNorm_two]
    refine hH.l2_opNorm_eq (fun μ hμ => ?_) ?_
    · obtain ⟨k, hk⟩ := (spectrum_eq_range_symmEigenvalue hA ▸ (hspec μ).1 hμ :
        μ ∈ Set.range (symmEigenvalue hA))
      simpa [← hk] using hbound k
    · rcases le_total |symmEigenvalue hA ⟨n - 1, by omega⟩| |symmEigenvalue hA ⟨0, hn⟩| with h | h
      · exact ⟨_, (hspec _).2 (symmEigenvalue_mem_spectrum hA ⟨0, hn⟩), by simp [M, h]⟩
      · exact ⟨_, (hspec _).2 (symmEigenvalue_mem_spectrum hA ⟨n - 1, by omega⟩), by simp [M, h]⟩

/-- **Theorem 8.1.2** of [golub2013matrix] (Courant–Fischer minimax theorem), max–min form. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric and $1 \le k \le n$. Then
$$\lambda_k(A) = \max_{\dim(S) = k} \; \min_{0 \neq y \in S} \frac{y^T A y}{y^T y},$$
where $S$ ranges over the subspaces of $\mathbb{R}^n$, and the maximum and every minimum are
attained.

The index `k : Fin n` is 0-based, so the subspaces have dimension `k + 1`. The statement says
that $\lambda_k(A)$ is the greatest element (`IsGreatest`) of the set of the least values
(`IsLeast`) of the Rayleigh quotient on $S \setminus \{0\}$. -/
theorem theorem_8_1_2 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (k : Fin n) :
    IsGreatest {c | ∃ S : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ S = k + 1 ∧
      IsLeast (rayleighQuotient A '' {y | y ∈ S ∧ y ≠ 0}) c} (symmEigenvalue hA k) := by
  have hT := isSymmetric_toEuclideanLin hA
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hlam : symmEigenvalue hA k = hT.eigenvalues hn k :=
    symmEigenvalue_eq_eigenvalues hA hT rfl hn k
  set e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  refine ⟨⟨(hT.eigenvectorSpan hn (Finset.Iic k)).map e.toLinearMap, ?_, ?_, ?_⟩, ?_⟩
  · rw [LinearEquiv.finrank_map_eq, hT.finrank_eigenvectorSpan hn, Fin.card_Iic]
  · refine ⟨e (hT.eigenvectorBasis hn k), ⟨Submodule.mem_map_of_mem
      (hT.eigenvectorBasis_mem_eigenvectorSpan hn (Finset.mem_Iic.mpr le_rfl)), ?_⟩, ?_⟩
    · simpa using hT.eigenvectorBasis_ne_zero hn k
    · rw [hlam, rayleighQuotient_eq, ← hT.rayleighQuotient_eigenvectorBasis hn k]
      rfl
  · rintro _ ⟨y, ⟨hyS, hy0⟩, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hyS
    rw [hlam, rayleighQuotient_eq]
    have hx0 : x ≠ 0 := fun h0 => hy0 (by rw [h0, map_zero])
    exact hT.le_rayleighQuotient_of_mem_eigenvectorSpan_Iic hn k hx hx0
  · rintro c ⟨S, hS, hc⟩
    rw [hlam]
    refine (hT.isGreatest_eigenvalues hn k).2 ⟨S.map e.symm.toLinearMap, ?_, fun x hx hx0 => ?_⟩
    · rw [LinearEquiv.finrank_map_eq, hS]
    · obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      have := hc.2 ⟨y, ⟨hy, fun h0 => hx0 (by rw [h0, map_zero])⟩, rfl⟩
      rwa [rayleighQuotient_eq] at this

/-- **Theorem 8.1.2** of [golub2013matrix] (Courant–Fischer minimax theorem), min–max form. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric and $1 \le k \le n$. Then
$$\lambda_k(A) = \min_{\dim(S) = n - k + 1} \; \max_{0 \neq y \in S} r(y),$$
where $S$ ranges over the subspaces of $\mathbb{R}^n$, $r$ is the Rayleigh quotient, and the
minimum and every maximum are attained.

The index `k : Fin n` is 0-based, so the subspaces have dimension `n - k`.

**Reading.** The source states the maximum of subspace minima. This declaration states the dual
minimum of subspace maxima. -/
theorem theorem_8_1_2_minmax {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (k : Fin n) :
    IsLeast {c | ∃ S : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ S = n - k ∧
      IsGreatest (rayleighQuotient A '' {y | y ∈ S ∧ y ≠ 0}) c} (symmEigenvalue hA k) := by
  have hT := isSymmetric_toEuclideanLin hA
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hlam : symmEigenvalue hA k = hT.eigenvalues hn k :=
    symmEigenvalue_eq_eigenvalues hA hT rfl hn k
  set e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  refine ⟨⟨(hT.eigenvectorSpan hn (Finset.Ici k)).map e.toLinearMap, ?_, ?_, ?_⟩, ?_⟩
  · rw [LinearEquiv.finrank_map_eq, hT.finrank_eigenvectorSpan hn, Fin.card_Ici]
  · refine ⟨e (hT.eigenvectorBasis hn k), ⟨Submodule.mem_map_of_mem
      (hT.eigenvectorBasis_mem_eigenvectorSpan hn (Finset.mem_Ici.mpr le_rfl)), ?_⟩, ?_⟩
    · simpa using hT.eigenvectorBasis_ne_zero hn k
    · rw [hlam, rayleighQuotient_eq, ← hT.rayleighQuotient_eigenvectorBasis hn k]
      rfl
  · rintro _ ⟨y, ⟨hyS, hy0⟩, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hyS
    rw [hlam, rayleighQuotient_eq]
    have hx0 : x ≠ 0 := fun h0 => hy0 (by rw [h0, map_zero])
    exact hT.rayleighQuotient_le_of_mem_eigenvectorSpan_Ici hn k hx hx0
  · rintro c ⟨S, hS, hc⟩
    rw [hlam]
    refine (hT.isLeast_eigenvalues hn k).2 ⟨S.map e.symm.toLinearMap, ?_, fun x hx hx0 => ?_⟩
    · rw [LinearEquiv.finrank_map_eq, hS]
    · obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      have := hc.2 ⟨y, ⟨hy, fun h0 => hx0 (by rw [h0, map_zero])⟩, rfl⟩
      rwa [rayleighQuotient_eq] at this

/-- **Section 8.1.1** of [golub2013matrix], last sentence. If $A \in \mathbb{R}^{n \times n}$ is
symmetric positive definite, then $\lambda_k(A) > 0$ for every $k$. -/
theorem symmEigenvalue_pos_of_posDef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hP : A.PosDef) (k : Fin n) : 0 < symmEigenvalue hA k := by
  obtain ⟨i, hi⟩ : symmEigenvalue hA k ∈ Set.range hP.isHermitian.eigenvalues := by
    rw [← hP.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact symmEigenvalue_mem_spectrum hA k
  rw [← hi]
  exact hP.eigenvalues_pos i

/-- **Theorem 8.1.3** of [golub2013matrix] (Gershgorin). Let $A, Q, F \in \mathbb{R}^{n \times n}$
and $d \in \mathbb{R}^n$, with $Q$ orthogonal, $Q^T A Q = \operatorname{diag}(d) + F$ and
$f_{ii} = 0$ for all $i$. Then every real eigenvalue $\lambda$ of $A$ satisfies
$$\lambda \in \bigcup_{i=1}^n [d_i - r_i, d_i + r_i], \qquad r_i = \sum_{j=1}^n |f_{ij}|.$$

**Generalization.** The source assumes that $A$ is symmetric, so that all eigenvalues of $A$ are
real. The inclusion holds for the real eigenvalues of every real matrix $A$.

The proof applies Theorem 7.2.1 (`GolubVanLoan.Chapter07.theorem_7_2_1`) to the complexified
matrices, whose Gershgorin discs meet the real line in these intervals. -/
theorem theorem_8_1_3 {A Q F : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (h : Qᵀ * A * Q = diagonal d + F) (hF : ∀ i, F i i = 0) :
    spectrum ℝ A ⊆ ⋃ i, Set.Icc (d i - ∑ j, |F i j|) (d i + ∑ j, |F i j|) := by
  intro μ hμ
  have hQQ : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hQ
  have hQu : IsUnit Q := (isUnit_iff_isUnit_det Q).2 (isUnit_det_of_left_inverse hQQ)
  have hinv : Q⁻¹ = Qᵀ := inv_eq_left_inv hQQ
  have hc : (complexify Q)⁻¹ * complexify A * complexify Q =
      diagonal (fun i => (d i : ℂ)) + complexify F := by
    rw [← complexify_inv, ← complexify_mul, ← complexify_mul, hinv, h, complexify_add]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hsub := GolubVanLoan.Chapter07.theorem_7_2_1 ((isUnit_complexify_iff Q).2 hQu) hc
    (fun i => by simp [hF i])
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hsub ((ofReal_mem_spectrum_complexify_iff A μ).2 hμ))
  rw [Metric.mem_closedBall, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at hi
  simp only [complexify_apply, Complex.norm_real, Real.norm_eq_abs] at hi
  obtain ⟨h1, h2⟩ := abs_le.1 hi
  exact Set.mem_iUnion.2 ⟨i, ⟨by linarith, by linarith⟩⟩

/-! ### Eigenvalue sensitivity (§8.1.2) -/

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Theorem 8.1.4** of [golub2013matrix] (Wielandt–Hoffman). Let
$A, E \in \mathbb{R}^{n \times n}$ with $A$ and $A + E$ symmetric. Then
$$\sum_{k=1}^n (\lambda_k(A + E) - \lambda_k(A))^2 \le \|E\|_F^2.$$

Since $A$ and $A + E$ are symmetric, $E$ is symmetric too. -/
theorem theorem_8_1_4 {A E : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hAE : (A + E).IsSymm) :
    ∑ k, (symmEigenvalue hAE k - symmEigenvalue hA k) ^ 2 ≤ ‖E‖ ^ 2 := by
  have h := IsHermitian.hoffman_wielandt (isHermitian_iff_isSymm.2 hAE)
    (isHermitian_iff_isSymm.2 hA)
  rw [add_sub_cancel_left] at h
  refine le_of_eq_of_le ?_ h
  exact (Equiv.sum_comp (finCongr (Fintype.card_fin n).symm)
    (fun j => ((isHermitian_iff_isSymm.2 hAE).eigenvalues₀ j -
      (isHermitian_iff_isSymm.2 hA).eigenvalues₀ j) ^ 2))

end Frobenius

/-- The trace of a symmetric $A$ is the sum of its eigenvalues:
$\operatorname{tr}(A) = \sum_k \lambda_k(A)$. -/
theorem trace_eq_sum_symmEigenvalue {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    A.trace = ∑ k, symmEigenvalue hA k := by
  rw [(isHermitian_iff_isSymm.2 hA).trace_eq_sum_eigenvalues₀]
  simp only [RCLike.ofReal_real_eq_id, id]
  exact (Equiv.sum_comp (finCongr (Fintype.card_fin n).symm) _).symm

/-- **Theorem 8.1.5** of [golub2013matrix]. Let $A, E \in \mathbb{R}^{n \times n}$ be symmetric,
with $n \ge 1$. Then for $k = 1, \dots, n$,
$$\lambda_k(A) + \lambda_n(E) \le \lambda_k(A + E) \le \lambda_k(A) + \lambda_1(E).$$

The Lean statement also takes a proof that $A + E$ is symmetric, which
`GolubVanLoan.Chapter08.symmEigenvalue` needs; it follows from the other two hypotheses. -/
theorem theorem_8_1_5 {A E : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hE : E.IsSymm)
    (hAE : (A + E).IsSymm) (hn : 0 < n) (k : Fin n) :
    symmEigenvalue hA k + symmEigenvalue hE ⟨n - 1, by omega⟩ ≤ symmEigenvalue hAE k ∧
      symmEigenvalue hAE k ≤ symmEigenvalue hA k + symmEigenvalue hE ⟨0, hn⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hTA := isSymmetric_toEuclideanLin hA
  have hTE := isSymmetric_toEuclideanLin hE
  have hTAE : (toEuclideanLin A + toEuclideanLin E).IsSymmetric := hTA.add hTE
  have hm : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1 :=
    finrank_euclideanSpace_fin
  have h := hTA.eigenvalues_add_mem_Icc hTE hTAE hm k
  have hlast : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
  have hzero : (⟨0, hn⟩ : Fin (m + 1)) = 0 := Fin.ext (by simp)
  simp only [hlast, hzero, symmEigenvalue_eq_eigenvalues hA hTA rfl hm,
    symmEigenvalue_eq_eigenvalues hE hTE rfl hm,
    symmEigenvalue_eq_eigenvalues hAE hTAE (map_add _ _ _) hm]
  exact h

/-- **Corollary 8.1.6** of [golub2013matrix] (Weyl). Let $A, E \in \mathbb{R}^{n \times n}$ be
symmetric. Then for $k = 1, \dots, n$,
$$|\lambda_k(A + E) - \lambda_k(A)| \le \|E\|_2.$$

The Lean statement also takes a proof that $A + E$ is symmetric. -/
theorem corollary_8_1_6 {A E : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hE : E.IsSymm)
    (hAE : (A + E).IsSymm) (k : Fin n) :
    |symmEigenvalue hAE k - symmEigenvalue hA k| ≤ lpOpNorm 2 E := by
  have hn : 0 < n := Fin.pos k
  have h := theorem_8_1_5 hA hE hAE hn k
  have hnorm := (l2_opNorm_eq_max_abs_symmEigenvalue hE hn).2
  have h1 : |symmEigenvalue hE ⟨0, hn⟩| ≤ lpOpNorm 2 E := hnorm ▸ le_max_left _ _
  have h2 : |symmEigenvalue hE ⟨n - 1, by omega⟩| ≤ lpOpNorm 2 E := hnorm ▸ le_max_right _ _
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Theorem 8.1.7** of [golub2013matrix] (interlacing property). Let
$A \in \mathbb{R}^{n \times n}$, let $r + 1 \le n$, and let $A_r = A(1{:}r, 1{:}r)$ and
$A_{r+1} = A(1{:}r{+}1, 1{:}r{+}1)$ be symmetric. Then for $k = 1, \dots, r$,
$$\lambda_{k+1}(A_{r+1}) \le \lambda_k(A_r) \le \lambda_k(A_{r+1}).$$

**Generalization.** The source assumes that $A$ is symmetric. Only the two leading principal
submatrices $A_r$ and $A_{r+1}$ need to be symmetric.

The index `k : Fin r` is 0-based, and the submatrices are
`A.submatrix (Fin.castLE _) (Fin.castLE _)`. -/
theorem theorem_8_1_7 {A : Matrix (Fin n) (Fin n) ℝ} {r : ℕ} (hr : r + 1 ≤ n)
    (hAr : (A.submatrix (Fin.castLE (by omega : r ≤ n)) (Fin.castLE (by omega))).IsSymm)
    (hAr1 : (A.submatrix (Fin.castLE hr) (Fin.castLE hr)).IsSymm) (k : Fin r) :
    symmEigenvalue hAr1 k.succ ≤ symmEigenvalue hAr k ∧
      symmEigenvalue hAr k ≤ symmEigenvalue hAr1 k.castSucc := by
  have hsub : (A.submatrix (Fin.castLE hr) (Fin.castLE hr)).submatrix Fin.castSucc Fin.castSucc =
      A.submatrix (Fin.castLE (by omega : r ≤ n)) (Fin.castLE (by omega)) := by
    ext i j; rfl
  have h := (isHermitian_iff_isSymm.2 hAr1).sortedEigenvalues_submatrix_castSucc_interlace
    (hsub ▸ isHermitian_iff_isSymm.2 hAr) k
  rw [IsHermitian.sortedEigenvalues_congr hsub _ (isHermitian_iff_isSymm.2 hAr)] at h
  exact h

/-- The case $\tau \ge 0$ of Theorem 8.1.8, from the backbone's rank-one interlacing:
$\lambda_i(A) \le \lambda_i(A + \tau c c^T)$, and
$\lambda_{i+1}(A + \tau c c^T) \le \lambda_i(A)$ for $i < n$. -/
private theorem rankOne_interlace {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 ≤ τ) (hB : (A + τ • vecMulVec c c).IsSymm) (i : Fin n) :
    symmEigenvalue hA i ≤ symmEigenvalue hB i ∧
      ∀ hi : (i : ℕ) + 1 < n, symmEigenvalue hB ⟨i + 1, hi⟩ ≤ symmEigenvalue hA i := by
  have hTA := isSymmetric_toEuclideanLin hA
  have hTB := isSymmetric_toEuclideanLin hB
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hsub : toEuclideanLin (A + τ • vecMulVec c c) - toEuclideanLin A =
      toEuclideanLin (τ • vecMulVec c c) := by
    rw [map_add, add_sub_cancel_left]
  have hpos : (toEuclideanLin (A + τ • vecMulVec c c) - toEuclideanLin A).IsPositive := by
    rw [hsub, isPositive_toEuclideanLin_iff]
    simpa using (posSemidef_vecMulVec_self_star c).smul hτ
  have hrank : Module.finrank ℝ (LinearMap.range
      (toEuclideanLin (A + τ • vecMulVec c c) - toEuclideanLin A)) ≤ 1 := by
    have hc : star c = c := funext fun i => by simp
    have := Matrix.finrank_range_toEuclideanLin_smul_vecMulVec_le τ c
    rw [hc] at this
    rw [hsub]
    exact this
  simp only [symmEigenvalue_eq_eigenvalues hA hTA rfl hn,
    symmEigenvalue_eq_eigenvalues hB hTB rfl hn]
  refine ⟨hTA.eigenvalues_le_of_re_inner_le hTB hn (fun x => ?_) i, fun hi =>
    (hTA.eigenvalues_le_of_isPositive_sub_of_finrank_range_le hTB hn hpos hrank i hi).1⟩
  have := hpos.2 x
  rw [LinearMap.sub_apply, inner_sub_left, map_sub] at this
  linarith

/-- **Theorem 8.1.8** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric,
$c \in \mathbb{R}^n$, $\tau \in \mathbb{R}$, and $B = A + \tau c c^T$. If $\tau \ge 0$, then
$$\lambda_i(B) \in [\lambda_i(A), \lambda_{i-1}(A)] \quad (i = 2, \dots, n), \qquad \lambda_1(A)
  \le \lambda_1(B).$$
If $\tau \le 0$, then
$$\lambda_i(B) \in [\lambda_{i+1}(A), \lambda_i(A)] \quad (i = 1, \dots, n - 1), \qquad
  \lambda_n(B) \le \lambda_n(A).$$

**Generalization.** The source assumes $\|c\|_2 = 1$. The interlacing holds for every
$c \in \mathbb{R}^n$.

The indices are 0-based. The Lean statement also takes a proof that $B$ is symmetric. -/
theorem theorem_8_1_8 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (c : Fin n → ℝ) (τ : ℝ)
    (hB : (A + τ • vecMulVec c c).IsSymm) :
    (0 ≤ τ → ∀ i : Fin n, symmEigenvalue hA i ≤ symmEigenvalue hB i ∧
        ∀ hi : 1 ≤ (i : ℕ), symmEigenvalue hB i ≤ symmEigenvalue hA ⟨i - 1, by omega⟩) ∧
      (τ ≤ 0 → ∀ i : Fin n, symmEigenvalue hB i ≤ symmEigenvalue hA i ∧
        ∀ hi : (i : ℕ) + 1 < n, symmEigenvalue hA ⟨i + 1, hi⟩ ≤ symmEigenvalue hB i) := by
  refine ⟨fun hτ i => ⟨(rankOne_interlace hA c hτ hB i).1, fun hi => ?_⟩, fun hτ i => ?_⟩
  · have := (rankOne_interlace hA c hτ hB ⟨i - 1, by omega⟩).2
      (by have := i.isLt; simp only; omega)
    convert this using 2
    ext
    simp only
    omega
  · have hBA : (A + τ • vecMulVec c c) + (-τ) • vecMulVec c c = A := by
      rw [neg_smul, add_neg_cancel_right]
    have hA' : ((A + τ • vecMulVec c c) + (-τ) • vecMulVec c c).IsSymm := by rw [hBA]; exact hA
    have h := rankOne_interlace hB c (neg_nonneg.2 hτ) hA' i
    rw [symmEigenvalue_eq_sortedEigenvalues hA' (by rw [hBA]; exact isHermitian_iff_isSymm.2 hA),
      IsHermitian.sortedEigenvalues_congr hBA _ (isHermitian_iff_isSymm.2 hA)] at h
    exact ⟨h.1, fun hi => h.2 hi⟩

/-- **Theorem 8.1.8** of [golub2013matrix], last part. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric with $n \ge 1$, let $c \in \mathbb{R}^n$ with $c^T c = 1$, let $\tau \in \mathbb{R}$
and $B = A + \tau c c^T$. Then there are $m_1, \dots, m_n \ge 0$ with $m_1 + \dots + m_n = 1$
and
$$\lambda_i(B) = \lambda_i(A) + m_i \tau, \qquad i = 1, \dots, n.$$
-/
theorem theorem_8_1_8_b {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {c : Fin n → ℝ}
    (hc : c ⬝ᵥ c = 1) (τ : ℝ) (hB : (A + τ • vecMulVec c c).IsSymm) (hn : 0 < n) :
    ∃ m : Fin n → ℝ, (∀ i, 0 ≤ m i) ∧ ∑ i, m i = 1 ∧
      ∀ i, symmEigenvalue hB i = symmEigenvalue hA i + m i * τ := by
  rcases eq_or_ne τ 0 with rfl | hτ
  · have hBA : A + (0 : ℝ) • vecMulVec c c = A := by rw [zero_smul, add_zero]
    have heq : symmEigenvalue hB = symmEigenvalue hA :=
      IsHermitian.sortedEigenvalues_congr hBA _ _
    refine ⟨Pi.single ⟨0, hn⟩ 1, fun i => ?_, by simp, fun i => by rw [heq]; simp⟩
    by_cases h : i = ⟨0, hn⟩ <;> simp [h]
  · have h8 := theorem_8_1_8 hA c τ hB
    refine ⟨fun i => (symmEigenvalue hB i - symmEigenvalue hA i) / τ, fun i => ?_, ?_,
      fun i => ?_⟩
    · rcases hτ.lt_or_gt with h | h
      · exact div_nonneg_of_nonpos (by linarith [(h8.2 h.le i).1]) h.le
      · exact div_nonneg (by linarith [(h8.1 h.le i).1]) h.le
    · rw [← Finset.sum_div, Finset.sum_sub_distrib, ← trace_eq_sum_symmEigenvalue,
        ← trace_eq_sum_symmEigenvalue, trace_add, trace_smul, trace_vecMulVec, hc, smul_eq_mul,
        mul_one, add_sub_cancel_left, div_self hτ]
    · rw [div_mul_cancel₀ _ hτ]
      ring

/-! ### Invariant subspaces (§8.1.3) -/

/-- If $Q_1$ has orthonormal columns and $\operatorname{ran}(Q_1)$ is $A$-invariant, then
$A Q_1 = Q_1 (Q_1^T A Q_1)$. -/
private theorem mul_eq_mul_of_invariant {A : Matrix (Fin n) (Fin n) ℝ} {r : ℕ}
    {Q₁ : Matrix (Fin n) (Fin r) ℝ} (hQ : Q₁ᵀ * Q₁ = 1)
    (hinv : ∀ x ∈ LinearMap.range (toLin' Q₁), A *ᵥ x ∈ LinearMap.range (toLin' Q₁)) :
    A * Q₁ = Q₁ * (Q₁ᵀ * A * Q₁) := by
  refine toLin'.injective (LinearMap.ext fun v => ?_)
  obtain ⟨y, hy⟩ := hinv _ ⟨v, rfl⟩
  simp only [toLin'_apply] at hy
  simp only [toLin'_apply, ← mulVec_mulVec, Matrix.mul_assoc]
  rw [← hy]
  congr 1
  rw [mulVec_mulVec, hQ, one_mulVec]

/-- **Theorem 8.1.9** of [golub2013matrix], with (8.1.1). Let $A \in \mathbb{R}^{n \times n}$ be
symmetric, and let $Q = [Q_1 \; Q_2]$ be orthogonal with $Q_1 \in \mathbb{R}^{n \times r}$ and
$Q_2 \in \mathbb{R}^{n \times s}$. If $\operatorname{ran}(Q_1)$ is $A$-invariant, then
$$Q^T A Q = \begin{bmatrix} D_1 & 0 \\ 0 & D_2 \end{bmatrix}, \qquad D_1 = Q_1^T A Q_1, \quad
  D_2 = Q_2^T A Q_2,$$
and $\det(\lambda I - A) = \det(\lambda I - D_1) \det(\lambda I - D_2)$, so that
$\lambda(A) = \lambda(D_1) \cup \lambda(D_2)$ with multiplicity.

Orthogonality of $Q$ is stated as $Q^T Q = I$ and $Q Q^T = I$. Invariance is stated as
$Ax \in \operatorname{ran}(Q_1)$ for all $x \in \operatorname{ran}(Q_1)$, and the determinants
are Mathlib's `Matrix.charpoly`. -/
theorem theorem_8_1_9 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {r s : ℕ}
    {Q₁ : Matrix (Fin n) (Fin r) ℝ} {Q₂ : Matrix (Fin n) (Fin s) ℝ}
    (hQ : (fromCols Q₁ Q₂)ᵀ * fromCols Q₁ Q₂ = 1) (hQ' : fromCols Q₁ Q₂ * (fromCols Q₁ Q₂)ᵀ = 1)
    (hinv : ∀ x ∈ LinearMap.range (toLin' Q₁), A *ᵥ x ∈ LinearMap.range (toLin' Q₁)) :
    (fromCols Q₁ Q₂)ᵀ * A * fromCols Q₁ Q₂ = fromBlocks (Q₁ᵀ * A * Q₁) 0 0 (Q₂ᵀ * A * Q₂) ∧
      A.charpoly = (Q₁ᵀ * A * Q₁).charpoly * (Q₂ᵀ * A * Q₂).charpoly := by
  have hH := isHermitian_iff_isSymm.2 hA
  have hQ₁ : Q₁ᵀ * Q₁ = 1 := by
    have h := hQ
    rw [transpose_fromCols, fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_inj] at h
    exact h.1
  have hAQ := mul_eq_mul_of_invariant hQ₁ hinv
  simp only [← conjTranspose_eq_transpose_of_trivial] at hQ hQ' ⊢
  exact ⟨hH.conjTranspose_mul_mul_fromCols_eq_fromBlocks hQ hAQ,
    hH.charpoly_eq_mul_of_mul_eq_mul hQ hQ' hAQ⟩

/-- **Equation (8.1.2)** of [golub2013matrix], the separation of two symmetric matrices. For
$B \in \mathbb{R}^{p \times p}$ and $C \in \mathbb{R}^{q \times q}$,
$$\operatorname{sep}(B, C) = \min_{\lambda \in \lambda(B), \, \mu \in \lambda(C)} |\lambda -
  \mu|.$$

The definition is the infimum over the real eigenvalues of $B$ and $C$, for any real square
matrices. If $B$ or $C$ has no real eigenvalue, for example when $p = 0$ or $q = 0$, the value
is $0$.

**Reading.** The source defines a minimum of distances between two nonempty spectra. Lean uses
a real infimum, with a total value when either spectrum is empty. -/
noncomputable def sepSymm {p q : ℕ} (B : Matrix (Fin p) (Fin p) ℝ)
    (C : Matrix (Fin q) (Fin q) ℝ) : ℝ :=
  sInf {d | ∃ l ∈ spectrum ℝ B, ∃ m ∈ spectrum ℝ C, d = |l - m|}

/-- **Equation (8.1.2)** of [golub2013matrix], with Problem P8.1.9. Let
$B \in \mathbb{R}^{p \times p}$ and $C \in \mathbb{R}^{q \times q}$ be symmetric with
$p, q \ge 1$. Then the separation (7.2.5) of the Sylvester operator,
$$\min_{X \neq 0} \frac{\|BX - XC\|_F}{\|X\|_F},$$
equals the eigenvalue gap $\operatorname{sep}(B, C)$ of (8.1.2).

The left side is the backbone's `Matrix.sep`.

**Correction.** Problem P8.1.9 prints an unconstrained minimum over $X$, which is always zero
by taking $X=0$. The backbone separation `Matrix.sep` represents the minimum over $X$ of unit
Frobenius norm. -/
theorem sepSymm_eq_sep {p q : ℕ} {B : Matrix (Fin p) (Fin p) ℝ} {C : Matrix (Fin q) (Fin q) ℝ}
    (hB : B.IsSymm) (hC : C.IsSymm) (hp : 0 < p) (hq : 0 < q) : sep B C = sepSymm B C := by
  have : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have hB' := isHermitian_iff_isSymm.2 hB
  have hC' := isHermitian_iff_isSymm.2 hC
  rw [hB'.sep_eq_iInf_abs_eigenvalues_sub hC', sepSymm, hB'.spectrum_real_eq_range_eigenvalues,
    hC'.spectrum_real_eq_range_eigenvalues]
  have hbdd : ∀ i, BddBelow (Set.range fun j => |hB'.eigenvalues i - hC'.eigenvalues j|) :=
    fun i => ⟨0, by rintro _ ⟨j, rfl⟩; exact abs_nonneg _⟩
  have hbdd' : BddBelow (Set.range fun i => ⨅ j, |hB'.eigenvalues i - hC'.eigenvalues j|) :=
    ⟨0, by rintro _ ⟨i, rfl⟩; exact le_ciInf fun j => abs_nonneg _⟩
  apply le_antisymm
  · refine le_csInf ⟨_, _, ⟨⟨0, hp⟩, rfl⟩, _, ⟨⟨0, hq⟩, rfl⟩, rfl⟩ ?_
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact (ciInf_le hbdd' i).trans (ciInf_le (hbdd i) j)
  · refine le_ciInf fun i => le_ciInf fun j => csInf_le ⟨0, ?_⟩ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    rintro _ ⟨_, _, _, _, rfl⟩
    exact abs_nonneg _

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- The Frobenius norm is invariant under $X \mapsto Q^T X Q$ for every $Q$ with $Q Q^T = I$. -/
private theorem frobenius_norm_transpose_mul_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Matrix (Fin n) (Fin n) ℝ) {Q : Matrix (Fin n) ι ℝ} (hQ : Q * Qᵀ = 1) :
    ‖Qᵀ * E * Q‖ = ‖E‖ := by
  have h1 := frobenius_norm_sq_eq_trace (Qᵀ * E * Q)
  have h2 := frobenius_norm_sq_eq_trace E
  simp only [conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id] at h1 h2
  have htr : trace ((Qᵀ * E * Q)ᵀ * (Qᵀ * E * Q)) = trace (Eᵀ * E) := by
    have e : (Qᵀ * E * Q)ᵀ * (Qᵀ * E * Q) = Qᵀ * (Eᵀ * E * Q) := by
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q Qᵀ, hQ, Matrix.one_mul]
    rw [e, trace_mul_comm, Matrix.mul_assoc (Eᵀ * E) Q Qᵀ, hQ, Matrix.mul_one]
  rw [htr, ← h2] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

/-- A symmetric positive semidefinite matrix $M$ has a symmetric square root $S$, with $S^2 = M$. -/
private theorem exists_isSymm_mul_self_eq {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsSymm)
    (hpos : M.PosSemidef) : ∃ S : Matrix (Fin n) (Fin n) ℝ, S.IsSymm ∧ S * S = M := by
  obtain ⟨V, hV, hVM, -⟩ := theorem_8_1_1 hM
  have hVV : V * Vᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hV
  have hVV' : Vᵀ * V = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hV
  have hnn : ∀ k, 0 ≤ symmEigenvalue hM k := fun k => by
    obtain ⟨i, hi⟩ : symmEigenvalue hM k ∈ Set.range hpos.isHermitian.eigenvalues := by
      rw [← hpos.isHermitian.spectrum_real_eq_range_eigenvalues]
      exact symmEigenvalue_mem_spectrum hM k
    rw [← hi]
    exact hpos.eigenvalues_nonneg i
  have hMe : M = V * diagonal (symmEigenvalue hM) * Vᵀ := by
    rw [← hVM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hVV, Matrix.one_mul, Matrix.mul_assoc,
      hVV, Matrix.mul_one]
  refine ⟨V * diagonal (fun k => Real.sqrt (symmEigenvalue hM k)) * Vᵀ, ?_, ?_⟩
  · rw [IsSymm, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose,
      Matrix.mul_assoc]
  · refine (?_ : _ = V * diagonal (symmEigenvalue hM) * Vᵀ).trans hMe.symm
    have : diagonal (fun k => Real.sqrt (symmEigenvalue hM k)) *
        diagonal (fun k => Real.sqrt (symmEigenvalue hM k)) = diagonal (symmEigenvalue hM) := by
      rw [diagonal_mul_diagonal]
      congr 1
      funext k
      exact Real.mul_self_sqrt (hnn k)
    calc V * diagonal (fun k => Real.sqrt (symmEigenvalue hM k)) * Vᵀ *
          (V * diagonal (fun k => Real.sqrt (symmEigenvalue hM k)) * Vᵀ)
        = V * (diagonal (fun k => Real.sqrt (symmEigenvalue hM k)) * (Vᵀ * V) *
            diagonal (fun k => Real.sqrt (symmEigenvalue hM k))) * Vᵀ := by
          simp only [Matrix.mul_assoc]
      _ = V * diagonal (symmEigenvalue hM) * Vᵀ := by rw [hVV', Matrix.mul_one, this]

/-- **Theorem 8.1.10** of [golub2013matrix]. Let $A, E \in \mathbb{R}^{n \times n}$ with $A$
symmetric, and let $Q = [Q_1 \; Q_2]$ be orthogonal with $Q_1 \in \mathbb{R}^{n \times r}$ and
$Q_2 \in \mathbb{R}^{n \times s}$. Assume
$$Q^T A Q = \begin{bmatrix} D_1 & 0 \\ 0 & D_2 \end{bmatrix}, \qquad Q^T E Q = \begin{bmatrix}
  E_{11} & E_{12} \\ E_{21} & E_{22} \end{bmatrix},$$
so that $\operatorname{ran}(Q_1)$ is $A$-invariant. If $\operatorname{sep}(D_1, D_2) > 0$ and
$\|E\|_F \le \operatorname{sep}(D_1, D_2)/5$, then there is $P \in \mathbb{R}^{s \times r}$ with
$$\|P\|_F \le \frac{4}{\operatorname{sep}(D_1, D_2)} \|E_{21}\|_F$$
such that the following holds. There is a symmetric $S \in \mathbb{R}^{r \times r}$ with
$S^2 = I + P^T P$, and for every such $S$ the columns of $\hat Q_1 = (Q_1 + Q_2 P) S^{-1}$ are
orthonormal and $\operatorname{ran}(\hat Q_1)$ is invariant for $A + E$, that is,
$(A + E) \hat Q_1 = \hat Q_1 M$ for some $M \in \mathbb{R}^{r \times r}$.

**Generalization.** The theorem does not need $E$ to be symmetric. The source takes
$\hat Q_1 = (Q_1 + Q_2 P)(I + P^T P)^{-1/2}$; the theorem holds for every symmetric square root
$S$ of $I + P^T P$, and the positive definite square root is one of them.

The block $E_{21}$ is `toBlocks₂₁` of $Q^T E Q$, and the separation (8.1.2) is
`GolubVanLoan.Chapter08.sepSymm`. The matrix $S$ is nonsingular because $S^2 = I + P^T P$ is
positive definite, and $S^{-1}$ is the matrix inverse. The theorem restates Theorem 7.2.4 of
[golub2013matrix] for symmetric $A$. -/
theorem theorem_8_1_10 {A E : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {r s : ℕ}
    {Q₁ : Matrix (Fin n) (Fin r) ℝ} {Q₂ : Matrix (Fin n) (Fin s) ℝ}
    (hQ : (fromCols Q₁ Q₂)ᵀ * fromCols Q₁ Q₂ = 1) (hQ' : fromCols Q₁ Q₂ * (fromCols Q₁ Q₂)ᵀ = 1)
    {D₁ : Matrix (Fin r) (Fin r) ℝ} {D₂ : Matrix (Fin s) (Fin s) ℝ}
    (hAQ : (fromCols Q₁ Q₂)ᵀ * A * fromCols Q₁ Q₂ = fromBlocks D₁ 0 0 D₂)
    (hsep : 0 < sepSymm D₁ D₂) (hEsmall : ‖E‖ ≤ sepSymm D₁ D₂ / 5) :
    ∃ P : Matrix (Fin s) (Fin r) ℝ,
      ‖P‖ ≤ 4 / sepSymm D₁ D₂ * ‖((fromCols Q₁ Q₂)ᵀ * E * fromCols Q₁ Q₂).toBlocks₂₁‖ ∧
      (∃ S : Matrix (Fin r) (Fin r) ℝ, S.IsSymm ∧ S * S = 1 + Pᵀ * P) ∧
      ∀ S : Matrix (Fin r) (Fin r) ℝ, S.IsSymm → S * S = 1 + Pᵀ * P →
        ((Q₁ + Q₂ * P) * S⁻¹)ᵀ * ((Q₁ + Q₂ * P) * S⁻¹) = 1 ∧
          ∃ M : Matrix (Fin r) (Fin r) ℝ, (A + E) * ((Q₁ + Q₂ * P) * S⁻¹) =
            ((Q₁ + Q₂ * P) * S⁻¹) * M := by
  set Q := fromCols Q₁ Q₂
  set E' := Qᵀ * E * Q
  -- the diagonal blocks are symmetric, hence both nonempty since `sep > 0`
  have hQAQs : (Qᵀ * A * Q).IsSymm := by
    exact hA.transpose_mul_mul Q
  have hD₁ : D₁.IsSymm := by
    have := hQAQs.eq
    rw [hAQ, fromBlocks_transpose, fromBlocks_inj] at this
    exact this.1
  have hD₂ : D₂.IsSymm := by
    have := hQAQs.eq
    rw [hAQ, fromBlocks_transpose, fromBlocks_inj] at this
    exact this.2.2.2
  have hr : 0 < r := by
    by_contra h0
    have : spectrum ℝ D₁ = ∅ := by
      rw [spectrum_eq_range_symmEigenvalue hD₁, Set.range_eq_empty_iff]
      exact ⟨fun k => absurd k.isLt (by omega)⟩
    simp [sepSymm, this] at hsep
  have hs : 0 < s := by
    by_contra h0
    have : spectrum ℝ D₂ = ∅ := by
      rw [spectrum_eq_range_symmEigenvalue hD₂, Set.range_eq_empty_iff]
      exact ⟨fun k => absurd k.isLt (by omega)⟩
    simp [sepSymm, this] at hsep
  have hsepeq : sep D₁ D₂ = sepSymm D₁ D₂ := sepSymm_eq_sep hD₁ hD₂ hr hs
  have hE' : ‖E'‖ = ‖E‖ := frobenius_norm_transpose_mul_mul E hQ'
  obtain ⟨P, hPn, hPeq⟩ := exists_invariant_graph_of_sep (𝕜 := ℝ) (T₁₁ := D₁)
    (T₁₂ := (0 : Matrix (Fin r) (Fin s) ℝ)) (T₂₂ := D₂) (E := E') (by rw [hsepeq]; exact hsep)
    (by rw [norm_zero, mul_zero, zero_div, add_zero, mul_one, hE', hsepeq]; exact hEsmall)
  have hQQ := hQ
  rw [transpose_fromCols, fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_inj] at hQQ
  obtain ⟨h11, h12, h21, h22⟩ := hQQ
  -- `Q [I; P] = Q₁ + Q₂ P`
  have hW : Q * fromRows 1 P = Q₁ + Q₂ * P := by
    simp only [Q, fromCols_mul_fromRows, Matrix.mul_one]
  set M := D₁ + E'.toBlocks₁₁ + (0 + E'.toBlocks₁₂) * P
  have hQAEQ : Qᵀ * (A + E) * Q = fromBlocks D₁ 0 0 D₂ + E' := by
    rw [← hAQ]
    simp only [E', Matrix.mul_add, Matrix.add_mul]
  have hinv : (A + E) * (Q₁ + Q₂ * P) = (Q₁ + Q₂ * P) * M := by
    calc (A + E) * (Q₁ + Q₂ * P) = Q * (Qᵀ * (A + E) * Q) * fromRows 1 P := by
          rw [← hW]
          simp only [← Matrix.mul_assoc]
          rw [hQ', Matrix.one_mul]
      _ = (Q₁ + Q₂ * P) * M := by
          rw [hQAEQ, Matrix.mul_assoc, hPeq, ← Matrix.mul_assoc, hW]
  have hWW : (Q₁ + Q₂ * P)ᵀ * (Q₁ + Q₂ * P) = 1 + Pᵀ * P := by
    simp only [transpose_add, transpose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    rw [h11, ← Matrix.mul_assoc Q₁ᵀ Q₂ P, h12, h21, ← Matrix.mul_assoc Q₂ᵀ Q₂ P, h22]
    simp
  have hMsymm : (1 + Pᵀ * P).IsSymm := by
    rw [IsSymm, transpose_add, transpose_one, transpose_mul, transpose_transpose]
  have hMpos : (1 + Pᵀ * P).PosSemidef := by
    have := PosSemidef.one.add (posSemidef_conjTranspose_mul_self P)
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  have hMdef : (1 + Pᵀ * P).PosDef := by
    have := PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self P)
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  refine ⟨P, by rw [hsepeq] at hPn; rw [div_mul_eq_mul_div]; exact hPn,
    exists_isSymm_mul_self_eq hMsymm hMpos, fun S hS hSS => ?_⟩
  have hSdet : IsUnit S.det := by
    have h := hMdef.det_pos
    rw [← hSS, det_mul] at h
    exact isUnit_iff_ne_zero.2 fun h0 => by rw [h0, zero_mul] at h; exact lt_irrefl _ h
  have hSi : S⁻¹ * S = 1 := nonsing_inv_mul S hSdet
  have hSi' : S * S⁻¹ = 1 := mul_nonsing_inv S hSdet
  have hSt : (S⁻¹)ᵀ = S⁻¹ := by rw [transpose_nonsing_inv, hS.eq]
  refine ⟨?_, S * M * S⁻¹, ?_⟩
  · rw [transpose_mul, hSt, Matrix.mul_assoc, ← Matrix.mul_assoc (Q₁ + Q₂ * P)ᵀ, hWW, ← hSS,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hSi, Matrix.one_mul, hSi']
  · rw [← Matrix.mul_assoc, hinv]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S⁻¹ S, hSi, Matrix.one_mul]

open scoped MatrixOrder in
/-- **Equation (8.1.3)** of [golub2013matrix]. For every $P \in \mathbb{R}^{s \times r}$,
$$\|P (I + P^T P)^{-1/2}\|_2 \le \|P\|_2 \le \|P\|_F.$$

The square root is `CFC.sqrt`, the positive semidefinite square root. Corollary 8.1.11 uses this
bound. -/
theorem equation_8_1_3 {r s : ℕ} (P : Matrix (Fin s) (Fin r) ℝ) :
    lpOpNorm 2 (P * (CFC.sqrt (1 + Pᵀ * P))⁻¹) ≤ lpOpNorm 2 P ∧ lpOpNorm 2 P ≤ ‖P‖ := by
  have h := l2_opNorm_mul_inv_sqrt_one_add_gram_le P
  rwa [conjTranspose_eq_transpose_of_trivial] at h

/-- For a square orthogonal $Q$, the distance between the column spaces of $QM$ and $QN$ equals the
gap between the column spaces of $M$ and $N$, because $Q$ is an isometry. -/
private theorem subspaceDist_range_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {Q : Matrix (Fin n) ι ℝ} (hQ : Qᵀ * Q = 1) (hQ' : Q * Qᵀ = 1)
    (M N : Matrix ι κ ℝ) :
    Chapter02.subspaceDist (LinearMap.range (toEuclideanLin (Q * M)))
        (LinearMap.range (toEuclideanLin (Q * N))) =
      (LinearMap.range (toEuclideanLin M)).gap (LinearMap.range (toEuclideanLin N)) := by
  have hQh : Qᴴ * Q = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  have hQh' : Q * Qᴴ = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  simp only [Chapter02.subspaceDist, range_mul_eq_map_of_mul_conjTranspose_eq_one hQh hQh']
  rw [Submodule.gap_map_linearIsometryEquiv]

/-- **Corollary 8.1.11** of [golub2013matrix]. Under the hypotheses of Theorem 8.1.10, there is
$P \in \mathbb{R}^{s \times r}$ with $\|P\|_F \le (4/\operatorname{sep}(D_1, D_2)) \|E_{21}\|_F$
such that a symmetric $S$ with $S^2 = I + P^T P$ exists, and for every such $S$ the matrix
$\hat Q_1 = (Q_1 + Q_2 P) S^{-1}$ has the properties of Theorem 8.1.10 and
$$\operatorname{dist}(\operatorname{ran}(Q_1), \operatorname{ran}(\hat Q_1)) \le
  \frac{4}{\operatorname{sep}(D_1, D_2)} \|E_{21}\|_F.$$

**Generalization.** As in Theorem 8.1.10, $E$ need not be symmetric and $S$ is any symmetric
square root of $I + P^T P$.

The conclusions of `GolubVanLoan.Chapter08.theorem_8_1_10` are repeated, so that the bound
refers to the same $P$ and $\hat Q_1$. The distance is `GolubVanLoan.Chapter02.subspaceDist` of
the column spaces. Since $\operatorname{ran}(\hat Q_1) = \operatorname{ran}(Q \begin{bmatrix} I
\\ P \end{bmatrix})$ and $\operatorname{ran}(Q_1) = \operatorname{ran}(Q \begin{bmatrix} I \\ 0
\end{bmatrix})$, the proof bounds the distance by $\|P\|_2 \le \|P\|_F$ with
`Matrix.gap_range_fromRows_le` and (8.1.3), instead of the route of the source through
$\operatorname{dist} = \|Q_2^T \hat Q_1\|_2 = \|P (I + P^T P)^{-1/2}\|_2$. -/
theorem corollary_8_1_11 {A E : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {r s : ℕ}
    {Q₁ : Matrix (Fin n) (Fin r) ℝ} {Q₂ : Matrix (Fin n) (Fin s) ℝ}
    (hQ : (fromCols Q₁ Q₂)ᵀ * fromCols Q₁ Q₂ = 1) (hQ' : fromCols Q₁ Q₂ * (fromCols Q₁ Q₂)ᵀ = 1)
    {D₁ : Matrix (Fin r) (Fin r) ℝ} {D₂ : Matrix (Fin s) (Fin s) ℝ}
    (hAQ : (fromCols Q₁ Q₂)ᵀ * A * fromCols Q₁ Q₂ = fromBlocks D₁ 0 0 D₂)
    (hsep : 0 < sepSymm D₁ D₂) (hEsmall : ‖E‖ ≤ sepSymm D₁ D₂ / 5) :
    ∃ P : Matrix (Fin s) (Fin r) ℝ,
      ‖P‖ ≤ 4 / sepSymm D₁ D₂ * ‖((fromCols Q₁ Q₂)ᵀ * E * fromCols Q₁ Q₂).toBlocks₂₁‖ ∧
      (∃ S : Matrix (Fin r) (Fin r) ℝ, S.IsSymm ∧ S * S = 1 + Pᵀ * P) ∧
      ∀ S : Matrix (Fin r) (Fin r) ℝ, S.IsSymm → S * S = 1 + Pᵀ * P →
        ((Q₁ + Q₂ * P) * S⁻¹)ᵀ * ((Q₁ + Q₂ * P) * S⁻¹) = 1 ∧
        (∃ M : Matrix (Fin r) (Fin r) ℝ, (A + E) * ((Q₁ + Q₂ * P) * S⁻¹) =
          ((Q₁ + Q₂ * P) * S⁻¹) * M) ∧
        Chapter02.subspaceDist (LinearMap.range (toEuclideanLin Q₁))
            (LinearMap.range (toEuclideanLin ((Q₁ + Q₂ * P) * S⁻¹))) ≤
          4 / sepSymm D₁ D₂ * ‖((fromCols Q₁ Q₂)ᵀ * E * fromCols Q₁ Q₂).toBlocks₂₁‖ := by
  obtain ⟨P, hP, hS, h⟩ := theorem_8_1_10 hA hQ hQ' hAQ hsep hEsmall
  refine ⟨P, hP, hS, fun S hSs hSS => ⟨(h S hSs hSS).1, (h S hSs hSS).2, ?_⟩⟩
  -- `S` is invertible, so `ran Q̂₁ = ran(Q₁ + Q₂ P)`
  have hSu : IsUnit S.det := by
    have hM : (1 + Pᵀ * P).PosDef := by
      simpa [conjTranspose_eq_transpose_of_trivial] using
        PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self P)
    have h2 := (isUnit_iff_isUnit_det _).1 hM.isUnit
    rw [← hSS, det_mul] at h2
    exact isUnit_of_mul_isUnit_left h2
  have hrange : LinearMap.range (toEuclideanLin ((Q₁ + Q₂ * P) * S⁻¹)) =
      LinearMap.range (toEuclideanLin (Q₁ + Q₂ * P)) := by
    rw [toEuclideanLin_mul]
    refine LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 fun y => ?_)
    refine ⟨toEuclideanLin S y, ?_⟩
    rw [← toEuclideanLin_mul_apply, nonsing_inv_mul _ hSu, toEuclideanLin_one_apply]
  have h₁ : Q₁ = fromCols Q₁ Q₂ * fromRows (1 : Matrix (Fin r) (Fin r) ℝ) 0 := by
    rw [fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]
  have h₂ : Q₁ + Q₂ * P = fromCols Q₁ Q₂ * fromRows 1 P := by
    rw [fromCols_mul_fromRows, Matrix.mul_one]
  have hd := subspaceDist_range_mul hQ hQ' (fromRows (1 : Matrix (Fin r) (Fin r) ℝ) 0)
    (fromRows 1 P)
  rw [← h₁, ← h₂] at hd
  rw [hrange, hd]
  exact (gap_range_fromRows_le P).trans ((equation_8_1_3 P).2.trans hP)

/-- A column $x$ with $x^T x = 1$ is a unit vector. -/
private theorem norm_toLp_eq_one_of_transpose_mul_self {x : Fin n → ℝ}
    (h : (replicateCol (Fin 1) x)ᵀ * replicateCol (Fin 1) x = 1) : ‖WithLp.toLp 2 x‖ = 1 := by
  have h00 := congrFun (congrFun h 0) 0
  simp only [Matrix.mul_apply, transpose_apply, replicateCol_apply, one_apply_eq] at h00
  have h2 : ‖WithLp.toLp 2 x‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [sq] using h00
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (by rw [h2, one_pow])

/-- For unit vectors $q$ and $u$ of a real inner product space, the sine of the angle between $q$
and $\operatorname{span}\{u\}$ is $\sqrt{1 - \langle u, q \rangle^2}$.

Section 8.2 also uses this lemma. -/
theorem sinAngle_span_singleton_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {q u : E} (hq : ‖q‖ = 1) (hu : ‖u‖ = 1) :
    (ℝ ∙ u).sinAngle q = √(1 - inner ℝ u q ^ 2) := by
  have hP : (ℝ ∙ u).starProjection q = inner ℝ u q • u := by
    rw [Submodule.starProjection_singleton, hu, one_pow, RCLike.ofReal_one, div_one]
  have h := Submodule.norm_starProjection_sq_add_norm_sub_sq (ℝ ∙ u) q
  rw [hP, norm_smul, hu, mul_one, hq, Real.norm_eq_abs, sq_abs] at h
  rw [Submodule.sinAngle, hq, div_one, hP,
    show 1 - inner ℝ u q ^ 2 = ‖q - inner ℝ u q • u‖ ^ 2 by linarith, Real.sqrt_sq (norm_nonneg _)]

/-- For unit vectors $u, v \in \mathbb{R}^n$, $\operatorname{dist}(\operatorname{span}\{u\},
\operatorname{span}\{v\}) = \sqrt{1 - (u^T v)^2}$. -/
private theorem subspaceDist_span_singleton {u v : Fin n → ℝ} (hu : ‖WithLp.toLp 2 u‖ = 1)
    (hv : ‖WithLp.toLp 2 v‖ = 1) :
    Chapter02.subspaceDist (ℝ ∙ WithLp.toLp 2 u) (ℝ ∙ WithLp.toLp 2 v) = √(1 - (u ⬝ᵥ v) ^ 2) := by
  have hi : inner ℝ (WithLp.toLp 2 v) (WithLp.toLp 2 u) = u ⬝ᵥ v := by
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial]
  rw [Chapter02.subspaceDist, Submodule.gap_span_singleton_eq_sinAngle hu hv,
    sinAngle_span_singleton_eq hu hv, hi]

/-- **Theorem 8.1.12** of [golub2013matrix] (eigenvector perturbation). Let
$A, E \in \mathbb{R}^{n \times n}$ with $A$ symmetric, and let $Q = [q_1 \; Q_2]$ be orthogonal
with $q_1 \in \mathbb{R}^n$ and $Q_2 \in \mathbb{R}^{n \times s}$. Partition
$$Q^T A Q = \begin{bmatrix} \lambda & 0 \\ 0 & D_2 \end{bmatrix}, \qquad Q^T E Q =
  \begin{bmatrix} \epsilon & e^T \\ e & E_{22} \end{bmatrix},$$
so that $q_1$ is an eigenvector of $A$. Let $d = \min_{\mu \in \lambda(D_2)} |\lambda - \mu|$.
If $d > 0$ and $\|E\|_F \le d/5$, then there is $p \in \mathbb{R}^s$ with
$\|p\|_2 \le (4/d) \|e\|_2$ such that
$$\hat q_1 = \frac{q_1 + Q_2 p}{\sqrt{1 + p^T p}}$$
is a unit 2-norm eigenvector of $A + E$, and
$$\operatorname{dist}(\operatorname{span}\{q_1\}, \operatorname{span}\{\hat q_1\}) = \sqrt{1 -
  (q_1^T \hat q_1)^2} \le \frac{4}{d} \|e\|_2.$$

**Generalization.** The source assumes that $A + E$ is symmetric. The theorem needs only $A$ to
be symmetric.

The source has $s = n - 1$; here orthogonality of $Q$ forces it. The vector $e$ is the column of
the $(2,1)$ block `toBlocks₂₁` of $Q^T E Q$, $d$ is the infimum over the real spectrum of $D_2$,
and the distance is `GolubVanLoan.Chapter02.subspaceDist`. The theorem is the case $r = 1$ of
Theorem 8.1.10 and Corollary 8.1.11, with $d = \operatorname{sep}((\lambda), D_2)$ and the
scalar square root of $1 + p^T p$. -/
theorem theorem_8_1_12 {A E : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {s : ℕ}
    {q₁ : Fin n → ℝ} {Q₂ : Matrix (Fin n) (Fin s) ℝ}
    (hQ : (fromCols (replicateCol (Fin 1) q₁) Q₂)ᵀ * fromCols (replicateCol (Fin 1) q₁) Q₂ = 1)
    (hQ' : fromCols (replicateCol (Fin 1) q₁) Q₂ * (fromCols (replicateCol (Fin 1) q₁) Q₂)ᵀ = 1)
    {l : ℝ} {D₂ : Matrix (Fin s) (Fin s) ℝ}
    (hAQ : (fromCols (replicateCol (Fin 1) q₁) Q₂)ᵀ * A * fromCols (replicateCol (Fin 1) q₁) Q₂ =
      fromBlocks !![l] 0 0 D₂)
    {e : Fin s → ℝ} (he : replicateCol (Fin 1) e =
      ((fromCols (replicateCol (Fin 1) q₁) Q₂)ᵀ * E *
        fromCols (replicateCol (Fin 1) q₁) Q₂).toBlocks₂₁)
    {d : ℝ} (hd : d = sInf {x | ∃ μ ∈ spectrum ℝ D₂, x = |l - μ|}) (hd0 : 0 < d)
    (hE : ‖E‖ ≤ d / 5) :
    ∃ p : Fin s → ℝ, ‖WithLp.toLp 2 p‖ ≤ 4 / d * ‖WithLp.toLp 2 e‖ ∧
      ∀ qh₁ : Fin n → ℝ, qh₁ = (√(1 + p ⬝ᵥ p))⁻¹ • (q₁ + Q₂ *ᵥ p) →
        ‖WithLp.toLp 2 qh₁‖ = 1 ∧ (∃ μ : ℝ, (A + E) *ᵥ qh₁ = μ • qh₁) ∧
        Chapter02.subspaceDist (ℝ ∙ WithLp.toLp 2 q₁) (ℝ ∙ WithLp.toLp 2 qh₁) =
          √(1 - (q₁ ⬝ᵥ qh₁) ^ 2) ∧
        √(1 - (q₁ ⬝ᵥ qh₁) ^ 2) ≤ 4 / d * ‖WithLp.toLp 2 e‖ := by
  -- `d = sep((λ), D₂)`
  have hl : (!![l] : Matrix (Fin 1) (Fin 1) ℝ).IsSymm := by
    ext i j
    fin_cases i; fin_cases j; rfl
  have hspec : spectrum ℝ (!![l] : Matrix (Fin 1) (Fin 1) ℝ) = {l} := by
    have h : l = symmEigenvalue hl 0 := by
      simpa [trace_fin_one] using trace_eq_sum_symmEigenvalue hl
    rw [spectrum_eq_range_symmEigenvalue hl, Set.range_unique]
    exact congrArg (fun x : ℝ => ({x} : Set ℝ)) h.symm
  have hsep : sepSymm !![l] D₂ = d := by
    rw [hd, sepSymm, hspec]
    congr 1
    ext x
    simp
  obtain ⟨P, hP, -, h⟩ := corollary_8_1_11 hA hQ hQ' hAQ (by rwa [hsep]) (by rwa [hsep])
  have hEe : ‖replicateCol (Fin 1) e‖ = ‖WithLp.toLp 2 e‖ := frobenius_norm_replicateCol e
  rw [hsep, ← he, hEe] at hP
  set p : Fin s → ℝ := fun i => P i 0 with hp
  have hPp : P = replicateCol (Fin 1) p := by
    ext i j
    rw [Fin.fin_one_eq_zero j]
    rfl
  have hPn : ‖P‖ = ‖WithLp.toLp 2 p‖ := by
    rw [hPp]
    exact frobenius_norm_replicateCol p
  refine ⟨p, hPn ▸ hP,
    fun qh₁ hqh => ?_⟩
  -- the square root of `1 + PᵀP` is the scalar `c = √(1 + pᵀp)`
  have hpp : 0 ≤ p ⬝ᵥ p := Finset.sum_nonneg fun i _ => mul_self_nonneg (p i)
  set c := √(1 + p ⬝ᵥ p) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 (by linarith)
  have hcc : c * c = 1 + p ⬝ᵥ p := Real.mul_self_sqrt (by linarith)
  have hPP : 1 + Pᵀ * P = (1 + p ⬝ᵥ p) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
    simp [hPp, Matrix.mul_apply, dotProduct]
  set S : Matrix (Fin 1) (Fin 1) ℝ := c • 1 with hS
  have hSs : S.IsSymm := by rw [hS, IsSymm, transpose_smul, transpose_one]
  have hSS : S * S = 1 + Pᵀ * P := by
    rw [hPP, hS, Matrix.smul_mul, Matrix.one_mul, smul_smul, hcc]
  have hSinv : S⁻¹ = c⁻¹ • 1 := inv_eq_left_inv (by
    rw [hS, Matrix.smul_mul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul])
  have hQh : (replicateCol (Fin 1) q₁ + Q₂ * P) * S⁻¹ = replicateCol (Fin 1) qh₁ := by
    rw [hSinv, Matrix.mul_smul, Matrix.mul_one, hqh]
    ext i j
    simp [hPp, Matrix.mul_apply, mulVec, dotProduct, mul_add]
  obtain ⟨horth, ⟨M, hM⟩, hdist⟩ := h S hSs hSS
  rw [hQh] at horth hM hdist
  rw [hsep, ← he, hEe, range_toEuclideanLin_replicateCol,
    range_toEuclideanLin_replicateCol] at hdist
  -- `q₁` and `qh₁` are unit vectors
  have hQQ := hQ
  rw [transpose_fromCols, fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_inj] at hQQ
  have hq₁ := norm_toLp_eq_one_of_transpose_mul_self hQQ.1
  have hqh₁ := norm_toLp_eq_one_of_transpose_mul_self horth
  have hgap := subspaceDist_span_singleton hq₁ hqh₁
  refine ⟨hqh₁, ⟨M 0 0, ?_⟩, hgap, hgap ▸ hdist⟩
  ext i
  have := congrFun (congrFun hM i) 0
  simpa [Matrix.mul_apply, mulVec, dotProduct, mul_comm] using this

end Frobenius

/-! ### Approximate invariant subspaces (§8.1.4) -/

/-- **Theorem 8.1.13** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ and
$S \in \mathbb{R}^{r \times r}$ be symmetric, and let $Q_1 \in \mathbb{R}^{n \times r}$ satisfy
$Q_1^T Q_1 = I_r$. Let $E_1 = A Q_1 - Q_1 S$. Then there is an injective map
$\sigma : \{1, \dots, r\} \to \{1, \dots, n\}$ such that
$$|\lambda_{\sigma(k)}(A) - \lambda_k(S)| \le \sqrt{2} \, \|E_1\|_2, \qquad k = 1, \dots, r.$$

**Reading.** The source says that there exist $\mu_1, \dots, \mu_r \in \lambda(A)$ with
$|\mu_k - \lambda_k(S)| \le \sqrt{2} \|E_1\|_2$. The theorem takes
$\mu_k = \lambda_{\sigma(k)}(A)$ with $\sigma$ injective, as the proof of the source produces
them: Weyl's inequality pairs the sorted eigenvalues of $A$ with those of
$B = \operatorname{diag}(S, Q_2^T A Q_2)$, among which the eigenvalues of $S$ sit at distinct
positions.

The map $\sigma$ is an embedding `Fin r ↪ Fin n`. The proof specializes
`Matrix.IsHermitian.exists_embedding_abs_sub_le_of_mul_sub_mul`. The unpaired form with constant
$1$ is `GolubVanLoan.Chapter08.theorem_8_1_13_weak`. -/
theorem theorem_8_1_13 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {r : ℕ}
    {S : Matrix (Fin r) (Fin r) ℝ} (hS : S.IsSymm) {Q₁ : Matrix (Fin n) (Fin r) ℝ}
    (hQ : Q₁ᵀ * Q₁ = 1) :
    ∃ σ : Fin r ↪ Fin n, ∀ k, |symmEigenvalue hA (σ k) - symmEigenvalue hS k| ≤
      √2 * lpOpNorm 2 (A * Q₁ - Q₁ * S) := by
  obtain ⟨σ, hσ⟩ := (isHermitian_iff_isSymm.2 hA).exists_embedding_abs_sub_le_of_mul_sub_mul
    (isHermitian_iff_isSymm.2 hS) (by rwa [conjTranspose_eq_transpose_of_trivial]) le_rfl
  refine ⟨(finCongr (Fintype.card_fin r).symm).toEmbedding.trans
    (σ.toEmbedding.trans (finCongr (Fintype.card_fin n)).toEmbedding), fun k => ?_⟩
  have h := hσ (Fin.cast (Fintype.card_fin r).symm k)
  simp only [symmEigenvalue, IsHermitian.sortedEigenvalues_apply, Function.Embedding.trans_apply,
    Equiv.coe_toEmbedding, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  exact h

/-- **Theorem 8.1.13** of [golub2013matrix], unpaired form. Let $A \in \mathbb{R}^{n \times n}$ and
$S \in \mathbb{R}^{r \times r}$ be symmetric, and let $Q_1 \in \mathbb{R}^{n \times r}$ satisfy
$Q_1^T Q_1 = I_r$. Then for every eigenvalue $\theta$ of $S$ there is an eigenvalue $\mu$ of $A$
with
$$|\mu - \theta| \le \|A Q_1 - Q_1 S\|_2.$$

The constant is $1$ instead of $\sqrt{2}$, but distinct eigenvalues $\theta$ need not get
distinct $\mu$, unlike `GolubVanLoan.Chapter08.theorem_8_1_13`. This form is not a corollary of
the paired form.

**Reading.** The source pairs eigenvalues with a factor $\sqrt{2}$. This version gives a
factor-one bound for a single projected eigenvalue, without requiring the choices for different
projected eigenvalues to be distinct. -/
theorem theorem_8_1_13_weak {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {r : ℕ}
    {S : Matrix (Fin r) (Fin r) ℝ} (hS : S.IsSymm) {Q₁ : Matrix (Fin n) (Fin r) ℝ}
    (hQ : Q₁ᵀ * Q₁ = 1) {θ : ℝ} (hθ : θ ∈ spectrum ℝ S) :
    ∃ μ ∈ spectrum ℝ A, |μ - θ| ≤ lpOpNorm 2 (A * Q₁ - Q₁ * S) :=
  (isHermitian_iff_isSymm.2 hA).exists_mem_spectrum_abs_sub_le_of_mul_sub_mul
    (isHermitian_iff_isSymm.2 hS) (by rwa [conjTranspose_eq_transpose_of_trivial]) le_rfl hθ

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Theorem 8.1.14** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$, and let
$Q_1 \in \mathbb{R}^{n \times r}$ have orthonormal columns. Then
$$\min_{S \in \mathbb{R}^{r \times r}} \|A Q_1 - Q_1 S\|_F = \|(I - Q_1 Q_1^T) A Q_1\|_F,$$
and the minimum is attained at $S = Q_1^T A Q_1$.

The statement says that the right side is the least element (`IsLeast`) of the set of values of
$\|A Q_1 - Q_1 S\|_F$. It is the value at $S = Q_1^T A Q_1$, since $(I - Q_1 Q_1^T) A Q_1 = A
Q_1 - Q_1 (Q_1^T A Q_1)$. The matrix $A$ need not be symmetric.

**Generalization.** The Frobenius minimum is stated for arbitrary real $A$. The source assumes
symmetry and identifies the attaining coefficient matrix explicitly; in Lean the stated minimum
value is attained at $Q_1^TAQ_1$ by the proof. -/
theorem theorem_8_1_14 (A : Matrix (Fin n) (Fin n) ℝ) {r : ℕ} {Q₁ : Matrix (Fin n) (Fin r) ℝ}
    (hQ : Q₁ᵀ * Q₁ = 1) :
    IsLeast (Set.range fun S : Matrix (Fin r) (Fin r) ℝ => ‖A * Q₁ - Q₁ * S‖)
      ‖(1 - Q₁ * Q₁ᵀ) * A * Q₁‖ := by
  have h := isLeast_frobenius_norm_mul_sub_mul A (Q := Q₁)
    (by rwa [conjTranspose_eq_transpose_of_trivial])
  rwa [conjTranspose_eq_transpose_of_trivial] at h

end Frobenius

/-- The residual identity behind Theorem 8.1.15: if $Z$ is orthogonal with $Z^T (Q_1^T A Q_1) Z =
\operatorname{diag}(\theta)$ and $y_k = Q_1 Z e_k$, then $A y_k - \theta_k y_k = (I - Q_1 Q_1^T)
A Q_1 Z e_k$. -/
private theorem ritz_residual_eq (A : Matrix (Fin n) (Fin n) ℝ) {r : ℕ}
    {Q₁ : Matrix (Fin n) (Fin r) ℝ} {Z : Matrix (Fin r) (Fin r) ℝ}
    (hZ : Z ∈ orthogonalGroup (Fin r) ℝ) {θ : Fin r → ℝ}
    (hZθ : Zᵀ * (Q₁ᵀ * A * Q₁) * Z = diagonal θ) (k : Fin r) :
    A *ᵥ (Q₁ * Z).col k - θ k • (Q₁ * Z).col k = ((1 - Q₁ * Q₁ᵀ) * A * Q₁) *ᵥ Z.col k := by
  have hZZ : Z * Zᵀ = 1 := (mem_orthogonalGroup_iff (Fin r) ℝ).1 hZ
  have hMZ : (Q₁ᵀ * A * Q₁) * Z = Z * diagonal θ := by
    rw [← hZθ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hZZ, Matrix.one_mul]
  have hcol : θ k • Z.col k = (Q₁ᵀ * A * Q₁) *ᵥ Z.col k := by
    rw [← col_mul_eq_mulVec_col, hMZ]
    ext i
    simp [col_apply, mul_diagonal, mul_comm]
  rw [col_mul_eq_mulVec_col, ← mulVec_smul, hcol, mulVec_mulVec, mulVec_mulVec, ← sub_mulVec]
  congr 1
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]

/-- **Theorem 8.1.15** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ and
$Q_1 \in \mathbb{R}^{n \times r}$, and let $Z \in \mathbb{R}^{r \times r}$ be orthogonal with
$$Z^T (Q_1^T A Q_1) Z = \operatorname{diag}(\theta_1, \dots, \theta_r).$$
Let $[y_1, \dots, y_r] = Q_1 Z$. Then for $k = 1, \dots, r$,
$$A y_k - \theta_k y_k = (I - Q_1 Q_1^T) A Q_1 Z e_k, \qquad \|A y_k - \theta_k y_k\|_2 \le
  \|(I - Q_1 Q_1^T) A Q_1\|_2.$$

**Generalization.** The source takes $Q_1$ with orthonormal columns. The identity and the bound
hold for every $Q_1$.

The matrix $A$ need not be symmetric. -/
theorem theorem_8_1_15 (A : Matrix (Fin n) (Fin n) ℝ) {r : ℕ} {Q₁ : Matrix (Fin n) (Fin r) ℝ}
    {Z : Matrix (Fin r) (Fin r) ℝ} (hZ : Z ∈ orthogonalGroup (Fin r) ℝ) {θ : Fin r → ℝ}
    (hZθ : Zᵀ * (Q₁ᵀ * A * Q₁) * Z = diagonal θ) (k : Fin r) :
    A *ᵥ (Q₁ * Z).col k - θ k • (Q₁ * Z).col k = ((1 - Q₁ * Q₁ᵀ) * A * Q₁) *ᵥ Z.col k ∧
      ‖WithLp.toLp 2 (A *ᵥ (Q₁ * Z).col k - θ k • (Q₁ * Z).col k)‖ ≤
        lpOpNorm 2 ((1 - Q₁ * Q₁ᵀ) * A * Q₁) := by
  refine ⟨ritz_residual_eq A hZ hZθ k, ?_⟩
  rw [ritz_residual_eq A hZ hZθ k, ← toEuclideanLin_toLp, lpOpNorm_two]
  have hZ' : Zᴴ * Z = 1 := by
    rw [conjTranspose_eq_transpose_of_trivial]; exact (mem_orthogonalGroup_iff' (Fin r) ℝ).1 hZ
  have hcol : ‖WithLp.toLp 2 (Z.col k)‖ = 1 := by
    rw [← mulVec_single_one, ← toEuclideanLin_toLp,
      norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one hZ']
    simp
  exact (norm_toEuclideanLin_apply_le _ _).trans_eq (by rw [hcol, mul_one])

/-- **Section 8.1.4** of [golub2013matrix], Ritz pairs. Let $A \in \mathbb{R}^{n \times n}$, let
$Q_1 \in \mathbb{R}^{n \times r}$ satisfy $Q_1^T Q_1 = I$, and let
$Z \in \mathbb{R}^{r \times r}$ be orthogonal with $Z^T (Q_1^T A Q_1) Z =
\operatorname{diag}(\theta_1, \dots, \theta_r)$ and $[y_1, \dots, y_r] = Q_1 Z$. Then:
* each $(\theta_k, y_k)$ is a Ritz pair of $A$ on $\operatorname{ran}(Q_1)$:
  $y_k \in \operatorname{ran}(Q_1)$, $y_k \neq 0$, and $A y_k - \theta_k y_k$ is orthogonal to
  $\operatorname{ran}(Q_1)$;
* conversely, every Ritz pair $(\mu, u)$ of $A$ on $\operatorname{ran}(Q_1)$ has $u = Q_1 w$ for
  some $w \neq 0$ with $(Q_1^T A Q_1) w = \mu w$.

A Ritz pair is `Krylov.IsRitzPair` for the operator `Matrix.toEuclideanLin A` and the subspace
`LinearMap.range (Matrix.toEuclideanLin Q₁)`.

**Reading.** The source names the pairs arising from the projected diagonalization. Lean
identifies those pairs with the Galerkin condition and proves the converse correspondence to
projected eigenvectors. -/
theorem ritzPair_isRitzPair (A : Matrix (Fin n) (Fin n) ℝ) {r : ℕ}
    {Q₁ : Matrix (Fin n) (Fin r) ℝ} (hQ : Q₁ᵀ * Q₁ = 1) {Z : Matrix (Fin r) (Fin r) ℝ}
    (hZ : Z ∈ orthogonalGroup (Fin r) ℝ) {θ : Fin r → ℝ}
    (hZθ : Zᵀ * (Q₁ᵀ * A * Q₁) * Z = diagonal θ) :
    (∀ k, Krylov.IsRitzPair (toEuclideanLin A) (LinearMap.range (toEuclideanLin Q₁)) (θ k)
      (WithLp.toLp 2 ((Q₁ * Z).col k))) ∧
    ∀ (μ : ℝ) (u : EuclideanSpace ℝ (Fin n)),
      Krylov.IsRitzPair (toEuclideanLin A) (LinearMap.range (toEuclideanLin Q₁)) μ u →
        ∃ w : Fin r → ℝ, w ≠ 0 ∧ u = WithLp.toLp 2 (Q₁ *ᵥ w) ∧ (Q₁ᵀ * A * Q₁) *ᵥ w = μ • w := by
  have hQ' : Q₁ᴴ * Q₁ = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  have hZ' : Zᴴ * Z = 1 := by
    rw [conjTranspose_eq_transpose_of_trivial]; exact (mem_orthogonalGroup_iff' (Fin r) ℝ).1 hZ
  -- `⟪Q₁ x, v⟫ = x ⬝ Q₁ᵀ v`
  have hinner : ∀ (x : Fin r → ℝ) (v : Fin n → ℝ),
      inner ℝ (WithLp.toLp 2 (Q₁ *ᵥ x) : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 v) =
        (Q₁ᵀ *ᵥ v) ⬝ᵥ x := fun x v => by
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_mulVec, mulVec_transpose]
  refine ⟨fun k => ⟨⟨WithLp.toLp 2 (Z.col k), by rw [toEuclideanLin_toLp, col_mul_eq_mulVec_col]⟩,
    fun h0 => ?_, ?_⟩, fun μ u hu => ?_⟩
  · have hn1 : ‖WithLp.toLp 2 ((Q₁ * Z).col k)‖ = 1 := by
      rw [col_mul_eq_mulVec_col, ← toEuclideanLin_toLp,
        norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one hQ', ← mulVec_single_one,
        ← toEuclideanLin_toLp, norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one hZ']
      simp
    rw [h0, norm_zero] at hn1
    exact zero_ne_one hn1
  · rw [Submodule.mem_orthogonal]
    rintro _ ⟨x, rfl⟩
    rw [toEuclideanLin_apply, toEuclideanLin_toLp, ← WithLp.toLp_smul, ← WithLp.toLp_sub,
      ritz_residual_eq A hZ hZθ k, hinner, mulVec_mulVec]
    have h0 : Q₁ᵀ * ((1 - Q₁ * Q₁ᵀ) * A * Q₁) = 0 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one,
        ← Matrix.mul_assoc, hQ, Matrix.one_mul, sub_self, Matrix.zero_mul, Matrix.zero_mul]
    rw [h0, zero_mulVec, zero_dotProduct]
  · obtain ⟨x, hx⟩ := hu.mem
    set w := WithLp.ofLp x
    have hu' : u = WithLp.toLp 2 (Q₁ *ᵥ w) := by rw [← hx, toEuclideanLin_apply]
    refine ⟨w, fun h0 => hu.ne_zero (by rw [hu', h0, mulVec_zero]; rfl), hu', ?_⟩
    have hres := hu.residual_mem_orthogonal
    rw [hu', toEuclideanLin_toLp, ← WithLp.toLp_smul, ← WithLp.toLp_sub,
      Submodule.mem_orthogonal] at hres
    have hr : Q₁ᵀ *ᵥ (A *ᵥ (Q₁ *ᵥ w) - μ • (Q₁ *ᵥ w)) = 0 := by
      ext j
      have := hres _ ⟨WithLp.toLp 2 (Pi.single j 1), rfl⟩
      rw [toEuclideanLin_toLp, hinner, dotProduct_single, mul_one] at this
      exact this
    rw [mulVec_sub, mulVec_smul, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, hQ, one_mulVec,
      sub_eq_zero] at hr
    exact hr

section L2

open scoped Matrix.Norms.L2Operator

/-- **Equation (8.1.5)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ and
$X_1, Q \in \mathbb{R}^{n \times r}$, and let $S = X_1^T A X_1$ and $F_1 = A X_1 - X_1 S$. Then
$E_1 = A Q - Q S$ satisfies
$$\|E_1\|_2 \le \|F_1\|_2 + \|Q - X_1\|_2 \, \|A\|_2 \, (1 + \|X_1\|_2^2).$$

**Generalization.** The source takes $Q$ with orthonormal columns. The bound holds for every
$Q$.

**Typo.** The source writes $\|Q-X\|_2$ where the difference in the preceding identity is
$Q-X_1$. -/
theorem equation_8_1_5 (A : Matrix (Fin n) (Fin n) ℝ) {r : ℕ} (X₁ Q : Matrix (Fin n) (Fin r) ℝ) :
    lpOpNorm 2 (A * Q - Q * (X₁ᵀ * A * X₁)) ≤ lpOpNorm 2 (A * X₁ - X₁ * (X₁ᵀ * A * X₁)) +
      lpOpNorm 2 (Q - X₁) * lpOpNorm 2 A * (1 + lpOpNorm 2 X₁ ^ 2) := by
  simp only [lpOpNorm_two]
  set S := X₁ᵀ * A * X₁
  have hS : ‖S‖ ≤ ‖X₁‖ ^ 2 * ‖A‖ := by
    calc ‖S‖ ≤ ‖X₁ᵀ * A‖ * ‖X₁‖ := l2_opNorm_mul _ _
      _ ≤ ‖X₁ᵀ‖ * ‖A‖ * ‖X₁‖ := by gcongr; exact l2_opNorm_mul _ _
      _ = ‖X₁‖ ^ 2 * ‖A‖ := by
        rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]; ring
  have heq : A * Q - Q * S = (A * X₁ - X₁ * S) + (A * (Q - X₁) - (Q - X₁) * S) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [heq]
  have h1 : ‖A * (Q - X₁)‖ ≤ ‖A‖ * ‖Q - X₁‖ := l2_opNorm_mul _ _
  have h2 : ‖(Q - X₁) * S‖ ≤ ‖Q - X₁‖ * (‖X₁‖ ^ 2 * ‖A‖) :=
    (l2_opNorm_mul _ _).trans (by gcongr)
  calc ‖(A * X₁ - X₁ * S) + (A * (Q - X₁) - (Q - X₁) * S)‖
      ≤ ‖A * X₁ - X₁ * S‖ + (‖A * (Q - X₁)‖ + ‖(Q - X₁) * S‖) :=
        (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ ‖A * X₁ - X₁ * S‖ + (‖A‖ * ‖Q - X₁‖ + ‖Q - X₁‖ * (‖X₁‖ ^ 2 * ‖A‖)) := by gcongr
    _ = _ := by ring

/-- **Equation (8.1.6)** of [golub2013matrix]. Let $X_1 \in \mathbb{R}^{n \times r}$ with
$\|X_1^T X_1 - I_r\|_2 = \tau$. Then $\|X_1\|_2^2 \le 1 + \tau$.

**Typo.** In the source’s intermediate norm the left factor is printed $X^T$. The matrix in the
orthogonality defect is $X_1^TX_1$. -/
theorem equation_8_1_6 {r : ℕ} (X₁ : Matrix (Fin n) (Fin r) ℝ) {τ : ℝ}
    (hτ : lpOpNorm 2 (X₁ᵀ * X₁ - 1) = τ) : lpOpNorm 2 X₁ ^ 2 ≤ 1 + τ := by
  have h1 : lpOpNorm 2 (1 : Matrix (Fin r) (Fin r) ℝ) ≤ 1 := by
    rw [lpOpNorm, lpCLM_one]; exact ContinuousLinearMap.norm_id_le
  rw [lpOpNorm_two] at h1 hτ ⊢
  rw [sq, ← l2_opNorm_conjTranspose_mul_self, conjTranspose_eq_transpose_of_trivial]
  calc ‖X₁ᵀ * X₁‖ = ‖(X₁ᵀ * X₁ - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ ‖X₁ᵀ * X₁ - 1‖ + ‖(1 : Matrix (Fin r) (Fin r) ℝ)‖ := norm_add_le _ _
    _ ≤ 1 + τ := by linarith

/-- If $\|X_1^T X_1 - I_r\|_2 < 1$, then $r \le n$: otherwise some $v \neq 0$ has $X_1 v = 0$, and
then $(X_1^T X_1 - I) v = -v$. -/
private theorem le_of_l2_opNorm_transpose_mul_self_sub_one_lt {r : ℕ}
    {X₁ : Matrix (Fin n) (Fin r) ℝ} (h : lpOpNorm 2 (X₁ᵀ * X₁ - 1) < 1) : r ≤ n := by
  by_contra hrn
  have hker : LinearMap.ker (toLin' X₁) ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp; omega)
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hker
  rw [LinearMap.mem_ker, toLin'_apply] at hv
  have hmv : (X₁ᵀ * X₁ - 1) *ᵥ v = -v := by
    rw [sub_mulVec, ← mulVec_mulVec, hv, mulVec_zero, one_mulVec, zero_sub]
  have hle := lpSeminorm_mulVec_le (r := 2) (X₁ᵀ * X₁ - 1) v
  rw [hmv, lpSeminorm_apply, lpSeminorm_apply, WithLp.toLp_neg, norm_neg] at hle
  have hpos : 0 < ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin r))‖ :=
    norm_pos_iff.2 (fun h0 => hv0 (by simpa using congrArg WithLp.ofLp h0))
  nlinarith

/-- **Equation (8.1.7)** of [golub2013matrix], in the proof of Theorem 8.1.16. Let
$X_1 \in \mathbb{R}^{n \times r}$ with $\|X_1^T X_1 - I_r\|_2 = \tau < 1$. Then there is
$Q \in \mathbb{R}^{n \times r}$ with $Q^T Q = I_r$ and
$$\|Q - X_1\|_2 \le \tau.$$

The matrix $Q$ is the $Q = U V^T$ of the source, from the thin SVD $U^T X_1 V = \Sigma$, that
is, the polar factor of $X_1$ (`Matrix.exists_orthonormal_cols_norm_sub_le`).

**Correction.** The source equates $\tau$ with $1-\sigma_r^2$ and $\|Q-X_1\|_2$ with
$1-\sigma_r$. A singular value above one can instead determine either norm. The bound uses
$|1-\sigma_i| \le |1-\sigma_i^2|$ for every singular value. -/
theorem equation_8_1_7 {r : ℕ} (X₁ : Matrix (Fin n) (Fin r) ℝ) {τ : ℝ}
    (hτ : lpOpNorm 2 (X₁ᵀ * X₁ - 1) = τ) (hτ1 : τ < 1) :
    ∃ Q : Matrix (Fin n) (Fin r) ℝ, Qᵀ * Q = 1 ∧ lpOpNorm 2 (Q - X₁) ≤ τ := by
  have hr := le_of_l2_opNorm_transpose_mul_self_sub_one_lt (hτ ▸ hτ1)
  obtain ⟨Q, hQ, -, hle⟩ := exists_orthonormal_cols_norm_sub_le X₁ (by simpa using hr)
    (by rw [conjTranspose_eq_transpose_of_trivial, hτ]) hτ1
  exact ⟨Q, by rwa [conjTranspose_eq_transpose_of_trivial] at hQ, hle⟩

end L2

/-- **Theorem 8.1.16** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric, let
$X_1 \in \mathbb{R}^{n \times r}$, and let $S = X_1^T A X_1$ and $F_1 = A X_1 - X_1 S$. If
$\|X_1^T X_1 - I_r\|_2 = \tau < 1$, which is (8.1.4), then there is an injective map
$\sigma : \{1, \dots, r\} \to \{1, \dots, n\}$ such that
$$|\lambda_{\sigma(k)}(A) - \lambda_k(S)| \le \sqrt{2} \left(\|F_1\|_2 + \tau (2 + \tau)
  \|A\|_2\right), \qquad k = 1, \dots, r.$$

**Reading.** The source says that there exist $\mu_1, \dots, \mu_r \in \lambda(A)$ with this
bound. As in Theorem 8.1.13, the theorem takes $\mu_k = \lambda_{\sigma(k)}(A)$ with $\sigma$
injective.

The proof follows the source: (8.1.7) gives $Q$ with orthonormal columns and
$\|Q - X_1\|_2 \le \tau$; (8.1.5) with (8.1.6) gives $\|A Q - Q S\|_2 \le \|F_1\|_2 + \tau (2 +
\tau) \|A\|_2$; and Theorem 8.1.13 applies to $Q$. The symmetry of $S$ is
`hA.transpose_mul_mul X₁`. -/
theorem theorem_8_1_16 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {r : ℕ}
    (X₁ : Matrix (Fin n) (Fin r) ℝ) {τ : ℝ} (hτ : lpOpNorm 2 (X₁ᵀ * X₁ - 1) = τ) (hτ1 : τ < 1) :
    ∃ σ : Fin r ↪ Fin n, ∀ k,
      |symmEigenvalue hA (σ k) - symmEigenvalue (hA.transpose_mul_mul X₁) k| ≤
        √2 * (lpOpNorm 2 (A * X₁ - X₁ * (X₁ᵀ * A * X₁)) + τ * (2 + τ) * lpOpNorm 2 A) := by
  obtain ⟨Q, hQ, hQX⟩ := equation_8_1_7 X₁ hτ hτ1
  obtain ⟨σ, hσ⟩ := theorem_8_1_13 hA (hA.transpose_mul_mul X₁) hQ
  refine ⟨σ, fun k => (hσ k).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2))⟩
  have h5 := equation_8_1_5 A X₁ Q
  have h6 := equation_8_1_6 X₁ hτ
  have hτ0 : 0 ≤ τ := hτ ▸ lpOpNorm_nonneg _ _
  have hA0 : 0 ≤ lpOpNorm 2 A := lpOpNorm_nonneg _ _
  have h7 : lpOpNorm 2 (Q - X₁) * lpOpNorm 2 A * (1 + lpOpNorm 2 X₁ ^ 2) ≤
      τ * (2 + τ) * lpOpNorm 2 A := by
    have h8 : 1 + lpOpNorm 2 X₁ ^ 2 ≤ 2 + τ := by linarith
    calc lpOpNorm 2 (Q - X₁) * lpOpNorm 2 A * (1 + lpOpNorm 2 X₁ ^ 2)
        ≤ τ * lpOpNorm 2 A * (2 + τ) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hQX hA0) h8 (by positivity)
            (mul_nonneg hτ0 hA0)
      _ = τ * (2 + τ) * lpOpNorm 2 A := by ring
  linarith

/-! ### The law of inertia (§8.1.5) -/

/-- **Section 8.1.5** of [golub2013matrix], the inertia. The **inertia** of a symmetric
$A \in \mathbb{R}^{n \times n}$ is the triple $(m, z, p)$ of the numbers of negative, zero and
positive eigenvalues of $A$, counted with multiplicity.

The definition is the backbone's `Matrix.IsHermitian.inertia`. -/
noncomputable def inertia {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) : ℕ × ℕ × ℕ :=
  (isHermitian_iff_isSymm.2 hA).inertia

/-- The inertia $(m, z, p)$ of a symmetric $A$ counts the $\lambda_k(A)$ that are negative, zero and
positive. -/
theorem inertia_eq {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    inertia hA = ((Finset.univ.filter fun k => symmEigenvalue hA k < 0).card,
      (Finset.univ.filter fun k => symmEigenvalue hA k = 0).card,
      (Finset.univ.filter fun k => 0 < symmEigenvalue hA k).card) := by
  have hH := isHermitian_iff_isSymm.2 hA
  rw [inertia, hH.inertia_eq_eigenvalues₀]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact (Finset.card_filter_comp_equiv (finCongr (Fintype.card_fin n).symm)
      (fun j => hH.eigenvalues₀ j < 0)).symm
  · exact (Finset.card_filter_comp_equiv (finCongr (Fintype.card_fin n).symm)
      (fun j => hH.eigenvalues₀ j = 0)).symm
  · exact (Finset.card_filter_comp_equiv (finCongr (Fintype.card_fin n).symm)
      (fun j => 0 < hH.eigenvalues₀ j)).symm

/-- For every property $p$ of real numbers, the number of $\lambda_k(A)$ with property $p$ equals
the number of entries of Mathlib's `Matrix.IsHermitian.eigenvalues` with property $p$. -/
theorem card_filter_symmEigenvalue {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (p : ℝ → Prop)
    [DecidablePred p] :
    (Finset.univ.filter fun k => p (symmEigenvalue hA k)).card =
      (Finset.univ.filter fun i => p ((isHermitian_iff_isSymm.2 hA).eigenvalues i)).card :=
  (Finset.card_filter_comp_equiv (finCongr (Fintype.card_fin n).symm)
    (fun j => p ((isHermitian_iff_isSymm.2 hA).eigenvalues₀ j))).trans
    (Finset.card_filter_comp_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      (fun j => p ((isHermitian_iff_isSymm.2 hA).eigenvalues₀ j))).symm

/-- The inertia depends only on the matrix, not on the proof of its symmetry. -/
private theorem inertia_congr {A B : Matrix (Fin n) (Fin n) ℝ} (h : A = B) (hA : A.IsSymm)
    (hB : B.IsSymm) : inertia hA = inertia hB := by
  subst h
  rfl

/-- **Theorem 8.1.17** of [golub2013matrix] (Sylvester law of inertia). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric and $X \in \mathbb{R}^{n \times n}$ nonsingular.
Then $A$ and $X^T A X$ have the same inertia.

The Lean statement also takes a proof that $X^T A X$ is symmetric. Nonsingularity is
`IsUnit X.det`. -/
theorem theorem_8_1_17 {A X : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hX : IsUnit X.det)
    (hXAX : (Xᵀ * A * X).IsSymm) : inertia hXAX = inertia hA := by
  have hc : Xᴴ * A * X = Xᵀ * A * X := by rw [conjTranspose_eq_transpose_of_trivial]
  have h := (isHermitian_iff_isSymm.2 hA).inertia_conj ((isUnit_iff_isUnit_det X).2 hX)
  rw [← inertia_congr hc (by rw [hc]; exact hA.transpose_mul_mul X) hXAX]
  exact h

end GolubVanLoan.Chapter08
