/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.Analysis.Matrix.SingularValues
import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.LeastSquares
import NumlibSurface.GolubVanLoan.Chapter02.Section06
import NumlibSurface.GolubVanLoan.Chapter05.Section01

/-!
# Golub and Van Loan, Section 5.2: The QR factorization

This module formalizes §5.2 of [golub2013matrix], the QR factorization $A = QR$ of
$A \in \mathbb{R}^{m \times n}$, with $Q \in \mathbb{R}^{m \times m}$ orthogonal and
$R \in \mathbb{R}^{m \times n}$ upper triangular. Theorem 5.2.1 says that every $A$ has such a
factorization. If $A$ has full column rank, Theorem 5.2.2 says that the first $k$ columns of $A$ and
of $Q$ span the same space, that $\operatorname{ran}(A) = \operatorname{ran}(Q_1)$ and
$\operatorname{ran}(A)^\perp = \operatorname{ran}(Q_2)$ for $Q_1 = Q(1{:}m, 1{:}n)$ and
$Q_2 = Q(1{:}m, n{+}1{:}m)$, and that $A = Q_1 R_1$ is a thin QR factorization. Theorem 5.2.3 says
that the thin factorization with a positive diagonal of $R_1$ is unique and that $R_1^T$ is the
Cholesky factor of $A^T A$. The 2-norm condition number of a rectangular matrix of full column rank
is $\kappa_2(A) = \sigma_{\max}(A)/\sigma_{\min}(A)$ (5.2.4).

The module defines the QR algorithms of the section as programs and proves that in exact arithmetic
they compute a QR factorization: Householder QR (Algorithm 5.2.1), block Householder QR (Algorithm
5.2.2), recursive block Householder QR (Algorithm 5.2.3), Givens QR (Algorithm 5.2.4) with its two
reorderings, Hessenberg QR (Algorithm 5.2.5), classical Gram–Schmidt and modified Gram–Schmidt
(Algorithm 5.2.6). For Householder QR, Givens QR and Hessenberg QR it also proves backward error
bounds $Z \hat R = A + E$ with $Z$ orthogonal and a columnwise bound on $E$. The exact statements
specialize `Numlib.LinearAlgebra.Matrix.QR`, `Numlib.LinearAlgebra.Matrix.Cholesky` and
`Numlib.Analysis.Matrix.SingularValues`. The rounding statements build on the Householder and Givens
programs of §5.1 and on `Numlib.FloatingPoint.Householder`.

## Main definitions

* (5.2.4), `GolubVanLoan.Chapter05.kappa2`: the condition number $\kappa_2(A) = \|A\|_2 \|A^+\|_2$
  of a rectangular matrix.
* Algorithm 5.2.1, `GolubVanLoan.Chapter05.upperPart`: the upper triangular part of an overwritten
  array.
* Algorithm 5.2.1, `GolubVanLoan.Chapter05.algorithm_5_2_1`: Householder QR, with the step
  `GolubVanLoan.Chapter05.householderQRStep`.
* Algorithm 5.2.2, `GolubVanLoan.Chapter05.algorithm_5_2_2`: block Householder QR, with one pass
  `GolubVanLoan.Chapter05.blockQRPanel`.
* Algorithm 5.2.3, `GolubVanLoan.Chapter05.algorithm_5_2_3`: recursive block Householder QR.
* Algorithm 5.2.4, `GolubVanLoan.Chapter05.algorithm_5_2_4`: Givens QR.
* §5.2.5, `GolubVanLoan.Chapter05.givensQRDiagonalPivot` and `GolubVanLoan.Chapter05.givensQRByRow`:
  the two reorderings of Givens QR.
* Algorithm 5.2.5, `GolubVanLoan.Chapter05.algorithm_5_2_5`: Hessenberg QR.
* §6.5.1, `GolubVanLoan.Chapter05.givensHessenbergSweep` and
  `GolubVanLoan.Chapter05.givensVectorSweep`: the two Givens sweeps of the updating procedures of
  §6.5.
* §5.2.7, `GolubVanLoan.Chapter05.classicalGramSchmidt`: classical Gram–Schmidt.
* Algorithm 5.2.6, `GolubVanLoan.Chapter05.algorithm_5_2_6`: modified Gram–Schmidt.

## Main results

* Theorem 5.2.1, `GolubVanLoan.Chapter05.theorem_5_2_1`: every real matrix has a QR factorization.
* Theorem 5.2.2, `GolubVanLoan.Chapter05.theorem_5_2_2`: for full column rank, the span identities
  (5.2.1), $r_{kk} \neq 0$, the ranges of $Q_1$ and $Q_2$, and $A = Q_1 R_1$.
* (5.2.1), `GolubVanLoan.Chapter05.equation_5_2_1`: the first $k$ columns of $A$ and of $Q$ span the
  same space, and $r_{kk} \neq 0$.
* (5.2.2), `GolubVanLoan.Chapter05.equation_5_2_2`: $A = Q_1 R_1$ is a thin QR factorization.
* (5.2.3), `GolubVanLoan.Chapter05.equation_5_2_3`: $a_k = \sum_{i \le k} r_{ik} q_i$.
* Theorem 5.2.3, `GolubVanLoan.Chapter05.theorem_5_2_3`: existence and uniqueness of the thin QR
  factorization with positive diagonal, and $R_1^T$ is the Cholesky factor of $A^T A$.
* (5.2.4), `GolubVanLoan.Chapter05.equation_5_2_4`: $\kappa_2(A) =
  \sigma_{\max}(A)/\sigma_{\min}(A)$ for full column rank.
* Algorithm 5.2.1, `GolubVanLoan.Chapter05.algorithm_5_2_1_spec`: in exact arithmetic, the factored
  form of the stored Householder vectors and the upper triangular part of the output give $A = QR$.
* §5.2.2, `GolubVanLoan.Chapter05.equation_5_1_4_beta`: the formula
  $\beta_j = 2/(1 + \|A(j{+}1{:}m, j)\|_2^2)$ recovers every nonzero $\beta_j$.
* §5.2.2, `GolubVanLoan.Chapter05.algorithm_5_2_1_rounding`: the computed $\hat R$ satisfies
  $Z \hat R = A + E$ with $Z$ orthogonal and a columnwise bound on $E$;
  `GolubVanLoan.Chapter05.algorithm_5_2_1_run_nonempty` shows that the statement is not vacuous.
* Algorithm 5.2.2, `GolubVanLoan.Chapter05.algorithm_5_2_2_spec`: in exact arithmetic, block
  Householder QR computes $A = QR$.
* Algorithm 5.2.3, `GolubVanLoan.Chapter05.algorithm_5_2_3_spec`: in exact arithmetic, recursive
  block Householder QR computes a thin QR factorization.
* Algorithm 5.2.4, `GolubVanLoan.Chapter05.algorithm_5_2_4_spec` and
  `GolubVanLoan.Chapter05.algorithm_5_2_4_rounding`: Givens QR computes $A = QR$ in exact
  arithmetic, and its computed $\hat R$ has a columnwise backward error bound.
* §5.2.5, `GolubVanLoan.Chapter05.givensQRDiagonalPivot_spec` and
  `GolubVanLoan.Chapter05.givensQRByRow_spec`: the two reorderings also compute $A = QR$.
* Algorithm 5.2.5, `GolubVanLoan.Chapter05.algorithm_5_2_5_spec` and
  `GolubVanLoan.Chapter05.algorithm_5_2_5_rounding`: Hessenberg QR computes $A = QR$ with an upper
  Hessenberg $Q$ in exact arithmetic, and its computed $\hat R$ has a columnwise backward error
  bound.
* §6.5.1, `GolubVanLoan.Chapter05.givensHessenbergSweep_spec` and
  `GolubVanLoan.Chapter05.givensVectorSweep_spec`: the exact semantics of the two Givens sweeps.
* §5.2.7, `GolubVanLoan.Chapter05.classicalGramSchmidt_eq_gramSchmidt` and
  `GolubVanLoan.Chapter05.classicalGramSchmidt_spec`: classical Gram–Schmidt computes the
  Gram–Schmidt factors, a thin QR factorization for full column rank.
* Algorithm 5.2.6, `GolubVanLoan.Chapter05.algorithm_5_2_6_eq_gramSchmidt` and
  `GolubVanLoan.Chapter05.algorithm_5_2_6_spec`: the same for modified Gram–Schmidt.
* §5.2.8, `GolubVanLoan.Chapter05.algorithm_5_2_6_eq_classicalGramSchmidt` and
  `GolubVanLoan.Chapter05.mgs_remainder_eq`: in exact arithmetic the two Gram–Schmidt algorithms
  compute the same factors, and the derivation of modified Gram–Schmidt.
* §5.2.10, `GolubVanLoan.Chapter05.complexHouseholderQR`: every complex matrix has a QR
  factorization with a unitary $Q$.

## Conventions

* Indices are 0-based. The source's column $j$ is the index $j - 1$, and a block $A(j{:}m, j{:}n)$
  is the full array together with the index lists `GolubVanLoan.Chapter05.indexFrom m j` and
  `GolubVanLoan.Chapter05.indexFrom n j`.
* "$A$ has full column rank" is `LinearIndependent ℝ Aᵀ`.
* The full QR factorization is `Matrix.IsQR A Q R`: $Q$ is unitary (orthogonal over $\mathbb{R}$),
  $R$ vanishes below the diagonal, and $QR = A$. The thin factorization is `Matrix.IsThinQR A Q R`:
  $QR = A$, $Q^T Q = I$ and $R$ is upper triangular, with no condition on the sign of the diagonal.
* An algorithm that overwrites $A$ is read through `GolubVanLoan.Chapter05.upperPart`, the upper
  triangular part of its output. For Householder QR, $Q$ is the factored form
  `GolubVanLoan.Chapter05.factoredQ β A'` of §5.1.6, built with the $\beta$ that the program
  returned and not with a $\beta$ recomputed from the stored vector.
* The source's approximate error statements, such as $\|E\|_2 \approx u \|A\|_2$, are stated as
  rigorous columnwise bounds with explicit constants $\gamma_k = ku/(1 - ku)$.

## Implementation notes

* Each algorithm is one program, generic in a monad and a rounding hook
  (`Numlib.FloatingPoint.Program`). The exact specification `_spec` uses the monad `Id` and the hook
  `pure`; the rounding theorem `_rounding` is about every run in the relational rounding model `fp`.
* A Householder step on $A(j{:}m, j{:}n)$ is `GolubVanLoan.Chapter05.houseOn` followed by
  `GolubVanLoan.Chapter05.householderApplyLeft` on the full array, and a Givens step is
  `GolubVanLoan.Chapter05.givensApplyLeft` on its list of columns.
* The backward error of Algorithm 5.2.1 is also stated with its reflector data
  (`GolubVanLoan.Chapter05.householderQRStep_rounding_data`,
  `GolubVanLoan.Chapter05.algorithm_5_2_1_rounding_data`), the form that Algorithm 5.3.2 of §5.3
  uses.
* The two Givens sweeps of §6.5, `GolubVanLoan.Chapter05.givensHessenbergSweep` and
  `GolubVanLoan.Chapter05.givensVectorSweep`, are defined here beside Algorithm 5.2.5, with the
  exact step `GolubVanLoan.Chapter05.givensPairStep`, so that all updating procedures of §6.5 share
  them.
* Classical and modified Gram–Schmidt compute, for every $A$, the Gram–Schmidt factors
  `Matrix.gramSchmidtQ` and `Matrix.gramSchmidtR` of the backbone. Their QR specifications follow
  from `Matrix.isThinQR_gramSchmidtQ`.
* `GolubVanLoan.Chapter05.kappa2` is defined for every $A$ through the pseudoinverse; the source's
  $\sigma_{\max}/\sigma_{\min}$ is the theorem `GolubVanLoan.Chapter05.equation_5_2_4`.
* The correctness of Algorithm 5.2.2 is proved by showing that in exact arithmetic it computes the
  same $Q$ and the same array as Algorithm 5.2.1 (`GolubVanLoan.Chapter05.algorithm_5_2_2_eq`).

## Deviations from the source

* **§5.2.2, the formula $\beta_j = 2/(1 + \|A(j{+}1{:}m, j)\|_2^2)$** (correction). The formula
  gives $2$ where `house` returned $\beta_j = 0$; it is stated only for the nonzero $\beta_j$. See
  `GolubVanLoan.Chapter05.equation_5_1_4_beta`.
* **(5.2.2)** (generalization). The source states it under the full column rank hypothesis of
  Theorem 5.2.2; it holds for every QR factorization with $m \ge n$. See
  `GolubVanLoan.Chapter05.equation_5_2_2`.
* **Algorithm 5.2.2** (reading). The source does not restrict $m$ and $n$; the specification assumes
  $m \ge n$, which its panel factorization by Algorithm 5.2.1 needs. See
  `GolubVanLoan.Chapter05.algorithm_5_2_2_spec`.
* **Algorithm 5.2.3** (generalization). The source assumes that the block size $n_b$ is a positive
  integer; the exact specification holds for every $n_b \ge 0$. See
  `GolubVanLoan.Chapter05.algorithm_5_2_3_spec`.
* **Algorithm 5.2.4** (generalization). The source assumes $m \ge n$; the exact specification and
  the backward error bound hold for all $m$ and $n$. See
  `GolubVanLoan.Chapter05.algorithm_5_2_4_spec` and
  `GolubVanLoan.Chapter05.algorithm_5_2_4_rounding`.

## Not formalized

* **Stewart's perturbation bound $O(\varepsilon \kappa_2(A))$ for the QR factors (§5.2.1).** The
  source quotes it without a statement.
* **The roundoff properties of Algorithm 5.2.2.** The source says only that they are essentially the
  same as those of Algorithm 5.2.1.
* **The roundoff properties of Gram–Schmidt (§5.2.9).** The source quotes them without derivation.
* **The orthogonality $\hat Q_1^T \hat Q_1 = I + E_H$, $\|E_H\|_2 \approx u$, of the Householder $Q$
  accumulated in floating point (§5.2.9).** No rounding theorem for
  `GolubVanLoan.Chapter05.forwardAccumulation` or `GolubVanLoan.Chapter05.backwardAccumulation` is
  stated.
* **Flop counts, level-3 fractions and parallel Givens orderings.**
-/

open FloatingPoint Matrix WithLp

namespace GolubVanLoan.Chapter05

variable {m n : ℕ}

/-! ### §5.2.1 Existence and properties -/

section Existence

/-- **Theorem 5.2.1** of [golub2013matrix] (QR factorization). For every
$A \in \mathbb{R}^{m \times n}$ there are an orthogonal $Q \in \mathbb{R}^{m \times m}$ and an
upper triangular $R \in \mathbb{R}^{m \times n}$ with $A = QR$.

"Upper triangular" means $r_{ij} = 0$ for $j < i$. The proof specializes `Matrix.exists_isQR`. -/
theorem theorem_5_2_1 (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ Q ∈ orthogonalGroup (Fin m) ℝ, ∃ R : Matrix (Fin m) (Fin n) ℝ,
      (∀ (i : Fin m) (j : Fin n), (j : ℕ) < i → R i j = 0) ∧ A = Q * R := by
  obtain ⟨Q, R, h⟩ := exists_isQR A
  exact ⟨Q, h.mem_unitaryGroup, R, h.apply_eq_zero, h.mul_eq.symm⟩

/-- **Equation (5.2.3)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$, and let $A = QR$
be a QR factorization, with $Q$ orthogonal and $R$ upper triangular. Then for every column index
$k$,
$$a_k = \sum_{i \le k} r_{ik} q_i,$$
where $a_k$ is column $k$ of $A$ and $q_i$ is column $i$ of $Q$.

The source obtains (5.2.3) in the proof of Theorem 5.2.2 by comparing the $k$-th columns of
$A = QR$; the statement needs no rank hypothesis. The factorization is `Matrix.IsQR`. -/
theorem equation_5_2_3 {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
    {R : Matrix (Fin m) (Fin n) ℝ} (h : IsQR A Q R) (k : Fin n) :
    A.col k = ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) ≤ k), R i k • Q.col i := by
  ext p
  rw [← h.mul_eq, Finset.sum_apply, col_apply, Matrix.mul_apply,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => (i : ℕ) ≤ k)]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) ≤ k)) fun i hi => by
    rw [h.apply_eq_zero i k (by simpa using hi), mul_zero], add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

/-- **Equation (5.2.1)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ have full column
rank, with $n \le m$, and let $A = QR$ be a QR factorization. Then for every $k = 0, \dots, n$,
$$\operatorname{span}\{a_1, \dots, a_k\} = \operatorname{span}\{q_1, \dots, q_k\},$$
and every diagonal entry $r_{kk}$ of $R$ is nonzero.

The first $k$ columns are indexed through `Fin.castLE`. Full column rank is
`LinearIndependent ℝ Aᵀ`. -/
theorem equation_5_2_1 {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
    {R : Matrix (Fin m) (Fin n) ℝ} (h : IsQR A Q R) (hA : LinearIndependent ℝ Aᵀ) (hnm : n ≤ m)
    {k : ℕ} (hk : k ≤ n) :
    Submodule.span ℝ (Set.range fun j : Fin k => A.col (Fin.castLE hk j)) =
        Submodule.span ℝ (Set.range fun i : Fin k => Q.col (Fin.castLE (hk.trans hnm) i)) ∧
      ∀ (i : Fin m) (j : Fin n), (i : ℕ) = j → R i j ≠ 0 :=
  h.span_col_prefix_eq hA hnm hk

/-- **Equation (5.2.2)** of [golub2013matrix] (the thin QR factorization). Let
$A \in \mathbb{R}^{m \times n}$ with $n \le m$, let $A = QR$ be a QR factorization, and let
$Q_1 = Q(1{:}m, 1{:}n)$ and $R_1 = R(1{:}n, 1{:}n)$. Then $A = Q_1 R_1$, and this is a thin QR
factorization: $Q_1$ has orthonormal columns and $R_1$ is upper triangular.

**Generalization.** In the source, (5.2.2) is part of Theorem 5.2.2, which assumes that $A$ has
full column rank. The statement here holds without this assumption.

$Q_1$ is `Matrix.firstColumns Q hnm`, $R_1$ is `Matrix.firstRows R hnm`, and the thin
factorization is `Matrix.IsThinQR`. -/
theorem equation_5_2_2 {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
    {R : Matrix (Fin m) (Fin n) ℝ} (h : IsQR A Q R) (hnm : n ≤ m) :
    Q.firstColumns hnm * R.firstRows hnm = A ∧ IsThinQR A (Q.firstColumns hnm) (R.firstRows hnm) :=
  ⟨h.firstColumns_mul_firstRows hnm, h.isThinQR hnm⟩

/-- **Theorem 5.2.2** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ have full column
rank, with $n \le m$, and let $A = QR$ be a QR factorization. Let $Q_1 = Q(1{:}m, 1{:}n)$,
$Q_2 = Q(1{:}m, n{+}1{:}m)$ and $R_1 = R(1{:}n, 1{:}n)$. Then:

* $\operatorname{span}\{a_1, \dots, a_k\} = \operatorname{span}\{q_1, \dots, q_k\}$ for
  $k = 0, \dots, n$ (5.2.1);
* every diagonal entry $r_{kk}$ of $R$ is nonzero;
* $\operatorname{ran}(A) = \operatorname{ran}(Q_1)$;
* $\operatorname{ran}(A)^\perp = \operatorname{ran}(Q_2)$;
* $A = Q_1 R_1$ (5.2.2).

The ranges $\operatorname{ran}(Q_1)$ and $\operatorname{ran}(A)$ are the spans of the rows of
$Q_1^T$ and $A^T$. The complement $\operatorname{ran}(A)^\perp$ is taken in
`EuclideanSpace ℝ (Fin m)`, and $\operatorname{ran}(Q_2)$ is the span of the columns $q_i$ with
0-based index $i \ge n$. -/
theorem theorem_5_2_2 {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
    {R : Matrix (Fin m) (Fin n) ℝ} (h : IsQR A Q R) (hA : LinearIndependent ℝ Aᵀ)
    (hnm : n ≤ m) :
    (∀ k (hk : k ≤ n),
      Submodule.span ℝ (Set.range fun j : Fin k => A.col (Fin.castLE hk j)) =
        Submodule.span ℝ (Set.range fun i : Fin k => Q.col (Fin.castLE (hk.trans hnm) i))) ∧
      (∀ (i : Fin m) (j : Fin n), (i : ℕ) = j → R i j ≠ 0) ∧
      Submodule.span ℝ (Set.range (Q.firstColumns hnm)ᵀ) = Submodule.span ℝ (Set.range Aᵀ) ∧
      (toEuclideanLin A).rangeᗮ =
        Submodule.span ℝ (Set.range fun i : {i : Fin m // n ≤ i} => toLp 2 (Qᵀ i)) ∧
      Q.firstColumns hnm * R.firstRows hnm = A := by
  have hset : (Set.range fun j : Fin (m - n) =>
      toLp 2 ((Q.lastColumns (Nat.sub_le m n))ᵀ j)) =
        Set.range fun i : {i : Fin m // n ≤ i} => toLp 2 (Qᵀ i) := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨⟨⟨m - (m - n) + j, by omega⟩, show n ≤ m - (m - n) + (j : ℕ) by omega⟩, rfl⟩
    · rintro ⟨⟨i, hi⟩, rfl⟩
      refine ⟨⟨i - n, by omega⟩, congrArg (toLp 2) (funext fun r => ?_)⟩
      simp only [transpose_apply, lastColumns_apply]
      congr 1
      ext
      simp only
      omega
  exact ⟨fun _ hk => (equation_5_2_1 h hA hnm hk).1, (equation_5_2_1 h hA hnm le_rfl).2,
    h.span_firstColumns_eq hnm hA, (h.range_orthogonal_eq_span_lastColumns hnm hA).trans
      (congrArg _ hset), (equation_5_2_2 h hnm).1⟩

/-- **Theorem 5.2.3** of [golub2013matrix] (thin QR factorization). Let
$A \in \mathbb{R}^{m \times n}$ have full column rank. Then:

* $A$ has a thin QR factorization $A = Q_1 R_1$, where $Q_1 \in \mathbb{R}^{m \times n}$ has
  orthonormal columns and $R_1 \in \mathbb{R}^{n \times n}$ is upper triangular with positive
  diagonal entries;
* this factorization is unique;
* $R_1 = G^T$, where $G$ is the lower triangular Cholesky factor of $A^T A$.

The thin factorization is `Matrix.IsThinQR`. The third part is `Matrix.IsCholesky (Aᵀ * A) R₁`:
$R_1$ is upper triangular with positive diagonal and $R_1^T R_1 = A^T A$. -/
theorem theorem_5_2_3 {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ) :
    (∃ Q R, IsThinQR A Q R ∧ ∀ j, 0 < R j j) ∧
      (∀ Q₁ Q₂ R₁ R₂, IsThinQR A Q₁ R₁ → IsThinQR A Q₂ R₂ → (∀ j, 0 < R₁ j j) →
        (∀ j, 0 < R₂ j j) → Q₁ = Q₂ ∧ R₁ = R₂) ∧
      ∀ Q R, IsThinQR A Q R → (∀ j, 0 < R j j) → IsCholesky (Aᵀ * A) R := by
  refine ⟨exists_isThinQR A hA, fun _ _ _ _ h₁ h₂ hd₁ hd₂ => h₁.unique h₂ hd₁ hd₂,
    fun Q R h hd => ?_⟩
  have := h.isCholesky hd
  rwa [conjTranspose_eq_transpose_of_trivial] at this

/-- **Equation (5.2.4)** of [golub2013matrix], the 2-norm condition number of a rectangular matrix.
For $A \in \mathbb{R}^{m \times n}$,
$$\kappa_2(A) = \|A\|_2 \, \|A^+\|_2,$$
where $A^+$ is the pseudoinverse of $A$.

The source defines $\kappa_2(A) = \sigma_{\max}(A)/\sigma_{\min}(A)$ for rectangular matrices
with full column rank. The definition here applies to every $A$. For full column rank it is
$\sigma_{\max}(A)/\sigma_{\min}(A)$ (`GolubVanLoan.Chapter05.equation_5_2_4`), and for a
nonsingular square $A$ it is the $\kappa_2(A)$ of §2.6.2
(`GolubVanLoan.Chapter05.kappa2_eq_kappa`). The definition is `Matrix.pinvCondNumberLp 2 A`. -/
noncomputable def kappa2 (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  pinvCondNumberLp 2 A

/-- **Equation (5.2.4)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ have full column
rank, with $n \ge 1$. Then
$$\kappa_2(A) = \frac{\sigma_{\max}(A)}{\sigma_{\min}(A)}.$$

The singular values are `Matrix.colSingularValues A`, indexed by the columns of $A$, and
$\sigma_{\max}(A)$ and $\sigma_{\min}(A)$ are their supremum and infimum. The proof specializes
`Matrix.pinvCondNumberLp_two_eq_div_colSingularValues`. -/
theorem equation_5_2_4 [NeZero n] {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ) :
    kappa2 A = (⨆ i, A.colSingularValues i) / ⨅ i, A.colSingularValues i :=
  pinvCondNumberLp_two_eq_div_colSingularValues hA

/-- For a nonsingular $A \in \mathbb{R}^{n \times n}$, the condition number $\kappa_2(A)$ of (5.2.4)
is the square condition number $\|A\|_2 \|A^{-1}\|_2$ (`Matrix.condNumberLp 2 A`), and the
condition number `GolubVanLoan.Chapter02.kappa 2 A` of §2.6.2 is this finite value. -/
theorem kappa2_eq_kappa {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) :
    kappa2 A = condNumberLp 2 A ∧ Chapter02.kappa 2 A = ENNReal.ofReal (kappa2 A) := by
  have h : kappa2 A = condNumberLp 2 A := pinvCondNumberLp_eq_condNumberLp 2 hA
  exact ⟨h, by rw [h, Chapter02.kappa_of_isUnit 2 hA]⟩

open scoped Matrix.Norms.L2Operator in
/-- If $A \in \mathbb{R}^{m \times n}$ has full column rank and $n \ge 1$, then $\|A\|_2 > 0$. -/
theorem l2_opNorm_pos_of_linearIndependent [NeZero n] {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) : 0 < ‖A‖ := by
  refine norm_pos_iff.2 fun h0 => ?_
  have := hA.ne_zero (0 : Fin n)
  rw [h0] at this
  exact this rfl

open scoped Matrix.Norms.L2Operator in
/-- If $A \in \mathbb{R}^{m \times n}$ has full column rank and $n \ge 1$, then
$\kappa_2(A) = \|A\|_2 / \sigma_{\min}(A)$, where $\sigma_{\min}(A)$ is the infimum of the
singular values `Matrix.colSingularValues A`. The twin of
`GolubVanLoan.Chapter05.kappa2_eq_div_of_rows`. -/
theorem kappa2_eq_div [NeZero n] {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) : kappa2 A = ‖A‖ / ⨅ i, A.colSingularValues i := by
  rw [kappa2, pinvCondNumberLp, lpOpNorm_two, lpOpNorm_two,
    l2_opNorm_pinv_eq_inv_iInf_colSingularValues hA, div_eq_mul_inv]

open scoped Matrix.Norms.L2Operator in
/-- If $A \in \mathbb{R}^{m \times n}$ has full row rank and $m \ge 1$, then
$\kappa_2(A) = \|A\|_2 / \sigma_m(A)$, where $\sigma_m(A)$ is the infimum of the $m$ singular
values `Matrix.colSingularValues Aᵀ` of $A^T$. The twin of
`GolubVanLoan.Chapter05.kappa2_eq_div`. -/
theorem kappa2_eq_div_of_rows [NeZero m] {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ A) : kappa2 A = ‖A‖ / ⨅ i, Aᵀ.colSingularValues i := by
  have hAt : LinearIndependent ℝ Aᵀᵀ := by rwa [transpose_transpose]
  have hp : A.pinv = (Aᵀ.pinv)ᵀ := by
    have := pinv_conjTranspose (A := Aᵀ)
    rw [conjTranspose_eq_transpose_of_trivial, conjTranspose_eq_transpose_of_trivial,
      transpose_transpose] at this
    rw [this]
  rw [kappa2, pinvCondNumberLp, lpOpNorm_two, lpOpNorm_two, hp,
    ← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose,
    l2_opNorm_pinv_eq_inv_iInf_colSingularValues hAt, div_eq_mul_inv]

end Existence

/-! ### §5.2.2 Householder QR -/

section Householder

/-- **Algorithm 5.2.1** of [golub2013matrix], the upper triangular part of the overwritten array.
For $A \in \mathbb{R}^{m \times n}$, `upperPart A` is the matrix with the entries $a_{ij}$ for
$i \le j$ and $0$ for $i > j$.

The source says that the upper triangular part of $A$ is overwritten by the upper triangular
part of $R$. The specifications of this module read $R$ from an overwritten array by this
function. -/
def upperPart (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  of fun i j => if (i : ℕ) ≤ j then A i j else 0

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- Step $j$ of Algorithm 5.2.1 on the array $A$ and the vector of recorded $\beta$:
$[v, \beta] = \operatorname{house}(A(j{:}m, j))$, then $A(j{:}m, j{:}n) = (I - \beta v v^T)
A(j{:}m, j{:}n)$ and $A(j{+}1{:}m, j) = v(2{:}m{-}j{+}1)$, and $\beta$ is recorded as $\beta_j$.
The step calls `GolubVanLoan.Chapter05.houseOn` and
`GolubVanLoan.Chapter05.householderApplyLeft` on the full array with the index lists of the rows
and columns from $j$ on. -/
noncomputable def householderQRStep (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)) (j : Fin n) :
    M (Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)) := do
  let vβ ← houseOn rnd (indexFrom m j) (fun i => st.1 i j)
  let A ← householderApplyLeft rnd vβ.1 vβ.2 (indexFrom m j) (indexFrom n j) st.1
  pure (A.updateCol j (fun i => if (j : ℕ) < i then vβ.1 i else A i j),
    Function.update st.2 j vβ.2)

/-- **Algorithm 5.2.1** of [golub2013matrix] (Householder QR). Given $A \in \mathbb{R}^{m \times n}$
with $m \ge n$, the algorithm finds Householder matrices $H_1, \dots, H_n$ such that $Q^T A = R$
is upper triangular for $Q = H_1 \cdots H_n$. The upper triangular part of $A$ is overwritten by
the upper triangular part of $R$, and components $j{+}1{:}m$ of the $j$-th Householder vector
are stored in $A(j{+}1{:}m, j)$.
```
for j = 1:n
    [v, β] = house(A(j:m, j))
    A(j:m, j:n) = (I - β v vᵀ) A(j:m, j:n)
    if j < m:  A(j+1:m, j) = v(2:m-j+1)
end
```
The program runs `GolubVanLoan.Chapter05.householderQRStep` for $j = 1, \dots, n$ and returns
the overwritten array together with the vector $(\beta_1, \dots, \beta_n)$.

The factored form of $Q$ consists of the Householder vectors and the corresponding $\beta_j$
(§5.1.6). The program returns the $\beta_j$ that `house` computed, and $Q$ is built from these
(`GolubVanLoan.Chapter05.factoredQ`). The program has no hypothesis on $m$ and $n$; the
specification `GolubVanLoan.Chapter05.algorithm_5_2_1_spec` assumes $m \ge n$. -/
noncomputable def algorithm_5_2_1 (A : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)) :=
  (List.finRange n).foldlM (householderQRStep rnd) (A, 0)

end Programs

/-- **Algorithm 5.2.1** of [golub2013matrix], existence of a run. Let
$A \in \mathbb{R}^{m \times n}$, and let the rounding model `fp` be total, that is, every real
number has an admissible rounding. Then Algorithm 5.2.1 has at least one run on $A$ in this
model.

A rounding theorem is a statement about every run of a program, and it is vacuous if there is no
run. This theorem shows that the rounding theorems of Algorithm 5.2.1 are not vacuous. Totality
is `FloatingPoint.RoundingModel.IsTotal`. -/
theorem algorithm_5_2_1_run_nonempty {fp : RoundingModel ℝ} (hfp : fp.IsTotal)
    (A : Matrix (Fin m) (Fin n) ℝ) : (algorithm_5_2_1 fp.round A).run.Nonempty := by
  have hround := RoundingModel.run_round_nonempty hfp
  unfold algorithm_5_2_1
  apply SetM.run_foldlM_nonempty
  intro st j _
  unfold householderQRStep householderApplyLeft householderScaled householderLeftColumn
  cases h : indexFrom m j with
  | nil =>
    simp only [houseOn]
    all_goals repeat' first
      | exact ⟨_, rfl⟩
      | (apply SetM.run_foldlM_nonempty; intros)
      | (apply SetM.run_bind_nonempty <;> intros)
  | cons p t =>
    simp only [houseOn]
    all_goals repeat' first
      | exact ⟨_, rfl⟩
      | exact hround _
      | exact dotAccum_run_nonempty hfp _ _ _ _
      | (apply SetM.run_foldlM_nonempty; intros)
      | (unfold parlettPivot; split_ifs)
      | split_ifs
      | (apply SetM.run_bind_nonempty <;> intros)

/-- If $k$ is among the first $j$ elements of the list $0, 1, \dots, n - 1$, then $k < j$. -/
theorem lt_of_mem_take_finRange {j : ℕ} {k : Fin n}
    (hk : k ∈ (List.finRange n).take j) : (k : ℕ) < j := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
  simp only [List.length_take, List.length_finRange] at hi
  rw [List.getElem_take, List.getElem_finRange]
  change i < j
  omega

/-- The product of the reflectors of the first $j$ steps of Algorithm 5.2.1, built from the stored
Householder vectors and the recorded $\beta$ of the state. -/
private noncomputable def qrPrefix (j : ℕ) (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)) :
    Matrix (Fin m) (Fin m) ℝ :=
  householderProduct
    (((List.finRange n).take j).map fun k => (storedHouseholderVec st.1 k, st.2 k))

/-- The invariant of Algorithm 5.2.1 after $j$ steps: for the product $Q_j$ of the reflectors so far
and $C = Q_j^T A$, the upper part and the unprocessed columns of the array hold $C$, the
processed columns of $C$ vanish below the diagonal, and every recorded $\beta$ is $0$ or
$2/v^T v$. -/
private def qrInvariant (A : Matrix (Fin m) (Fin n) ℝ) (j : ℕ)
    (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)) : Prop :=
  (∀ (i : Fin m) (q : Fin n), ((i : ℕ) ≤ q ∨ j ≤ (q : ℕ)) →
      st.1 i q = ((qrPrefix j st)ᵀ * A) i q) ∧
    (∀ (i : Fin m) (q : Fin n), (q : ℕ) < j → (q : ℕ) < i →
      ((qrPrefix j st)ᵀ * A) i q = 0) ∧
    ∀ k : Fin n, (k : ℕ) < j →
      st.2 k = 0 ∨ st.2 k * (storedHouseholderVec st.1 k ⬝ᵥ storedHouseholderVec st.1 k) = 2

/-- One exact step of Algorithm 5.2.1 preserves the invariant of the algorithm. -/
private theorem qrInvariant_step (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ) (β : Fin n → ℝ) (j : Fin n)
    (hI : qrInvariant A j (B, β)) :
    qrInvariant A (j + 1) (Id.run (householderQRStep pure (B, β) j)) := by
  obtain ⟨ha, hb, hc⟩ := hI
  have hjm : (j : ℕ) < m := lt_of_lt_of_le j.isLt hnm
  have hne := indexFrom_ne_nil hjm
  set x : Fin m → ℝ := fun i => B i j with hx
  obtain ⟨hv1, hvout, hdich, -, hmul⟩ := houseOn_spec (nodup_indexFrom m j) hne x
  rw [head_indexFrom hjm hne] at hv1 hmul
  simp only [householderQRStep, Id.run_bind, Id.run_pure]
  rw [householderApplyLeft_spec (nodup_indexFrom m j) (nodup_indexFrom n j) hvout]
  generalize Id.run (houseOn pure (indexFrom m ↑j) x) = vβ at hv1 hvout hdich hmul ⊢
  obtain ⟨v, b⟩ := vβ
  dsimp only at hv1 hvout hdich hmul ⊢
  set P : Matrix (Fin m) (Fin m) ℝ := 1 - b • vecMulVec v v with hP
  set C := (qrPrefix j (B, β))ᵀ * A with hC
  have ha' : ∀ (i : Fin m) (q : Fin n), ((i : ℕ) ≤ q ∨ (j : ℕ) ≤ q) → B i q = C i q := ha
  set B' : Matrix (Fin m) (Fin n) ℝ :=
    of fun i q => if q ∈ indexFrom n j then (P * B) i q else B i q with hB'
  set B'' : Matrix (Fin m) (Fin n) ℝ :=
    B'.updateCol j (fun i => if (j : ℕ) < i then v i else B' i j) with hB''
  -- the entries of the new array
  have hBq : ∀ i (q : Fin n), q ≠ j →
      B'' i q = if q ∈ indexFrom n j then (P * B) i q else B i q := fun i q hq => by
    simp only [hB'', hB', updateCol_ne hq, of_apply]
  have hBj : ∀ i, B'' i j = if (j : ℕ) < i then v i else (P * B) i j := fun i => by
    simp only [hB'', hB', updateCol_self, of_apply, mem_indexFrom, le_refl, ite_true]
  -- facts about the old state
  have hvlt : ∀ r : Fin m, (r : ℕ) < j → v r = 0 := fun r hr =>
    hvout r (by rw [mem_indexFrom]; omega)
  have hxC : ∀ i, B i j = C i j := fun i => ha i j (Or.inr le_rfl)
  have hvC : ∀ q : Fin n, (q : ℕ) < j → (v ⬝ᵥ fun r => C r q) = 0 := fun q hq =>
    Finset.sum_eq_zero fun r _ => by
      change v r * C r q = 0
      by_cases hr : (r : ℕ) < j
      · rw [hvlt r hr, zero_mul]
      · rw [hb r q hq (by omega), mul_zero]
  have hPC : ∀ i (q : Fin n), (q : ℕ) < j → (P * C) i q = C i q := fun i q hq => by
    rw [hP, one_sub_smul_vecMulVec_mul_apply, hvC q hq, mul_zero, sub_zero]
  have hcol : ∀ k : Fin n, (k : ℕ) < j → ∀ i, B'' i k = B i k := fun k hk i => by
    have hkj : k ≠ j := fun e => by rw [e] at hk; omega
    have hk' : k ∉ indexFrom n j := by rw [mem_indexFrom]; omega
    rw [hBq i k hkj, ite_eq_right hk']
  have hsvk : ∀ k : Fin n, (k : ℕ) < j →
      storedHouseholderVec B'' k = storedHouseholderVec B k :=
    fun k hk => funext fun i => by simp only [storedHouseholderVec, hcol k hk]
  have hsvj : storedHouseholderVec B'' j = v := funext fun i => by
    simp only [storedHouseholderVec]
    by_cases hij : (i : ℕ) < j
    · rw [ite_eq_left hij, hvlt i hij]
    · rw [ite_eq_right hij]
      by_cases hij' : (i : ℕ) = j
      · rw [ite_eq_left hij']
        have : i = ⟨j, hjm⟩ := Fin.ext hij'
        rw [this, hv1]
      · rw [ite_eq_right hij', hBj, ite_eq_left (by omega)]
  have hQ : qrPrefix (j + 1) (B'', Function.update β j b) = qrPrefix j (B, β) * P := by
    have htake : (List.finRange n).take ((j : ℕ) + 1) = (List.finRange n).take j ++ [j] := by
      rw [List.take_succ_eq_append_getElem (by simp)]
      simp
    rw [qrPrefix, qrPrefix, htake, List.map_append, List.map_cons, List.map_nil,
      householderProduct_concat]
    congr 1
    · congr 1
      refine List.map_congr_left fun k hk => ?_
      have hk' := lt_of_mem_take_finRange hk
      have hkj : k ≠ j := fun e => by rw [e] at hk'; omega
      simp only [hsvk k hk', Function.update_of_ne hkj]
    · simp only [hsvj, Function.update_self]
      exact hP.symm
  have hQT : (qrPrefix (j + 1) (B'', Function.update β j b))ᵀ * A = P * C := by
    rw [hQ, transpose_mul, hP, transpose_one_sub_smul_vecMulVec, Matrix.mul_assoc]
  refine ⟨fun i q hiq => ?_, fun i q hq hqi => ?_, fun k hk => ?_⟩
  · dsimp only
    rw [hQT]
    rcases lt_trichotomy (q : ℕ) j with hqj | hqj | hqj
    · -- a processed column: unchanged, and the reflector fixes it
      have hiq' : (i : ℕ) ≤ q := hiq.resolve_right (by omega)
      rw [hcol q hqj, ha' i q (Or.inl hiq'), hPC i q hqj]
    · -- the current column
      have hq : q = j := Fin.ext hqj
      subst hq
      have hij : ¬ ((q : ℕ) < i) := by
        rcases hiq with h | h
        · omega
        · omega
      rw [hBj, ite_eq_right hij, hP, one_sub_smul_vecMulVec_mul_apply,
        one_sub_smul_vecMulVec_mul_apply]
      simp only [hxC]
    · -- a later column: the reflector applied to the (unchanged) column of `C`
      have hqj' : q ≠ j := fun e => by rw [e] at hqj; omega
      rw [hBq i q hqj', ite_eq_left (by rw [mem_indexFrom]; omega), hP,
        one_sub_smul_vecMulVec_mul_apply, one_sub_smul_vecMulVec_mul_apply]
      have hcq : ∀ r, B r q = C r q := fun r => ha r q (Or.inr (by omega))
      simp only [hcq]
  · rw [hQT]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hqj | hqj
    · rw [hPC i q hqj]
      exact hb i q hqj hqi
    · have hq : q = j := Fin.ext hqj
      subst hq
      have h1 : (P * C) i q = (P *ᵥ x) i := by
        change ((1 - b • vecMulVec v v) *ᵥ fun r => C r q) i = _
        congr 2
        funext r
        exact (hxC r).symm
      rw [h1, hmul]
      have hi1 : i ≠ ⟨q, hjm⟩ := fun e => by rw [e] at hqi; exact lt_irrefl _ hqi
      have hi2 : i ∈ indexFrom m q := by rw [mem_indexFrom]; omega
      simp [hi1, hi2]
  · dsimp only
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hkj | hkj
    · have hkj' : k ≠ j := fun e => by rw [e] at hkj; omega
      simp only [Function.update_of_ne hkj', hsvk k hkj]
      exact hc k hkj
    · have hk' : k = j := Fin.ext hkj
      subst hk'
      simp only [Function.update_self, hsvj]
      exact hdich

/-- **Algorithm 5.2.1** of [golub2013matrix], exact correctness. Let $A \in \mathbb{R}^{m \times n}$
with $m \ge n$, and let $(A', \beta)$ be the output of Algorithm 5.2.1 in exact arithmetic. Let
$v^{(j)}$ be the Householder vectors stored in $A'$, let $Q = H_1 \cdots H_n$ with
$H_j = I - \beta_j v^{(j)} v^{(j)T}$, and let $R$ be the upper triangular part of $A'$. Then $Q$
is orthogonal and $A = QR$. Moreover, for every $j$,
$$\beta_j = 0 \quad \text{or} \quad \beta_j \, v^{(j)T} v^{(j)} = 2,$$
so that each $H_j$ is the identity or the Householder matrix of $v^{(j)}$.

$Q$ is `GolubVanLoan.Chapter05.factoredQ β A'`, $R$ is `GolubVanLoan.Chapter05.upperPart A'`,
$v^{(j)}$ is `GolubVanLoan.Chapter05.storedHouseholderVec A' j`, and the factorization is
`Matrix.IsQR`. Exact arithmetic is the monad `Id` with the hook `pure`. -/
theorem algorithm_5_2_1_spec (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    IsQR A (factoredQ (Id.run (algorithm_5_2_1 pure A)).2 (Id.run (algorithm_5_2_1 pure A)).1)
        (upperPart (Id.run (algorithm_5_2_1 pure A)).1) ∧
      ∀ j, (Id.run (algorithm_5_2_1 pure A)).2 j = 0 ∨
        (Id.run (algorithm_5_2_1 pure A)).2 j *
          (storedHouseholderVec (Id.run (algorithm_5_2_1 pure A)).1 j ⬝ᵥ
            storedHouseholderVec (Id.run (algorithm_5_2_1 pure A)).1 j) = 2 := by
  set f := fun st j => Id.run (householderQRStep (m := m) (n := n) pure st j) with hf
  have hprog : Id.run (algorithm_5_2_1 pure A) = (List.finRange n).foldl f (A, 0) := by
    rw [algorithm_5_2_1, List.idRun_foldlM]
  have hall : ∀ j ≤ n, qrInvariant A j (((List.finRange n).take j).foldl f (A, 0)) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun i q _ => ?_, fun i q hq => absurd hq (Nat.not_lt_zero _),
        fun k hk => absurd hk (Nat.not_lt_zero _)⟩
      simp [qrPrefix]
    | succ j ih =>
      intro hj
      rw [List.take_succ_eq_append_getElem (by simpa using hj), List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have h := qrInvariant_step hnm A _ _ ⟨j, by omega⟩ (ih (by omega))
      simpa [hf] using h
  have hn := hall n le_rfl
  rw [List.take_of_length_le (by simp), ← hprog] at hn
  generalize Id.run (algorithm_5_2_1 pure A) = st at hn ⊢
  obtain ⟨B, β⟩ := st
  obtain ⟨ha, hb, hc⟩ := hn
  have hQeq : qrPrefix n (B, β) = factoredQ β B := by
    rw [qrPrefix, List.take_of_length_le (by simp), factoredQ, storedReflectors,
      List.ofFn_eq_map]
  rw [hQeq] at ha hb
  simp only at ha hb hc ⊢
  have hdich : ∀ j : Fin n, β j = 0 ∨ β j * (storedHouseholderVec B j ⬝ᵥ
      storedHouseholderVec B j) = 2 := fun j => hc j j.isLt
  have hO : factoredQ β B ∈ orthogonalGroup (Fin m) ℝ := by
    refine householderProduct_mem_orthogonalGroup fun p hp => ?_
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hp
    exact hdich k
  have hR : (factoredQ β B)ᵀ * A = upperPart B := by
    ext i q
    rw [upperPart, of_apply]
    split_ifs with hiq
    · exact (ha i q (Or.inl hiq)).symm
    · exact hb i q q.isLt (by omega)
  refine ⟨⟨hO, fun i q hqi => ?_, ?_⟩, hdich⟩
  · simp [upperPart, show ¬ ((i : ℕ) ≤ q) by omega]
  · rw [← hR, mul_transpose_mul_of_mem_orthogonalGroup hO]

/-- **Section 5.2.2** of [golub2013matrix], the formula $\beta_j = 2/(1 + \|A(j{+}1{:}m, j)\|_2^2)$
that recovers $\beta_j$ from the stored Householder vector after Algorithm 5.2.1, as after
(5.1.4). Let $A \in \mathbb{R}^{m \times n}$ with $m \ge n$, and let $(A', \beta)$ be the output
of Algorithm 5.2.1 in exact arithmetic, with stored Householder vectors $v^{(j)}$. Then every
nonzero $\beta_j$ equals $2/v^{(j)T} v^{(j)}$. Consequently, if no $\beta_j$ is zero, the
factored form built with the recomputed values $2/v^{(j)T} v^{(j)}$ is the same matrix as the
factored form built with the returned $\beta_j$.

**Correction.** The source recovers every $\beta_j$ by the formula. The formula is wrong when
`house` returned $\beta_j = 0$, which happens when $\sigma = 0$ and $x_1 \ge 0$: then $H_j = I$,
but the stored vector is a unit vector and the formula gives $2$. The statement therefore
applies the formula only to the nonzero $\beta_j$.

The recomputed value is `GolubVanLoan.Chapter05.recomputedBeta A' j`, and $v^{(j)T} v^{(j)} =
1 + \|A'(j{+}1{:}m, j)\|_2^2$. -/
theorem equation_5_1_4_beta (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    (∀ j, (Id.run (algorithm_5_2_1 pure A)).2 j ≠ 0 →
      (Id.run (algorithm_5_2_1 pure A)).2 j =
        recomputedBeta (Id.run (algorithm_5_2_1 pure A)).1 j) ∧
      ((∀ j, (Id.run (algorithm_5_2_1 pure A)).2 j ≠ 0) →
        factoredQ (Id.run (algorithm_5_2_1 pure A)).2 (Id.run (algorithm_5_2_1 pure A)).1 =
          factoredQ (recomputedBeta (Id.run (algorithm_5_2_1 pure A)).1)
            (Id.run (algorithm_5_2_1 pure A)).1) := by
  have hdich := (algorithm_5_2_1_spec hnm A).2
  generalize Id.run (algorithm_5_2_1 pure A) = st at hdich ⊢
  obtain ⟨B, β⟩ := st
  simp only at hdich ⊢
  have key : ∀ j, β j ≠ 0 → β j = recomputedBeta B j := fun j hj => by
    have h2 := (hdich j).resolve_left hj
    have hvv : storedHouseholderVec B j ⬝ᵥ storedHouseholderVec B j ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at h2; norm_num at h2
    rw [recomputedBeta, eq_div_iff hvv, h2]
  refine ⟨key, fun h => ?_⟩
  rw [factoredQ_eq_prod, factoredQ_eq_prod]
  congr 1
  exact List.map_congr_left fun j _ => by rw [key j (h j)]

/-! ### The backward error of Householder QR -/

section Rounding

/-- The computed $R^{(k)}$ of Algorithm 5.2.1: the array $B$ after $k$ steps, with the stored
Householder vectors, which lie below the diagonal of the first $k$ columns, replaced by zeros. -/
def householderQRPartialR (k : ℕ) (B : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  of fun i q => if (q : ℕ) < k ∧ (q : ℕ) < i then 0 else B i q

/-- One computed step of Householder QR, with its reflector data. Let the rounding model `fp` be
idempotent with unit roundoff $u$, let $m \ge n$ and $(3(18m + 31) + m + 3)u < 1$, and let
$(A'', \hat\beta')$ be a run of step $k$ of Algorithm 5.2.1 from the state $(A', \hat\beta)$.
Then there are $v \in \mathbb{R}^m$ and $\beta \in \mathbb{R}$ such that $P = I - \beta v v^T$
is orthogonal, $|\beta| \, v^T v \le 2$, $v_i = 0$ for $i < k$, every entry of the stored
Householder vector of column $k$ of $A''$ is a relative perturbation of order $18m + 31$ of the
entry of $v$, and $\hat\beta'_k$ is such a perturbation of $\beta$; the columns before $k$ and
the other $\hat\beta'_q$ are unchanged; and for every column $q$,
$$\|(R^{(k+1)} - P R^{(k)})(:, q)\|_2 \le \varepsilon \, \|R^{(k)}(:, q)\|_2, \qquad
  \varepsilon = 3\gamma_{3(18m+31)+m+3},$$
where $R^{(k)}$ is the array with the stored vectors replaced by zeros
(`GolubVanLoan.Chapter05.householderQRPartialR`).

A relative perturbation of order $r$ of $x$ is $x(1 + \theta)$ with $|\theta| \le \gamma_r$
(`FloatingPoint.IsRelPert`). Algorithm 5.3.2 uses the reflector data besides the backward error. -/
theorem householderQRStep_rounding_data {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent)
    (hnm : n ≤ m) (hu : ((3 * (18 * m + 31) + m + 3 : ℕ) : ℝ) * fp.u < 1)
    (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)) (k : Fin n)
    {st' : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)}
    (h : st' ∈ (householderQRStep fp.round st k).run) :
    ∃ (v : Fin m → ℝ) (β : ℝ), 1 - β • vecMulVec v v ∈ orthogonalGroup (Fin m) ℝ ∧
      |β| * (v ⬝ᵥ v) ≤ 2 ∧ (∀ i, i ∉ indexFrom m k → v i = 0) ∧
      (∀ i, IsRelPert fp.u (18 * m + 31) (v i) (storedHouseholderVec st'.1 k i)) ∧
      IsRelPert fp.u (18 * m + 31) β (st'.2 k) ∧
      (∀ i (q : Fin n), (q : ℕ) < k → st'.1 i q = st.1 i q) ∧
      (∀ q, q ≠ k → st'.2 q = st.2 q) ∧
      ∀ q : Fin n,
        ‖(toLp 2 ((householderQRPartialR ((k : ℕ) + 1) st'.1 -
            (1 - β • vecMulVec v v) * householderQRPartialR k st.1).col q) :
            EuclideanSpace ℝ (Fin m))‖ ≤
          3 * gamma fp.u (3 * (18 * m + 31) + m + 3) *
            ‖(toLp 2 ((householderQRPartialR k st.1).col q) : EuclideanSpace ℝ (Fin m))‖ := by
  obtain ⟨B, β⟩ := st
  have hjm : (k : ℕ) < m := lt_of_lt_of_le k.isLt hnm
  have hne := indexFrom_ne_nil hjm
  have hnd := nodup_indexFrom m k
  have hhead := head_indexFrom hjm hne
  set o := indexFrom m k with ho
  have hlen : o.length ≤ m := (List.length_filter_le _ _).trans (by simp)
  have hu0 := fp.u_nonneg
  have hle : ∀ a : ℕ, a ≤ 3 * (18 * m + 31) + m + 3 → (a : ℝ) * fp.u < 1 := fun a ha =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 ha) hu0).trans_lt hu
  simp only [householderQRStep, SetM.mem_run_bind, SetM.mem_run_pure] at h
  obtain ⟨vβ, hvβ, B', hB', rfl⟩ := h
  set x : Fin m → ℝ := fun i => B i k with hx
  obtain ⟨hvout, v, bb, hO, hmul, hbv, hbb, hv⟩ :=
    houseOn_rounding hfp hnd hne (hle _ (by omega)) x hvβ
  have hpiv : vβ.1 (o.head hne) = 1 := by
    obtain ⟨-, σhat, -, hvi, -⟩ := houseOn_rounds hfp hnd hne x hvβ
    exact hvi
  set K := 18 * o.length + 31 with hK
  -- the exact vector, extended by zero off `o`
  set v' : Fin m → ℝ := extendByZero (· ∈ o) v with hv'
  have hv'o : (fun i : {i // i ∈ o} => v' i) = v := funext fun i => extendByZero_apply v i
  have hv'out : ∀ i, i ∉ o → v' i = 0 := fun i hi => extendByZero_apply_of_not v hi
  have hvv' : ∀ i, IsRelPert fp.u K (v' i) (vβ.1 i) := fun i => by
    by_cases hi : i ∈ o
    · rw [show v' i = v ⟨i, hi⟩ from extendByZero_apply v ⟨i, hi⟩]
      exact hv ⟨i, hi⟩
    · rw [hv'out i hi, hvout i hi]
      exact ⟨0, by simpa using gamma_nonneg hu0 (hle K (by omega)), by ring⟩
  have hdot' : v' ⬝ᵥ v' = v ⬝ᵥ v := by rw [dotProduct_eq_dotProduct_subtype hv'out, hv'o]
  have hP2 : |bb| * (v' ⬝ᵥ v') ≤ 2 := by rwa [hdot']
  obtain ⟨hBout, hcolb, -⟩ := householderApplyLeft_rounding hfp hnd (nodup_indexFrom n k)
    (K := K) (hle _ (by omega)) hbb hvv' hv'out hP2 B hB'
  simp only [hv'o] at hcolb
  have hε : 3 * gamma fp.u (3 * K + o.length + 3) ≤ 3 * gamma fp.u (3 * (18 * m + 31) + m + 3) :=
    mul_le_mul_of_nonneg_left (gamma_mono hu0 (by omega) hu) (by norm_num)
  have hε0 : 0 ≤ 3 * gamma fp.u (3 * (18 * m + 31) + m + 3) := by
    have := gamma_nonneg hu0 hu; positivity
  -- the exact reflector on `ℝ^m`: the block reflector extended by the identity
  set P : Matrix (Fin m) (Fin m) ℝ := 1 - bb • vecMulVec v' v' with hP
  have hPO : P ∈ orthogonalGroup (Fin m) ℝ :=
    one_sub_smul_vecMulVec_extendByZero_mem_orthogonalGroup hO
  set B'' := B'.updateCol k fun i => if (k : ℕ) < i then vβ.1 i else B' i k with hB''
  have hB''q : ∀ i (q : Fin n), q ≠ k → B'' i q = B' i q := fun i q hq => by
    simp only [hB'', updateCol_ne hq]
  have hB''k : ∀ i, B'' i k = if (k : ℕ) < i then vβ.1 i else B' i k := fun i => by
    simp only [hB'', updateCol_self]
  refine ⟨v', bb, hPO, hP2, hv'out, fun i => ?_, ?_, fun i q hq => ?_, fun q hq => ?_,
    fun q => ?_⟩
  · -- the stored vector
    refine IsRelPert.mono hu0 (by omega) (hle _ (by omega)) (m := K) ?_
    simp only [storedHouseholderVec]
    rcases lt_trichotomy (i : ℕ) k with hik | hik | hik
    · rw [ite_eq_left hik, hv'out i (by rw [ho, mem_indexFrom]; omega)]
      exact IsRelPert.zero (gamma_nonneg hu0 (hle K (by omega)))
    · rw [ite_eq_right (by omega), ite_eq_left hik]
      have hh : ((o.head hne : Fin m) : ℕ) = k := congrArg Fin.val (head_indexFrom hjm hne)
      have h1 : vβ.1 i = 1 := by
        rw [show i = o.head hne from Fin.ext (hik.trans hh.symm)]
        exact hpiv
      have := hvv' i
      rwa [h1] at this
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), hB''k, ite_eq_left hik]
      exact hvv' i
  · simp only [Function.update_self]
    exact hbb.mono hu0 (by omega) (hle _ (by omega))
  · have hqk : q ≠ k := fun e => by rw [e] at hq; exact lt_irrefl _ hq
    change B'' i q = B i q
    rw [hB''q i q hqk]
    exact hBout i q (Or.inr (by rw [mem_indexFrom]; omega))
  · exact Function.update_of_ne hq _ _
  dsimp only
  set R := householderQRPartialR k B with hR
  set R' := householderQRPartialR ((k : ℕ) + 1) B'' with hR'
  have hRe : ∀ i (q : Fin n), R i q = if (q : ℕ) < k ∧ (q : ℕ) < i then 0 else B i q :=
    fun _ _ => rfl
  have hR'e : ∀ i (q : Fin n),
      R' i q = if (q : ℕ) < (k : ℕ) + 1 ∧ (q : ℕ) < i then 0 else B'' i q := fun _ _ => rfl
  have hPR : ∀ i, (P * R) i q = (P *ᵥ fun r => R r q) i := fun i => rfl
  rcases lt_or_ge (q : ℕ) k with hqk | hqk
  · -- a processed column is unchanged, and fixed by the reflector
    have hqk' : q ≠ k := fun e => by rw [e] at hqk; omega
    have hq' : q ∉ indexFrom n k := by rw [mem_indexFrom]; omega
    have hdot0 : (v' ⬝ᵥ fun r => R r q) = 0 := Finset.sum_eq_zero fun r _ => by
      change v' r * R r q = 0
      by_cases hr : r ∈ o
      · have hr' : (k : ℕ) ≤ r := mem_indexFrom.1 hr
        rw [hRe, ite_eq_left ⟨hqk, by omega⟩, mul_zero]
      · rw [hv'out r hr, zero_mul]
    have hzero : (R' - P * R).col q = 0 := funext fun i => by
      change R' i q - (P * R) i q = 0
      rw [hPR, one_sub_smul_vecMulVec_mulVec_apply, hdot0, mul_zero, sub_zero]
      by_cases hqi : (q : ℕ) < i
      · rw [hR'e, ite_eq_left ⟨by omega, hqi⟩, hRe, ite_eq_left ⟨hqk, hqi⟩, sub_self]
      · rw [hR'e, ite_eq_right (by omega), hRe, ite_eq_right (by omega), hB''q i q hqk',
          hBout i q (Or.inr hq'), sub_self]
    rw [hzero, toLp_zero, norm_zero]
    exact mul_nonneg hε0 (norm_nonneg _)
  · -- a column of the current block, by the backbone's block-reflector bound
    have hq : q ∈ indexFrom n k := mem_indexFrom.2 hqk
    have hRcol : (fun r : {r // r ∈ o} => R r q) = fun r : {r // r ∈ o} => B r q :=
      funext fun r => by rw [hRe, ite_eq_right (by omega)]
    have hcol : (R' - P * R).col q = (fun i => R' i q) - P *ᵥ fun r => R r q := rfl
    rw [hcol, show R.col q = fun r => R r q from rfl]
    refine norm_sub_one_sub_smul_vecMulVec_extendByZero_mulVec_le (p := (· ∈ o))
      (y := fun a => B' a q) hε0 (fun i hi => ?_) (fun a => ?_) ?_
    · -- off the block both arrays keep the entry
      have hik : (i : ℕ) < k := by rw [ho, mem_indexFrom] at hi; omega
      change R' i q = R i q
      rw [hRe, ite_eq_right (by omega), hR'e, ite_eq_right (by omega)]
      by_cases h : q = k
      · subst h
        rw [hB''k, ite_eq_right (by omega)]
        exact hBout i _ (Or.inl hi)
      · rw [hB''q i q h]
        exact hBout i q (Or.inl hi)
    · -- on the block the stored entries are at least as close as the computed ones
      obtain ⟨i, hi⟩ := a
      rw [hRcol]
      by_cases hqk' : q = k
      · subst hqk'
        by_cases hik : (q : ℕ) < i
        · -- below the diagonal of the current column: both sides vanish
          have hne' : (⟨i, hi⟩ : {r // r ∈ o}) ≠ ⟨o.head hne, List.head_mem hne⟩ :=
            fun h => by
              have := congrArg (fun r : {r // r ∈ o} => (r.1 : ℕ)) h
              have hh : ((o.head hne : Fin m) : ℕ) = q := by
                have := congrArg Fin.val hhead
                simpa only [Fin.val_mk] using this
              simp only at this
              omega
          have hx0 : ((1 - bb • vecMulVec v v) *ᵥ fun r : {r // r ∈ o} => B r q) ⟨i, hi⟩ =
              0 := by
            refine (congrFun hmul ⟨i, hi⟩).trans ?_
            simp [Pi.single_eq_of_ne hne']
          change |R' i q - _| ≤ _
          rw [hR'e, ite_eq_left ⟨by omega, hik⟩, hx0, sub_zero, abs_zero]
          exact abs_nonneg _
        · change |R' i q - _| ≤ _
          rw [hR'e, ite_eq_right (by omega), hB''k, ite_eq_right hik]
      · change |R' i q - _| ≤ _
        rw [hR'e, ite_eq_right (by omega), hB''q i q hqk']
    · -- the block bound of `householderApplyLeft_rounding`
      rw [hRcol]
      exact (hcolb ⟨q, hq⟩).trans (mul_le_mul_of_nonneg_right hε (norm_nonneg _))

/-- The exact reflector $I - \beta_j v_j v_j^T$ of the reflector data $(v, \beta)$ at index $j$. -/
noncomputable def dataReflector (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (j : ℕ) :
    Matrix (Fin m) (Fin m) ℝ :=
  1 - β j • vecMulVec (v j) (v j)

/-- The reflector data $(v, \beta)$ is admissible for step $q$ of Algorithm 5.2.1 against the state
$(A', \hat\beta)$, with unit roundoff $u$, if $|\beta| \, v^T v \le 2$, $v_i = 0$ for $i < q$,
every entry of the stored Householder vector of column $q$ of $A'$ is a relative perturbation of
order $18m + 31$ of the entry of $v$, and $\hat\beta_q$ is such a perturbation of $\beta$. This
is what Algorithm 5.3.2 needs of step $q$. -/
def IsStepData (u : ℝ) (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)) (q : Fin n)
    (v : Fin m → ℝ) (β : ℝ) : Prop :=
  |β| * (v ⬝ᵥ v) ≤ 2 ∧ (∀ i, i ∉ indexFrom m q → v i = 0) ∧
    (∀ i, IsRelPert u (18 * m + 31) (v i) (storedHouseholderVec st.1 q i)) ∧
    IsRelPert u (18 * m + 31) β (st.2 q)

/-- Algorithm 5.2.1, backward error with the reflector data. Let the rounding model `fp` be
idempotent with unit roundoff $u$, let $m \ge n$ and $(3(18m + 31) + m + 3)u < 1$, and let
$(A', \hat\beta)$ be a run of Algorithm 5.2.1 on $A \in \mathbb{R}^{m \times n}$. Then there are
reflector data $(v_j, \beta_j)$ and $E \in \mathbb{R}^{m \times n}$ such that every
$P_j = I - \beta_j v_j v_j^T$ is orthogonal, the data of each column $q$ is admissible in the
sense of `GolubVanLoan.Chapter05.IsStepData`, the upper triangular part $\hat R$ of $A'$ is
$\hat R = P_{n-1} \cdots P_0 (A + E)$, and $\|E(:, q)\|_2 \le ((1 + \varepsilon)^n - 1) \|A(:,
q)\|_2$ for every column $q$, with $\varepsilon = 3\gamma_{3(18m+31)+m+3}$. This is the form of
`GolubVanLoan.Chapter05.algorithm_5_2_1_rounding` that keeps the reflectors. -/
theorem algorithm_5_2_1_rounding_data {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent)
    (hnm : n ≤ m) (hu : ((3 * (18 * m + 31) + m + 3 : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin m) (Fin n) ℝ) {st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)}
    (h : st ∈ (algorithm_5_2_1 fp.round A).run) :
    ∃ (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (E : Matrix (Fin m) (Fin n) ℝ),
      (∀ j, dataReflector v β j ∈ orthogonalGroup (Fin m) ℝ) ∧
      (∀ q : Fin n, IsStepData fp.u st q (v q) (β q)) ∧
      upperPart st.1 = prodRev (dataReflector v β) n * (A + E) ∧
      ∀ q, ‖(toLp 2 (E.col q) : EuclideanSpace ℝ (Fin m))‖ ≤
        ((1 + 3 * gamma fp.u (3 * (18 * m + 31) + m + 3)) ^ n - 1) *
          ‖(toLp 2 (A.col q) : EuclideanSpace ℝ (Fin m))‖ := by
  set ε := 3 * gamma fp.u (3 * (18 * m + 31) + m + 3) with hε
  have hε0 : 0 ≤ ε := by have := gamma_nonneg fp.u_nonneg hu; positivity
  set I : ℕ → Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) → Prop := fun k st =>
    ∃ (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (E : Matrix (Fin m) (Fin n) ℝ),
      (∀ j, dataReflector v β j ∈ orthogonalGroup (Fin m) ℝ) ∧
      (∀ q : Fin n, (q : ℕ) < k → IsStepData fp.u st q (v q) (β q)) ∧
      householderQRPartialR k st.1 = prodRev (dataReflector v β) k * (A + E) ∧
      ∀ q, ‖(toLp 2 (E.col q) : EuclideanSpace ℝ (Fin m))‖ ≤
        ((1 + ε) ^ k - 1) * ‖(toLp 2 (A.col q) : EuclideanSpace ℝ (Fin m))‖ with hI
  have h0 : I 0 (A, 0) := by
    refine ⟨fun _ => 0, fun _ => 0, 0, fun j => ?_, fun q hq => absurd hq (Nat.not_lt_zero _),
      ?_, fun q => ?_⟩
    · simp only [dataReflector, vecMulVec_zero, smul_zero, sub_zero]
      exact one_mem _
    · ext i q
      simp [householderQRPartialR]
    · rw [show (0 : Matrix (Fin m) (Fin n) ℝ).col q = 0 from rfl]
      simp
  have hstep : ∀ (k : Fin n) (c : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)), I k c →
      ∀ c' ∈ (householderQRStep fp.round c k).run, I ((k : ℕ) + 1) c' := by
    rintro k c ⟨v, β, E, hO, hdata, hE, hEb⟩ c' hc'
    obtain ⟨w, γ, hwO, hw2, hwout, hwrel, hγrel, hcols, hβs, hFb⟩ :=
      householderQRStep_rounding_data hfp hnm hu c k hc'
    set v' : ℕ → Fin m → ℝ := fun j => if j = k then w else v j with hv'
    set β' : ℕ → ℝ := fun j => if j = k then γ else β j with hβ'
    have hrefl : ∀ j, dataReflector v' β' j =
        if j = k then 1 - γ • vecMulVec w w else dataReflector v β j := fun j => by
      simp only [dataReflector, hv', hβ']
      split_ifs <;> rfl
    have hO' : ∀ j, dataReflector v' β' j ∈ orthogonalGroup (Fin m) ℝ := fun j => by
      rw [hrefl]
      split_ifs
      · exact hwO
      · exact hO j
    have hW : prodRev (dataReflector v' β') k = prodRev (dataReflector v β) k :=
      prodRev_congr fun j hj => by rw [hrefl, ite_eq_right (show ¬ j = (k : ℕ) by omega)]
    set W := prodRev (dataReflector v' β') ((k : ℕ) + 1) with hWdef
    have hWk : W = (1 - γ • vecMulVec w w) * prodRev (dataReflector v β) k := by
      rw [hWdef, prodRev_succ, hW, hrefl, ite_eq_left rfl]
    -- Lemma 19.3, one step (`FloatingPoint.exists_eq_mul_add_of_step`)
    obtain ⟨E', hE'eq, hE'b⟩ := exists_eq_mul_add_of_step hwO
      (prodRev_mem_orthogonalGroup fun k _ => hO k) hε0 hE hEb hFb
    refine ⟨v', β', E', hO', fun q hq => ?_, ?_, hE'b⟩
    · -- the step data
      by_cases hqk : (q : ℕ) = k
      · have hq' : q = k := Fin.ext hqk
        subst hq'
        simp only [hv', hβ', ite_true]
        exact ⟨hw2, hwout, hwrel, hγrel⟩
      · have hq2 : (q : ℕ) < k := by omega
        have hqk' : q ≠ k := fun e => hqk (by rw [e])
        obtain ⟨h1, h2, h3, h4⟩ := hdata q hq2
        simp only [hv', hβ', hqk, ↓reduceIte]
        refine ⟨h1, h2, fun i => ?_, by rwa [hβs q hqk']⟩
        have hst : storedHouseholderVec c'.1 q = storedHouseholderVec c.1 q := by
          funext i
          simp only [storedHouseholderVec, hcols i q hq2]
        rw [hst]
        exact h3 i
    · rw [hE'eq, ← hWk]
  obtain ⟨v, β, E, hO, hdata, hE, hEb⟩ := SetM.forall_mem_run_foldlM_finRange I h0 hstep st h
  refine ⟨v, β, E, hO, fun q => hdata q q.isLt, ?_, hEb⟩
  have hup : householderQRPartialR n st.1 = upperPart st.1 := by
    ext i q
    have := q.isLt
    simp only [householderQRPartialR, upperPart, of_apply]
    split_ifs <;> first | rfl | (exfalso; omega)
  rwa [hup] at hE

/-- **Section 5.2.2** of [golub2013matrix], the backward error of Householder QR. Let the rounding
model `fp` be idempotent with unit roundoff $u$, let $A \in \mathbb{R}^{m \times n}$ with
$m \ge n$, and let $(3(18m + 31) + m + 3)u < 1$. Let $(A', \hat\beta)$ be a run of Algorithm
5.2.1 on $A$ in this model, and let $\hat R$ be the upper triangular part of $A'$. Then there
are an orthogonal $Z \in \mathbb{R}^{m \times m}$ and $E \in \mathbb{R}^{m \times n}$ with
$$Z \hat R = A + E, \qquad \|E(:, q)\|_2 \le \bigl((1 + \varepsilon)^n - 1\bigr) \|A(:, q)\|_2$$
for every column $q$, where $\varepsilon = 3\gamma_{3(18m+31)+m+3}$ and
$\gamma_k = ku/(1 - ku)$.

The source says that the computed $\hat R$ is the exact $R$ for a nearby matrix:
$Z^T(A + E) = \hat R$ with $\|E\|_2 \approx u \|A\|_2$. The theorem is a rigorous columnwise
form of this statement; $(1 + \varepsilon)^n - 1 \le n\varepsilon/(1 - n\varepsilon)$ for
$n\varepsilon < 1$ by `FloatingPoint.one_add_pow_sub_one_le_gamma`. $Z$ is the product of the
exact reflectors of the computed columns. The subdiagonal entries of the processed columns,
which hold the Householder vectors, are not part of $\hat R$, and $E$ accounts for them.
Idempotence is `FloatingPoint.RoundingModel.IsIdempotent`. The proof specializes
`GolubVanLoan.Chapter05.algorithm_5_2_1_rounding_data`. -/
theorem algorithm_5_2_1_rounding {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent) (hnm : n ≤ m)
    (hu : ((3 * (18 * m + 31) + m + 3 : ℕ) : ℝ) * fp.u < 1) (A : Matrix (Fin m) (Fin n) ℝ)
    {st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)} (h : st ∈ (algorithm_5_2_1 fp.round A).run) :
    ∃ Z ∈ orthogonalGroup (Fin m) ℝ, ∃ E : Matrix (Fin m) (Fin n) ℝ,
      Z * upperPart st.1 = A + E ∧ ∀ q, ‖(toLp 2 (E.col q) : EuclideanSpace ℝ (Fin m))‖ ≤
        ((1 + 3 * gamma fp.u (3 * (18 * m + 31) + m + 3)) ^ n - 1) *
          ‖(toLp 2 (A.col q) : EuclideanSpace ℝ (Fin m))‖ := by
  obtain ⟨v, β, E, hO, -, hE, hEb⟩ := algorithm_5_2_1_rounding_data hfp hnm hu A h
  have hW := prodRev_mem_orthogonalGroup (r := n) fun k _ => hO k
  refine ⟨(prodRev (dataReflector v β) n)ᵀ, transpose_mem_unitaryGroup_iff.2 hW, E, ?_, hEb⟩
  rw [hE, ← Matrix.mul_assoc, (mem_orthogonalGroup_iff' _ _).1 hW, Matrix.one_mul]

end Rounding

end Householder

/-! ### §5.2.5 Givens QR methods -/

section Givens

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The index $i - 1$ of the row above row $i$, with value $0$ for $i = 0$; the programs use it only
for $i \ge 1$. -/
def rowAbove (i : Fin m) : Fin m := ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

/-- **Algorithm 5.2.4** of [golub2013matrix] (Givens QR). Given $A \in \mathbb{R}^{m \times n}$ with
$m \ge n$, the algorithm overwrites $A$ with $Q^T A = R$, where $R$ is upper triangular and $Q$
is orthogonal.
```
for j = 1:n
    for i = m:-1:j+1
        [c, s] = givens(A(i-1, j), A(i, j))
        A(i-1:i, j:n) = [c s; -s c]ᵀ A(i-1:i, j:n)
    end
end
```

The pair $(c, s)$ is computed by Algorithm 5.1.3 (`GolubVanLoan.Chapter05.algorithm_5_1_3`), and
the row update is `GolubVanLoan.Chapter05.givensApplyLeft` on the columns $j{:}n$. The program
needs no hypothesis on $m$ and $n$, and neither do its specifications. -/
noncomputable def algorithm_5_2_4 (A : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) =>
    ((List.finRange m).filter (fun i : Fin m => (j : ℕ) < i)).reverse.foldlM
      (fun (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) => do
        let cs ← algorithm_5_1_3 rnd (A (rowAbove i) j) (A i j)
        givensApplyLeft rnd (rowAbove i) i cs.1 cs.2 (indexFrom n j) A) A) A

/-- **Section 5.2.5** of [golub2013matrix], the first reordering of Givens QR. Let
$A \in \mathbb{R}^{m \times n}$ with $m \ge n$. The program is Algorithm 5.2.4 with the inner
loop body replaced by
```
[c, s] = givens(A(j, j), A(i, j))
A([j i], j:n) = [c s; -s c]ᵀ A([j i], j:n)
```
so that row $i$ is rotated against the diagonal row $j$ instead of row $i - 1$. The source says
that one still emerges with the QR factorization; this is
`GolubVanLoan.Chapter05.givensQRDiagonalPivot_spec`.

The hypothesis $m \ge n$ makes the column index $j$ a row index. -/
noncomputable def givensQRDiagonalPivot (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) =>
    ((List.finRange m).filter (fun i : Fin m => (j : ℕ) < i)).reverse.foldlM
      (fun (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) => do
        let jj : Fin m := Fin.castLE hnm j
        let cs ← algorithm_5_1_3 rnd (A jj j) (A i j)
        givensApplyLeft rnd jj i cs.1 cs.2 (indexFrom n j) A) A) A

/-- **Section 5.2.5** of [golub2013matrix], the second reordering of Givens QR, which introduces the
zeros row by row. Let $A \in \mathbb{R}^{m \times n}$ with $m \ge n$. The program is
```
for i = 2:m
    for j = 1:i-1
        [c, s] = givens(A(j, j), A(i, j))
        A([j i], j:n) = [c s; -s c]ᵀ A([j i], j:n)
    end
end
```

The inner loop runs over the columns $j < \min(i, n)$. -/
noncomputable def givensQRByRow (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ) :=
  (List.finRange m).foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) =>
    ((List.finRange n).filter (fun j : Fin n => (j : ℕ) < i)).foldlM
      (fun (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) => do
        let jj : Fin m := Fin.castLE hnm j
        let cs ← algorithm_5_1_3 rnd (A jj j) (A i j)
        givensApplyLeft rnd jj i cs.1 cs.2 (indexFrom n j) A) A) A

/-- **Algorithm 5.2.5** of [golub2013matrix] (Hessenberg QR). If $A \in \mathbb{R}^{n \times n}$ is
upper Hessenberg, the algorithm overwrites $A$ with $Q^T A = R$, where $Q$ is orthogonal and $R$
is upper triangular. $Q = G_1 \cdots G_{n-1}$ is a product of Givens rotations
$G_j = G(j, j+1, \theta_j)$.
```
for j = 1:n-1
    [c, s] = givens(A(j, j), A(j+1, j))
    A(j:j+1, j:n) = [c s; -s c]ᵀ A(j:j+1, j:n)
end
```
The program also returns the pairs $(c_j, s_j)$.

The order is written $n = k + 1$, so $n \ge 1$. -/
noncomputable def algorithm_5_2_5 {k : ℕ} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    M (Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × (Fin k → ℝ × ℝ)) :=
  (List.finRange k).foldlM
    (fun (st : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × (Fin k → ℝ × ℝ)) (j : Fin k) => do
      let cs ← algorithm_5_1_3 rnd (st.1 j.castSucc j.castSucc) (st.1 j.succ j.castSucc)
      let A ← givensApplyLeft rnd j.castSucc j.succ cs.1 cs.2 (indexFrom (k + 1) j) st.1
      pure (A, Function.update st.2 j cs)) (A, fun _ => (1, 0))

/-- **Section 6.5.1** of [golub2013matrix], the top-down Givens sweep of an upper Hessenberg matrix.
Let $Q \in \mathbb{R}^{m \times m}$ and $H \in \mathbb{R}^{m \times n}$. For the `count` indices
$j = a, a + 1, \dots$ in increasing order, the program computes $[c, s] =
\operatorname{givens}(H(j, j), H(j + 1, j))$ by Algorithm 5.1.3, rotates the rows $j$ and
$j + 1$ of $H$, and accumulates the rotation into the columns $j$ and $j + 1$ of $Q$. A step
with $j + 1 \ge m$ or $j \ge n$ is skipped.

In §6.5.1 the source computes, following Algorithm 5.2.4, Givens rotations $G_k$, $k = 1{:}n-1$,
such that $G_{n-1}^T \cdots G_1^T H_1 = R_1$ is upper triangular; §6.5.2 and §6.5.3 start the
same sweep at a column $a$. Indices are 0-based. -/
noncomputable def givensHessenbergSweep {m n : ℕ} (a count : ℕ) (Q : Matrix (Fin m) (Fin m) ℝ)
    (H : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) :=
  (List.range' a count).foldlM
    (fun (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) (j : ℕ) =>
      if h : j + 1 < m ∧ j < n then do
        let cs ← algorithm_5_1_3 rnd (st.2 ⟨j, by omega⟩ ⟨j, h.2⟩)
          (st.2 ⟨j + 1, h.1⟩ ⟨j, h.2⟩)
        let H ← givensApplyLeft rnd ⟨j, by omega⟩ ⟨j + 1, h.1⟩ cs.1 cs.2
          (List.finRange n) st.2
        let Q ← givensApplyRight rnd ⟨j, by omega⟩ ⟨j + 1, h.1⟩ cs.1 cs.2
          (List.finRange m) st.1
        pure (Q, H)
      else pure st) (Q, H)

/-- **Section 6.5.1** of [golub2013matrix], the bottom-up Givens sweep driven by a vector. Let
$w \in \mathbb{R}^m$, $Q \in \mathbb{R}^{m \times m}$ and $R \in \mathbb{R}^{m \times n}$. For
the `count` indices $j = b + \mathrm{count} - 1, \dots, b$ in decreasing order, the program
computes $[c, s] = \operatorname{givens}(w(j), w(j + 1))$ by Algorithm 5.1.3, rotates the
entries $j$ and $j + 1$ of $w$ and the rows $j$ and $j + 1$ of $R$, and accumulates the rotation
into the columns $j$ and $j + 1$ of $Q$. A step with $j + 1 \ge m$ is skipped.

In §6.5.1 the source computes rotations $J_{n-1}, \dots, J_1$ with
$J_1^T \cdots J_{n-1}^T w = \pm \|w\|_2 e_1$ and applies them to $R$; in §6.5.3 it computes
Givens rotations $G_1, \dots, G_{m-1}$ with $G_1^T \cdots G_{m-1}^T q = \alpha e_1$. Indices are
0-based. -/
noncomputable def givensVectorSweep {m n : ℕ} (b count : ℕ) (w : Fin m → ℝ)
    (Q : Matrix (Fin m) (Fin m) ℝ) (R : Matrix (Fin m) (Fin n) ℝ) :
    M ((Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) :=
  (List.range' b count).reverse.foldlM
    (fun (st : (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) (j : ℕ) =>
      if h : j + 1 < m then do
        let cs ← algorithm_5_1_3 rnd (st.1 ⟨j, by omega⟩) (st.1 ⟨j + 1, h⟩)
        let w ← givensRotateVec rnd ⟨j, by omega⟩ ⟨j + 1, h⟩ cs.1 cs.2 st.1
        let R ← givensApplyLeft rnd ⟨j, by omega⟩ ⟨j + 1, h⟩ cs.1 cs.2
          (List.finRange n) st.2.2
        let Q ← givensApplyRight rnd ⟨j, by omega⟩ ⟨j + 1, h⟩ cs.1 cs.2
          (List.finRange m) st.2.1
        pure (w, Q, R)
      else pure st) (w, Q, R)

end Programs

/-! ### §5.2.5–5.2.6 Givens QR: exact semantics -/

section GivensQRSpec

/-- Let $p \neq i$. The product $G(p, i, \theta)^T B$ has row $p$ equal to
$c\,B(p, :) - s\,B(i, :)$, row $i$ equal to $s\,B(p, :) + c\,B(i, :)$, and the other rows equal
to those of $B$. -/
theorem givensRotation_transpose_mul_apply {p i : Fin m} (hpi : p ≠ i) (c s : ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ) (r : Fin m) (q : Fin n) :
    ((givensRotation p i c s)ᵀ * B) r q =
      if r = p then c * B p q - s * B i q else if r = i then s * B p q + c * B i q else B r q := by
  change ((givensRotation p i c s)ᵀ *ᵥ fun t => B t q) r = _
  rw [givensRotation_transpose_mulVec_apply hpi]

/-- Let $i \neq k$. The product $A\,G(i, k, \theta)$ has column $i$ equal to
$c\,A(:, i) - s\,A(:, k)$, column $k$ equal to $s\,A(:, i) + c\,A(:, k)$, and the other columns
equal to those of $A$. -/
theorem mul_givensRotation_apply {p : ℕ} {i k : Fin n} (hik : i ≠ k) (c s : ℝ)
    (A : Matrix (Fin p) (Fin n) ℝ) (r : Fin p) (q : Fin n) :
    (A * givensRotation i k c s) r q =
      if q = i then c * A r i - s * A r k else if q = k then s * A r i + c * A r k
        else A r q := by
  have h : (A * givensRotation i k c s) r q = ((givensRotation i k c s)ᵀ *ᵥ A r) q := by
    rw [mulVec_transpose]; rfl
  rw [h, givensRotation_transpose_mulVec_apply hik]

/-- One exact step of the Givens QR algorithms on $B$: $[c, s] = \operatorname{givens}(B(p, j), B(i,
j))$, then the rows $p$ and $i$ of $B$ are rotated on the columns $j{:}n$. -/
noncomputable def givensStepExact (p i : Fin m) (j : Fin n) (B : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  Id.run (givensApplyLeft pure p i (Id.run (algorithm_5_1_3 pure (B p j) (B i j))).1
    (Id.run (algorithm_5_1_3 pure (B p j) (B i j))).2 (indexFrom n j) B)

/-- Let $p \neq i$, and let the rows $p$ and $i$ of $B$ vanish in the columns before $j$. Then the
pair $(c, s)$ of the exact Givens step satisfies $c^2 + s^2 = 1$, and the step equals the full
product $G(p, i, \theta)^T B$. The step makes the entry $(i, j)$ zero and keeps the rows other
than $p$ and $i$ and the columns before $j$. -/
theorem givensStepExact_spec {p i : Fin m} (hpi : p ≠ i) (j : Fin n)
    (B : Matrix (Fin m) (Fin n) ℝ) (hz : ∀ q : Fin n, (q : ℕ) < j → B p q = 0 ∧ B i q = 0) :
    (Id.run (algorithm_5_1_3 pure (B p j) (B i j))).1 ^ 2 +
        (Id.run (algorithm_5_1_3 pure (B p j) (B i j))).2 ^ 2 = 1 ∧
      givensStepExact p i j B = (givensRotation p i (Id.run (algorithm_5_1_3 pure (B p j)
        (B i j))).1 (Id.run (algorithm_5_1_3 pure (B p j) (B i j))).2)ᵀ * B ∧
      givensStepExact p i j B i j = 0 ∧
      (∀ r q, r ≠ p → r ≠ i → givensStepExact p i j B r q = B r q) ∧
      (∀ r (q : Fin n), (q : ℕ) < j → givensStepExact p i j B r q = B r q) := by
  obtain ⟨hcs, hz0, -⟩ := algorithm_5_1_3_spec (B p j) (B i j)
  set c := (Id.run (algorithm_5_1_3 pure (B p j) (B i j))).1 with hc
  set s := (Id.run (algorithm_5_1_3 pure (B p j) (B i j))).2 with hs
  have hdef : givensStepExact p i j B = Id.run (givensApplyLeft pure p i c s (indexFrom n j) B) :=
    rfl
  have hleft : ∀ r (q : Fin n), (q : ℕ) < j → ((givensRotation p i c s)ᵀ * B) r q = B r q := by
    intro r q hq
    obtain ⟨h1, h2⟩ := hz q hq
    rw [givensRotation_transpose_mul_apply hpi]
    split_ifs with hr1 hr2
    · rw [hr1, h1, h2]; ring
    · rw [hr2, h1, h2]; ring
    · rfl
  have hG : givensStepExact p i j B = (givensRotation p i c s)ᵀ * B := by
    rw [hdef, givensApplyLeft_spec hpi c s (nodup_indexFrom n j)]
    ext r q
    rw [of_apply]
    split_ifs with hq
    · rfl
    · rw [mem_indexFrom, not_le] at hq
      exact (hleft r q hq).symm
  refine ⟨hcs, hG, ?_, ?_, ?_⟩
  · rw [hG, givensRotation_transpose_mul_apply hpi, ite_eq_right hpi.symm, ite_eq_left rfl]
    exact hz0
  · intro r q hrp hri
    rw [hG, givensRotation_transpose_mul_apply hpi, ite_eq_right hrp, ite_eq_right hri]
  · intro r q hq
    rw [hG]
    exact hleft r q hq

/-- If $QB = A_0$ for an orthogonal $Q$ and $G$ is orthogonal, then $Q'(G^T B) = A_0$ for an
orthogonal $Q'$, namely $Q' = QG$. -/
theorem exists_mul_eq_of_transpose_mul {A₀ B : Matrix (Fin m) (Fin n) ℝ}
    {G : Matrix (Fin m) (Fin m) ℝ} (hG : G ∈ orthogonalGroup (Fin m) ℝ)
    (hQ : ∃ Q ∈ orthogonalGroup (Fin m) ℝ, Q * B = A₀) :
    ∃ Q ∈ orthogonalGroup (Fin m) ℝ, Q * (Gᵀ * B) = A₀ := by
  obtain ⟨Q, hQo, hQB⟩ := hQ
  refine ⟨Q * G, mul_mem hQo hG, ?_⟩
  rw [← Matrix.mul_assoc, Matrix.mul_assoc Q G, (mem_orthogonalGroup_iff _ _).1 hG,
    Matrix.mul_one, hQB]

/-- The inner loop of the column-oriented Givens QR algorithms (Algorithm 5.2.4 and its first
reordering). Let $j$ be a column and $l$ a list of distinct rows $i > j$, each rotated against a
pivot row $\pi(i) \neq i$ with $\pi(i) \ge j$, such that no row of $l$ is the pivot of a later
row of $l$. Let $S$ be a set of rows that are neither in $l$ nor pivots, let $QB = A_0$ with $Q$
orthogonal, let the columns of $B$ before $j$ vanish below the diagonal, and let $B(r, j) = 0$
for $r \in S$. Then after the rotations, each of which zeroes $B(i, j)$, there is an orthogonal
$Q'$ with $Q'B' = A_0$, the columns before $j$ still vanish below the diagonal, and
$B'(r, j) = 0$ for every row $r$ in $S$ or in $l$. -/
theorem givensColumnLoop (A₀ : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) (piv : Fin m → Fin m) :
    ∀ (l : List (Fin m)) (B : Matrix (Fin m) (Fin n) ℝ) (S : Fin m → Prop),
      (∀ i ∈ l, piv i ≠ i ∧ (j : ℕ) ≤ piv i ∧ (j : ℕ) < i) →
      l.Pairwise (fun i i' => i ≠ piv i' ∧ i ≠ i') →
      (∀ r, S r → ∀ i ∈ l, r ≠ piv i ∧ r ≠ i) →
      (∃ Q ∈ orthogonalGroup (Fin m) ℝ, Q * B = A₀) →
      (∀ q : Fin n, (q : ℕ) < j → ∀ r : Fin m, (q : ℕ) < r → B r q = 0) →
      (∀ r, S r → B r j = 0) →
      (∃ Q ∈ orthogonalGroup (Fin m) ℝ,
          Q * l.foldl (fun B i => givensStepExact (piv i) i j B) B = A₀) ∧
        (∀ q : Fin n, (q : ℕ) < j → ∀ r : Fin m, (q : ℕ) < r →
          l.foldl (fun B i => givensStepExact (piv i) i j B) B r q = 0) ∧
        ∀ r, (S r ∨ r ∈ l) → l.foldl (fun B i => givensStepExact (piv i) i j B) B r j = 0 := by
  intro l
  induction l with
  | nil =>
    intro B S _ _ _ hQ hlow hS
    simp only [List.foldl_nil]
    exact ⟨hQ, hlow, fun r hr => hS r (by simpa using hr)⟩
  | cons i l ih =>
    intro B S hpiv hpw hSl hQ hlow hS
    obtain ⟨hpi, hjp, hji⟩ := hpiv i List.mem_cons_self
    have hz : ∀ q : Fin n, (q : ℕ) < j → B (piv i) q = 0 ∧ B i q = 0 := fun q hq =>
      ⟨hlow q hq _ (by omega), hlow q hq _ (by omega)⟩
    obtain ⟨hcs, hB1, hi0, hrest, hleft⟩ := givensStepExact_spec hpi j B hz
    have hG := givensRotation_mem_orthogonalGroup hpi hcs
    rw [List.pairwise_cons] at hpw
    rw [List.foldl_cons]
    have key := ih (givensStepExact (piv i) i j B) (fun r => S r ∨ r = i)
      (fun i' hi' => hpiv i' (List.mem_cons_of_mem _ hi')) hpw.2
      (by
        rintro r (hr | rfl) i' hi'
        · exact hSl r hr i' (List.mem_cons_of_mem _ hi')
        · exact hpw.1 i' hi')
      (by rw [hB1]; exact exists_mul_eq_of_transpose_mul hG hQ)
      (fun q hq r hr => by rw [hleft r q hq]; exact hlow q hq r hr)
      (by
        rintro r (hr | rfl)
        · obtain ⟨h1, h2⟩ := hSl r hr i List.mem_cons_self
          rw [hrest r j h1 h2]
          exact hS r hr
        · exact hi0)
    obtain ⟨h1, h2, h3⟩ := key
    refine ⟨h1, h2, fun r hr => h3 r ?_⟩
    rcases hr with hr | hr
    · exact Or.inl (Or.inl hr)
    · rcases List.mem_cons.1 hr with rfl | hr
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr hr

/-- A row $i$ is in the reversed list of the rows below $j$ if and only if $j < i$. -/
theorem mem_rowsBelow_reverse {j : ℕ} {i : Fin m} :
    i ∈ ((List.finRange m).filter (fun i : Fin m => j < i)).reverse ↔ j < i := by
  simp

/-- The column-oriented Givens QR algorithms compute a QR factorization; this is the common proof
for Algorithm 5.2.4 and its first reordering. Let $A \in \mathbb{R}^{m \times n}$, and for each
column $j$ let the rows $i = m - 1, \dots, j + 1$ be rotated in the plane $(\pi_j(i), i)$, where
$\pi_j(i) \neq i$, $\pi_j(i) \ge j$, and no row $b > a$ is the pivot $\pi_j(a)$ of a row $a > j$
processed after it. Then the resulting array $R$ is upper triangular and $A = QR$ for an
orthogonal $Q$. -/
theorem givensQR_columnwise (A : Matrix (Fin m) (Fin n) ℝ) (pivF : Fin n → Fin m → Fin m)
    (hpiv : ∀ (j : Fin n) (i : Fin m), (j : ℕ) < i → pivF j i ≠ i ∧ (j : ℕ) ≤ pivF j i)
    (hpw : ∀ (j : Fin n) (a b : Fin m), (j : ℕ) < a → a < b → b ≠ pivF j a) :
    ∃ Q, IsQR A Q ((List.finRange n).foldl (fun (B : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) =>
      (((List.finRange m).filter (fun i : Fin m => (j : ℕ) < i)).reverse).foldl
        (fun (B : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) => givensStepExact (pivF j i) i j B) B)
          A) := by
  set F : Matrix (Fin m) (Fin n) ℝ → Fin n → Matrix (Fin m) (Fin n) ℝ :=
    fun (B : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) =>
      (((List.finRange m).filter (fun i : Fin m => (j : ℕ) < i)).reverse).foldl
        (fun (B : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) => givensStepExact (pivF j i) i j B) B
    with hF
  have hall : ∀ k ≤ n,
      (∃ Q ∈ orthogonalGroup (Fin m) ℝ, Q * ((List.finRange n).take k).foldl F A = A) ∧
      ∀ q : Fin n, (q : ℕ) < k → ∀ r : Fin m, (q : ℕ) < r →
        ((List.finRange n).take k).foldl F A r q = 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [List.take_zero, List.foldl_nil]
      exact ⟨⟨1, one_mem _, Matrix.one_mul A⟩, fun q hq => absurd hq (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨hQ, hlow⟩ := ih (by omega)
      rw [List.take_succ_eq_append_getElem (by simpa using hk), List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have hget : (List.finRange n)[k]'(by simpa using hk) = ⟨k, hk⟩ := by simp
      rw [hget]
      obtain ⟨h1, h2, h3⟩ := givensColumnLoop A ⟨k, hk⟩ (pivF ⟨k, hk⟩)
        ((List.finRange m).filter (fun i : Fin m => k < i)).reverse
        (((List.finRange n).take k).foldl F A) (fun _ => False)
        (fun i hi => by
          have hi' := mem_rowsBelow_reverse.1 hi
          exact ⟨(hpiv ⟨k, hk⟩ i hi').1, (hpiv ⟨k, hk⟩ i hi').2, hi'⟩)
        (List.pairwise_reverse.2 (List.pairwise_filter.2
          (((List.sortedLT_finRange m).pairwise).imp fun {a b} hab ha _ =>
            ⟨hpw ⟨k, hk⟩ a b (by simpa using ha) hab, ne_of_gt hab⟩)))
        (fun _ h => h.elim) hQ hlow (fun _ h => h.elim)
      refine ⟨h1, fun q hq r hr => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | hq
      · exact h2 q hq r hr
      · have hqk : q = ⟨k, hk⟩ := Fin.ext hq
        subst hqk
        exact h3 r (Or.inr (mem_rowsBelow_reverse.2 hr))
  obtain ⟨⟨Q, hQo, hQB⟩, hlow⟩ := hall n le_rfl
  rw [List.take_of_length_le (by simp)] at hQB hlow
  exact ⟨Q, hQo, fun i j hji => hlow j j.2 i hji, hQB⟩

/-- **Algorithm 5.2.4** of [golub2013matrix], exact correctness. Let
$A \in \mathbb{R}^{m \times n}$, and let $R$ be the array that Algorithm 5.2.4 computes from $A$
in exact arithmetic. Then $R$ is upper triangular and $A = QR$ for an orthogonal
$Q \in \mathbb{R}^{m \times m}$.

**Generalization.** The source assumes $m \ge n$. The statement holds for all $m$ and $n$.

The factorization is `Matrix.IsQR`. $Q$ is the product $G_1 \cdots G_t$ of the rotations that
the algorithm applies. The proof specializes `GolubVanLoan.Chapter05.givensQR_columnwise` with
the pivot row $i - 1$. -/
theorem algorithm_5_2_4_spec (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ Q, IsQR A Q (Id.run (algorithm_5_2_4 pure A)) := by
  have hprog : Id.run (algorithm_5_2_4 pure A) =
      (List.finRange n).foldl (fun (B : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) =>
        (((List.finRange m).filter (fun i : Fin m => (j : ℕ) < i)).reverse).foldl
          (fun (B : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) =>
            givensStepExact (rowAbove i) i j B) B) A := by
    simp only [algorithm_5_2_4, List.idRun_foldlM]
    rfl
  rw [hprog]
  refine givensQR_columnwise A (fun _ i => rowAbove i) (fun j i hji => ⟨fun h => ?_, ?_⟩)
    (fun j a b hja hab h => ?_)
  · have := congrArg Fin.val h
    simp only [rowAbove] at this
    omega
  · change (j : ℕ) ≤ (i : ℕ) - 1
    omega
  · have := congrArg Fin.val h
    have hab' := Fin.lt_def.1 hab
    simp only [rowAbove] at this
    omega

/-- **Section 5.2.5** of [golub2013matrix], exact correctness of the first reordering of Givens QR.
Let $A \in \mathbb{R}^{m \times n}$ with $m \ge n$, and let $R$ be the array that the first
reordering computes from $A$ in exact arithmetic, with the rotations in the planes $(j, i)$
instead of $(i - 1, i)$. Then $R$ is upper triangular and $A = QR$ for an orthogonal $Q$. The
source says that one still emerges with the QR factorization.

The factorization is `Matrix.IsQR`. The proof specializes
`GolubVanLoan.Chapter05.givensQR_columnwise` with the pivot row $j$. -/
theorem givensQRDiagonalPivot_spec (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ Q, IsQR A Q (Id.run (givensQRDiagonalPivot pure hnm A)) := by
  have hprog : Id.run (givensQRDiagonalPivot pure hnm A) =
      (List.finRange n).foldl (fun (B : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) =>
        (((List.finRange m).filter (fun i : Fin m => (j : ℕ) < i)).reverse).foldl
          (fun (B : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) =>
            givensStepExact (Fin.castLE hnm j) i j B) B) A := by
    simp only [givensQRDiagonalPivot, List.idRun_foldlM]
    rfl
  rw [hprog]
  refine givensQR_columnwise A (fun j _ => Fin.castLE hnm j) (fun j i hji => ⟨fun h => ?_, ?_⟩)
    (fun j a b hja hab h => ?_)
  · have := congrArg Fin.val h
    simp only [Fin.val_castLE] at this
    omega
  · simp
  · have := congrArg Fin.val h
    have hab' := Fin.lt_def.1 hab
    simp only [Fin.val_castLE] at this
    omega

/-- The inner loop of the row-oriented Givens QR (§5.2.5, zeros introduced by row). Let $m \ge n$,
let $i$ be a row, and let $l$ be a strictly increasing list of columns $j < i$, each rotated in
the plane $(j, i)$. Let $T$ be a set of columns such that every column before a column of $l$ is
in $T$ or in $l$, and every column of $T$ is before every column of $l$. Let $QB = A_0$ with $Q$
orthogonal, let the rows of $B$ before $i$ vanish below the diagonal, and let $B(i, q) = 0$ for
$q \in T$. Then after the rotations there is an orthogonal $Q'$ with $Q'B' = A_0$, the rows
before $i$ still vanish below the diagonal, and $B'(i, q) = 0$ for every column $q$ in $T$ or in
$l$. -/
theorem givensRowLoop (A₀ : Matrix (Fin m) (Fin n) ℝ) (hnm : n ≤ m) (i : Fin m) :
    ∀ (l : List (Fin n)) (B : Matrix (Fin m) (Fin n) ℝ) (T : Fin n → Prop),
      (∀ j ∈ l, (j : ℕ) < i) → l.Pairwise (· < ·) →
      (∀ j ∈ l, ∀ q : Fin n, q < j → T q ∨ q ∈ l) →
      (∀ q, T q → ∀ j ∈ l, q < j) →
      (∃ Q ∈ orthogonalGroup (Fin m) ℝ, Q * B = A₀) →
      (∀ r : Fin m, r < i → ∀ q : Fin n, (q : ℕ) < r → B r q = 0) →
      (∀ q, T q → B i q = 0) →
      (∃ Q ∈ orthogonalGroup (Fin m) ℝ,
          Q * l.foldl (fun B j => givensStepExact (Fin.castLE hnm j) i j B) B = A₀) ∧
        (∀ r : Fin m, r < i → ∀ q : Fin n, (q : ℕ) < r →
          l.foldl (fun B j => givensStepExact (Fin.castLE hnm j) i j B) B r q = 0) ∧
        ∀ q, (T q ∨ q ∈ l) →
          l.foldl (fun B j => givensStepExact (Fin.castLE hnm j) i j B) B i q = 0 := by
  intro l
  induction l with
  | nil =>
    intro B T _ _ _ _ hQ hlow hT
    simp only [List.foldl_nil]
    exact ⟨hQ, hlow, fun q hq => hT q (by simpa using hq)⟩
  | cons j l ih =>
    intro B T hli hpw hcov hTl hQ hlow hT
    rw [List.pairwise_cons] at hpw
    have hji : (j : ℕ) < i := hli j List.mem_cons_self
    have hpi : Fin.castLE hnm j ≠ i := fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_castLE] at this
      omega
    have hpilt : Fin.castLE hnm j < i := Fin.lt_def.2 (by simpa using hji)
    have hz : ∀ q : Fin n, (q : ℕ) < j → B (Fin.castLE hnm j) q = 0 ∧ B i q = 0 := by
      intro q hq
      refine ⟨hlow _ hpilt q (by simpa using hq), ?_⟩
      rcases hcov j List.mem_cons_self q (Fin.lt_def.2 hq) with hTq | hql
      · exact hT q hTq
      · rcases List.mem_cons.1 hql with rfl | hql
        · exact absurd hq (lt_irrefl _)
        · exact absurd (Fin.lt_def.1 (hpw.1 q hql)) (by omega)
    obtain ⟨hcs, hB1, hi0, hrest, hleft⟩ := givensStepExact_spec hpi j B hz
    have hG := givensRotation_mem_orthogonalGroup hpi hcs
    rw [List.foldl_cons]
    have key := ih (givensStepExact (Fin.castLE hnm j) i j B) (fun q => T q ∨ q = j)
      (fun j' hj' => hli j' (List.mem_cons_of_mem _ hj')) hpw.2
      (fun j' hj' q hq => by
        rcases hcov j' (List.mem_cons_of_mem _ hj') q hq with h | h
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr h)
      (by
        rintro q (hq | rfl) j' hj'
        · exact hTl q hq j' (List.mem_cons_of_mem _ hj')
        · exact hpw.1 j' hj')
      (by rw [hB1]; exact exists_mul_eq_of_transpose_mul hG hQ)
      (fun r hr q hqr => by
        by_cases hrp : r = Fin.castLE hnm j
        · subst hrp
          rw [hleft _ q (by simpa using hqr)]
          exact hlow _ hr q hqr
        · rw [hrest r q hrp (ne_of_lt hr)]
          exact hlow r hr q hqr)
      (by
        rintro q (hq | rfl)
        · rw [hleft i q (Fin.lt_def.1 (hTl q hq j List.mem_cons_self))]
          exact hT q hq
        · exact hi0)
    obtain ⟨h1, h2, h3⟩ := key
    refine ⟨h1, h2, fun q hq => h3 q ?_⟩
    rcases hq with hq | hq
    · exact Or.inl (Or.inl hq)
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr hq

/-- **Section 5.2.5** of [golub2013matrix], exact correctness of the second reordering of Givens QR.
Let $A \in \mathbb{R}^{m \times n}$ with $m \ge n$, and let $R$ be the array that the
row-oriented Givens QR computes from $A$ in exact arithmetic (for $i = 2{:}m$, for
$j = 1{:}i-1$, rotations in the planes $(j, i)$). Then $R$ is upper triangular and $A = QR$ for
an orthogonal $Q$.

The factorization is `Matrix.IsQR`. The proof is an induction over the rows with
`GolubVanLoan.Chapter05.givensRowLoop`. -/
theorem givensQRByRow_spec (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ Q, IsQR A Q (Id.run (givensQRByRow pure hnm A)) := by
  set F : Matrix (Fin m) (Fin n) ℝ → Fin m → Matrix (Fin m) (Fin n) ℝ :=
    fun (B : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) =>
      ((List.finRange n).filter (fun j : Fin n => (j : ℕ) < i)).foldl
        (fun (B : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) =>
          givensStepExact (Fin.castLE hnm j) i j B) B
    with hF
  have hprog : Id.run (givensQRByRow pure hnm A) = (List.finRange m).foldl F A := by
    simp only [givensQRByRow, List.idRun_foldlM, hF]
    rfl
  have hall : ∀ k ≤ m,
      (∃ Q ∈ orthogonalGroup (Fin m) ℝ, Q * ((List.finRange m).take k).foldl F A = A) ∧
      ∀ r : Fin m, (r : ℕ) < k → ∀ q : Fin n, (q : ℕ) < r →
        ((List.finRange m).take k).foldl F A r q = 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [List.take_zero, List.foldl_nil]
      exact ⟨⟨1, one_mem _, Matrix.one_mul A⟩, fun r hr => absurd hr (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨hQ, hlow⟩ := ih (by omega)
      rw [List.take_succ_eq_append_getElem (by simpa using hk), List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have hget : (List.finRange m)[k]'(by simpa using hk) = ⟨k, hk⟩ := by simp
      rw [hget]
      obtain ⟨h1, h2, h3⟩ := givensRowLoop A hnm ⟨k, hk⟩
        ((List.finRange n).filter (fun j : Fin n => (j : ℕ) < k))
        (((List.finRange m).take k).foldl F A) (fun _ => False)
        (fun j hj => by simpa using hj) (((List.sortedLT_finRange n).pairwise).filter _)
        (fun j hj q hq => Or.inr (by
          simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hj ⊢
          exact lt_trans (Fin.lt_def.1 hq) hj))
        (fun _ h => h.elim) hQ
        (fun r hr q hq => hlow r (Fin.lt_def.1 hr) q hq) (fun _ h => h.elim)
      refine ⟨h1, fun r hr q hqr => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | hr
      · exact h2 r (Fin.lt_def.2 hr) q hqr
      · have hrk : r = ⟨k, hk⟩ := Fin.ext hr
        subst hrk
        exact h3 q (Or.inr (by simpa using hqr))
  obtain ⟨⟨Q, hQo, hQB⟩, hlow⟩ := hall m le_rfl
  rw [List.take_of_length_le (by simp)] at hQB hlow
  refine ⟨Q, hQo, fun i j hji => ?_, ?_⟩
  · rw [hprog]; exact hlow i i.2 j hji
  · rw [hprog]; exact hQB

/-! ### Hessenberg QR -/

/-- The product $G_0 G_1 \cdots G_{t-1}$ of the first $t$ rotations $G_j = G(j, j+1, \theta_j)$ of
Algorithm 5.2.5, for the pairs $(c_j, s_j)$ given by `cs` (0-based). -/
noncomputable def hessenbergRotationsProd {k : ℕ} (cs : Fin k → ℝ × ℝ) (t : ℕ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  (((List.finRange k).take t).map fun j =>
    givensRotation j.castSucc j.succ (cs j).1 (cs j).2).prod

/-- One more rotation: $G_0 \cdots G_t = (G_0 \cdots G_{t-1})\, G_t$ for $t < k$. -/
theorem hessenbergRotationsProd_succ {k : ℕ} (cs : Fin k → ℝ × ℝ) {t : ℕ} (ht : t < k) :
    hessenbergRotationsProd cs (t + 1) = hessenbergRotationsProd cs t *
      givensRotation (⟨t, ht⟩ : Fin k).castSucc (⟨t, ht⟩ : Fin k).succ
        (cs ⟨t, ht⟩).1 (cs ⟨t, ht⟩).2 := by
  unfold hessenbergRotationsProd
  have hget : (List.finRange k)[t]'(by simpa using ht) = ⟨t, ht⟩ := by simp
  rw [List.take_succ_eq_append_getElem (by simpa using ht), List.map_append, List.prod_append,
    hget, List.map_singleton, List.prod_singleton]

/-- A product of rotations in the adjacent planes $(j, j + 1)$, in increasing order, is upper
Hessenberg: for $t \le k$, the partial product $G_0 \cdots G_{t-1}$ vanishes below the first
subdiagonal, and its columns $q > t$ are the unit vectors $e_q$. For $t = k$ this shows that the
$Q = G_1 \cdots G_{n-1}$ of Algorithm 5.2.5 is upper Hessenberg. -/
theorem hessenbergRotationsProd_shape {k : ℕ} (cs : Fin k → ℝ × ℝ) :
    ∀ t ≤ k, (∀ r q : Fin (k + 1), (q : ℕ) + 1 < r → hessenbergRotationsProd cs t r q = 0) ∧
      ∀ r q : Fin (k + 1), t < (q : ℕ) →
        hessenbergRotationsProd cs t r q = if r = q then 1 else 0 := by
  intro t
  induction t with
  | zero =>
    intro _
    simp only [hessenbergRotationsProd, List.take_zero, List.map_nil, List.prod_nil]
    refine ⟨fun r q hqr => ?_, fun r q _ => rfl⟩
    rw [one_apply_ne (fun h => by rw [h] at hqr; omega)]
  | succ t ih =>
    intro ht
    obtain ⟨hH, hI⟩ := ih (by omega)
    set a : Fin (k + 1) := (⟨t, ht⟩ : Fin k).castSucc with ha
    set b : Fin (k + 1) := (⟨t, ht⟩ : Fin k).succ with hb
    have hav : (a : ℕ) = t := rfl
    have hbv : (b : ℕ) = t + 1 := rfl
    have hab : a ≠ b := fun h => by have := congrArg Fin.val h; omega
    have hP := hessenbergRotationsProd_succ cs ht
    rw [← ha, ← hb] at hP
    have hent : ∀ r q, hessenbergRotationsProd cs (t + 1) r q =
        if q = a then (cs ⟨t, ht⟩).1 * hessenbergRotationsProd cs t r a +
            -(cs ⟨t, ht⟩).2 * hessenbergRotationsProd cs t r b
        else if q = b then -(-(cs ⟨t, ht⟩).2) * hessenbergRotationsProd cs t r a +
            (cs ⟨t, ht⟩).1 * hessenbergRotationsProd cs t r b
        else hessenbergRotationsProd cs t r q := by
      intro r q
      rw [hP, givensRotation, mul_planeRotation_apply hab]
    have hrb : ∀ r : Fin (k + 1), t + 1 < (r : ℕ) → hessenbergRotationsProd cs t r b = 0 := by
      intro r hr
      rw [hI r b (by omega), ite_eq_right (fun h => by have := congrArg Fin.val h; omega)]
    refine ⟨fun r q hqr => ?_, fun r q hq => ?_⟩
    · rw [hent]
      split_ifs with hqa hqb
      · subst hqa
        rw [hH r a hqr, hrb r (by omega)]
        ring
      · subst hqb
        rw [hH r a (by omega), hrb r (by omega)]
        ring
      · exact hH r q hqr
    · have hqa : q ≠ a := fun h => by rw [h] at hq; omega
      have hqb : q ≠ b := fun h => by rw [h] at hq; omega
      rw [hent, ite_eq_right hqa, ite_eq_right hqb]
      exact hI r q (by omega)

/-- For indices $r, q \in \{0, \dots, k\}$, some index lies strictly between $q$ and $r$ if and only
if $q + 1 < r$. This translates the condition of `Matrix.IsUpperHessenberg`. -/
theorem exists_between_iff {k : ℕ} (r q : Fin (k + 1)) :
    (∃ w, q < w ∧ w < r) ↔ (q : ℕ) + 1 < r := by
  constructor
  · rintro ⟨w, hqw, hwr⟩
    have := Fin.lt_def.1 hqw
    have := Fin.lt_def.1 hwr
    omega
  · intro h
    exact ⟨⟨q + 1, by omega⟩, Fin.lt_def.2 (by simp),
      Fin.lt_def.2 (by simpa using h)⟩

/-- **Algorithm 5.2.5** of [golub2013matrix], exact correctness. Let
$A \in \mathbb{R}^{n \times n}$, $n \ge 1$, be upper Hessenberg, and let $(R, (c_j, s_j)_j)$ be
the output of Algorithm 5.2.5 in exact arithmetic. Let $Q = G_1 \cdots G_{n-1}$, where
$G_j = G(j, j+1, \theta_j)$ is the Givens rotation of the returned pair $(c_j, s_j)$. Then $Q$
is orthogonal, $R$ is upper triangular, $A = QR$, and $Q$ is upper Hessenberg.

The order is $n = k + 1$. The rotation $G_j$ is `GolubVanLoan.Chapter05.givensRotation` in the
plane of the 0-based rows $j$ and $j + 1$, and the product is taken in increasing order of $j$.
The factorization is `Matrix.IsQR`. -/
theorem algorithm_5_2_5_spec {k : ℕ} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : A.IsUpperHessenberg) :
    IsQR A (List.ofFn fun j : Fin k => givensRotation j.castSucc j.succ
          ((Id.run (algorithm_5_2_5 pure A)).2 j).1 ((Id.run (algorithm_5_2_5 pure A)).2 j).2).prod
        (Id.run (algorithm_5_2_5 pure A)).1 ∧
      (List.ofFn fun j : Fin k => givensRotation j.castSucc j.succ
          ((Id.run (algorithm_5_2_5 pure A)).2 j).1
          ((Id.run (algorithm_5_2_5 pure A)).2 j).2).prod.IsUpperHessenberg := by
  have hofn : ∀ cs : Fin k → ℝ × ℝ, (List.ofFn fun j : Fin k =>
      givensRotation j.castSucc j.succ (cs j).1 (cs j).2).prod = hessenbergRotationsProd cs k := by
    intro cs
    rw [hessenbergRotationsProd, List.take_of_length_le (by simp), List.ofFn_eq_map]
  rw [hofn]
  set F := fun (st : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × (Fin k → ℝ × ℝ)) (j : Fin k) =>
    (givensStepExact j.castSucc j.succ j.castSucc st.1, Function.update st.2 j
      (Id.run (algorithm_5_1_3 pure (st.1 j.castSucc j.castSucc) (st.1 j.succ j.castSucc))))
    with hF
  have hprog :
      Id.run (algorithm_5_2_5 pure A) = (List.finRange k).foldl F (A, fun _ => (1, 0)) := by
    simp only [algorithm_5_2_5, List.idRun_foldlM, hF]
    rfl
  have hAH : ∀ r q : Fin (k + 1), (q : ℕ) + 1 < r → A r q = 0 :=
    fun r q h => hA r q ((exists_between_iff r q).2 h)
  have hall : ∀ t ≤ k,
      hessenbergRotationsProd (((List.finRange k).take t).foldl F (A, fun _ => (1, 0))).2 t *
          (((List.finRange k).take t).foldl F (A, fun _ => (1, 0))).1 = A ∧
        (∀ j : Fin k, (j : ℕ) < t →
          ((((List.finRange k).take t).foldl F (A, fun _ => (1, 0))).2 j).1 ^ 2 +
            ((((List.finRange k).take t).foldl F (A, fun _ => (1, 0))).2 j).2 ^ 2 = 1) ∧
        (∀ q : Fin (k + 1), (q : ℕ) < t → ∀ r : Fin (k + 1), (q : ℕ) < r →
          (((List.finRange k).take t).foldl F (A, fun _ => (1, 0))).1 r q = 0) ∧
        ∀ r q : Fin (k + 1), (q : ℕ) + 1 < r →
          (((List.finRange k).take t).foldl F (A, fun _ => (1, 0))).1 r q = 0 := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨by simp [hessenbergRotationsProd], fun j hj => absurd hj (Nat.not_lt_zero _),
        fun q hq => absurd hq (Nat.not_lt_zero _), ?_⟩
      simpa using hAH
    | succ t ih =>
      intro ht
      obtain ⟨hQ, hunit, htri, hhess⟩ := ih (by omega)
      rw [List.take_succ_eq_append_getElem (by simpa using ht), List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have hget : (List.finRange k)[t]'(by simpa using ht) = ⟨t, ht⟩ := by simp
      rw [hget]
      set st := ((List.finRange k).take t).foldl F (A, fun _ => (1, 0)) with hst
      set j : Fin k := ⟨t, ht⟩ with hj
      set a : Fin (k + 1) := j.castSucc with ha
      set b : Fin (k + 1) := j.succ with hb
      have hav : (a : ℕ) = t := rfl
      have hbv : (b : ℕ) = t + 1 := rfl
      have hab : a ≠ b := fun h => by have := congrArg Fin.val h; omega
      have hz : ∀ q : Fin (k + 1), (q : ℕ) < (a : ℕ) → st.1 a q = 0 ∧ st.1 b q = 0 :=
        fun q hq => ⟨htri q (by omega) a (by omega), htri q (by omega) b (by omega)⟩
      obtain ⟨hcs, hB1, hi0, hrest, hleft⟩ := givensStepExact_spec hab a st.1 hz
      have hG := givensRotation_mem_orthogonalGroup hab hcs
      have hFst : F st j = (givensStepExact a b a st.1, Function.update st.2 j
          (Id.run (algorithm_5_1_3 pure (st.1 a a) (st.1 b a)))) := rfl
      rw [hFst]
      dsimp only
      refine ⟨?_, fun j' hj' => ?_, fun q hq r hqr => ?_, fun r q hqr => ?_⟩
      · -- the product gains the rotation of step `t`
        rw [hessenbergRotationsProd_succ _ ht, ← hj]
        have hsame : hessenbergRotationsProd (Function.update st.2 j
            (Id.run (algorithm_5_1_3 pure (st.1 a a) (st.1 b a)))) t =
            hessenbergRotationsProd st.2 t := by
          unfold hessenbergRotationsProd
          congr 1
          refine List.map_congr_left fun j' hj' => ?_
          have hne : j' ≠ j := fun h => by
            have := lt_of_mem_take_finRange hj'
            rw [h] at this
            simp [hj] at this
          rw [Function.update_of_ne hne]
        rw [hsame, Function.update_self, ← ha, ← hb, hB1, Matrix.mul_assoc,
          ← Matrix.mul_assoc _ (_ᵀ), (mem_orthogonalGroup_iff _ _).1 hG, Matrix.one_mul, hQ]
      · by_cases hjj : j' = j
        · subst hjj
          rw [Function.update_self]
          exact hcs
        · rw [Function.update_of_ne hjj]
          refine hunit j' ?_
          have : (j' : ℕ) ≠ t := fun h => hjj (Fin.ext h)
          omega
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | hq
        · rw [hleft r q (by omega)]
          exact htri q hq r hqr
        · have hqa : q = a := Fin.ext (by omega)
          subst hqa
          by_cases hrb : r = b
          · rw [hrb]; exact hi0
          · have hra : r ≠ a := fun h => by rw [h] at hqr; omega
            rw [hrest r _ hra hrb]
            refine hhess r _ ?_
            have : (r : ℕ) ≠ t + 1 := fun h => hrb (Fin.ext h)
            omega
      · by_cases hra : r = a
        · subst hra
          rw [hleft _ q (by omega)]
          exact hhess _ q hqr
        · by_cases hrb : r = b
          · subst hrb
            rw [hleft _ q (by omega)]
            exact hhess _ q hqr
          · rw [hrest r q hra hrb]
            exact hhess r q hqr
  obtain ⟨hQ, hunit, htri, -⟩ := hall k le_rfl
  rw [List.take_of_length_le (by simp)] at hQ hunit htri
  rw [hprog]
  refine ⟨⟨?_, fun i j hji => ?_, hQ⟩, fun r q hrq => ?_⟩
  · unfold hessenbergRotationsProd
    rw [List.take_of_length_le (by simp)]
    refine list_prod_mem fun G hG => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hG
    exact givensRotation_mem_orthogonalGroup
      (show j.castSucc < j.succ from Fin.castSucc_lt_succ).ne (hunit j j.2)
  · have hjk : (j : ℕ) < k := by have := i.2; omega
    exact htri j hjk i hji
  · exact ((hessenbergRotationsProd_shape _ k le_rfl).1 r q ((exists_between_iff r q).1 hrq))

end GivensQRSpec

section Sweeps

/-! ### The Givens sweeps of §6.5: exact semantics -/

/-- One exact Givens step on a pair $(Q, H)$ with the pair $(c, s)$:
$H \leftarrow G(p, q, \theta)^T H$ and $Q \leftarrow Q\, G(p, q, \theta)$. -/
noncomputable def givensPairStep {m n : ℕ} (p q : Fin m) (cs : ℝ × ℝ)
    (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ :=
  (st.1 * givensRotation p q cs.1 cs.2, (givensRotation p q cs.1 cs.2)ᵀ * st.2)

/-- If $p \neq q$, $c^2 + s^2 = 1$ and $Q$ is orthogonal, then the $Q$ of an exact Givens step is
orthogonal. -/
theorem givensPairStep_mem {m n : ℕ} {p q : Fin m} (hpq : p ≠ q) {cs : ℝ × ℝ}
    (hcs : cs.1 ^ 2 + cs.2 ^ 2 = 1) {st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ}
    (hQ : st.1 ∈ orthogonalGroup (Fin m) ℝ) :
    (givensPairStep p q cs st).1 ∈ orthogonalGroup (Fin m) ℝ :=
  mul_mem hQ (givensRotation_mem_orthogonalGroup hpq hcs)

/-- If $p \neq q$ and $c^2 + s^2 = 1$, an exact Givens step keeps the product $QH$. -/
theorem givensPairStep_mul {m n : ℕ} {p q : Fin m} (hpq : p ≠ q) {cs : ℝ × ℝ}
    (hcs : cs.1 ^ 2 + cs.2 ^ 2 = 1) (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) :
    (givensPairStep p q cs st).1 * (givensPairStep p q cs st).2 = st.1 * st.2 := by
  have hG := (mem_orthogonalGroup_iff _ ℝ).1
    (givensRotation_mem_orthogonalGroup hpq hcs)
  simp only [givensPairStep]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (givensRotation p q cs.1 cs.2), hG,
    Matrix.one_mul]

/-- Let $p \neq q$. After an exact Givens step, row $p$ of $H$ is $c\,H(p, :) - s\,H(q, :)$, row $q$
is $s\,H(p, :) + c\,H(q, :)$, and the other rows are unchanged. -/
theorem givensPairStep_apply {m n : ℕ} {p q : Fin m} (hpq : p ≠ q) (cs : ℝ × ℝ)
    (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) (r : Fin m) (l : Fin n) :
    (givensPairStep p q cs st).2 r l =
      if r = p then cs.1 * st.2 p l - cs.2 * st.2 q l
      else if r = q then cs.2 * st.2 p l + cs.1 * st.2 q l else st.2 r l :=
  givensRotation_transpose_mul_apply hpq cs.1 cs.2 st.2 r l

/-- Let $p \neq q$. The exact Givens step with $[c, s] = \operatorname{givens}(H(p, l), H(q, l))$
makes the entry $H(q, l)$ zero. -/
theorem givensPairStep_zero {m n : ℕ} {p q : Fin m} (hpq : p ≠ q) (l : Fin n)
    (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) :
    (givensPairStep p q (Id.run (algorithm_5_1_3 pure (st.2 p l) (st.2 q l))) st).2 q l
      = 0 := by
  rw [givensPairStep_apply hpq, ite_eq_right hpq.symm, ite_eq_left rfl]
  exact (algorithm_5_1_3_spec _ _).2.1

/-- Let $p \neq q$. An exact Givens step leaves the entry $H(r, l)$ zero if $H(p, l) = H(q, l) = 0$
in the case $r \in \{p, q\}$, and if $H(r, l) = 0$ in the other case. -/
theorem givensPairStep_eq_zero {m n : ℕ} {p q : Fin m} (hpq : p ≠ q) (cs : ℝ × ℝ)
    (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) {r : Fin m} {l : Fin n}
    (hin : r = p ∨ r = q → st.2 p l = 0 ∧ st.2 q l = 0)
    (hr : r ≠ p → r ≠ q → st.2 r l = 0) :
    (givensPairStep p q cs st).2 r l = 0 := by
  rw [givensPairStep_apply hpq]
  split_ifs with h1 h2
  · obtain ⟨hp, hq⟩ := hin (Or.inl h1)
    rw [hp, hq]; ring
  · obtain ⟨hp, hq⟩ := hin (Or.inr h2)
    rw [hp, hq]; ring
  · exact hr h1 h2

/-- If $r = p$ or $r = q$ in `Fin m`, then the same holds for the natural number values. -/
private theorem val_eq_or_of_eq_or {m : ℕ} {p q r : Fin m} (h : r = p ∨ r = q) :
    (r : ℕ) = p ∨ (r : ℕ) = q := h.imp (congrArg _) (congrArg _)

/-- The exact step of `GolubVanLoan.Chapter05.givensHessenbergSweep` at index $j$. -/
private noncomputable def hessStep {m n : ℕ}
    (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) (j : ℕ) :
    Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ :=
  if h : j + 1 < m ∧ j < n then
    givensPairStep ⟨j, by omega⟩ ⟨j + 1, h.1⟩
      (Id.run (algorithm_5_1_3 pure (st.2 ⟨j, by omega⟩ ⟨j, h.2⟩)
        (st.2 ⟨j + 1, h.1⟩ ⟨j, h.2⟩))) st
  else st

private theorem idRun_givensHessenbergSweep {m n : ℕ} (a count : ℕ)
    (Q : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (givensHessenbergSweep pure a count Q H) =
      (List.range' a count).foldl hessStep (Q, H) := by
  rw [givensHessenbergSweep, List.idRun_foldlM]
  congr 1
  funext st j
  unfold hessStep
  split_ifs with h
  · have hpq : (⟨j, by omega⟩ : Fin m) ≠ ⟨j + 1, h.1⟩ := fun e => by simp [Fin.ext_iff] at e
    simp only [Id.run_bind, Id.run_pure]
    rw [givensApplyLeft_spec_of_forall_mem hpq _ _ (List.nodup_finRange n)
      (List.mem_finRange), givensApplyRight_spec_of_forall_mem hpq _ _
      (List.nodup_finRange m) (List.mem_finRange)]
    rfl
  · rfl

/-- **Section 6.5.1** of [golub2013matrix], exact semantics of the top-down Givens sweep. Let
$Q \in \mathbb{R}^{m \times m}$ be orthogonal and $H \in \mathbb{R}^{m \times n}$ with $QH = A$.
Let $H$ be upper Hessenberg, $h_{ij} = 0$ for $i > j + 1$, and upper triangular in its columns
before $a$, $h_{ij} = 0$ for $i > j$ and $j < a$. If the sweep from column $a$ with `count`
steps reaches the last column or the last row, that is, $n \le a + \mathrm{count}$ or
$m \le a + \mathrm{count} + 1$, then its output $(Q', H')$ in exact arithmetic is a QR
factorization of $A$: $Q'$ is orthogonal, $H'$ is upper triangular, and $Q'H' = A$.

Each rotation zeroes the subdiagonal entry of its column and keeps the earlier columns. The
factorization is `Matrix.IsQR`. -/
theorem givensHessenbergSweep_spec {m n : ℕ} {a count : ℕ} {A H : Matrix (Fin m) (Fin n) ℝ}
    {Q : Matrix (Fin m) (Fin m) ℝ} (hQ : Q ∈ orthogonalGroup (Fin m) ℝ) (hQH : Q * H = A)
    (hH : ∀ (i : Fin m) (j : Fin n), (j : ℕ) + 1 < i → H i j = 0)
    (ha : ∀ (i : Fin m) (j : Fin n), (j : ℕ) < i → (j : ℕ) < a → H i j = 0)
    (hc : n ≤ a + count ∨ m ≤ a + count + 1) :
    IsQR A (Id.run (givensHessenbergSweep pure a count Q H)).1
      (Id.run (givensHessenbergSweep pure a count Q H)).2 := by
  set Inv : ℕ → Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ → Prop := fun t st =>
    st.1 ∈ orthogonalGroup (Fin m) ℝ ∧ st.1 * st.2 = A ∧
      (∀ (i : Fin m) (j : Fin n), (j : ℕ) + 1 < i → st.2 i j = 0) ∧
      ∀ (i : Fin m) (j : Fin n), (j : ℕ) < i → (j : ℕ) < a + t → st.2 i j = 0 with hInv
  have hstep : ∀ t st, Inv t st → Inv (t + 1) (hessStep st (a + t)) := by
    rintro t st ⟨hQ, hQH, hH, hlow⟩
    unfold hessStep
    split_ifs with h
    · set p : Fin m := ⟨a + t, by omega⟩ with hp
      set q : Fin m := ⟨a + t + 1, h.1⟩ with hq
      set jc : Fin n := ⟨a + t, h.2⟩ with hjc
      have hpv : (p : ℕ) = a + t := rfl
      have hqv : (q : ℕ) = a + t + 1 := rfl
      have hpq : p ≠ q := fun e => by have := congrArg Fin.val e; omega
      have hcs := (algorithm_5_1_3_spec (st.2 p jc) (st.2 q jc)).1
      refine ⟨givensPairStep_mem hpq hcs hQ, by rw [givensPairStep_mul hpq hcs, hQH],
        fun i l hil => ?_, fun i l hil hl => ?_⟩
      · refine givensPairStep_eq_zero hpq _ st (fun hi => ?_) fun _ _ => hH i l hil
        have hiv := val_eq_or_of_eq_or hi
        refine ⟨?_, hH q l (by omega)⟩
        by_cases hl2 : (l : ℕ) + 1 < a + t
        · exact hH p l (by omega)
        · exact hlow p l (by omega) (by omega)
      · by_cases hlj : (l : ℕ) < a + t
        · refine givensPairStep_eq_zero hpq _ st (fun hi => ⟨hlow p l (by omega) hlj,
            hH q l (by omega)⟩) fun _ _ => hlow i l hil hlj
        · have hl' : l = jc := Fin.ext (by simp [hjc]; omega)
          by_cases hi : i = q
          · rw [hi, hl']
            exact givensPairStep_zero hpq jc st
          · have hip : i ≠ p := by
              intro e
              rw [e] at hil
              omega
            rw [givensPairStep_apply hpq, ite_eq_right hip, ite_eq_right hi]
            exact hH i l (by
              have : (i : ℕ) ≠ a + t + 1 := fun e => hi (Fin.ext (by rw [hqv, e]))
              omega)
    · refine ⟨hQ, hQH, hH, fun i l hil hl => ?_⟩
      by_cases hlj : (l : ℕ) < a + t
      · exact hlow i l hil hlj
      · exfalso
        have := i.isLt
        have := l.isLt
        omega
  have hall : ∀ t, Inv t ((List.range' a t).foldl hessStep (Q, H)) := by
    intro t
    induction t with
    | zero => exact ⟨hQ, hQH, hH, fun i j hij hj => ha i j hij (by simpa using hj)⟩
    | succ t ih =>
      rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, one_mul]
      exact hstep t _ ih
  obtain ⟨hQ', hQH', -, hlow'⟩ := hall count
  rw [idRun_givensHessenbergSweep]
  refine ⟨hQ', fun i j hij => hlow' i j hij ?_, hQH'⟩
  have := i.isLt
  have := j.isLt
  omega

/-- The exact step of `GolubVanLoan.Chapter05.givensVectorSweep` at index $j$. -/
private noncomputable def vecStep {m n : ℕ}
    (st : (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) (j : ℕ) :
    (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ :=
  if h : j + 1 < m then
    let cs := Id.run (algorithm_5_1_3 pure (st.1 ⟨j, by omega⟩) (st.1 ⟨j + 1, h⟩))
    ((givensRotation ⟨j, by omega⟩ ⟨j + 1, h⟩ cs.1 cs.2)ᵀ *ᵥ st.1,
      givensPairStep ⟨j, by omega⟩ ⟨j + 1, h⟩ cs (st.2.1, st.2.2))
  else st

private theorem idRun_givensVectorSweep {m n : ℕ} (b count : ℕ) (w : Fin m → ℝ)
    (Q : Matrix (Fin m) (Fin m) ℝ) (R : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (givensVectorSweep pure b count w Q R) =
      (List.range' b count).reverse.foldl vecStep (w, Q, R) := by
  rw [givensVectorSweep, List.idRun_foldlM]
  congr 1
  funext st j
  unfold vecStep
  split_ifs with h
  · have hpq : (⟨j, by omega⟩ : Fin m) ≠ ⟨j + 1, h⟩ := fun e => by simp [Fin.ext_iff] at e
    simp only [Id.run_bind, Id.run_pure]
    rw [givensRotateVec_pure hpq, givensApplyLeft_spec_of_forall_mem hpq _ _
      (List.nodup_finRange n) (List.mem_finRange), givensApplyRight_spec_of_forall_mem hpq
      _ _ (List.nodup_finRange m) (List.mem_finRange)]
    rfl
  · rfl

/-- **Section 6.5.1** of [golub2013matrix], exact semantics of the bottom-up Givens sweep. Let
$w \in \mathbb{R}^m$, $Q \in \mathbb{R}^{m \times m}$ and $R \in \mathbb{R}^{m \times n}$, let
$R$ be upper triangular, $r_{ij} = 0$ for $i > j$, and let $w_i = 0$ for
$i > b + \mathrm{count}$. Let $(w', Q', R')$ be the output of the sweep in exact arithmetic.
Then:

* there is an orthogonal $P \in \mathbb{R}^{m \times m}$ with $w' = Pw$, $Q' = QP^T$ and
  $R' = PR$;
* $w'_i = 0$ for $i > b$;
* $R'$ is upper Hessenberg: $r'_{ij} = 0$ for $i > j + 1$;
* $R'$ is still upper triangular in its columns before $b$: $r'_{ij} = 0$ for $i > j$ and
  $j < b$.

Indices are 0-based. $Q$ need not be orthogonal. -/
theorem givensVectorSweep_spec {m n : ℕ} (b count : ℕ) (w : Fin m → ℝ)
    (Q : Matrix (Fin m) (Fin m) ℝ) (R : Matrix (Fin m) (Fin n) ℝ)
    (hR : ∀ (i : Fin m) (j : Fin n), (j : ℕ) < i → R i j = 0)
    (hw : ∀ i : Fin m, b + count < i → w i = 0) :
    (∃ P ∈ orthogonalGroup (Fin m) ℝ,
      (Id.run (givensVectorSweep pure b count w Q R)).1 = P *ᵥ w ∧
      (Id.run (givensVectorSweep pure b count w Q R)).2.1 = Q * Pᵀ ∧
      (Id.run (givensVectorSweep pure b count w Q R)).2.2 = P * R) ∧
    (∀ i : Fin m, b < i → (Id.run (givensVectorSweep pure b count w Q R)).1 i = 0) ∧
    (∀ (i : Fin m) (j : Fin n), (j : ℕ) + 1 < i →
      (Id.run (givensVectorSweep pure b count w Q R)).2.2 i j = 0) ∧
    ∀ (i : Fin m) (j : Fin n), (j : ℕ) < i → (j : ℕ) < b →
      (Id.run (givensVectorSweep pure b count w Q R)).2.2 i j = 0 := by
  set V : ℕ → (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ → Prop :=
    fun K st => (∃ P ∈ orthogonalGroup (Fin m) ℝ, st.1 = P *ᵥ w ∧ st.2.1 = Q * Pᵀ ∧
      st.2.2 = P * R) ∧ (∀ i : Fin m, K < i → st.1 i = 0) ∧
      (∀ (i : Fin m) (j : Fin n), (j : ℕ) + 1 < i → st.2.2 i j = 0) ∧
      ∀ (i : Fin m) (j : Fin n), (j : ℕ) < i → (j : ℕ) < K → st.2.2 i j = 0 with hV
  have hstep : ∀ j st, V (j + 1) st → V j (vecStep st j) := by
    rintro j ⟨x, Q', R'⟩ ⟨⟨P, hP, hx, hQ', hR'⟩, hxz, hH, hlow⟩
    dsimp only at hx hQ' hR' hxz hH hlow
    unfold vecStep
    split_ifs with h
    · set p : Fin m := ⟨j, by omega⟩ with hp
      set q : Fin m := ⟨j + 1, h⟩ with hq
      have hpv : (p : ℕ) = j := rfl
      have hqv : (q : ℕ) = j + 1 := rfl
      have hpq : p ≠ q := fun e => by have := congrArg Fin.val e; omega
      obtain ⟨hcs, hz, -⟩ := algorithm_5_1_3_spec (x p) (x q)
      set cs := Id.run (algorithm_5_1_3 pure (x p) (x q)) with hcsdef
      set G := givensRotation p q cs.1 cs.2 with hG
      have hGo : G ∈ orthogonalGroup (Fin m) ℝ :=
        givensRotation_mem_orthogonalGroup hpq hcs
      have hGto : Gᵀ ∈ orthogonalGroup (Fin m) ℝ := by
        rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose]
        exact Unitary.star_mem hGo
      have happ := givensPairStep_apply hpq cs (Q', R')
      dsimp only at happ
      refine ⟨⟨Gᵀ * P, mul_mem hGto hP, ?_, ?_, ?_⟩, fun i hi => ?_, fun i l hil => ?_,
        fun i l hil hl => ?_⟩
      · dsimp only
        rw [hx, mulVec_mulVec]
      · change Q' * G = Q * (Gᵀ * P)ᵀ
        rw [hQ', transpose_mul, transpose_transpose, Matrix.mul_assoc]
      · change Gᵀ * R' = Gᵀ * P * R
        rw [hR', Matrix.mul_assoc]
      · dsimp only
        rw [givensRotation_transpose_mulVec_apply hpq]
        by_cases hiq : i = q
        · rw [ite_eq_right (by rw [hiq]; exact hpq.symm), ite_eq_left hiq]
          exact hz
        · have hip : i ≠ p := fun e => by rw [e] at hi; omega
          rw [ite_eq_right hip, ite_eq_right hiq]
          exact hxz i (by
            have : (i : ℕ) ≠ j + 1 := fun e => hiq (Fin.ext (by rw [hqv, e]))
            omega)
      · change (givensPairStep p q cs (Q', R')).2 i l = 0
        refine givensPairStep_eq_zero hpq cs _ (fun hi => ?_) fun _ _ => hH i l hil
        have hiv := val_eq_or_of_eq_or hi
        refine ⟨?_, hH q l (by omega)⟩
        by_cases hl2 : (l : ℕ) + 1 < j
        · exact hH p l (by omega)
        · exact hlow p l (by omega) (by omega)
      · change (givensPairStep p q cs (Q', R')).2 i l = 0
        exact givensPairStep_eq_zero hpq cs _ (fun _ => ⟨hlow p l (by omega) (by omega),
          hH q l (by omega)⟩) fun _ _ => hlow i l hil (by omega)
    · refine ⟨⟨P, hP, hx, hQ', hR'⟩, fun i hi => ?_, hH, fun i l hil hl => hlow i l hil (by omega)⟩
      exfalso
      have := i.isLt
      omega
  have hall : ∀ t st, V (b + t) st → V b ((List.range' b t).reverse.foldl vecStep st) := by
    intro t
    induction t with
    | zero => intro st h; simpa using h
    | succ t ih =>
      intro st h
      rw [List.range'_concat, List.reverse_append, one_mul]
      simp only [List.reverse_singleton, List.singleton_append, List.foldl_cons]
      exact ih _ (hstep (b + t) st h)
  have h0 : V (b + count) (w, Q, R) :=
    ⟨⟨1, one_mem _, by simp, by simp, by simp⟩, hw, fun i j hij => hR i j (by omega),
      fun i j hij _ => hR i j hij⟩
  rw [idRun_givensVectorSweep]
  exact hall count _ h0

end Sweeps

/-! ### Givens QR: rounding errors -/

section GivensQRRounding

/-- Let $p \neq i$, $c^2 + s^2 = 1$ and $\gamma \ge 0$, and let $d \in \mathbb{R}^M$ vanish off the
entry $p$, with $|d_p| \le \gamma(|c|\,|x_p| + |s|\,|x_i|)$. Then $\|d\|_2 \le \gamma \|x\|_2$,
by the Cauchy–Schwarz inequality on $(x_p, x_i)$. This bounds the error made when the computed
second entry of a rotation is replaced by an exact zero. -/
theorem norm_le_of_single_of_abs_le {M : ℕ} {p i : Fin M} (hpi : p ≠ i) {c s γ : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) (hγ : 0 ≤ γ) {x d : Fin M → ℝ} (hd : ∀ l, l ≠ p → d l = 0)
    (hdp : |d p| ≤ γ * (|c| * |x p| + |s| * |x i|)) :
    ‖(toLp 2 d : EuclideanSpace ℝ (Fin M))‖ ≤ γ * ‖(toLp 2 x : EuclideanSpace ℝ (Fin M))‖ := by
  have hnorm : ‖(toLp 2 d : EuclideanSpace ℝ (Fin M))‖ = |d p| := by
    rw [EuclideanSpace.norm_eq, Finset.sum_eq_single p (fun l _ hl => by simp [hd l hl])
      (by simp)]
    simp [Real.sqrt_sq_eq_abs]
  have hcs2 : (|c| * |x p| + |s| * |x i|) ^ 2 ≤ x p ^ 2 + x i ^ 2 := by
    have := sq_abs c; have := sq_abs s; have := sq_abs (x p); have := sq_abs (x i)
    nlinarith [sq_nonneg (|c| * |x i| - |s| * |x p|)]
  have hle : |c| * |x p| + |s| * |x i| ≤ ‖(toLp 2 x : EuclideanSpace ℝ (Fin M))‖ := by
    have h2 := hcs2.trans (sq_add_sq_le_norm_toLp_sq hpi x)
    have h0 : 0 ≤ |c| * |x p| + |s| * |x i| := by positivity
    nlinarith [norm_nonneg (toLp 2 x : EuclideanSpace ℝ (Fin M))]
  rw [hnorm]
  exact hdp.trans (mul_le_mul_of_nonneg_left hle hγ)

/-- Column $q$ of a product is the product with column $q$: $(GX)(:, q) = G\,X(:, q)$. -/
theorem col_mul_eq_mulVec {M N : ℕ} (G : Matrix (Fin M) (Fin M) ℝ)
    (X : Matrix (Fin M) (Fin N) ℝ) (q : Fin N) : (G * X).col q = G *ᵥ X.col q := by
  ext r
  rfl

/-- One step of the columnwise accumulation of backward errors, Lemma 19.3 of [higham2002accuracy].
Let $Q$ and $G$ be orthogonal, let $\varepsilon \ge 0$, let $QC = A + E$ with $\|E(:, q)\|_2 \le
((1 + \varepsilon)^t - 1)\|A(:, q)\|_2$ for every column $q$, and let $\|(C' - G^T C)(:, q)\|_2
\le \varepsilon \|C(:, q)\|_2$ for every $q$. Then $(QG)C' = A + E'$ with $\|E'(:, q)\|_2 \le
((1 + \varepsilon)^{t+1} - 1)\|A(:, q)\|_2$ for every $q$. This is
`FloatingPoint.exists_eq_mul_add_of_step` for the inverse factor $Q^T$. -/
theorem exists_mul_eq_add_of_step {M N : ℕ} {A C C' : Matrix (Fin M) (Fin N) ℝ}
    {Q G : Matrix (Fin M) (Fin M) ℝ} (hQ : Q ∈ orthogonalGroup (Fin M) ℝ)
    (hG : G ∈ orthogonalGroup (Fin M) ℝ) {E : Matrix (Fin M) (Fin N) ℝ} (hQE : Q * C = A + E)
    {ε : ℝ} (hε : 0 ≤ ε) {t : ℕ}
    (hE : ∀ q, ‖(toLp 2 (E.col q) : EuclideanSpace ℝ (Fin M))‖ ≤
      ((1 + ε) ^ t - 1) * ‖(toLp 2 (A.col q) : EuclideanSpace ℝ (Fin M))‖)
    (hF : ∀ q, ‖(toLp 2 ((C' - Gᵀ * C).col q) : EuclideanSpace ℝ (Fin M))‖ ≤
      ε * ‖(toLp 2 (C.col q) : EuclideanSpace ℝ (Fin M))‖) :
    ∃ E' : Matrix (Fin M) (Fin N) ℝ, (Q * G) * C' = A + E' ∧
      ∀ q, ‖(toLp 2 (E'.col q) : EuclideanSpace ℝ (Fin M))‖ ≤
        ((1 + ε) ^ (t + 1) - 1) * ‖(toLp 2 (A.col q) : EuclideanSpace ℝ (Fin M))‖ := by
  have hC : C = Qᵀ * (A + E) := by
    rw [← hQE, ← Matrix.mul_assoc, (mem_orthogonalGroup_iff' _ _).1 hQ, Matrix.one_mul]
  obtain ⟨E', hE', hb⟩ := FloatingPoint.exists_eq_mul_add_of_step
    (transpose_mem_unitaryGroup_iff.2 hG) (transpose_mem_unitaryGroup_iff.2 hQ) hε hC hE hF
  refine ⟨E', ?_, hb⟩
  rw [hE']
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc G Gᵀ, (mem_orthogonalGroup_iff _ _).1 hG, Matrix.one_mul,
    ← Matrix.mul_assoc Q Qᵀ, (mem_orthogonalGroup_iff _ _).1 hQ, Matrix.one_mul]

/-- The array $B$ of a run of Algorithm 5.2.5 with the computed entries $(j + 1, j)$ of its first
$t$ rotations set to zero; in exact arithmetic these entries are zero. -/
def hessenbergJunkClean {k : ℕ} (t : ℕ) (B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  of fun r q => if (q : ℕ) < t ∧ (r : ℕ) = q + 1 then 0 else B r q

/-- **Algorithm 5.2.5** of [golub2013matrix], backward error. Let $A \in \mathbb{R}^{n \times n}$,
$n \ge 1$, be upper Hessenberg, and let the unit roundoff $u$ satisfy $15u < 1$. Let
$(R', (\hat c_j, \hat s_j)_j)$ be a run of Algorithm 5.2.5 on $A$ in the rounding model `fp`,
and let $\hat R$ be the upper triangular part of $R'$. Then there are an orthogonal $Q$ and
$E \in \mathbb{R}^{n \times n}$ with
$$Q \hat R = A + E, \qquad \|E(:, q)\|_2 \le \bigl((1 + \sqrt{2}\,\gamma_{15})^{n-1} - 1\bigr)
  \|A(:, q)\|_2$$
for every column $q$.

The bound applies the rounding analysis of a sequence of rotations in §5.1.12 to the $n - 1$
rotations of the algorithm. $Q$ is the product of the exact rotations of which the computed
pairs are relative perturbations (`GolubVanLoan.Chapter05.algorithm_5_1_3_rounding`). The
computed subdiagonal entries, which are zero in exact arithmetic, are not part of $\hat R$
(`GolubVanLoan.Chapter05.upperPart`). The order is $n = k + 1$. -/
theorem algorithm_5_2_5_rounding {fp : RoundingModel ℝ} (hu : ((15 : ℕ) : ℝ) * fp.u < 1) {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (hA : A.IsUpperHessenberg)
    {st : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × (Fin k → ℝ × ℝ)}
    (h : st ∈ (algorithm_5_2_5 fp.round A).run) :
    ∃ Q ∈ orthogonalGroup (Fin (k + 1)) ℝ, ∃ E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ,
      Q * upperPart st.1 = A + E ∧
        ∀ q, ‖(toLp 2 (E.col q) : EuclideanSpace ℝ (Fin (k + 1)))‖ ≤
          ((1 + √2 * gamma fp.u 15) ^ k - 1) *
            ‖(toLp 2 (A.col q) : EuclideanSpace ℝ (Fin (k + 1)))‖ := by
  set ε := √2 * gamma fp.u 15 with hεdef
  have hu0 := fp.u_nonneg
  have hγ : 0 ≤ gamma fp.u 15 := gamma_nonneg hu0 hu
  have hε : 0 ≤ ε := by positivity
  have hγε : gamma fp.u 15 ≤ ε := by
    have : (1 : ℝ) ≤ √2 := by rw [Real.one_le_sqrt]; norm_num
    nlinarith
  have hu13 : ((13 : ℕ) : ℝ) * fp.u < 1 :=
    (mul_le_mul_of_nonneg_right (by norm_num) hu0).trans_lt hu
  have hAH : ∀ r q : Fin (k + 1), (q : ℕ) + 1 < r → A r q = 0 :=
    fun r q h => hA r q ((exists_between_iff r q).2 h)
  -- the invariant after `t` rotations
  have hinv := SetM.forall_mem_run_foldlM_finRange
    (fun (t : ℕ) (st : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × (Fin k → ℝ × ℝ)) =>
      (∀ r q : Fin (k + 1), (q : ℕ) + 1 < r → st.1 r q = 0) ∧
        ∃ Q ∈ orthogonalGroup (Fin (k + 1)) ℝ, ∃ E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ,
          Q * hessenbergJunkClean t st.1 = A + E ∧
            ∀ q, ‖(toLp 2 (E.col q) : EuclideanSpace ℝ (Fin (k + 1)))‖ ≤
              ((1 + ε) ^ t - 1) * ‖(toLp 2 (A.col q) : EuclideanSpace ℝ (Fin (k + 1)))‖)
    ⟨hAH, 1, one_mem _, 0, by
      ext r q
      simp [hessenbergJunkClean], fun q => by
        rw [show (0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).col q = 0 from rfl]; simp⟩ ?_ st h
  · obtain ⟨hH, Q, hQ, E, hQE, hE⟩ := hinv
    have hclean : hessenbergJunkClean k st.1 = upperPart st.1 := by
      ext r q
      simp only [hessenbergJunkClean, upperPart, of_apply]
      split_ifs with h1 h2 h2
      · omega
      · rfl
      · rfl
      · have hr := r.2
        by_cases hrq : (r : ℕ) = q + 1
        · exact absurd ⟨by omega, hrq⟩ h1
        · exact hH r q (by omega)
    exact ⟨Q, hQ, E, by rw [← hclean]; exact hQE, hE⟩
  · intro jj st hI st' hst'
    obtain ⟨hH, Q, hQ, E, hQE, hE⟩ := hI
    simp only [SetM.mem_run_bind, SetM.mem_run_pure] at hst'
    obtain ⟨cs, hcs, B', hB', rfl⟩ := hst'
    dsimp only
    set t : ℕ := (jj : ℕ) with ht
    set a : Fin (k + 1) := jj.castSucc with ha
    set b : Fin (k + 1) := jj.succ with hb
    have hav : (a : ℕ) = t := rfl
    have hbv : (b : ℕ) = t + 1 := rfl
    have hab : a ≠ b := fun h => by have := congrArg Fin.val h; omega
    obtain ⟨c, s, hcs1, hzero, hc, hs⟩ := algorithm_5_1_3_rounding hu13 _ _ hcs
    obtain ⟨hout, hrows, hrel⟩ := givensApplyLeft_rounds hab cs.1 cs.2
      (nodup_indexFrom (k + 1) jj) st.1 hB'
    have hG := givensRotation_mem_orthogonalGroup hab hcs1
    have hmem : ∀ q : Fin (k + 1), q ∈ indexFrom (k + 1) jj ↔ t ≤ (q : ℕ) := fun q => by
      rw [mem_indexFrom]
    set C := hessenbergJunkClean t st.1 with hC
    set C' := hessenbergJunkClean (t + 1) B' with hC'
    -- the entries of `Gᵀ C`
    have hGC := fun r q => givensRotation_transpose_mul_apply hab c s C r q
    refine ⟨fun r q hqr => ?_, ?_⟩
    · -- the exact zeros below the subdiagonal are never touched
      by_cases hq : t ≤ (q : ℕ)
      · rw [hrows r q (fun h => by rw [h] at hqr; omega) (fun h => by rw [h] at hqr; omega)]
        exact hH r q hqr
      · rw [hout r q (fun h => hq ((hmem q).1 h))]
        exact hH r q hqr
    have hF : ∀ q, ‖(toLp 2 ((C' - (givensRotation a b c s)ᵀ * C).col q) :
        EuclideanSpace ℝ (Fin (k + 1)))‖ ≤ ε * ‖(toLp 2 (C.col q) :
          EuclideanSpace ℝ (Fin (k + 1)))‖ := by
      intro q
      rcases lt_trichotomy (q : ℕ) t with hq | hq | hq
      · -- a column already reduced: rows `a, b` of `C` vanish there, nothing changes
        have hCa : C a q = 0 := by
          simp only [hC, hessenbergJunkClean, of_apply]
          split_ifs with h1
          · rfl
          · exact hH a q (by omega)
        have hCb : C b q = 0 := by
          simp only [hC, hessenbergJunkClean, of_apply]
          split_ifs with h1
          · rfl
          · exact hH b q (by omega)
        have hzero' : (C' - (givensRotation a b c s)ᵀ * C).col q = 0 := by
          ext r
          simp only [col_apply, Matrix.sub_apply, Pi.zero_apply, hGC, hCa, hCb]
          have hCC : C' r q = C r q := by
            simp only [hC, hC', hessenbergJunkClean, of_apply]
            rw [hout r q (fun h => by have := (hmem q).1 h; omega)]
            split_ifs with h1 h2 h2
            · rfl
            · exact absurd ⟨by omega, h1.2⟩ h2
            · exact absurd ⟨by omega, h2.2⟩ h1
            · rfl
          split_ifs with hra hrb
          · rw [hCC, hra, hCa]; ring
          · rw [hCC, hrb, hCb]; ring
          · rw [hCC, sub_self]
        rw [hzero']
        simp only [toLp_zero, norm_zero]
        positivity
      · -- the column being reduced: only the pivot row carries a rounding error
        have hqa : q = a := Fin.ext (by omega)
        subst hqa
        have hCcol : ∀ r, C r a = st.1 r a := fun r => by
          simp only [hC, hessenbergJunkClean, of_apply]
          rw [ite_eq_right (fun h => by omega)]
        have hdiff := abs_sub_le_of_roundsGivensApply
          (show ((13 + 2 : ℕ) : ℝ) * fp.u < 1 from hu) hc hs (hrel ⟨a, (hmem a).2 le_rfl⟩)
        simp only [submatrix_apply, id] at hdiff
        obtain ⟨hda, -, -⟩ := hdiff
        refine (norm_le_of_single_of_abs_le hab hcs1 hγ (x := C.col a) (p := a) (i := b)
          (fun r hra => ?_) ?_).trans (mul_le_mul_of_nonneg_right hγε (norm_nonneg _))
        · simp only [col_apply, Matrix.sub_apply, hGC, ite_eq_right hra]
          by_cases hrb : r = b
          · rw [ite_eq_left hrb, hrb, hCcol a, hCcol b]
            simp only [hC', hessenbergJunkClean, of_apply]
            rw [ite_eq_left ⟨by omega, by omega⟩]
            linarith [hzero]
          · rw [ite_eq_right hrb]
            simp only [hC', hessenbergJunkClean, of_apply]
            rw [ite_eq_right (fun h => hrb (Fin.ext (by omega))), hrows r a hra hrb, hCcol r,
              sub_self]
        · simp only [col_apply, Matrix.sub_apply, hGC, ↓reduceIte, hCcol]
          simp only [hC', hessenbergJunkClean, of_apply]
          rw [ite_eq_right (fun h => by omega)]
          exact hda
      · -- a column not yet reached: the backbone's bound for a computed rotation
        have hCcol : C.col q = st.1.col q := by
          ext r
          simp only [col_apply, hC, hessenbergJunkClean, of_apply]
          rw [ite_eq_right (fun h => by omega)]
        have hC'col : C'.col q = B'.col q := by
          ext r
          simp only [col_apply, hC', hessenbergJunkClean, of_apply]
          rw [ite_eq_right (fun h => by omega)]
        have hcol : (C' - (givensRotation a b c s)ᵀ * C).col q =
            B'.col q - (planeRotation a b c (-s))ᵀ *ᵥ st.1.col q := by
          rw [show (C' - (givensRotation a b c s)ᵀ * C).col q =
              C'.col q - ((givensRotation a b c s)ᵀ * C).col q from rfl,
            col_mul_eq_mulVec, hCcol, hC'col]
          rfl
        rw [hcol, hCcol]
        exact norm_sub_le_of_roundsGivensApply (show ((13 + 2 : ℕ) : ℝ) * fp.u < 1 from hu) hab
          hcs1 hc hs (hrel ⟨q, (hmem q).2 hq.le⟩)
    obtain ⟨E', hE'eq, hE'⟩ := exists_mul_eq_add_of_step hQ hG hQE hε hE hF
    refine ⟨Q * givensRotation a b c s, mul_mem hQ hG, E', ?_, ?_⟩
    · exact hE'eq
    · exact hE'

end GivensQRRounding

section GivensQRRounding'

/-- The array $B$ of a run of Algorithm 5.2.4 with its computed zeros set to zero: the entries below
the diagonal of the columns before $j$, and the entries of column $j$ in the rows of the list
$p$, which are already processed. -/
def givensQRJunkClean (j : ℕ) (p : List (Fin m)) (B : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  of fun r q => if ((q : ℕ) < j ∧ (q : ℕ) < r) ∨ ((q : ℕ) = j ∧ r ∈ p) then 0 else B r q

/-- **Algorithm 5.2.4** of [golub2013matrix], backward error. Let $A \in \mathbb{R}^{m \times n}$,
and let the unit roundoff $u$ satisfy $15u < 1$. Let $A'$ be a run of Algorithm 5.2.4 on $A$ in
the rounding model `fp`, and let $\hat R$ be the upper triangular part of $A'$. Then there are
an orthogonal $Q \in \mathbb{R}^{m \times m}$ and $E \in \mathbb{R}^{m \times n}$ with
$$Q \hat R = A + E, \qquad \|E(:, q)\|_2 \le \bigl((1 + \sqrt{2}\,\gamma_{15})^{mn} - 1\bigr)
  \|A(:, q)\|_2$$
for every column $q$.

**Generalization.** The source states Algorithm 5.2.4 for $m \ge n$. The statement holds for all
$m$ and $n$.

In §5.3.3 the source says that similar results hold if Givens QR is used; the bound applies the
rounding analysis of §5.1.12 to the rotations of Algorithm 5.2.4. The exponent $mn$ bounds the
number of rotations. $Q$ is the product of the exact rotations of which the computed pairs are
relative perturbations, and the computed subdiagonal entries are not part of $\hat R$. -/
theorem algorithm_5_2_4_rounding {fp : RoundingModel ℝ} (hu : ((15 : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin m) (Fin n) ℝ) {A' : Matrix (Fin m) (Fin n) ℝ}
    (h : A' ∈ (algorithm_5_2_4 fp.round A).run) :
    ∃ Q ∈ orthogonalGroup (Fin m) ℝ, ∃ E : Matrix (Fin m) (Fin n) ℝ,
      Q * upperPart A' = A + E ∧
        ∀ q, ‖(toLp 2 (E.col q) : EuclideanSpace ℝ (Fin m))‖ ≤
          ((1 + √2 * gamma fp.u 15) ^ (m * n) - 1) *
            ‖(toLp 2 (A.col q) : EuclideanSpace ℝ (Fin m))‖ := by
  set ε := √2 * gamma fp.u 15 with hεdef
  have hu0 := fp.u_nonneg
  have hγ : 0 ≤ gamma fp.u 15 := gamma_nonneg hu0 hu
  have hε : 0 ≤ ε := by positivity
  have hγε : gamma fp.u 15 ≤ ε := by
    have : (1 : ℝ) ≤ √2 := by rw [Real.one_le_sqrt]; norm_num
    nlinarith
  have hu13 : ((13 : ℕ) : ℝ) * fp.u < 1 :=
    (mul_le_mul_of_nonneg_right (by norm_num) hu0).trans_lt hu
  -- the invariant, with `t` rotations done
  set J : ℕ → List (Fin m) → Matrix (Fin m) (Fin n) ℝ → ℕ → Prop := fun j p B t =>
    ∃ Q ∈ orthogonalGroup (Fin m) ℝ, ∃ E : Matrix (Fin m) (Fin n) ℝ,
      Q * givensQRJunkClean j p B = A + E ∧
        ∀ q, ‖(toLp 2 (E.col q) : EuclideanSpace ℝ (Fin m))‖ ≤
          ((1 + ε) ^ t - 1) * ‖(toLp 2 (A.col q) : EuclideanSpace ℝ (Fin m))‖ with hJ
  -- one rotation
  have hrot : ∀ (jj : Fin n) (p : List (Fin m)) (i : Fin m) (B B' : Matrix (Fin m) (Fin n) ℝ)
      (t : ℕ) (cs : ℝ × ℝ), (jj : ℕ) < i → (∀ r ∈ p, i < r) → J jj p B t →
      cs ∈ (algorithm_5_1_3 fp.round (B (rowAbove i) jj) (B i jj)).run →
      B' ∈ (givensApplyLeft fp.round (rowAbove i) i cs.1 cs.2 (indexFrom n jj) B).run →
      J jj (p ++ [i]) B' (t + 1) := by
    intro jj p i B B' t cs hji hp hI hcs hB'
    obtain ⟨Q, hQ, E, hQE, hE⟩ := hI
    set a := rowAbove i with ha
    have hav : (a : ℕ) = i - 1 := rfl
    have hai : a ≠ i := fun h => by have := congrArg Fin.val h; omega
    obtain ⟨c, s, hcs1, hzero, hc, hs⟩ := algorithm_5_1_3_rounding hu13 _ _ hcs
    obtain ⟨hout, hrows, hrel⟩ := givensApplyLeft_rounds hai cs.1 cs.2
      (nodup_indexFrom n jj) B hB'
    have hG := givensRotation_mem_orthogonalGroup hai hcs1
    have hmem : ∀ q : Fin n, q ∈ indexFrom n jj ↔ (jj : ℕ) ≤ q := fun q => by
      rw [mem_indexFrom]
    have hpa : ∀ r ∈ p, r ≠ a ∧ r ≠ i := fun r hr => by
      have := Fin.lt_def.1 (hp r hr)
      exact ⟨fun h => by rw [h] at this; omega, fun h => by rw [h] at this; omega⟩
    set C := givensQRJunkClean jj p B with hC
    set C' := givensQRJunkClean jj (p ++ [i]) B' with hC'
    have hGC := fun r q => givensRotation_transpose_mul_apply hai c s C r q
    have hF : ∀ q, ‖(toLp 2 ((C' - (givensRotation a i c s)ᵀ * C).col q) :
        EuclideanSpace ℝ (Fin m))‖ ≤ ε * ‖(toLp 2 (C.col q) : EuclideanSpace ℝ (Fin m))‖ := by
      intro q
      rcases lt_trichotomy (q : ℕ) jj with hq | hq | hq
      · -- a column already reduced: rows `a, i` of `C` vanish there
        have hCa : C a q = 0 := by
          simp only [hC, givensQRJunkClean, of_apply]
          rw [ite_eq_left (Or.inl ⟨hq, by omega⟩)]
        have hCi : C i q = 0 := by
          simp only [hC, givensQRJunkClean, of_apply]
          rw [ite_eq_left (Or.inl ⟨hq, by omega⟩)]
        have hzero' : (C' - (givensRotation a i c s)ᵀ * C).col q = 0 := by
          ext r
          simp only [col_apply, Matrix.sub_apply, Pi.zero_apply, hGC, hCa, hCi]
          have hCC : C' r q = C r q := by
            simp only [hC, hC', givensQRJunkClean, of_apply]
            rw [hout r q (fun h => by have := (hmem q).1 h; omega)]
            have hne : (q : ℕ) ≠ jj := by omega
            simp only [hne, false_and, or_false]
          split_ifs with hra hri
          · rw [hCC, hra, hCa]; ring
          · rw [hCC, hri, hCi]; ring
          · rw [hCC, sub_self]
        rw [hzero']
        simp only [toLp_zero, norm_zero]
        positivity
      · -- the column being reduced
        have hqj : q = jj := Fin.ext hq
        subst hqj
        have hCcol : ∀ r, r ∉ p → C r q = B r q := fun r hr => by
          simp only [hC, givensQRJunkClean, of_apply]
          rw [ite_eq_right (fun h => by
            rcases h with h | h
            · omega
            · exact hr h.2)]
        have hai' : a ∉ p := fun h => (hpa a h).1 rfl
        have hii' : i ∉ p := fun h => (hpa i h).2 rfl
        have hdiff := abs_sub_le_of_roundsGivensApply
          (show ((13 + 2 : ℕ) : ℝ) * fp.u < 1 from hu) hc hs (hrel ⟨q, (hmem q).2 le_rfl⟩)
        simp only [submatrix_apply, id] at hdiff
        obtain ⟨hda, -, -⟩ := hdiff
        refine (norm_le_of_single_of_abs_le hai hcs1 hγ (x := C.col q) (p := a) (i := i)
          (fun r hra => ?_) ?_).trans (mul_le_mul_of_nonneg_right hγε (norm_nonneg _))
        · simp only [col_apply, Matrix.sub_apply, hGC, ite_eq_right hra]
          by_cases hri : r = i
          · rw [ite_eq_left hri, hri, hCcol a hai', hCcol i hii']
            simp only [hC', givensQRJunkClean, of_apply]
            rw [ite_eq_left (Or.inr ⟨trivial, List.mem_append_right _ (List.mem_singleton_self i)⟩)]
            linarith [hzero]
          · rw [ite_eq_right hri]
            by_cases hrp : r ∈ p
            · have hC0 : C r q = 0 := by
                simp only [hC, givensQRJunkClean, of_apply]
                rw [ite_eq_left (Or.inr ⟨trivial, hrp⟩)]
              simp only [hC', givensQRJunkClean, of_apply]
              rw [ite_eq_left (Or.inr ⟨trivial, List.mem_append_left _ hrp⟩), hC0, sub_self]
            · simp only [hC', givensQRJunkClean, of_apply]
              rw [ite_eq_right (fun h => by
                rcases h with h | h
                · omega
                · rcases List.mem_append.1 h.2 with h' | h'
                  · exact hrp h'
                  · exact hri (List.mem_singleton.1 h')),
                hrows r q hra hri, hCcol r hrp, sub_self]
        · simp only [col_apply, Matrix.sub_apply, hGC, ↓reduceIte,
            hCcol a hai', hCcol i hii']
          simp only [hC', givensQRJunkClean, of_apply]
          rw [ite_eq_right (fun h => by
            rcases h with h | h
            · omega
            · rcases List.mem_append.1 h.2 with h' | h'
              · exact hai' h'
              · exact hai (List.mem_singleton.1 h'))]
          exact hda
      · -- a column not yet reached
        have hCcol : C.col q = B.col q := by
          ext r
          simp only [col_apply, hC, givensQRJunkClean, of_apply]
          rw [ite_eq_right (fun h => by omega)]
        have hC'col : C'.col q = B'.col q := by
          ext r
          simp only [col_apply, hC', givensQRJunkClean, of_apply]
          rw [ite_eq_right (fun h => by omega)]
        have hcol : (C' - (givensRotation a i c s)ᵀ * C).col q =
            B'.col q - (planeRotation a i c (-s))ᵀ *ᵥ B.col q := by
          rw [show (C' - (givensRotation a i c s)ᵀ * C).col q =
              C'.col q - ((givensRotation a i c s)ᵀ * C).col q from rfl,
            col_mul_eq_mulVec, hCcol, hC'col]
          rfl
        rw [hcol, hCcol]
        exact norm_sub_le_of_roundsGivensApply (show ((13 + 2 : ℕ) : ℝ) * fp.u < 1 from hu) hai
          hcs1 hc hs (hrel ⟨q, (hmem q).2 hq.le⟩)
    obtain ⟨E', hE'eq, hE'⟩ := exists_mul_eq_add_of_step hQ hG hQE hε hE hF
    exact ⟨Q * givensRotation a i c s, mul_mem hQ hG, E', hE'eq, hE'⟩
  -- the loop over the rows of column `j`
  have hcolumn : ∀ (jj : Fin n) (B : Matrix (Fin m) (Fin n) ℝ) (t : ℕ), J jj [] B t →
      ∀ B' ∈ ((((List.finRange m).filter (fun i : Fin m => (jj : ℕ) < i)).reverse).foldlM
        (fun (B : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) => do
          let cs ← algorithm_5_1_3 fp.round (B (rowAbove i) jj) (B i jj)
          givensApplyLeft fp.round (rowAbove i) i cs.1 cs.2 (indexFrom n jj) B) B).run,
      J jj ((List.finRange m).filter (fun i : Fin m => (jj : ℕ) < i)).reverse B'
        (t + (((List.finRange m).filter (fun i : Fin m => (jj : ℕ) < i)).reverse).length) := by
    intro jj B t hI
    have hpw : ((List.finRange m).filter (fun i : Fin m => (jj : ℕ) < i)).reverse.Pairwise
        (fun a b => b < a) :=
      List.pairwise_reverse.2 (((List.sortedLT_finRange m).pairwise).filter _)
    refine SetM.forall_mem_run_foldlM (fun p B => J jj p B (t + p.length)) (by simpa using hI) ?_
    intro p x q hl c hc c' hc'
    simp only [SetM.mem_run_bind] at hc'
    obtain ⟨cs, hcs, hc'⟩ := hc'
    have hx : x ∈ ((List.finRange m).filter (fun i : Fin m => (jj : ℕ) < i)).reverse := by
      rw [hl]; simp
    have hpx : ∀ r ∈ p, x < r := by
      intro r hr
      rw [hl, List.pairwise_append] at hpw
      exact hpw.2.2 r hr x List.mem_cons_self
    have := hrot jj p x c c' (t + p.length) cs (mem_rowsBelow_reverse.1 hx) hpx hc hcs hc'
    simpa [Nat.add_assoc] using this
  -- the loop over the columns
  have houter := SetM.forall_mem_run_foldlM_finRange
    (fun (k : ℕ) (B : Matrix (Fin m) (Fin n) ℝ) => ∃ t ≤ m * k, J k [] B t)
    ⟨0, Nat.zero_le _, 1, one_mem _, 0, by
      ext r q
      simp [givensQRJunkClean], fun q => by
        rw [show (0 : Matrix (Fin m) (Fin n) ℝ).col q = 0 from rfl]; simp⟩ ?_ A' h
  · obtain ⟨t, ht, Q, hQ, E, hQE, hE⟩ := houter
    have hclean : givensQRJunkClean n [] A' = upperPart A' := by
      ext r q
      simp only [givensQRJunkClean, upperPart, of_apply, List.not_mem_nil, and_false, or_false]
      have hq := q.2
      split_ifs with h1 h2 h2
      · omega
      · rfl
      · rfl
      · exact absurd ⟨hq, by omega⟩ h1
    refine ⟨Q, hQ, E, by rw [← hclean]; exact hQE, fun q => (hE q).trans ?_⟩
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have h1 : (1 : ℝ) ≤ 1 + ε := by linarith
    linarith [pow_le_pow_right₀ h1 (show t ≤ m * n from ht)]
  · intro jj B hI B' hB'
    obtain ⟨t, ht, hJ0⟩ := hI
    have hJ1 := hcolumn jj B t hJ0 B' hB'
    set L := ((List.finRange m).filter (fun i : Fin m => (jj : ℕ) < i)).reverse with hL
    have hlen : L.length ≤ m := by
      rw [hL, List.length_reverse]
      exact (List.length_filter_le _ _).trans (by simp)
    refine ⟨t + L.length, by nlinarith, ?_⟩
    have hsame : givensQRJunkClean jj L B' = givensQRJunkClean (jj + 1) [] B' := by
      ext r q
      simp only [givensQRJunkClean, of_apply, List.not_mem_nil, and_false, or_false, hL,
        mem_rowsBelow_reverse]
      congr 1
      apply propext
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> omega
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
        · exact Or.inl ⟨h, h2⟩
        · exact Or.inr ⟨h, by omega⟩
    obtain ⟨Q, hQ, E, hQE, hE⟩ := hJ1
    exact ⟨Q, hQ, E, by rw [← hsame]; exact hQE, hE⟩

end GivensQRRounding'

end Givens

/-! ### §5.2.7–5.2.8 Gram–Schmidt -/

section GramSchmidt

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- Step $k$ of classical Gram–Schmidt on the state $(Q, R)$, in the 1-based indices of the source:
$R(1{:}k{-}1, k) = Q(:, 1{:}k{-}1)^T A(:, k)$, $z = A(:, k) - Q(:, 1{:}k{-}1) R(1{:}k{-}1, k)$,
$R(k, k) = \|z\|_2$ and $Q(:, k) = z / R(k, k)$. The dot products are Algorithm 1.1.1, and for
$k = 1$ no subtraction is performed. -/
noncomputable def cgsStep (A : Matrix (Fin m) (Fin n) ℝ)
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) := do
  let prev := (List.finRange n).filter (· < k)
  let R ← prev.foldlM (fun (R : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
    let r ← Chapter01.algorithm_1_1_1 rnd (fun p => st.1 p i) (fun p => A p k)
    pure (R.updateRow i (Function.update (R i) k r))) st.2
  let z ← if prev = [] then pure (fun p => A p k) else
    (List.finRange m).foldlM (fun (z : Fin m → ℝ) (p : Fin m) => do
      let s ← dotAccum rnd prev (st.1 p) (fun i => R i k) 0
      let d ← rnd (A p k - s)
      pure (Function.update z p d)) 0
  let rkk ← rnd √(← Chapter01.algorithm_1_1_1 rnd z z)
  let q ← (List.finRange m).foldlM (fun (q : Fin m → ℝ) (p : Fin m) => do
    let d ← rnd (z p / rkk)
    pure (Function.update q p d)) 0
  pure (st.1.updateCol k q, R.updateRow k (Function.update (R k) k rkk))

/-- **Section 5.2.7** of [golub2013matrix], classical Gram–Schmidt (CGS). For
$A \in \mathbb{R}^{m \times n}$ the algorithm computes $Q \in \mathbb{R}^{m \times n}$ and
$R \in \mathbb{R}^{n \times n}$:
```
R(1,1) = ‖A(:,1)‖₂;  Q(:,1) = A(:,1)/R(1,1)
for k = 2:n
    R(1:k-1, k) = Q(1:m, 1:k-1)ᵀ A(1:m, k)
    z = A(1:m, k) - Q(1:m, 1:k-1) R(1:k-1, k)
    R(k, k) = ‖z‖₂
    Q(1:m, k) = z/R(k, k)
end
```
The program runs `GolubVanLoan.Chapter05.cgsStep` for $k = 1, \dots, n$, starting from $Q = 0$
and $R = 0$, and returns $(Q, R)$.

The first step is the loop body with no previous columns: $z = A(:, 1)$, and no subtraction is
performed. The dot products are Algorithm 1.1.1 (`GolubVanLoan.Chapter01.algorithm_1_1_1`), and
the norm is the square root of a dot product. -/
noncomputable def classicalGramSchmidt (A : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (cgsStep rnd A) (0, 0)

/-- The inner loop body of Algorithm 5.2.6 for a column $j > k$: $R(k, j) = Q(:, k)^T A(:, j)$ by
Algorithm 1.1.1, then $A(:, j) = A(:, j) - Q(:, k) R(k, j)$. -/
noncomputable def mgsInner (q : Fin m → ℝ) (k : Fin n)
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) := do
  let rkj ← Chapter01.algorithm_1_1_1 rnd q (fun p => st.1 p j)
  let a ← (List.finRange m).foldlM (fun (a : Fin m → ℝ) (p : Fin m) => do
    let t ← rnd (q p * rkj)
    let d ← rnd (a p - t)
    pure (Function.update a p d)) (fun p => st.1 p j)
  pure (st.1.updateCol j a, st.2.updateRow k (Function.update (st.2 k) j rkj))

/-- Step $k$ of Algorithm 5.2.6 on the state consisting of the working array, $Q$ and $R$:
$R(k, k) = \|A(:, k)\|_2$ and $Q(:, k) = A(:, k)/R(k, k)$, then the inner loop
`GolubVanLoan.Chapter05.mgsInner` over $j = k{+}1{:}n$. -/
noncomputable def mgsStep
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) := do
  let rkk ← rnd √(← Chapter01.algorithm_1_1_1 rnd (fun p => st.1 p k) (fun p => st.1 p k))
  let q ← (List.finRange m).foldlM (fun (q : Fin m → ℝ) (p : Fin m) => do
    let d ← rnd (st.1 p k / rkk)
    pure (Function.update q p d)) 0
  let st' ← ((List.finRange n).filter (k < ·)).foldlM (mgsInner rnd q k)
    (st.1, st.2.2.updateRow k (Function.update (st.2.2 k) k rkk))
  pure (st'.1, st.2.1.updateCol k q, st'.2)

/-- **Algorithm 5.2.6** of [golub2013matrix] (modified Gram–Schmidt). Given
$A \in \mathbb{R}^{m \times n}$ with $\operatorname{rank}(A) = n$, the algorithm computes the
thin QR factorization $A = Q_1 R_1$, where $Q_1 \in \mathbb{R}^{m \times n}$ has orthonormal
columns and $R_1 \in \mathbb{R}^{n \times n}$ is upper triangular.
```
for k = 1:n
    R(k, k) = ‖A(1:m, k)‖₂
    Q(1:m, k) = A(1:m, k)/R(k, k)
    for j = k+1:n
        R(k, j) = Q(1:m, k)ᵀ A(1:m, j)
        A(1:m, j) = A(1:m, j) - Q(1:m, k) R(k, j)
    end
end
```
The program runs `GolubVanLoan.Chapter05.mgsStep` for $k = 1, \dots, n$. The working array $A$
is part of the state, and the result is $(Q_1, R_1)$.

The program has no hypothesis on $A$; the rank condition is a hypothesis of
`GolubVanLoan.Chapter05.algorithm_5_2_6_spec`. -/
noncomputable def algorithm_5_2_6 (A : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) := do
  let st ← (List.finRange n).foldlM (mgsStep rnd) (A, 0, 0)
  pure (st.2.1, st.2.2)

end Programs

/-- A loop that writes, for each row $i$ of a list $l$, a value $g(i)$ that does not depend on the
state into entry $(i, k)$ of a matrix sets the entries $(i, k)$, $i \in l$, to $g(i)$ and keeps
the other entries. -/
theorem foldl_updateRow_update_eq {α : Type*} (g : Fin n → α) (k : Fin n) (l : List (Fin n))
    (R : Matrix (Fin n) (Fin n) α) :
    l.foldl (fun (R : Matrix (Fin n) (Fin n) α) i => R.updateRow i (Function.update (R i) k (g i)))
      R = of fun i j => if j = k ∧ i ∈ l then g i else R i j := by
  refine (List.foldl_foldl_update_update_eq_ite (fun i _ => g i) l [k] R).trans ?_
  ext i j
  simp only [List.mem_singleton, and_comm, of_apply]

/-- The residual of classical Gram–Schmidt at column $k$,
$z = a_k - \sum_{i < k} (q_i^T a_k)\, q_i$, for the columns $q_i$ of $Q$ and $a_k$ of $A$. -/
noncomputable def cgsResidual (Q : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (k : Fin n) : Fin m → ℝ :=
  A.col k - ∑ i ∈ Finset.univ.filter (· < k), (Q.col i ⬝ᵥ A.col k) • Q.col i

/-- The exact step $k$ of classical Gram–Schmidt. With $z$ the residual
`GolubVanLoan.Chapter05.cgsResidual` of the current $Q$, column $k$ of $Q$ becomes $z / \|z\|_2$
(zero if $z = 0$), entry $(i, k)$ of $R$ becomes $q_i^T a_k$ for $i < k$ and $\|z\|_2$ for
$i = k$, and the other entries are unchanged. -/
theorem cgsStep_pure (A : Matrix (Fin m) (Fin n) ℝ)
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    Id.run (cgsStep pure A st k) =
      (st.1.updateCol k ((√(cgsResidual st.1 A k ⬝ᵥ cgsResidual st.1 A k))⁻¹ •
          cgsResidual st.1 A k),
        of fun i j => if j = k ∧ i < k then st.1.col i ⬝ᵥ A.col k
          else if j = k ∧ i = k then √(cgsResidual st.1 A k ⬝ᵥ cgsResidual st.1 A k)
          else st.2 i j) := by
  have hmem : ∀ i : Fin n, i ∈ (List.finRange n).filter (· < k) ↔ i < k := fun i => by simp
  have hR : List.foldl (fun (R : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
        R.updateRow i (Function.update (R i) k ((fun p => st.1 p i) ⬝ᵥ fun p => A p k))) st.2
        ((List.finRange n).filter (· < k)) =
      of fun i j => if j = k ∧ i < k then st.1.col i ⬝ᵥ A.col k else st.2 i j := by
    rw [foldl_updateRow_update_eq (fun i => (fun p => st.1 p i) ⬝ᵥ fun p => A p k)]
    ext i j
    simp only [of_apply, hmem]
    rfl
  have hsum : ∀ f : Fin n → ℝ, (((List.finRange n).filter (· < k)).map f).sum =
      ∑ i ∈ Finset.univ.filter (· < k), f i := by
    intro f
    rw [← List.sum_toFinset f ((List.nodup_finRange n).filter _)]
    congr 1
    ext i
    simp
  -- the common tail of both branches, once the residual is identified
  have key : ∀ z : Fin m → ℝ, z = cgsResidual st.1 A k →
      (st.1.updateCol k (List.foldl (fun (q : Fin m → ℝ) (p : Fin m) =>
          Function.update q p (z p / √(z ⬝ᵥ z))) 0 (List.finRange m)),
        (of fun i j => if j = k ∧ i < k then st.1.col i ⬝ᵥ A.col k else st.2 i j :
          Matrix (Fin n) (Fin n) ℝ).updateRow k (Function.update
          ((of fun i j => if j = k ∧ i < k then st.1.col i ⬝ᵥ A.col k else st.2 i j :
            Matrix (Fin n) (Fin n) ℝ) k) k √(z ⬝ᵥ z))) =
      (st.1.updateCol k ((√(cgsResidual st.1 A k ⬝ᵥ cgsResidual st.1 A k))⁻¹ •
          cgsResidual st.1 A k),
        of fun i j => if j = k ∧ i < k then st.1.col i ⬝ᵥ A.col k
          else if j = k ∧ i = k then √(cgsResidual st.1 A k ⬝ᵥ cgsResidual st.1 A k)
          else st.2 i j) := by
    rintro z rfl
    refine Prod.ext ?_ ?_
    · simp only
      congr 1
      rw [List.foldl_update_eq_ite]
      funext p
      simp only [List.mem_finRange, ↓reduceIte, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
    · simp only
      ext i j
      simp only [updateRow_apply, Function.update_apply, of_apply]
      by_cases hik : i = k
      · subst hik
        by_cases hjk : j = i <;> simp [hjk]
      · simp [hik]
  have hres : ∀ p, cgsResidual st.1 A k p =
      A p k - ∑ i ∈ Finset.univ.filter (· < k), st.1 p i * (st.1.col i ⬝ᵥ A.col k) := by
    intro p
    simp only [cgsResidual, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      col_apply, mul_comm]
  unfold cgsStep
  by_cases h0 : (List.finRange n).filter (· < k) = []
  · simp only [h0, ↓reduceIte, Id.run_bind, Id.run_pure, List.idRun_foldlM,
      Chapter01.algorithm_1_1_1_spec]
    rw [← h0, hR]
    refine key _ (funext fun p => ?_)
    rw [hres]
    have : Finset.univ.filter (fun i : Fin n => i < k) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hi
      have := (hmem i).2 hi
      rw [h0] at this
      exact List.not_mem_nil this
    rw [this, Finset.sum_empty, sub_zero]
  · simp only [h0, ↓reduceIte, Id.run_bind, Id.run_pure, List.idRun_foldlM,
      Chapter01.algorithm_1_1_1_spec, dotAccum_id, hR]
    refine key _ (funext fun p => ?_)
    rw [List.foldl_update_eq_ite]
    simp only [List.mem_finRange, ↓reduceIte, zero_add, hsum, of_apply, true_and]
    rw [hres]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ite_eq_left (Finset.mem_filter.1 hi).2]

/-- The state of classical Gram–Schmidt after $k$ steps: the first $k$ columns of the Gram–Schmidt
factors `Matrix.gramSchmidtQ` and `Matrix.gramSchmidtR`, and zero elsewhere. -/
private noncomputable def cgsState (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ :=
  (of fun p j => if (j : ℕ) < k then gramSchmidtQ A p j else 0,
    of fun i j => if (j : ℕ) < k then gramSchmidtR A i j else 0)

/-- One exact step of classical Gram–Schmidt computes the next column of the Gram–Schmidt factors,
because the residual against the first $k$ columns is `Matrix.gramSchmidtResidual`. -/
private theorem cgsStep_cgsState (A : Matrix (Fin m) (Fin n) ℝ) (k : Fin n) :
    Id.run (cgsStep pure A (cgsState A k) k) = cgsState A (k + 1) := by
  rw [cgsStep_pure]
  set Q := (cgsState A k).1 with hQ
  have hQc : ∀ i : Fin n, i < k → Q.col i = (gramSchmidtQ A).col i := fun i hi => by
    ext p
    simp only [hQ, cgsState, col_apply, of_apply, ite_eq_left_iff]
    exact fun h => absurd hi h
  have hres : cgsResidual Q A k = gramSchmidtResidual A k := by
    rw [cgsResidual, gramSchmidtResidual, Finset.filter_gt_eq_Iio]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hQc i (Finset.mem_Iio.1 hi), gramSchmidtR_apply_eq_dotProduct]
  rw [hres, ← col_gramSchmidtQ_eq_inv_sqrt_smul, ← gramSchmidtR_apply_self_eq_sqrt]
  refine Prod.ext ?_ ?_
  · ext p j
    simp only [cgsState, updateCol_apply, of_apply]
    by_cases hjk : j = k
    · subst hjk
      simp
    · have : (j : ℕ) < k + 1 ↔ (j : ℕ) < k := by
        have : (j : ℕ) ≠ k := fun e => hjk (Fin.ext e)
        omega
      simp [hjk, this, hQ, cgsState]
  · ext i j
    simp only [cgsState, of_apply]
    by_cases hjk : j = k
    · subst hjk
      rcases lt_trichotomy i j with hij | hij | hij
      · simp only [true_and, hij, ↓reduceIte, lt_add_one]
        rw [hQc i hij, gramSchmidtR_apply_eq_dotProduct]
      · subst hij
        simp
      · simp [hij.ne', not_lt.2 hij.le, gramSchmidtR_apply_of_lt A hij]
    · have : (j : ℕ) < k + 1 ↔ (j : ℕ) < k := by
        have : (j : ℕ) ≠ k := fun e => hjk (Fin.ext e)
        omega
      simp [hjk, this]

/-- **Section 5.2.7** of [golub2013matrix], classical Gram–Schmidt in exact arithmetic. For every
$A \in \mathbb{R}^{m \times n}$, the output of classical Gram–Schmidt in exact arithmetic is the
pair of Gram–Schmidt factors $(Q, R)$ of $A$: column $k$ of $Q$ is the normalized Gram–Schmidt
vector of the columns of $A$, and $r_{ik} = q_i^T a_k$.

There is no rank hypothesis. A column whose residual vanishes gives a zero column of $Q$ and a
zero diagonal entry of $R$. The factors are `Matrix.gramSchmidtQ A` and `Matrix.gramSchmidtR A`. -/
theorem classicalGramSchmidt_eq_gramSchmidt (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (classicalGramSchmidt pure A) = (gramSchmidtQ A, gramSchmidtR A) := by
  have hall : ∀ j ≤ n, ((List.finRange n).take j).foldl
      (fun st k => Id.run (cgsStep pure A st k)) (0, 0) = cgsState A j := by
    intro j
    induction j with
    | zero =>
      intro _
      refine Prod.ext ?_ ?_ <;> ext <;> simp [cgsState]
    | succ j ih =>
      intro hj
      rw [List.take_succ_eq_append_getElem (by simpa using hj), List.foldl_append,
        List.foldl_cons, List.foldl_nil, ih (by omega)]
      simpa using cgsStep_cgsState A ⟨j, by omega⟩
  have h := hall n le_rfl
  rw [List.take_of_length_le (by simp)] at h
  rw [classicalGramSchmidt, List.idRun_foldlM, h]
  refine Prod.ext ?_ ?_ <;> ext <;> simp [cgsState]

/-- **Section 5.2.7** of [golub2013matrix], classical Gram–Schmidt computes the thin QR
factorization. Let $A \in \mathbb{R}^{m \times n}$ have full column rank, and let $(Q, R)$ be
the output of classical Gram–Schmidt in exact arithmetic. Then $A = QR$, $Q^T Q = I$, and $R$ is
upper triangular with positive diagonal entries.

The factorization is `Matrix.IsThinQR`. The proof combines
`GolubVanLoan.Chapter05.classicalGramSchmidt_eq_gramSchmidt` and `Matrix.isThinQR_gramSchmidtQ`. -/
theorem classicalGramSchmidt_spec (A : Matrix (Fin m) (Fin n) ℝ) (hA : LinearIndependent ℝ Aᵀ) :
    IsThinQR A (Id.run (classicalGramSchmidt pure A)).1 (Id.run (classicalGramSchmidt pure A)).2 ∧
      ∀ j, 0 < (Id.run (classicalGramSchmidt pure A)).2 j j := by
  rw [classicalGramSchmidt_eq_gramSchmidt]
  exact ⟨isThinQR_gramSchmidtQ hA, gramSchmidtR_apply_self_pos hA⟩

/-- A loop that subtracts $q_p c$ from each entry $p$ of a duplicate-free list, once each, changes
the vector $a$ to $a_p - q_p c$ on the listed entries and keeps the other entries. -/
theorem foldl_update_sub_mul (a₀ q : Fin m → ℝ) (c : ℝ) {l : List (Fin m)} (hl : l.Nodup) :
    l.foldl (fun (y : Fin m → ℝ) p => Function.update y p (y p - q p * c)) a₀ =
      fun p => if p ∈ l then a₀ p - q p * c else a₀ p :=
  List.foldl_update_of_nodup hl (fun p y => y p - q p * c) (fun _ _ _ _ _ h => by rw [h]) a₀

/-- The exact inner step of modified Gram–Schmidt at column $j$: column $j$ of the working array $W$
becomes $w_j - (q^T w_j)\, q$, and entry $(k, j)$ of $R$ becomes $q^T w_j$. -/
theorem mgsInner_pure (q : Fin m → ℝ) (k : Fin n)
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    Id.run (mgsInner pure q k st j) =
      (st.1.updateCol j (st.1.col j - (q ⬝ᵥ st.1.col j) • q),
        st.2.updateRow k (Function.update (st.2 k) j (q ⬝ᵥ st.1.col j))) := by
  simp only [mgsInner, Id.run_bind, Id.run_pure, List.idRun_foldlM,
    Chapter01.algorithm_1_1_1_spec]
  rw [foldl_update_sub_mul _ _ _ (List.nodup_finRange m)]
  congr 2
  funext p
  simp only [List.mem_finRange, ↓reduceIte, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, col_apply,
    mul_comm]
  rfl

/-- The exact inner loop of modified Gram–Schmidt over a duplicate-free list $l$ of columns: for
$j \in l$, column $j$ of $W$ becomes $w_j - (q^T w_j)\, q$ and entry $(k, j)$ of $R$ becomes
$q^T w_j$, where $w_j$ is column $j$ before the loop; the other entries are unchanged. -/
theorem foldl_mgsInner_pure (q : Fin m → ℝ) (k : Fin n) (l : List (Fin n)) (hl : l.Nodup)
    (W : Matrix (Fin m) (Fin n) ℝ) (R : Matrix (Fin n) (Fin n) ℝ) :
    l.foldl (fun st j => Id.run (mgsInner pure q k st j)) (W, R) =
      (of fun p j => if j ∈ l then W p j - (q ⬝ᵥ W.col j) * q p else W p j,
        of fun i j => if i = k ∧ j ∈ l then q ⬝ᵥ W.col j else R i j) := by
  induction l generalizing W R with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, ite_false, and_false]; rfl
  | cons a l ih =>
    rcases List.nodup_cons.1 hl with ⟨ha, hl'⟩
    rw [List.foldl_cons, mgsInner_pure, ih hl']
    have hcol : ∀ j, j ∈ l → (W.updateCol a (W.col a - (q ⬝ᵥ W.col a) • q)).col j = W.col j :=
      fun j hj => by
        have hja : j ≠ a := fun e => ha (e ▸ hj)
        ext p; simp [hja]
    refine Prod.ext ?_ ?_
    · ext p j
      simp only [of_apply, List.mem_cons]
      by_cases hj : j ∈ l
      · have hja : j ≠ a := fun e => ha (e ▸ hj)
        simp only [hj, ↓reduceIte, or_true, hcol j hj, updateCol_apply, hja]
      · by_cases hja : j = a
        · subst hja; simp [hj]
        · simp [hj, hja]
    · ext i j
      simp only [of_apply, List.mem_cons]
      by_cases hj : j ∈ l
      · have hja : j ≠ a := fun e => ha (e ▸ hj)
        by_cases hik : i = k
        · simp [hik, hj, hcol j hj]
        · simp [hik, hj, updateRow_apply]
      · by_cases hja : j = a
        · subst hja; by_cases hik : i = k <;> simp [hik, hj, updateRow_apply]
        · by_cases hik : i = k <;> simp [hik, hj, hja, updateRow_apply]

/-- The exact step $k$ of modified Gram–Schmidt on the state $(W, Q, R)$. With $r_{kk} = \|w_k\|_2$
and $q = w_k / r_{kk}$, the columns $j > k$ of $W$ become $w_j - (q^T w_j)\, q$, column $k$ of
$Q$ becomes $q$, entry $(k, j)$ of $R$ becomes $q^T w_j$ for $j > k$ and $r_{kk}$ for $j = k$,
and the other entries are unchanged. -/
theorem mgsStep_pure
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n) :
    Id.run (mgsStep pure st k) =
      (of fun p j => if k < j then st.1 p j -
          (((√(st.1.col k ⬝ᵥ st.1.col k))⁻¹ • st.1.col k) ⬝ᵥ st.1.col j) *
            ((√(st.1.col k ⬝ᵥ st.1.col k))⁻¹ • st.1.col k) p
          else st.1 p j,
        st.2.1.updateCol k ((√(st.1.col k ⬝ᵥ st.1.col k))⁻¹ • st.1.col k),
        of fun i j => if i = k ∧ k < j then
            ((√(st.1.col k ⬝ᵥ st.1.col k))⁻¹ • st.1.col k) ⬝ᵥ st.1.col j
          else (st.2.2.updateRow k (Function.update (st.2.2 k) k
            √(st.1.col k ⬝ᵥ st.1.col k))) i j) := by
  have hq : List.foldl (fun (q : Fin m → ℝ) (p : Fin m) =>
      Function.update q p (st.1 p k / √((fun p => st.1 p k) ⬝ᵥ fun p => st.1 p k))) 0
        (List.finRange m) = (√(st.1.col k ⬝ᵥ st.1.col k))⁻¹ • st.1.col k := by
    rw [List.foldl_update_eq_ite]
    funext p
    simp only [List.mem_finRange, ↓reduceIte, Pi.smul_apply, smul_eq_mul, col_apply,
      div_eq_inv_mul]
    rfl
  simp only [mgsStep, Id.run_bind, Id.run_pure, List.idRun_foldlM,
    Chapter01.algorithm_1_1_1_spec, hq]
  rw [foldl_mgsInner_pure _ _ _ ((List.nodup_finRange n).filter _)]
  simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq, true_and]
  rfl

/-- The state of modified Gram–Schmidt after $k$ steps: working column $j$ is
$a_j - \sum r_{ij} q_i$ over the $i < k$ with $i < j$, and $Q$ and $R$ hold the first $k$
columns and rows of the Gram–Schmidt factors, and zero elsewhere. -/
private noncomputable def mgsState (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ :=
  (of fun p j => (A.col j - ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k ∧ i < j),
      gramSchmidtR A i j • (gramSchmidtQ A).col i) p,
    of fun p j => if (j : ℕ) < k then gramSchmidtQ A p j else 0,
    of fun i j => if (i : ℕ) < k then gramSchmidtR A i j else 0)

/-- One exact step of modified Gram–Schmidt computes the next row of the Gram–Schmidt factors; the
coefficient $q_k^T w_j$ equals $r_{kj} = q_k^T a_j$ because $w_j - a_j$ lies in the span of
$q_0, \dots, q_{k-1}$ (`Matrix.col_gramSchmidtQ_dotProduct_col`). -/
private theorem mgsStep_mgsState (A : Matrix (Fin m) (Fin n) ℝ) (k : Fin n) :
    Id.run (mgsStep pure (mgsState A k) k) = mgsState A (k + 1) := by
  rw [mgsStep_pure]
  set W := (mgsState A k).1 with hW
  have hWc : ∀ j, W.col j = A.col j - ∑ i ∈ Finset.univ.filter
      (fun i : Fin n => (i : ℕ) < k ∧ i < j), gramSchmidtR A i j • (gramSchmidtQ A).col i :=
    fun _ => rfl
  have hWk : W.col k = gramSchmidtResidual A k := by
    rw [hWc, gramSchmidtResidual]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i
    simp
  rw [hWk, ← col_gramSchmidtQ_eq_inv_sqrt_smul, ← gramSchmidtR_apply_self_eq_sqrt]
  set q := (gramSchmidtQ A).col k with hq
  have hdot : ∀ j, q ⬝ᵥ W.col j = gramSchmidtR A k j := fun j => by
    rw [hWc, dotProduct_sub, dotProduct_sum, Finset.sum_eq_zero fun i hi => ?_, sub_zero,
      gramSchmidtR_apply_eq_dotProduct]
    have hik : k ≠ i := fun e => by
      have := (Finset.mem_filter.1 hi).2.1
      rw [← e] at this
      exact lt_irrefl _ this
    rw [dotProduct_smul, hq, col_gramSchmidtQ_dotProduct_col A hik, smul_zero]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext p j
    simp only [of_apply, hdot]
    change _ = (A.col j - ∑ i ∈ Finset.univ.filter
      (fun i : Fin n => (i : ℕ) < (k : ℕ) + 1 ∧ i < j),
        gramSchmidtR A i j • (gramSchmidtQ A).col i) p
    rw [show W p j = _ from congrFun (hWc j) p]
    by_cases hkj : k < j
    · have hF : Finset.univ.filter (fun i : Fin n => (i : ℕ) < (k : ℕ) + 1 ∧ i < j) =
          insert k (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k ∧ i < j)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def,
          Fin.ext_iff]
        omega
      simp only [hkj, ↓reduceIte]
      rw [hF, Finset.sum_insert (by simp)]
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, hq,
        col_apply]
      ring
    · have hF : Finset.univ.filter (fun i : Fin n => (i : ℕ) < (k : ℕ) + 1 ∧ i < j) =
          Finset.univ.filter (fun i : Fin n => (i : ℕ) < k ∧ i < j) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hkj ⊢
        omega
      simp only [hkj, ↓reduceIte]
      rw [hF]
  · ext p j
    simp only [mgsState, updateCol_apply, of_apply]
    by_cases hjk : j = k
    · subst hjk
      simp [hq]
    · have : (j : ℕ) < k + 1 ↔ (j : ℕ) < k := by
        have : (j : ℕ) ≠ k := fun e => hjk (Fin.ext e)
        omega
      simp [hjk, this]
  · ext i j
    simp only [mgsState, of_apply, hdot]
    by_cases hik : i = k
    · subst hik
      rcases lt_trichotomy i j with hij | hij | hij
      · simp [hij]
      · subst hij
        simp
      · simp [not_lt.2 hij.le, hij.ne, gramSchmidtR_apply_of_lt A hij]
    · have : (i : ℕ) < k + 1 ↔ (i : ℕ) < k := by
        have : (i : ℕ) ≠ k := fun e => hik (Fin.ext e)
        omega
      simp [hik, this]

/-- **Algorithm 5.2.6** of [golub2013matrix], modified Gram–Schmidt in exact arithmetic. For every
$A \in \mathbb{R}^{m \times n}$, the output of Algorithm 5.2.6 in exact arithmetic is the pair
of Gram–Schmidt factors $(Q, R)$ of $A$.

There is no rank hypothesis. The factors are `Matrix.gramSchmidtQ A` and
`Matrix.gramSchmidtR A`. -/
theorem algorithm_5_2_6_eq_gramSchmidt (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (algorithm_5_2_6 pure A) = (gramSchmidtQ A, gramSchmidtR A) := by
  have hall : ∀ j ≤ n, ((List.finRange n).take j).foldl
      (fun st k => Id.run (mgsStep pure st k)) (A, 0, 0) = mgsState A j := by
    intro j
    induction j with
    | zero =>
      intro _
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ext <;> simp [mgsState]
    | succ j ih =>
      intro hj
      rw [List.take_succ_eq_append_getElem (by simpa using hj), List.foldl_append,
        List.foldl_cons, List.foldl_nil, ih (by omega)]
      simpa using mgsStep_mgsState A ⟨j, by omega⟩
  have h := hall n le_rfl
  rw [List.take_of_length_le (by simp)] at h
  simp only [algorithm_5_2_6, Id.run_bind, Id.run_pure, List.idRun_foldlM, h]
  refine Prod.ext ?_ ?_ <;> ext <;> simp [mgsState]

/-- **Algorithm 5.2.6** of [golub2013matrix], exact correctness. Let $A \in \mathbb{R}^{m \times n}$
have rank $n$, and let $(Q_1, R_1)$ be the output of Algorithm 5.2.6 in exact arithmetic. Then
$A = Q_1 R_1$, $Q_1$ has orthonormal columns, and $R_1$ is upper triangular with positive
diagonal entries.

The source asks for an upper triangular $R_1$; the statement adds that its diagonal is positive.
The factorization is `Matrix.IsThinQR`, and rank $n$ is `LinearIndependent ℝ Aᵀ`. The proof
combines `GolubVanLoan.Chapter05.algorithm_5_2_6_eq_gramSchmidt` and
`Matrix.isThinQR_gramSchmidtQ`. -/
theorem algorithm_5_2_6_spec (A : Matrix (Fin m) (Fin n) ℝ) (hA : LinearIndependent ℝ Aᵀ) :
    IsThinQR A (Id.run (algorithm_5_2_6 pure A)).1 (Id.run (algorithm_5_2_6 pure A)).2 ∧
      ∀ j, 0 < (Id.run (algorithm_5_2_6 pure A)).2 j j := by
  rw [algorithm_5_2_6_eq_gramSchmidt]
  exact ⟨isThinQR_gramSchmidtQ hA, gramSchmidtR_apply_self_pos hA⟩

/-- **Section 5.2.8** of [golub2013matrix], modified Gram–Schmidt as a rearrangement of classical
Gram–Schmidt. For every $A \in \mathbb{R}^{m \times n}$, Algorithm 5.2.6 and classical
Gram–Schmidt compute the same pair $(Q, R)$ in exact arithmetic.

The source calls MGS a rearrangement of the calculation in CGS. The common value is the pair of
Gram–Schmidt factors (`GolubVanLoan.Chapter05.algorithm_5_2_6_eq_gramSchmidt`,
`GolubVanLoan.Chapter05.classicalGramSchmidt_eq_gramSchmidt`), and no rank hypothesis is needed. -/
theorem algorithm_5_2_6_eq_classicalGramSchmidt (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (algorithm_5_2_6 pure A) = Id.run (classicalGramSchmidt pure A) := by
  rw [algorithm_5_2_6_eq_gramSchmidt, classicalGramSchmidt_eq_gramSchmidt]

/-- The columns of the orthonormal factor $Q$ of a thin QR factorization are orthonormal:
$q_i^T q_j$ is $1$ for $i = j$ and $0$ otherwise. -/
theorem isThinQR_col_dotProduct_col {A Q : Matrix (Fin m) (Fin n) ℝ} {R : Matrix (Fin n) (Fin n) ℝ}
    (h : IsThinQR A Q R) (i j : Fin n) : Q.col i ⬝ᵥ Q.col j = if i = j then 1 else 0 := by
  have := congrFun (congrFun h.conjTranspose_mul_self i) j
  simp only [Matrix.mul_apply, conjTranspose_apply, star_trivial, Matrix.one_apply] at this
  rw [← this]
  rfl

/-- **Section 5.2.8** of [golub2013matrix], the derivation of modified Gram–Schmidt. Let
$A = Q_1 R_1$ be a thin QR factorization of $A \in \mathbb{R}^{m \times n}$, with columns $q_i$
of $Q_1$ and rows $r_i^T$ of $R_1$, let $k$ be a column index, and let
$$A^{(k)} = \sum_{i \ge k} q_i r_i^T.$$
Then:

* $A - \sum_{i < k} q_i r_i^T = A^{(k)}$;
* the columns of $A^{(k)}$ before $k$ are zero;
* if $r_{kk} > 0$ and $z$ is column $k$ of $A^{(k)}$, then $r_{kk} = \|z\|_2$,
  $q_k = z / r_{kk}$, and $r_{kj} = q_k^T A^{(k)}(:, j)$ for every $j > k$.

The source writes the remainder as $[0 \mid A^{(k)}]$ with $A^{(k)} = [z \mid B]$, and the last
part as $[r_{k,k+1} \cdots r_{kn}] = q_k^T B$. Here $A^{(k)}$ denotes the full $m \times n$
matrix with zero leading columns. Indices are 0-based. -/
theorem mgs_remainder_eq {A Q : Matrix (Fin m) (Fin n) ℝ} {R : Matrix (Fin n) (Fin n) ℝ}
    (h : IsThinQR A Q R) (k : Fin n) :
    A - ∑ i ∈ Finset.univ.filter (· < k), vecMulVec (Q.col i) (R i) =
        ∑ i ∈ Finset.univ.filter (k ≤ ·), vecMulVec (Q.col i) (R i) ∧
      (∀ j, j < k → (∑ i ∈ Finset.univ.filter (k ≤ ·), vecMulVec (Q.col i) (R i)).col j = 0) ∧
      (0 < R k k →
        R k k = ‖(toLp 2 ((∑ i ∈ Finset.univ.filter (k ≤ ·), vecMulVec (Q.col i) (R i)).col k) :
          EuclideanSpace ℝ (Fin m))‖ ∧
        Q.col k = (R k k)⁻¹ • (∑ i ∈ Finset.univ.filter (k ≤ ·), vecMulVec (Q.col i) (R i)).col k ∧
        ∀ j, k < j → R k j =
          Q.col k ⬝ᵥ (∑ i ∈ Finset.univ.filter (k ≤ ·), vecMulVec (Q.col i) (R i)).col j) := by
  set Ak := ∑ i ∈ Finset.univ.filter (k ≤ ·), vecMulVec (Q.col i) (R i) with hAk
  have hA : A = ∑ i, vecMulVec (Q.col i) (R i) := by
    rw [← h.mul_eq, Chapter01.equation_1_1_4]
    rfl
  have hsplit : A - ∑ i ∈ Finset.univ.filter (· < k), vecMulVec (Q.col i) (R i) = Ak := by
    rw [hA, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· < k), add_sub_cancel_left, hAk]
    congr 1
    ext i
    simp
  -- the columns of `A^{(k)}`
  have hcol : ∀ j, Ak.col j = ∑ i ∈ Finset.univ.filter (k ≤ ·), R i j • Q.col i := by
    intro j
    ext p
    simp only [hAk, col_apply, Matrix.sum_apply, vecMulVec_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, mul_comm]
  have hup : ∀ i j : Fin n, j < i → R i j = 0 := fun i j hij => h.isUpperTriangular hij
  have hon := isThinQR_col_dotProduct_col h
  have hkk : Q.col k ⬝ᵥ Q.col k = 1 := by simpa using hon k k
  have hcolk : Ak.col k = R k k • Q.col k := by
    rw [hcol, Finset.sum_eq_single k (fun i hi hik => by
      rw [hup i k (lt_of_le_of_ne (Finset.mem_filter.1 hi).2 (Ne.symm hik)), zero_smul])
      (by simp)]
  refine ⟨hsplit, fun j hj => ?_, fun hk => ⟨?_, ?_, fun j hj => ?_⟩⟩
  · rw [hcol]
    exact Finset.sum_eq_zero fun i hi => by
      rw [hup i j (lt_of_lt_of_le hj (Finset.mem_filter.1 hi).2), zero_smul]
  · rw [hcolk, toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    have : ‖(toLp 2 (Q.col k) : EuclideanSpace ℝ (Fin m))‖ = 1 := by
      have h1 := hkk
      rw [dotProduct_self_eq_norm_sq] at h1
      nlinarith [norm_nonneg (toLp 2 (Q.col k) : EuclideanSpace ℝ (Fin m))]
    rw [this, mul_one]
  · rw [hcolk, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  · rw [hcol, dotProduct_sum]
    rw [Finset.sum_eq_single k (fun i hi hik => by
      rw [dotProduct_smul, hon k i, ite_eq_right_iff.2 (fun e => absurd e.symm hik),
        smul_zero]) (by simp)]
    rw [dotProduct_smul, hkk, smul_eq_mul, mul_one]

end GramSchmidt

/-! ### §5.2.4 Recursive block Householder QR -/

section BlockQR

/-- The column split of Algorithm 5.2.3: the equivalence between the disjoint union of
$\{0, \dots, \lfloor n/2 \rfloor - 1\}$ and $\{0, \dots, n - \lfloor n/2 \rfloor - 1\}$ and
$\{0, \dots, n - 1\}$ that sends the left part to the first $n_1 = \lfloor n/2 \rfloor$ columns
and the right part to the remaining $n - n_1$ columns. -/
def blockSplit (n : ℕ) : Fin (n / 2) ⊕ Fin (n - n / 2) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- The left part of the column split is the first $\lfloor n/2 \rfloor$ indices: $a \mapsto a$. -/
@[simp]
theorem blockSplit_inl_val {n : ℕ} (a : Fin (n / 2)) :
    ((blockSplit n (Sum.inl a) : Fin n) : ℕ) = a := by
  simp [blockSplit]

/-- The right part of the column split starts at $\lfloor n/2 \rfloor$:
$b \mapsto \lfloor n/2 \rfloor + b$. -/
@[simp]
theorem blockSplit_inr_val {n : ℕ} (b : Fin (n - n / 2)) :
    ((blockSplit n (Sum.inr b) : Fin n) : ℕ) = n / 2 + b := by
  simp [blockSplit]

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The base case of Algorithm 5.2.3: the thin factorization $A = Q_1 R_1$ from Algorithm 5.2.1.
$Q_1$ is the first $n$ columns of the product of the stored reflectors with the returned
$\beta$, accumulated by `GolubVanLoan.Chapter05.backwardAccumulation`, and $R_1$ is the first
$n$ rows of the upper triangular part of the overwritten array; entries past row or column $m$
are $0$, so the program is defined for all $m$ and $n$. -/
noncomputable def thinHouseholderQR {n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) := do
  let st ← algorithm_5_2_1 rnd A
  let Q ← backwardAccumulation rnd (storedReflectors st.1 st.2)
  pure (of fun i j => if hj : (j : ℕ) < m then Q i ⟨j, hj⟩ else 0,
    of fun i j => if hi : (i : ℕ) < m then upperPart st.1 ⟨i, hi⟩ j else 0)

/-- **Algorithm 5.2.3** of [golub2013matrix] (recursive block Householder QR). Suppose
$A \in \mathbb{R}^{m \times n}$ has full column rank and $n_b$ is a positive integer. The
algorithm computes $Q_1 \in \mathbb{R}^{m \times n}$ with orthonormal columns and an upper
triangular $R_1 \in \mathbb{R}^{n \times n}$ such that $A = Q_1 R_1$.
```
function [Q₁, R₁] = BlockQR(A, n, n_b)
if n ≤ n_b
    Use Algorithm 5.2.1 to compute the thin QR factorization A = Q₁R₁.
else
    n₁ = floor(n/2)
    [Q₁, R₁₁] = BlockQR(A(:, 1:n₁), n₁, n_b)
    R₁₂ = Q₁ᵀ A(:, n₁+1:n)
    A(:, n₁+1:n) = A(:, n₁+1:n) - Q₁R₁₂
    [Q₂, R₂₂] = BlockQR(A(:, n₁+1:n), n - n₁, n_b)
    Q₁ = [Q₁ | Q₂],  R₁ = [R₁₁ R₁₂; 0 R₂₂]
end
```
The recursion is well founded on $n$. The column blocks are split and reassembled along
`GolubVanLoan.Chapter05.blockSplit`, and the base case is
`GolubVanLoan.Chapter05.thinHouseholderQR`.

The two matrix products are Algorithm 1.1.5 (`GolubVanLoan.Chapter01.algorithm_1_1_5`), computed
as $R_{12} = 0 + Q_1^T A_2$ and $A_2 + (-Q_1) R_{12}$. The base case is also taken when
$n \le 1$. For $n_b \ge 1$ this is the test of the source; for $n_b = 0$ it makes the recursion
stop at $n = 1$, where the recursion of the source would not terminate. -/
noncomputable def algorithm_5_2_3 (nb : ℕ) {n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  if _h : n ≤ nb ∨ n ≤ 1 then thinHouseholderQR rnd A
  else do
    let QR₁ ← algorithm_5_2_3 nb (A.submatrix id (blockSplit n ∘ Sum.inl))
    let R₁₂ ← Chapter01.algorithm_1_1_5 rnd QR₁.1ᵀ (A.submatrix id (blockSplit n ∘ Sum.inr)) 0
    let A₂ ← Chapter01.algorithm_1_1_5 rnd (-QR₁.1) R₁₂ (A.submatrix id (blockSplit n ∘ Sum.inr))
    let QR₂ ← algorithm_5_2_3 nb A₂
    pure ((fromCols QR₁.1 QR₂.1).submatrix id (blockSplit n).symm,
      (fromBlocks QR₁.2 R₁₂ 0 QR₂.2).submatrix (blockSplit n).symm (blockSplit n).symm)
termination_by n
decreasing_by all_goals omega

end Programs

/-- If $A \in \mathbb{R}^{m \times k}$ has full column rank and $Ax = 0$, then $x = 0$. -/
theorem eq_zero_of_mulVec_eq_zero_of_linearIndependent {k : ℕ} {A : Matrix (Fin m) (Fin k) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) {x : Fin k → ℝ} (hx : A *ᵥ x = 0) : x = 0 := by
  have hA' := Fintype.linearIndependent_iff.mp hA
  funext i
  refine hA' x ?_ i
  ext p
  have := congrFun hx p
  simp only [mulVec, dotProduct, Pi.zero_apply] at this
  simp only [Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul, Pi.zero_apply]
  rw [← this]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- If $Ax = 0$ implies $x = 0$ for $A \in \mathbb{R}^{m \times k}$, then $A$ has full column rank.
-/
theorem linearIndependent_transpose_of_mulVec {k : ℕ} {A : Matrix (Fin m) (Fin k) ℝ}
    (h : ∀ x, A *ᵥ x = 0 → x = 0) : LinearIndependent ℝ Aᵀ := by
  refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
  refine congrFun (h g ?_) i
  ext p
  have := congrFun hg p
  simp only [Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul,
    Pi.zero_apply] at this
  simp only [mulVec, dotProduct, Pi.zero_apply]
  rw [← this]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- If $A \in \mathbb{R}^{m \times k}$ has full column rank, then $k \le m$. -/
theorem le_of_linearIndependent_transpose {k : ℕ} {A : Matrix (Fin m) (Fin k) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) : k ≤ m := by
  simpa using hA.fintype_card_le_finrank

/-- If $A = QR$ is a thin QR factorization of a matrix $A \in \mathbb{R}^{m \times k}$ of full
column rank, then $R$ is nonsingular. -/
theorem isUnit_of_isThinQR {k : ℕ} {A Q : Matrix (Fin m) (Fin k) ℝ} {R : Matrix (Fin k) (Fin k) ℝ}
    (h : IsThinQR A Q R) (hA : LinearIndependent ℝ Aᵀ) : IsUnit R := by
  rw [← mulVec_injective_iff_isUnit]
  intro x y hxy
  have : A *ᵥ (x - y) = 0 := by
    rw [← h.mul_eq, ← mulVec_mulVec, mulVec_sub]
    change Q *ᵥ (R *ᵥ x - R *ᵥ y) = 0
    rw [show R *ᵥ x = R *ᵥ y from hxy, sub_self, mulVec_zero]
  exact sub_eq_zero.1 (eq_zero_of_mulVec_eq_zero_of_linearIndependent hA this)

/-- Joining the two column blocks of $A$ along the column split `GolubVanLoan.Chapter05.blockSplit`
gives $A$ with its columns reindexed by the split. -/
theorem fromCols_blockSplit {n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    fromCols (A.submatrix id (blockSplit n ∘ Sum.inl))
      (A.submatrix id (blockSplit n ∘ Sum.inr)) = A.submatrix id (blockSplit n) := by
  ext i (j | j) <;> rfl

/-- For $x$ assembled from $u$ on the first $\lfloor n/2 \rfloor$ columns and $v$ on the others,
$Ax = A_1 u + A_2 v$, where $A_1$ and $A_2$ are the two column blocks of $A$. -/
theorem mulVec_blockSplit {n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (u : Fin (n / 2) → ℝ)
    (v : Fin (n - n / 2) → ℝ) :
    A *ᵥ (fun j => Sum.elim u v ((blockSplit n).symm j)) =
      A.submatrix id (blockSplit n ∘ Sum.inl) *ᵥ u +
        A.submatrix id (blockSplit n ∘ Sum.inr) *ᵥ v := by
  ext p
  simp only [mulVec, dotProduct, Pi.add_apply, submatrix_apply, id, Function.comp_apply]
  rw [← Equiv.sum_comp (blockSplit n), Fintype.sum_sum_type]
  simp

/-- If $n \le m$, the base case of Algorithm 5.2.3 computes a thin QR factorization of
$A \in \mathbb{R}^{m \times n}$ in exact arithmetic. -/
theorem thinHouseholderQR_spec {n : ℕ} (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    IsThinQR A (Id.run (thinHouseholderQR pure A)).1 (Id.run (thinHouseholderQR pure A)).2 := by
  obtain ⟨hQR, -⟩ := algorithm_5_2_1_spec hnm A
  set st := Id.run (algorithm_5_2_1 pure A) with hst
  have hrun : Id.run (thinHouseholderQR pure A) =
      (of fun i (j : Fin n) => if hj : (j : ℕ) < m then
          Id.run (backwardAccumulation pure (storedReflectors st.1 st.2)) i ⟨j, hj⟩ else 0,
        of fun (i : Fin n) j => if hi : (i : ℕ) < m then upperPart st.1 ⟨i, hi⟩ j else 0) := rfl
  have e1 : (of fun i (j : Fin n) => if hj : (j : ℕ) < m then
      Id.run (backwardAccumulation pure (storedReflectors st.1 st.2)) i ⟨j, hj⟩ else 0) =
      firstColumns (factoredQ st.2 st.1) hnm := by
    ext i j
    have hj : (j : ℕ) < m := lt_of_lt_of_le j.isLt hnm
    simp only [of_apply, hj, ↓reduceDIte, backwardAccumulation_spec]
    rfl
  have e2 : (of fun (i : Fin n) j => if hi : (i : ℕ) < m then upperPart st.1 ⟨i, hi⟩ j else 0) =
      firstRows (upperPart st.1) hnm := by
    ext i j
    have hi : (i : ℕ) < m := lt_of_lt_of_le i.isLt hnm
    simp only [of_apply, hi, ↓reduceDIte]
    rfl
  rw [hrun, e1, e2]
  exact hQR.isThinQR hnm

private theorem algorithm_5_2_3_spec_aux (nb : ℕ) :
    ∀ n (A : Matrix (Fin m) (Fin n) ℝ), LinearIndependent ℝ Aᵀ →
      IsThinQR A (Id.run (algorithm_5_2_3 pure nb A)).1
        (Id.run (algorithm_5_2_3 pure nb A)).2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hA
  rw [algorithm_5_2_3]
  split_ifs with h
  · exact thinHouseholderQR_spec (le_of_linearIndependent_transpose hA) A
  · have hn1 : n / 2 < n := by omega
    have hn2 : n - n / 2 < n := by omega
    set e := blockSplit n with he
    set A₁ := A.submatrix id (e ∘ Sum.inl) with hA₁
    set A₂ := A.submatrix id (e ∘ Sum.inr) with hA₂
    have hA₁i : LinearIndependent ℝ A₁ᵀ := hA.comp _ (e.injective.comp Sum.inl_injective)
    simp only [Id.run_bind, Id.run_pure, Chapter01.algorithm_1_1_5_spec, zero_add]
    set QR₁ := Id.run (algorithm_5_2_3 pure nb A₁) with hQR₁
    obtain ⟨h1m, h1o, h1u⟩ := ih _ hn1 A₁ hA₁i
    rw [← hQR₁] at h1m h1o h1u
    set Q₁ := QR₁.1 with hQ₁
    set R₁₁ := QR₁.2 with hR₁₁
    rw [conjTranspose_eq_transpose_of_trivial] at h1o
    set R₁₂ := Q₁ᵀ * A₂ with hR₁₂
    set A₂' := A₂ + -Q₁ * R₁₂ with hA₂'
    have hR₁₁u : IsUnit R₁₁.det :=
      (isUnit_iff_isUnit_det _).1 (isUnit_of_isThinQR ⟨h1m, by
        rw [conjTranspose_eq_transpose_of_trivial]; exact h1o, h1u⟩ hA₁i)
    have hQ₁A : Q₁ = A₁ * R₁₁⁻¹ := by
      rw [← h1m, mul_nonsing_inv_cancel_right _ _ hR₁₁u]
    -- `Q₁ᵀ A₂' = 0`
    have hQA₂' : Q₁ᵀ * A₂' = 0 := by
      rw [hA₂', Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, h1o,
        Matrix.one_mul, hR₁₂, add_neg_cancel]
    -- `A₂'` has full column rank
    have hA₂'i : LinearIndependent ℝ A₂'ᵀ := by
      refine linearIndependent_transpose_of_mulVec fun c hc => ?_
      set d := R₁₁⁻¹ *ᵥ (R₁₂ *ᵥ c) with hd
      have h2 : A₂ *ᵥ c = A₁ *ᵥ d := by
        have := hc
        rw [hA₂', add_mulVec, Matrix.neg_mul, neg_mulVec, add_neg_eq_zero] at this
        rw [this, hd, mulVec_mulVec, ← hQ₁A, mulVec_mulVec]
      have hx := mulVec_blockSplit A (-d) c
      rw [← hA₁, ← hA₂, mulVec_neg, h2, neg_add_cancel] at hx
      have hx0 := eq_zero_of_mulVec_eq_zero_of_linearIndependent hA hx
      funext j
      have := congrFun hx0 (e (Sum.inr j))
      simpa [he] using this
    set QR₂ := Id.run (algorithm_5_2_3 pure nb A₂') with hQR₂
    obtain ⟨h2m, h2o, h2u⟩ := ih _ hn2 A₂' hA₂'i
    rw [← hQR₂] at h2m h2o h2u
    set Q₂ := QR₂.1 with hQ₂
    set R₂₂ := QR₂.2 with hR₂₂
    rw [conjTranspose_eq_transpose_of_trivial] at h2o
    have hR₂₂u : IsUnit R₂₂.det :=
      (isUnit_iff_isUnit_det _).1 (isUnit_of_isThinQR ⟨h2m, by
        rw [conjTranspose_eq_transpose_of_trivial]; exact h2o, h2u⟩ hA₂'i)
    have hQ₁Q₂ : Q₁ᵀ * Q₂ = 0 := by
      have : Q₂ = A₂' * R₂₂⁻¹ := by rw [← h2m, mul_nonsing_inv_cancel_right _ _ hR₂₂u]
      rw [this, ← Matrix.mul_assoc, hQA₂', Matrix.zero_mul]
    have hQ₂Q₁ : Q₂ᵀ * Q₁ = 0 := by
      rw [← transpose_transpose (Q₂ᵀ * Q₁), transpose_mul, transpose_transpose, hQ₁Q₂,
        transpose_zero]
    refine ⟨?_, ?_, ?_⟩
    · rw [← submatrix_mul _ _ _ _ _ e.symm.bijective, fromCols_mul_fromBlocks, h1m, h2m,
        Matrix.mul_zero, add_zero, hA₂', Matrix.neg_mul,
        show Q₁ * R₁₂ + (A₂ + -(Q₁ * R₁₂)) = A₂ by abel]
      ext i j
      obtain ⟨b, rfl⟩ := e.surjective j
      rcases b with b | b <;> simp [hA₁, hA₂]
    · rw [conjTranspose_eq_transpose_of_trivial, transpose_submatrix, transpose_fromCols,
        ← submatrix_mul _ _ _ _ _ Function.bijective_id, fromRows_mul_fromCols, h1o, h2o,
        hQ₁Q₂, hQ₂Q₁, fromBlocks_one, submatrix_one_equiv]
    · intro i j hij
      obtain ⟨a, rfl⟩ := e.surjective i
      obtain ⟨b, rfl⟩ := e.surjective j
      replace hij : ((e b : Fin n) : ℕ) < e a := hij
      rw [he] at hij
      simp only [submatrix_apply, Equiv.symm_apply_apply]
      rcases a with a | a <;> rcases b with b | b
      · rw [blockSplit_inl_val, blockSplit_inl_val] at hij
        exact h1u (Fin.lt_def.2 hij)
      · rw [blockSplit_inl_val, blockSplit_inr_val] at hij
        omega
      · rfl
      · rw [blockSplit_inr_val, blockSplit_inr_val] at hij
        exact h2u (show b < a from Fin.lt_def.2 (by omega))

/-- **Algorithm 5.2.3** of [golub2013matrix], exact correctness. Let $A \in \mathbb{R}^{m \times n}$
have full column rank, and let $n_b \ge 0$ be any block size. Then the output $(Q_1, R_1)$ of
Algorithm 5.2.3 in exact arithmetic is a thin QR factorization of $A$: $A = Q_1 R_1$,
$Q_1^T Q_1 = I$, and $R_1$ is upper triangular.

**Generalization.** The source assumes that $n_b$ is a positive integer. The statement holds for
every $n_b \ge 0$; for $n_b = 0$ the program stops the recursion at $n \le 1$
(`GolubVanLoan.Chapter05.algorithm_5_2_3`).

The factorization is `Matrix.IsThinQR`. The proof is a strong induction on $n$ with the block
identities $Q_1 R_{11} = A_1$, $R_{12} = Q_1^T A_2$, $Q_2 R_{22} = A_2 - Q_1 R_{12}$ and
$Q_1^T Q_2 = 0$; the last one holds because $Q_1^T (A_2 - Q_1 R_{12}) = 0$ and $R_{22}$ is
nonsingular. -/
theorem algorithm_5_2_3_spec (nb : ℕ) {n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : LinearIndependent ℝ Aᵀ) :
    IsThinQR A (Id.run (algorithm_5_2_3 pure nb A)).1 (Id.run (algorithm_5_2_3 pure nb A)).2 :=
  algorithm_5_2_3_spec_aux nb n A hA

end BlockQR

/-! ### §5.2.3 Block Householder QR -/

section BlockHouseholder

/-- The list of the columns $q$ with $j \le q < \tau$, in increasing order (0-based): the panel
columns from $j$ on. -/
def colsBetween (n j τ : ℕ) : List (Fin n) :=
  (List.finRange n).filter fun q => j ≤ (q : ℕ) ∧ (q : ℕ) < τ

/-- A column $q$ is in `GolubVanLoan.Chapter05.colsBetween n j τ` if and only if $j \le q < \tau$.
-/
@[simp]
theorem mem_colsBetween {j τ : ℕ} {q : Fin n} :
    q ∈ colsBetween n j τ ↔ j ≤ (q : ℕ) ∧ (q : ℕ) < τ := by
  simp [colsBetween]

/-- The list `GolubVanLoan.Chapter05.colsBetween n j τ` has no duplicates. -/
theorem nodup_colsBetween (j τ : ℕ) : (colsBetween n j τ).Nodup :=
  (List.nodup_finRange n).filter _

/-- The panel $\lambda{:}\tau$ of Algorithm 5.2.2 as a list of columns: $\lambda, \dots, \tau - 1$
in increasing order (0-based). -/
def panelCols (n lam τ : ℕ) : List (Fin n) := ((List.finRange n).take τ).drop lam

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- Step $j$ of the panel factorization of Algorithm 5.2.2, the loop body of Algorithm 5.2.1
restricted to the panel $\lambda{:}\tau$: $[v, \beta] = \operatorname{house}(A(j{:}m, j))$,
$A(j{:}m, j{:}\tau) = (I - \beta v v^T) A(j{:}m, j{:}\tau)$ in place on the full array,
$A(j{+}1{:}m, j) = v(2{:}m{-}j{+}1)$, $\beta$ recorded, and $(v, \beta)$ appended to the
reflector data of the panel. -/
noncomputable def blockPanelStep (τ : ℕ)
    (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) × List ((Fin m → ℝ) × ℝ)) (j : Fin n) :
    M (Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) × List ((Fin m → ℝ) × ℝ)) := do
  let vβ ← houseOn rnd (indexFrom m j) (fun i => st.1 i j)
  let A ← householderApplyLeft rnd vβ.1 vβ.2 (indexFrom m j) (colsBetween n j τ) st.1
  pure (A.updateCol j (fun i => if (j : ℕ) < i then vβ.1 i else A i j),
    Function.update st.2.1 j vβ.2, st.2.2 ++ [vβ])

/-- The block update $A(:, \mathrm{cols}) = (I - WY^T)^T A(:, \mathrm{cols}) = A(:, \mathrm{cols}) -
Y(W^T A(:, \mathrm{cols}))$, in place, column by column. For each listed column $a$, it computes
$t = W^T a$ by Algorithm 1.1.1 entry by entry, then
$a_i \leftarrow \mathrm{fl}(a_i - Y(i, :)\, t)$, with the inner product accumulated as in
Algorithm 1.1.1. -/
noncomputable def wyApplyLeft {r : ℕ} (W Y : Matrix (Fin m) (Fin r) ℝ) (cols : List (Fin n))
    (A : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) :=
  cols.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) q => do
    let t ← (List.finRange r).foldlM (fun (t : Fin r → ℝ) k => do
      let d ← dotAccum rnd (List.finRange m) (fun i => W i k) (fun i => A i q) 0
      pure (Function.update t k d)) 0
    let c ← (List.finRange m).foldlM (fun (c : Fin m → ℝ) i => do
      let yt ← dotAccum rnd (List.finRange r) (Y i) t 0
      let d ← rnd (c i - yt)
      pure (Function.update c i d)) (fun i => A i q)
    pure (A.updateCol q c)) A

/-- The block update of the accumulated orthogonal factor, $Q = Q(I - WY^T) = Q - (QW)Y^T$, in
place, row by row over the listed rows. For each row $i$ it computes $s = Q(i, :)\, W$ by
Algorithm 1.1.1 entry by entry, then $Q(i, p) \leftarrow \mathrm{fl}(Q(i, p) - Y(p, :)\, s)$. -/
noncomputable def wyApplyRight {r : ℕ} (W Y : Matrix (Fin m) (Fin r) ℝ) (rows : List (Fin m))
    (Q : Matrix (Fin m) (Fin m) ℝ) : M (Matrix (Fin m) (Fin m) ℝ) :=
  rows.foldlM (fun (Q : Matrix (Fin m) (Fin m) ℝ) i => do
    let s ← (List.finRange r).foldlM (fun (s : Fin r → ℝ) k => do
      let d ← dotAccum rnd (List.finRange m) (Q i) (fun p => W p k) 0
      pure (Function.update s k d)) 0
    let c ← (List.finRange m).foldlM (fun (c : Fin m → ℝ) p => do
      let ys ← dotAccum rnd (List.finRange r) (Y p) s 0
      let d ← rnd (c p - ys)
      pure (Function.update c p d)) (Q i)
    pure (Q.updateRow i c)) Q

/-- One pass of the while loop of Algorithm 5.2.2, at panel start $\lambda$ with block size $r$.
With $\tau = \min(\lambda + r, n)$ the panel is the columns $\lambda, \dots, \tau - 1$; this is
the source's $\tau = \min(\lambda + r - 1, n)$ in 0-based form. The pass factors the panel by
`GolubVanLoan.Chapter05.blockPanelStep` and collects its reflector data, forms
$I - WY^T = H_\lambda \cdots H_\tau$ by Algorithm 5.1.2, updates the columns from $\tau$ on by
$(I - WY^T)^T$ (`GolubVanLoan.Chapter05.wyApplyLeft`), and updates $Q = Q(I - WY^T)$
(`GolubVanLoan.Chapter05.wyApplyRight`). -/
noncomputable def blockQRPanel (r : ℕ)
    (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)) (lam : ℕ) :
    M (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)) := do
  let P ← (panelCols n lam (min (lam + r) n)).foldlM (blockPanelStep rnd (min (lam + r) n))
    (st.2.1, st.2.2, [])
  let WY ← algorithm_5_1_2 rnd P.2.2
  let A ← wyApplyLeft rnd WY.1 WY.2 (indexFrom n (min (lam + r) n)) P.1
  let Q ← wyApplyRight rnd WY.1 WY.2 (List.finRange m) st.1
  pure (Q, A, P.2.1)

/-- **Algorithm 5.2.2** of [golub2013matrix] (block Householder QR). If
$A \in \mathbb{R}^{m \times n}$ and $r$ is a positive integer, the algorithm computes an
orthogonal $Q \in \mathbb{R}^{m \times m}$ and an upper triangular
$R \in \mathbb{R}^{m \times n}$ so that $A = QR$.
```
Q = I_m;  λ = 1;  k = 0
while λ ≤ n
    τ = min(λ + r - 1, n);  k = k + 1
    Use Algorithm 5.2.1 to upper triangularize A(λ:m, λ:τ), generating Householder
        matrices H_λ, …, H_τ.
    Use Algorithm 5.1.2 to get the block representation I - W_k Y_kᵀ = H_λ ⋯ H_τ.
    A(λ:m, τ+1:n) = (I - W_k Y_kᵀ)ᵀ A(λ:m, τ+1:n)
    Q(:, λ:m) = Q(:, λ:m)(I - W_k Y_kᵀ)
    λ = τ + 1
end
```
The while loop is a fold over the $\lceil n/r \rceil$ panel starts $0, r, 2r, \dots$, each pass
being `GolubVanLoan.Chapter05.blockQRPanel`. The program returns $(Q, A')$, and $R$ is the upper
triangular part of $A'$.

As in Algorithm 5.2.1, the array keeps the Householder vectors below the diagonal. $W$ and $Y$
are full-length $m \times r$ arrays, zero above row $\lambda$ in exact arithmetic, so the two
block updates run over all rows. -/
noncomputable def algorithm_5_2_2 (r : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) := do
  let st ← ((List.range ((n + r - 1) / r)).map (· * r)).foldlM (blockQRPanel rnd r) (1, A, 0)
  pure (st.1, st.2.1)

end Programs

/-! ### Exact semantics of the block updates -/

/-- A loop that subtracts $h(k)$ from each entry $k$ of a duplicate-free list, once each, changes
the vector $y$ to $y_k - h(k)$ on the listed entries and keeps the other entries. -/
theorem foldl_update_sub_eq {ι : Type*} [DecidableEq ι] (h : ι → ℝ) {l : List ι}
    (hl : l.Nodup) (y₀ : ι → ℝ) :
    l.foldl (fun (y : ι → ℝ) k => Function.update y k (y k - h k)) y₀ =
      fun k => if k ∈ l then y₀ k - h k else y₀ k :=
  List.foldl_update_of_nodup hl (fun k y => y k - h k) (fun _ _ _ _ _ h => by rw [h]) y₀

/-- The exact block update of one column $q$: column $q$ of $A$ becomes column $q$ of $(I - YW^T)A$.
-/
theorem wyApplyLeft_single {r : ℕ} (W Y : Matrix (Fin m) (Fin r) ℝ) (q : Fin n)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (wyApplyLeft pure W Y [q] A) =
      A.updateCol q (fun i => ((1 - Y * Wᵀ : Matrix (Fin m) (Fin m) ℝ) * A) i q) := by
  simp only [wyApplyLeft, List.foldlM_cons, List.foldlM_nil, Id.run_bind, Id.run_pure,
    bind_pure, List.idRun_foldlM, dotAccum_id_finRange, zero_add]
  rw [List.foldl_update_eq_ite, foldl_update_sub_eq _ (List.nodup_finRange m)]
  congr 1
  funext i
  simp only [List.mem_finRange, ↓reduceIte]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.mul_assoc]
  rfl

/-- Exact semantics of the block update: for a duplicate-free list of columns,
`GolubVanLoan.Chapter05.wyApplyLeft` replaces the listed columns of $A$ by those of
$(I - YW^T)A$ and keeps the other columns. -/
theorem wyApplyLeft_pure {r : ℕ} (W Y : Matrix (Fin m) (Fin r) ℝ) {cols : List (Fin n)}
    (hcols : cols.Nodup) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (wyApplyLeft pure W Y cols A) =
      of fun i q => if q ∈ cols then ((1 - Y * Wᵀ : Matrix (Fin m) (Fin m) ℝ) * A) i q
        else A i q := by
  induction cols generalizing A with
  | nil => ext i q; simp [wyApplyLeft]
  | cons a l ih =>
    rcases List.nodup_cons.1 hcols with ⟨ha, hl⟩
    rw [show Id.run (wyApplyLeft pure W Y (a :: l) A) =
      Id.run (wyApplyLeft pure W Y l (Id.run (wyApplyLeft pure W Y [a] A))) from rfl, ih hl,
      wyApplyLeft_single]
    ext i q
    by_cases hq : q ∈ l
    · have hqa : q ≠ a := fun e => ha (e ▸ hq)
      simp only [of_apply, hq, List.mem_cons, or_true, ↓reduceIte, Matrix.mul_apply,
        updateCol_apply, hqa]
    · by_cases hqa : q = a
      · subst hqa
        simp [hq]
      · simp [hq, hqa]

/-- The exact block update of one row $i$ of $Q$: row $i$ becomes row $i$ of $Q(I - WY^T)$. -/
theorem wyApplyRight_single {r : ℕ} (W Y : Matrix (Fin m) (Fin r) ℝ) (i : Fin m)
    (Q : Matrix (Fin m) (Fin m) ℝ) :
    Id.run (wyApplyRight pure W Y [i] Q) =
      Q.updateRow i (fun p => (Q * (1 - W * Yᵀ : Matrix (Fin m) (Fin m) ℝ)) i p) := by
  simp only [wyApplyRight, List.foldlM_cons, List.foldlM_nil, Id.run_bind, Id.run_pure,
    bind_pure, List.idRun_foldlM, dotAccum_id_finRange, zero_add]
  rw [List.foldl_update_eq_ite, foldl_update_sub_eq _ (List.nodup_finRange m)]
  congr 1
  funext p
  simp only [List.mem_finRange, ↓reduceIte]
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, ← Matrix.mul_assoc, dotProduct_comm]
  rfl

/-- Exact semantics of the update of $Q$: for a duplicate-free list of rows,
`GolubVanLoan.Chapter05.wyApplyRight` replaces the listed rows of $Q$ by those of $Q(I - WY^T)$
and keeps the other rows. -/
theorem wyApplyRight_pure {r : ℕ} (W Y : Matrix (Fin m) (Fin r) ℝ) {rows : List (Fin m)}
    (hrows : rows.Nodup) (Q : Matrix (Fin m) (Fin m) ℝ) :
    Id.run (wyApplyRight pure W Y rows Q) =
      of fun i p => if i ∈ rows then (Q * (1 - W * Yᵀ : Matrix (Fin m) (Fin m) ℝ)) i p
        else Q i p := by
  induction rows generalizing Q with
  | nil => ext i p; simp [wyApplyRight]
  | cons a l ih =>
    rcases List.nodup_cons.1 hrows with ⟨ha, hl⟩
    rw [show Id.run (wyApplyRight pure W Y (a :: l) Q) =
      Id.run (wyApplyRight pure W Y l (Id.run (wyApplyRight pure W Y [a] Q))) from rfl, ih hl,
      wyApplyRight_single]
    ext i p
    by_cases hi : i ∈ l
    · have hia : i ≠ a := fun e => ha (e ▸ hi)
      simp only [of_apply, hi, List.mem_cons, or_true, ↓reduceIte, Matrix.mul_apply,
        updateRow_apply, hia]
    · by_cases hia : i = a
      · subst hia
        simp [hi]
      · simp [hi, hia]

/-! ### Exact steps of Householder QR on a column list -/

/-- The exact reflector data $(v, \beta) = \operatorname{house}(B(j{:}m, j))$ of step $j$ on the
array $B$. -/
noncomputable def exactHouse (B : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) : (Fin m → ℝ) × ℝ :=
  Id.run (houseOn pure (indexFrom m j) (fun i => B i j))

/-- The reflector $I - \beta v v^T$ of $p = (v, \beta)$ applied to the listed columns of $B$; the
other columns are kept. -/
noncomputable def reflectCols (p : (Fin m → ℝ) × ℝ) (cols : List (Fin n))
    (B : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  of fun i q => if q ∈ cols then
    ((1 - p.2 • vecMulVec p.1 p.1 : Matrix (Fin m) (Fin m) ℝ) * B) i q else B i q

/-- Column $j$ of $B$ with its entries below the diagonal replaced by those of $v$. -/
def storeCol (j : Fin n) (v : Fin m → ℝ) (B : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  B.updateCol j (fun i => if (j : ℕ) < i then v i else B i j)

/-- One exact step $j$ of Householder QR in which the reflector is applied to the column list
`cols j`: the reflector of `GolubVanLoan.Chapter05.exactHouse` is applied to these columns, the
Householder vector is stored below the diagonal of column $j$, $\beta_j$ is recorded, and
$(v, \beta)$ is appended to the reflector data. -/
noncomputable def exactQRStep (cols : Fin n → List (Fin n))
    (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) × List ((Fin m → ℝ) × ℝ)) (j : Fin n) :
    Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) × List ((Fin m → ℝ) × ℝ) :=
  (storeCol j (exactHouse st.1 j).1 (reflectCols (exactHouse st.1 j) (cols j) st.1),
    Function.update st.2.1 j (exactHouse st.1 j).2, st.2.2 ++ [exactHouse st.1 j])

/-- If $n \le m$, the exact step $j$ of Algorithm 5.2.1 is `GolubVanLoan.Chapter05.exactQRStep` on
the columns $j, \dots, n - 1$, without its reflector data. -/
theorem run_householderQRStep (hnm : n ≤ m) (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ))
    (D : List ((Fin m → ℝ) × ℝ)) (j : Fin n) :
    Id.run (householderQRStep pure st j) =
      ((exactQRStep (fun j => indexFrom n j) (st.1, st.2, D) j).1,
        (exactQRStep (fun j => indexFrom n j) (st.1, st.2, D) j).2.1) := by
  have hjm : (j : ℕ) < m := lt_of_lt_of_le j.isLt hnm
  obtain ⟨-, hvout, -⟩ :=
    houseOn_spec (nodup_indexFrom m j) (indexFrom_ne_nil hjm) (fun i => st.1 i j)
  simp only [householderQRStep, Id.run_bind, Id.run_pure]
  rw [householderApplyLeft_spec (nodup_indexFrom m j) (nodup_indexFrom n j) hvout]
  rfl

/-- If $n \le m$, the exact step $j$ of the panel factorization of Algorithm 5.2.2 is
`GolubVanLoan.Chapter05.exactQRStep` on the panel columns $j, \dots, \tau - 1$. -/
theorem run_blockPanelStep (hnm : n ≤ m) (τ : ℕ)
    (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) × List ((Fin m → ℝ) × ℝ)) (j : Fin n) :
    Id.run (blockPanelStep pure τ st j) = exactQRStep (fun j => colsBetween n j τ) st j := by
  have hjm : (j : ℕ) < m := lt_of_lt_of_le j.isLt hnm
  obtain ⟨-, hvout, -⟩ :=
    houseOn_spec (nodup_indexFrom m j) (indexFrom_ne_nil hjm) (fun i => st.1 i j)
  simp only [blockPanelStep, Id.run_bind, Id.run_pure]
  rw [householderApplyLeft_spec (nodup_indexFrom m j) (nodup_colsBetween j τ) hvout]
  rfl

/-- The array whose columns before $\tau$ are those of $X$ and whose other columns are those of $Y$.
-/
def colMix (τ : ℕ) (X Y : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  of fun i q => if (q : ℕ) < τ then X i q else Y i q

/-- If $X$ and $Y$ agree in column $q$, then $NX$ and $NY$ agree in column $q$. -/
theorem mul_apply_eq_of_col_eq {p : ℕ} (N : Matrix (Fin m) (Fin m) ℝ)
    {X Y : Matrix (Fin m) (Fin p) ℝ} {q : Fin p} (h : ∀ r, X r q = Y r q) (i : Fin m) :
    (N * X) i q = (N * Y) i q := by
  simp only [Matrix.mul_apply, h]

/-- One unblocked step against one panel step. Let $j < \tau$, and let the array have its columns
before $\tau$ from $B_p$ and its other columns from $P^T C$. Then step $j$ of Algorithm 5.2.1,
applied to all columns from $j$ on, equals the panel step on $B_p$, applied to the columns
$j{:}\tau$, with the trailing columns now $(PH_j)^T C$ for the reflector $H_j$ of the step; both
record the same $\beta_j$ and the same reflector. -/
theorem exactQRStep_panel (τ : ℕ) (Bp C : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin m) (Fin m) ℝ) (β : Fin n → ℝ) (D₀ E₀ : List ((Fin m → ℝ) × ℝ)) (j : Fin n)
    (hj : (j : ℕ) < τ) :
    exactQRStep (fun j => indexFrom n j) (colMix τ Bp (Pᵀ * C), β, D₀) j =
      (colMix τ (exactQRStep (fun j => colsBetween n j τ) (Bp, β, E₀) j).1
          ((P * (1 - (exactHouse Bp j).2 •
            vecMulVec (exactHouse Bp j).1 (exactHouse Bp j).1))ᵀ * C),
        (exactQRStep (fun j => colsBetween n j τ) (Bp, β, E₀) j).2.1,
        D₀ ++ [exactHouse Bp j]) := by
  have hx : (fun i => colMix τ Bp (Pᵀ * C) i j) = fun i => Bp i j := by
    funext i
    simp [colMix, hj]
  have hH : exactHouse (colMix τ Bp (Pᵀ * C)) j = exactHouse Bp j := by
    unfold exactHouse
    rw [hx]
  simp only [exactQRStep, hH]
  set p := exactHouse Bp j with hp
  set H : Matrix (Fin m) (Fin m) ℝ := 1 - p.2 • vecMulVec p.1 p.1 with hHdef
  refine Prod.ext ?_ rfl
  ext i q
  simp only [storeCol, reflectCols, colMix, of_apply, updateCol_apply, mem_indexFrom,
    mem_colsBetween]
  by_cases hqj : q = j
  · subst hqj
    simp only [↓reduceIte, hj, le_refl, true_and]
    split_ifs
    · rfl
    · exact mul_apply_eq_of_col_eq _ (fun r => by simp [hj]) i
  · simp only [hqj, ↓reduceIte]
    by_cases hqτ : (q : ℕ) < τ
    · simp only [hqτ, and_true, ↓reduceIte]
      split_ifs
      · exact mul_apply_eq_of_col_eq _ (fun r => by simp [hqτ]) i
      · rfl
    · have hjq : (j : ℕ) ≤ q := by omega
      simp only [hqτ, ↓reduceIte, hjq]
      rw [← hHdef, transpose_mul, hHdef, transpose_one_sub_smul_vecMulVec, ← hHdef,
        Matrix.mul_assoc]
      exact mul_apply_eq_of_col_eq _ (fun r => by simp [hqτ]) i

/-- A panel against the unblocked steps. For a list of steps $j < \tau$ there is reflector data $D$,
the data that the panel steps collect, such that the steps of Algorithm 5.2.1 on the array with
columns $B_p$ before $\tau$ and $P^T C$ from $\tau$ on equal the panel steps on $B_p$ with the
trailing columns $(PH_D)^T C$, where $H_D$ is the product of the reflectors of $D$. The panel
steps leave the columns from $\tau$ on unchanged. -/
theorem foldl_exactQRStep_panel (τ : ℕ) :
    ∀ (l : List (Fin n)), (∀ j ∈ l, (j : ℕ) < τ) →
      ∀ (Bp C : Matrix (Fin m) (Fin n) ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (β : Fin n → ℝ)
        (D₀ E₀ : List ((Fin m → ℝ) × ℝ)),
      ∃ D, (l.foldl (exactQRStep (fun j => colsBetween n j τ)) (Bp, β, E₀)).2.2 = E₀ ++ D ∧
        l.foldl (exactQRStep (fun j => indexFrom n j)) (colMix τ Bp (Pᵀ * C), β, D₀) =
          (colMix τ (l.foldl (exactQRStep (fun j => colsBetween n j τ)) (Bp, β, E₀)).1
              ((P * householderProduct D)ᵀ * C),
            (l.foldl (exactQRStep (fun j => colsBetween n j τ)) (Bp, β, E₀)).2.1, D₀ ++ D) ∧
        ∀ i (q : Fin n), τ ≤ (q : ℕ) →
          (l.foldl (exactQRStep (fun j => colsBetween n j τ)) (Bp, β, E₀)).1 i q = Bp i q := by
  intro l
  induction l with
  | nil =>
    intro _ Bp C P β D₀ E₀
    refine ⟨[], by simp, ?_, fun _ _ _ => rfl⟩
    simp
  | cons j l ih =>
    intro hl Bp C P β D₀ E₀
    have hj : (j : ℕ) < τ := hl j List.mem_cons_self
    set p := exactHouse Bp j with hp
    set s := exactQRStep (fun j => colsBetween n j τ) (Bp, β, E₀) j with hs
    have hs' : s = (s.1, s.2.1, E₀ ++ [p]) := rfl
    obtain ⟨D', hD', hfull, htrail⟩ := ih (fun k hk => hl k (List.mem_cons_of_mem j hk)) s.1 C
      (P * (1 - p.2 • vecMulVec p.1 p.1)) s.2.1 (D₀ ++ [p]) (E₀ ++ [p])
    refine ⟨p :: D', ?_, ?_, fun i q hq => ?_⟩
    · rw [List.foldl_cons, ← hs, hs', hD']
      simp
    · rw [List.foldl_cons, List.foldl_cons, exactQRStep_panel τ Bp C P β D₀ E₀ j hj, ← hp, ← hs,
        hfull, hs', householderProduct_cons, Matrix.mul_assoc]
      simp
    · rw [List.foldl_cons, ← hs, hs', htrail i q hq, hs]
      have hqj : q ≠ j := fun e => by rw [e] at hq; omega
      simp only [exactQRStep, storeCol, reflectCols, updateCol_apply, hqj, ↓reduceIte, of_apply,
        mem_colsBetween]
      rw [ite_eq_right_iff.2 fun h => absurd h.2 (by omega)]

/-- A column in the panel list `GolubVanLoan.Chapter05.panelCols n λ τ` is less than $\tau$. -/
theorem val_lt_of_mem_panelCols {lam τ : ℕ} {j : Fin n} (h : j ∈ panelCols n lam τ) :
    (j : ℕ) < τ := by
  obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.1 (List.mem_of_mem_drop h)
  simp only [List.getElem_finRange, Fin.val_cast]
  omega

/-- The first $\min(\lambda + r, n)$ columns are the first $\min(\lambda, n)$ columns followed by
the panel $\lambda, \dots, \min(\lambda + r, n) - 1$. -/
theorem take_eq_take_append_panelCols (lam r : ℕ) :
    (List.finRange n).take (min (lam + r) n) =
      (List.finRange n).take (min lam n) ++ panelCols n lam (min (lam + r) n) := by
  unfold panelCols
  by_cases h : lam ≤ n
  · rw [min_eq_left h]
    conv_lhs => rw [← List.take_append_drop lam ((List.finRange n).take (min (lam + r) n))]
    rw [List.take_take, min_eq_left (by omega : lam ≤ min (lam + r) n)]
  · have h1 : min lam n = n := by omega
    have h2 : min (lam + r) n = n := by omega
    rw [h1, h2, List.take_of_length_le (by simp only [List.length_finRange, le_refl]),
      List.drop_eq_nil_of_le (by simp only [List.length_finRange]; omega), List.append_nil]

/-- The exact reflector data of Algorithm 5.2.1 is its factored form: if $n \le m$ and $t \le n$,
the data $(v^{(k)}, \beta_k)$, $k < t$, that the first $t$ exact steps collect are the
Householder vectors stored in the current array together with the recorded $\beta_k$. -/
theorem exactQR_data (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) : ∀ t ≤ n,
    (((List.finRange n).take t).foldl (exactQRStep (fun j => indexFrom n j)) (A, 0, [])).2.2 =
      ((List.finRange n).take t).map fun k =>
        (storedHouseholderVec (((List.finRange n).take t).foldl
            (exactQRStep (fun j => indexFrom n j)) (A, 0, [])).1 k,
          (((List.finRange n).take t).foldl
            (exactQRStep (fun j => indexFrom n j)) (A, 0, [])).2.1 k) := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have ih' := ih (by omega)
    have hlt : t < (List.finRange n).length := by simp only [List.length_finRange]; omega
    rw [List.take_succ_eq_append_getElem hlt, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.map_append]
    set S := ((List.finRange n).take t).foldl (exactQRStep (fun j => indexFrom n j)) (A, 0, [])
      with hS
    set jj := (List.finRange n)[t] with hjj
    have hjjv : (jj : ℕ) = t := by simp [hjj]
    have hjm : (jj : ℕ) < m := by omega
    obtain ⟨hv1, hvout, -⟩ :=
      houseOn_spec (nodup_indexFrom m jj) (indexFrom_ne_nil hjm) (fun i => S.1 i jj)
    rw [head_indexFrom hjm (indexFrom_ne_nil hjm)] at hv1
    have hcol : ∀ k : Fin n, (k : ℕ) < t → ∀ i,
        (exactQRStep (fun j => indexFrom n j) S jj).1 i k = S.1 i k := by
      intro k hk i
      have hkj : k ≠ jj := fun e => by rw [e] at hk; omega
      simp only [exactQRStep, storeCol, reflectCols, updateCol_apply, hkj, ↓reduceIte, of_apply,
        mem_indexFrom]
      rw [ite_eq_right (by omega)]
    have hsv : storedHouseholderVec (exactQRStep (fun j => indexFrom n j) S jj).1 jj =
        (exactHouse S.1 jj).1 := by
      funext i
      simp only [storedHouseholderVec]
      by_cases hij : (i : ℕ) < jj
      · rw [ite_eq_left hij]
        exact (hvout i (by rw [mem_indexFrom]; omega)).symm
      · rw [ite_eq_right hij]
        by_cases hij' : (i : ℕ) = jj
        · rw [ite_eq_left hij']
          have : i = ⟨jj, hjm⟩ := Fin.ext hij'
          rw [this]
          exact hv1.symm
        · rw [ite_eq_right hij']
          simp only [exactQRStep, storeCol, updateCol_self]
          rw [ite_eq_left (by omega)]
    change S.2.2 ++ [exactHouse S.1 jj] = _
    rw [ih']
    congr 1
    · refine List.map_congr_left fun k hk => ?_
      have hk' : (k : ℕ) < t := by
        obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.1 hk
        simp only [List.getElem_finRange, Fin.val_cast]
        omega
      have hkj : k ≠ jj := fun e => by rw [e] at hk'; omega
      refine Prod.ext ?_ ?_
      · funext i
        simp only [storedHouseholderVec, hcol k hk']
      · exact (Function.update_of_ne hkj _ _).symm
    · simp only [List.map_cons, List.map_nil, hsv]
      congr 1
      exact Prod.ext rfl (Function.update_self jj (exactHouse S.1 jj).2 S.2.1).symm

/-- The exact block pass. If $n \le m$, one pass of Algorithm 5.2.2 at $\lambda$ in exact arithmetic
runs the panel steps on the array, multiplies $Q$ by the product $H$ of the panel's reflectors,
and replaces the columns from $\tau = \min(\lambda + r, n)$ on by those of $H^T$ times the array
after the panel steps. -/
theorem run_blockQRPanel (hnm : n ≤ m) (r : ℕ) (Q : Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ) (β : Fin n → ℝ) (lam : ℕ) :
    Id.run (blockQRPanel pure r (Q, B, β) lam) =
      (Q * householderProduct ((panelCols n lam (min (lam + r) n)).foldl
          (exactQRStep (fun j => colsBetween n j (min (lam + r) n))) (B, β, [])).2.2,
        of fun i q => if q ∈ indexFrom n (min (lam + r) n) then
          ((householderProduct ((panelCols n lam (min (lam + r) n)).foldl
            (exactQRStep (fun j => colsBetween n j (min (lam + r) n))) (B, β, [])).2.2)ᵀ *
            ((panelCols n lam (min (lam + r) n)).foldl
              (exactQRStep (fun j => colsBetween n j (min (lam + r) n))) (B, β, [])).1) i q
          else ((panelCols n lam (min (lam + r) n)).foldl
              (exactQRStep (fun j => colsBetween n j (min (lam + r) n))) (B, β, [])).1 i q,
        ((panelCols n lam (min (lam + r) n)).foldl
          (exactQRStep (fun j => colsBetween n j (min (lam + r) n))) (B, β, [])).2.1) := by
  set P := (panelCols n lam (min (lam + r) n)).foldl
    (exactQRStep (fun j => colsBetween n j (min (lam + r) n))) (B, β, []) with hP
  have hPeq : Id.run ((panelCols n lam (min (lam + r) n)).foldlM
      (blockPanelStep pure (min (lam + r) n)) (B, β, [])) = P := by
    rw [List.idRun_foldlM]
    congr 1
    funext st j
    exact run_blockPanelStep hnm _ st j
  simp only [blockQRPanel, Id.run_bind, Id.run_pure]
  rw [hPeq]
  obtain ⟨hWY, -⟩ := algorithm_5_1_2_spec P.2.2
  rw [wyApplyLeft_pure _ _ (nodup_indexFrom n _), wyApplyRight_pure _ _ (List.nodup_finRange m)]
  have hT : (1 - (Id.run (algorithm_5_1_2 pure P.2.2)).2 *
      (Id.run (algorithm_5_1_2 pure P.2.2)).1ᵀ : Matrix (Fin m) (Fin m) ℝ) =
      (householderProduct P.2.2)ᵀ := by
    rw [hWY, transpose_sub, transpose_one, transpose_mul, transpose_transpose]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · ext i p
    simp only [of_apply, List.mem_finRange, ↓reduceIte, hWY]
  · ext i q
    simp only [of_apply, hT]

/-- If $n \le m$, the exact run of Algorithm 5.2.1 over a list of steps is the run of
`GolubVanLoan.Chapter05.exactQRStep` with the columns from each step on, without its reflector
data. -/
theorem foldl_householderQRStep_eq (hnm : n ≤ m) : ∀ (l : List (Fin n))
    (B : Matrix (Fin m) (Fin n) ℝ) (β : Fin n → ℝ) (D : List ((Fin m → ℝ) × ℝ)),
    l.foldl (fun st j => Id.run (householderQRStep pure st j)) (B, β) =
      ((l.foldl (exactQRStep (fun j => indexFrom n j)) (B, β, D)).1,
        (l.foldl (exactQRStep (fun j => indexFrom n j)) (B, β, D)).2.1) := by
  intro l
  induction l with
  | nil => intro B β D; rfl
  | cons j l ih =>
    intro B β D
    rw [List.foldl_cons, List.foldl_cons, run_householderQRStep hnm (B, β) D j]
    exact ih _ _ _

/-- The invariant of Algorithm 5.2.2. If $n \le m$, then after the first $K$ passes in exact
arithmetic the array and the recorded $\beta$ are those of Algorithm 5.2.1 after $\min(Kr, n)$
steps, and $Q$ is the product of the reflectors of these steps. -/
theorem algorithm_5_2_2_inv (hnm : n ≤ m) (r : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (K : ℕ) :
    ((List.range K).map (· * r)).foldl (fun st lam => Id.run (blockQRPanel pure r st lam))
        (1, A, 0) =
      (householderProduct (((List.finRange n).take (min (K * r) n)).foldl
          (exactQRStep (fun j => indexFrom n j)) (A, 0, [])).2.2,
        (((List.finRange n).take (min (K * r) n)).foldl
          (exactQRStep (fun j => indexFrom n j)) (A, 0, [])).1,
        (((List.finRange n).take (min (K * r) n)).foldl
          (exactQRStep (fun j => indexFrom n j)) (A, 0, [])).2.1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih, run_blockQRPanel hnm]
    have hK : (K + 1) * r = K * r + r := by ring
    rw [hK, take_eq_take_append_panelCols (K * r) r, List.foldl_append]
    set U := ((List.finRange n).take (min (K * r) n)).foldl
      (exactQRStep (fun j => indexFrom n j)) (A, 0, []) with hU
    set τ := min (K * r + r) n with hτ
    obtain ⟨D, hD, hfull, htrail⟩ := foldl_exactQRStep_panel τ (panelCols n (K * r) τ)
      (fun j hj => val_lt_of_mem_panelCols hj) U.1 U.1 1 U.2.1 U.2.2 []
    have hmix : colMix τ U.1 ((1 : Matrix (Fin m) (Fin m) ℝ)ᵀ * U.1) = U.1 := by
      ext i q
      simp [colMix]
    rw [hmix] at hfull
    have hfull' : (panelCols n (K * r) τ).foldl (exactQRStep (fun j => indexFrom n j)) U =
        _ := hfull
    rw [hfull']
    rw [List.nil_append] at hD
    rw [hD]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · exact (householderProduct_append _ _).symm
    · ext i q
      simp only [of_apply, colMix, mem_indexFrom, Matrix.one_mul]
      by_cases hq : τ ≤ (q : ℕ)
      · rw [ite_eq_left hq, ite_eq_right (by omega)]
        exact mul_apply_eq_of_col_eq _ (fun r => htrail r q hq) i
      · rw [ite_eq_right hq, ite_eq_left (by omega)]

/-- Algorithm 5.2.2 computes what Algorithm 5.2.1 computes. Let $A \in \mathbb{R}^{m \times n}$ with
$m \ge n$ and $r \ge 1$; in exact arithmetic, the array that Algorithm 5.2.2 returns is the
output $A'$ of Algorithm 5.2.1, and its $Q$ is the factored form $H_1 \cdots H_n$ of the stored
vectors with the returned $\beta$. The blocked updates by $(I - W_k Y_k^T)^T$ and
$I - W_k Y_k^T$ are the products of the panel's reflectors (Algorithm 5.1.2). -/
theorem algorithm_5_2_2_eq (hnm : n ≤ m) {r : ℕ} (hr : 0 < r) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (algorithm_5_2_2 pure r A) =
      (factoredQ (Id.run (algorithm_5_2_1 pure A)).2 (Id.run (algorithm_5_2_1 pure A)).1,
        (Id.run (algorithm_5_2_1 pure A)).1) := by
  have hN : min ((n + r - 1) / r * r) n = n := by
    have := Nat.lt_div_mul_add (a := n + r - 1) hr
    generalize (n + r - 1) / r * r = N at this ⊢
    omega
  have hrun : Id.run (algorithm_5_2_2 pure r A) =
      ((((List.range ((n + r - 1) / r)).map (· * r)).foldl
          (fun st lam => Id.run (blockQRPanel pure r st lam)) (1, A, 0)).1,
        (((List.range ((n + r - 1) / r)).map (· * r)).foldl
          (fun st lam => Id.run (blockQRPanel pure r st lam)) (1, A, 0)).2.1) := by
    simp only [algorithm_5_2_2, Id.run_bind, Id.run_pure, List.idRun_foldlM]
  have htake : (List.finRange n).take n = List.finRange n :=
    List.take_of_length_le (by simp only [List.length_finRange, le_refl])
  have h521 : Id.run (algorithm_5_2_1 pure A) =
      (((List.finRange n).foldl (exactQRStep (fun j => indexFrom n j)) (A, 0, [])).1,
        ((List.finRange n).foldl (exactQRStep (fun j => indexFrom n j)) (A, 0, [])).2.1) := by
    rw [algorithm_5_2_1, List.idRun_foldlM]
    exact foldl_householderQRStep_eq hnm _ A 0 []
  have hdata := exactQR_data hnm A n le_rfl
  rw [htake] at hdata
  rw [hrun, algorithm_5_2_2_inv hnm r A, hN, htake, h521, hdata]
  simp only [factoredQ, storedReflectors, List.ofFn_eq_map]

/-- **Algorithm 5.2.2** of [golub2013matrix], exact correctness. Let $A \in \mathbb{R}^{m \times n}$
with $m \ge n$, let $r \ge 1$ be the block size, and let $(Q, A')$ be the output of Algorithm
5.2.2 in exact arithmetic. Then $Q$ is orthogonal, and $A = QR$ for the upper triangular part
$R$ of $A'$.

**Reading.** The source states the algorithm for every $A \in \mathbb{R}^{m \times n}$. Its
panel factorization is Algorithm 5.2.1, which assumes $m \ge n$, and the statement assumes
$m \ge n$ as well.

The factorization is `Matrix.IsQR`. The proof is `GolubVanLoan.Chapter05.algorithm_5_2_2_eq`:
the blocked algorithm computes the same $Q$ and $R$ as Algorithm 5.2.1, whose specification is
`GolubVanLoan.Chapter05.algorithm_5_2_1_spec`. -/
theorem algorithm_5_2_2_spec (hnm : n ≤ m) {r : ℕ} (hr : 0 < r) (A : Matrix (Fin m) (Fin n) ℝ) :
    IsQR A (Id.run (algorithm_5_2_2 pure r A)).1 (upperPart (Id.run (algorithm_5_2_2 pure r A)).2)
    := by
  rw [algorithm_5_2_2_eq hnm hr A]
  exact (algorithm_5_2_1_spec hnm A).1

end BlockHouseholder

/-! ### §5.2.10 A note on complex Householder QR -/

/-- **Section 5.2.10** of [golub2013matrix], complex Householder QR. Every
$A \in \mathbb{C}^{m \times n}$ has a factorization $A = QR$ with
$Q \in \mathbb{C}^{m \times m}$ unitary and $R \in \mathbb{C}^{m \times n}$ upper triangular.

The factorization is `Matrix.IsQR`. The statement does not say that $Q$ is a product of complex
Householder matrices; the proof specializes `Matrix.exists_isQR`, which constructs $Q$ by
Householder triangularization. -/
theorem complexHouseholderQR (A : Matrix (Fin m) (Fin n) ℂ) : ∃ Q R, IsQR A Q R :=
  exists_isQR A

end GolubVanLoan.Chapter05
