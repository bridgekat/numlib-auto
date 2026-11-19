/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Numlib.LinearAlgebra.Matrix.QR

/-!
# Saad, Section 1.7: Orthogonal vectors and subspaces

This module formalizes §1.7 of [saad2003iterative]: the Gram–Schmidt process (Algorithms 1.1 and
1.2), the QR factorization (1.19), and Householder orthogonalization ((1.20)–(1.28) and Algorithm
1.3). For vectors $x_1, \dots, x_r \in \mathbb{K}^n$, where $\mathbb{K}$ is $\mathbb{R}$ or
$\mathbb{C}$, the Gram–Schmidt process computes orthonormal vectors $q_1, \dots, q_r$ and
coefficients $r_{ij} = (x_j, q_i)$ with $x_j = \sum_{i \le j} r_{ij} q_i$. For a matrix $X$ with
linearly independent columns this is the factorization $X = QR$ with $Q^H Q = I$ and $R$ upper
triangular with positive diagonal. Householder orthogonalization reaches a factorization of the same
form with reflectors $P = I - 2ww^H$.

The module proves that Algorithm 1.1 completes exactly when the $x_j$ are linearly independent, that
Algorithm 1.2 (modified Gram–Schmidt) computes the same $Q$ and $R$ as Algorithm 1.1 in exact
arithmetic, the existence and uniqueness of the QR factorization, the properties of the Householder
reflector, and that the Householder factorization agrees with the Gram–Schmidt factorization up to a
unitary diagonal factor. The proofs specialize the backbone module `Numlib.LinearAlgebra.Matrix.QR`.

## Main definitions

* Algorithm 1.2, `SaadSparse.Chapter01.modifiedGramSchmidt`: the vectors $q_j$ of modified
  Gram–Schmidt.
* Algorithm 1.2, `SaadSparse.Chapter01.modifiedGramSchmidtCoeff`: the coefficients $r_{ij}$ of
  modified Gram–Schmidt.
* Equation (1.28), `SaadSparse.Chapter01.stdCols`: the matrix $E_m = [e_1, \dots, e_m]$ of the first
  $m$ columns of the identity.

## Main results

* Algorithm 1.1, `SaadSparse.Chapter01.gramSchmidt_completes_iff`: Algorithm 1.1 completes all $r$
  steps if and only if $x_1, \dots, x_r$ are linearly independent.
* Algorithm 1.1, `SaadSparse.Chapter01.gramSchmidt_expansion`: $x_j = \sum_{i \le j} r_{ij} q_i$
  with $r_{ij} = (x_j, q_i)$.
* Algorithm 1.2, `SaadSparse.Chapter01.algorithm_1_2_eq`: in exact arithmetic, Algorithm 1.2
  computes the same $q_j$ and the same $r_{ij}$ as Algorithm 1.1.
* Equation (1.19), `SaadSparse.Chapter01.equation_1_19`: a matrix with linearly independent columns
  has a unique factorization $X = QR$ with $Q^H Q = I$ and $R$ upper triangular with positive
  diagonal.
* Equations (1.20)–(1.22), `SaadSparse.Chapter01.equation_1_22`: the Householder reflector built
  from $x \neq 0$ and an index $i$ is involutive and unitary, and maps $x$ to a multiple of $e_i$.
* Equations (1.23)–(1.26), `SaadSparse.Chapter01.householder_mulVec_apply_of_eq_zero`: the reflector
  does not change an entry of a vector at a position where $x$ vanishes, other than the pivot.
* Equations (1.27)–(1.28) and Algorithm 1.3, `SaadSparse.Chapter01.equation_1_28`: for $m \le n$, a
  unitary $P$ makes $PX$ upper triangular, and then $X = (P^H E_m)(E_m^H P X)$ is a factorization
  with orthonormal columns and an upper triangular factor.
* §1.7, `SaadSparse.Chapter01.equation_1_28_normalized`: the Householder factorization and the
  factorization (1.19) differ by a unitary upper triangular factor $D$.

## Conventions

* Indices are $0$-based. The book's $x_1, \dots, x_r$ are `x 0, …, x (r-1)`, and its $q_j$ is
  `SaadSparse.Chapter01.modifiedGramSchmidt x (j-1)`.
* The book's inner product $(x, y) = \sum_i x_i \bar y_i$ is `inner 𝕜 y x`, so the book's
  $r_{ij} = (x_j, q_i)$ is `inner 𝕜 (q i) (x j)`.

## Implementation notes

* The vocabulary of the section is Mathlib's and is not restated: orthogonal and orthonormal sets
  (`Orthonormal`), the orthogonal complement (`Submodule.orthogonal`), the orthogonal projector
  (`Submodule.starProjection`), and the existence of an orthonormal basis of a subspace
  (`stdOrthonormalBasis`).
* Algorithm 1.1 (classical Gram–Schmidt) is Mathlib's `InnerProductSpace.gramSchmidtNormed` applied
  to the family $x_1, \dots, x_r$. The module states the two claims of the book about it: the
  breakdown criterion and the triangular expansion.
* Algorithm 1.2 is written out as the recursion `SaadSparse.Chapter01.modifiedGramSchmidt`, with the
  running vector `SaadSparse.Chapter01.mgsRun` and the coefficients
  `SaadSparse.Chapter01.modifiedGramSchmidtCoeff`.
* Division by a vanishing norm gives zero at that step. The Lean recurrences are defined at
  later steps as well, and the identities of the module apply to those values.

## Deviations from the source

* **Algorithms 1.1 and 1.2** (reading). The book stops at the first zero pivot. The recurrences
  put a zero vector at that index and continue. See `SaadSparse.Chapter01.gramSchmidt_expansion`,
  `SaadSparse.Chapter01.modifiedGramSchmidt` and `SaadSparse.Chapter01.algorithm_1_2_eq`.
* **Equation (1.19)** (generalization). The statement adds uniqueness with a positive real
  diagonal in $R$. See `SaadSparse.Chapter01.equation_1_19`.
* **Derivation of (1.22)** (typo). The book prints $\|x\|_1^2$ where $\|x\|_2^2$ is meant. See
  `SaadSparse.Chapter01.equation_1_22`.
* **Equation (1.22)** (generalization and reading). The reflector uses a conjugate transpose and
  can target any coordinate. The phase of a zero pivot is $1$. See
  `SaadSparse.Chapter01.equation_1_22`.
* **Equation (1.25)** (typo). The book prints the axis entry $z_i = \beta + x_{ii}$, where
  $\beta + x_{kk}$, the pivot of step $k$, is meant. See
  `SaadSparse.Chapter01.householder_mulVec_apply_of_eq_zero`.
* **Equations (1.27)–(1.28) and Algorithm 1.3** (reading). The surface gives the factorization
  with a unitary factor. The individual reflectors and intermediate states are absent from its
  statement. See `SaadSparse.Chapter01.equation_1_28`.
* **§1.7, the leading identity columns** (generalization). A request for more than $n$ columns
  appends zero columns. See `SaadSparse.Chapter01.stdCols`.

## Not formalized

* **The difference between Algorithms 1.1 and 1.2 in floating-point arithmetic.** It belongs to a
  floating-point layer.
* **Algorithm 1.3, the step-by-step program.** The declaration states the factorization that
  results from the reduction.
-/

open InnerProductSpace Matrix

open scoped ComplexOrder Matrix

namespace SaadSparse.Chapter01

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- `𝔼` abbreviates `EuclideanSpace 𝕜 (Fin n)`, the space $\mathbb{K}^n$ of the book, in this
module. -/
local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-!
### Gram–Schmidt for an arbitrary index type

Facts about `InnerProductSpace.gramSchmidt` that the section uses and that neither Mathlib nor the
backbone module `Numlib.Analysis.InnerProductSpace.GramSchmidt` states. They hold for any
well-ordered index type; the statements of the book below are their instances at `Fin r` and at `ℕ`.
-/

section Aux

variable {ι E : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

private theorem inner_gramSchmidt_self (x : ι → E) (j : ι) :
    inner 𝕜 (gramSchmidt 𝕜 x j) (x j) = ((‖gramSchmidt 𝕜 x j‖ : 𝕜)) ^ 2 := by
  conv_lhs => rw [gramSchmidt_def'' 𝕜 x j]
  rw [inner_add_right, inner_sum, inner_self_eq_norm_sq_to_K]
  convert add_zero _
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [inner_smul_right, gramSchmidt_orthogonal 𝕜 x (Finset.mem_Iio.1 hi).ne', mul_zero]

private theorem inner_gramSchmidtNormed_smul (x : ι → E) (i j : ι) :
    inner 𝕜 (gramSchmidtNormed 𝕜 x i) (x j) • gramSchmidtNormed 𝕜 x i
      = (inner 𝕜 (gramSchmidt 𝕜 x i) (x j) / ((‖gramSchmidt 𝕜 x i‖ : 𝕜)) ^ 2)
        • gramSchmidt 𝕜 x i := by
  rw [gramSchmidtNormed, inner_smul_left, RCLike.conj_inv, RCLike.conj_ofReal, smul_smul,
    div_eq_mul_inv, sq, mul_inv]
  ring_nf

private theorem gramSchmidtNormed_pairwise_orthogonal (x : ι → E) :
    Pairwise fun i j => inner 𝕜 (gramSchmidtNormed 𝕜 x i) (gramSchmidtNormed 𝕜 x j) = 0 := by
  intro i j hij
  simp [gramSchmidtNormed, inner_smul_left, inner_smul_right, gramSchmidt_orthogonal 𝕜 x hij]

/-- The Gram–Schmidt vector $\tilde q_j$ is $x_j$ minus its projections on the earlier normalized
vectors: $\tilde q_j = x_j - \sum_{i < j} (x_j, q_i) q_i$.

**Reading.** The printed loop stops at a zero pivot. The formula uses the totalized family and
also holds beyond the first zero pivot. -/
private theorem gramSchmidt_eq_sub_sum (x : ι → E) (j : ι) :
    gramSchmidt 𝕜 x j
      = x j - ∑ i ∈ Finset.Iio j,
          inner 𝕜 (gramSchmidtNormed 𝕜 x i) (x j) • gramSchmidtNormed 𝕜 x i := by
  rw [eq_sub_iff_add_eq, Finset.sum_congr rfl fun i _ => inner_gramSchmidtNormed_smul x i j]
  exact (gramSchmidt_def'' 𝕜 x j).symm

/-- For every $j$, $(x_j, q_j) q_j = \tilde q_j$, where $\tilde q_j$ is the unnormalized
Gram–Schmidt vector; at a breakdown both sides vanish. -/
private theorem inner_gramSchmidtNormed_smul_self (x : ι → E) (j : ι) :
    inner 𝕜 (gramSchmidtNormed 𝕜 x j) (x j) • gramSchmidtNormed 𝕜 x j = gramSchmidt 𝕜 x j := by
  rw [inner_gramSchmidtNormed_smul, inner_gramSchmidt_self]
  rcases eq_or_ne ((‖gramSchmidt 𝕜 x j‖ : 𝕜)) 0 with h | h
  · have h0 : gramSchmidt 𝕜 x j = 0 := by simpa using h
    simp [h0]
  · rw [div_self (pow_ne_zero 2 h), one_smul]

end Aux

/-! ### Algorithm 1.1: the Gram–Schmidt process -/

section Algorithm11

variable {r : ℕ}

/-- **Algorithm 1.1** of [saad2003iterative], breakdown criterion. Let
$x_1, \dots, x_r \in \mathbb{K}^n$, and let $q_1, \dots, q_r$ be the vectors of the Gram–Schmidt
process. Then $q_j \neq 0$ for every $j$ if and only if $x_1, \dots, x_r$ are linearly
independent. Since $q_j \neq 0$ is $r_{jj} \neq 0$, this says that the algorithm completes all
$r$ steps exactly when the $x_j$ are linearly independent; the algorithm stops at the first $j$
where $r_{jj} = 0$.

The vectors $q_j$ are `InnerProductSpace.gramSchmidtNormed 𝕜 x j`. Mathlib proves the direction
from independence to nonvanishing (`InnerProductSpace.gramSchmidt_ne_zero`). The converse holds
because the Gram–Schmidt family is orthogonal for every $x$, so nonvanishing makes it linearly
independent, and it spans the same space as $x$. -/
theorem gramSchmidt_completes_iff (x : Fin r → 𝔼) :
    (∀ j, gramSchmidtNormed 𝕜 x j ≠ 0) ↔ LinearIndependent 𝕜 x := by
  refine ⟨fun h => ?_, fun h j h0 => ?_⟩
  · have hq : LinearIndependent 𝕜 (gramSchmidtNormed 𝕜 x) :=
      linearIndependent_of_ne_zero_of_inner_eq_zero h (gramSchmidtNormed_pairwise_orthogonal x)
    have hspan : Submodule.span 𝕜 (Set.range (gramSchmidtNormed 𝕜 x))
        = Submodule.span 𝕜 (Set.range x) := by
      rw [span_gramSchmidtNormed_range, span_gramSchmidt]
    refine linearIndependent_iff_card_eq_finrank_span.2 ?_
    rw [linearIndependent_iff_card_eq_finrank_span.1 hq]
    exact congrArg (fun p : Submodule 𝕜 𝔼 => Module.finrank 𝕜 p) hspan
  · simpa [h0] using gramSchmidtNormed_unit_length j h

/-- **Algorithm 1.1** of [saad2003iterative], triangular expansion. Let
$x_1, \dots, x_r \in \mathbb{K}^n$, and let $q_1, \dots, q_r$ be the vectors of the Gram–Schmidt
process. Then for every $j$,
$$x_j = \sum_{i \le j} r_{ij} q_i, \qquad r_{ij} = (x_j, q_i).$$

**Reading.** The book gives this expansion at each step of its stopping algorithm. The theorem
uses the totalized Gram–Schmidt family at every index. A zero pivot gives $q_j = r_{jj} = 0$, and
the expansion still holds at later indices. -/
theorem gramSchmidt_expansion (x : Fin r → 𝔼) (j : Fin r) :
    x j = ∑ i ∈ Finset.Iic j,
      inner 𝕜 (gramSchmidtNormed 𝕜 x i) (x j) • gramSchmidtNormed 𝕜 x i := by
  rw [← Finset.Iio_insert, Finset.sum_insert (by simp), inner_gramSchmidtNormed_smul_self,
    gramSchmidt_eq_sub_sum]
  abel

end Algorithm11

/-! ### Algorithm 1.2: modified Gram–Schmidt -/

/-- The inner loop of **Algorithm 1.2** of [saad2003iterative]. For vectors $q_0, q_1, \dots$ and
$v$, the running vector $\hat q^{(k)}$ is defined by $\hat q^{(0)} = v$ and $\hat q^{(k+1)} =
\hat q^{(k)} - (\hat q^{(k)}, q_k) q_k$: the projections on $q_0, \dots, q_{k-1}$ are subtracted
one at a time. -/
noncomputable def mgsRun (q : ℕ → 𝔼) (v : 𝔼) : ℕ → 𝔼
  | 0 => v
  | k + 1 => mgsRun q v k - inner 𝕜 (q k) (mgsRun q v k) • q k

/-- **Algorithm 1.2** of [saad2003iterative] (modified Gram–Schmidt), with $0$-based indices. For
vectors $x_0, x_1, \dots \in \mathbb{K}^n$, the vectors $q_j$ are defined by
$q_0 = x_0 / \|x_0\|_2$ and
$$q_{j+1} = \hat q / \|\hat q\|_2,$$
where $\hat q$ is the running vector `SaadSparse.Chapter01.mgsRun` that starts from $x_{j+1}$
and subtracts the projections on $q_0, \dots, q_j$ one at a time.

**Reading.** The book stops when the running vector has norm zero. The recurrence takes
$q_j = 0$ at such a step and continues. For $x_0 = 0$ and $x_1 \neq 0$, it gives $q_0 = 0$ and
$q_1 = x_1/\|x_1\|_2$.

The book's $q_j$ is `SaadSparse.Chapter01.modifiedGramSchmidt x (j - 1)` before a stop. -/
noncomputable def modifiedGramSchmidt (x : ℕ → 𝔼) : ℕ → 𝔼
  | 0 => ((‖x 0‖ : 𝕜)⁻¹) • x 0
  | j + 1 =>
    let q : ℕ → 𝔼 := fun i => modifiedGramSchmidt x (min i j)
    ((‖mgsRun q (x (j + 1)) (j + 1)‖ : 𝕜)⁻¹) • mgsRun q (x (j + 1)) (j + 1)
  termination_by j => j
  decreasing_by exact Nat.lt_succ_of_le (Nat.min_le_right _ _)

/-- The coefficients $r_{ij}$ of **Algorithm 1.2** of [saad2003iterative]. For $i < j$,
$r_{ij} = (\hat q, q_i)$, where $\hat q$ is the running vector of the inner loop for $x_j$ after
the projections on $q_0, \dots, q_{i-1}$ have been subtracted. The diagonal coefficient $r_{jj}$
is the norm of the vector that the inner loop leaves, and $r_{ij} = 0$ for $i > j$.

**Reading.** The coefficients of the printed loop are available only up to its stopping step.
The recurrence defines them also for later steps. -/
noncomputable def modifiedGramSchmidtCoeff (x : ℕ → 𝔼) (i j : ℕ) : 𝕜 :=
  if i < j then inner 𝕜 (modifiedGramSchmidt x i) (mgsRun (modifiedGramSchmidt x) (x j) i)
  else if i = j then ((‖mgsRun (modifiedGramSchmidt x) (x j) j‖ : 𝕜)) else 0

/-- The inner loop reads only $q_0, \dots, q_{k-1}$. -/
private theorem mgsRun_congr {q q' : ℕ → 𝔼} (v : 𝔼) {k : ℕ} (h : ∀ i < k, q i = q' i) :
    mgsRun q v k = mgsRun q' v k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [mgsRun, mgsRun, ih fun i hi => h i (hi.trans k.lt_succ_self), h k k.lt_succ_self]

/-- If the vectors $q_i$ are pairwise orthogonal, the inner loop subtracts in total
$\sum_{i < k} (v, q_i) q_i$, as classical Gram–Schmidt does in one step. -/
private theorem mgsRun_eq_sub_sum {q : ℕ → 𝔼}
    (ho : ∀ i j, i ≠ j → inner 𝕜 (q i) (q j) = 0) (v : 𝔼) (k : ℕ) :
    mgsRun q v k = v - ∑ i ∈ Finset.range k, inner 𝕜 (q i) v • q i := by
  induction k with
  | zero => simp [mgsRun]
  | succ k ih =>
    have hik : inner 𝕜 (q k) (mgsRun q v k) = inner 𝕜 (q k) v := by
      rw [ih, inner_sub_right, inner_sum]
      refine sub_eq_self.2 (Finset.sum_eq_zero fun i hi => ?_)
      rw [inner_smul_right, ho k i (Ne.symm (Finset.mem_range.1 hi).ne), mul_zero]
    rw [mgsRun, hik, ih, Finset.sum_range_succ]
    abel

/-- If the vectors $q_i$ are pairwise orthogonal, the coefficient that the inner loop reads at step
$k$ is the classical coefficient $(v, q_k)$. -/
private theorem inner_mgsRun_self {q : ℕ → 𝔼}
    (ho : ∀ i j, i ≠ j → inner 𝕜 (q i) (q j) = 0) (v : 𝔼) (k : ℕ) :
    inner 𝕜 (q k) (mgsRun q v k) = inner 𝕜 (q k) v := by
  rw [mgsRun_eq_sub_sum ho, inner_sub_right, inner_sum]
  refine sub_eq_self.2 (Finset.sum_eq_zero fun i hi => ?_)
  rw [inner_smul_right, ho k i (Ne.symm (Finset.mem_range.1 hi).ne), mul_zero]

private theorem mgsRun_gramSchmidtNormed (x : ℕ → 𝔼) (k : ℕ) :
    mgsRun (gramSchmidtNormed 𝕜 x) (x k) k = gramSchmidt 𝕜 x k := by
  rw [mgsRun_eq_sub_sum (fun i j hij => gramSchmidtNormed_pairwise_orthogonal x hij),
    ← Nat.Iio_eq_range]
  exact (gramSchmidt_eq_sub_sum x k).symm

/-- The first step of Algorithm 1.2: $q_0 = x_0 / \|x_0\|_2$, since the inner loop is empty.

**Reading.** When $x_0=0$, the printed loop stops and the total recurrence defines $q_0=0$. -/
@[simp]
theorem modifiedGramSchmidt_zero (x : ℕ → 𝔼) :
    modifiedGramSchmidt x 0 = ((‖x 0‖ : 𝕜)⁻¹) • x 0 := by
  rw [modifiedGramSchmidt]

/-- The later steps of Algorithm 1.2: $q_{j+1}$ is the running vector of the inner loop for
$x_{j+1}$, after the projections on $q_0, \dots, q_j$, divided by its norm.

**Reading.** The printed normalization is conditional on a nonzero residual. The recurrence
uses zero when the residual vanishes and continues. -/
theorem modifiedGramSchmidt_succ (x : ℕ → 𝔼) (j : ℕ) :
    modifiedGramSchmidt x (j + 1)
      = ((‖mgsRun (modifiedGramSchmidt x) (x (j + 1)) (j + 1)‖ : 𝕜)⁻¹)
        • mgsRun (modifiedGramSchmidt x) (x (j + 1)) (j + 1) := by
  rw [modifiedGramSchmidt,
    mgsRun_congr (q := fun i => modifiedGramSchmidt x (min i j)) (q' := modifiedGramSchmidt x)
      (x (j + 1)) fun i hi => by rw [Nat.min_eq_left (Nat.lt_succ_iff.1 hi)]]

/-- For every $j$, the vector $q_j$ of Algorithm 1.2 equals the vector $q_j$ of Algorithm 1.1,
`InnerProductSpace.gramSchmidtNormed 𝕜 x j`.

**Reading.** The comparison extends beyond the printed stopping steps by using the total
recurrences of both algorithms. -/
theorem modifiedGramSchmidt_eq (x : ℕ → 𝔼) (j : ℕ) :
    modifiedGramSchmidt x j = gramSchmidtNormed 𝕜 x j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero =>
      have h0 : gramSchmidt 𝕜 x 0 = x 0 := (mgsRun_gramSchmidtNormed x 0).symm
      rw [modifiedGramSchmidt_zero, gramSchmidtNormed, h0]
    | succ k =>
      rw [modifiedGramSchmidt_succ, mgsRun_congr _ (fun i hi => ih i hi),
        mgsRun_gramSchmidtNormed, gramSchmidtNormed]

/-- For $i \le j$, the coefficient $r_{ij}$ of Algorithm 1.2 equals the coefficient $(x_j, q_i)$ of
Algorithm 1.1.

**Reading.** The comparison uses both total recurrences, with coefficients defined also beyond
a zero pivot. -/
theorem modifiedGramSchmidtCoeff_eq (x : ℕ → 𝔼) {i j : ℕ} (hij : i ≤ j) :
    modifiedGramSchmidtCoeff x i j = inner 𝕜 (gramSchmidtNormed 𝕜 x i) (x j) := by
  have hvec : modifiedGramSchmidt x = gramSchmidtNormed 𝕜 x := funext (modifiedGramSchmidt_eq x)
  rw [modifiedGramSchmidtCoeff, hvec]
  rcases lt_or_eq_of_le hij with h | h
  · rw [ite_eq_left h]
    exact inner_mgsRun_self (fun a b hab => gramSchmidtNormed_pairwise_orthogonal x hab) (x j) i
  · subst h
    rw [ite_eq_right (lt_irrefl i), ite_eq_left rfl, mgsRun_gramSchmidtNormed,
      InnerProductSpace.inner_gramSchmidtNormed_self]

/-- **Algorithm 1.2** of [saad2003iterative], equality with Algorithm 1.1. Let
$x_0, x_1, \dots \in \mathbb{K}^n$. In exact arithmetic, Algorithm 1.2 computes the same vectors
and the same coefficients as Algorithm 1.1: for every $j$ the vector $q_j$ of Algorithm 1.2 is
the Gram–Schmidt vector $q_j$, and for all $i \le j$ the coefficient $r_{ij}$ of Algorithm 1.2
is $(x_j, q_i)$.

**Reading.** Both printed algorithms stop at a zero pivot. The theorem compares their total
recurrences, which assign a zero vector and a zero diagonal coefficient at each zero pivot and
can have nonzero vectors at later indices. -/
theorem algorithm_1_2_eq (x : ℕ → 𝔼) :
    modifiedGramSchmidt x = gramSchmidtNormed 𝕜 x ∧
      ∀ i j, i ≤ j → modifiedGramSchmidtCoeff x i j = inner 𝕜 (gramSchmidtNormed 𝕜 x i) (x j) :=
  ⟨funext (modifiedGramSchmidt_eq x), fun _ _ hij => modifiedGramSchmidtCoeff_eq x hij⟩

/-! ### Equation (1.19): the QR factorization -/

/-- **Equation (1.19)** of [saad2003iterative]. Let $X \in \mathbb{K}^{n \times r}$ have linearly
independent columns. Then there is exactly one pair $(Q, R)$ with
$Q \in \mathbb{K}^{n \times r}$ and $R \in \mathbb{K}^{r \times r}$ such that
$$X = QR, \qquad Q^H Q = I,$$
and $R$ is upper triangular with positive real diagonal entries.

**Generalization.** The book establishes existence of the factorization. The theorem also
establishes uniqueness under the positive real diagonal convention supplied by the algorithm.

The columns of $X$ are the rows of `Xᵀ`, and positivity of a scalar in $\mathbb{K}$ means that
it is real and positive. In this factorization, $Q$ is the Gram–Schmidt orthonormalization of
the columns of $X$ and $r_{ij} = (x_j, q_i)$. -/
theorem equation_1_19 {r : ℕ} (X : Matrix (Fin n) (Fin r) 𝕜) (hX : LinearIndependent 𝕜 Xᵀ) :
    ∃! QR : Matrix (Fin n) (Fin r) 𝕜 × Matrix (Fin r) (Fin r) 𝕜,
      X = QR.1 * QR.2 ∧ QR.1ᴴ * QR.1 = 1 ∧ QR.2.IsUpperTriangular ∧ ∀ j, 0 < QR.2.diag j := by
  obtain ⟨Q, R, ⟨hXQR, hQ, hR⟩, hd⟩ := Matrix.exists_isThinQR X hX
  refine ⟨(Q, R), ⟨hXQR.symm, hQ, hR, hd⟩, ?_⟩
  rintro ⟨Q', R'⟩ ⟨hXQR', hQ', hR', hd'⟩
  obtain ⟨hQQ, hRR⟩ := Matrix.IsThinQR.unique ⟨hXQR'.symm, hQ', hR'⟩ ⟨hXQR, hQ, hR⟩ hd' hd
  exact Prod.ext hQQ hRR

/-! ### Equations (1.20)–(1.28): Householder orthogonalization -/

/-- **Equations (1.20)–(1.22)** of [saad2003iterative]. Let $x \in \mathbb{K}^n$ be nonzero and let
$i$ be an index. Let
$$w = \frac{x + \operatorname{sign}(\xi_i) \|x\|_2 e_i}{\|x + \operatorname{sign}(\xi_i) \|x\|_2
  e_i\|_2},$$
where $\xi_i$ is entry $i$ of $x$, and let $P = I - 2ww^H$ be the Householder reflector. Then
$P^2 = I$, $P$ is unitary, and
$$Px = -\operatorname{sign}(\xi_i) \|x\|_2 e_i,$$
so one reflector annihilates every entry of $x$ except entry $i$.

**Typo.** The derivation in the book, in which $2(x - \alpha e_1)^T x = \|x - \alpha e_1\|_2^2$
forces $\alpha = \pm \|x\|_2$, prints $\|x\|_1^2$ where $\|x\|_2^2$ is meant.

**Generalization.** The printed derivation uses a real reflector targeting $e_1$. The theorem
uses $ww^H$ over complex scalars and can target any $e_i$.

**Reading.** The printed formula leaves the zero pivot case implicit. Taking the phase
to be $1$ there preserves a nonzero pivot magnitude when $x$ is nonzero.

The phase is `Matrix.phase`, the vector $w$ is `Matrix.householderVec x i`, and $P$ is
`Matrix.householder`. -/
theorem equation_1_22 {x : Fin n → 𝕜} (hx : x ≠ 0) (i : Fin n) :
    householder (householderVec x i) * householder (householderVec x i) = 1 ∧
      householder (householderVec x i) ∈ Matrix.unitaryGroup (Fin n) 𝕜 ∧
      householder (householderVec x i) *ᵥ x
        = (-(phase (x i) * ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 (Fin n))‖ : 𝕜))))
          • (Pi.single i 1 : Fin n → 𝕜) :=
  ⟨householder_mul_self (star_dotProduct_householderVec_self hx i),
    householder_householderVec_mem_unitaryGroup hx i,
    householder_mulVec_eq_smul_single hx i⟩

/-- **Equations (1.23)–(1.26)** of [saad2003iterative]. Let $x \in \mathbb{K}^n$, let $i$ be the
pivot index, and let $P$ be the Householder reflector of $x$ and $i$. If $s \neq i$ and
$x_s = 0$, then $(Pz)_s = z_s$ for every $z \in \mathbb{K}^n$. So the reflector of step $k$ of
Algorithm 1.3, built from a vector that vanishes above the pivot, acts only on the entries from
$k$ on.

**Typo.** The book's (1.25) prints the axis entry $z_i = \beta + x_{ii}$, where
$\beta + x_{kk}$, the pivot of step $k$, is meant. The backbone's `Matrix.householderAxis` has
the correct form, which is the one that Algorithm 1.3 needs.

Where $x$ vanishes, the axis $w$ of the reflector also vanishes, and this gives the statement. -/
theorem householder_mulVec_apply_of_eq_zero {x : Fin n → 𝕜} {i s : Fin n} (hsi : s ≠ i)
    (hs : x s = 0) (z : Fin n → 𝕜) : (householder (householderVec x i) *ᵥ z) s = z s := by
  rw [householder_mulVec, Pi.sub_apply, Pi.smul_apply, householderVec_apply_eq_zero hsi hs,
    smul_zero, sub_zero]

/-- **Equation (1.28)** of [saad2003iterative]. The matrix $E_m = [e_1, e_2, \dots, e_m] \in
\mathbb{K}^{n \times m}$ has entry $1$ at position $(i, j)$ when $i = j$, and $0$ elsewhere. For
$m \le n$ its columns are the first $m$ columns of the $n \times n$ identity matrix.

**Generalization.** The source selects at most $n$ columns. When $m>n$, the entry formula
appends $m-n$ zero columns. -/
def stdCols (𝕜 : Type*) [RCLike 𝕜] (n m : ℕ) : Matrix (Fin n) (Fin m) 𝕜 :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0

/-- The entry of $E_m$ at $(i, j)$ is $1$ if $i = j$ and $0$ otherwise. -/
@[simp]
theorem stdCols_apply {m : ℕ} (i : Fin n) (j : Fin m) :
    stdCols 𝕜 n m i j = if (i : ℕ) = (j : ℕ) then 1 else 0 := rfl

/-- If $m \le n$, then $E_m^H E_m = I$: the columns of $E_m$ are orthonormal. -/
theorem conjTranspose_stdCols_mul_self {m : ℕ} (hmn : m ≤ n) :
    (stdCols 𝕜 n m)ᴴ * stdCols 𝕜 n m = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE hmn i), Matrix.one_apply]
  · rw [conjTranspose_apply, stdCols_apply, stdCols_apply]
    simp [Fin.ext_iff]
  · intro k _ hk
    have hki : ¬((k : ℕ) = (i : ℕ)) := fun h => hk (Fin.ext h)
    rw [conjTranspose_apply, stdCols_apply, ite_eq_right hki, star_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- If $m \le n$, then for every matrix $M$ with $n$ rows, $E_m^H M$ consists of the first $m$ rows
of $M$. -/
theorem conjTranspose_stdCols_mul_apply {m k : ℕ} (hmn : m ≤ n) (M : Matrix (Fin n) (Fin k) 𝕜)
    (i : Fin m) (j : Fin k) : ((stdCols 𝕜 n m)ᴴ * M) i j = M (Fin.castLE hmn i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE hmn i)]
  · rw [conjTranspose_apply, stdCols_apply]
    simp
  · intro k' _ hk'
    have hki : ¬((k' : ℕ) = (i : ℕ)) := fun h => hk' (Fin.ext h)
    rw [conjTranspose_apply, stdCols_apply, ite_eq_right hki, star_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- If $m \le n$ and the rows of $M$ with index at least $m$ vanish, then $E_m E_m^H M = M$. -/
theorem stdCols_mul_conjTranspose_stdCols_mul {m k : ℕ} (hmn : m ≤ n)
    {M : Matrix (Fin n) (Fin k) 𝕜} (hM : ∀ (i : Fin n) (j : Fin k), m ≤ (i : ℕ) → M i j = 0) :
    stdCols 𝕜 n m * ((stdCols 𝕜 n m)ᴴ * M) = M := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : (i : ℕ) < m
  · rw [Finset.sum_eq_single (⟨(i : ℕ), hi⟩ : Fin m)]
    · rw [stdCols_apply, conjTranspose_stdCols_mul_apply hmn]
      have hcast : Fin.castLE hmn (⟨(i : ℕ), hi⟩ : Fin m) = i := Fin.ext rfl
      rw [hcast]
      simp
    · intro k' _ hk'
      have hik : ¬((i : ℕ) = (k' : ℕ)) := fun h => hk' (Fin.ext h.symm)
      rw [stdCols_apply, ite_eq_right hik, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [hM i j (Nat.not_lt.1 hi)]
    refine Finset.sum_eq_zero fun k' _ => ?_
    have hik : ¬((i : ℕ) = (k' : ℕ)) := by
      have := k'.isLt
      omega
    rw [stdCols_apply, ite_eq_right hik, zero_mul]

/-- If $P$ is unitary and $PX$ is upper triangular, then $Q = P^H E_m$ has orthonormal columns,
$R = E_m^H P X$ is upper triangular, and $X = QR$. -/
private theorem factorization_of_unitary_mul_upperTriangular {m : ℕ} (hmn : m ≤ n)
    {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P ∈ Matrix.unitaryGroup (Fin n) 𝕜)
    {X : Matrix (Fin n) (Fin m) 𝕜}
    (hT : ∀ (i : Fin n) (j : Fin m), (j : ℕ) < (i : ℕ) → (P * X) i j = 0) :
    X = (Pᴴ * stdCols 𝕜 n m) * ((stdCols 𝕜 n m)ᴴ * (P * X)) ∧
      (Pᴴ * stdCols 𝕜 n m)ᴴ * (Pᴴ * stdCols 𝕜 n m) = 1 ∧
      ((stdCols 𝕜 n m)ᴴ * (P * X)).IsUpperTriangular := by
  have hPP : Pᴴ * P = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.1 hP
    rwa [Matrix.star_eq_conjTranspose] at h
  have hPPh : P * Pᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.1 hP
    rwa [Matrix.star_eq_conjTranspose] at h
  refine ⟨?_, ?_, ?_⟩
  · have hrows : ∀ (i : Fin n) (j : Fin m), m ≤ (i : ℕ) → (P * X) i j = 0 := fun i j hi =>
      hT i j (by have := j.isLt; omega)
    calc X = Pᴴ * (P * X) := by rw [← Matrix.mul_assoc, hPP, Matrix.one_mul]
      _ = Pᴴ * (stdCols 𝕜 n m * ((stdCols 𝕜 n m)ᴴ * (P * X))) := by
          rw [stdCols_mul_conjTranspose_stdCols_mul hmn hrows]
      _ = (Pᴴ * stdCols 𝕜 n m) * ((stdCols 𝕜 n m)ᴴ * (P * X)) := (Matrix.mul_assoc _ _ _).symm
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc (stdCols 𝕜 n m)ᴴ * P * (Pᴴ * stdCols 𝕜 n m)
        = (stdCols 𝕜 n m)ᴴ * (P * Pᴴ * stdCols 𝕜 n m) := by simp only [Matrix.mul_assoc]
      _ = (stdCols 𝕜 n m)ᴴ * stdCols 𝕜 n m := by rw [hPPh, Matrix.one_mul]
      _ = 1 := conjTranspose_stdCols_mul_self hmn
  · intro i j hji
    rw [conjTranspose_stdCols_mul_apply hmn]
    exact hT (Fin.castLE hmn i) j hji

/-- **Equations (1.27)–(1.28)** and **Algorithm 1.3** of [saad2003iterative]. Let $m \le n$ and
$X \in \mathbb{K}^{n \times m}$. Then there is a unitary $P \in \mathbb{K}^{n \times n}$ such
that $PX$ is upper triangular, that is $(PX)_{ij} = 0$ for $j < i$, and with $Q = P^H E_m$ and
$R = E_m^H P X$,
$$X = QR, \qquad Q^H Q = I,$$
and $R$ is upper triangular.

**Reading.** The source describes the successive reflectors and the resulting orthogonal
factorization. The theorem asserts the final factorization using a unitary $P$ and therefore
also covers complex inputs. The individual steps of Algorithm 1.3 are outside its conclusion.

The backbone constructs $P$ as a product of reflectors by
`Matrix.exists_unitary_mul_upperTriangular`. The comparison with positive-diagonal QR is
`SaadSparse.Chapter01.equation_1_28_normalized`. -/
theorem equation_1_28 {m : ℕ} (hmn : m ≤ n) (X : Matrix (Fin n) (Fin m) 𝕜) :
    ∃ P ∈ Matrix.unitaryGroup (Fin n) 𝕜,
      (∀ (i : Fin n) (j : Fin m), (j : ℕ) < (i : ℕ) → (P * X) i j = 0) ∧
        X = (Pᴴ * stdCols 𝕜 n m) * ((stdCols 𝕜 n m)ᴴ * (P * X)) ∧
        (Pᴴ * stdCols 𝕜 n m)ᴴ * (Pᴴ * stdCols 𝕜 n m) = 1 ∧
        ((stdCols 𝕜 n m)ᴴ * (P * X)).IsUpperTriangular := by
  obtain ⟨P, hP, hT⟩ := Matrix.exists_unitary_mul_upperTriangular X
  exact ⟨P, hP, hT, factorization_of_unitary_mul_upperTriangular hmn hP hT⟩

/-- Two factorizations $X = Q_0 R_0 = QR$ with $Q_0^H Q_0 = Q^H Q = I$ and $R$ invertible differ by
the unitary matrix $D = R_0 R^{-1}$: $Q = Q_0 D$ and $R = D^H R_0$. -/
private theorem qr_change_of_factor {m : ℕ} {X Q₀ Q : Matrix (Fin n) (Fin m) 𝕜}
    {R₀ R : Matrix (Fin m) (Fin m) 𝕜} (hX₀ : X = Q₀ * R₀) (hX : X = Q * R)
    (hQ₀ : Q₀ᴴ * Q₀ = 1) (hQ : Qᴴ * Q = 1) (hdet : IsUnit R.det) :
    (R₀ * R⁻¹)ᴴ * (R₀ * R⁻¹) = 1 ∧ Q = Q₀ * (R₀ * R⁻¹) ∧ R = (R₀ * R⁻¹)ᴴ * R₀ := by
  have hRR : R₀ᴴ * R₀ = Rᴴ * R := by
    have h1 : Xᴴ * X = R₀ᴴ * R₀ := by
      rw [hX₀, conjTranspose_mul]
      calc R₀ᴴ * Q₀ᴴ * (Q₀ * R₀) = R₀ᴴ * (Q₀ᴴ * Q₀ * R₀) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc]
        _ = R₀ᴴ * R₀ := by rw [hQ₀, Matrix.one_mul]
    have h2 : Xᴴ * X = Rᴴ * R := by
      rw [hX, conjTranspose_mul]
      calc Rᴴ * Qᴴ * (Q * R) = Rᴴ * (Qᴴ * Q * R) := by rw [Matrix.mul_assoc, Matrix.mul_assoc]
        _ = Rᴴ * R := by rw [hQ, Matrix.one_mul]
    rw [← h1, h2]
  have hDu : (R₀ * R⁻¹)ᴴ * (R₀ * R⁻¹) = 1 := by
    have h1 : (R₀ * R⁻¹)ᴴ * (R₀ * R⁻¹) = (R⁻¹)ᴴ * (R₀ᴴ * R₀ * R⁻¹) := by
      rw [conjTranspose_mul]; noncomm_ring
    have h2 : (R⁻¹)ᴴ * (Rᴴ * R * R⁻¹) = (R * R⁻¹)ᴴ * (R * R⁻¹) := by
      rw [conjTranspose_mul]; noncomm_ring
    rw [h1, hRR, h2, mul_nonsing_inv R hdet, conjTranspose_one, mul_one]
  refine ⟨hDu, ?_, ?_⟩
  · calc Q = Q * (R * R⁻¹) := by rw [mul_nonsing_inv R hdet, Matrix.mul_one]
      _ = Q * R * R⁻¹ := (Matrix.mul_assoc _ _ _).symm
      _ = Q₀ * R₀ * R⁻¹ := by rw [← hX, hX₀]
      _ = Q₀ * (R₀ * R⁻¹) := Matrix.mul_assoc _ _ _
  · have hDR : R₀ * R⁻¹ * R = R₀ := by
      rw [Matrix.mul_assoc, nonsing_inv_mul R hdet, Matrix.mul_one]
    calc R = (R₀ * R⁻¹)ᴴ * (R₀ * R⁻¹) * R := by rw [hDu, Matrix.one_mul]
      _ = (R₀ * R⁻¹)ᴴ * (R₀ * R⁻¹ * R) := Matrix.mul_assoc _ _ _
      _ = (R₀ * R⁻¹)ᴴ * R₀ := by rw [hDR]

/-- The two QR constructions of §1.7 of [saad2003iterative] agree up to diagonal unitary scaling.
Let $m \le n$, and let $X = QR$ with $Q \in \mathbb{K}^{n \times m}$, $Q^H Q = I$, and
$R \in \mathbb{K}^{m \times m}$ upper triangular with positive real diagonal entries. Then there
are a unitary $P \in \mathbb{K}^{n \times n}$ such that $PX$ is upper triangular and a matrix
$D \in \mathbb{K}^{m \times m}$ with $D^H D = I$ and $D$ upper triangular, such that
$$Q = P^H E_m D, \qquad R = D^H E_m^H P X.$$

A unitary upper triangular matrix is diagonal with entries of modulus $1$, so the Householder
factorization and the factorization (1.19) differ only by the signs of the columns. If these
signs are normalized, the Householder factors become the pair of (1.19), which by uniqueness is
the Gram–Schmidt pair. As in `SaadSparse.Chapter01.equation_1_28`, the statement asserts only
that $P$ is unitary; the backbone constructs it from Householder reflectors. -/
theorem equation_1_28_normalized {m : ℕ} (hmn : m ≤ n) {X Q : Matrix (Fin n) (Fin m) 𝕜}
    {R : Matrix (Fin m) (Fin m) 𝕜} (hXQR : X = Q * R) (hQ : Qᴴ * Q = 1)
    (hR : R.IsUpperTriangular) (hd : ∀ j, 0 < R.diag j) :
    ∃ P ∈ Matrix.unitaryGroup (Fin n) 𝕜, ∃ D : Matrix (Fin m) (Fin m) 𝕜,
      (∀ (i : Fin n) (j : Fin m), (j : ℕ) < (i : ℕ) → (P * X) i j = 0) ∧
        Dᴴ * D = 1 ∧ D.IsUpperTriangular ∧ Q = (Pᴴ * stdCols 𝕜 n m) * D ∧
        R = Dᴴ * ((stdCols 𝕜 n m)ᴴ * (P * X)) := by
  obtain ⟨P, hP, hT⟩ := Matrix.exists_unitary_mul_upperTriangular X
  obtain ⟨hX₀, hQ₀, hR₀⟩ := factorization_of_unitary_mul_upperTriangular hmn hP hT
  have hdet : IsUnit R.det := by
    rw [det_of_isUpperTriangular hR, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun j _ => (hd j).ne'
  have : Invertible R := invertibleOfIsUnitDet R hdet
  obtain ⟨hDu, hQeq, hReq⟩ := qr_change_of_factor hX₀ hXQR hQ₀ hQ hdet
  exact ⟨P, hP, _, hT, hDu, hR₀.mul (blockTriangular_inv_of_blockTriangular hR), hQeq, hReq⟩

end SaadSparse.Chapter01
