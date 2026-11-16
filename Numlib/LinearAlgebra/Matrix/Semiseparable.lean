/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a file beside `Mathlib.LinearAlgebra.Matrix.Rank`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.LinearAlgebra.Matrix.Charpoly
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.Kronecker
import Numlib.LinearAlgebra.Matrix.LU
import Numlib.LinearAlgebra.Matrix.PlaneRotation
import Numlib.LinearAlgebra.Matrix.Products
import Numlib.LinearAlgebra.Matrix.Rank
import Numlib.LinearAlgebra.Matrix.Similar

/-!
# Semiseparable and quasiseparable matrices

Let $K$ be a field and $A$ a square matrix over $K$ with finite, totally ordered indices. The matrix
$A$ is **semiseparable** if every block of $A$ that lies on or below the diagonal, and every block
that lies on or above it, has rank at most one. It is **quasiseparable** if every block strictly
below or strictly above the diagonal has rank at most one. This module follows [golub2013matrix]
§12.2 and Vandebril, Van Barel and Mastronardi (2008). It defines the two classes and their
generator and quasiseparable representations, and it proves the facts about inverses and
factorizations that make $O(n)$ algorithms possible: inverses of tridiagonal, quasiseparable and
diagonal-plus-semiseparable matrices, the LU and QR factorizations of semiseparable matrices, and
the product form and the odd–even factorization of an orthogonal upper Hessenberg matrix. The
statements about inverses all come from the nullity theorem `Matrix.rank_toBlock_inv_add_card`.

The central objects are the unit upper bidiagonal matrix $B(r)$, with $1$ on the diagonal and $-r_i$
at $(i, i + 1)$, and the quasiseparable representation $\mathbf{S}(u, v, t, d, p, q, r)$ of
[golub2013matrix] (12.2.8), with the entries
$$a_{ij} = \begin{cases} u_i \, t_j \cdots t_{i-1} \, v_j & i > j, \\ d_i & i = j, \\
  p_i \, r_i \cdots r_{j-1} \, q_j & i < j. \end{cases}$$
The source claims in §12.2.3 that every quasiseparable matrix has such a representation. This is
false: for $n \ge 3$ and $r_0, r_1 \neq 0$, the matrix $B(r)$ is quasiseparable but has none
(`Matrix.unitBidiagonal_ne_quasiseparableOf`). The representation
$\widetilde{\mathbf{S}}(u, v, t, d, p, q, r)$ of Eidelman and Gohberg, with one transfer factor
fewer, represents every quasiseparable matrix (`Matrix.exists_quasiseparableRep`).

## Main definitions

* `Matrix.IsSemiseparable`: every block on or below the diagonal and every block on or above it has
  rank at most one ([golub2013matrix] (12.2.1)).
* `Matrix.IsQuasiseparable`: every block strictly below or strictly above the diagonal has rank at
  most one ([golub2013matrix] (12.2.5)).
* `Matrix.unitBidiagonal`: the unit upper bidiagonal matrix $B(r)$ of (12.2.2).
* `Matrix.quasiseparableOf`: the quasiseparable representation $\mathbf{S}(u, v, t, d, p, q, r)$ of
  (12.2.8).
* `Matrix.quasiseparableRep`: the corrected representation
  $\widetilde{\mathbf{S}}(u, v, t, d, p, q, r)$, with the transfer factors strictly between the row
  and the column.
* `Matrix.IsGeneratorRepresentableOfOrder`: the $\{p, q\}$-generator representable matrices of
  §12.2.8.
* `Matrix.givensFactor`, `Matrix.givensChain`: the product $G_0 G_1 \cdots G_{N-1}$ of $2 \times 2$
  blocks embedded in consecutive coordinate planes ((12.2.4), (12.2.12)).
* `Matrix.reflectorFactor`: the factors of the product form (12.2.18) of an orthogonal upper
  Hessenberg matrix.
* `Matrix.oddEvenHalfSum`, `Matrix.oddEvenHalfDiff`: the matrices $C = (H_o + H_e)/2$ and
  $S = (H_o - H_e)/2$ of Fact 2 of §12.2.10.

## Main results

* `Matrix.isSemiseparable_iff_forall_rank_toBlock_Icc_le`,
  `Matrix.isQuasiseparable_iff_forall_rank_toBlock_Icc_le`: the formulations of the source by index
  intervals.
* `Matrix.inv_unitBidiagonal`, `Matrix.isSemiseparable_inv_unitBidiagonal`: the entries (12.2.3) of
  $B(r)^{-1}$, which is semiseparable.
* `Matrix.quasiseparableOf_eq`, `Matrix.isQuasiseparable_quasiseparableOf`,
  `Matrix.isSemiseparable_quasiseparableOf`, `Matrix.transpose_quasiseparableOf`: the representation
  (12.2.8) in terms of $B(t)$ and $B(r)$, its class, and its transpose.
* `Matrix.IsTridiagonal.isSemiseparable_inv`, `Matrix.IsTridiagonal.inv_eq_generatorRep`: Fact 1 of
  §12.2.3, the inverse of a tridiagonal matrix is semiseparable, and generator representable when
  the off-diagonal entries are nonzero.
* `Matrix.IsQuasiseparable.inv`: Fact 2 of §12.2.3, the inverse of a quasiseparable matrix is
  quasiseparable.
* `Matrix.inv_diagonal_add_eq_add`: Fact 3 of §12.2.3, the inverse of a diagonal-plus-semiseparable
  matrix is diagonal-plus-semiseparable.
* `Matrix.IsGeneratorRepresentableOfOrder.hasBandwidth_inv`: the inverse of a $\{p, q\}$-generator
  representable matrix has lower bandwidth $p$ and upper bandwidth $q$ (§12.2.8).
* `Matrix.isLU_quasiseparableOf`: the closed-form LU factorization of a semiseparable matrix, the
  content of [golub2013matrix] Algorithm 12.2.1.
* `Matrix.IsLU.isSemiseparable_upper`, `Matrix.IsLU.isSemiseparable_lower`: the LU factors of a
  semiseparable matrix are semiseparable (§12.2.5).
* `Matrix.unitBidiagonal_ne_quasiseparableOf`, `Matrix.exists_quasiseparableRep`: $B(r)$ has no
  representation (12.2.8), and every quasiseparable matrix has a corrected representation.
* `Matrix.exists_lower_semiseparable_rep`, `Matrix.exists_upper_semiseparable_rep`: triangular
  semiseparable matrices have representations (12.2.8) (§12.2.4).
* `Matrix.givensChain_apply`, `Matrix.givensChain_isUpperHessenberg`,
  `Matrix.givensChain_isQuasiseparable`: the entries (12.2.4) of a chain of $2 \times 2$ blocks in
  consecutive planes, which is upper Hessenberg and quasiseparable.
* `Matrix.exists_givensVector_rep`, `Matrix.givensChain_mul_strictLower_add_diagPart`: the
  Givens-vector representation (12.2.11) of a lower triangular semiseparable matrix, and its QR
  factorization (12.2.14).
* `Matrix.orthogonalHessenberg_isQuasiseparable`,
  `Matrix.exists_orthogonalHessenberg_eq_prod_planeReflector`: an orthogonal upper Hessenberg matrix
  is quasiseparable and has the product form (12.2.18).
* `Matrix.prodFwd_reflectorFactor_mem_orthogonalGroup`, `Matrix.det_prodFwd_reflectorFactor`,
  `Matrix.prodFwd_reflectorFactor_mem_specialOrthogonalGroup`: the product (12.2.18) is orthogonal
  with determinant $(-1)^{N+1}$.
* `Matrix.isSimilar_prodFwd_evenOdd`, `Matrix.isSimilar_prod_planeReflector_oddEven`: a product of
  the generators of a path is similar to the product of its even-indexed factors times the product
  of its odd-indexed factors, which gives Fact 1 of §12.2.10.
* `Matrix.isTridiagonal_oddEvenHalfSum`, `Matrix.isTridiagonal_oddEvenHalfDiff`,
  `Matrix.charpoly_oddEven_half_sum`: Fact 2 of §12.2.10, $C$ and $S$ are symmetric tridiagonal with
  the eigenvalues $\pm \cos(\theta_k/2)$ and $\pm \sin(\theta_k/2)$.

## Notation

* $B(r)$: the unit upper bidiagonal matrix `Matrix.unitBidiagonal n r`, and
  $B(r)^{-T} = (B(r)^{-1})^T$.
* $\mathbf{S}(u, v, t, d, p, q, r)$: `Matrix.quasiseparableOf u v t d p q r`.
* $\widetilde{\mathbf{S}}(u, v, t, d, p, q, r)$: `Matrix.quasiseparableRep u v t d p q r`.
* $X \circ Y$: the Hadamard (entrywise) product `X ⊙ Y`, written `X .* Y` in the source; $u \circ v$
  is also the entrywise product of two vectors.
* $\operatorname{tril}(X, -1)$ and $\operatorname{triu}(X, 1)$: the strictly lower and strictly
  upper parts `Matrix.strictLower X` and `Matrix.strictUpper X`.
* $A[\{i \ge k\}, \{j \le k\}]$: the block of $A$ on the rows $i \ge k$ and the columns $j \le k$,
  `A.toBlock (k ≤ ·) (· ≤ k)`.

## Implementation notes

* The predicates are stated through the *maximal* blocks $A[\{i \ge k\}, \{j \le k\}]$ and
  $A[\{i \le k\}, \{j \ge k\}]$, with strict inequalities $i > k$ and $j > k$ in the quasiseparable
  case. Every block of the form in the source is a sub-block of one of them, and the nullity theorem
  speaks about the maximal blocks.
* Index arithmetic is on `Fin n`, with indices starting at $0$. The vectors $t$ and $r$ of length
  $n - 1$ in the source are sequences `ℕ → K`, and the products $t_j \cdots t_{i-1}$ run over
  `Finset.Ico j i`.
* The $2 \times 2$ reflections `Matrix.planeReflector φ` of §12.2.10 are in
  `Numlib.LinearAlgebra.Matrix.PlaneRotation`. The products are `prodFwd`, `prodFwdEven` and
  `prodFwdOdd` of `Numlib.LinearAlgebra.Matrix.Products`.
-/

open Finset

namespace Matrix

variable {K : Type*} [Field K]

/-! ### The two classes -/

section Classes

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- Let $K$ be a field and $A$ a square matrix over $K$ whose index set $n$ is finite and totally
ordered. The matrix $A$ is **semiseparable** if for every index $k$ the two blocks
$$A[\{i \ge k\}, \{j \le k\}] \quad \text{and} \quad A[\{i \le k\}, \{j \ge k\}]$$
have rank at most one.

These are the maximal blocks that do not cross the diagonal. The condition (12.2.1) of
[golub2013matrix], that every such block has rank at most one, is equivalent
(`Matrix.isSemiseparable_iff_forall_rank_toBlock_Icc_le`). -/
def IsSemiseparable (A : Matrix n n K) : Prop :=
  ∀ k, (A.toBlock (k ≤ ·) (· ≤ k)).rank ≤ 1 ∧ (A.toBlock (· ≤ k) (k ≤ ·)).rank ≤ 1

/-- Let $K$ be a field and $A$ a square matrix over $K$ whose index set $n$ is finite and totally
ordered. The matrix $A$ is **quasiseparable** if for every index $k$ the two blocks
$$A[\{i > k\}, \{j \le k\}] \quad \text{and} \quad A[\{i \le k\}, \{j > k\}]$$
have rank at most one.

These are the maximal blocks strictly below and strictly above the diagonal. The condition
(12.2.5) of [golub2013matrix], that every such block has rank at most one, is equivalent
(`Matrix.isQuasiseparable_iff_forall_rank_toBlock_Icc_le`). -/
def IsQuasiseparable (A : Matrix n n K) : Prop :=
  ∀ k, (A.toBlock (k < ·) (· ≤ k)).rank ≤ 1 ∧ (A.toBlock (· ≤ k) (k < ·)).rank ≤ 1

omit [Fintype n] in
private theorem exists_top_bot [Finite n] (k : n) : ∃ t b : n, ∀ i, i ≤ t ∧ b ≤ i := by
  have : Nonempty n := ⟨k⟩
  obtain ⟨t, ht⟩ := Finite.exists_max (id : n → n)
  obtain ⟨b, hb⟩ := Finite.exists_min (id : n → n)
  exact ⟨t, b, fun i => ⟨ht i, hb i⟩⟩

/-- A square matrix $A$ over $K$ is semiseparable if and only if every block
$A(i_1{:}i_2, j_1{:}j_2)$ with $j_2 \le i_1$ or $i_2 \le j_1$ has rank at most one. This is the
formulation (12.2.1) of [golub2013matrix].

The block $A(i_1{:}i_2, j_1{:}j_2)$ consists of the rows $i$ with $i_1 \le i \le i_2$ and the
columns $j$ with $j_1 \le j \le j_2$. -/
theorem isSemiseparable_iff_forall_rank_toBlock_Icc_le {A : Matrix n n K} :
    A.IsSemiseparable ↔ ∀ i₁ i₂ j₁ j₂ : n, j₂ ≤ i₁ ∨ i₂ ≤ j₁ →
      (A.toBlock (· ∈ Set.Icc i₁ i₂) (· ∈ Set.Icc j₁ j₂)).rank ≤ 1 := by
  refine ⟨fun h i₁ i₂ j₁ j₂ hc => ?_, fun h k => ?_⟩
  · rcases hc with hc | hc
    · exact (rank_toBlock_mono A (fun i hi => hi.1) fun j hj => hj.2.trans hc).trans (h i₁).1
    · exact (rank_toBlock_mono A (fun i hi => hi.2.trans hc) fun j hj => hj.1).trans (h j₁).2
  · obtain ⟨t, b, htb⟩ := exists_top_bot k
    exact ⟨(rank_toBlock_mono A (fun i hi => ⟨hi, (htb i).1⟩) fun j hj => ⟨(htb j).2, hj⟩).trans
        (h k t b k (Or.inl le_rfl)),
      (rank_toBlock_mono A (fun i hi => ⟨(htb i).2, hi⟩) fun j hj => ⟨hj, (htb j).1⟩).trans
        (h b k k t (Or.inr le_rfl))⟩

/-- A square matrix $A$ over $K$ is quasiseparable if and only if every block
$A(i_1{:}i_2, j_1{:}j_2)$ with $j_2 < i_1$ or $i_2 < j_1$ has rank at most one. This is the
formulation (12.2.5) of [golub2013matrix].

The block $A(i_1{:}i_2, j_1{:}j_2)$ consists of the rows $i$ with $i_1 \le i \le i_2$ and the
columns $j$ with $j_1 \le j \le j_2$. -/
theorem isQuasiseparable_iff_forall_rank_toBlock_Icc_le {A : Matrix n n K} :
    A.IsQuasiseparable ↔ ∀ i₁ i₂ j₁ j₂ : n, j₂ < i₁ ∨ i₂ < j₁ →
      (A.toBlock (· ∈ Set.Icc i₁ i₂) (· ∈ Set.Icc j₁ j₂)).rank ≤ 1 := by
  refine ⟨fun h i₁ i₂ j₁ j₂ hc => ?_, fun h k => ?_⟩
  · rcases hc with hc | hc
    · exact (rank_toBlock_mono A (fun i hi => hc.trans_le hi.1) fun j hj => hj.2).trans (h j₂).1
    · exact (rank_toBlock_mono A (fun i hi => hi.2) fun j hj => hc.trans_le hj.1).trans (h i₂).2
  obtain ⟨t, b, htb⟩ := exists_top_bot k
  constructor
  · by_cases hne : (univ.filter (k < ·)).Nonempty
    · refine (rank_toBlock_mono A (p' := (· ∈ Set.Icc ((univ.filter (k < ·)).min' hne) t))
        (q' := (· ∈ Set.Icc b k)) (fun i hi => ⟨min'_le _ i (by simpa using hi), (htb i).1⟩)
        fun j hj => ⟨(htb j).2, hj⟩).trans (h _ _ _ _ (Or.inl ?_))
      simp
    · refine (rank_le_card_height _).trans (le_of_eq_of_le ?_ zero_le_one)
      simp only [Fintype.card_eq_zero_iff]
      exact ⟨fun i => hne ⟨i, by simpa using i.2⟩⟩
  · by_cases hne : (univ.filter (k < ·)).Nonempty
    · refine (rank_toBlock_mono A (p' := (· ∈ Set.Icc b k))
        (q' := (· ∈ Set.Icc ((univ.filter (k < ·)).min' hne) t)) (fun i hi => ⟨(htb i).2, hi⟩)
        fun j hj => ⟨min'_le _ j (by simpa using hj), (htb j).1⟩).trans (h _ _ _ _ (Or.inr ?_))
      simp
    · refine (rank_le_card_width _).trans (le_of_eq_of_le ?_ zero_le_one)
      simp only [Fintype.card_eq_zero_iff]
      exact ⟨fun j => hne ⟨j, by simpa using j.2⟩⟩

/-- Every semiseparable matrix is quasiseparable, as noted in [golub2013matrix] §12.2.2.

A block strictly below the diagonal is a sub-block of a maximal block that includes the
diagonal. -/
theorem IsSemiseparable.isQuasiseparable {A : Matrix n n K} (h : A.IsSemiseparable) :
    A.IsQuasiseparable := fun k =>
  ⟨(rank_toBlock_mono A (fun _ hi => le_of_lt hi) fun _ hj => hj).trans (h k).1,
    (rank_toBlock_mono A (fun _ hi => hi) fun _ hj => le_of_lt hj).trans (h k).2⟩

/-- If $A$ is semiseparable, then $A^T$ is semiseparable. -/
theorem IsSemiseparable.transpose {A : Matrix n n K} (h : A.IsSemiseparable) :
    Aᵀ.IsSemiseparable := fun k => by
  rw [rank_toBlock_transpose, rank_toBlock_transpose]
  exact (h k).symm

/-- If $A$ is quasiseparable, then $A^T$ is quasiseparable. -/
theorem IsQuasiseparable.transpose {A : Matrix n n K} (h : A.IsQuasiseparable) :
    Aᵀ.IsQuasiseparable := fun k => by
  rw [rank_toBlock_transpose, rank_toBlock_transpose]
  exact (h k).symm

/-- Scaling the rows and the columns of a matrix does not increase the rank of any of its blocks. -/
private theorem rank_toBlock_diagonal_mul_mul_diagonal_le (A : Matrix n n K) (a b : n → K)
    (p q : n → Prop) [DecidablePred q] :
    ((diagonal a * A * diagonal b).toBlock p q).rank ≤ (A.toBlock p q).rank := by
  classical
  have : (diagonal a * A * diagonal b).toBlock p q =
      diagonal (fun i : {i // p i} => a i) * A.toBlock p q *
        diagonal (fun j : {j // q j} => b j) := by
    ext i j
    simp [toBlock_apply]
  rw [this]
  exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

/-- If $A$ is semiseparable and $a, b \in K^n$, then $\operatorname{diag}(a) \, A
\operatorname{diag}(b)$ is semiseparable. -/
theorem IsSemiseparable.diagonal_mul_mul_diagonal {A : Matrix n n K} (h : A.IsSemiseparable)
    (a b : n → K) : (diagonal a * A * diagonal b).IsSemiseparable := fun k =>
  ⟨(rank_toBlock_diagonal_mul_mul_diagonal_le A a b _ _).trans (h k).1,
    (rank_toBlock_diagonal_mul_mul_diagonal_le A a b _ _).trans (h k).2⟩

/-- If $A$ is quasiseparable and $a, b \in K^n$, then $\operatorname{diag}(a) \, A
\operatorname{diag}(b)$ is quasiseparable. -/
theorem IsQuasiseparable.diagonal_mul_mul_diagonal {A : Matrix n n K} (h : A.IsQuasiseparable)
    (a b : n → K) : (diagonal a * A * diagonal b).IsQuasiseparable := fun k =>
  ⟨(rank_toBlock_diagonal_mul_mul_diagonal_le A a b _ _).trans (h k).1,
    (rank_toBlock_diagonal_mul_mul_diagonal_le A a b _ _).trans (h k).2⟩

/-- If $A$ is quasiseparable and $d \in K^n$, then $A + \operatorname{diag}(d)$ is quasiseparable,
because the blocks strictly below and strictly above the diagonal contain no diagonal entry. -/
theorem IsQuasiseparable.add_diagonal {A : Matrix n n K} (h : A.IsQuasiseparable) (d : n → K) :
    (A + diagonal d).IsQuasiseparable := fun k => by
  have h₁ : (A + diagonal d).toBlock (k < ·) (· ≤ k) = A.toBlock (k < ·) (· ≤ k) := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp [toBlock_apply, diagonal_apply_ne d (ne_of_gt (lt_of_le_of_lt hj hi))]
  have h₂ : (A + diagonal d).toBlock (· ≤ k) (k < ·) = A.toBlock (· ≤ k) (k < ·) := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp [toBlock_apply, diagonal_apply_ne d (ne_of_lt (lt_of_le_of_lt hi hj))]
  rw [h₁, h₂]
  exact h k

omit [LinearOrder n] in
/-- The rank of a block of a Hadamard product $A \circ B$ is at most the product of the ranks of the
corresponding blocks of $A$ and $B$. -/
private theorem rank_toBlock_hadamard_le (A B : Matrix n n K) (p q : n → Prop) [DecidablePred q] :
    ((A ⊙ B).toBlock p q).rank ≤ (A.toBlock p q).rank * (B.toBlock p q).rank :=
  rank_hadamard_le (A.toBlock p q) (B.toBlock p q)

/-- If $A$ and $B$ are quasiseparable, then their Hadamard product $A \circ B$ is quasiseparable.
This is (12.2.7) of [golub2013matrix].

On each block, $\operatorname{rank}(X \circ Y) \le \operatorname{rank} X \cdot
\operatorname{rank} Y$. -/
theorem IsQuasiseparable.hadamard {A B : Matrix n n K} (hA : A.IsQuasiseparable)
    (hB : B.IsQuasiseparable) : (A ⊙ B).IsQuasiseparable := fun k =>
  ⟨(rank_toBlock_hadamard_le A B _ _).trans (mul_le_one' (hA k).1 (hB k).1),
    (rank_toBlock_hadamard_le A B _ _).trans (mul_le_one' (hA k).2 (hB k).2)⟩

/-- If $A$ and $B$ are semiseparable, then their Hadamard product $A \circ B$ is semiseparable. -/
theorem IsSemiseparable.hadamard {A B : Matrix n n K} (hA : A.IsSemiseparable)
    (hB : B.IsSemiseparable) : (A ⊙ B).IsSemiseparable := fun k =>
  ⟨(rank_toBlock_hadamard_le A B _ _).trans (mul_le_one' (hA k).1 (hB k).1),
    (rank_toBlock_hadamard_le A B _ _).trans (mul_le_one' (hA k).2 (hB k).2)⟩

end Classes

/-! ### The unit bidiagonal matrix $B(r)$ and its inverse -/

section UnitBidiagonal

variable {n : ℕ}

/-- Let $r = (r_0, r_1, \dots)$ be a sequence in $K$. The **unit upper bidiagonal matrix**
$B(r) \in K^{n \times n}$ of [golub2013matrix] (12.2.2) has the entries
$$B(r)_{ij} = \begin{cases} 1 & i = j, \\ -r_i & j = i + 1, \\
  0 & \text{otherwise}. \end{cases}$$

Indices start at $0$. The vector $r \in K^{n-1}$ of the source is a sequence `ℕ → K`, of which
only $r_0, \dots, r_{n-2}$ enter. -/
def unitBidiagonal (n : ℕ) (r : ℕ → K) : Matrix (Fin n) (Fin n) K :=
  of fun i j => if i = j then 1 else if (j : ℕ) = i + 1 then -r i else 0

/-- The entries of $B(r)$ are $1$ on the diagonal, $-r_i$ at $(i, i + 1)$, and $0$ elsewhere. -/
theorem unitBidiagonal_apply (r : ℕ → K) (i j : Fin n) :
    unitBidiagonal n r i j = if i = j then 1 else if (j : ℕ) = i + 1 then -r i else 0 :=
  rfl

/-- $B(r) = I - N(r)$, where $N(r)$ has $r_i$ at $(i, i + 1)$ and zeros elsewhere. -/
private theorem unitBidiagonal_eq_one_sub (r : ℕ → K) :
    unitBidiagonal n r = 1 - of fun i j : Fin n => if (j : ℕ) = i + 1 then r i else 0 := by
  ext i j
  rw [unitBidiagonal_apply, Matrix.sub_apply, of_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [one_apply_ne hij]
    simp only [hij, ite_false]
    split_ifs <;> simp

/-- $B(r)$ times the upper triangular matrix with the entries $r_i r_{i+1} \cdots r_{j-1}$ for
$i \le j$ is the identity. -/
private theorem unitBidiagonal_mul_prod (r : ℕ → K) :
    unitBidiagonal n r *
      (of fun (i j : Fin n) => if i ≤ j then ∏ l ∈ Finset.Ico (i : ℕ) j, r l else 0) = 1 := by
  rw [unitBidiagonal_eq_one_sub, Matrix.sub_mul, Matrix.one_mul]
  ext i j
  rw [Matrix.sub_apply, Matrix.mul_apply]
  simp_rw [of_apply, ite_mul, zero_mul]
  have hs := sum_dite_val_eq_add_one i fun k (_ : (k : ℕ) = i + 1) =>
    r i * if k ≤ j then ∏ l ∈ Finset.Ico (k : ℕ) j, r l else 0
  simp only [dite_eq_ite] at hs
  rw [hs]
  rcases lt_trichotomy (i : ℕ) j with h | h | h
  · have h1 : (i : ℕ) + 1 < n := by omega
    have hij : i ≤ j := Fin.le_def.2 h.le
    have h2 : (⟨i + 1, h1⟩ : Fin n) ≤ j := Fin.le_def.2 (by simp; omega)
    rw [one_apply_ne (Fin.ne_of_lt (Fin.lt_def.2 h)), dite_eq_left h1]
    simp only [hij, h2, ite_true, Finset.prod_eq_prod_Ico_succ_bot h, sub_self]
  · have hij : i = j := Fin.ext h
    subst hij
    have h2 : ∀ h1 : (i : ℕ) + 1 < n, ¬ (⟨i + 1, h1⟩ : Fin n) ≤ i :=
      fun h1 h2 => by rw [Fin.le_def] at h2; simp at h2
    simp only [le_refl, ↓reduceIte, Finset.Ico_self, prod_empty, one_apply_eq]
    by_cases h1 : (i : ℕ) + 1 < n
    · rw [dite_eq_left h1, ite_eq_right (h2 h1), mul_zero, sub_zero]
    · rw [dite_eq_right h1, sub_zero]
  · have hij : ¬ i ≤ j := fun h' => by rw [Fin.le_def] at h'; omega
    have h2 : ∀ h1 : (i : ℕ) + 1 < n, ¬ (⟨i + 1, h1⟩ : Fin n) ≤ j :=
      fun h1 h2 => by rw [Fin.le_def] at h2; simp at h2; omega
    rw [one_apply_ne (fun e => hij (le_of_eq e)), ite_eq_right hij]
    by_cases h1 : (i : ℕ) + 1 < n
    · rw [dite_eq_left h1, ite_eq_right (h2 h1), mul_zero, sub_zero]
    · rw [dite_eq_right h1, sub_zero]

/-- For every sequence $r$ in $K$, the inverse of $B(r) \in K^{n \times n}$ is upper triangular with
the entries
$$\bigl(B(r)^{-1}\bigr)_{ij} = r_i r_{i+1} \cdots r_{j-1} \quad (i \le j),$$
and $0$ for $i > j$. This is (12.2.3) of [golub2013matrix].

The diagonal entries are the empty product $1$. -/
theorem inv_unitBidiagonal (r : ℕ → K) :
    (unitBidiagonal n r)⁻¹ =
      of fun (i j : Fin n) => if i ≤ j then ∏ l ∈ Finset.Ico (i : ℕ) j, r l else 0 :=
  inv_eq_right_inv (unitBidiagonal_mul_prod r)

/-- For every sequence $r$, $B(r) \, B(r)^{-1} = I$, so $B(r)$ is invertible. -/
theorem unitBidiagonal_mul_inv (r : ℕ → K) : unitBidiagonal n r * (unitBidiagonal n r)⁻¹ = 1 := by
  rw [inv_unitBidiagonal]
  exact unitBidiagonal_mul_prod r

/-- For every sequence $r$, the inverse $B(r)^{-1}$ is semiseparable. This is (12.2.3) and P12.2.1
of [golub2013matrix].

An upper maximal block of $B(r)^{-1}$ at $k$ is the outer product of the vectors
$(r_i \cdots r_{k-1})_{i \le k}$ and $(r_k \cdots r_{j-1})_{j \ge k}$, and a lower maximal block
has the single nonzero entry $1$. -/
theorem isSemiseparable_inv_unitBidiagonal (r : ℕ → K) :
    (unitBidiagonal n r)⁻¹.IsSemiseparable := by
  rw [inv_unitBidiagonal]
  intro k
  constructor
  · have : (of fun i j : Fin n => if i ≤ j then ∏ l ∈ Finset.Ico (i : ℕ) j, r l else 0).toBlock
        (k ≤ ·) (· ≤ k) = vecMulVec (fun i : {i // k ≤ i} => if (i : Fin n) = k then (1 : K) else 0)
          (fun j : {j // j ≤ k} => if (j : Fin n) = k then (1 : K) else 0) := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [toBlock_apply, of_apply, vecMulVec_apply]
      by_cases hij : i ≤ j
      · obtain rfl : i = k := le_antisymm (hij.trans hj) hi
        obtain rfl : j = i := le_antisymm hj hij
        simp
      · by_cases hik : i = k
        · subst hik
          simp [hij, show j ≠ i from fun e => hij (e ▸ le_rfl)]
        · simp [hij, hik]
    rw [this]
    exact rank_vecMulVec_le _ _
  · have : (of fun i j : Fin n => if i ≤ j then ∏ l ∈ Finset.Ico (i : ℕ) j, r l else 0).toBlock
        (· ≤ k) (k ≤ ·) = vecMulVec (fun i : {i // i ≤ k} => ∏ l ∈ Finset.Ico (i : ℕ) k, r l)
          (fun j : {j // k ≤ j} => ∏ l ∈ Finset.Ico (k : ℕ) j, r l) := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [toBlock_apply, of_apply, vecMulVec_apply, hi.trans hj, ite_true]
      exact (prod_Ico_consecutive r (Fin.le_def.1 hi) (Fin.le_def.1 hj)).symm
    rw [this]
    exact rank_vecMulVec_le _ _

/-- **$B(r)^T$ introduces zeros into a vector.** Let $x \in K^{n+1}$ with $x_l \neq 0$ for $l < n$,
and let $r_l = x_{l+1} / x_l$ for $l < n$. Then, for $B(r) \in K^{(n+1) \times (n+1)}$,
$$B(r)^T x = x_0 \, e_0,$$
where $e_0$ is the first unit vector. This is the use of $B(r)$ in [golub2013matrix] §12.2.1. -/
theorem unitBidiagonal_transpose_mulVec_eq_single {x : Fin (n + 1) → K} {r : ℕ → K}
    (hx : ∀ l (h : l < n), x ⟨l, by omega⟩ ≠ 0)
    (hr : ∀ l (h : l < n), r l = x ⟨l + 1, by omega⟩ / x ⟨l, by omega⟩) :
    (unitBidiagonal (n + 1) r)ᵀ *ᵥ x = Pi.single 0 (x 0) := by
  ext j
  rw [unitBidiagonal_eq_one_sub, transpose_sub, transpose_one, sub_mulVec, one_mulVec,
    Pi.sub_apply, mulVec, dotProduct]
  simp_rw [transpose_apply, of_apply, ite_mul, zero_mul]
  induction j using Fin.cases with
  | zero => simp
  | succ l =>
    rw [Finset.sum_eq_single l.castSucc
      (fun k _ hk => ite_eq_right_iff.2 fun e => absurd (Fin.ext (by simp at e ⊢; omega)) hk)
      (fun h => absurd (mem_univ _) h)]
    have hne : x l.castSucc ≠ 0 := hx l l.2
    have hrl : r l = x l.succ / x l.castSucc := hr l l.2
    simp only [Fin.val_succ, Fin.val_castSucc, ↓reduceIte,
      Pi.single_eq_of_ne (Fin.succ_ne_zero l)]
    rw [hrl, div_mul_cancel₀ _ hne, sub_self]

end UnitBidiagonal

/-! ### The quasiseparable representation $\mathbf{S}(u, v, t, d, p, q, r)$ -/

section Representation

variable {n : ℕ}

/-- Let $u, v, d, p, q \in K^n$, and let $t$ and $r$ be sequences in $K$. The **quasiseparable
representation** $\widetilde{\mathbf{S}}(u, v, t, d, p, q, r)$, with the transfer factors
strictly between the row and the column, is the matrix with the entries
$$a_{ij} = \begin{cases} u_i \, t_{j+1} \cdots t_{i-1} \, v_j & i > j, \\ d_i & i = j, \\
  p_i \, r_{i+1} \cdots r_{j-1} \, q_j & i < j. \end{cases}$$
This is the representation of Eidelman and Gohberg (1999), as in Vandebril, Van Barel and
Mastronardi (2008).

It has one transfer factor fewer than the representation $\mathbf{S}(u, v, t, d, p, q, r)$ of
[golub2013matrix] (12.2.8) (`Matrix.quasiseparableOf`). This lets it represent every
quasiseparable matrix (`Matrix.exists_quasiseparableRep`), $B(r)$ included. -/
def quasiseparableRep (u v : Fin n → K) (t : ℕ → K) (d p q : Fin n → K) (r : ℕ → K) :
    Matrix (Fin n) (Fin n) K :=
  of fun i j => if j < i then u i * (∏ l ∈ Finset.Ico ((j : ℕ) + 1) i, t l) * v j
    else if i = j then d i else p i * (∏ l ∈ Finset.Ico ((i : ℕ) + 1) j, r l) * q j

/-- The entries of $\widetilde{\mathbf{S}}(u, v, t, d, p, q, r)$ are
$u_i t_{j+1} \cdots t_{i-1} v_j$ below the diagonal, $d_i$ on it, and
$p_i r_{i+1} \cdots r_{j-1} q_j$ above it. -/
theorem quasiseparableRep_apply (u v : Fin n → K) (t : ℕ → K) (d p q : Fin n → K) (r : ℕ → K)
    (i j : Fin n) :
    quasiseparableRep u v t d p q r i j =
      if j < i then u i * (∏ l ∈ Finset.Ico ((j : ℕ) + 1) i, t l) * v j
      else if i = j then d i else p i * (∏ l ∈ Finset.Ico ((i : ℕ) + 1) j, r l) * q j :=
  rfl

/-- For all $u, v, d, p, q \in K^n$ and sequences $t$, $r$, transposition exchanges the lower and
the upper generators of the representation:
$$\widetilde{\mathbf{S}}(u, v, t, d, p, q, r)^T = \widetilde{\mathbf{S}}(q, p, r, d, v, u, t).$$
-/
theorem transpose_quasiseparableRep (u v : Fin n → K) (t : ℕ → K) (d p q : Fin n → K)
    (r : ℕ → K) : (quasiseparableRep u v t d p q r)ᵀ = quasiseparableRep q p r d v u t := by
  ext i j
  simp only [transpose_apply, quasiseparableRep_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, lt_asymm h, h.ne]
    ring
  · simp
  · simp [h, lt_asymm h, h.ne]
    ring

/-- For all $u, v, d, p, q \in K^n$ and sequences $t$, $r$, the matrix
$\widetilde{\mathbf{S}}(u, v, t, d, p, q, r)$ is quasiseparable.

The strictly lower maximal block at $k$ is the outer product of the vectors
$(u_i t_{k+1} \cdots t_{i-1})_{i > k}$ and $(t_{j+1} \cdots t_k v_j)_{j \le k}$, and the
strictly upper ones are similar. -/
theorem isQuasiseparable_quasiseparableRep (u v : Fin n → K) (t : ℕ → K) (d p q : Fin n → K)
    (r : ℕ → K) : (quasiseparableRep u v t d p q r).IsQuasiseparable := by
  intro k
  constructor
  · have : (quasiseparableRep u v t d p q r).toBlock (k < ·) (· ≤ k) =
        vecMulVec (fun i : {i // k < i} => u i * ∏ l ∈ Finset.Ico ((k : ℕ) + 1) i, t l)
          (fun j : {j // j ≤ k} => (∏ l ∈ Finset.Ico ((j : ℕ) + 1) ((k : ℕ) + 1), t l) * v j) := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      have hji : j < i := lt_of_le_of_lt hj hi
      simp only [toBlock_apply, quasiseparableRep_apply, vecMulVec_apply, hji, ↓reduceIte]
      rw [← prod_Ico_consecutive t (Nat.succ_le_succ (Fin.le_def.1 hj))
        (Nat.succ_le_of_lt (Fin.lt_def.1 hi))]
      ring
    rw [this]
    exact rank_vecMulVec_le _ _
  · have : (quasiseparableRep u v t d p q r).toBlock (· ≤ k) (k < ·) =
        vecMulVec (fun i : {i // i ≤ k} => p i * ∏ l ∈ Finset.Ico ((i : ℕ) + 1) ((k : ℕ) + 1), r l)
          (fun j : {j // k < j} => (∏ l ∈ Finset.Ico ((k : ℕ) + 1) j, r l) * q j) := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      have hij : i < j := lt_of_le_of_lt hi hj
      simp only [toBlock_apply, quasiseparableRep_apply, vecMulVec_apply, lt_asymm hij, hij.ne,
        ↓reduceIte]
      rw [← prod_Ico_consecutive r (Nat.succ_le_succ (Fin.le_def.1 hi))
        (Nat.succ_le_of_lt (Fin.lt_def.1 hj))]
      ring
    rw [this]
    exact rank_vecMulVec_le _ _

/-- Let $u, v, d, p, q \in K^n$, and let $t$ and $r$ be sequences in $K$. The **quasiseparable
representation** $\mathbf{S}(u, v, t, d, p, q, r)$ of [golub2013matrix] (12.2.8) is the matrix
with the entries
$$a_{ij} = \begin{cases} u_i \, t_j \cdots t_{i-1} \, v_j & i > j, \\ d_i & i = j, \\
  p_i \, r_i \cdots r_{j-1} \, q_j & i < j. \end{cases}$$
Equivalently, $\mathbf{S}(u, v, t, d, p, q, r) = \operatorname{tril}(uv^T, -1) \circ B(t)^{-T} +
\operatorname{diag}(d) + \operatorname{triu}(pq^T, 1) \circ B(r)^{-1}$
(`Matrix.quasiseparableOf_eq`).

Not every quasiseparable matrix has this form (`Matrix.unitBidiagonal_ne_quasiseparableOf`). The
representation `Matrix.quasiseparableRep` corrects this. -/
def quasiseparableOf (u v : Fin n → K) (t : ℕ → K) (d p q : Fin n → K) (r : ℕ → K) :
    Matrix (Fin n) (Fin n) K :=
  of fun i j => if j < i then u i * (∏ l ∈ Finset.Ico (j : ℕ) i, t l) * v j
    else if i = j then d i else p i * (∏ l ∈ Finset.Ico (i : ℕ) j, r l) * q j

/-- The entries of $\mathbf{S}(u, v, t, d, p, q, r)$ are $u_i t_j \cdots t_{i-1} v_j$ below the
diagonal, $d_i$ on it, and $p_i r_i \cdots r_{j-1} q_j$ above it. -/
theorem quasiseparableOf_apply (u v : Fin n → K) (t : ℕ → K) (d p q : Fin n → K) (r : ℕ → K)
    (i j : Fin n) :
    quasiseparableOf u v t d p q r i j =
      if j < i then u i * (∏ l ∈ Finset.Ico (j : ℕ) i, t l) * v j
      else if i = j then d i else p i * (∏ l ∈ Finset.Ico (i : ℕ) j, r l) * q j :=
  rfl

/-- For all $u, v, d, p, q \in K^n$ and sequences $t$, $r$,
$$\mathbf{S}(u, v, t, d, p, q, r) = \operatorname{tril}(uv^T, -1) \circ B(t)^{-T} +
  \operatorname{diag}(d) + \operatorname{triu}(pq^T, 1) \circ B(r)^{-1}.$$
This is the form in which [golub2013matrix] (12.2.8) writes the representation.

Here $\operatorname{tril}(X, -1)$ and $\operatorname{triu}(X, 1)$ are `Matrix.strictLower X` and
`Matrix.strictUpper X`, and $\circ$ is the Hadamard product. -/
theorem quasiseparableOf_eq (u v : Fin n → K) (t : ℕ → K) (d p q : Fin n → K) (r : ℕ → K) :
    quasiseparableOf u v t d p q r =
      strictLower (vecMulVec u v) ⊙ ((unitBidiagonal n t)⁻¹)ᵀ + diagonal d +
        strictUpper (vecMulVec p q) ⊙ (unitBidiagonal n r)⁻¹ := by
  rw [inv_unitBidiagonal, inv_unitBidiagonal]
  ext i j
  simp only [quasiseparableOf_apply, Matrix.add_apply, hadamard_apply, strictLower_apply,
    strictUpper_apply, transpose_apply, of_apply, diagonal_apply, vecMulVec_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, lt_asymm h, h.ne, h.le]
    ring
  · simp
  · simp [h, lt_asymm h, h.ne', h.le]
    ring

/-- With $t = r = (1, 1, \dots)$, the representation is the **generator representation** (12.2.6) of
[golub2013matrix]:
$$\mathbf{S}(u, v, 1, d, p, q, 1)
  = \operatorname{tril}(uv^T, -1) + \operatorname{diag}(d) + \operatorname{triu}(pq^T, 1).$$
-/
theorem quasiseparableOf_one_one (u v d p q : Fin n → K) :
    quasiseparableOf u v 1 d p q 1 =
      strictLower (vecMulVec u v) + diagonal d + strictUpper (vecMulVec p q) := by
  ext i j
  simp only [quasiseparableOf_apply, Matrix.add_apply, strictLower_apply, strictUpper_apply,
    diagonal_apply, vecMulVec_apply, Pi.one_apply, prod_const_one, mul_one]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, lt_asymm h, h.ne]
  · simp
  · simp [h, lt_asymm h, h.ne']

/-- The representation (12.2.8) is the corrected representation with the first transfer factor
absorbed into the generators: $\mathbf{S}(u, v, t, d, p, q, r) = \widetilde{\mathbf{S}}(u, v',
t, d, p', q, r)$ with $v'_j = t_j v_j$ and $p'_i = p_i r_i$. -/
theorem quasiseparableOf_eq_quasiseparableRep (u v : Fin n → K) (t : ℕ → K) (d p q : Fin n → K)
    (r : ℕ → K) :
    quasiseparableOf u v t d p q r
      = quasiseparableRep u (fun j => t j * v j) t d (fun i => p i * r i) q r := by
  ext i j
  rw [quasiseparableOf_apply, quasiseparableRep_apply]
  split_ifs with h1 h2
  · rw [Finset.prod_eq_prod_Ico_succ_bot (Fin.lt_def.1 h1)]
    ring
  · rfl
  · have : i < j := lt_of_le_of_ne (not_lt.1 h1) h2
    rw [Finset.prod_eq_prod_Ico_succ_bot (Fin.lt_def.1 this)]
    ring

/-- For all $u, v, d, p, q \in K^n$ and sequences $t$, $r$, the matrix
$\mathbf{S}(u, v, t, d, p, q, r)$ is quasiseparable, as stated in [golub2013matrix] §12.2.3.

The proof goes through `Matrix.quasiseparableOf_eq_quasiseparableRep`. -/
theorem isQuasiseparable_quasiseparableOf (u v : Fin n → K) (t : ℕ → K) (d p q : Fin n → K)
    (r : ℕ → K) : (quasiseparableOf u v t d p q r).IsQuasiseparable := by
  rw [quasiseparableOf_eq_quasiseparableRep]
  exact isQuasiseparable_quasiseparableRep _ _ _ _ _ _ _

/-- Let $u, v, d, p, q \in K^n$ with $d_i = u_i v_i$ and $d_i = p_i q_i$ for all $i$, and let $t$
and $r$ be sequences. Then $\mathbf{S}(u, v, t, d, p, q, r)$ is semiseparable. This is stated in
[golub2013matrix] §12.2.3.

The diagonal entry $d_k = u_k v_k$ continues the rank-one pattern of the lower blocks, and
$d_k = p_k q_k$ that of the upper blocks. -/
theorem isSemiseparable_quasiseparableOf (u v : Fin n → K) (t : ℕ → K) (d p q : Fin n → K)
    (r : ℕ → K) (huv : d = u * v) (hpq : d = p * q) :
    (quasiseparableOf u v t d p q r).IsSemiseparable := by
  intro k
  constructor
  · have : (quasiseparableOf u v t d p q r).toBlock (k ≤ ·) (· ≤ k) =
        vecMulVec (fun i : {i // k ≤ i} => u i * ∏ l ∈ Finset.Ico (k : ℕ) i, t l)
          (fun j : {j // j ≤ k} => (∏ l ∈ Finset.Ico (j : ℕ) k, t l) * v j) := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [toBlock_apply, vecMulVec_apply]
      rcases (hj.trans hi).lt_or_eq with hji | hji
      · simp only [quasiseparableOf_apply, hji, ↓reduceIte]
        rw [← prod_Ico_consecutive t (Fin.le_def.1 hj) (Fin.le_def.1 hi)]
        ring
      · obtain rfl : j = i := hji
        obtain rfl : j = k := le_antisymm hj hi
        simp [quasiseparableOf_apply, huv]
    rw [this]
    exact rank_vecMulVec_le _ _
  · have : (quasiseparableOf u v t d p q r).toBlock (· ≤ k) (k ≤ ·) =
        vecMulVec (fun i : {i // i ≤ k} => p i * ∏ l ∈ Finset.Ico (i : ℕ) k, r l)
          (fun j : {j // k ≤ j} => (∏ l ∈ Finset.Ico (k : ℕ) j, r l) * q j) := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [toBlock_apply, vecMulVec_apply]
      rcases (hi.trans hj).lt_or_eq with hij | hij
      · simp only [quasiseparableOf_apply, lt_asymm hij, hij.ne, ↓reduceIte]
        rw [← prod_Ico_consecutive r (Fin.le_def.1 hi) (Fin.le_def.1 hj)]
        ring
      · obtain rfl : i = j := hij
        obtain rfl : i = k := le_antisymm hi hj
        simp [quasiseparableOf_apply, hpq]
    rw [this]
    exact rank_vecMulVec_le _ _

/-- For all $u, v, d, p, q \in K^n$ and sequences $t$, $r$,
$$\mathbf{S}(u, v, t, d, p, q, r)^T = \mathbf{S}(q, p, r, d, v, u, t).$$
This is stated in [golub2013matrix] §12.2.3.

In particular, the matrix is symmetric when $u = q$, $v = p$ and $t = r$. -/
theorem transpose_quasiseparableOf (u v : Fin n → K) (t : ℕ → K) (d p q : Fin n → K)
    (r : ℕ → K) : (quasiseparableOf u v t d p q r)ᵀ = quasiseparableOf q p r d v u t := by
  rw [quasiseparableOf_eq_quasiseparableRep, transpose_quasiseparableRep,
    quasiseparableOf_eq_quasiseparableRep]
  simp only [mul_comm]

/-- **Structured products.** For $p, q \in K^n$ and a sequence $r$,
$$(pq^T) \circ B(r)^{-1} = \operatorname{diag}(p) \, B(r)^{-1} \operatorname{diag}(q).$$
This is the product (12.2.9) of [golub2013matrix].

The source writes $\operatorname{triu}(pq^T) \circ B(r)^{-1}$. The $\operatorname{triu}$ is
redundant because $B(r)^{-1}$ is upper triangular, and the statement omits it. -/
theorem vecMulVec_hadamard_inv_unitBidiagonal (p q : Fin n → K) (r : ℕ → K) :
    vecMulVec p q ⊙ (unitBidiagonal n r)⁻¹ = diagonal p * (unitBidiagonal n r)⁻¹ * diagonal q := by
  ext i j
  simp only [hadamard_apply, vecMulVec_apply, diagonal_mul, mul_diagonal]
  ring

/-- For $p, q, x \in K^n$ and a sequence $r$, $\bigl((pq^T) \circ B(r)^{-1}\bigr) x = p \circ
\bigl(B(r)^{-1} (q \circ x)\bigr)$. This computes the matrix–vector product of (12.2.9) in
$O(n)$ operations. -/
theorem vecMulVec_hadamard_inv_unitBidiagonal_mulVec (p q : Fin n → K) (r : ℕ → K)
    (x : Fin n → K) :
    (vecMulVec p q ⊙ (unitBidiagonal n r)⁻¹) *ᵥ x = p * ((unitBidiagonal n r)⁻¹ *ᵥ (q * x)) := by
  have hd : ∀ w : Fin n → K, diagonal w *ᵥ x = w * x := fun w => funext (mulVec_diagonal w x)
  rw [vecMulVec_hadamard_inv_unitBidiagonal, ← mulVec_mulVec, ← mulVec_mulVec, hd]
  exact funext (mulVec_diagonal p _)

/-- Let $p, q \in K^n$ have nonzero entries and let $r$ be a sequence. If
$\bigl((pq^T) \circ B(r)^{-1}\bigr) x = y$, then $x = \bigl(B(r) (y / p)\bigr) / q$, with
entrywise division. This solves the system of (12.2.9) in $O(n)$ operations. -/
theorem eq_div_of_vecMulVec_hadamard_inv_unitBidiagonal_mulVec_eq {p q : Fin n → K} (r : ℕ → K)
    (hp : ∀ i, p i ≠ 0) (hq : ∀ i, q i ≠ 0) {x y : Fin n → K}
    (h : (vecMulVec p q ⊙ (unitBidiagonal n r)⁻¹) *ᵥ x = y) :
    x = (unitBidiagonal n r *ᵥ (y / p)) / q := by
  rw [vecMulVec_hadamard_inv_unitBidiagonal_mulVec] at h
  have hy : y / p = (unitBidiagonal n r)⁻¹ *ᵥ (q * x) := by
    ext i
    rw [← h, Pi.div_apply, Pi.mul_apply, mul_div_cancel_left₀ _ (hp i)]
  rw [hy, mulVec_mulVec, unitBidiagonal_mul_inv, one_mulVec]
  ext i
  rw [Pi.div_apply, Pi.mul_apply, mul_div_cancel_left₀ _ (hq i)]

end Representation

/-! ### Inverses, through the nullity theorem -/

section Inverse

section Order

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- For an index $k$, the number of indices $i \ge k$ plus the number of indices $j \le k$ is
$|n| + 1$. -/
private theorem card_le_add_card_le (k : n) :
    Fintype.card {i // k ≤ i} + Fintype.card {j // j ≤ k} = Fintype.card n + 1 := by
  rw [Fintype.card_subtype, Fintype.card_subtype, ← card_univ, ← card_singleton k,
    ← card_union_add_card_inter]
  congr 2
  · ext i
    simp [le_total]
  · ext i
    simp only [mem_inter, mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => h ▸ ⟨le_rfl, le_rfl⟩⟩

/-- For an index $k$, the number of indices $i > k$ plus the number of indices $j \le k$ is $|n|$.
-/
private theorem card_lt_add_card_le (k : n) :
    Fintype.card {i // k < i} + Fintype.card {j // j ≤ k} = Fintype.card n := by
  have e := card_filter_add_card_filter_not (s := (univ : Finset n)) (· ≤ k)
  simp only [not_le] at e
  rw [Fintype.card_subtype, Fintype.card_subtype, ← card_univ]
  omega

/-- If $A$ is invertible and tridiagonal, then every block $A^{-1}[\{i \ge k\}, \{j \le k\}]$ has
rank at most one. -/
private theorem rank_toBlock_inv_le_one_of_isTridiagonal {A : Matrix n n K} (hA : IsUnit A)
    (hT : A.IsTridiagonal) (k : n) : (A⁻¹.toBlock (k ≤ ·) (· ≤ k)).rank ≤ 1 := by
  have h := rank_toBlock_inv_add_card hA (k ≤ ·) (· ≤ k)
  beta_reduce at h
  have h0 : A.toBlock (fun i => ¬ i ≤ k) (fun j => ¬ k ≤ j) = 0 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    exact hT i j (Or.inl ⟨k, not_le.1 hj, not_le.1 hi⟩)
  rw [h0, rank_zero] at h
  have hc := card_le_add_card_le k
  omega

/-- Let $A$ be an invertible tridiagonal matrix over $K$ with finite, totally ordered indices. Then
$A^{-1}$ is semiseparable. This is the first half of Fact 1 in [golub2013matrix] §12.2.3.

By the nullity theorem (`Matrix.rank_toBlock_inv_add_card`), the lower maximal block of $A^{-1}$
at $k$ has rank $\operatorname{rank} A[\{i > k\}, \{j < k\}] + 1 = 1$, since that block of a
tridiagonal matrix is zero. The upper blocks follow by transposition. -/
theorem IsTridiagonal.isSemiseparable_inv {A : Matrix n n K} (hT : A.IsTridiagonal)
    (hA : IsUnit A) : A⁻¹.IsSemiseparable := by
  refine fun k => ⟨rank_toBlock_inv_le_one_of_isTridiagonal hA hT k, ?_⟩
  have := rank_toBlock_inv_le_one_of_isTridiagonal (A := Aᵀ) ((isUnit_transpose A).2 hA)
    (fun i j h => hT j i h.symm) k
  rwa [← transpose_nonsing_inv, rank_toBlock_transpose] at this

/-- If $A$ is invertible and $A[\{i > k\}, \{j \le k\}]$ has rank at most one, then
$A^{-1}[\{i > k\}, \{j \le k\}]$ has rank at most one. -/
private theorem rank_toBlock_inv_le_one_of_isQuasiseparable {A : Matrix n n K} (hA : IsUnit A)
    (k : n) (hq : (A.toBlock (k < ·) (· ≤ k)).rank ≤ 1) :
    (A⁻¹.toBlock (k < ·) (· ≤ k)).rank ≤ 1 := by
  have h := rank_toBlock_inv_add_card hA (k < ·) (· ≤ k)
  beta_reduce at h
  have h1 : (A.toBlock (fun i => ¬ i ≤ k) (fun j => ¬ k < j)).rank ≤ 1 :=
    (rank_toBlock_mono A (fun _ hi => not_le.1 hi) fun _ hj => not_lt.1 hj).trans hq
  have hc := card_lt_add_card_le k
  omega

/-- Let $A$ be an invertible quasiseparable matrix over $K$ with finite, totally ordered indices.
Then $A^{-1}$ is quasiseparable. This is Fact 2 in [golub2013matrix] §12.2.3.

By the nullity theorem, the complementary block of a strictly lower maximal block of $A^{-1}$ is
a strictly lower maximal block of $A$, of the same rank. -/
theorem IsQuasiseparable.inv {A : Matrix n n K} (h : A.IsQuasiseparable) (hA : IsUnit A) :
    A⁻¹.IsQuasiseparable := by
  refine fun k => ⟨rank_toBlock_inv_le_one_of_isQuasiseparable hA k (h k).1, ?_⟩
  have := rank_toBlock_inv_le_one_of_isQuasiseparable ((isUnit_transpose A).2 hA) k
    (h.transpose k).1
  rwa [← transpose_nonsing_inv, rank_toBlock_transpose] at this

/-- Let $H$ be an orthogonal upper Hessenberg matrix over $K$ with finite, totally ordered indices,
so $H^T H = H H^T = I$. Then $H$ is quasiseparable. [golub2013matrix] §12.2.10 uses this for the
product form (12.2.18).

A strictly lower maximal block of an upper Hessenberg matrix is supported on one column. A
strictly upper maximal block of $H$ is the transpose of a strictly lower block of
$H^{-1} = H^T$, which has the same rank as the corresponding block of $H$ by the nullity
theorem. -/
theorem orthogonalHessenberg_isQuasiseparable {H : Matrix n n K} (hH : H ∈ orthogonalGroup n K)
    (hHess : H.IsUpperHessenberg) : H.IsQuasiseparable := by
  have hlow : ∀ k, (H.toBlock (k < ·) (· ≤ k)).rank ≤ 1 := fun k => by
    have : H.toBlock (k < ·) (· ≤ k) = vecMulVec (fun i : {i // k < i} => H i k)
        (fun j : {j // j ≤ k} => if (j : n) = k then 1 else 0) := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [toBlock_apply, vecMulVec_apply]
      rcases hj.lt_or_eq with hj | rfl
      · simp [hj.ne, hHess i j ⟨k, hj, hi⟩]
      · simp
    rw [this]
    exact rank_vecMulVec_le _ _
  have hinv : H⁻¹ = Hᵀ := inv_eq_left_inv ((mem_orthogonalGroup_iff' n K).1 hH)
  have hu : IsUnit H := (isUnit_iff_isUnit_det _).2
    (isUnit_det_of_left_inverse ((mem_orthogonalGroup_iff' n K).1 hH))
  refine fun k => ⟨hlow k, ?_⟩
  have := rank_toBlock_inv_le_one_of_isQuasiseparable hu k (hlow k)
  rwa [hinv, rank_toBlock_transpose] at this

end Order

section Generator

variable {n : ℕ}

/-- Let $A \in K^{n \times n}$ and $p, q \in \mathbb{N}$. The matrix $A$ is **$\{p, q\}$-generator
representable** if there are $U, V \in K^{n \times p}$ and $P, Q \in K^{n \times q}$ with
$$a_{ij} = (UV^T)_{ij} \ \text{ for } j < i + p, \qquad
  a_{ij} = (PQ^T)_{ij} \ \text{ for } i < j + q.$$
That is, $A$ agrees with $UV^T$ in its part $\operatorname{tril}(A, p - 1)$ and with $PQ^T$ in
its part $\operatorname{triu}(A, -q + 1)$. This is the class of [golub2013matrix] §12.2.8.

The matrices $UV^T$ and $PQ^T$ have rank at most $p$ and at most $q$. -/
def IsGeneratorRepresentableOfOrder (A : Matrix (Fin n) (Fin n) K) (p q : ℕ) : Prop :=
  ∃ (U V : Matrix (Fin n) (Fin p) K) (P Q : Matrix (Fin n) (Fin q) K),
    (∀ i j : Fin n, (j : ℕ) < i + p → A i j = (U * Vᵀ) i j) ∧
      ∀ i j : Fin n, (i : ℕ) < j + q → A i j = (P * Qᵀ) i j

/-- If $A$ is $\{p, q\}$-generator representable, then $A^T$ is $\{q, p\}$-generator representable.
-/
theorem IsGeneratorRepresentableOfOrder.transpose {A : Matrix (Fin n) (Fin n) K} {p q : ℕ}
    (h : A.IsGeneratorRepresentableOfOrder p q) : Aᵀ.IsGeneratorRepresentableOfOrder q p := by
  obtain ⟨U, V, P, Q, h₁, h₂⟩ := h
  refine ⟨Q, P, V, U, fun i j hij => ?_, fun i j hij => ?_⟩
  · rw [transpose_apply, h₂ j i hij, ← transpose_apply (P * Qᵀ), transpose_mul,
      transpose_transpose]
  · rw [transpose_apply, h₁ j i hij, ← transpose_apply (U * Vᵀ), transpose_mul,
      transpose_transpose]

/-- The number of $x \in \{0, \dots, n - 1\}$ with $x < m$ is $\min(n, m)$. -/
private theorem card_val_lt (m : ℕ) : Fintype.card {x : Fin n // (x : ℕ) < m} = min n m := by
  rw [Fintype.card_subtype, Fin.card_filter_val_lt]

/-- The number of $x \in \{0, \dots, n - 1\}$ with $m \le x$ is $n - \min(n, m)$. -/
private theorem card_le_val (m : ℕ) : Fintype.card {x : Fin n // m ≤ (x : ℕ)} = n - min n m := by
  have e := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) fun x => (x : ℕ) < m
  rw [Fin.card_filter_val_lt, card_univ, Fintype.card_fin] at e
  simp only [not_lt] at e
  rw [Fintype.card_subtype]
  omega

private theorem hasLowerBandwidth_inv_of_isGeneratorRepresentableOfOrder
    {A : Matrix (Fin n) (Fin n) K} {p q : ℕ} (hA : IsUnit A)
    (h : A.IsGeneratorRepresentableOfOrder p q) : A⁻¹.HasLowerBandwidth p := by
  rw [hasLowerBandwidth_iff_fin]
  intro i j hij
  obtain ⟨U, V, P, Q, h₁, -⟩ := h
  have hk : (j : ℕ) + 1 + p ≤ n := by omega
  have hn := rank_toBlock_inv_add_card (isUnit_nonsing_inv_iff.2 hA)
    (fun x : Fin n => (j : ℕ) + 1 ≤ x) (fun y : Fin n => (y : ℕ) < j + 1 + p)
  rw [nonsing_inv_nonsing_inv A ((isUnit_iff_isUnit_det A).1 hA)] at hn
  have hr : (A.toBlock (fun x : Fin n => (j : ℕ) + 1 ≤ x)
      (fun y : Fin n => (y : ℕ) < j + 1 + p)).rank ≤ p := by
    have : A.toBlock (fun x : Fin n => (j : ℕ) + 1 ≤ x) (fun y : Fin n => (y : ℕ) < j + 1 + p) =
        (U * Vᵀ).toBlock (fun x : Fin n => (j : ℕ) + 1 ≤ x)
          (fun y : Fin n => (y : ℕ) < j + 1 + p) := by
      ext ⟨x, hx⟩ ⟨y, hy⟩
      exact h₁ x y (by omega)
    rw [this]
    exact (rank_submatrix_le (U * Vᵀ) Subtype.val Subtype.val).trans
      ((rank_mul_le_left _ _).trans (rank_le_width U))
  simp only [card_val_lt, card_le_val, Fintype.card_fin] at hn
  have h0 : (A⁻¹.toBlock (fun y : Fin n => ¬ (y : ℕ) < j + 1 + p)
      (fun x : Fin n => ¬ (j : ℕ) + 1 ≤ x)).rank = 0 := by
    have : min n (j + 1) = j + 1 := by omega
    have : min n (j + 1 + p) = j + 1 + p := by omega
    omega
  exact congrFun (congrFun (rank_eq_zero_iff.1 h0) ⟨i, by simp; omega⟩) ⟨j, by simp⟩

/-- Let $A \in K^{n \times n}$ be invertible and $\{p, q\}$-generator representable. Then $A^{-1}$
has lower bandwidth $p$ and upper bandwidth $q$: $(A^{-1})_{ij} = 0$ for $i > j + p$ and for
$j > i + q$. This is the banded inverse of [golub2013matrix] §12.2.8.

By the nullity theorem, the block of $A^{-1}$ on the rows $i \ge k + p$ and the columns $j < k$
has rank $\operatorname{rank} A[\{i \ge k\}, \{j < k + p\}] - p \le 0$, because that block of
$A$ is a block of $UV^T$. The upper bandwidth follows by transposition. -/
theorem IsGeneratorRepresentableOfOrder.hasBandwidth_inv {A : Matrix (Fin n) (Fin n) K}
    {p q : ℕ} (h : A.IsGeneratorRepresentableOfOrder p q) (hA : IsUnit A) :
    A⁻¹.HasLowerBandwidth p ∧ A⁻¹.HasUpperBandwidth q := by
  refine ⟨hasLowerBandwidth_inv_of_isGeneratorRepresentableOfOrder hA h, ?_⟩
  rw [← hasLowerBandwidth_transpose_iff, transpose_nonsing_inv]
  exact hasLowerBandwidth_inv_of_isGeneratorRepresentableOfOrder ((isUnit_transpose A).2 hA)
    h.transpose

end Generator

end Inverse

/-! ### The LU factorization of a semiseparable matrix -/

section LU

variable {n : ℕ}

/-- Under the hypotheses of `Matrix.isLU_quasiseparableOf`, $B(\tau)^T \, \mathbf{S}(u, v, t, u
\circ v, p, q, r) = (\tilde{p} q^T) \circ B(r)^{-1}$, which is the row elimination of
[golub2013matrix] Algorithm 12.2.1 in closed form. -/
private theorem transpose_unitBidiagonal_mul_quasiseparableOf (u v p q p' : Fin n → K)
    (t r τ : ℕ → K) (huv : u * v = p * q)
    (hτ : ∀ k (h : k + 1 < n), τ k * u ⟨k, by omega⟩ = t k * u ⟨k + 1, h⟩)
    (hp₀ : ∀ h : 0 < n, p' ⟨0, h⟩ = p ⟨0, h⟩)
    (hp : ∀ k (h : k + 1 < n), p' ⟨k + 1, h⟩ = p ⟨k + 1, h⟩ - p ⟨k, by omega⟩ * τ k * r k) :
    (unitBidiagonal n τ)ᵀ * quasiseparableOf u v t (u * v) p q r =
      vecMulVec p' q ⊙ (unitBidiagonal n r)⁻¹ := by
  rw [unitBidiagonal_eq_one_sub, transpose_sub, transpose_one, Matrix.sub_mul, Matrix.one_mul,
    inv_unitBidiagonal]
  ext i j
  rw [Matrix.sub_apply, Matrix.mul_apply]
  simp_rw [transpose_apply, of_apply, ite_mul, zero_mul]
  have hs := sum_dite_val_add_one_eq i fun k (_ : (k : ℕ) + 1 = i) =>
    τ k * quasiseparableOf u v t (u * v) p q r k j
  simp only [dite_eq_ite] at hs
  simp_rw [@eq_comm ℕ (i : ℕ)]
  rw [hs]
  simp only [hadamard_apply, vecMulVec_apply, of_apply]
  by_cases hi : 0 < (i : ℕ)
  · rw [dite_eq_left hi]
    obtain ⟨m, hm⟩ : ∃ m, (i : ℕ) = m + 1 := ⟨i - 1, by omega⟩
    have hmn : m + 1 < n := by omega
    have him : (⟨(i : ℕ) - 1, by omega⟩ : Fin n) = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
    rw [him]
    obtain rfl : i = ⟨m + 1, hmn⟩ := Fin.ext hm
    simp only [Nat.add_sub_cancel]
    have hm' : m < n := by omega
    have hτm := hτ m hmn
    have hpm := hp m hmn
    have e := congrFun huv ⟨m + 1, hmn⟩
    simp only [Pi.mul_apply] at e ⊢
    rcases lt_trichotomy (j : ℕ) m with hj | hj | hj
    · have h1 : j < (⟨m + 1, hmn⟩ : Fin n) := Fin.lt_def.2 (by simp; omega)
      have h2 : j < (⟨m, by omega⟩ : Fin n) := Fin.lt_def.2 (by simp; omega)
      have h3 : ¬ (⟨m + 1, hmn⟩ : Fin n) ≤ j := not_le.2 h1
      simp only [quasiseparableOf_apply, h1, h2, h3, ↓reduceIte, mul_zero]
      rw [Finset.prod_Ico_succ_top (by omega : (j : ℕ) ≤ m)]
      linear_combination (-(∏ l ∈ Finset.Ico (j : ℕ) m, t l) * v j) * hτm
    · obtain rfl : j = ⟨m, hm'⟩ := Fin.ext hj
      have h1 : (⟨m, hm'⟩ : Fin n) < ⟨m + 1, hmn⟩ := Fin.lt_def.2 (by simp)
      have h3 : ¬ (⟨m + 1, hmn⟩ : Fin n) ≤ ⟨m, hm'⟩ := not_le.2 h1
      simp only [quasiseparableOf_apply, h1, h3, lt_irrefl, ↓reduceIte, mul_zero,
        Nat.Ico_succ_singleton, prod_singleton, Pi.mul_apply]
      linear_combination (-v ⟨m, by omega⟩) * hτm
    · rcases (Nat.succ_le_of_lt hj).lt_or_eq with hj' | hj'
      · have h1 : (⟨m + 1, hmn⟩ : Fin n) < j := Fin.lt_def.2 (by simp; omega)
        have h2 : (⟨m, by omega⟩ : Fin n) < j := Fin.lt_def.2 (by simp; omega)
        simp only [quasiseparableOf_apply, lt_asymm h1, lt_asymm h2, h1.ne, h2.ne, h1.le,
          ↓reduceIte]
        rw [Finset.prod_eq_prod_Ico_succ_bot (by omega : m < (j : ℕ))]
        linear_combination (-(q j) * ∏ l ∈ Finset.Ico (m + 1) (j : ℕ), r l) * hpm
      · obtain rfl : j = ⟨m + 1, hmn⟩ := Fin.ext hj'.symm
        have h1 : (⟨m, by omega⟩ : Fin n) < ⟨m + 1, hmn⟩ := Fin.lt_def.2 (by simp)
        simp only [quasiseparableOf_apply, lt_asymm h1, h1.ne, lt_irrefl, le_refl, ↓reduceIte,
          Nat.Ico_succ_singleton, prod_singleton, Finset.Ico_self, prod_empty, mul_one,
          Pi.mul_apply]
        linear_combination e - q ⟨m + 1, hmn⟩ * hpm
  · rw [dite_eq_right hi, sub_zero]
    have h0 : 0 < n := by omega
    obtain rfl : i = ⟨0, h0⟩ := Fin.ext (Nat.eq_zero_of_not_pos hi)
    have hp0 := hp₀ h0
    have e := congrFun huv ⟨0, h0⟩
    simp only [Pi.mul_apply] at e
    rcases (Nat.zero_le (j : ℕ)).lt_or_eq with hj | hj
    · have h1 : (⟨0, by omega⟩ : Fin n) < j := Fin.lt_def.2 (by simp; omega)
      simp only [quasiseparableOf_apply, lt_asymm h1, h1.ne, h1.le, ↓reduceIte, hp0]
      ring
    · obtain rfl : j = ⟨0, h0⟩ := Fin.ext hj.symm
      simp only [quasiseparableOf_apply, lt_irrefl, le_refl, ↓reduceIte, Pi.mul_apply,
        Finset.Ico_self, prod_empty, mul_one, hp0, e]

/-- **The LU factorization of a semiseparable matrix.** Let $u, v, p, q, \tilde{p} \in K^n$ and let
$t, r, \tau$ be sequences in $K$, with $u \circ v = p \circ q$,
$$\tau_k u_k = t_k u_{k+1} \quad \text{and} \quad
  \tilde{p}_{k+1} = p_{k+1} - p_k \tau_k r_k \qquad (k + 1 < n),$$
and $\tilde{p}_0 = p_0$. Then the semiseparable matrix
$A = \mathbf{S}(u, v, t, u \circ v, p, q, r)$ has the LU factorization $A = LU$ with
$$L = B(\tau)^{-T}, \qquad U = (\tilde{p} q^T) \circ B(r)^{-1},$$
where $L$ is unit lower triangular and $U$ is upper triangular. This is the content of
[golub2013matrix] Algorithm 12.2.1 in closed form.

The source takes $\tau_k = t_k u_{k+1} / u_k$, which needs $u_k \neq 0$. The hypothesis
$\tau_k u_k = t_k u_{k+1}$ does not. The factorization is stated as `Matrix.IsLU`. -/
theorem isLU_quasiseparableOf (u v p q p' : Fin n → K) (t r τ : ℕ → K) (huv : u * v = p * q)
    (hτ : ∀ k (h : k + 1 < n), τ k * u ⟨k, by omega⟩ = t k * u ⟨k + 1, h⟩)
    (hp₀ : ∀ h : 0 < n, p' ⟨0, h⟩ = p ⟨0, h⟩)
    (hp : ∀ k (h : k + 1 < n), p' ⟨k + 1, h⟩ = p ⟨k + 1, h⟩ - p ⟨k, by omega⟩ * τ k * r k) :
    IsLU (quasiseparableOf u v t (u * v) p q r) ((unitBidiagonal n τ)ᵀ)⁻¹
      (vecMulVec p' q ⊙ (unitBidiagonal n r)⁻¹) where
  isUnitLowerTriangular := by
    rw [← transpose_nonsing_inv, inv_unitBidiagonal]
    refine ⟨fun i j hij => ?_, fun i => by simp⟩
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    simp [not_le.2 hij']
  isUpperTriangular := fun i j (hij : j < i) => by
    simp [inv_unitBidiagonal, not_le.2 hij]
  mul_eq := by
    rw [← transpose_unitBidiagonal_mul_quasiseparableOf u v p q p' t r τ huv hτ hp₀ hp,
      ← Matrix.mul_assoc, ← transpose_nonsing_inv, ← transpose_mul, unitBidiagonal_mul_inv,
      transpose_one, Matrix.one_mul]

end LU

/-! ### Products of $2 \times 2$ blocks in consecutive planes -/

section Chain

variable (N : ℕ) (M : ℕ → Matrix (Fin 2) (Fin 2) K)

/-- Let $N \in \mathbb{N}$ and $M_k \in K^{2 \times 2}$ for $k \in \mathbb{N}$. The $k$-th **factor
of the chain** of the $M_k$ is the matrix $G_k \in K^{(N+1) \times (N+1)}$ that is $M_k$ in the
coordinate plane $(k, k + 1)$ and the identity elsewhere, for $k < N$. For $k \ge N$ it is the
identity.

The embedding is `Matrix.planeEmbed`. -/
def givensFactor (k : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) K :=
  if h : k < N then planeEmbed ⟨k, by omega⟩ ⟨k + 1, by omega⟩ (M k) else 1

/-- The $k$-th factor of a chain is the adjacent embedding `Matrix.adjacentEmbed k (M k)` of
`Numlib.LinearAlgebra.Matrix.PlaneRotation`, in $K^{(N+1) \times (N+1)}$. -/
theorem givensFactor_eq_adjacentEmbed (k : ℕ) : givensFactor N M k = adjacentEmbed k (M k) := by
  unfold givensFactor adjacentEmbed
  split_ifs <;> first | rfl | omega

/-- **A chain of $2 \times 2$ blocks.** Let $N \in \mathbb{N}$ and $M_k \in K^{2 \times 2}$ for
$k \in \mathbb{N}$. The chain of the $M_k$ is the product
$$G_0 G_1 \cdots G_{N-1} \in K^{(N+1) \times (N+1)},$$
where $G_k$ is $M_k$ embedded in the coordinate plane $(k, k + 1)$ (`Matrix.givensFactor`). It
appears in [golub2013matrix] (12.2.4) and (12.2.12)–(12.2.13).

With plane rotations $M_k$, it is the matrix $Q^T = G_1 \cdots G_{n-1}$ of the source, whose
indices start at $1$. The product is `prodFwd`. -/
def givensChain : Matrix (Fin (N + 1)) (Fin (N + 1)) K :=
  prodFwd (givensFactor N M) N

/-- The leading factor $c_i$ of the entries of a chain: $c_0 = 1$, and $c_i = \delta_{i-1}$, the
lower right entry of $M_{i-1}$, for $i \ge 1$. -/
private def chainHead (i : ℕ) : K := if i = 0 then 1 else M (i - 1) 1 1

variable {N M}

/-- The entries of the partial product $G_0 \cdots G_{m-1}$ of a chain: the columns $j < m$ are
those of the full chain, the column $m$ still lacks its factor $\alpha_m$, and the columns
$j > m$ are those of the identity. -/
private theorem prodFwd_givensFactor_apply {m : ℕ} (hm : m ≤ N) (i j : Fin (N + 1)) :
    prodFwd (givensFactor N M) m i j =
      if (j : ℕ) < m then
        (if (i : ℕ) = j + 1 then M j 1 0
          else if (i : ℕ) ≤ j then
            chainHead M i * (∏ l ∈ Finset.Ico (i : ℕ) j, M l 0 1) * M j 0 0
          else 0)
      else if (j : ℕ) = m then
        (if (i : ℕ) ≤ j then chainHead M i * ∏ l ∈ Finset.Ico (i : ℕ) j, M l 0 1 else 0)
      else if (i : ℕ) = j then 1 else 0 := by
  induction m generalizing i j with
  | zero =>
    rw [prodFwd_zero, Matrix.one_apply]
    simp only [Nat.not_lt_zero, ↓reduceIte, Fin.ext_iff]
    by_cases hj : (j : ℕ) = 0
    · by_cases hi : (i : ℕ) = 0
      · simp [hi, hj, chainHead]
      · simp [hi, hj]
    · simp [hj]
  | succ m ih =>
    have hmN : m < N := by omega
    have hne : (⟨m, by omega⟩ : Fin (N + 1)) ≠ ⟨m + 1, by omega⟩ := by simp [Fin.ext_iff]
    rw [prodFwd_succ, givensFactor, dite_eq_left hmN, mul_planeEmbed_apply _ hne,
      ih hmN.le, ih hmN.le, ih hmN.le]
    simp only [Fin.ext_iff]
    rcases lt_trichotomy (j : ℕ) m with hj | hj | hj
    · have h1 : (j : ℕ) ≠ m := hj.ne
      have h2 : (j : ℕ) ≠ m + 1 := by omega
      have h3 : (j : ℕ) < m + 1 := by omega
      simp only [h1, h2, h3, hj, ↓reduceIte]
    · rw [hj]
      rcases lt_trichotomy (i : ℕ) (m + 1) with hi | hi | hi
      · have h1 : (i : ℕ) ≤ m := by omega
        simp [h1, hi.ne]
      · simp [hi]
      · simp [show ¬ (i : ℕ) ≤ m by omega, show (i : ℕ) ≠ m + 1 by omega]
    · rcases (Nat.succ_le_of_lt hj).lt_or_eq with hj' | hj'
      · simp only [show ¬ (j : ℕ) < m by omega, show (j : ℕ) ≠ m by omega,
          show (j : ℕ) ≠ m + 1 by omega, show ¬ (j : ℕ) < m + 1 by omega, ↓reduceIte]
      · have hj'' : (j : ℕ) = m + 1 := hj'.symm
        rw [hj'']
        rcases lt_trichotomy (i : ℕ) (m + 1) with hi | hi | hi
        · have h1 : (i : ℕ) ≤ m := by omega
          simp only [h1, show (i : ℕ) ≤ m + 1 by omega, hi.ne, lt_irrefl, ↓reduceIte,
            show ¬ (m + 1 < m) by omega, show m + 1 ≠ m by omega]
          rw [Finset.prod_Ico_succ_top h1]
          ring
        · simp [hi, chainHead]
        · simp [show ¬ (i : ℕ) ≤ m by omega, show ¬ (i : ℕ) ≤ m + 1 by omega,
            show (i : ℕ) ≠ m + 1 by omega]

/-- **The entries of a chain.** Let $M_k = \begin{bmatrix} \alpha_k & \beta_k \\ \gamma_k & \delta_k
\end{bmatrix} \in K^{2 \times 2}$ for $k \in \mathbb{N}$, and let $G = G_0 \cdots G_{N-1}$ be
their chain. Then
$$G_{ij} = \begin{cases} \gamma_j & i = j + 1, \\
  c_i \, \beta_i \cdots \beta_{j-1} \, \alpha'_j & i \le j, \\
  0 & i > j + 1, \end{cases}$$
where $c_0 = 1$, $c_i = \delta_{i-1}$ for $i \ge 1$, $\alpha'_j = \alpha_j$ for $j < N$, and
$\alpha'_N = 1$. This is (12.2.4) of [golub2013matrix]. -/
theorem givensChain_apply (i j : Fin (N + 1)) :
    givensChain N M i j =
      if (i : ℕ) = j + 1 then M j 1 0
      else if (i : ℕ) ≤ j then
        (if (i : ℕ) = 0 then 1 else M (i - 1) 1 1) * (∏ l ∈ Finset.Ico (i : ℕ) j, M l 0 1) *
          (if (j : ℕ) = N then 1 else M j 0 0)
      else 0 := by
  rw [givensChain, prodFwd_givensFactor_apply le_rfl]
  rcases (Nat.le_of_lt_succ j.2).lt_or_eq with hj | hj
  · simp only [hj, hj.ne, ↓reduceIte, chainHead]
  · have hi : (i : ℕ) ≠ N + 1 := by omega
    rw [hj]
    simp only [lt_irrefl, ↓reduceIte, hi, chainHead, mul_one]

/-- Every chain $G_0 \cdots G_{N-1}$ of $2 \times 2$ blocks is upper Hessenberg, as (12.2.4) of
[golub2013matrix] shows. -/
theorem givensChain_isUpperHessenberg : (givensChain N M).IsUpperHessenberg := by
  rw [isUpperHessenberg_iff_fin]
  intro i j hij
  rw [givensChain_apply]
  simp [show (i : ℕ) ≠ j + 1 by omega, show ¬ (i : ℕ) ≤ j by omega]

/-- Every chain $G_0 \cdots G_{N-1}$ of $2 \times 2$ blocks is quasiseparable. This is the remark of
[golub2013matrix] §12.2.2 that the "off-diagonal blocks have unit rank or less".

In the notation of `Matrix.givensChain_apply`, a strictly lower maximal block holds the single
entry $\gamma_k$, and a strictly upper one is the outer product of the vectors
$(c_i \beta_i \cdots \beta_{k-1})_i$ and $(\beta_k \cdots \beta_{j-1} \alpha'_j)_j$. -/
theorem givensChain_isQuasiseparable : (givensChain N M).IsQuasiseparable := by
  intro k
  constructor
  · have : (givensChain N M).toBlock (k < ·) (· ≤ k) =
        vecMulVec (fun i : {i // k < i} => if (i : ℕ) = k + 1 then (1 : K) else 0)
          (fun j : {j // j ≤ k} => if j = k then M k 1 0 else 0) := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [toBlock_apply, vecMulVec_apply, givensChain_apply]
      rw [Fin.lt_def] at hi
      rw [Fin.le_def] at hj
      have h1 : ¬ (i : ℕ) ≤ j := by omega
      by_cases hjk : j = k
      · subst hjk
        by_cases hik : (i : ℕ) = j + 1
        · simp only [hik, ↓reduceIte, one_mul]
        · simp only [hik, h1, ↓reduceIte, zero_mul]
      · have h2 : (i : ℕ) ≠ j + 1 := by
          have : (j : ℕ) < k := lt_of_le_of_ne hj (fun e => hjk (Fin.ext e))
          omega
        simp only [h2, h1, hjk, ↓reduceIte, mul_zero]
    rw [this]
    exact rank_vecMulVec_le _ _
  · have : (givensChain N M).toBlock (· ≤ k) (k < ·) =
        vecMulVec (fun i : {i // i ≤ k} =>
            (if (i : ℕ) = 0 then 1 else M (i - 1) 1 1) * ∏ l ∈ Finset.Ico (i : ℕ) k, M l 0 1)
          (fun j : {j // k < j} =>
            (∏ l ∈ Finset.Ico (k : ℕ) j, M l 0 1) * if (j : ℕ) = N then 1 else M j 0 0) := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [toBlock_apply, vecMulVec_apply, givensChain_apply]
      rw [Fin.le_def] at hi
      rw [Fin.lt_def] at hj
      rw [ite_eq_right (show ¬ (i : ℕ) = j + 1 by omega), ite_eq_left (show (i : ℕ) ≤ j by omega),
        ← prod_Ico_consecutive _ hi hj.le]
      ring
    rw [this]
    exact rank_vecMulVec_le _ _

end Chain

/-! ### LU factors of a semiseparable matrix -/

section LUFactors

variable {n : Type*} [Fintype n] [LinearOrder n]

omit [LinearOrder n] in
/-- If $f_l = 0$ for every $l$ that does not satisfy $p$, then $\sum_l f_l$ is the sum over the $l$
that satisfy $p$. -/
private theorem sum_eq_sum_subtype_of_eq_zero {p : n → Prop} [DecidablePred p] (f : n → K)
    (hf : ∀ l, ¬ p l → f l = 0) : ∑ l, f l = ∑ l : {l // p l}, f l := by
  rw [← Fintype.sum_subtype_add_sum_subtype p f,
    Finset.sum_eq_zero (s := (univ : Finset {l // ¬ p l})) (fun l _ => hf l l.2), add_zero]

/-- For an upper triangular $U$, every block $U[\{i \ge k\}, \{j \le k\}]$ has at most the one
nonzero entry $u_{kk}$, so its rank is at most one. -/
private theorem rank_toBlock_le_one_of_isUpperTriangular {U : Matrix n n K}
    (hU : U.IsUpperTriangular) (k : n) : (U.toBlock (k ≤ ·) (· ≤ k)).rank ≤ 1 := by
  have : U.toBlock (k ≤ ·) (· ≤ k) = vecMulVec (fun i : {i // k ≤ i} => if (i : n) = k then U k k
      else 0) (fun j : {j // j ≤ k} => if (j : n) = k then 1 else 0) := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [toBlock_apply, vecMulVec_apply]
    rcases (hj.trans hi).lt_or_eq with h | h
    · rw [hU h]
      by_cases hik : i = k
      · simp [hik, show j ≠ k by rintro rfl; exact h.ne hik.symm]
      · simp [hik]
    · obtain rfl : j = i := h
      obtain rfl : j = k := le_antisymm hj hi
      simp
  rw [this]
  exact rank_vecMulVec_le _ _

/-- For a lower triangular $L$, every block $L[\{i \le k\}, \{j \ge k\}]$ has at most the one
nonzero entry $l_{kk}$, so its rank is at most one. -/
private theorem rank_toBlock_le_one_of_isLowerTriangular {L : Matrix n n K}
    (hL : L.IsLowerTriangular) (k : n) : (L.toBlock (· ≤ k) (k ≤ ·)).rank ≤ 1 := by
  have : L.toBlock (· ≤ k) (k ≤ ·) = vecMulVec (fun i : {i // i ≤ k} => if (i : n) = k then L k k
      else 0) (fun j : {j // k ≤ j} => if (j : n) = k then 1 else 0) := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [toBlock_apply, vecMulVec_apply]
    rcases (hi.trans hj).lt_or_eq with h | h
    · rw [hL (OrderDual.toDual_lt_toDual.2 h)]
      by_cases hik : i = k
      · simp [hik, show j ≠ k by rintro rfl; exact h.ne hik]
      · simp [hik]
    · obtain rfl : i = j := h
      obtain rfl : i = k := le_antisymm hi hj
      simp
  rw [this]
  exact rank_vecMulVec_le _ _

/-- Let $A = LU$ with $L$ unit lower triangular and $U$ upper triangular, over $K$ with finite,
totally ordered indices. If $A$ is semiseparable, then $U$ is semiseparable. This is stated in
[golub2013matrix] §12.2.5.

An upper maximal block of $U = L^{-1} A$ is $L^{-1}[\{i \le k\}, \{j \le k\}] \, A[\{i \le k\},
\{j \ge k\}]$, since $L^{-1}$ is lower triangular. A lower maximal block of $U$ holds at most
its corner entry. -/
theorem IsLU.isSemiseparable_upper {A L U : Matrix n n K} (h : IsLU A L U)
    (hA : A.IsSemiseparable) : U.IsSemiseparable := by
  have hdet : IsUnit L.det := by rw [h.isUnitLowerTriangular.det_eq_one]; exact isUnit_one
  have hU : U = L⁻¹ * A := by rw [← h.mul_eq, ← Matrix.mul_assoc, nonsing_inv_mul L hdet,
    Matrix.one_mul]
  have hLi : L⁻¹.IsLowerTriangular := h.isUnitLowerTriangular.isLowerTriangular.inv
  refine fun k => ⟨rank_toBlock_le_one_of_isUpperTriangular h.isUpperTriangular k, ?_⟩
  have hblock : U.toBlock (· ≤ k) (k ≤ ·) =
      L⁻¹.toBlock (· ≤ k) (· ≤ k) * A.toBlock (· ≤ k) (k ≤ ·) := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    rw [hU, toBlock_apply, Matrix.mul_apply, Matrix.mul_apply,
      sum_eq_sum_subtype_of_eq_zero (p := (· ≤ k)) _ fun l hl => ?_]
    · rfl
    · exact mul_eq_zero_of_left
        (hLi (OrderDual.toDual_lt_toDual.2 (lt_of_le_of_lt hi (not_le.1 hl)))) _
  rw [hblock]
  exact (rank_mul_le_right _ _).trans (hA k).2

/-- Let $A = LU$ with $L$ unit lower triangular and $U$ upper triangular, over $K$ with finite,
totally ordered indices. If $A$ is semiseparable and every leading principal submatrix
$A[\{i < k\}, \{j < k\}]$ is nonsingular, then $L$ is semiseparable. This is stated in
[golub2013matrix] §12.2.5.

A lower maximal block of $L$ is $A[\{i \ge k\}, \{j \le k\}] \, U[\{i \le k\}, \{j \le
k\}]^{-1}$. The leading principal submatrices are those of the orders $0, \dots, |n| - 1$
(`Matrix.HasUnitStrictLeadingPrincipalSubmatrices`). Without this hypothesis the claim fails for
singular $A$. -/
theorem IsLU.isSemiseparable_lower {A L U : Matrix n n K} (h : IsLU A L U)
    (hA : A.IsSemiseparable) (hk : A.HasUnitStrictLeadingPrincipalSubmatrices) :
    L.IsSemiseparable := by
  refine fun k => ⟨?_, rank_toBlock_le_one_of_isLowerTriangular
    h.isUnitLowerTriangular.isLowerTriangular k⟩
  by_cases hne : (univ.filter (k < ·)).Nonempty
  · set k' := (univ.filter (k < ·)).min' hne with hk'
    have hkk' : k < k' := (Finset.mem_filter.1 ((univ.filter (k < ·)).min'_mem hne)).2
    have hiff : ∀ x, x < k' ↔ x ≤ k := fun x =>
      ⟨fun hx => not_lt.1 fun hkx => not_le.2 hx (min'_le _ x (by simpa using hkx)),
        fun hx => lt_of_le_of_lt hx hkk'⟩
    have hLU := h.toBlock_lt k'
    have hUu : IsUnit (U.strictLeadingPrincipalSubmatrix k') := by
      have hd := (isUnit_iff_isUnit_det _).1 (hk k')
      rw [← hLU.mul_eq, det_mul] at hd
      exact (isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hd)
    have hblock : L.toBlock (k ≤ ·) (· < k') * U.strictLeadingPrincipalSubmatrix k' =
        A.toBlock (k ≤ ·) (· < k') := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      rw [toBlock_apply, ← h.mul_eq, Matrix.mul_apply, Matrix.mul_apply,
        sum_eq_sum_subtype_of_eq_zero (p := (· < k')) _ fun l hl => ?_]
      · rfl
      · exact mul_eq_zero_of_right _ (h.isUpperTriangular (lt_of_lt_of_le hj (not_lt.1 hl)))
    have hL : L.toBlock (k ≤ ·) (· < k') =
        A.toBlock (k ≤ ·) (· < k') * (U.strictLeadingPrincipalSubmatrix k')⁻¹ := by
      rw [← hblock, Matrix.mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hUu),
        Matrix.mul_one]
    calc (L.toBlock (k ≤ ·) (· ≤ k)).rank
        ≤ (L.toBlock (k ≤ ·) (· < k')).rank :=
          rank_toBlock_mono L (fun _ hi => hi) fun x hx => (hiff x).2 hx
      _ ≤ (A.toBlock (k ≤ ·) (· < k')).rank := by rw [hL]; exact rank_mul_le_left _ _
      _ ≤ (A.toBlock (k ≤ ·) (· ≤ k)).rank :=
          rank_toBlock_mono A (fun _ hi => hi) fun x hx => (hiff x).1 hx
      _ ≤ 1 := (hA k).1
  · refine (rank_le_card_height _).trans (Fintype.card_le_one_iff.2 fun a b => ?_)
    have hmax : ∀ x, x ≤ k := fun x => not_lt.1 fun hx => hne ⟨x, by simpa using hx⟩
    exact Subtype.ext (le_antisymm ((hmax a).trans b.2) ((hmax b).trans a.2))

end LUFactors

/-! ### Quasiseparable matrices without a representation -/

section Counterexample

variable {n : ℕ}

/-- For every sequence $r$, the matrix $B(r)$ is quasiseparable, because it is the inverse of the
semiseparable matrix $B(r)^{-1}$ (`Matrix.IsQuasiseparable.inv`). -/
theorem isQuasiseparable_unitBidiagonal (r : ℕ → K) : (unitBidiagonal n r).IsQuasiseparable := by
  have hdet := isUnit_det_of_right_inverse (unitBidiagonal_mul_inv (n := n) r)
  have := (isSemiseparable_inv_unitBidiagonal r).isQuasiseparable.inv
    (isUnit_nonsing_inv_iff.2 ((isUnit_iff_isUnit_det _).2 hdet))
  rwa [nonsing_inv_nonsing_inv _ hdet] at this

/-- **$B(r)$ has no quasiseparable representation.** Let $n \ge 3$, and let $r$ be a sequence with
$r_0 \neq 0$ and $r_1 \neq 0$. Then $B(r) \in K^{n \times n}$ is not
$\mathbf{S}(u, v, t, d, p, q, r')$ for any $u, v, d, p, q \in K^n$ and any sequences $t$, $r'$.
Since $B(r)$ is quasiseparable (`Matrix.isQuasiseparable_unitBidiagonal`), this is a
counterexample to the claim of [golub2013matrix] §12.2.3 that every quasiseparable matrix has a
representation (12.2.8).

The entries of a representation satisfy $a_{01} a_{12} = a_{02} \, p_1 q_1$, with
$a_{01} = p_0 r'_0 q_1$, $a_{12} = p_1 r'_1 q_2$ and $a_{02} = p_0 r'_0 r'_1 q_2$. The matrix
$B(r)$ has $a_{01} a_{12} = r_0 r_1 \neq 0 = a_{02}$. The representation (12.2.8) carries one
transfer factor too many to leave a zero at distance two beside nonzero entries at distance one.
The representation `Matrix.quasiseparableRep` corrects this. -/
theorem unitBidiagonal_ne_quasiseparableOf {r : ℕ → K} (hn : 3 ≤ n) (h₀ : r 0 ≠ 0)
    (h₁ : r 1 ≠ 0) (u v : Fin n → K) (t : ℕ → K) (d p q : Fin n → K) (r' : ℕ → K) :
    unitBidiagonal n r ≠ quasiseparableOf u v t d p q r' := by
  intro h
  set a₀ : Fin n := ⟨0, by omega⟩
  set a₁ : Fin n := ⟨1, by omega⟩
  set a₂ : Fin n := ⟨2, by omega⟩
  have e : ∀ i j, unitBidiagonal n r i j = quasiseparableOf u v t d p q r' i j := fun i j => by
    rw [h]
  have b01 : unitBidiagonal n r a₀ a₁ = -r 0 := by simp [a₀, a₁, unitBidiagonal_apply]
  have b12 : unitBidiagonal n r a₁ a₂ = -r 1 := by simp [a₁, a₂, unitBidiagonal_apply]
  have b02 : unitBidiagonal n r a₀ a₂ = 0 := by simp [a₀, a₂, unitBidiagonal_apply]
  have s01 : quasiseparableOf u v t d p q r' a₀ a₁ = p a₀ * r' 0 * q a₁ := by
    simp [a₀, a₁, quasiseparableOf_apply]
  have s12 : quasiseparableOf u v t d p q r' a₁ a₂ = p a₁ * r' 1 * q a₂ := by
    simp [a₁, a₂, quasiseparableOf_apply]
  have s02 : quasiseparableOf u v t d p q r' a₀ a₂ = p a₀ * (r' 0 * r' 1) * q a₂ := by
    simp [a₀, a₂, quasiseparableOf_apply, Finset.prod_range_succ]
  have e01 := (b01.symm.trans (e a₀ a₁)).trans s01
  have e12 := (b12.symm.trans (e a₁ a₂)).trans s12
  have e02 := (b02.symm.trans (e a₀ a₂)).trans s02
  exact mul_ne_zero h₀ h₁ (by
    linear_combination (-r 1) * e01 + (p a₀ * r' 0 * q a₁) * e12 - (p a₁ * q a₁) * e02)

/-- **$B(r)$ has no generator representation.** Let $n \ge 3$, and let $r$ be a sequence with
$r_0 \neq 0$ and $r_1 \neq 0$. Then $B(r) \in K^{n \times n}$ is not $\mathbf{S}(u, v, 1, d, p,
q, 1) = \operatorname{tril}(uv^T, -1) + \operatorname{diag}(d) + \operatorname{triu}(pq^T, 1)$
for any $u, v, d, p, q \in K^n$. This illustrates the remark of [golub2013matrix] §12.2.3 that
"not every quasiseparable matrix has a generator representation".

This is the case $t = r' = 1$ of `Matrix.unitBidiagonal_ne_quasiseparableOf`. -/
theorem unitBidiagonal_ne_generatorRep {r : ℕ → K} (hn : 3 ≤ n) (h₀ : r 0 ≠ 0) (h₁ : r 1 ≠ 0)
    (u v d p q : Fin n → K) : unitBidiagonal n r ≠ quasiseparableOf u v 1 d p q 1 :=
  unitBidiagonal_ne_quasiseparableOf hn h₀ h₁ u v 1 d p q 1

end Counterexample

/-! ### The inverse of an irreducible tridiagonal matrix -/

section TridiagonalInverse

variable {m : ℕ}

/-- If $A$ is invertible and tridiagonal with nonzero subdiagonal entries, then the corner entry
$(A^{-1})_{N0}$ is nonzero, by the nullity theorem. -/
private theorem inv_last_zero_ne_zero {A : Matrix (Fin (m + 1)) (Fin (m + 1)) K}
    (hT : A.IsTridiagonal) (hA : IsUnit A)
    (hsub : ∀ i j : Fin (m + 1), (i : ℕ) = j + 1 → A i j ≠ 0) : A⁻¹ (Fin.last m) 0 ≠ 0 := by
  have h := rank_toBlock_inv_add_card hA (Fin.last m ≤ ·) (· ≤ 0)
  beta_reduce at h
  let e₀ : Fin m ≃ {x : Fin (m + 1) // ¬ x ≤ 0} :=
    (finSuccAboveEquiv 0).trans (Equiv.subtypeEquivRight fun x => (not_congr Fin.le_zero_iff).symm)
  let e₁ : Fin m ≃ {x : Fin (m + 1) // ¬ Fin.last m ≤ x} :=
    (finSuccAboveEquiv (Fin.last m)).trans
      (Equiv.subtypeEquivRight fun x => (not_congr Fin.last_le_iff).symm)
  set B := (A.toBlock (fun i => ¬ i ≤ 0) (fun j => ¬ Fin.last m ≤ j)).submatrix e₀ e₁ with hB
  have hBapply : ∀ i j, B i j = A i.succ j.castSucc := fun i j => by
    simp [hB, e₀, e₁, finSuccAboveEquiv_apply]
  have hBu : B.IsUpperTriangular := fun i j hij => by
    rw [hBapply]
    exact hT _ _ (Or.inl ⟨j.succ, Fin.castSucc_lt_succ, Fin.succ_lt_succ_iff.2 hij⟩)
  have hBdet : IsUnit B := hBu.isUnit_iff.2 fun i => by
    rw [hBapply]
    exact hsub _ _ (by simp)
  have hrank : (A.toBlock (fun i => ¬ i ≤ 0) (fun j => ¬ Fin.last m ≤ j)).rank = m := by
    rw [← rank_submatrix _ e₀ e₁, ← hB, rank_of_isUnit B hBdet, Fintype.card_fin]
  have c₁ : Fintype.card {x : Fin (m + 1) // Fin.last m ≤ x} = 1 :=
    Fintype.card_eq_one_iff.2 ⟨⟨Fin.last m, le_rfl⟩, fun x => Subtype.ext (Fin.last_le_iff.1 x.2)⟩
  have c₂ : Fintype.card {x : Fin (m + 1) // x ≤ 0} = 1 :=
    Fintype.card_eq_one_iff.2 ⟨⟨0, le_rfl⟩, fun x => Subtype.ext (Fin.le_zero_iff.1 x.2)⟩
  rw [hrank, Fintype.card_fin, c₁, c₂] at h
  intro h0
  have hz : A⁻¹.toBlock (Fin.last m ≤ ·) (· ≤ 0) = 0 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    obtain rfl := Fin.last_le_iff.1 hi
    obtain rfl := Fin.le_zero_iff.1 hj
    exact h0
  rw [hz, rank_zero] at h
  omega

/-- If $B$ is semiseparable and $j \le i$, then $b_{i0} \, b_{Nj} = b_{ij} \, b_{N0}$. -/
private theorem mul_eq_mul_of_isSemiseparable {B : Matrix (Fin (m + 1)) (Fin (m + 1)) K}
    (hB : B.IsSemiseparable) {i j : Fin (m + 1)} (hji : j ≤ i) :
    B i 0 * B (Fin.last m) j = B i j * B (Fin.last m) 0 := by
  have hblk := (hB j).1
  by_contra hne
  have := card_le_rank_of_det_submatrix_ne_zero (A := B.toBlock (j ≤ ·) (· ≤ j))
    (r := ![⟨i, hji⟩, ⟨Fin.last m, Fin.le_last j⟩]) (c := ![⟨0, Fin.zero_le j⟩, ⟨j, le_rfl⟩])
    (by rw [det_fin_two]; simpa [sub_eq_zero] using hne)
  omega

/-- If $A$ is invertible and tridiagonal and $j \le i$, then $(A^{-1})_{i0} (A^{-1})_{Nj} =
(A^{-1})_{ij} (A^{-1})_{N0}$. -/
private theorem inv_apply_eq_of_le {A : Matrix (Fin (m + 1)) (Fin (m + 1)) K}
    (hT : A.IsTridiagonal) (hA : IsUnit A) {i j : Fin (m + 1)} (hji : j ≤ i) :
    A⁻¹ i 0 * A⁻¹ (Fin.last m) j = A⁻¹ i j * A⁻¹ (Fin.last m) 0 :=
  mul_eq_mul_of_isSemiseparable (hT.isSemiseparable_inv hA) hji

/-- Let $A \in K^{n \times n}$ be invertible and tridiagonal, with nonzero subdiagonal entries
$a_{j+1, j}$ and nonzero superdiagonal entries $a_{i, i+1}$. Then there are $u, v, p, q \in K^n$
with $u \circ v = p \circ q$ and
$$A^{-1} = \operatorname{tril}(uv^T, -1) + \operatorname{diag}(u \circ v) +
  \operatorname{triu}(pq^T, 1),$$
that is, $A^{-1} = \mathbf{S}(u, v, 1, u \circ v, p, q, 1)$ is **generator representable**. This
is the second half of Fact 1 in [golub2013matrix] §12.2.3.

The corners $(A^{-1})_{N0}$ and $(A^{-1})_{0N}$ are nonzero by the nullity theorem, and every
$2 \times 2$ minor of $A^{-1}$ on the rows $i, N$ and the columns $0, j$ with $j \le i$ vanishes
because $A^{-1}$ is semiseparable. The upper part follows by transposition. -/
theorem IsTridiagonal.inv_eq_generatorRep {n : ℕ} {A : Matrix (Fin n) (Fin n) K}
    (hT : A.IsTridiagonal) (hA : IsUnit A)
    (hsub : ∀ i j : Fin n, (i : ℕ) = j + 1 → A i j ≠ 0)
    (hsup : ∀ i j : Fin n, (j : ℕ) = i + 1 → A i j ≠ 0) :
    ∃ u v p q : Fin n → K, u * v = p * q ∧ A⁻¹ = quasiseparableOf u v 1 (u * v) p q 1 := by
  cases n with
  | zero => exact ⟨0, 0, 0, 0, rfl, Subsingleton.elim _ _⟩
  | succ m =>
  have hTt : Aᵀ.IsTridiagonal := fun i j h => hT j i h.symm
  have hAt : IsUnit Aᵀ := (isUnit_transpose A).2 hA
  have hXt : Aᵀ⁻¹ = A⁻¹ᵀ := (transpose_nonsing_inv A).symm
  have hc := inv_last_zero_ne_zero hT hA hsub
  have hc' : A⁻¹ 0 (Fin.last m) ≠ 0 := by
    have := inv_last_zero_ne_zero hTt hAt fun i j h => hsup j i h
    rwa [hXt, transpose_apply] at this
  have hlow : ∀ i j : Fin (m + 1), j ≤ i →
      A⁻¹ i j = A⁻¹ i 0 / A⁻¹ (Fin.last m) 0 * A⁻¹ (Fin.last m) j := fun i j hji => by
    rw [div_mul_eq_mul_div, eq_div_iff hc, inv_apply_eq_of_le hT hA hji]
  have hup : ∀ i j : Fin (m + 1), i ≤ j →
      A⁻¹ i j = A⁻¹ i (Fin.last m) / A⁻¹ 0 (Fin.last m) * A⁻¹ 0 j := fun i j hij => by
    have := inv_apply_eq_of_le hTt hAt hij
    rw [hXt] at this
    simp only [transpose_apply] at this
    rw [div_mul_eq_mul_div, eq_div_iff hc', mul_comm (A⁻¹ i (Fin.last m)), this]
  refine ⟨fun i => A⁻¹ i 0 / A⁻¹ (Fin.last m) 0, fun j => A⁻¹ (Fin.last m) j,
    fun i => A⁻¹ i (Fin.last m) / A⁻¹ 0 (Fin.last m), fun j => A⁻¹ 0 j, ?_, ?_⟩
  · ext i
    simp only [Pi.mul_apply]
    rw [← hlow i i le_rfl, ← hup i i le_rfl]
  · ext i j
    simp only [quasiseparableOf_apply, Pi.one_apply, prod_const_one, mul_one, Pi.mul_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [hup i j h.le]
      simp [lt_asymm h, h.ne]
    · rw [hlow i i le_rfl]
      simp
    · rw [hlow i j h.le]
      simp [h]

end TridiagonalInverse

/-! ### Diagonal plus semiseparable -/

section DiagonalPlus

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- The indices of the right summand of $n \oplus n$ that satisfy a predicate $P$ correspond to the
indices of $n$ that satisfy $P$. -/
private def sumInrSubtypeEquiv (P : n → Prop) :
    {x : n ⊕ n // Sum.elim (fun _ => False) P x} ≃ {i // P i} where
  toFun x := match x with
    | ⟨Sum.inr i, h⟩ => ⟨i, h⟩
    | ⟨Sum.inl _, h⟩ => h.elim
  invFun i := ⟨Sum.inr i, i.2⟩
  left_inv := by
    rintro ⟨_ | i, h⟩
    · exact h.elim
    · rfl
  right_inv _ := rfl

/-- If $I + T$ is invertible and $C = (I + T)^{-1}$, then $\begin{bmatrix} T & I \\ I & -I
\end{bmatrix} \begin{bmatrix} C & C \\ C & C - I \end{bmatrix} = I$. -/
private theorem fromBlocks_mul_fromBlocks_inv {T : Matrix n n K} (hu : IsUnit (1 + T)) :
    fromBlocks T 1 1 (-1) * fromBlocks (1 + T)⁻¹ (1 + T)⁻¹ (1 + T)⁻¹ ((1 + T)⁻¹ - 1) = 1 := by
  have hC : (1 + T)⁻¹ + T * (1 + T)⁻¹ = 1 := by
    simpa [Matrix.add_mul] using mul_nonsing_inv (1 + T) ((isUnit_iff_isUnit_det _).1 hu)
  rw [fromBlocks_multiply, ← fromBlocks_one]
  refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.one_mul, add_comm, hC]
  · rw [Matrix.one_mul, ← add_sub_assoc, add_comm, hC, sub_self]
  · rw [Matrix.one_mul, Matrix.neg_mul, Matrix.one_mul, add_neg_cancel]
  · rw [Matrix.one_mul, Matrix.neg_mul, Matrix.one_mul, ← sub_eq_add_neg, sub_sub_cancel]

/-- If $T$ is semiseparable and $I + T$ is invertible, then every block $\bigl((I + T)^{-1} -
I\bigr)[\{i \ge k\}, \{j \le k\}]$ has rank at most one, by the nullity theorem for the bordered
matrix $\begin{bmatrix} T & I \\ I & -I \end{bmatrix}$. -/
private theorem rank_toBlock_inv_one_add_sub_one_le {T : Matrix n n K} (hT : T.IsSemiseparable)
    (hu : IsUnit (1 + T)) (k : n) : (((1 + T)⁻¹ - 1).toBlock (k ≤ ·) (· ≤ k)).rank ≤ 1 := by
  classical
  set M : Matrix (n ⊕ n) (n ⊕ n) K := fromBlocks T 1 1 (-1) with hM
  have hMM := fromBlocks_mul_fromBlocks_inv hu
  rw [← hM] at hMM
  have hMu : IsUnit M := (isUnit_iff_isUnit_det _).2 (isUnit_det_of_right_inverse hMM)
  set p : n ⊕ n → Prop := Sum.elim (fun _ => False) (k ≤ ·) with hp
  set q : n ⊕ n → Prop := Sum.elim (fun _ => False) (· ≤ k) with hq
  have hnull := rank_toBlock_inv_add_card hMu p q
  -- the block of `M⁻¹` is the block of `(1 + T)⁻¹ - 1`
  have hblock : ((1 + T)⁻¹ - 1).toBlock (k ≤ ·) (· ≤ k) =
      (M⁻¹.toBlock p q).submatrix (sumInrSubtypeEquiv (k ≤ ·)).symm
        (sumInrSubtypeEquiv (· ≤ k)).symm := by
    rw [inv_eq_right_inv hMM]
    ext i j
    rfl
  -- the complementary block of `M` has rank at most `card n`
  obtain ⟨X, Y, hXY⟩ := (rank_le_iff_exists_mul_transpose (T.toBlock (k ≤ ·) (· ≤ k)) 1).1 (hT k).1
  let f : {x // ¬ q x} → K := fun x => match x.1 with
    | Sum.inl i => if h : k ≤ i then X ⟨i, h⟩ 0 else 0
    | Sum.inr _ => 0
  let g : {y // ¬ p y} → K := fun y => match y.1 with
    | Sum.inl j => if h : j ≤ k then Y ⟨j, h⟩ 0 else 0
    | Sum.inr _ => 0
  have hTij : ∀ i j (hi : k ≤ i) (hj : j ≤ k), T i j = X ⟨i, hi⟩ 0 * Y ⟨j, hj⟩ 0 := by
    intro i j hi hj
    have := congrFun (congrFun hXY ⟨i, hi⟩) ⟨j, hj⟩
    simpa [toBlock_apply, Matrix.mul_apply] using this
  let s : Finset {x // ¬ q x} :=
    (univ : Finset {i // i < k}).image fun i => ⟨Sum.inl i.1, by simp [hq]⟩
  let t : Finset {y // ¬ p y} :=
    (univ : Finset {j // k < j}).image fun j => ⟨Sum.inl j.1, by simp [hp]⟩
  have hE : ∀ x y, (M.toBlock (fun x => ¬ q x) (fun y => ¬ p y) - vecMulVec f g) x y ≠ 0 →
      x ∈ s ∨ y ∈ t := by
    rintro ⟨i | i, hx⟩ ⟨j | j, hy⟩ hne
    · by_cases hik : k ≤ i
      · by_cases hjk : j ≤ k
        · exact absurd (by simp [hM, f, g, toBlock_apply, vecMulVec_apply, hik, hjk,
            hTij i j hik hjk]) hne
        · exact Or.inr (mem_image.2 ⟨⟨j, not_le.1 hjk⟩, mem_univ _, rfl⟩)
      · exact Or.inl (mem_image.2 ⟨⟨i, not_le.1 hik⟩, mem_univ _, rfl⟩)
    · have hjk : j < k := by simpa [hp] using hy
      by_cases hij : i = j
      · subst hij
        exact Or.inl (mem_image.2 ⟨⟨i, hjk⟩, mem_univ _, rfl⟩)
      · exact absurd (by simp [hM, f, g, toBlock_apply, vecMulVec_apply, one_apply_ne hij]) hne
    · have hik : k < i := by simpa [hq] using hx
      by_cases hij : i = j
      · subst hij
        exact Or.inr (mem_image.2 ⟨⟨i, hik⟩, mem_univ _, rfl⟩)
      · exact absurd (by simp [hM, f, g, toBlock_apply, vecMulVec_apply, one_apply_ne hij]) hne
    · have hik : k < i := by simpa [hq] using hx
      have hjk : j < k := by simpa [hp] using hy
      exact absurd (by simp [hM, f, g, toBlock_apply, vecMulVec_apply,
        one_apply_ne (hjk.trans hik).ne']) hne
  have hEr := rank_le_card_add_card_of_forall_ne_zero _ s t hE
  have hs : s.card ≤ Fintype.card {i // i < k} := card_image_le.trans (card_univ.le)
  have ht : t.card ≤ Fintype.card {j // k < j} := card_image_le.trans (card_univ.le)
  have hMr : (M.toBlock (fun x => ¬ q x) (fun y => ¬ p y)).rank ≤
      1 + (Fintype.card {i // i < k} + Fintype.card {j // k < j}) := by
    have h := rank_add_le (vecMulVec f g) (M.toBlock (fun x => ¬ q x) (fun y => ¬ p y) -
      vecMulVec f g)
    rw [add_sub_cancel] at h
    have := rank_vecMulVec_le f g
    omega
  -- counting
  have c1 : Fintype.card {x // p x} = Fintype.card {i // k ≤ i} :=
    Fintype.card_congr (sumInrSubtypeEquiv (k ≤ ·))
  have c2 : Fintype.card {x // q x} = Fintype.card {j // j ≤ k} :=
    Fintype.card_congr (sumInrSubtypeEquiv (· ≤ k))
  have c3 := card_le_add_card_le k
  have c4 := card_lt_add_card_le k
  have c5 : Fintype.card {i // i < k} + Fintype.card {i // k ≤ i} = Fintype.card n := by
    have e := card_filter_add_card_filter_not (s := (univ : Finset n)) (· < k)
    simp only [not_lt] at e
    rw [Fintype.card_subtype, Fintype.card_subtype, ← card_univ]
    omega
  rw [Fintype.card_sum, c1, c2] at hnull
  rw [hblock, rank_submatrix]
  omega

/-- Let $\delta \in K^n$ have nonzero entries, let $D = \operatorname{diag}(\delta)$, let $S$ be
semiseparable, and let $D + S$ be invertible. Then there is a semiseparable matrix $S_1$ with
$$(D + S)^{-1} = D^{-1} + S_1.$$
So the inverse of a nonsingular diagonal-plus-semiseparable matrix is
diagonal-plus-semiseparable. This is Fact 3 in [golub2013matrix] §12.2.3.

With $T = D^{-1} S$, the difference $(D + S)^{-1} - D^{-1}$ is
$\bigl((I + T)^{-1} - I\bigr) D^{-1}$, and $(I + T)^{-1} - I$ is a block of the inverse of the
bordered matrix $\begin{bmatrix} T & I \\ I & -I \end{bmatrix}$, to which the nullity theorem
applies. -/
theorem inv_diagonal_add_eq_add {δ : n → K} (hδ : ∀ i, δ i ≠ 0) {S : Matrix n n K}
    (hS : S.IsSemiseparable) (hu : IsUnit (diagonal δ + S)) :
    ∃ S₁ : Matrix n n K, S₁.IsSemiseparable ∧ (diagonal δ + S)⁻¹ = (diagonal δ)⁻¹ + S₁ := by
  have hDinv : (diagonal δ)⁻¹ = diagonal δ⁻¹ := by
    refine inv_eq_right_inv ?_
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    exact mul_inv_cancel₀ (hδ i)
  set T := diagonal δ⁻¹ * S with hT
  have hTs : T.IsSemiseparable := by
    have := hS.diagonal_mul_mul_diagonal δ⁻¹ fun _ => 1
    rwa [diagonal_one, Matrix.mul_one] at this
  have hDT : diagonal δ + S = diagonal δ * (1 + T) := by
    rw [hT, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, diagonal_mul_diagonal,
      show (fun i => δ i * δ⁻¹ i) = fun _ => (1 : K) from funext fun i => mul_inv_cancel₀ (hδ i),
      diagonal_one, Matrix.one_mul]
  have hu' : IsUnit (1 + T) := by
    rw [hDT, isUnit_iff_isUnit_det, det_mul] at hu
    exact (isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hu)
  have hlow : ∀ {T : Matrix n n K}, T.IsSemiseparable → IsUnit (1 + T) →
      ((1 + T)⁻¹ - 1).IsSemiseparable := fun {T} hT hu k => by
    refine ⟨rank_toBlock_inv_one_add_sub_one_le hT hu k, ?_⟩
    have := rank_toBlock_inv_one_add_sub_one_le hT.transpose
      (by rw [← transpose_one, ← transpose_add]; exact (isUnit_transpose _).2 hu) k
    rwa [← transpose_one, ← transpose_add, ← transpose_nonsing_inv, ← transpose_sub,
      rank_toBlock_transpose] at this
  refine ⟨((1 + T)⁻¹ - 1) * (diagonal δ)⁻¹, ?_, ?_⟩
  · have := (hlow hTs hu').diagonal_mul_mul_diagonal (fun _ => 1) δ⁻¹
    rwa [diagonal_one, Matrix.one_mul, ← hDinv] at this
  · rw [hDT, Matrix.mul_inv_rev, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]

end DiagonalPlus

/-! ### The Givens-vector representation -/

section GivensVector

variable {m : ℕ}

/-- If $\rho_l \neq 0$ for $l \le N$ and $j \le i \le N$, then $\prod_{l=j}^{i-1} \rho_{l+1} /
\rho_l = \rho_i / \rho_j$. -/
private theorem prod_Ico_div_eq {ρ : ℕ → ℝ} {N : ℕ} (hρ : ∀ l ≤ N, ρ l ≠ 0) {j i : ℕ}
    (hji : j ≤ i) (hi : i ≤ N) : ∏ l ∈ Finset.Ico j i, ρ (l + 1) / ρ l = ρ i / ρ j := by
  induction i, hji using Nat.le_induction with
  | base => simp [div_self (hρ j hi)]
  | succ i hji ih =>
    rw [Finset.prod_Ico_succ_top hji, ih (by omega), div_mul_div_comm, mul_comm (ρ i),
      mul_div_mul_right _ _ (hρ i (by omega))]

/-- **The Givens-vector representation.** Let $A \in \mathbb{R}^{(N+1) \times (N+1)}$ be lower
triangular and semiseparable, with $a_{N0} \neq 0$. Then there are sequences $c$ and $s$ of
reals with $c_k^2 + s_k^2 = 1$ and $s_k \neq 0$ for all $k$, and a vector
$v \in \mathbb{R}^{N+1}$, such that
$$a_{ij} = c'_i \, s_j s_{j+1} \cdots s_{i-1} \, v_j \quad (j \le i),$$
where $c'_i = c_i$ for $i < N$ and $c'_N = 1$. This is (12.2.11) of [golub2013matrix] (Vandebril
and Van Barel, 2005).

The pairs $(c_k, s_k)$ are those of the Givens rotations that reduce the first column of $A$ to
a multiple of $e_0$ from the bottom up: with $\rho_k = \pm \|A(k{:}N, 0)\|$, they are
$c_k = a_{k0} / \rho_k$ and $s_k = \rho_{k+1} / \rho_k$. Below the diagonal, the other columns
are multiples of the first. The hypothesis $a_{N0} \neq 0$ makes every $\rho_k$ nonzero. -/
theorem exists_givensVector_rep {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hA : A.IsSemiseparable) (hL : A.IsLowerTriangular) (h0 : A (Fin.last m) 0 ≠ 0) :
    ∃ c s : ℕ → ℝ, (∀ k, c k ^ 2 + s k ^ 2 = 1) ∧ (∀ k, s k ≠ 0) ∧
      ∃ v : Fin (m + 1) → ℝ, ∀ i j : Fin (m + 1), A i j =
        if j ≤ i then (if (i : ℕ) = m then 1 else c i) * (∏ l ∈ Finset.Ico (j : ℕ) i, s l) * v j
        else 0 := by
  set a : ℕ → ℝ := fun k => if h : k < m + 1 then A ⟨k, h⟩ 0 else 0 with ha
  have ham : a m = A (Fin.last m) 0 := by simp [ha, Fin.last]
  set σ : ℝ := a m / |a m| with hσ
  have habs : |a m| ≠ 0 := abs_ne_zero.2 (ham ▸ h0)
  have hσsq : σ ^ 2 = 1 := by rw [hσ, div_pow, sq_abs, div_self (pow_ne_zero 2 (ham ▸ h0))]
  set ρ : ℕ → ℝ := fun k => σ * Real.sqrt (∑ l ∈ Finset.Ico k (m + 1), a l ^ 2) with hρ
  have hS : ∀ k, 0 ≤ ∑ l ∈ Finset.Ico k (m + 1), a l ^ 2 :=
    fun k => Finset.sum_nonneg fun l _ => sq_nonneg _
  have hρsq' : ∀ k, ρ k ^ 2 = ∑ l ∈ Finset.Ico k (m + 1), a l ^ 2 := fun k => by
    rw [hρ, mul_pow, hσsq, one_mul, Real.sq_sqrt (hS k)]
  have hρsq : ∀ k ≤ m, ρ k ^ 2 = a k ^ 2 + ρ (k + 1) ^ 2 := fun k hk => by
    rw [hρsq', hρsq', Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have hρne : ∀ k ≤ m, ρ k ≠ 0 := fun k hk h => by
    have h1 := hρsq' k
    rw [h, zero_pow two_ne_zero] at h1
    have h2 : a m ^ 2 ≤ ∑ l ∈ Finset.Ico k (m + 1), a l ^ 2 :=
      Finset.single_le_sum (fun l _ => sq_nonneg (a l)) (Finset.mem_Ico.2 ⟨hk, by omega⟩)
    have h3 : 0 < a m ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (ham ▸ h0)))
    linarith
  have hρm : ρ m = a m := by
    rw [hρ]
    dsimp only
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton, Real.sqrt_sq_eq_abs, hσ,
      div_mul_cancel₀ _ habs]
  set c : ℕ → ℝ := fun k => if k < m then a k / ρ k else 0 with hc
  set s : ℕ → ℝ := fun k => if k < m then ρ (k + 1) / ρ k else 1 with hs
  refine ⟨c, s, fun k => ?_, fun k => ?_,
    fun j => A (Fin.last m) j / A (Fin.last m) 0 * ρ j, fun i j => ?_⟩
  · by_cases hk : k < m
    · simp only [hc, hs, hk, ↓reduceIte]
      rw [div_pow, div_pow, ← add_div, ← hρsq k hk.le,
        div_self (pow_ne_zero 2 (hρne k hk.le))]
    · simp [hc, hs, hk]
  · by_cases hk : k < m
    · simp only [hs, hk, ↓reduceIte]
      exact div_ne_zero (hρne (k + 1) hk) (hρne k hk.le)
    · simp [hs, hk]
  by_cases hji : j ≤ i
  · rw [ite_eq_left hji]
    have hmin := mul_eq_mul_of_isSemiseparable hA hji
    have hi : (i : ℕ) ≤ m := Nat.le_of_lt_succ i.2
    have hai : A i 0 = (if (i : ℕ) = m then 1 else c i) * ρ i := by
      split_ifs with him
      · rw [one_mul, him, hρm, ham]
        congr 1
        exact Fin.ext him
      · have hlt : (i : ℕ) < m := lt_of_le_of_ne hi him
        simp only [hc, hlt, ↓reduceIte]
        rw [div_mul_cancel₀ _ (hρne i hi)]
        change A i 0 = if h : (i : ℕ) < m + 1 then A ⟨i, h⟩ 0 else 0
        rw [dite_eq_left i.2]
    have hprod : ∏ l ∈ Finset.Ico (j : ℕ) i, s l = ρ i / ρ j := by
      rw [Finset.prod_congr rfl fun l hl => (by
        have : l < m := by have := (Finset.mem_Ico.1 hl).2; omega
        simp only [hs, this, ↓reduceIte] : s l = ρ (l + 1) / ρ l)]
      exact prod_Ico_div_eq hρne (Fin.le_def.1 hji) hi
    have hρj := hρne j (le_trans (Fin.le_def.1 hji) hi)
    rw [hprod]
    calc A i j = A i 0 * A (Fin.last m) j / A (Fin.last m) 0 := by
          rw [hmin, mul_div_cancel_right₀ _ h0]
      _ = (if (i : ℕ) = m then 1 else c i) * ρ i * A (Fin.last m) j / A (Fin.last m) 0 := by
          rw [hai]
      _ = _ := by field_simp
  · rw [ite_eq_right hji]
    exact hL (OrderDual.toDual_lt_toDual.2 (not_le.1 hji))

end GivensVector

/-! ### Orthogonal upper Hessenberg matrices as products of reflections -/

section OrthogonalHessenberg

variable {N : ℕ}

/-- If $XX^T = I$ and $x_{jj} = 1$, then $x_{jl} = 0$ for every $l \neq j$. -/
private theorem apply_eq_zero_of_mul_transpose {X : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hX : X * Xᵀ = 1) {j : Fin (N + 1)} (hj : X j j = 1) {l : Fin (N + 1)} (hl : l ≠ j) :
    X j l = 0 := by
  have h := congrFun (congrFun hX j) j
  rw [Matrix.mul_apply, one_apply_eq, ← Finset.add_sum_erase _ _ (mem_univ j)] at h
  simp only [transpose_apply, hj, mul_one] at h
  have h0 : ∑ x ∈ univ.erase j, X j x * X j x = 0 := by linarith
  exact mul_self_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg
    (fun x _ => mul_self_nonneg (X j x))).1 h0 l (mem_erase.2 ⟨hl, mem_univ l⟩))

/-- The plane reflection $R(\varphi_l)$ embedded in the plane $(l, l + 1)$ is an involution. -/
private theorem givensFactor_planeReflector_mul_self (φ : ℕ → ℝ) (l : ℕ) :
    givensFactor N (fun k => planeReflector (φ k)) l *
      givensFactor N (fun k => planeReflector (φ k)) l = 1 := by
  unfold givensFactor
  split_ifs with h
  · rw [planeEmbed_mul_planeEmbed _ (Fin.ne_of_lt (Fin.lt_def.2 (by simp))),
      planeReflector_mul_self, planeEmbed_one (Fin.ne_of_lt (Fin.lt_def.2 (by simp)))]
  · exact Matrix.one_mul 1

/-- The plane reflection $R(\varphi_l)$ embedded in the plane $(l, l + 1)$ is symmetric. -/
private theorem givensFactor_planeReflector_transpose (φ : ℕ → ℝ) (l : ℕ) :
    (givensFactor N (fun k => planeReflector (φ k)) l)ᵀ =
      givensFactor N (fun k => planeReflector (φ k)) l := by
  unfold givensFactor
  split_ifs with h
  · rw [planeEmbed_transpose _ (Fin.ne_of_lt (Fin.lt_def.2 (by simp))),
      planeReflector_transpose]
  · exact transpose_one

/-- The angle of the reflection that clears the subdiagonal entry of column $k$: $\arccos(-x_{kk})$
for $k < N$, and $0$ otherwise. -/
private noncomputable def ohAngle (X : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (k : ℕ) : ℝ :=
  if h : k < N then Real.arccos (-X ⟨k, by omega⟩ ⟨k, by omega⟩) else 0

/-- The reduction of an orthogonal upper Hessenberg matrix by plane reflections from the left, one
column at a time. -/
private noncomputable def ohReduce (H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  | 0 => H
  | k + 1 => givensFactor N (fun _ => planeReflector (ohAngle (ohReduce H k) k)) k * ohReduce H k

/-- The invariant of the reduction after $k$ steps: $X$ is orthogonal and upper Hessenberg, its
subdiagonal entries in the columns $\ge k$ are positive, and $x_{jj} = 1$ for $j < k$. -/
private def OhInv (k : ℕ) (X : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : Prop :=
  X * Xᵀ = 1 ∧ Xᵀ * X = 1 ∧ (∀ i j : Fin (N + 1), (j : ℕ) + 1 < i → X i j = 0) ∧
    (∀ i : Fin N, k ≤ (i : ℕ) → 0 < X i.succ i.castSucc) ∧
    ∀ j : Fin (N + 1), (j : ℕ) < k → X j j = 1

/-- One step of the reduction keeps the invariant, and its angle lies in $(0, \pi)$. -/
private theorem ohInv_step {k : ℕ} (hk : k < N) {X : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hX : OhInv k X) :
    OhInv (k + 1) (givensFactor N (fun _ => planeReflector (ohAngle X k)) k * X) ∧
      0 < ohAngle X k ∧ ohAngle X k < Real.pi := by
  obtain ⟨h1, h2, hH, hpos, hdiag⟩ := hX
  set kk : Fin (N + 1) := ⟨k, by omega⟩ with hkk
  set k1 : Fin (N + 1) := ⟨k + 1, by omega⟩ with hk1
  have hne : kk ≠ k1 := Fin.ne_of_lt (Fin.lt_def.2 (by simp [hkk, hk1]))
  -- the rows `< k` are unit rows, the columns `< k` unit columns
  have hrow : ∀ j : Fin (N + 1), (j : ℕ) < k → ∀ l, l ≠ j → X j l = 0 :=
    fun j hj l hl => apply_eq_zero_of_mul_transpose h1 (hdiag j hj) hl
  have hcol : ∀ j : Fin (N + 1), (j : ℕ) < k → ∀ l, l ≠ j → X l j = 0 := fun j hj l hl => by
    have := apply_eq_zero_of_mul_transpose (X := Xᵀ) (by rwa [transpose_transpose])
      (by rw [transpose_apply]; exact hdiag j hj) hl
    rwa [transpose_apply] at this
  -- column `k` lives on the rows `k`, `k + 1`
  have hb : 0 < X k1 kk := hpos ⟨k, hk⟩ le_rfl
  have hsupp : ∀ i, i ≠ kk → i ≠ k1 → X i kk = 0 := fun i hi hi' => by
    rcases lt_trichotomy (i : ℕ) k with h | h | h
    · exact hrow i h kk (fun e => by rw [← e] at h; simp [hkk] at h)
    · exact absurd (Fin.ext (by simp [hkk, h])) hi
    · have : (i : ℕ) ≠ k + 1 := fun e => hi' (Fin.ext (by rw [e, hk1]))
      exact hH i kk (show k + 1 < (i : ℕ) by omega)
  have hnorm : X kk kk ^ 2 + X k1 kk ^ 2 = 1 := by
    have h := congrFun (congrFun h2 kk) kk
    rw [Matrix.mul_apply, one_apply_eq, ← Finset.sum_subset (Finset.subset_univ {kk, k1})
      (fun i _ hi => by simp only [mem_insert, mem_singleton, not_or] at hi
                        simp [transpose_apply, hsupp i hi.1 hi.2]),
      Finset.sum_pair hne] at h
    simp only [transpose_apply] at h
    nlinarith [h]
  set a := X kk kk with ha
  set b := X k1 kk with hb'
  have ha1 : -1 < -a ∧ -a < 1 := by constructor <;> nlinarith
  have hangle : ohAngle X k = Real.arccos (-a) := by simp [ohAngle, hk, ha, hkk]
  have hcos : Real.cos (ohAngle X k) = -a := by
    rw [hangle, Real.cos_arccos ha1.1.le ha1.2.le]
  have hsin : Real.sin (ohAngle X k) = b := by
    rw [hangle, Real.sin_arccos, neg_sq, show 1 - a ^ 2 = b ^ 2 by linarith,
      Real.sqrt_sq hb.le]
  refine ⟨?_, by rw [hangle]; exact Real.arccos_pos.2 ha1.2,
    by rw [hangle]; exact Real.arccos_lt_pi.2 ha1.1⟩
  set G := givensFactor N (fun _ => planeReflector (ohAngle X k)) k with hG
  have hGe : G = planeEmbed kk k1 (planeReflector (ohAngle X k)) := by
    simp [hG, givensFactor, hk, hkk, hk1]
  have hGG : G * G = 1 := givensFactor_planeReflector_mul_self (fun _ => ohAngle X k) k
  have hGt : Gᵀ = G := givensFactor_planeReflector_transpose (fun _ => ohAngle X k) k
  have happ : ∀ p q, (G * X) p q = if p = kk then a * X kk q + b * X k1 q
      else if p = k1 then b * X kk q - a * X k1 q else X p q := fun p q => by
    rw [hGe, planeEmbed_mul_apply _ hne]
    simp [planeReflector, hcos, hsin, sub_eq_add_neg]
  refine ⟨?_, ?_, fun i j hij => ?_, fun i hi => ?_, fun j hj => ?_⟩
  · rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc X, h1, Matrix.one_mul, hGt, hGG]
  · rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Gᵀ, hGt, hGG, Matrix.one_mul, h2]
  · rw [happ]
    have hj1 : ((j : ℕ) < k) → X k1 j = 0 := fun hjk => hcol j hjk k1
      (fun e => by rw [← e] at hjk; simp [hk1] at hjk)
    split_ifs with hp hp'
    · subst hp
      rw [hH _ _ (by simpa [hkk] using hij), hH _ _ (by simp [hk1]; simp [hkk] at hij; omega)]
      ring
    · subst hp'
      simp only [hk1] at hij
      rw [hcol j (by omega) kk (fun e => by rw [← e] at hij; simp [hkk] at hij),
        hj1 (by omega)]
      ring
    · exact hH i j hij
  · rw [happ]
    have h3 : i.succ ≠ kk := fun e => by
      have := congrArg Fin.val e; simp [hkk] at this; omega
    have h4 : i.succ ≠ k1 := fun e => by
      have := congrArg Fin.val e; simp [hk1] at this; omega
    rw [ite_eq_right h3, ite_eq_right h4]
    exact hpos i (by omega)
  · rw [happ]
    rcases (Nat.lt_succ_iff_lt_or_eq.1 hj) with hj | hj
    · have h3 : j ≠ kk := fun e => by rw [e] at hj; simp [hkk] at hj
      have h4 : j ≠ k1 := fun e => by rw [e] at hj; simp [hk1] at hj
      rw [ite_eq_right h3, ite_eq_right h4]
      exact hdiag j hj
    · obtain rfl : j = kk := Fin.ext hj
      rw [ite_eq_left rfl]
      nlinarith [hnorm]

/-- The reduction after $k$ steps is the product of its first $k$ reflections, in reverse order,
times $H$. -/
private theorem ohReduce_eq (H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (k : ℕ) :
    ohReduce H k = prodRev (givensFactor N fun l => planeReflector (ohAngle (ohReduce H l) l)) k *
      H := by
  induction k with
  | zero => rw [prodRev_zero, Matrix.one_mul]; rfl
  | succ k ih => rw [prodRev_succ, Matrix.mul_assoc, ← ih]; rfl

/-- **Orthogonal upper Hessenberg matrices as products of reflections.** Let
$H \in \mathbb{R}^{(N+1) \times (N+1)}$ be orthogonal and upper Hessenberg, with positive
subdiagonal entries $h_{k+1, k} > 0$ and $\det H = 1$, and let $N + 1$ be even. Then there are
angles $\varphi_k$ with $0 < \varphi_k < \pi$ for $k < N$ such that
$$H = G_0 G_1 \cdots G_{N-1} \operatorname{diag}(1, \dots, 1, -1),$$
where $G_k$ is the reflection $R(\varphi_k) = \begin{bmatrix} -\cos \varphi_k & \sin \varphi_k
\\ \sin \varphi_k & \cos \varphi_k \end{bmatrix}$ in the plane $(k, k + 1)$. This is the product
form (12.2.18) of [golub2013matrix].

The product $G_0 \cdots G_{N-1}$ is `Matrix.givensChain` of the blocks
`Matrix.planeReflector (φ k)`. Reflections from the left clear the subdiagonal one column at a
time; this is the reduction $G_{n-1} \cdots G_1 H = \operatorname{diag}(1, \dots, 1, -c_n)$ of
the source. The positivity of the subdiagonal puts each angle in $(0, \pi)$, and the determinant
fixes the last sign. The source assumes a nonzero subdiagonal "without loss of generality"; the
angles need positivity. -/
theorem exists_orthogonalHessenberg_eq_prod_planeReflector
    {H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hH : H ∈ orthogonalGroup (Fin (N + 1)) ℝ)
    (hHess : H.IsUpperHessenberg) (hsub : ∀ i : Fin N, 0 < H i.succ i.castSucc)
    (hdet : H.det = 1) (heven : Even (N + 1)) :
    ∃ φ : ℕ → ℝ, (∀ k < N, 0 < φ k ∧ φ k < Real.pi) ∧
      H = givensChain N (fun k => planeReflector (φ k)) *
        diagonal fun i : Fin (N + 1) => if (i : ℕ) = N then -1 else 1 := by
  set φ : ℕ → ℝ := fun l => ohAngle (ohReduce H l) l with hφ
  have hinv : ∀ k ≤ N, OhInv k (ohReduce H k) := by
    intro k hk
    induction k with
    | zero =>
      exact ⟨(mem_orthogonalGroup_iff (Fin (N + 1)) ℝ).1 hH,
        (mem_orthogonalGroup_iff' (Fin (N + 1)) ℝ).1 hH,
        (isUpperHessenberg_iff_fin).1 hHess, fun i _ => hsub i, fun j hj => absurd hj (by omega)⟩
    | succ k ih => exact (ohInv_step (by omega) (ih (by omega))).1
  have hangle : ∀ k < N, 0 < φ k ∧ φ k < Real.pi := fun k hk =>
    (ohInv_step hk (hinv k hk.le)).2
  refine ⟨φ, hangle, ?_⟩
  obtain ⟨h1, h2, -, -, hdiag⟩ := hinv N le_rfl
  set X := ohReduce H N with hX
  set G : ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
    givensFactor N fun l => planeReflector (φ l) with hG
  have hGG : ∀ l, G l * G l = 1 := givensFactor_planeReflector_mul_self φ
  have hXe : X = prodRev G N * H := ohReduce_eq H N
  have hHX : H = givensChain N (fun k => planeReflector (φ k)) * X := by
    rw [givensChain, hXe, ← Matrix.mul_assoc, prodFwd_mul_prodRev fun l _ => hGG l, Matrix.one_mul]
  -- `X` is diagonal with last entry `± 1`
  have hXdiag : X = diagonal fun i : Fin (N + 1) => if (i : ℕ) = N then X (Fin.last N) (Fin.last N)
      else 1 := by
    ext i j
    rw [diagonal_apply]
    by_cases hij : i = j
    · subst hij
      by_cases hi : (i : ℕ) = N
      · rw [show i = Fin.last N from Fin.ext hi]
        simp
      · simp [hi, hdiag i (by omega)]
    · rw [ite_eq_right hij]
      by_cases hj : (j : ℕ) < N
      · have := apply_eq_zero_of_mul_transpose (X := Xᵀ) (by rwa [transpose_transpose])
          (by rw [transpose_apply]; exact hdiag j hj) hij
        rwa [transpose_apply] at this
      · have hi : (i : ℕ) < N := by
          by_contra h; exact hij (Fin.ext (by omega))
        exact apply_eq_zero_of_mul_transpose h1 (hdiag i hi) (Ne.symm hij)
  have hdetX : X.det = X (Fin.last N) (Fin.last N) := by
    rw [hXdiag, det_diagonal, Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ↓reduceIte, diagonal_apply_eq]
    rw [Finset.prod_eq_one fun x _ => by simp [x.2.ne], one_mul]
  have hdetG : (givensChain N (fun k => planeReflector (φ k))).det = (-1) ^ N := by
    rw [givensChain, det_prodFwd, Finset.prod_eq_pow_card (b := -1), card_range]
    intro l hl
    rw [givensFactor, dite_eq_left (Finset.mem_range.1 hl),
      det_planeEmbed _ (Fin.ne_of_lt (Fin.lt_def.2 (by simp))), det_planeReflector]
  have hodd : (-1 : ℝ) ^ N = -1 := by
    obtain ⟨t, ht⟩ := heven
    rw [show N = 2 * t - 1 + 0 by omega]
    rcases t with _ | t
    · omega
    · rw [show 2 * (t + 1) - 1 + 0 = 2 * t + 1 by omega, pow_succ, pow_mul]; simp
  have hd : X (Fin.last N) (Fin.last N) = -1 := by
    have := congrArg det hHX
    rw [det_mul, hdetG, hodd, hdetX, hdet] at this
    linarith
  rw [hHX, hXdiag, hd]

end OrthogonalHessenberg

/-! ### Constructing representations: triangular semiseparable and quasiseparable matrices -/

section Construction

variable {n : ℕ}

open Classical in
/-- The factorizations $L[\{i \ge k + \delta\}, \{j \le k\}] = x_k y_k^T$ of the lower blocks of $L$
($\delta = 0$ for the maximal blocks of a semiseparable matrix, $\delta = 1$ for those of a
quasiseparable one), chosen so that consecutive left factors are related by a scalar. -/
private noncomputable def lsState (δ : ℕ) (L : Matrix (Fin n) (Fin n) K) :
    ℕ → (Fin n → K) × (Fin n → K)
  | 0 => (fun i => L i ⟨0, i.pos⟩, fun j : Fin n => if (j : ℕ) = 0 then 1 else 0)
  | k + 1 =>
    if h : ∃ i : Fin n, k + 1 + δ ≤ (i : ℕ) ∧ (lsState δ L k).1 i ≠ 0 then
      ((lsState δ L k).1, fun j => L h.choose j / (lsState δ L k).1 h.choose)
    else
      (fun i => if h' : k + 1 < n then L i ⟨k + 1, h'⟩ else 0,
        fun j : Fin n => if (j : ℕ) = k + 1 then 1 else 0)

open Classical in
/-- The scalar that relates the left factors of the factorizations at $k$ and at $k + 1$: $1$ if the
left factor is kept, and $0$ if the factorization restarts. -/
private noncomputable def lsTransfer (δ : ℕ) (L : Matrix (Fin n) (Fin n) K) (k : ℕ) : K :=
  if ∃ i : Fin n, k + 1 + δ ≤ (i : ℕ) ∧ (lsState δ L k).1 i ≠ 0 then 1 else 0

/-- The factorization at $k$ factors the block $L[\{i \ge k + \delta\}, \{j \le k\}]$, and its right
factor is nonzero at some column $j \le k$. -/
private theorem lsState_spec {δ : ℕ} {L : Matrix (Fin n) (Fin n) K}
    (hL : ∀ k, k < n → (L.toBlock (fun i : Fin n => k + δ ≤ (i : ℕ))
      (fun j : Fin n => (j : ℕ) ≤ k)).rank ≤ 1) (k : ℕ) (hk : k < n) :
    (∀ i j : Fin n, k + δ ≤ (i : ℕ) → (j : ℕ) ≤ k →
      L i j = (lsState δ L k).1 i * (lsState δ L k).2 j) ∧
      ∃ j : Fin n, (j : ℕ) ≤ k ∧ (lsState δ L k).2 j ≠ 0 := by
  induction k with
  | zero =>
    refine ⟨fun i j _ hj => ?_, ⟨⟨0, hk⟩, le_rfl, by simp [lsState]⟩⟩
    obtain rfl : j = ⟨0, i.pos⟩ := Fin.ext (Nat.le_zero.1 hj)
    simp [lsState]
  | succ k ih =>
    obtain ⟨hI, j₀, hj₀, hy₀⟩ := ih (by omega)
    by_cases h : ∃ i : Fin n, k + 1 + δ ≤ (i : ℕ) ∧ (lsState δ L k).1 i ≠ 0
    · have hs : lsState δ L (k + 1) = ((lsState δ L k).1,
          fun j => L h.choose j / (lsState δ L k).1 h.choose) := by
        rw [lsState, dite_eq_left h]
      obtain ⟨hi₀k, hx₀⟩ := h.choose_spec
      set i₀ := h.choose
      rw [hs]
      dsimp only
      -- the `2 × 2` minors of the block at `k + 1` vanish
      have hminor : ∀ i j : Fin n, k + 1 + δ ≤ (i : ℕ) → (j : ℕ) ≤ k + 1 →
          L i j * L i₀ j₀ = L i j₀ * L i₀ j := fun i j hi hj => by
        have hblk := hL (k + 1) hk
        by_contra hne
        have := card_le_rank_of_det_submatrix_ne_zero
          (A := L.toBlock (fun i : Fin n => k + 1 + δ ≤ (i : ℕ)) (fun j : Fin n => (j : ℕ) ≤ k + 1))
          (r := ![⟨i, hi⟩, ⟨i₀, hi₀k⟩]) (c := ![⟨j, hj⟩, ⟨j₀, by omega⟩])
          (by rw [det_fin_two]; simpa [sub_eq_zero] using hne)
        omega
      refine ⟨fun i j hi hj => ?_, ⟨j₀, by omega, ?_⟩⟩
      · have e := hminor i j hi hj
        rw [hI i j₀ (by omega) hj₀, hI i₀ j₀ (by omega) hj₀] at e
        rw [eq_comm, mul_div_assoc', div_eq_iff hx₀]
        exact mul_right_cancel₀ hy₀ (by linear_combination -e)
      · rw [hI i₀ j₀ (by omega) hj₀, mul_div_cancel_left₀ _ hx₀]
        exact hy₀
    · have hs : lsState δ L (k + 1) = (fun i => if h' : k + 1 < n then L i ⟨k + 1, h'⟩ else 0,
          fun j : Fin n => if (j : ℕ) = k + 1 then 1 else 0) := by
        rw [lsState, dite_eq_right h]
      rw [hs]
      dsimp only
      refine ⟨fun i j hi hj => ?_, ⟨⟨k + 1, hk⟩, le_rfl, by simp⟩⟩
      rcases (Nat.lt_or_eq_of_le hj) with hj | hj
      · have hx : (lsState δ L k).1 i = 0 := by
          by_contra hne; exact h ⟨i, hi, hne⟩
        rw [hI i j (by omega) (by omega), hx]
        simp [show (j : ℕ) ≠ k + 1 by omega]
      · obtain rfl : j = ⟨k + 1, hk⟩ := Fin.ext hj
        simp [hk]

/-- On the rows $i \ge k + 1 + \delta$, the left factor at $k$ is the transfer scalar times the left
factor at $k + 1$. -/
private theorem lsState_fst_eq (δ : ℕ) (L : Matrix (Fin n) (Fin n) K) {k : ℕ} (i : Fin n)
    (hi : k + 1 + δ ≤ (i : ℕ)) :
    (lsState δ L k).1 i = lsTransfer δ L k * (lsState δ L (k + 1)).1 i := by
  by_cases h : ∃ i : Fin n, k + 1 + δ ≤ (i : ℕ) ∧ (lsState δ L k).1 i ≠ 0
  · rw [lsTransfer, ite_eq_left h, one_mul]
    conv_rhs => rw [lsState, dite_eq_left h]
  · rw [lsTransfer, ite_eq_right h, zero_mul]
    by_contra hne
    exact h ⟨i, hi, hne⟩

/-- The left factor at $j$ is the left factor at $i - \delta$ times the transfer scalars in between.
-/
private theorem lsState_fst_eq_prod (δ : ℕ) (L : Matrix (Fin n) (Fin n) K) (i : Fin n) {j : ℕ}
    (hji : j ≤ (i : ℕ) - δ) (hδ : δ ≤ (i : ℕ)) :
    (lsState δ L j).1 i =
      (∏ l ∈ Finset.Ico j ((i : ℕ) - δ), lsTransfer δ L l) * (lsState δ L ((i : ℕ) - δ)).1 i := by
  induction hji using Nat.decreasingInduction with
  | self => simp
  | of_succ j hj ih =>
    rw [lsState_fst_eq δ L i (by omega), ih, Finset.prod_eq_prod_Ico_succ_bot hj]
    ring

/-- If every block $L[\{i \ge k + \delta\}, \{j \le k\}]$ has rank at most one, then $l_{ij} = u_i
\, t_j \cdots t_{i-\delta-1} \, v_j$ for $j + \delta \le i$. -/
private theorem apply_eq_of_lsState {δ : ℕ} {L : Matrix (Fin n) (Fin n) K}
    (hL : ∀ k, k < n → (L.toBlock (fun i : Fin n => k + δ ≤ (i : ℕ))
      (fun j : Fin n => (j : ℕ) ≤ k)).rank ≤ 1) {i j : Fin n} (hji : (j : ℕ) + δ ≤ i) :
    L i j = (lsState δ L ((i : ℕ) - δ)).1 i *
      (∏ l ∈ Finset.Ico (j : ℕ) ((i : ℕ) - δ), lsTransfer δ L l) * (lsState δ L j).2 j := by
  rw [(lsState_spec hL j j.2).1 i j hji le_rfl, lsState_fst_eq_prod δ L i (by omega) (by omega)]
  ring

/-- **Triangular semiseparable matrices.** Let $L \in K^{n \times n}$ be lower triangular and
semiseparable. Then there are $u, v \in K^n$ and a sequence $t$ in $K$ with
$$L = \mathbf{S}(u, v, t, u \circ v, 0, 0, 0) = \operatorname{tril}(uv^T) \circ B(t)^{-T}.$$
This is the representation of [golub2013matrix] §12.2.4.

The lower maximal blocks $L[\{i \ge k\}, \{j \le k\}] = x_k y_k^T$ are factored so that
$x_k = t_k x_{k+1}$ below the row $k$: the left factor is kept when it does not vanish there,
and otherwise the factorization restarts from the column $k + 1$ with $t_k = 0$. Then $u_i$ is
the entry $i$ of $x_i$, and $v_j$ is the entry $j$ of $y_j$. -/
theorem exists_lower_semiseparable_rep {L : Matrix (Fin n) (Fin n) K} (hL : L.IsSemiseparable)
    (hlow : L.IsLowerTriangular) :
    ∃ (u v : Fin n → K) (t : ℕ → K), L = quasiseparableOf u v t (u * v) 0 0 0 := by
  have hL' : ∀ k, k < n → (L.toBlock (fun i : Fin n => k + 0 ≤ (i : ℕ))
      (fun j : Fin n => (j : ℕ) ≤ k)).rank ≤ 1 := fun k hk =>
    (rank_toBlock_mono L (p' := (⟨k, hk⟩ ≤ ·)) (q' := (· ≤ ⟨k, hk⟩))
      (fun i hi => Fin.le_def.2 (by simpa using hi)) fun j hj => Fin.le_def.2 hj).trans
      (hL ⟨k, hk⟩).1
  refine ⟨fun i => (lsState 0 L i).1 i, fun j => (lsState 0 L j).2 j, lsTransfer 0 L, ?_⟩
  ext i j
  rw [quasiseparableOf_apply]
  split_ifs with hji hij
  · rw [apply_eq_of_lsState hL' (by simpa using Fin.le_def.1 hji.le)]
    simp only [Nat.sub_zero]
  · subst hij
    rw [apply_eq_of_lsState hL' (by simp)]
    simp
  · simp only [Pi.zero_apply, zero_mul]
    exact hlow (OrderDual.toDual_lt_toDual.2 (lt_of_le_of_ne (not_lt.1 hji) hij))

/-- **Upper triangular semiseparable matrices.** Let $U \in K^{n \times n}$ be upper triangular and
semiseparable. Then there are $p, q \in K^n$ and a sequence $r$ in $K$ with
$$U = \mathbf{S}(0, 0, 0, p \circ q, p, q, r) = \operatorname{triu}(pq^T) \circ B(r)^{-1}.$$
This is the representation of [golub2013matrix] §12.2.4.

The proof is by transposition from `Matrix.exists_lower_semiseparable_rep`. -/
theorem exists_upper_semiseparable_rep {U : Matrix (Fin n) (Fin n) K} (hU : U.IsSemiseparable)
    (hup : U.IsUpperTriangular) :
    ∃ (p q : Fin n → K) (r : ℕ → K), U = quasiseparableOf 0 0 0 (p * q) p q r := by
  obtain ⟨u, v, t, h⟩ := exists_lower_semiseparable_rep hU.transpose
    (fun i j hij => hup (OrderDual.toDual_lt_toDual.1 hij))
  refine ⟨v, u, t, ?_⟩
  rw [← transpose_transpose U, h, transpose_quasiseparableOf, mul_comm u v]

/-- If every block $A[\{i > k\}, \{j \le k\}]$ has rank at most one, then there are $u, v$ and $t$
with $a_{ij} = u_i \, t_{j+1} \cdots t_{i-1} \, v_j$ for $j < i$. -/
private theorem exists_lower_quasiseparableRep {A : Matrix (Fin n) (Fin n) K}
    (hA : ∀ k : Fin n, (A.toBlock (k < ·) (· ≤ k)).rank ≤ 1) :
    ∃ (u v : Fin n → K) (t : ℕ → K), ∀ i j : Fin n, j < i →
      A i j = u i * (∏ l ∈ Finset.Ico ((j : ℕ) + 1) i, t l) * v j := by
  have hA' : ∀ k, k < n → (A.toBlock (fun i : Fin n => k + 1 ≤ (i : ℕ))
      (fun j : Fin n => (j : ℕ) ≤ k)).rank ≤ 1 := fun k hk =>
    (rank_toBlock_mono A (p' := (⟨k, hk⟩ < ·)) (q' := (· ≤ ⟨k, hk⟩))
      (fun i hi => Fin.lt_def.2 hi) fun j hj => Fin.le_def.2 hj).trans (hA ⟨k, hk⟩)
  refine ⟨fun i => (lsState 1 A ((i : ℕ) - 1)).1 i, fun j => (lsState 1 A j).2 j,
    fun l => lsTransfer 1 A (l - 1), fun i j hji => ?_⟩
  have hji' : (j : ℕ) + 1 ≤ i := Fin.lt_def.1 hji
  rw [apply_eq_of_lsState hA' hji']
  congr 2
  have := Finset.prod_Ico_add' (fun l => lsTransfer 1 A (l - 1)) (j : ℕ) ((i : ℕ) - 1) 1
  simp only [Nat.add_sub_cancel] at this
  rw [this, Nat.sub_add_cancel (by omega)]

/-- **Every quasiseparable matrix has a quasiseparable representation.** A matrix
$A \in K^{n \times n}$ is quasiseparable if and only if
$$A = \widetilde{\mathbf{S}}(u, v, t, d, p, q, r)$$
for some $u, v, d, p, q \in K^n$ and sequences $t$, $r$ in $K$. This is the corrected form of
the claim of [golub2013matrix] §12.2.3, for the representation of Eidelman and Gohberg.

The strictly lower maximal blocks $A[\{i > k\}, \{j \le k\}] = x_k y_k^T$ are factored so that
consecutive left factors differ by a scalar $t_{k+1}$ on the rows of the next block. Then $u_i$
is the entry $i$ of $x_{i-1}$, and $v_j$ is the entry $j$ of $y_j$. The upper part follows by
transposition. No division by generators is needed. -/
theorem exists_quasiseparableRep {A : Matrix (Fin n) (Fin n) K} :
    A.IsQuasiseparable ↔ ∃ (u v : Fin n → K) (t : ℕ → K) (d p q : Fin n → K) (r : ℕ → K),
      A = quasiseparableRep u v t d p q r := by
  refine ⟨fun hA => ?_, fun ⟨u, v, t, d, p, q, r, h⟩ => h ▸
    isQuasiseparable_quasiseparableRep u v t d p q r⟩
  obtain ⟨u, v, t, hl⟩ := exists_lower_quasiseparableRep fun k => (hA k).1
  obtain ⟨q, p, r, hu⟩ := exists_lower_quasiseparableRep (A := Aᵀ) fun k => (hA.transpose k).1
  refine ⟨u, v, t, fun i => A i i, p, q, r, ?_⟩
  ext i j
  rw [quasiseparableRep_apply]
  split_ifs with hji hij
  · exact hl i j hji
  · subst hij; rfl
  · have hij' : i < j := lt_of_le_of_ne (not_lt.1 hji) hij
    rw [← transpose_apply A j i, hu j i hij']
    ring

end Construction

/-! ### The QR factorization of a triangular semiseparable matrix -/

section SemiseparableQR

variable {N : ℕ} {c s : ℕ → K}

/-- The cosines $c'_k$ of a Givens-vector representation: $c'_N = 1$, and $c'_k = c_k$ for
$k \neq N$. -/
private def gvCos (N : ℕ) (c : ℕ → K) (k : ℕ) : K := if k = N then 1 else c k

/-- If $c_k^2 + s_k^2 = 1$ for all $k$ and $a \le N$, then $\sum_{k=a}^{N} (s_a \cdots s_{k-1})^2 \,
c_k'^2 = 1$. -/
private theorem sum_sq_prod_mul_gvCos_sq (hcs : ∀ k, c k ^ 2 + s k ^ 2 = 1) {a : ℕ} (ha : a ≤ N) :
    ∑ k ∈ Finset.Ico a (N + 1), (∏ l ∈ Finset.Ico a k, s l) ^ 2 * gvCos N c k ^ 2 = 1 := by
  induction ha using Nat.decreasingInduction with
  | self => simp [gvCos]
  | of_succ a ha ih =>
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.Ico_self, prod_empty,
      Finset.sum_congr rfl fun k hk => by
        rw [Finset.prod_eq_prod_Ico_succ_bot (Finset.mem_Ico.1 hk).1, mul_pow, mul_assoc],
      ← Finset.mul_sum, ih, gvCos, ite_eq_right (by omega)]
    linear_combination hcs a

/-- If $G$ is a chain of $2 \times 2$ blocks and $g_{ik} \, l_{kj} = F_k$ for every $k$, then
$(GL)_{ij} = \sum_{k=0}^{N} F_k$. -/
private theorem givensChain_mul_apply (M : ℕ → Matrix (Fin 2) (Fin 2) K)
    (L : Matrix (Fin (N + 1)) (Fin (N + 1)) K) (F : ℕ → K) (i j : Fin (N + 1))
    (hF : ∀ k : Fin (N + 1), givensChain N M i k * L k j = F k) :
    (givensChain N M * L) i j = ∑ k ∈ Finset.range (N + 1), F k := by
  rw [Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun k _ => hF k

/-- **The QR factorization of a lower triangular semiseparable matrix.** Let $c$ and $s$ be
sequences in $K$ with $c_k^2 + s_k^2 = 1$ for all $k$, let $v \in K^{N+1}$, and let
$A \in K^{(N+1) \times (N+1)}$ satisfy
$$a_{ij} = c'_i \, s_j \cdots s_{i-1} \, v_j \quad (j \le i),$$
with $c'_i = c_i$ for $i < N$ and $c'_N = 1$. Let $Q^T$ be the chain $G_0 \cdots G_{N-1}$ of the
rotations $\begin{bmatrix} c_k & s_k \\ -s_k & c_k \end{bmatrix}$. Then
$$Q^T \operatorname{tril}(A) = \bigl((\mathcal{D} c) \, v^T\bigr) \circ B(s)^{-1}, \qquad
  (\mathcal{D} c)_0 = 1, \ (\mathcal{D} c)_{i+1} = c_i,$$
and $Q^T \operatorname{triu}(A, 1)$ is upper triangular. Hence $Q^T A$ is upper triangular. This
is (12.2.14) and P12.2.9 of [golub2013matrix].

Here $\operatorname{tril}(A)$ is `strictLower A + diagPart A` and $\operatorname{triu}(A, 1)$ is
`Matrix.strictUpper A`. The rotation weights telescope: $\sum_{k \ge a} (s_a \cdots s_{k-1})^2
c_k'^2 = 1$. The second part holds because $Q^T$ is upper Hessenberg. -/
theorem givensChain_mul_strictLower_add_diagPart
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) K} (hcs : ∀ k, c k ^ 2 + s k ^ 2 = 1)
    {v : Fin (N + 1) → K}
    (hA : ∀ i j : Fin (N + 1), j ≤ i →
      A i j = (if (i : ℕ) = N then 1 else c i) * (∏ l ∈ Finset.Ico (j : ℕ) i, s l) * v j) :
    givensChain N (fun k => !![c k, s k; -s k, c k]) * (strictLower A + diagPart A) =
        vecMulVec (fun i : Fin (N + 1) => if (i : ℕ) = 0 then 1 else c (i - 1)) v ⊙
          (unitBidiagonal (N + 1) s)⁻¹ ∧
      (givensChain N (fun k => !![c k, s k; -s k, c k]) * strictUpper A).IsUpperTriangular := by
  set M : ℕ → Matrix (Fin 2) (Fin 2) K := fun k => !![c k, s k; -s k, c k] with hM
  set P : ℕ → ℕ → K := fun a b => ∏ l ∈ Finset.Ico a b, s l with hP
  set h : ℕ → K := fun i => if i = 0 then 1 else c (i - 1) with hh
  refine ⟨?_, fun i j (hji : j < i) => ?_⟩
  · ext i j
    have hL : ∀ k : Fin (N + 1), (strictLower A + diagPart A) k j =
        if (j : ℕ) ≤ k then gvCos N c k * P j k * v j else 0 := fun k => by
      rw [Matrix.add_apply, strictLower_apply, diagPart_apply]
      rcases lt_trichotomy j k with hjk | hjk | hjk
      · rw [ite_eq_left hjk, ite_eq_right hjk.ne', add_zero, hA k j hjk.le,
          ite_eq_left (Fin.le_def.1 hjk.le)]
        rfl
      · subst hjk
        simp only [lt_irrefl, ↓reduceIte, zero_add, le_refl]
        rw [hA _ _ le_rfl]
        rfl
      · rw [ite_eq_right (not_lt.2 hjk.le), ite_eq_right hjk.ne, add_zero,
          ite_eq_right (not_le.2 (Fin.lt_def.1 hjk))]
    have hG : ∀ k : Fin (N + 1), givensChain N M i k = if (i : ℕ) = k + 1 then -s k
        else if (i : ℕ) ≤ k then h i * P i k * gvCos N c k else 0 := fun k => by
      rw [givensChain_apply]
      simp [hM, hh, hP, gvCos]
    rw [givensChain_mul_apply M _ (fun k => (if (i : ℕ) = k + 1 then -s k
        else if (i : ℕ) ≤ k then h i * P i k * gvCos N c k else 0) *
        (if (j : ℕ) ≤ k then gvCos N c k * P j k * v j else 0)) i j
      (fun k => by rw [hG, hL])]
    have hj := Nat.le_of_lt_succ j.2
    have hi := Nat.le_of_lt_succ i.2
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le j) (by omega : (j : ℕ) ≤ N + 1),
      Finset.sum_eq_zero fun k hk => by
        rw [ite_eq_right (not_le.2 (Finset.mem_Ico.1 hk).2), mul_zero], zero_add]
    simp only [hadamard_apply, vecMulVec_apply, inv_unitBidiagonal, of_apply]
    by_cases hij : i ≤ j
    · have hij' : (i : ℕ) ≤ j := Fin.le_def.1 hij
      rw [ite_eq_left hij, Finset.sum_congr rfl (g := fun k =>
          (h i * (∏ l ∈ Finset.Ico (i : ℕ) j, s l) * v j) *
            ((∏ l ∈ Finset.Ico (j : ℕ) k, s l) ^ 2 * gvCos N c k ^ 2)) fun k hk => by
        have hk' := (Finset.mem_Ico.1 hk).1
        rw [ite_eq_right (show ¬ (i : ℕ) = k + 1 by omega),
          ite_eq_left (show (i : ℕ) ≤ k by omega), ite_eq_left hk', hP]
        dsimp only
        rw [← prod_Ico_consecutive s hij' hk']
        ring,
        ← Finset.mul_sum, sum_sq_prod_mul_gvCos_sq hcs hj, mul_one, hh]
      dsimp only
      ring
    · have hji' : (j : ℕ) < i := by rw [Fin.le_def] at hij; omega
      rw [ite_eq_right hij, mul_zero]
      obtain ⟨m, hm⟩ : ∃ m, (i : ℕ) = m + 1 := ⟨i - 1, by omega⟩
      rw [← Finset.sum_Ico_consecutive _ (by omega : (j : ℕ) ≤ m) (by omega : m ≤ N + 1),
        Finset.sum_eq_zero fun k hk => by
          have := Finset.mem_Ico.1 hk
          rw [ite_eq_right (show ¬ (i : ℕ) = k + 1 by omega),
            ite_eq_right (show ¬ (i : ℕ) ≤ k by omega), zero_mul], zero_add,
        Finset.sum_eq_sum_Ico_succ_bot (by omega),
        ite_eq_left (show (i : ℕ) = m + 1 from hm), ite_eq_left (show (j : ℕ) ≤ m by omega), ← hm,
        Finset.sum_congr rfl (g := fun k =>
          (h i * (∏ l ∈ Finset.Ico (j : ℕ) i, s l) * v j) *
            ((∏ l ∈ Finset.Ico (i : ℕ) k, s l) ^ 2 * gvCos N c k ^ 2)) fun k hk => by
          have hk' := (Finset.mem_Ico.1 hk).1
          rw [ite_eq_right (show ¬ (i : ℕ) = k + 1 by omega),
            ite_eq_left (show (i : ℕ) ≤ k by omega), ite_eq_left (show (j : ℕ) ≤ k by omega), hP]
          dsimp only
          rw [← prod_Ico_consecutive s hji'.le hk']
          ring,
        ← Finset.mul_sum, sum_sq_prod_mul_gvCos_sq hcs hi, mul_one]
      simp only [hh, hP, gvCos, show m ≠ N by omega, ↓reduceIte, hm, Nat.add_sub_cancel,
        Nat.add_one_ne_zero]
      rw [Finset.prod_Ico_succ_top (by omega : (j : ℕ) ≤ m)]
      ring
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [strictUpper_apply]
    by_cases hkj : k < j
    · rw [(isUpperHessenberg_iff_fin.1 givensChain_isUpperHessenberg) i k
        (by rw [Fin.lt_def] at hkj hji; omega), zero_mul]
    · rw [ite_eq_right hkj, mul_zero]

end SemiseparableQR

/-! ### Products along a path: the odd–even splitting -/

section OddEven

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- After $m$ steps of the reordering, $g_0 \cdots g_{n-1}$ is similar to the product of the
even-indexed factors among the first $m$, times the product of the odd-indexed ones among them,
times $g_m \cdots g_{n-1}$. -/
private theorem isSimilar_prodFwd_evenOdd_aux {g : ℕ → Matrix ι ι R} {n : ℕ}
    (hcomm : ∀ k l, k + 2 ≤ l → l < n → Commute (g k) (g l)) (hunit : ∀ k, IsUnit (g k))
    {m : ℕ} (hm : m ≤ n) :
    IsSimilar (prodFwd g n)
      (prodFwdEven g m * prodFwdOdd g m * prodFwd (fun k => g (m + k)) (n - m)) := by
  induction m with
  | zero => simpa [prodFwdEven, prodFwdOdd] using IsSimilar.refl (prodFwd g n)
  | succ m ih =>
    refine (ih (by omega)).trans ?_
    obtain ⟨R', hR'⟩ : ∃ R', R' = prodFwd (fun k => g (m + 1 + k)) (n - (m + 1)) := ⟨_, rfl⟩
    have hsplit : prodFwd (fun k => g (m + k)) (n - m) = g m * R' := by
      rw [show n - m = n - (m + 1) + 1 by omega, prodFwd_succ', add_zero, hR']
      congr 2
      funext k
      congr 1
      omega
    have hRu : IsUnit R' := hR' ▸ isUnit_prodFwd fun k _ => hunit _
    have hRcomm : ∀ y : Matrix ι ι R, (∀ l, m + 1 ≤ l → l < n → Commute (g l) y) →
        Commute R' y := fun y hy => by
      rw [hR']
      exact commute_prodFwd fun k hk => hy _ (by omega) (by omega)
    rw [hsplit]
    rcases Nat.even_or_odd m with hev | hodd
    · rcases Nat.eq_zero_or_pos m with rfl | hpos
      · rw [hR']
        simp [prodFwdEven, prodFwdOdd, prodFwd_succ, IsSimilar.refl]
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨s', hs'⟩ : Odd m' := by
        rcases Nat.even_or_odd m' with h | h
        · exact absurd hev (by simpa [Nat.even_add_one] using h)
        · exact h
      have hodd' : Odd m' := ⟨s', hs'⟩
      obtain ⟨X, hX⟩ : ∃ X, X = prodFwdEven g (m' + 1) * prodFwdOdd g m' := ⟨_, rfl⟩
      have hO : prodFwdOdd g (m' + 1) = prodFwdOdd g m' * g m' := by
        rw [prodFwdOdd, prodFwd_succ, ite_eq_left hodd']
        rfl
      have hE : prodFwdEven g (m' + 1 + 1) = prodFwdEven g (m' + 1) * g (m' + 1) := by
        rw [prodFwdEven, prodFwd_succ, ite_eq_left hev]
        rfl
      have hO' : prodFwdOdd g (m' + 1 + 1) = prodFwdOdd g (m' + 1) := by
        rw [prodFwdOdd, prodFwd_succ, ite_eq_right (Nat.not_odd_iff_even.2 hev), Matrix.mul_one]
        rfl
      have hEcomm : ∀ l, m' + 1 ≤ l → l < n → Commute (prodFwdEven g (m' + 1)) (g l) :=
        fun l hl hln => commute_prodFwd fun k hk => by
          split_ifs with hk'
          · obtain ⟨t, rfl⟩ := hk'
            exact hcomm _ l (by omega) hln
          · exact Commute.one_left _
      have hOcomm : ∀ l, m' + 1 ≤ l → l < n → Commute (prodFwdOdd g m') (g l) :=
        fun l hl hln => commute_prodFwd fun k hk => by
          split_ifs with hk'
          · exact hcomm _ l (by omega) hln
          · exact Commute.one_left _
      have hXl : ∀ l, m' + 1 ≤ l → l < n → Commute X (g l) := fun l hl hln =>
        hX ▸ (hEcomm l hl hln).mul_left (hOcomm l hl hln)
      have hXg : Commute X (g (m' + 1)) := hXl _ le_rfl (by omega)
      have hXR : Commute X R' :=
        (hRcomm X fun l hl hln => (hXl l (by omega) hln).symm).symm
      have hgR : Commute (g m') R' :=
        (hRcomm _ fun l hl hln => (hcomm m' l (by omega) hln).symm).symm
      have hOg : Commute (prodFwdOdd g m') (g (m' + 1)) := hOcomm _ le_rfl (by omega)
      have hsrc : prodFwdEven g (m' + 1) * prodFwdOdd g (m' + 1) * (g (m' + 1) * R') =
          (X * g m') * (g (m' + 1) * R') := by
        rw [hO, hX]
        simp only [Matrix.mul_assoc]
      have htgt : (g (m' + 1) * R') * (X * g m') = prodFwdEven g (m' + 1 + 1) *
          prodFwdOdd g (m' + 1 + 1) * R' := by
        calc (g (m' + 1) * R') * (X * g m') = g (m' + 1) * ((R' * X) * g m') := by
              simp only [Matrix.mul_assoc]
          _ = g (m' + 1) * ((X * R') * g m') := by rw [← hXR.eq]
          _ = (g (m' + 1) * X) * (R' * g m') := by simp only [Matrix.mul_assoc]
          _ = (X * g (m' + 1)) * (g m' * R') := by rw [← hXg.eq, ← hgR.eq]
          _ = prodFwdEven g (m' + 1) * (prodFwdOdd g m' * g (m' + 1)) * (g m' * R') := by
              rw [hX]
              simp only [Matrix.mul_assoc]
          _ = prodFwdEven g (m' + 1) * (g (m' + 1) * prodFwdOdd g m') * (g m' * R') := by
              rw [hOg.eq]
          _ = _ := by
              rw [hE, hO', hO]
              simp only [Matrix.mul_assoc]
      rw [hsrc, ← hR', ← htgt]
      exact isSimilar_mul_comm_of_isUnit ((hunit _).mul hRu)
    · have hE : prodFwdEven g (m + 1) = prodFwdEven g m := by
        rw [prodFwdEven, prodFwd_succ, ite_eq_right (Nat.not_even_iff_odd.2 hodd), Matrix.mul_one]
        rfl
      have hO : prodFwdOdd g (m + 1) = prodFwdOdd g m * g m := by
        rw [prodFwdOdd, prodFwd_succ, ite_eq_left hodd]
        rfl
      rw [hE, hO, ← hR']
      simp only [Matrix.mul_assoc]
      exact IsSimilar.refl _

/-- **Products of the generators of a path in two orders are similar.** Let $R$ be a commutative
ring, and let $g_0, g_1, \dots$ be invertible square matrices over $R$ such that $g_k$ and $g_l$
commute whenever $k + 2 \le l < n$. Then
$$g_0 g_1 \cdots g_{n-1} \quad \text{is similar to} \quad \Bigl(\prod_{k < n, \ k \text{ even}}
  g_k\Bigr) \Bigl(\prod_{k < n, \ k \text{ odd}} g_k\Bigr),$$
where each product is taken in increasing order of $k$. This is the Coxeter-element argument
behind Fact 1 of [golub2013matrix] §12.2.10.

The two products are `prodFwdEven g n` and `prodFwdOdd g n`. The proof is by induction on the
number of factors already split. An odd-indexed factor joins the odd product in place, and an
even-indexed one moves past the odd factor before it by a cyclic shift $PQ \sim QP$. -/
theorem isSimilar_prodFwd_evenOdd {g : ℕ → Matrix ι ι R} {n : ℕ}
    (hcomm : ∀ k l, k + 2 ≤ l → l < n → Commute (g k) (g l)) (hunit : ∀ k, IsUnit (g k)) :
    IsSimilar (prodFwd g n) (prodFwdEven g n * prodFwdOdd g n) := by
  simpa using isSimilar_prodFwd_evenOdd_aux hcomm hunit (le_refl n)

end OddEven

/-! ### The odd–even factorization of an orthogonal Hessenberg matrix -/

section ReflectorProduct

variable {N : ℕ}

/-- Let $N \in \mathbb{N}$ and let $\varphi$ be a sequence of reals. The **factors of the product
form** (12.2.18) of [golub2013matrix] are the matrices
$G_k \in \mathbb{R}^{(N+1) \times (N+1)}$, where $G_k$ is the plane reflection $R(\varphi_k)$ in
the plane $(k, k + 1)$ for $k < N$, and $G_k = \operatorname{diag}(1, \dots, 1, -1)$ for
$k \ge N$.

Only $G_0, \dots, G_N$ enter the product (12.2.18). The reflection $R(\varphi)$ is
`Matrix.planeReflector φ`. -/
noncomputable def reflectorFactor (N : ℕ) (φ : ℕ → ℝ) (k : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  if k < N then givensFactor N (fun l => planeReflector (φ l)) k
  else diagonal fun i => if (i : ℕ) = N then -1 else 1

/-- For every sequence $\varphi$, the product form (12.2.18) is the product of its $N + 1$ factors:
$$G_0 G_1 \cdots G_{N-1} \operatorname{diag}(1, \dots, 1, -1) = G_0 G_1 \cdots G_N,$$
where on the left the first $N$ factors form the chain of the blocks $R(\varphi_k)$, and on the
right the $G_k$ are `Matrix.reflectorFactor N φ k`. -/
theorem givensChain_mul_diagonal_eq_prodFwd (φ : ℕ → ℝ) :
    givensChain N (fun k => planeReflector (φ k)) *
        diagonal (fun i : Fin (N + 1) => if (i : ℕ) = N then -1 else 1) =
      prodFwd (reflectorFactor N φ) (N + 1) := by
  rw [prodFwd_succ, givensChain, reflectorFactor, ite_eq_right (lt_irrefl N)]
  congr 1
  exact prodFwd_congr fun k hk => by rw [reflectorFactor, ite_eq_left hk]

/-- Every factor $G_k$ of (12.2.18) is an involution: $G_k^2 = I$. -/
theorem reflectorFactor_mul_self (φ : ℕ → ℝ) (k : ℕ) :
    reflectorFactor N φ k * reflectorFactor N φ k = 1 := by
  unfold reflectorFactor
  split_ifs with h
  · exact givensFactor_planeReflector_mul_self φ k
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    split_ifs <;> norm_num

/-- Every factor $G_k$ of (12.2.18) is symmetric. -/
theorem reflectorFactor_transpose (φ : ℕ → ℝ) (k : ℕ) :
    (reflectorFactor N φ k)ᵀ = reflectorFactor N φ k := by
  unfold reflectorFactor
  split_ifs
  · exact givensFactor_planeReflector_transpose φ k
  · exact diagonal_transpose _

/-- Every factor $G_k$ of (12.2.18) is orthogonal, as a symmetric involution. -/
theorem reflectorFactor_mem_orthogonalGroup (φ : ℕ → ℝ) (k : ℕ) :
    reflectorFactor N φ k ∈ orthogonalGroup (Fin (N + 1)) ℝ := by
  rw [mem_orthogonalGroup_iff, reflectorFactor_transpose, reflectorFactor_mul_self]

/-- Every factor $G_k$ of (12.2.18) has determinant $-1$: it is a plane reflection or
$\operatorname{diag}(1, \dots, 1, -1)$. -/
theorem det_reflectorFactor (φ : ℕ → ℝ) (k : ℕ) :
    (reflectorFactor N φ k).det = -1 := by
  unfold reflectorFactor
  split_ifs with h
  · rw [givensFactor, dite_eq_left h, det_planeEmbed _ (Fin.ne_of_lt (Fin.lt_def.2 (by simp))),
      det_planeReflector]
  · rw [det_diagonal, Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ↓reduceIte]
    rw [Finset.prod_eq_one fun x _ => by simp [x.2.ne], one_mul]

/-- For every $r \in \mathbb{N}$, the product $G_0 \cdots G_{r-1}$ of factors of (12.2.18) is
orthogonal, as a product of orthogonal factors. -/
theorem prodFwd_reflectorFactor_mem_orthogonalGroup (φ : ℕ → ℝ) (r : ℕ) :
    prodFwd (reflectorFactor N φ) r ∈ orthogonalGroup (Fin (N + 1)) ℝ :=
  prodFwd_mem_orthogonalGroup fun k _ => reflectorFactor_mem_orthogonalGroup φ k

/-- The product $G_0 \cdots G_N$ of (12.2.18) has determinant $(-1)^{N+1}$, since each of its
$N + 1$ factors has determinant $-1$. -/
theorem det_prodFwd_reflectorFactor (φ : ℕ → ℝ) :
    (prodFwd (reflectorFactor N φ) (N + 1)).det = (-1) ^ (N + 1) := by
  rw [det_prodFwd, Finset.prod_eq_pow_card (b := -1), card_range]
  exact fun k _ => det_reflectorFactor φ k

/-- If $N + 1 = 2m$ is even, then the product $G_0 \cdots G_N$ of (12.2.18) is special orthogonal:
it is orthogonal with determinant $1$.

This is the hypothesis of (12.2.19) of [golub2013matrix], which is
`Matrix.exists_charpoly_eq_prod_of_mem_specialOrthogonalGroup`. -/
theorem prodFwd_reflectorFactor_mem_specialOrthogonalGroup (φ : ℕ → ℝ) {m : ℕ}
    (hN : N + 1 = 2 * m) :
    prodFwd (reflectorFactor N φ) (N + 1) ∈ specialOrthogonalGroup (Fin (N + 1)) ℝ := by
  refine mem_specialOrthogonalGroup_iff.2 ⟨prodFwd_reflectorFactor_mem_orthogonalGroup φ _, ?_⟩
  rw [det_prodFwd_reflectorFactor, hN, pow_mul]
  norm_num

/-- For every sequence $\varphi$, the product $H = G_0 G_1 \cdots G_N$ of (12.2.18) is similar to
$H_o H_e$, where $H_o = G_0 G_2 \cdots$ is the product of the even-indexed factors and
$H_e = G_1 G_3 \cdots$ is the product of the odd-indexed factors. This is Fact 1 in
[golub2013matrix] §12.2.10 (Ammar, Gragg and Reichel).

The source numbers the factors from $1$, so its $H_o = G_1 G_3 \cdots$ is the product of the
even-indexed factors here. Factors in planes at distance two or more commute, and
`Matrix.isSimilar_prodFwd_evenOdd` reorders the product. -/
theorem isSimilar_prod_planeReflector_oddEven (φ : ℕ → ℝ) :
    IsSimilar (prodFwd (reflectorFactor N φ) (N + 1))
      (prodFwdEven (reflectorFactor N φ) (N + 1) * prodFwdOdd (reflectorFactor N φ) (N + 1)) := by
  refine isSimilar_prodFwd_evenOdd (fun k l hkl hl => ?_) fun k =>
    (isUnit_iff_isUnit_det _).2 (isUnit_det_of_right_inverse (reflectorFactor_mul_self φ k))
  have hk : k < N := by omega
  rw [reflectorFactor, ite_eq_left hk, givensFactor, dite_eq_left hk]
  rcases (Nat.le_of_lt_succ hl).lt_or_eq with hlN | rfl
  · rw [reflectorFactor, ite_eq_left hlN, givensFactor, dite_eq_left hlN]
    exact commute_planeEmbed_planeEmbed (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)
      (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega) _ _
  · rw [reflectorFactor, ite_eq_right (lt_irrefl _)]
    exact commute_planeEmbed_diagonal (by simp; omega) (by simp; omega) _

end ReflectorProduct

end Matrix

open Polynomial

namespace Matrix

/-! ### Fact 2 of §12.2.10: the odd–even half-sums -/

section HalfSums

variable {N : ℕ}

/-- For $k \le N$, the entry $(G_k - I)_{pq}$ is $0$ unless both $p$ and $q$ lie in $\{k, k + 1\}$.
-/
private theorem reflectorFactor_sub_one_apply_eq_zero (φ : ℕ → ℝ) {k : ℕ} (hk : k ≤ N)
    {p q : Fin (N + 1)}
    (h : ¬((k ≤ (p : ℕ) ∧ (p : ℕ) ≤ k + 1) ∧ (k ≤ (q : ℕ) ∧ (q : ℕ) ≤ k + 1))) :
    (reflectorFactor N φ k - 1) p q = 0 := by
  rw [Matrix.sub_apply, Matrix.one_apply]
  rcases hk.lt_or_eq with hk | rfl
  · rw [reflectorFactor, ite_eq_left hk, givensFactor, dite_eq_left hk]
    by_cases hp : k ≤ (p : ℕ) ∧ (p : ℕ) ≤ k + 1
    · have hq : ¬(k ≤ (q : ℕ) ∧ (q : ℕ) ≤ k + 1) := fun hq => h ⟨hp, hq⟩
      rw [planeEmbed_apply_of_ne_right _ _ (fun e => hq (by simp [Fin.ext_iff] at e; omega))
        (fun e => hq (by simp [Fin.ext_iff] at e; omega)), sub_self]
    · rw [planeEmbed_apply_of_ne_left _ (fun e => hp (by simp [Fin.ext_iff] at e; omega))
        (fun e => hp (by simp [Fin.ext_iff] at e; omega)), sub_self]
  · rw [reflectorFactor, ite_eq_right (lt_irrefl k), diagonal_apply]
    split_ifs with hpq hp <;> first | simp | (subst hpq; exfalso; exact h (by omega))

/-- For $k + 2 \le l \le N$, the departures of $G_k$ and $G_l$ from the identity have zero products:
$(G_k - I)(G_l - I) = 0$ and $(G_l - I)(G_k - I) = 0$. -/
private theorem reflectorFactor_sub_one_mul_sub_one (φ : ℕ → ℝ) {k l : ℕ} (hkl : k + 2 ≤ l)
    (hl : l ≤ N) :
    (reflectorFactor N φ k - 1) * (reflectorFactor N φ l - 1) = 0 ∧
      (reflectorFactor N φ l - 1) * (reflectorFactor N φ k - 1) = 0 := by
  constructor <;> ext p q <;> rw [Matrix.mul_apply,
      Matrix.zero_apply] <;> refine sum_eq_zero fun r _ => ?_
  · by_cases hr : (r : ℕ) ≤ k + 1
    · rw [reflectorFactor_sub_one_apply_eq_zero (k := l) (p := r) (q := q) φ hl (by omega),
        mul_zero]
    · rw [reflectorFactor_sub_one_apply_eq_zero (k := k) (p := p) (q := r) φ (by omega)
        (by omega), zero_mul]
  · by_cases hr : (r : ℕ) ≤ k + 1
    · rw [reflectorFactor_sub_one_apply_eq_zero (k := l) (p := p) (q := r) φ hl (by omega),
        zero_mul]
    · rw [reflectorFactor_sub_one_apply_eq_zero (k := k) (p := r) (q := q) φ (by omega)
        (by omega), mul_zero]

/-- For $k \le N$, $\operatorname{tr}(G_k - I) = -2$, because every factor $G_k$ with $k \le N$ has
trace $N - 1$. -/
private theorem trace_reflectorFactor_sub_one (φ : ℕ → ℝ) {k : ℕ} (hk : k ≤ N) :
    trace (reflectorFactor N φ k - 1) = -2 := by
  rw [trace]
  simp only [diag_apply]
  rcases hk.lt_or_eq with hk | rfl
  · have hne : (⟨k, by omega⟩ : Fin (N + 1)) ≠ ⟨k + 1, by omega⟩ := by simp [Fin.ext_iff]
    rw [Finset.sum_eq_add_of_mem (⟨k, by omega⟩ : Fin (N + 1)) (⟨k + 1, by omega⟩ : Fin (N + 1))
      (mem_univ _) (mem_univ _) hne fun c _ hc =>
        reflectorFactor_sub_one_apply_eq_zero (k := k) φ hk.le (by
          have h1 : (c : ℕ) ≠ k := fun e => hc.1 (Fin.ext e)
          have h2 : (c : ℕ) ≠ k + 1 := fun e => hc.2 (Fin.ext e)
          omega)]
    simp [reflectorFactor, hk, givensFactor, planeEmbed_apply, planeReflector,
      Fin.ext_iff]
    ring
  · rw [Finset.sum_eq_single (⟨k, by omega⟩ : Fin (k + 1)) (fun c _ hc =>
      reflectorFactor_sub_one_apply_eq_zero (k := k) φ le_rfl (by
        have h1 : (c : ℕ) ≠ k := fun e => hc (Fin.ext e)
        have h2 := c.isLt
        omega)) (fun h => absurd (mem_univ _) h)]
    simp [reflectorFactor]
    norm_num

/-- If no two indices $k < l$ with the property $P$ are adjacent, then the product of the factors
$G_k$ with $k \le N$ and $P(k)$ is $I + \sum_{k \le N, \, P(k)} (G_k - I)$. -/
private theorem prodFwd_mask_eq (φ : ℕ → ℝ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ k l, P k → P l → k < l → k + 2 ≤ l) :
    prodFwd (fun k => if P k then reflectorFactor N φ k else 1) (N + 1) =
      1 + ∑ k ∈ range (N + 1), if P k then reflectorFactor N φ k - 1 else 0 := by
  rw [prodFwd_eq_one_add_sum_sub_one fun k l hkl hl => ?_]
  · refine congrArg _ (sum_congr rfl fun k _ => ?_)
    split_ifs <;> simp
  · split_ifs with hk hl'
    · exact (reflectorFactor_sub_one_mul_sub_one φ (hP k l hk hl' hkl) (by omega)).1
    all_goals simp

private theorem even_add_two_le {k l : ℕ} (hk : Even k) (hl : Even l) (hkl : k < l) :
    k + 2 ≤ l := by
  obtain ⟨a, rfl⟩ := hk
  obtain ⟨b, rfl⟩ := hl
  omega

private theorem odd_add_two_le {k l : ℕ} (hk : Odd k) (hl : Odd l) (hkl : k < l) :
    k + 2 ≤ l := by
  obtain ⟨a, rfl⟩ := hk
  obtain ⟨b, rfl⟩ := hl
  omega

/-- The product $H_o$ of the even-indexed factors of (12.2.18) is $I$ plus the sum of their
departures $G_k - I$. -/
private theorem prodFwdEven_reflectorFactor_eq (φ : ℕ → ℝ) :
    prodFwdEven (reflectorFactor N φ) (N + 1) =
      1 + ∑ k ∈ range (N + 1), if Even k then reflectorFactor N φ k - 1 else 0 :=
  prodFwd_mask_eq φ Even fun _ _ => even_add_two_le

/-- The product $H_e$ of the odd-indexed factors of (12.2.18) is $I$ plus the sum of their
departures $G_k - I$. -/
private theorem prodFwdOdd_reflectorFactor_eq (φ : ℕ → ℝ) :
    prodFwdOdd (reflectorFactor N φ) (N + 1) =
      1 + ∑ k ∈ range (N + 1), if Odd k then reflectorFactor N φ k - 1 else 0 :=
  prodFwd_mask_eq φ Odd fun _ _ => odd_add_two_le

/-- A product of factors $G_k$ of (12.2.18) with pairwise nonadjacent indices is symmetric. -/
private theorem transpose_prodFwd_mask (φ : ℕ → ℝ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ k l, P k → P l → k < l → k + 2 ≤ l) :
    (prodFwd (fun k => if P k then reflectorFactor N φ k else 1) (N + 1))ᵀ =
      prodFwd (fun k => if P k then reflectorFactor N φ k else 1) (N + 1) := by
  rw [prodFwd_mask_eq φ P hP, transpose_add, transpose_one, transpose_sum]
  refine congrArg _ (sum_congr rfl fun k _ => ?_)
  split_ifs
  · rw [transpose_sub, transpose_one, reflectorFactor_transpose]
  · exact transpose_zero

/-- A product of factors $G_k$ of (12.2.18) with pairwise nonadjacent indices is tridiagonal. -/
private theorem prodFwd_mask_apply_eq_zero (φ : ℕ → ℝ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ k l, P k → P l → k < l → k + 2 ≤ l) {i j : Fin (N + 1)}
    (hij : (j : ℕ) + 1 < i ∨ (i : ℕ) + 1 < j) :
    prodFwd (fun k => if P k then reflectorFactor N φ k else 1) (N + 1) i j = 0 := by
  rw [prodFwd_mask_eq φ P hP, Matrix.add_apply, one_apply_ne (fun h => by subst h; omega), zero_add,
    Matrix.sum_apply]
  refine sum_eq_zero fun k hk => ?_
  split_ifs
  · exact reflectorFactor_sub_one_apply_eq_zero (k := k) φ (by have := mem_range.1 hk; omega)
      (by omega)
  · rfl

/-- A product of factors $G_k$ of (12.2.18) with pairwise nonadjacent indices is an involution. -/
private theorem prodFwd_mask_mul_self (φ : ℕ → ℝ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ k l, P k → P l → k < l → k + 2 ≤ l) :
    prodFwd (fun k => if P k then reflectorFactor N φ k else 1) (N + 1) *
      prodFwd (fun k => if P k then reflectorFactor N φ k else 1) (N + 1) = 1 := by
  refine prodFwd_mul_self (fun k l hkl hl => ?_) fun k _ => ?_
  · split_ifs with hk hl'
    · have h := reflectorFactor_sub_one_mul_sub_one (N := N) φ (hP k l hk hl' hkl) (by omega)
      exact commute_of_sub_one_mul_sub_one h.1 h.2
    all_goals first | exact Commute.one_left _ | exact Commute.one_right _
  · split_ifs
    · exact reflectorFactor_mul_self φ k
    · exact Matrix.one_mul 1

/-- Among the indices $k < 2m$ there are $m$ even and $m$ odd ones, so summing a constant $c$ over
either kind gives $mc$. -/
private theorem sum_range_two_mul_ite (c : ℝ) (m : ℕ) :
    ∑ k ∈ range (2 * m), (if Even k then c else 0) = m * c ∧
      ∑ k ∈ range (2 * m), (if Odd k then c else 0) = m * c := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : Even (2 * m) := even_two_mul m
    have h2 : ¬Even (2 * m + 1) := Nat.not_even_two_mul_add_one m
    have h3 : ¬Odd (2 * m) := Nat.not_odd_iff_even.2 h1
    have h4 : Odd (2 * m + 1) := odd_two_mul_add_one m
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, sum_range_succ,
      sum_range_succ, ih.1, ih.2]
    simp only [h1, h2, h3, h4, ite_true, ite_false]
    push_cast
    constructor <;> ring

/-- If $N + 1 = 2m$, then $H_o$ and $H_e$ have trace $0$: each is $I$ plus $m$ departures of trace
$-2$. -/
private theorem trace_prodFwd_mask {m : ℕ} (hN : N + 1 = 2 * m) (φ : ℕ → ℝ) :
    trace (prodFwdEven (reflectorFactor N φ) (N + 1)) = 0 ∧
      trace (prodFwdOdd (reflectorFactor N φ) (N + 1)) = 0 := by
  have hs : ∀ (P : ℕ → Prop) [DecidablePred P],
      trace (1 + ∑ k ∈ range (N + 1), if P k then reflectorFactor N φ k - 1 else 0) =
        ((N + 1 : ℕ) : ℝ) + ∑ k ∈ range (N + 1), if P k then (-2 : ℝ) else 0 := fun P _ => by
    rw [trace_add, trace_one, Fintype.card_fin, trace_sum]
    refine congrArg _ (sum_congr rfl fun k hk => ?_)
    split_ifs
    · exact trace_reflectorFactor_sub_one (k := k) φ (by have := mem_range.1 hk; omega)
    · exact trace_zero _ _
  rw [prodFwdEven_reflectorFactor_eq, prodFwdOdd_reflectorFactor_eq, hs, hs, hN,
    (sum_range_two_mul_ite (-2) m).1, (sum_range_two_mul_ite (-2) m).2]
  push_cast
  constructor <;> ring

variable (N) in
/-- The half-sum $C = \frac{1}{2} (H_o + H_e)$ of the product $H_o$ of the even-indexed factors and
the product $H_e$ of the odd-indexed factors of (12.2.18). It appears in Fact 2 of
[golub2013matrix] §12.2.10. -/
noncomputable def oddEvenHalfSum (φ : ℕ → ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  (1 / 2 : ℝ) • (prodFwdEven (reflectorFactor N φ) (N + 1) +
    prodFwdOdd (reflectorFactor N φ) (N + 1))

variable (N) in
/-- The half-difference $S = \frac{1}{2} (H_o - H_e)$ of the product $H_o$ of the even-indexed
factors and the product $H_e$ of the odd-indexed factors of (12.2.18). It appears in Fact 2 of
[golub2013matrix] §12.2.10. -/
noncomputable def oddEvenHalfDiff (φ : ℕ → ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  (1 / 2 : ℝ) • (prodFwdEven (reflectorFactor N φ) (N + 1) -
    prodFwdOdd (reflectorFactor N φ) (N + 1))

/-- The half-sum $C = \frac{1}{2} (H_o + H_e)$ is symmetric, since $H_o$ and $H_e$ are products of
commuting symmetric factors. -/
theorem isSymm_oddEvenHalfSum (φ : ℕ → ℝ) : (oddEvenHalfSum N φ).IsSymm := by
  have hE : (prodFwdEven (reflectorFactor N φ) (N + 1)).IsSymm :=
    transpose_prodFwd_mask φ Even fun _ _ => even_add_two_le
  have hO : (prodFwdOdd (reflectorFactor N φ) (N + 1)).IsSymm :=
    transpose_prodFwd_mask φ Odd fun _ _ => odd_add_two_le
  exact (hE.add hO).smul _

/-- The half-difference $S = \frac{1}{2} (H_o - H_e)$ is symmetric. -/
theorem isSymm_oddEvenHalfDiff (φ : ℕ → ℝ) : (oddEvenHalfDiff N φ).IsSymm := by
  have hE : (prodFwdEven (reflectorFactor N φ) (N + 1)).IsSymm :=
    transpose_prodFwd_mask φ Even fun _ _ => even_add_two_le
  have hO : (prodFwdOdd (reflectorFactor N φ) (N + 1)).IsSymm :=
    transpose_prodFwd_mask φ Odd fun _ _ => odd_add_two_le
  exact (hE.sub hO).smul _

/-- For every sequence $\varphi$, the half-sum $C = \frac{1}{2} (H_o + H_e)$ is tridiagonal. This is
the shape part of Fact 2 in [golub2013matrix] §12.2.10.

Each of $H_o$ and $H_e$ is the identity plus the departures $G_k - I$ of its factors
(`prodFwd_eq_one_add_sum_sub_one`), and these departures live in disjoint $2 \times 2$ diagonal
blocks. -/
theorem isTridiagonal_oddEvenHalfSum (φ : ℕ → ℝ) : (oddEvenHalfSum N φ).IsTridiagonal := by
  refine isTridiagonal_iff_fin.2 fun i j hij => ?_
  rw [oddEvenHalfSum, Matrix.smul_apply, Matrix.add_apply, prodFwdEven, prodFwdOdd,
    prodFwd_mask_apply_eq_zero φ Even (fun _ _ => even_add_two_le) hij,
    prodFwd_mask_apply_eq_zero φ Odd (fun _ _ => odd_add_two_le) hij, add_zero, smul_zero]

/-- For every sequence $\varphi$, the half-difference $S = \frac{1}{2} (H_o - H_e)$ is tridiagonal.
This is the shape part of Fact 2 in [golub2013matrix] §12.2.10. -/
theorem isTridiagonal_oddEvenHalfDiff (φ : ℕ → ℝ) : (oddEvenHalfDiff N φ).IsTridiagonal := by
  refine isTridiagonal_iff_fin.2 fun i j hij => ?_
  rw [oddEvenHalfDiff, Matrix.smul_apply, Matrix.sub_apply, prodFwdEven, prodFwdOdd,
    prodFwd_mask_apply_eq_zero φ Even (fun _ _ => even_add_two_le) hij,
    prodFwd_mask_apply_eq_zero φ Odd (fun _ _ => odd_add_two_le) hij, sub_zero, smul_zero]

open Complex in
/-- Let $\varphi$ be a sequence of reals, let $H = G_0 \cdots G_N$ be the product (12.2.18), and let
$\theta_0, \dots, \theta_{m-1}$ be reals such that the characteristic polynomial of $H$, as a
complex matrix, is
$$\prod_{k < m} (X - e^{i \theta_k}) (X - e^{-i \theta_k}).$$
Then the characteristic polynomials $p_C$ of $C = \frac{1}{2} (H_o + H_e)$ and $p_S$ of
$S = \frac{1}{2} (H_o - H_e)$ are
$$p_C = \prod_{k < m} \bigl(X - \cos(\theta_k / 2)\bigr) \bigl(X + \cos(\theta_k / 2)\bigr),$$
$$p_S = \prod_{k < m} \bigl(X - \sin(\theta_k / 2)\bigr) \bigl(X + \sin(\theta_k / 2)\bigr).$$
So the eigenvalues of $C$ are $\pm \cos(\theta_k / 2)$ and those of $S$ are
$\pm \sin(\theta_k / 2)$. This is the spectral part of Fact 2 in [golub2013matrix] §12.2.10.

The hypothesis is the form (12.2.19) of the eigenvalues, and it forces $N + 1 = 2m$. The
matrices $H_o$ and $H_e$ are symmetric involutions of trace $0$, and $H_o H_e$ is similar to $H$
(`Matrix.isSimilar_prod_planeReflector_oddEven`). So `Matrix.charpoly_half_add_of_involutive`
applies to $(H_o, H_e)$ and to $(H_o, -H_e)$, whose product $-H_o H_e$ has the eigenvalues
$e^{\pm i (\theta_k + \pi)}$. -/
theorem charpoly_oddEven_half_sum (φ : ℕ → ℝ) {m : ℕ} (θ : Fin m → ℝ)
    (hθ : ((prodFwd (reflectorFactor N φ) (N + 1)).map (algebraMap ℝ ℂ)).charpoly =
      ∏ k, (X - C (exp (θ k * I))) * (X - C (exp (-θ k * I)))) :
    (oddEvenHalfSum N φ).charpoly =
        ∏ k, (X - C (Real.cos (θ k / 2))) * (X + C (Real.cos (θ k / 2))) ∧
      (oddEvenHalfDiff N φ).charpoly =
        ∏ k, (X - C (Real.sin (θ k / 2))) * (X + C (Real.sin (θ k / 2))) := by
  rw [oddEvenHalfSum, oddEvenHalfDiff]
  have hN : N + 1 = 2 * m := by simpa using card_eq_of_charpoly_eq_prod hθ
  obtain ⟨A, hA⟩ : ∃ A, A = prodFwdEven (reflectorFactor N φ) (N + 1) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = prodFwdOdd (reflectorFactor N φ) (N + 1) := ⟨_, rfl⟩
  rw [← hA, ← hB]
  have hAs : A.IsSymm := hA ▸ transpose_prodFwd_mask φ Even fun _ _ => even_add_two_le
  have hBs : B.IsSymm := hB ▸ transpose_prodFwd_mask φ Odd fun _ _ => odd_add_two_le
  have hAA : A * A = 1 := hA ▸ prodFwd_mask_mul_self φ Even fun _ _ => even_add_two_le
  have hBB : B * B = 1 := hB ▸ prodFwd_mask_mul_self φ Odd fun _ _ => odd_add_two_le
  obtain ⟨htA, htB⟩ := trace_prodFwd_mask hN φ
  rw [← hA] at htA
  rw [← hB] at htB
  have hAB : ((A * B).map (algebraMap ℝ ℂ)).charpoly =
      ∏ k, (X - C (exp (θ k * I))) * (X - C (exp (-θ k * I))) := by
    rw [charpoly_map, hA, hB, ← (isSimilar_prod_planeReflector_oddEven φ).charpoly_eq,
      ← charpoly_map, hθ]
  refine ⟨charpoly_half_add_of_involutive hAs hBs hAA hBB htA htB θ hAB, ?_⟩
  -- `S = (A + (−B))/2`, and `A (−B) = −AB` has the eigenvalues `e^{±i(θ_k + π)}`
  have hneg : ((A * -B).map (algebraMap ℝ ℂ)).charpoly =
      ∏ k, (X - C (exp ((θ k + Real.pi : ℝ) * I))) * (X - C (exp (-(θ k + Real.pi : ℝ) * I))) := by
    have hcard : Fintype.card (Fin (N + 1)) = 2 * m := by rw [Fintype.card_fin, hN]
    refine Polynomial.funext fun w => ?_
    have h := congrArg (eval (-w)) hAB
    rw [eval_charpoly, eval_prod] at h
    rw [eval_charpoly, eval_prod, mul_neg, Matrix.map_neg _ (map_neg _),
      show scalar (Fin (N + 1)) w - -(A * B).map (algebraMap ℝ ℂ) =
        -(scalar (Fin (N + 1)) (-w) - (A * B).map (algebraMap ℝ ℂ)) by
        rw [map_neg]
        abel,
      det_neg, hcard, pow_mul, neg_one_sq, one_pow, one_mul, h]
    refine prod_congr rfl fun k _ => ?_
    have e1 : exp ((θ k + Real.pi : ℝ) * I) = -exp (θ k * I) := by
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]
    have e2 : exp (-(θ k + Real.pi : ℝ) * I) = -exp (-θ k * I) := by
      push_cast
      rw [neg_add, add_mul, Complex.exp_add, neg_mul (Real.pi : ℂ), Complex.exp_neg,
        Complex.exp_pi_mul_I]
      norm_num
    simp only [eval_mul, eval_sub, eval_X, eval_C, e1, e2]
    ring
  have hS := charpoly_half_add_of_involutive hAs
    (show (-B).IsSymm by rw [IsSymm, transpose_neg, hBs.eq]) hAA
    (by rw [neg_mul_neg, hBB]) htA (by rw [trace_neg, htB, neg_zero]) _ hneg
  rw [← sub_eq_add_neg] at hS
  rw [hS]
  refine prod_congr rfl fun k _ => ?_
  rw [show (θ k + Real.pi) / 2 = θ k / 2 + Real.pi / 2 by ring, Real.cos_add_pi_div_two, C_neg]
  ring

end HalfSums

end Matrix
