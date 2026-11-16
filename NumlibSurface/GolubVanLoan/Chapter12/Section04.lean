/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Tensor.MultilinearProduct

/-!
# Golub and Van Loan, Section 12.4: Tensor unfoldings and contractions

This module formalizes §12.4 of [golub2013matrix], the basic operations on an order-$d$ tensor
$\mathcal{A} \in \mathbb{R}^{n_1 \times \cdots \times n_d}$, a real array with one entry
$\mathcal{A}(i)$ for each index tuple $i = (i_1, \dots, i_d)$. It covers fibers, slices, subtensors
and the Frobenius norm (§12.4.2), the vectorization $\operatorname{vec}(\mathcal{A})$
(12.4.2)–(12.4.5), tensor transposition (§12.4.4), the mode-$k$ unfolding $\mathcal{A}_{(k)}$
(12.4.6) and the general unfolding $\mathcal{A}_{r \times c}$ (12.4.8), outer products and rank-one
tensors (12.4.9)–(12.4.10), contractions (12.4.11)–(12.4.13), and the mode-$k$ product
$\mathcal{S} \times_k M$ and the multilinear product $\mathcal{S} \times_1 M_1 \cdots \times_d M_d$
(12.4.14)–(12.4.19). Theorem 12.4.1 gives the unfoldings of a multilinear product:
$\mathcal{A}_{(k)} = M_k \mathcal{S}_{(k)} (M_d \otimes \cdots \otimes M_{k+1} \otimes M_{k-1}
\otimes \cdots \otimes M_1)^T$.

The proofs specialize the backbone modules `Numlib.LinearAlgebra.Tensor.Basic`,
`Numlib.LinearAlgebra.Tensor.Unfolding` and `Numlib.LinearAlgebra.Tensor.MultilinearProduct`, which
work with tensors on arbitrary index types and with unfoldings whose rows and columns are index
tuples.

## Main definitions

* §12.4.2, `GolubVanLoan.Chapter12.RTensor`: the space $\mathbb{R}^{n_1 \times \cdots \times n_d}$
  of order-$d$ tensors.
* §12.4.2, `GolubVanLoan.Chapter12.fiber`, `GolubVanLoan.Chapter12.slice` and
  `GolubVanLoan.Chapter12.subtensor`: the subtensors obtained by fixing all indices but one, all
  indices but two, or by restricting each index to an interval.
* §12.4.5, `GolubVanLoan.Chapter12.modalUnfolding`: the mode-$k$ unfolding $\mathcal{A}_{(k)}$,
  whose columns are the mode-$k$ fibers in the vec order.
* §12.4.6, `GolubVanLoan.Chapter12.generalUnfolding`: the general unfolding
  $\mathcal{A}_{r \times c}$ for a list $r$ of row modes and a list $c$ of column modes.
* §12.4.10, `GolubVanLoan.Chapter12.modeProduct`: the mode-$k$ product $\mathcal{S} \times_k M$ with
  a rectangular matrix $M \in \mathbb{R}^{m \times n_k}$.

## Main results

* §12.4.2, `GolubVanLoan.Chapter12.frobenius_norm_tensor`: $\|\mathcal{A}\|_F$ is the square root of
  the sum of the squares of the entries.
* Equations (12.4.2)–(12.4.3), `GolubVanLoan.Chapter12.equation_12_4_2`:
  $\operatorname{vec}(\mathcal{A})$ stacks the vectorizations of the slices of $\mathcal{A}$ in the
  last mode.
* Equations (12.4.4)–(12.4.5), `GolubVanLoan.Chapter12.equation_12_4_4`:
  $\operatorname{vec}(\mathcal{A})(\operatorname{col}(i, n)) = \mathcal{A}(i)$.
* §12.4.4, `GolubVanLoan.Chapter12.tensorTranspose_apply`: the $p$-transpose satisfies
  $\mathcal{A}^{\langle p \rangle}(j(p)) = \mathcal{A}(j)$.
* Equation (12.4.6), `GolubVanLoan.Chapter12.equation_12_4_6`: $\mathcal{A}_{(k)}(i_k,
  \operatorname{col}(\tilde\imath_k, \tilde n_k)) = \mathcal{A}(i)$.
* Equation (12.4.8), `GolubVanLoan.Chapter12.equation_12_4_8`: the entries of
  $\mathcal{A}_{r \times c}$, and the modal unfolding and $\operatorname{vec}(\mathcal{A})$ as
  special cases.
* §12.4.7, `GolubVanLoan.Chapter12.outer_kronecker`: for matrices $B$ and $C$, the unfolding
  $(B \circ C)_{[3\,1] \times [4\,2]}$ is $B \otimes C$.
* §12.4.8, `GolubVanLoan.Chapter12.eq_sum_rankOne`: every tensor is the sum of its entries times
  rank-one tensors of unit vectors.
* Equation (12.4.9), `GolubVanLoan.Chapter12.equation_12_4_9`: the mode-$k$ unfolding of a rank-one
  tensor.
* Equation (12.4.10), `GolubVanLoan.Chapter12.equation_12_4_10`: the general unfolding of a rank-one
  tensor.
* Equation (12.4.11), `GolubVanLoan.Chapter12.equation_12_4_11`: a contraction of an order-4 and an
  order-5 tensor is a matrix product of slices.
* Equations (12.4.12)–(12.4.13), `GolubVanLoan.Chapter12.equation_12_4_13`: the unfolding of a
  contraction is the product of the unfoldings.
* Equation (12.4.14), `GolubVanLoan.Chapter12.equation_12_4_14`: $(\mathcal{S} \times_k M)_{(k)} = M
  \mathcal{S}_{(k)}$, and the entries of $\mathcal{S} \times_k M$.
* Equation (12.4.15), `GolubVanLoan.Chapter12.equation_12_4_15`: $\operatorname{vec}(\mathcal{S}
  \times_k M) = (I \otimes M \otimes I) \operatorname{vec}(\mathcal{S})$.
* Equation (12.4.16), `GolubVanLoan.Chapter12.equation_12_4_16`: mode products in distinct modes
  commute.
* Equation (12.4.17), `GolubVanLoan.Chapter12.equation_12_4_17`: $(\mathcal{S} \times_k F) \times_k
  G = \mathcal{S} \times_k (GF)$.
* Equations (12.4.18)–(12.4.19), `GolubVanLoan.Chapter12.equation_12_4_19`: for order 4, the entries
  and the vectorization of a multilinear product, and the multilinear product as a sequence of mode
  products.
* Theorem 12.4.1, `GolubVanLoan.Chapter12.theorem_12_4_1`: $\mathcal{A}_{(k)} = M_k
  \mathcal{S}_{(k)} (M_d \otimes \cdots \otimes M_{k+1} \otimes M_{k-1} \otimes \cdots \otimes
  M_1)^T$ for $\mathcal{A} = \mathcal{S} \times_1 M_1 \cdots \times_d M_d$.
* Theorem 12.4.1, `GolubVanLoan.Chapter12.theorem_12_4_1_b`: if every $M_k$ is nonsingular, then
  $\mathcal{S} = \mathcal{A} \times_1 M_1^{-1} \cdots \times_d M_d^{-1}$.

## Conventions

* The space $\mathbb{R}^{n_1 \times \cdots \times n_d}$ is `GolubVanLoan.Chapter12.RTensor n`, the
  backbone's `Tensor (fun k : Fin d => Fin (n k)) ℝ`. Indices are 0-based: the entry
  $\mathcal{A}(i)$ is `A i` for `i : ∀ k, Fin (n k)`, and mode $k$ of the source is mode `k - 1` in
  Lean.
* The position $\operatorname{col}(i, n) - 1$ is Mathlib's little-endian `finPiFinEquiv i`, in which
  the first index runs fastest. The source's $\operatorname{vec}$ is `Tensor.vecFin`.
* A Kronecker product in the reversed order $M_d \otimes \cdots \otimes M_1$ of the source is the
  backbone's family product `Matrix.piKronecker M`, flattened by `finPiFinEquiv` in rows and
  columns. `Matrix.piKronecker_reindex_finPiFinEquiv` identifies it with the positional product
  `Matrix.kroneckerFin`, last factor outermost.
* The lists $r$ of row modes and $c$ of column modes of a general unfolding are an equivalence
  `p : Fin e ⊕ Fin f ≃ Fin d`: the row modes are `p (inl 0), …, p (inl (e - 1))` and the column
  modes `p (inr 0), …, p (inr (f - 1))`, in the listed order.

## Implementation notes

* The backbone's unfoldings `Tensor.modeUnfold` and `Tensor.unfold` are typed: their rows and
  columns are index tuples. The unfoldings of the source are matrices on `Fin`. The surface
  definitions `GolubVanLoan.Chapter12.modalUnfolding` and `GolubVanLoan.Chapter12.generalUnfolding`
  flatten the typed ones by `finPiFinEquiv`, in the column order of the source.
* The mode-$k$ product with $M \in \mathbb{R}^{m \times n_k}$ changes the $k$-th size, so its result
  has the shape `Function.update n k m`. It is the backbone's rectangular mode product
  `Tensor.rectModeProd`, and the sizes off $k$ are matched by `Function.update_of_ne`. Where two
  shapes are only propositionally equal, a tensor is read in the other shape through
  `GolubVanLoan.Chapter12.castShape`. The laws (12.4.14)–(12.4.17) specialize
  `Tensor.modeUnfold_rectModeProd`, `Tensor.vecFin_rectModeProd`, `Tensor.rectModeProd_comm` and
  `Tensor.rectModeProd_rectModeProd`.
* The multilinear product as a sequence of mode products, in the table after (12.4.19), is stated
  for square factors through the backbone's shape-preserving `Tensor.modeProd`, for order 4 and for
  the two orders $1, 2, 3, 4$ and $4, 1, 2, 3$ of the mode products.

## Deviations from the source

* **Equation (12.4.17)** (correction). The source prints $\mathcal{S} \times_k (FG)$. The correct
  right side is $\mathcal{S} \times_k (GF)$. See `GolubVanLoan.Chapter12.equation_12_4_17`.

## Not formalized

* **The loops (12.4.1) and (12.4.12).**
* **The numerical examples**: the $2 \times 2 \times 3 \times 4$ unfolding of §12.4.1, the vec and
  transposition examples of §12.4.3–12.4.4, and (12.4.7). Numerical examples are out of scope for
  the library.
* **The vec formula for $\mathcal{A}^{\langle [3\,2\,1] \rangle}$** in the transposition example.
  The source misprints it; the correct formula is $(\mathcal{P}_{n_2, n_1} \otimes I_{n_3})
  \mathcal{P}_{n_3, n_1 n_2}$.
* **The space–time contraction example of §12.4.12.**
* **The flop counts.** Operation counts are out of scope for the library.
-/

open Matrix

namespace GolubVanLoan.Chapter12

variable {d : ℕ}

/-! ### Order-$d$ tensors (§12.4.2) -/

/-- **Section 12.4.2** of [golub2013matrix], definition of a tensor. For $d \in \mathbb{N}$ and
sizes $n = (n_1, \dots, n_d)$, the space $\mathbb{R}^{n_1 \times \cdots \times n_d}$ of
**order-$d$ tensors** consists of the real arrays $\mathcal{A}$ with one entry $\mathcal{A}(i)$
for each index tuple $i = (i_1, \dots, i_d)$ with $1 \le i_k \le n_k$.

The type is the backbone's `Tensor (fun k : Fin d => Fin (n k)) ℝ`. Indices are 0-based: the
entry $\mathcal{A}(i)$ is `A i` for `i : ∀ k, Fin (n k)`. The norm of this type is the Frobenius
norm (`GolubVanLoan.Chapter12.frobenius_norm_tensor`). -/
abbrev RTensor (n : Fin d → ℕ) : Type :=
  Tensor (fun k : Fin d => Fin (n k)) ℝ

/-- **Section 12.4.2** of [golub2013matrix], definition of a fiber. Let $\mathcal{A} \in
\mathbb{R}^{n_1 \times \cdots \times n_d}$, let $k$ be a mode, and fix an index $c_i$ of every
mode $i \neq k$. The **fiber** of $\mathcal{A}$ at $c$ is the order-1 subtensor obtained by
fixing every index except the $k$-th to $c$, such as $\mathcal{A}(1, :, 2, 4)$. It is
`Tensor.restrict` for the predicate $i = k$. -/
def fiber {n : Fin d → ℕ} (A : RTensor n) (k : Fin d) (c : ∀ i : {i // ¬i = k}, Fin (n i)) :
    Tensor (fun i : {i // i = k} => Fin (n i)) ℝ :=
  Tensor.restrict (· = k) c A

/-- **Section 12.4.2** of [golub2013matrix], definition of a slice. Let $\mathcal{A} \in
\mathbb{R}^{n_1 \times \cdots \times n_d}$, let $k$ and $l$ be modes, and fix an index $c_i$ of
every mode $i \notin \{k, l\}$. The **slice** of $\mathcal{A}$ at $c$ is the order-2 subtensor
obtained by fixing every index except the $k$-th and the $l$-th to $c$. It is `Tensor.restrict`
for the predicate $i = k \lor i = l$. -/
def slice {n : Fin d → ℕ} (A : RTensor n) (k l : Fin d)
    (c : ∀ i : {i // ¬(i = k ∨ i = l)}, Fin (n i)) :
    Tensor (fun i : {i // i = k ∨ i = l} => Fin (n i)) ℝ :=
  Tensor.restrict (fun i => i = k ∨ i = l) c A

/-- **Section 12.4.2** of [golub2013matrix], the colon subtensor. For $\mathcal{A} \in
\mathbb{R}^{n_1 \times \cdots \times n_d}$ and index tuples $L$ and $R$, the **subtensor**
$\mathcal{A}(L{:}R)$ consists of the entries $\mathcal{A}(i)$ with $L_k \le i_k \le R_k$ for
every $k$. Mode $k$ of the subtensor has no indices if $L_k > R_k$. -/
def subtensor {n : Fin d → ℕ} (A : RTensor n) (L R : ∀ k, Fin (n k)) :
    Tensor (fun k => {x : Fin (n k) // L k ≤ x ∧ x ≤ R k}) ℝ :=
  Tensor.of fun a => A fun k => a k

/-- **Section 12.4.2** of [golub2013matrix], the Frobenius norm of a tensor. For every $\mathcal{A}
\in \mathbb{R}^{n_1 \times \cdots \times n_d}$,
$$\|\mathcal{A}\|_F = \sqrt{\sum_{i=1}^{n} \mathcal{A}(i)^2},$$
where the sum runs over all index tuples $i$ with $1 \le i_k \le n_k$.

The norm $\|\mathcal{A}\|_F$ is the norm `‖A‖` of the backbone's `Tensor`, which comes from the
Frobenius inner product $\langle \mathcal{A}, \mathcal{B} \rangle = \sum_i \mathcal{A}(i)
\mathcal{B}(i)$. -/
theorem frobenius_norm_tensor {n : Fin d → ℕ} (A : RTensor n) : ‖A‖ = √(∑ i, A i ^ 2) := by
  rw [Tensor.frobenius_norm_def]
  simp only [Real.norm_eq_abs, sq_abs]

/-! ### Vectorization (12.4.2)–(12.4.5) -/

/-- **Equations (12.4.4)–(12.4.5)** of [golub2013matrix]. Let $\mathcal{A} \in \mathbb{R}^{n_1
\times \cdots \times n_d}$, and for an index tuple $i$ let
$$\operatorname{col}(i, n) = i_1 + (i_2 - 1) n_1 + (i_3 - 1) n_1 n_2 + \cdots + (i_d - 1) n_1
  \cdots n_{d-1}.$$
Then the vector $a = \operatorname{vec}(\mathcal{A})$ satisfies
$a(\operatorname{col}(i, n)) = \mathcal{A}(i)$ for every $i$.

Indices are 0-based. The 0-based position $\operatorname{col}(i, n) - 1$ is `finPiFinEquiv i`,
and the first part of the statement says that its value is $\sum_k i_k \prod_{j < k} n_j$ for
the 0-based indices $i_k$. The vector $\operatorname{vec}(\mathcal{A})$ is `Tensor.vecFin A`. -/
theorem equation_12_4_4 {n : Fin d → ℕ} (A : RTensor n) (i : ∀ k, Fin (n k)) :
    ((finPiFinEquiv i : Fin (∏ k, n k)) : ℕ) =
        ∑ k, (i k : ℕ) * ∏ j : Fin k, n (Fin.castLE k.2.le j) ∧
      Tensor.vecFin A (finPiFinEquiv i) = A i :=
  ⟨finPiFinEquiv_apply i, Tensor.vecFin_apply A i⟩

/-- **Equations (12.4.2)–(12.4.3)** of [golub2013matrix]. Let $\mathcal{A} \in \mathbb{R}^{n_1
\times \cdots \times n_d}$ with $d \ge 1$, and for $1 \le x \le n_d$ let $\mathcal{A}^{(x)} \in
\mathbb{R}^{n_1 \times \cdots \times n_{d-1}}$ be the slice $\mathcal{A}^{(x)}(i_1, \dots,
i_{d-1}) = \mathcal{A}(i_1, \dots, i_{d-1}, x)$. Then
$$\operatorname{vec}(\mathcal{A}) = \begin{bmatrix} \operatorname{vec}(\mathcal{A}^{(1)}) \\
  \vdots \\ \operatorname{vec}(\mathcal{A}^{(n_d)}) \end{bmatrix}.$$
So the recursive definition of $\operatorname{vec}$ in the source agrees with the closed form
(12.4.4)–(12.4.5), as Problem P12.4.2 of the source asks.

The Lean tensor has order `d + 1`. The statement is entrywise: entry $t$ of block $x$ of
`Tensor.vecFin A`, at the position `finProdFinEquiv (x, t)` of the positional block layout, is
entry $t$ of the vectorization of the slice $\mathcal{A}^{(x)}$, which is built with `Fin.snoc`. -/
theorem equation_12_4_2 {n : Fin (d + 1) → ℕ} (A : RTensor n) (x : Fin (n (Fin.last d)))
    (t : Fin (∏ k : Fin d, n k.castSucc)) :
    Tensor.vecFin A (Fin.cast (by rw [Fin.prod_univ_castSucc, mul_comm]) (finProdFinEquiv (x, t)))
      = Tensor.vecFin (Tensor.of fun i => A (Fin.snoc (α := fun k => Fin (n k)) i x) :
          RTensor fun k : Fin d => n k.castSucc) t :=
  Tensor.vecFin_snoc A x t

/-! ### Transposition (§12.4.4) -/

/-- **Section 12.4.4** of [golub2013matrix], definition of tensor transposition. Let $\mathcal{A}
\in \mathbb{R}^{n_1 \times \cdots \times n_d}$ and let $p$ be a permutation of $1{:}d$. The
**$p$-transpose** $\mathcal{A}^{\langle p \rangle} \in \mathbb{R}^{n_{p_1} \times \cdots \times
n_{p_d}}$ satisfies
$$\mathcal{A}^{\langle p \rangle}(j(p)) = \mathcal{A}(j)$$
for every index tuple $j$, where $j(p) = (j_{p_1}, \dots, j_{p_d})$.

The transpose is the backbone's `Tensor.permute p A`, of shape `n ∘ p`, and the theorem states
its defining property. -/
theorem tensorTranspose_apply {n : Fin d → ℕ} (p : Equiv.Perm (Fin d)) (A : RTensor n)
    (j : ∀ k, Fin (n k)) :
    (Tensor.permute p A : RTensor (n ∘ p)) (fun k => j (p k)) = A j :=
  Tensor.permute_apply p A j

/-! ### Modal unfoldings (12.4.6) -/

section Modal

variable {n : Fin (d + 1) → ℕ}

/-- The column order of the mode-$k$ unfolding of a tensor of order $d + 1$. A tuple of indices of
the modes other than $k$ is relabelled by $0, \dots, d - 1$ in increasing order of the modes,
through `Fin.succAbove k`. The relabelled tuple is then flattened by `finPiFinEquiv`, which is
$\operatorname{col}$. -/
def modalColumnEquiv (n : Fin (d + 1) → ℕ) (k : Fin (d + 1)) :
    (∀ j : {j // j ≠ k}, Fin (n j)) ≃ Fin (∏ j : Fin d, n (k.succAbove j)) :=
  (Equiv.piCongrLeft' (fun j : {j // j ≠ k} => Fin (n j)) (finSuccAboveEquiv k).symm).trans
    (finPiFinEquiv (n := fun j : Fin d => n (k.succAbove j)))

/-- For an index tuple $i$, the column of the mode-$k$ unfolding that holds the entry
$\mathcal{A}(i)$ is $\operatorname{col}(\tilde\imath_k, \tilde n_k)$, where $\tilde\imath_k$ and
$\tilde n_k$ are $i$ and $n$ with their $k$-th entries deleted. -/
theorem modalColumnEquiv_apply (k : Fin (d + 1)) (i : ∀ j, Fin (n j)) :
    modalColumnEquiv n k (fun j => i j) = finPiFinEquiv fun j => i (k.succAbove j) :=
  rfl

/-- For a tuple $c$ of indices of the modes other than $k$, the index tuple decoded from the column
`modalColumnEquiv n k c` has, at position $i$, the index that $c$ gives to the $i$-th mode other
than $k$, which is mode `k.succAbove i`. -/
theorem modalColumnEquiv_symm_apply (k : Fin (d + 1)) (c : ∀ j : {j // j ≠ k}, Fin (n j))
    (i : Fin d) :
    finPiFinEquiv.symm (modalColumnEquiv n k c) i = c ⟨k.succAbove i, Fin.succAbove_ne k i⟩ :=
  congrFun (finPiFinEquiv.symm_apply_apply
    (Equiv.piCongrLeft' _ (finSuccAboveEquiv k).symm c :
      ∀ j : Fin d, Fin (n (k.succAbove j)))) i

/-- **Section 12.4.5** of [golub2013matrix], definition of the modal unfolding. Let $\mathcal{A} \in
\mathbb{R}^{n_1 \times \cdots \times n_d}$ and let $k$ be a mode. The **mode-$k$ unfolding**
$\mathcal{A}_{(k)} \in \mathbb{R}^{n_k \times (n_1 \cdots n_d / n_k)}$ is the matrix whose
columns are the mode-$k$ fibers of $\mathcal{A}$, ordered "left to right according to the vec
ordering" of the remaining indices.

The Lean tensor has order `d + 1`, so that a mode exists. The number of columns is
$\prod_{j \neq k} n_j$, which is $n_1 \cdots n_d / n_k$ when $n_k \neq 0$. The definition is the
backbone's typed unfolding `Tensor.modeUnfold`, whose columns are the tuples of the other
indices, with the columns flattened by `GolubVanLoan.Chapter12.modalColumnEquiv`. -/
def modalUnfolding (A : RTensor n) (k : Fin (d + 1)) :
    Matrix (Fin (n k)) (Fin (∏ j : Fin d, n (k.succAbove j))) ℝ :=
  (A.modeUnfold k).reindex (Equiv.refl _) (modalColumnEquiv n k)

/-- **Equation (12.4.6)** of [golub2013matrix]. Let $\mathcal{A} \in \mathbb{R}^{n_1 \times \cdots
\times n_d}$ and let $k$ be a mode. For an index tuple $i$, let $\tilde\imath_k$ and
$\tilde n_k$ be $i$ and $n$ with their $k$-th entries deleted. Then
$$\mathcal{A}_{(k)}(i_k, \operatorname{col}(\tilde\imath_k, \tilde n_k)) = \mathcal{A}(i).$$

The Lean tensor has order `d + 1`, and $\mathcal{A}_{(k)}$ is
`GolubVanLoan.Chapter12.modalUnfolding A k`. -/
theorem equation_12_4_6 (A : RTensor n) (k : Fin (d + 1)) (i : ∀ j, Fin (n j)) :
    modalUnfolding A k (i k) (finPiFinEquiv fun j => i (k.succAbove j)) = A i := by
  rw [modalUnfolding, reindex_apply, submatrix_apply, ← modalColumnEquiv_apply,
    Equiv.symm_apply_apply]
  exact Tensor.modeUnfold_apply A k i

end Modal

/-! ### General unfoldings (12.4.8) -/

section General

variable {e f : ℕ} {n : Fin d → ℕ}

/-- **Section 12.4.6** of [golub2013matrix], definition of the general unfolding. Let $\mathcal{A}
\in \mathbb{R}^{n_1 \times \cdots \times n_d}$, and split the modes $1{:}d$ into a list
$r = (r_1, \dots, r_e)$ of row modes and a list $c = (c_1, \dots, c_f)$ of column modes, so that
each mode is in exactly one list. The **general unfolding** $\mathcal{A}_{r \times c}$ is the
$(n_{r_1} \cdots n_{r_e}) \times (n_{c_1} \cdots n_{c_f})$ matrix whose rows are the index
tuples of the row modes and whose columns are the index tuples of the column modes, each
flattened by $\operatorname{col}$ in the listed order. Its entries are given by (12.4.8).

The two lists are the equivalence `p : Fin e ⊕ Fin f ≃ Fin d`, with row modes
`p (inl 0), …, p (inl (e - 1))` and column modes `p (inr 0), …, p (inr (f - 1))`. The definition
transposes $\mathcal{A}$ by `Tensor.permute p` and decodes the row and the column by
`finPiFinEquiv.symm`. -/
def generalUnfolding (A : RTensor n) (p : Fin e ⊕ Fin f ≃ Fin d) :
    Matrix (Fin (∏ j : Fin e, n (p (.inl j)))) (Fin (∏ j : Fin f, n (p (.inr j)))) ℝ :=
  Matrix.of fun R C => (Tensor.permute p A : Tensor (fun s => Fin (n (p s))) ℝ)
    (Sum.rec (motive := fun s => Fin (n (p s))) (finPiFinEquiv.symm R) (finPiFinEquiv.symm C))

/-- For every index tuple $i$, the general unfolding $\mathcal{A}_{r \times c}$ has the entry
$\mathcal{A}(i)$ in row $\operatorname{col}(i(r), n(r))$ and column
$\operatorname{col}(i(c), n(c))$, where $i(r)$ and $n(r)$ are $i$ and $n$ restricted to the row
modes, in the listed order, and likewise for $c$. -/
theorem generalUnfolding_apply (A : RTensor n) (p : Fin e ⊕ Fin f ≃ Fin d)
    (i : ∀ k, Fin (n k)) :
    generalUnfolding A p (finPiFinEquiv fun j => i (p (.inl j)))
      (finPiFinEquiv fun j => i (p (.inr j))) = A i := by
  rw [generalUnfolding, of_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have h : (Sum.rec (motive := fun s => Fin (n (p s))) (fun j => i (p (.inl j)))
      (fun j => i (p (.inr j))) : ∀ s, Fin (n (p s))) = fun s => i (p s) := by
    funext s
    cases s <;> rfl
  rw [h]
  exact Tensor.permute_apply p A i

/-- The listing of the modes of a tensor of order $d + 1$ that gives the mode-$k$ unfolding: the
single row mode $k$, then the other modes, in increasing order, as the column modes. -/
def modalModes (k : Fin (d + 1)) : Fin 1 ⊕ Fin d ≃ Fin (d + 1) where
  toFun := Sum.elim (fun _ => k) k.succAbove
  invFun x := if h : x = k then .inl 0 else .inr ((finSuccAboveEquiv k).symm ⟨x, h⟩)
  left_inv s := by
    rcases s with s | s
    · simp [Fin.fin_one_eq_zero s]
    · change (if h : k.succAbove s = k then _ else _) = _
      split_ifs with h
      · exact absurd h (Fin.succAbove_ne k s)
      · exact congrArg Sum.inr
          ((finSuccAboveEquiv k).symm_apply_eq.2 (finSuccAboveEquiv_apply k s).symm)
  right_inv x := by
    by_cases h : x = k
    · simp [h]
    · have := (finSuccAboveEquiv k).apply_symm_apply ⟨x, h⟩
      simp only [finSuccAboveEquiv_apply, Subtype.ext_iff] at this
      simp [h, this]

/-- **Equation (12.4.8)** of [golub2013matrix], with the special cases in the sentences after it.
Let $\mathcal{A} \in \mathbb{R}^{n_1 \times \cdots \times n_d}$ with row modes $r$ and column
modes $c$. Then:

* for every index tuple $i$, $$\mathcal{A}_{r \times c}(\operatorname{col}(i(r), n(r)),
  \operatorname{col}(i(c), n(c))) = \mathcal{A}(i);$$
* for every tensor of order at least $1$ and every mode $k$, the general unfolding with
  $r = [k]$ and $c = [1, \dots, k-1, k+1, \dots, d]$ is the mode-$k$ unfolding
  $\mathcal{A}_{(k)}$;
* with $r = 1{:}d$ and $c = \emptyset$, the general unfolding $\mathcal{A}_{r \times c}$ is
  $\operatorname{vec}(\mathcal{A})$ as a one-column matrix.

The second part uses the listing `GolubVanLoan.Chapter12.modalModes k`, and compares the two
unfoldings at the position of each entry $\mathcal{A}(i)$. The third part uses the listing
`Equiv.sumEmpty (Fin d) (Fin 0)`. -/
theorem equation_12_4_8 (A : RTensor n) (p : Fin e ⊕ Fin f ≃ Fin d) (i : ∀ k, Fin (n k)) :
    generalUnfolding A p (finPiFinEquiv fun j => i (p (.inl j)))
        (finPiFinEquiv fun j => i (p (.inr j))) = A i ∧
      (∀ {d' : ℕ} {n' : Fin (d' + 1) → ℕ} (A' : RTensor n') (k : Fin (d' + 1))
          (i' : ∀ j, Fin (n' j)),
        generalUnfolding A' (modalModes k) (finPiFinEquiv fun j => i' (modalModes k (.inl j)))
            (finPiFinEquiv fun j => i' (modalModes k (.inr j))) =
          modalUnfolding A' k (i' k) (finPiFinEquiv fun j => i' (k.succAbove j))) ∧
      ∀ c, generalUnfolding A (Equiv.sumEmpty (Fin d) (Fin 0)) (finPiFinEquiv i) c =
        Tensor.vecFin A (finPiFinEquiv i) := by
  refine ⟨generalUnfolding_apply A p i, fun A' k i' => ?_, fun c => ?_⟩
  · rw [generalUnfolding_apply, equation_12_4_6]
  · obtain ⟨c, rfl⟩ := finPiFinEquiv.surjective c
    have h : c = fun j => i (Equiv.sumEmpty (Fin d) (Fin 0) (.inr j)) := funext fun j => j.elim0
    rw [h, Tensor.vecFin_apply]
    exact generalUnfolding_apply A _ i

end General

/-! ### Outer products and rank-one tensors (§12.4.7–12.4.8) -/

section Outer

variable {m₁ n₁ m₂ n₂ : ℕ}

/-- The listing $r = [3\ 1]$, $c = [4\ 2]$ of the modes of an order-4 tensor. In 0-based modes, the
row modes are $2, 0$ and the column modes are $3, 1$. -/
def kroneckerModes : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ![2, 0] ![3, 1]
  invFun := ![.inl 1, .inr 1, .inl 0, .inr 0]
  left_inv s := by rcases s with s | s <;> fin_cases s <;> rfl
  right_inv x := by fin_cases x <;> rfl

/-- **Section 12.4.7** of [golub2013matrix], the Kronecker product as an unfolding of an outer
product. Let $B \in \mathbb{R}^{n_1 \times n_2}$ and $C \in \mathbb{R}^{n_3 \times n_4}$, and
let $\mathcal{A} = B \circ C \in \mathbb{R}^{n_1 \times n_2 \times n_3 \times n_4}$ be their
outer product, $\mathcal{A}(i_1, i_2, j_1, j_2) = B(i_1, i_2) C(j_1, j_2)$. Then
$$\mathcal{A}_{[3\,1] \times [4\,2]} = B \otimes C.$$
So the Kronecker product of two matrices is their outer product as tensors.

The Kronecker product is `Matrix.kroneckerFin B C`, in the layout of the source. The unfolding
has $n_3 n_1$ rows and $n_4 n_2$ columns, and the Kronecker product has $n_1 n_3$ rows and
$n_2 n_4$ columns; the statement identifies these sizes by `finCongr`. The listing of the modes
is `GolubVanLoan.Chapter12.kroneckerModes`. -/
theorem outer_kronecker {n : Fin 4 → ℕ} (B : Matrix (Fin (n 0)) (Fin (n 1)) ℝ)
    (C : Matrix (Fin (n 2)) (Fin (n 3)) ℝ) :
    generalUnfolding (Tensor.of fun i => B (i 0) (i 1) * C (i 2) (i 3) : RTensor n)
        kroneckerModes =
      (kroneckerFin B C).submatrix
        (finCongr (by simp [kroneckerModes, Fin.prod_univ_two, mul_comm]))
        (finCongr (by simp [kroneckerModes, Fin.prod_univ_two, mul_comm])) := by
  ext R C'
  obtain ⟨r, rfl⟩ := finPiFinEquiv.surjective R
  obtain ⟨c, rfl⟩ := finPiFinEquiv.surjective C'
  set i : ∀ k, Fin (n k) := (Equiv.piCongrLeft (fun k => Fin (n k)) kroneckerModes)
    (Sum.rec (motive := fun s => Fin (n (kroneckerModes s))) r c) with hi
  have hr : r = fun j => i (kroneckerModes (.inl j)) := by
    funext j; rw [hi, Equiv.piCongrLeft_apply_apply]
  have hc : c = fun j => i (kroneckerModes (.inr j)) := by
    funext j; rw [hi, Equiv.piCongrLeft_apply_apply]
  rw [hr, hc, generalUnfolding_apply, submatrix_apply]
  have e1 : finCongr (by simp [kroneckerModes, Fin.prod_univ_two, mul_comm])
      (finPiFinEquiv fun j => i (kroneckerModes (.inl j))) =
        (finProdFinEquiv (i 0, i 2) : Fin (n 0 * n 2)) := by
    apply Fin.ext
    rw [finCongr_apply, Fin.val_cast, finPiFinEquiv_apply, Fin.sum_univ_two]
    (try simp [kroneckerModes]); ring
  have e2 : finCongr (by simp [kroneckerModes, Fin.prod_univ_two, mul_comm])
      (finPiFinEquiv fun j => i (kroneckerModes (.inr j))) =
        (finProdFinEquiv (i 1, i 3) : Fin (n 1 * n 3)) := by
    apply Fin.ext
    rw [finCongr_apply, Fin.val_cast, finPiFinEquiv_apply, Fin.sum_univ_two]
    (try simp [kroneckerModes]); ring
  rw [e1, e2, kroneckerFin_apply, Tensor.of_apply]

end Outer

section RankOne

variable {n : Fin d → ℕ}

/-- **Section 12.4.8** of [golub2013matrix], last display. Every $\mathcal{A} \in \mathbb{R}^{n_1
\times \cdots \times n_d}$ is the sum
$$\mathcal{A} = \sum_{i=1}^{n} \mathcal{A}(i) \, I_{n_1}(:, i_1) \circ \cdots \circ I_{n_d}(:,
  i_d)$$
over all index tuples $i$, of rank-one tensors of columns of identity matrices.

The column $I_{n_k}(:, i_k)$ is `Pi.single (i k) 1`, and the outer product of the columns is
`Tensor.rankOne`. -/
theorem eq_sum_rankOne (A : RTensor n) :
    A = ∑ i, A i • Tensor.rankOne (κ := fun k : Fin d => Fin (n k))
      (fun k => (Pi.single (i k) (1 : ℝ) : Fin (n k) → ℝ)) :=
  Tensor.eq_sum_rankOne_single A

/-- For vectors $z^{(k)} \in \mathbb{R}^{n_k}$, the vectorization of the rank-one tensor
$z^{(1)} \circ \cdots \circ z^{(d)}$ is the Kronecker product
$z^{(d)} \otimes \cdots \otimes z^{(1)}$; for example, $\operatorname{vec}(u \circ v \circ w) =
w \otimes v \otimes u$. The Kronecker product is the family product `Matrix.piKronecker` of the
one-column matrices $z^{(k)}$, flattened by `finPiFinEquiv` and read in its only column. -/
theorem vecFin_rankOne (z : ∀ k, Fin (n k) → ℝ) (t : Fin (∏ k, n k)) :
    Tensor.vecFin (Tensor.rankOne z : RTensor n) t =
      ((piKronecker fun k => replicateCol (Fin 1) (z k)).reindex finPiFinEquiv finPiFinEquiv) t
        (finPiFinEquiv fun _ => 0) := by
  obtain ⟨a, rfl⟩ := finPiFinEquiv.surjective t
  simp [reindex_apply, replicateCol_apply]

/-- **Equation (12.4.9)** of [golub2013matrix]. Let $z^{(k)} \in \mathbb{R}^{n_k}$ for
$k = 1, \dots, d$, and let $\mathcal{A} = z^{(1)} \circ \cdots \circ z^{(d)}$. Then for every
mode $k$,
$$\mathcal{A}_{(k)} = z^{(k)} \bigl(z^{(d)} \otimes \cdots \otimes z^{(k+1)} \otimes z^{(k-1)}
  \otimes \cdots \otimes z^{(1)}\bigr)^T.$$

The Lean tensor has order `d + 1`. The product $x y^T$ is `Matrix.vecMulVec x y`. The Kronecker
product of the other factors is written as the vectorization of their rank-one tensor, which is
that Kronecker product by `GolubVanLoan.Chapter12.vecFin_rankOne`. -/
theorem equation_12_4_9 {n : Fin (d + 1) → ℕ} (z : ∀ k, Fin (n k) → ℝ) (k : Fin (d + 1)) :
    modalUnfolding (Tensor.rankOne z : RTensor n) k =
      vecMulVec (z k) (Tensor.vecFin (Tensor.rankOne fun j : Fin d => z (k.succAbove j) :
        RTensor fun j => n (k.succAbove j))) := by
  ext x c
  obtain ⟨b, rfl⟩ := finPiFinEquiv.surjective c
  have := equation_12_4_6 (Tensor.rankOne z : RTensor n) k (Fin.insertNth k x b)
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at this
  rw [this, vecMulVec_apply, Tensor.vecFin_apply, Tensor.rankOne_apply, Tensor.rankOne_apply,
    Fin.prod_univ_succAbove _ k]
  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/-- **Equation (12.4.10)** of [golub2013matrix]. Let $\mathcal{A} = z^{(1)} \circ \cdots \circ
z^{(d)}$ with $z^{(k)} \in \mathbb{R}^{n_k}$, and let the row modes be $r = p(1{:}e)$ and the
column modes $c = p(e+1{:}d)$ for a permutation $p$ of $1{:}d$. Then
$$\mathcal{A}_{r \times c} = \bigl(z^{(p_e)} \otimes \cdots \otimes z^{(p_1)}\bigr)
  \bigl(z^{(p_d)} \otimes \cdots \otimes z^{(p_{e+1})}\bigr)^T.$$

The permutation is the listing `p : Fin e ⊕ Fin f ≃ Fin d`. The product $x y^T$ is
`Matrix.vecMulVec x y`, and each Kronecker product of vectors is written as the vectorization of
the rank-one tensor of its factors (`GolubVanLoan.Chapter12.vecFin_rankOne`). -/
theorem equation_12_4_10 {e f : ℕ} (z : ∀ k, Fin (n k) → ℝ) (p : Fin e ⊕ Fin f ≃ Fin d) :
    generalUnfolding (Tensor.rankOne z : RTensor n) p =
      vecMulVec (Tensor.vecFin (Tensor.rankOne fun j : Fin e => z (p (.inl j)) :
          RTensor fun j => n (p (.inl j))))
        (Tensor.vecFin (Tensor.rankOne fun j : Fin f => z (p (.inr j)) :
          RTensor fun j => n (p (.inr j)))) := by
  ext R C
  obtain ⟨r, rfl⟩ := finPiFinEquiv.surjective R
  obtain ⟨c, rfl⟩ := finPiFinEquiv.surjective C
  set i : ∀ k, Fin (n k) := (Equiv.piCongrLeft (fun k => Fin (n k)) p)
    (Sum.rec (motive := fun s => Fin (n (p s))) r c) with hi
  have hr : r = fun j => i (p (.inl j)) := by
    funext j; rw [hi, Equiv.piCongrLeft_apply_apply]
  have hc : c = fun j => i (p (.inr j)) := by
    funext j; rw [hi, Equiv.piCongrLeft_apply_apply]
  rw [hr, hc, generalUnfolding_apply, vecMulVec_apply, Tensor.vecFin_apply, Tensor.vecFin_apply,
    Tensor.rankOne_apply, Tensor.rankOne_apply, Tensor.rankOne_apply,
    ← Equiv.prod_comp p, Fintype.prod_sum_type]

end RankOne

/-! ### Contractions (12.4.11)–(12.4.13) -/

/-- **Equation (12.4.11)** of [golub2013matrix], with the slice form after it. Let $\mathcal{B} \in
\mathbb{R}^{n_1 \times t \times p_3 \times p_4}$ and $\mathcal{C} \in \mathbb{R}^{t \times n_2
\times q_3 \times q_4 \times q_5}$, and let $\mathcal{A} \in \mathbb{R}^{n_1 \times n_2 \times
p_3 \times p_4 \times q_3 \times q_4 \times q_5}$ be their contraction
$$\mathcal{A}(i, j, \alpha_3, \alpha_4, \beta_3, \beta_4, \beta_5) = \sum_{k=1}^{t}
  \mathcal{B}(i, k, \alpha_3, \alpha_4) \, \mathcal{C}(k, j, \beta_3, \beta_4, \beta_5).$$
Then for every fixed $\alpha = (\alpha_3, \alpha_4)$ and $\beta = (\beta_3, \beta_4, \beta_5)$,
the slices satisfy
$$\mathcal{A}(:, :, \alpha, \beta) = \mathcal{B}(:, :, \alpha) \, \mathcal{C}(:, :, \beta).$$

The three tensors are curried functions of their indices, not values of `Tensor`. -/
theorem equation_12_4_11 {n₁ t n₂ p₃ p₄ q₃ q₄ q₅ : ℕ}
    (B : Fin n₁ → Fin t → Fin p₃ → Fin p₄ → ℝ) (C : Fin t → Fin n₂ → Fin q₃ → Fin q₄ → Fin q₅ → ℝ)
    (A : Fin n₁ → Fin n₂ → Fin p₃ → Fin p₄ → Fin q₃ → Fin q₄ → Fin q₅ → ℝ)
    (hA : ∀ i j a₃ a₄ b₃ b₄ b₅, A i j a₃ a₄ b₃ b₄ b₅ = ∑ k, B i k a₃ a₄ * C k j b₃ b₄ b₅)
    (a₃ : Fin p₃) (a₄ : Fin p₄) (b₃ : Fin q₃) (b₄ : Fin q₄) (b₅ : Fin q₅) :
    (Matrix.of fun i j => A i j a₃ a₄ b₃ b₄ b₅) =
      (Matrix.of fun i k => B i k a₃ a₄) * Matrix.of fun k j => C k j b₃ b₄ b₅ := by
  ext i j
  rw [of_apply, hA, Matrix.mul_apply]
  rfl

/-- **Equations (12.4.12)–(12.4.13)** of [golub2013matrix], with the display after (12.4.13). Let
$\mathcal{B}$ be a tensor on the free modes $\iota_1$ and the contracted modes $\iota_2$, and
let $\mathcal{C}$ be a tensor on the same contracted modes $\iota_2$, with the same index sets,
and the free modes $\iota_3$. Assume that there are finitely many contracted modes and that each
has a finite index set. The contraction $\mathcal{A}$ of $\mathcal{B}$ and $\mathcal{C}$ is a
tensor on the modes $\iota_1$ and $\iota_3$ with
$$\mathcal{A}(x, z) = \sum_{y} \mathcal{B}(x, y) \, \mathcal{C}(y, z),$$
the sum over all index tuples $y$ of the contracted modes. Its unfolding with the rows $\iota_1$
and the columns $\iota_3$ is the product of the unfoldings of $\mathcal{B}$ and $\mathcal{C}$:
$$\mathcal{A}_{\iota_1 \times \iota_3} = \mathcal{B}_{\iota_1 \times \iota_2} \,
  \mathcal{C}_{\iota_2 \times \iota_3}.$$
In the example of the source this is $\mathcal{A}_{[1\,2] \times [3\,4\,5]} =
\mathcal{B}_{[1\,2] \times [3\,4]} \, \mathcal{C}_{[1\,2] \times [3\,4\,5]}$.

The contraction is `Tensor.contract B C`. The modes of each tensor are two blocks of a
`Sum`-indexed family, the index $(x, y)$ is `(Equiv.sumPiEquivProdPi _).symm (x, y)`, and the
unfoldings are the typed unfoldings `Tensor.sumUnfold`, whose rows and columns are index tuples.
The unfolding identity is the backbone's `Tensor.sumUnfold_contract`. -/
theorem equation_12_4_13 {ι₁ ι₂ ι₃ : Type} [Fintype ι₂] [DecidableEq ι₂] {κ₁ : ι₁ → Type}
    {κ₂ : ι₂ → Type} {κ₃ : ι₃ → Type} [∀ j, Fintype (κ₂ j)]
    (B : Tensor (Sum.elim κ₁ κ₂) ℝ) (C : Tensor (Sum.elim κ₂ κ₃) ℝ) :
    (∀ (x : ∀ i, κ₁ i) (z : ∀ l, κ₃ l),
      Tensor.contract B C ((Equiv.sumPiEquivProdPi _).symm (x, z)) =
        ∑ y : ∀ j, κ₂ j, B ((Equiv.sumPiEquivProdPi _).symm (x, y)) *
          C ((Equiv.sumPiEquivProdPi _).symm (y, z))) ∧
      Tensor.sumUnfold (Tensor.contract B C) = Tensor.sumUnfold B * Tensor.sumUnfold C :=
  ⟨Tensor.contract_apply B C, Tensor.sumUnfold_contract B C⟩

/-! ### Modal and multilinear products (12.4.14)–(12.4.19) -/

section ModeProduct

variable {n : Fin d → ℕ}

/-- **Section 12.4.10** of [golub2013matrix], definition of the mode-$k$ product. Let $\mathcal{S}
\in \mathbb{R}^{n_1 \times \cdots \times n_d}$, let $k$ be a mode, and let
$M \in \mathbb{R}^{m \times n_k}$. The **mode-$k$ product** $\mathcal{S} \times_k M \in
\mathbb{R}^{n_1 \times \cdots \times n_{k-1} \times m \times n_{k+1} \times \cdots \times n_d}$
is the multilinear product of $\mathcal{S}$ with $M$ in mode $k$ and identity matrices in the
other modes. Its entries are given in `GolubVanLoan.Chapter12.equation_12_4_14`.

The result has the shape `Function.update n k m`. The definition is the backbone's rectangular
mode product `Tensor.rectModeProd`, with the sizes off $k$ matched by `Function.update_of_ne`. -/
def modeProduct (n : Fin d → ℕ) (S : RTensor n) (k : Fin d) {m : ℕ}
    (M : Matrix (Fin m) (Fin (n k)) ℝ) : RTensor (Function.update n k m) :=
  S.rectModeProd k (μ := fun i => Fin (Function.update n k m i))
    (fun _ h => finCongr (Function.update_of_ne h m n))
    (M.reindex (finCongr (Function.update_self k m n).symm) (Equiv.refl _))

/-- For an index tuple $a$ of $\mathcal{S} \times_k M$ and an index $y$ of mode $k$ of
$\mathcal{S}$, the index tuple of $\mathcal{S}$ that is $y$ at mode $k$ and agrees with $a$ at
the other modes. It is the index of $\mathcal{S}$ that the entry $a$ of $\mathcal{S} \times_k M$
meets at the summation index $y$. -/
def spliceIndex (k : Fin d) {m : ℕ} (a : ∀ i, Fin (Function.update n k m i)) (y : Fin (n k)) :
    ∀ i, Fin (n i) := fun i =>
  if h : i = k then Fin.cast (congrArg n h.symm) y
  else Fin.cast (Function.update_of_ne h m n) (a i)

/-- The index tuple `spliceIndex k a y` has the value $y$ at mode $k$ and the value $a_i$ at every
mode $i \neq k$. -/
theorem val_spliceIndex (k : Fin d) {m : ℕ} (a : ∀ i, Fin (Function.update n k m i))
    (y : Fin (n k)) (i : Fin d) :
    (spliceIndex k a y i : ℕ) = if i = k then (y : ℕ) else a i := by
  unfold spliceIndex
  split_ifs <;> simp

/-- **Equation (12.4.14)** of [golub2013matrix], with the entry formula after it. Let $\mathcal{S}
\in \mathbb{R}^{n_1 \times \cdots \times n_d}$, let $k$ be a mode, and let
$M \in \mathbb{R}^{m \times n_k}$. Then
$$(\mathcal{S} \times_k M)_{(k)} = M \, \mathcal{S}_{(k)},$$
and for every index tuple $\alpha$ of $\mathcal{S} \times_k M$ with $\alpha_k = i$,
$$(\mathcal{S} \times_k M)(\alpha_1, \dots, \alpha_{k-1}, i, \alpha_{k+1}, \dots, \alpha_d) =
  \sum_{j=1}^{n_k} M(i, j) \, \mathcal{S}(\alpha_1, \dots, \alpha_{k-1}, j, \alpha_{k+1}, \dots,
  \alpha_d).$$

The unfoldings are the typed unfoldings `Tensor.modeUnfold`. The first identity holds up to the
identifications of the size `Function.update n k m k` with $m$ and of `Function.update n k m j`
with $n_j$ for $j \neq k$. In the second identity the index of $\mathcal{S}$ is
`GolubVanLoan.Chapter12.spliceIndex` applied to $k$, $\alpha$ and $j$. The first identity is the
backbone's `Tensor.modeUnfold_rectModeProd`. -/
theorem equation_12_4_14 (S : RTensor n) (k : Fin d) {m : ℕ} (M : Matrix (Fin m) (Fin (n k)) ℝ) :
    (modeProduct n S k M).modeUnfold k =
        (M * S.modeUnfold k).reindex (finCongr (Function.update_self k m n).symm)
          (Equiv.piCongrRight fun j : {j // j ≠ k} =>
            finCongr (Function.update_of_ne j.2 m n).symm) ∧
      ∀ a : ∀ i, Fin (Function.update n k m i), modeProduct n S k M a =
        ∑ y : Fin (n k), M (Fin.cast (Function.update_self k m n) (a k)) y *
          S (spliceIndex k a y) := by
  have h1 : (modeProduct n S k M).modeUnfold k =
      (M * S.modeUnfold k).reindex (finCongr (Function.update_self k m n).symm)
        (Equiv.piCongrRight fun j : {j // j ≠ k} =>
          finCongr (Function.update_of_ne j.2 m n).symm) := by
    rw [modeProduct, Tensor.modeUnfold_rectModeProd]
    ext x c
    simp only [submatrix_apply, reindex_apply, Matrix.mul_apply, id, Equiv.refl_symm,
        Equiv.coe_refl]
    rfl
  refine ⟨h1, fun a => ?_⟩
  rw [← Tensor.modeUnfold_apply (modeProduct n S k M) k a, h1, reindex_apply, submatrix_apply,
    Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  simp only [Tensor.modeUnfold, of_apply]
  congr 1
  funext i
  by_cases h : i = k
  · subst h
    simp [spliceIndex, Equiv.piSplitAt_symm_apply]
  · simp [spliceIndex, Equiv.piSplitAt_symm_apply, h]

/-- The entries of a mode-$k$ product with $M \in \mathbb{R}^{m \times n_k}$: $(\mathcal{S} \times_k
M)(\alpha) = \sum_{j=1}^{n_k} M(\alpha_k, j) \, \mathcal{S}(\alpha')$, where $\alpha'$ is
$\alpha$ with its $k$-th index replaced by $j$. This is the second part of
`GolubVanLoan.Chapter12.equation_12_4_14`. -/
theorem modeProduct_apply (S : RTensor n) (k : Fin d) {m : ℕ} (M : Matrix (Fin m) (Fin (n k)) ℝ)
    (a : ∀ i, Fin (Function.update n k m i)) :
    modeProduct n S k M a = ∑ y : Fin (n k),
      M (Fin.cast (Function.update_self k m n) (a k)) y * S (spliceIndex k a y) :=
  (equation_12_4_14 S k M).2 a

/-- A tensor read in an equal shape: for shapes $n = n'$, the tensor of shape $n'$ that has the same
entries as $\mathcal{A}$. -/
def castShape {n' : Fin d → ℕ} (h : n = n') (A : RTensor n) : RTensor n' :=
  h ▸ A

/-- The entry of a tensor read in an equal shape, at an index tuple $i$, is the entry of the
original tensor at the same indices, cast to the original shape. -/
theorem castShape_apply {n' : Fin d → ℕ} (h : n = n') (A : RTensor n) (i : ∀ k, Fin (n' k)) :
    castShape h A i = A fun k => Fin.cast (congrFun h k).symm (i k) := by
  subst h
  rfl

/-- A rectangular mode product $\mathcal{S} \times_k M$ of shape $s$, read in an equal shape $s'$,
is the rectangular mode product into the shape $s'$, with the equivalences of the sizes off $k$
and the rows of $M$ read through the casts. -/
theorem castShape_rectModeProd {s s' : Fin d → ℕ} (h : s = s') (S : RTensor n) (k : Fin d)
    (e : ∀ i, i ≠ k → Fin (s i) ≃ Fin (n i)) (M : Matrix (Fin (s k)) (Fin (n k)) ℝ) :
    castShape h (S.rectModeProd k (μ := fun i => Fin (s i)) e M) =
      S.rectModeProd k (μ := fun i => Fin (s' i))
        (fun i hi => (finCongr (congrFun h i).symm).trans (e i hi))
        (M.submatrix (finCongr (congrFun h k).symm) id) := by
  subst h
  rfl

/-- **Equation (12.4.16)** of [golub2013matrix]. Let $\mathcal{S} \in \mathbb{R}^{n_1 \times \cdots
\times n_d}$, let $j \neq k$ be two modes, and let $F \in \mathbb{R}^{p \times n_k}$ and
$G \in \mathbb{R}^{q \times n_j}$. Then mode products in the distinct modes commute:
$$(\mathcal{S} \times_k F) \times_j G = (\mathcal{S} \times_j G) \times_k F.$$

The two sides have the shapes `Function.update (Function.update n k p) j q` and
`Function.update (Function.update n j q) k p`. These are equal by `Function.update_comm`, and
the right side is read in the shape of the left side through `GolubVanLoan.Chapter12.castShape`.
Each second factor has its columns re-indexed into the corresponding size of the updated shape.
The proof specializes the backbone's `Tensor.rectModeProd_comm`. -/
theorem equation_12_4_16 (S : RTensor n) {j k : Fin d} (hjk : j ≠ k) {p q : ℕ}
    (F : Matrix (Fin p) (Fin (n k)) ℝ) (G : Matrix (Fin q) (Fin (n j)) ℝ) :
    modeProduct (Function.update n k p) (modeProduct n S k F) j
        (G.reindex (Equiv.refl _) (finCongr (Function.update_of_ne hjk p n).symm)) =
      castShape (Function.update_comm hjk q p n)
        (modeProduct (Function.update n j q) (modeProduct n S j G) k
          (F.reindex (Equiv.refl _) (finCongr (Function.update_of_ne hjk.symm q n).symm))) := by
  rw [modeProduct, modeProduct, modeProduct, modeProduct, castShape_rectModeProd,
    Tensor.rectModeProd_comm _ hjk (f := fun _ h => finCongr (Function.update_of_ne h q n))
      (f' := fun i hi => (finCongr (congrFun (Function.update_comm hjk q p n) i).symm).trans
        (finCongr (Function.update_of_ne hi p (Function.update n j q))))]
  · congr 1
  · intro i hj hk
    ext x
    simp

/-- **Equation (12.4.17)** of [golub2013matrix]. Let $\mathcal{S} \in \mathbb{R}^{n_1 \times \cdots
\times n_d}$, let $k$ be a mode, and let $F \in \mathbb{R}^{p \times n_k}$ and
$G \in \mathbb{R}^{q \times p}$. Then
$$(\mathcal{S} \times_k F) \times_k G = \mathcal{S} \times_k (GF).$$

**Correction.** The source prints $\mathcal{S} \times_k (FG)$. This is false: $(\mathcal{S}
\times_k F)_{(k)} = F \mathcal{S}_{(k)}$ by (12.4.14), so the second product gives
$G F \mathcal{S}_{(k)}$. For rectangular $F$ and $G$ the product $FG$ is not even defined.

The two sides have the shapes `Function.update (Function.update n k p) k q` and
`Function.update n k q`, identified along `Function.update_idem`. The proof specializes the
backbone's `Tensor.rectModeProd_rectModeProd`. -/
theorem equation_12_4_17 (S : RTensor n) (k : Fin d) {p q : ℕ} (F : Matrix (Fin p) (Fin (n k)) ℝ)
    (G : Matrix (Fin q) (Fin p) ℝ) :
    modeProduct (Function.update n k p) (modeProduct n S k F) k
        (G.reindex (Equiv.refl _) (finCongr (Function.update_self k p n).symm)) =
      castShape (Function.update_idem (a := k) p q n).symm (modeProduct n S k (G * F)) := by
  rw [modeProduct, modeProduct, modeProduct, castShape_rectModeProd,
    Tensor.rectModeProd_rectModeProd]
  congr 1
  ext a b
  simp only [reindex_apply, submatrix_apply, Matrix.mul_apply, id, Equiv.refl_symm, Equiv.coe_refl]
  rw [← (finCongr (Function.update_self k p n)).sum_comp]
  rfl

/-- Equation (12.4.14) for a square factor: for $M \in \mathbb{R}^{n_k \times n_k}$, the mode-$k$
product $\mathcal{S} \times_k M$ agrees with the backbone's shape-preserving mode product
`Tensor.modeProd`, up to the identification of the shape `Function.update n k (n k)` with $n$. -/
theorem modeProduct_eq_modeProd (S : RTensor n) (k : Fin d)
    (M : Matrix (Fin (n k)) (Fin (n k)) ℝ) :
    modeProduct n S k M = castShape (Function.update_eq_self k n).symm (S.modeProd k M) := by
  rw [← Tensor.rectModeProd_refl, castShape_rectModeProd, modeProduct]
  congr 1

end ModeProduct

/-! ### Vectorizing a mode product (12.4.15) -/

section VecModeProduct

/-- The product $n_1 \cdots n_{k-1}$ of the sizes of the modes before mode $k$ (in 0-based modes,
the modes $0, \dots, k - 1$). It is $1$ for the first mode. -/
def lowerSize (n : Fin d → ℕ) (k : Fin d) : ℕ :=
  ∏ j : Fin k, n (Fin.castLE k.2.le j)

/-- The product $n_{k+1} \cdots n_d$ of the sizes of the modes after mode $k$. It is $1$ for the
last mode. -/
def upperSize (n : Fin d → ℕ) (k : Fin d) : ℕ :=
  ∏ j : Fin (d - (k + 1)), n ⟨k + 1 + j, by have := j.2; omega⟩

/-- For every mode $k$, $n_1 \cdots n_d = (n_{k+1} \cdots n_d) \, n_k \, (n_1 \cdots n_{k-1})$. -/
theorem prod_eq_upperSize_mul (n : Fin d → ℕ) (k : Fin d) :
    ∏ i, n i = upperSize n k * n k * lowerSize n k := by
  set g : ℕ → ℕ := fun l => if h : l < d then n ⟨l, h⟩ else 1 with hg
  have hT : ∏ i, n i = ∏ i : Fin d, g i := Finset.prod_congr rfl fun i _ => by
    rw [hg]; simp only [i.2, ↓reduceDIte]
  have hL : lowerSize n k = ∏ j : Fin k, g j := Finset.prod_congr rfl fun j _ => by
    rw [hg]; simp only [show (j : ℕ) < d by omega, ↓reduceDIte]; rfl
  have hU : upperSize n k = ∏ j : Fin (d - (k + 1)), g (k + 1 + j) :=
    Finset.prod_congr rfl fun j _ => by
      rw [hg]; simp only [show (k : ℕ) + 1 + j < d by omega, ↓reduceDIte]
  have hk : g k = n k := by rw [hg]; simp only [k.2, ↓reduceDIte]
  have hd : d = k + 1 + (d - (k + 1)) := by omega
  rw [hT, hL, hU, Fin.prod_univ_eq_prod_range g d, Fin.prod_univ_eq_prod_range g k,
    Fin.prod_univ_eq_prod_range (fun j => g (k + 1 + j)),
    show Finset.range d = Finset.range (k + 1 + (d - (k + 1))) by rw [← hd],
    Finset.prod_range_add, Finset.prod_range_succ, hk]
  ring

/-- For every mode $k$ and every $m$, the product of the sizes
$n_1, \dots, n_{k-1}, m, n_{k+1}, \dots, n_d$, which is the number of entries of
$\mathcal{S} \times_k M$ for $M \in \mathbb{R}^{m \times n_k}$, is $(n_{k+1} \cdots n_d) \, m \,
(n_1 \cdots n_{k-1})$. -/
theorem prod_update_eq_upperSize_mul (n : Fin d → ℕ) (k : Fin d) (m : ℕ) :
    ∏ i, Function.update n k m i = upperSize n k * m * lowerSize n k := by
  have hU : upperSize (Function.update n k m) k = upperSize n k :=
    Finset.prod_congr rfl fun j _ => Function.update_of_ne
      (Fin.ne_of_val_ne (show (k : ℕ) + 1 + j ≠ k by omega)) _ _
  have hL : lowerSize (Function.update n k m) k = lowerSize n k :=
    Finset.prod_congr rfl fun j _ => Function.update_of_ne
      (Fin.ne_of_val_ne (show (j : ℕ) ≠ k by omega)) _ _
  rw [prod_eq_upperSize_mul (Function.update n k m) k, Function.update_self, hU, hL]

/-- Re-indexing the rows of the middle factor $M$ of $I_H \otimes M \otimes I_L$ along an equality
of row counts does not change the product, after the matching casts of its rows. -/
private theorem kroneckerFin_reindex_cast {R : Type*} [CommSemiring R] {H L a b p N P : ℕ}
    (h : a = b) (M : Matrix (Fin a) (Fin p) R) (hN : N = H * b * L) (hN' : N = H * a * L)
    (c : Fin P → Fin (H * p * L)) :
    (kroneckerFin (kroneckerFin (1 : Matrix (Fin H) (Fin H) R)
        (M.reindex (finCongr h) (Equiv.refl _))) (1 : Matrix (Fin L) (Fin L) R)).submatrix
        (finCongr hN) c =
      (kroneckerFin (kroneckerFin (1 : Matrix (Fin H) (Fin H) R) M)
        (1 : Matrix (Fin L) (Fin L) R)).submatrix (finCongr hN') c := by
  subst h
  rfl

/-- **Equation (12.4.15)** of [golub2013matrix]. Let $\mathcal{S} \in \mathbb{R}^{n_1 \times \cdots
\times n_d}$, let $k$ be a mode, and let $M \in \mathbb{R}^{m \times n_k}$. Then
$$\operatorname{vec}(\mathcal{S} \times_k M) = \bigl(I_{n_{k+1} \cdots n_d} \otimes M \otimes
  I_{n_1 \cdots n_{k-1}}\bigr) \operatorname{vec}(\mathcal{S}).$$

The Kronecker product is the positional `Matrix.kroneckerFin`, and $\operatorname{vec}$ is
`Tensor.vecFin`. The sizes are identified by
`GolubVanLoan.Chapter12.prod_update_eq_upperSize_mul` and
`GolubVanLoan.Chapter12.prod_eq_upperSize_mul`. The proof specializes the backbone's
`Tensor.vecFin_rectModeProd`. -/
theorem equation_12_4_15 {n : Fin d → ℕ} (S : RTensor n) (k : Fin d) {m : ℕ}
    (M : Matrix (Fin m) (Fin (n k)) ℝ) :
    Tensor.vecFin (modeProduct n S k M) =
      (kroneckerFin (kroneckerFin (1 : Matrix (Fin (upperSize n k)) (Fin (upperSize n k)) ℝ) M)
          (1 : Matrix (Fin (lowerSize n k)) (Fin (lowerSize n k)) ℝ)).submatrix
        (finCongr (prod_update_eq_upperSize_mul n k m)) (finCongr (prod_eq_upperSize_mul n k)) *ᵥ
        Tensor.vecFin S := by
  have h := Tensor.vecFin_rectModeProd S k (m := Function.update n k m)
    (fun _ h => Function.update_of_ne h m n)
    (M.reindex (finCongr (Function.update_self k m n).symm) (Equiv.refl _))
  rw [modeProduct, h, kroneckerFin_reindex_cast (Function.update_self k m n).symm M]
  rfl

end VecModeProduct

/-! ### The multilinear product of order 4 (12.4.18)–(12.4.19) -/

section Order4

/-- For an order-4 index tuple $a$ with 0-based indices, the 0-based position $\operatorname{col}(a,
n) - 1 = a_1 + n_1 a_2 + n_1 n_2 a_3 + n_1 n_2 n_3 a_4$ is the big-endian position of the nested
pair $(a_4, (a_3, (a_2, a_1)))$ under `finProdFinEquiv`, up to the identification of
$n_1 n_2 n_3 n_4$ with $n_4 (n_3 (n_2 n_1))$. -/
theorem finPiFinEquiv_four {n : Fin 4 → ℕ} (h : ∏ k, n k = n 3 * (n 2 * (n 1 * n 0)))
    (a : ∀ k, Fin (n k)) :
    finCongr h (finPiFinEquiv a) =
      finProdFinEquiv (a 3, finProdFinEquiv (a 2, finProdFinEquiv (a 1, a 0))) := by
  apply Fin.ext
  rw [finCongr_apply, Fin.val_cast, finPiFinEquiv_apply]
  simp [Fin.sum_univ_four, finProdFinEquiv_apply_val, Fin.prod_univ_succ]
  ring

/-- **Equations (12.4.18)–(12.4.19)** of [golub2013matrix], for order 4, with the table after
(12.4.19). Let $\mathcal{S} \in \mathbb{R}^{n_1 \times n_2 \times n_3 \times n_4}$ and
$M_k \in \mathbb{R}^{m_k \times n_k}$ for $k = 1, \dots, 4$, and let $\mathcal{A} = \mathcal{S}
\times_1 M_1 \times_2 M_2 \times_3 M_3 \times_4 M_4$ be their multilinear product. Then for
every index tuple $i$,
$$\mathcal{A}(i) = \sum_{j} \mathcal{S}(j) \, M_1(i_1, j_1) \, M_2(i_2, j_2) \, M_3(i_3, j_3) \,
  M_4(i_4, j_4),$$
the sum over all index tuples $j$ of $\mathcal{S}$, and
$$\operatorname{vec}(\mathcal{A}) = (M_4 \otimes M_3 \otimes M_2 \otimes M_1)
  \operatorname{vec}(\mathcal{S}).$$
Moreover, for square matrices $N_k \in \mathbb{R}^{n_k \times n_k}$, the multilinear product
$\mathcal{S} \times_1 N_1 \times_2 N_2 \times_3 N_3 \times_4 N_4$ equals the sequence of the
four mode products taken in the order $1, 2, 3, 4$, and also in the order $4, 1, 2, 3$:
$$\mathcal{S} \times_1 N_1 \times_2 N_2 \times_3 N_3 \times_4 N_4 = (((\mathcal{S} \times_1 N_1)
  \times_2 N_2) \times_3 N_3) \times_4 N_4 = (((\mathcal{S} \times_4 N_4) \times_1 N_1) \times_2
  N_2) \times_3 N_3.$$

The multilinear product is `Tensor.multilinearProd`, and the sequence of mode products is a fold
of the shape-preserving `Tensor.modeProd` over the list of modes. The Kronecker product is the
positional `Matrix.kroneckerFin`, and the sizes are identified by `finCongr`. The source says
that the mode products can be taken in any order; the statement gives the two orders above, and
`GolubVanLoan.Chapter12.equation_12_4_16` gives the commutation of mode products in distinct
modes. -/
theorem equation_12_4_19 {n m : Fin 4 → ℕ} (M : ∀ k, Matrix (Fin (m k)) (Fin (n k)) ℝ)
    (S : RTensor n) :
    (∀ i, (Tensor.multilinearProd M S : RTensor m) i = ∑ j, S j * ∏ k, M k (i k) (j k)) ∧
      Tensor.vecFin (Tensor.multilinearProd M S : RTensor m) =
        (kroneckerFin (M 3) (kroneckerFin (M 2) (kroneckerFin (M 1) (M 0)))).submatrix
          (finCongr (by rw [Fin.prod_univ_four]; ring))
          (finCongr (by rw [Fin.prod_univ_four]; ring)) *ᵥ
          Tensor.vecFin S ∧
      ∀ (N : ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℝ),
        Tensor.multilinearProd N S =
            [0, 1, 2, 3].foldl (fun T k => T.modeProd k (N k)) S ∧
          Tensor.multilinearProd N S =
            [3, 0, 1, 2].foldl (fun T k => T.modeProd k (N k)) S := by
  refine ⟨fun i => ?_, ?_, fun N => ⟨?_, ?_⟩⟩
  · rw [Tensor.multilinearProd_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · rw [Tensor.vecFin_multilinearProd]
    congr 1
    ext I J
    obtain ⟨a, rfl⟩ := finPiFinEquiv.surjective I
    obtain ⟨b, rfl⟩ := finPiFinEquiv.surjective J
    rw [reindex_apply, submatrix_apply, submatrix_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply, finPiFinEquiv_four, finPiFinEquiv_four, kroneckerFin_apply,
      kroneckerFin_apply, kroneckerFin_apply, piKronecker_apply, Fin.prod_univ_four]
    ring
  · exact Tensor.multilinearProd_eq_modeProd N (by decide) (by decide) S
  · exact Tensor.multilinearProd_eq_modeProd N (by decide) (by decide) S

end Order4

/-! ### Theorem 12.4.1 -/

section Theorem1241

variable {n m : Fin (d + 1) → ℕ}

/-- **Theorem 12.4.1** of [golub2013matrix]. Let $\mathcal{S} \in \mathbb{R}^{n_1 \times \cdots
\times n_d}$ with $d \ge 1$, let $M_k \in \mathbb{R}^{m_k \times n_k}$ for $k = 1, \dots, d$,
and let $\mathcal{A} = \mathcal{S} \times_1 M_1 \times_2 M_2 \cdots \times_d M_d$. Then for
every mode $k$,
$$\mathcal{A}_{(k)} = M_k \, \mathcal{S}_{(k)} \, \bigl(M_d \otimes \cdots \otimes M_{k+1}
  \otimes M_{k-1} \otimes \cdots \otimes M_1\bigr)^T.$$

The Lean tensors have order `d + 1`. The multilinear product is `Tensor.multilinearProd M S`,
and the unfoldings are the flattened `GolubVanLoan.Chapter12.modalUnfolding`. The Kronecker
product of the other factors is the family product `Matrix.piKronecker` flattened by
`finPiFinEquiv`, which is the product in the reversed order of the source by
`Matrix.piKronecker_reindex_finPiFinEquiv`. -/
theorem theorem_12_4_1 (M : ∀ k, Matrix (Fin (m k)) (Fin (n k)) ℝ) (S : RTensor n)
    (k : Fin (d + 1)) :
    modalUnfolding (Tensor.multilinearProd M S : RTensor m) k =
      M k * modalUnfolding S k *
        ((piKronecker fun j : Fin d => M (k.succAbove j)).reindex finPiFinEquiv
          finPiFinEquiv)ᵀ := by
  have hP : (piKronecker fun j : {j // j ≠ k} => M j).reindex (modalColumnEquiv m k)
      (modalColumnEquiv n k) =
        (piKronecker fun j : Fin d => M (k.succAbove j)).reindex finPiFinEquiv finPiFinEquiv := by
    ext a b
    obtain ⟨a', rfl⟩ := (modalColumnEquiv m k).surjective a
    obtain ⟨b', rfl⟩ := (modalColumnEquiv n k).surjective b
    simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, piKronecker_apply,
      modalColumnEquiv_symm_apply]
    rw [← (finSuccAboveEquiv k).prod_comp]
    rfl
  rw [modalUnfolding, Tensor.modeUnfold_multilinearProd, modalUnfolding, ← hP]
  simp only [reindex_apply, Equiv.refl_symm, Equiv.coe_refl, transpose_submatrix]
  rw [Matrix.submatrix_mul _ _ id (modalColumnEquiv n k).symm _
      (modalColumnEquiv n k).symm.bijective,
    Matrix.submatrix_mul _ _ id id _ Function.bijective_id, submatrix_id_id]

/-- **Theorem 12.4.1** of [golub2013matrix], second statement. Let $\mathcal{S}, \mathcal{A} \in
\mathbb{R}^{n_1 \times \cdots \times n_d}$, and let $M_k \in \mathbb{R}^{n_k \times n_k}$ be
nonsingular for $k = 1, \dots, d$. If $\mathcal{A} = \mathcal{S} \times_1 M_1 \cdots \times_d
M_d$, then
$$\mathcal{S} = \mathcal{A} \times_1 M_1^{-1} \cdots \times_d M_d^{-1}.$$

Nonsingularity is `IsUnit (M k)`, and the multilinear product is `Tensor.multilinearProd`. -/
theorem theorem_12_4_1_b {n : Fin d → ℕ} (M : ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℝ)
    (hM : ∀ k, IsUnit (M k)) (S A : RTensor n) (h : A = Tensor.multilinearProd M S) :
    S = Tensor.multilinearProd (fun k => (M k)⁻¹) A :=
  Tensor.multilinearProd_inv hM h

end Theorem1241

end GolubVanLoan.Chapter12
