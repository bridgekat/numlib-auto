/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a new `Mathlib.LinearAlgebra.Tensor` directory beside `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.LinearAlgebra.Tensor.Basic

/-!
# Unfoldings and contractions of tensors

An unfolding (matricization) of a tensor $\mathcal{A}$ arranges its entries in a matrix whose rows
are indexed by the indices of some modes and whose columns are indexed by the indices of the other
modes ([golub2013matrix], §12.4.5–12.4.6). The mode-$k$ unfolding $\mathcal{A}_{(k)}$ has the rows
indexed by mode $k$ and the columns indexed by the other modes, so its columns are the mode-$k$
fibers. This module proves that unfoldings preserve the Frobenius norm, that an unfolding of a
rank-one tensor is a rank-one matrix, and that the Kronecker product $B \otimes C$ is an unfolding
of the outer product of $B$ and $C$.

A tensor whose modes are a disjoint union $\iota_1 \sqcup \iota_2$ has an unfolding with the rows
indexed by the $\iota_1$-tuples and the columns indexed by the $\iota_2$-tuples. In this unfolding,
a contraction of tensors over common modes ([golub2013matrix], §12.4.9) is a matrix product.

## Main definitions

* `Tensor.unfold`, `Tensor.unfoldLinearEquiv`: the unfolding with the row modes $\{i \mid p(i)\}$
  and the column modes $\{i \mid \neg p(i)\}$.
* `Tensor.modeUnfold`: the mode-$k$ unfolding $\mathcal{A}_{(k)}$.
* `Tensor.sumUnfold`: the unfolding of a tensor with modes $\iota_1 \sqcup \iota_2$.
* `Tensor.contract`: the contraction of two tensors over common modes.

## Main results

* `Tensor.frobenius_norm_unfold`, `Tensor.frobenius_norm_modeUnfold`: unfoldings preserve the
  Frobenius norm.
* `Tensor.unfold_rankOne`, `Tensor.modeUnfold_rankOne`: an unfolding of a rank-one tensor is a
  rank-one matrix.
* `Tensor.unfold_outer_eq_kronecker`: the Kronecker product $B \otimes C$ is an unfolding of the
  outer product of $B$ and $C$.

## Implementation notes

* The unfoldings are typed. The rows of `A.unfold p` are the tuples `∀ i : {i // p i}, κ i`, and its
  columns are the tuples `∀ i : {i // ¬p i}, κ i`, through `Equiv.piEquivPiSubtypeProd`. The
  mode-$k$ unfolding `A.modeUnfold k` has the rows `κ k` and the columns `∀ j : {j // j ≠ k}, κ j`,
  through `Equiv.piSplitAt`.
* The order in which [golub2013matrix] lists the row modes and the column modes, and its numbering
  of the flattened indices, matter only after the index tuples are flattened to `Fin`. This
  flattening is left to the modules that use the unfoldings.
-/

universe u v w

open scoped Kronecker Matrix

namespace Tensor

variable {ι : Type u} {κ : ι → Type v} {R : Type w}

/-! ### Unfolding along a predicate -/

section Unfold

variable (p : ι → Prop) [DecidablePred p]

/-- The **unfolding** $\mathcal{A}_{r \times c}$ of a tensor $\mathcal{A}$ with the row modes
$\{i \mid p(i)\}$ and the column modes $\{i \mid \neg p(i)\}$ ([golub2013matrix], (12.4.8)). It
is the matrix whose entry in the row $r$ and the column $c$ is the entry of $\mathcal{A}$ at the
tuple that agrees with $r$ on the row modes and with $c$ on the column modes.

The rows are indexed by the tuples `∀ i : {i // p i}, κ i`, and the columns by the tuples
`∀ i : {i // ¬p i}, κ i`. -/
def unfold (A : Tensor κ R) : Matrix (∀ i : {i // p i}, κ i) (∀ i : {i // ¬p i}, κ i) R :=
  Matrix.of fun r c => A ((Equiv.piEquivPiSubtypeProd p κ).symm (r, c))

/-- The entry of the unfolding in the row given by the restriction of $a$ to the row modes and the
column given by the restriction of $a$ to the column modes is $\mathcal{A}(a)$. -/
@[simp]
theorem unfold_apply (A : Tensor κ R) (a : ∀ i, κ i) :
    A.unfold p (fun i => a i) (fun i => a i) = A a :=
  congrArg A ((Equiv.piEquivPiSubtypeProd p κ).symm_apply_apply a)

/-- A tensor is determined by any of its unfoldings: `Tensor.unfold` as a linear equivalence between
tensors and matrices. -/
def unfoldLinearEquiv [Semiring R] :
    Tensor κ R ≃ₗ[R] Matrix (∀ i : {i // p i}, κ i) (∀ i : {i // ¬p i}, κ i) R where
  toFun := unfold p
  invFun M := of fun a => M (fun i => a i) (fun i => a i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv A := ext fun a => unfold_apply p A a
  right_inv M := by
    ext r c
    have h := (Equiv.piEquivPiSubtypeProd p κ).apply_symm_apply (r, c)
    exact congrArg₂ M (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- The linear equivalence `Tensor.unfoldLinearEquiv` is the unfolding `Tensor.unfold`. -/
@[simp]
theorem unfoldLinearEquiv_apply [Semiring R] (A : Tensor κ R) :
    unfoldLinearEquiv p A = A.unfold p :=
  rfl

/-- A subtensor is a column of an unfolding: the subtensor that fixes the indices of the modes
outside $p$ to $c$ is the column $c$ of the unfolding with the row modes $\{i \mid p(i)\}$. -/
theorem restrict_eq_col (c : ∀ i : {i // ¬p i}, κ i) (A : Tensor κ R) :
    restrict p c A = of ((A.unfold p).col c) :=
  rfl

end Unfold

/-! ### The mode-$k$ unfolding -/

section ModeUnfold

variable [DecidableEq ι]

/-- The **mode-$k$ unfolding** $\mathcal{A}_{(k)}$ of a tensor $\mathcal{A}$ ([golub2013matrix],
(12.4.6)). Its rows are indexed by the indices of mode $k$, its columns are indexed by the
tuples of indices of the other modes, and its entry in the row $x$ and the column $c$ is the
entry of $\mathcal{A}$ at the tuple that has $x$ at mode $k$ and agrees with $c$ elsewhere. The
columns of $\mathcal{A}_{(k)}$ are the mode-$k$ fibers of $\mathcal{A}$. -/
def modeUnfold (A : Tensor κ R) (k : ι) : Matrix (κ k) (∀ j : {j // j ≠ k}, κ j) R :=
  Matrix.of fun x c => A ((Equiv.piSplitAt k κ).symm (x, c))

/-- The entry of $\mathcal{A}_{(k)}$ in the row $a_k$ and the column given by the restriction of $a$
to the modes $j \neq k$ is $\mathcal{A}(a)$. -/
@[simp]
theorem modeUnfold_apply (A : Tensor κ R) (k : ι) (a : ∀ i, κ i) :
    A.modeUnfold k (a k) (fun j => a j) = A a :=
  congrArg A ((Equiv.piSplitAt k κ).symm_apply_apply a)

/-- A tensor is determined by its mode-$k$ unfolding: `Tensor.modeUnfold` as a linear equivalence
between tensors and matrices, in the same way as `Tensor.unfoldLinearEquiv`. -/
def modeUnfoldLinearEquiv [Semiring R] (k : ι) :
    Tensor κ R ≃ₗ[R] Matrix (κ k) (∀ j : {j // j ≠ k}, κ j) R where
  toFun A := A.modeUnfold k
  invFun M := of fun a => M (a k) fun j => a j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv A := ext fun a => modeUnfold_apply A k a
  right_inv M := by
    ext x c
    have h := (Equiv.piSplitAt k κ).apply_symm_apply (x, c)
    exact congrArg₂ M (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- The linear equivalence `Tensor.modeUnfoldLinearEquiv k` is the mode-$k$ unfolding. -/
@[simp]
theorem modeUnfoldLinearEquiv_apply [Semiring R] (k : ι) (A : Tensor κ R) :
    modeUnfoldLinearEquiv k A = A.modeUnfold k :=
  rfl

variable {κ : Fin 2 → Type v}

/-- The mode-$0$ unfolding of a matrix $M$, read as an order-2 tensor, is $M$, up to the
identification of the one-element column tuples with the column indices. -/
theorem modeUnfold_ofMatrix_zero [Semiring R] (M : Matrix (κ 0) (κ 1) R) :
    (ofMatrix M).modeUnfold 0 = M.submatrix id fun c => c ⟨1, one_ne_zero⟩ := by
  ext x c
  simp [modeUnfold, Equiv.piSplitAt_symm_apply]

/-- The mode-$1$ unfolding of a matrix $M$, read as an order-2 tensor, is $M^T$, up to the
identification of the one-element column tuples with the row indices. -/
theorem modeUnfold_ofMatrix_one [Semiring R] (M : Matrix (κ 0) (κ 1) R) :
    (ofMatrix M).modeUnfold 1 = (Mᵀ).submatrix id fun c => c ⟨0, zero_ne_one⟩ := by
  ext x c
  simp [modeUnfold, Equiv.piSplitAt_symm_apply]

end ModeUnfold

/-! ### Unfoldings are isometries -/

section Norm

open scoped Matrix.Norms.Frobenius

variable {𝕜 : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)]

/-- Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. A matrix whose entries are the entries of a
tensor $\mathcal{A}$ over $\mathbb{K}$, rearranged along a bijection of the index tuples with
the pairs of a row index and a column index, has the Frobenius norm $\|\mathcal{A}\|$. -/
theorem frobenius_norm_of_equiv {m n : Type*} [Fintype m] [Fintype n] (e : (∀ i, κ i) ≃ m × n)
    (A : Tensor κ 𝕜) : ‖(Matrix.of fun r c => A (e.symm (r, c)) : Matrix m n 𝕜)‖ = ‖A‖ := by
  rw [Matrix.frobenius_norm_def, frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  simp_rw [Real.rpow_two, ← Fintype.sum_prod_type', Matrix.of_apply]
  exact Equiv.sum_comp e.symm fun a => ‖A a‖ ^ 2

/-- Unfoldings preserve the Frobenius norm. Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let
the set of modes and all index types be finite, and let $\mathcal{A}$ be a tensor over
$\mathbb{K}$. Then for every set $p$ of row modes,
$$\|\mathcal{A}_{r \times c}\|_F = \|\mathcal{A}\|.$$

[golub2013matrix] uses this fact without comment in §12.5.3–12.5.4. -/
theorem frobenius_norm_unfold (p : ι → Prop) [DecidablePred p] (A : Tensor κ 𝕜) :
    ‖A.unfold p‖ = ‖A‖ :=
  frobenius_norm_of_equiv _ A

/-- The mode-$k$ unfolding preserves the Frobenius norm:
$\|\mathcal{A}_{(k)}\|_F = \|\mathcal{A}\|$. -/
theorem frobenius_norm_modeUnfold (A : Tensor κ 𝕜) (k : ι) : ‖A.modeUnfold k‖ = ‖A‖ :=
  frobenius_norm_of_equiv _ A

end Norm

/-! ### Unfoldings of rank-one tensors and of outer products -/

section RankOne

variable [Fintype ι] [CommMonoid R]

/-- An unfolding of a rank-one tensor is a rank-one matrix ([golub2013matrix], (12.4.9)–(12.4.10)).
Let $R$ be a commutative monoid and let the set of modes be finite. The unfolding of
$z_1 \circ \cdots \circ z_d$ with the row modes $\{i \mid p(i)\}$ is the outer product $u v^T$,
where $u$ is the rank-one tensor of the vectors $z_i$ with $p(i)$, and $v$ is the rank-one
tensor of the vectors $z_i$ with $\neg p(i)$. -/
theorem unfold_rankOne (p : ι → Prop) [DecidablePred p] (z : ∀ i, κ i → R) :
    (rankOne z).unfold p
      = Matrix.vecMulVec (rankOne fun i : {i // p i} => z i)
          (rankOne fun i : {i // ¬p i} => z i) := by
  ext r c
  simp only [unfold, Matrix.of_apply, rankOne_apply]
  rw [← Fintype.prod_subtype_mul_prod_subtype p]
  congr 1
  · exact Finset.prod_congr rfl fun i _ => by
      rw [Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_left i.2]
  · exact Finset.prod_congr rfl fun i _ => by
      rw [Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_right i.2]

/-- The mode-$k$ unfolding of a rank-one tensor is a rank-one matrix:
$(z_1 \circ \cdots \circ z_d)_{(k)} = z_k w^T$, where $w$ is the rank-one tensor of the vectors
$z_j$ with $j \neq k$, that is, $\bigotimes_{j \neq k} z_j$ as an array. -/
theorem modeUnfold_rankOne [DecidableEq ι] (z : ∀ i, κ i → R) (k : ι) :
    (rankOne z).modeUnfold k = Matrix.vecMulVec (z k) (rankOne fun j : {j // j ≠ k} => z j) := by
  ext x c
  simp only [modeUnfold, Matrix.of_apply, rankOne_apply]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ k]
  congr 1
  · simp [Equiv.piSplitAt_symm_apply]
  · exact Finset.prod_congr rfl fun j _ => by
      rw [Equiv.piSplitAt_symm_apply, dite_eq_right j.2]

end RankOne

section Outer

variable {m₁ n₁ m₂ n₂ : Type v}

/-- The row modes of the outer product of two order-2 tensors: the first mode of each. -/
abbrev rowModes (x : Fin 2 ⊕ Fin 2) : Prop :=
  x = .inl 0 ∨ x = .inr 0

/-- The Kronecker product is an unfolding of the outer product ([golub2013matrix], §12.4.7,
$\mathcal{A}_{[3\,1] \times [4\,2]} = B \otimes C$). Let $R$ be a semiring, and let
$B \in R^{m_1 \times n_1}$ and $C \in R^{m_2 \times n_2}$, read as order-2 tensors. The
unfolding of the outer product of $B$ and $C$ with the two row modes as rows and the two column
modes as columns is $B \otimes C$:
$$\bigl(\text{unfolding of } B \circ C\bigr)\bigl((i_1, i_2), (j_1, j_2)\bigr) = (B \otimes
  C)\bigl((i_1, i_2), (j_1, j_2)\bigr) = b_{i_1 j_1} c_{i_2 j_2}.$$

The row and column tuples of the unfolding are read as pairs through `Matrix.submatrix`. The row
modes are `Tensor.rowModes`. -/
theorem unfold_outer_eq_kronecker [Semiring R] (B : Matrix m₁ n₁ R) (C : Matrix m₂ n₂ R) :
    (outer (ofMatrix (κ := ![m₁, n₁]) B) (ofMatrix (κ := ![m₂, n₂]) C)).unfold rowModes
      = (B ⊗ₖ C).submatrix (fun r => (r ⟨.inl 0, .inl rfl⟩, r ⟨.inr 0, .inr rfl⟩))
          (fun c => (c ⟨.inl 1, by decide⟩, c ⟨.inr 1, by decide⟩)) := by
  ext r c
  rfl

end Outer

/-! ### Contractions -/

section Contract

variable {ι₁ ι₂ ι₃ : Type*} {κ₁ : ι₁ → Type v} {κ₂ : ι₂ → Type v} {κ₃ : ι₃ → Type v}

/-- The unfolding of a tensor with modes $\iota_1 \sqcup \iota_2$ whose rows are indexed by the
$\iota_1$-tuples and whose columns are indexed by the $\iota_2$-tuples: the entry in the row $r$
and the column $c$ is $\mathcal{A}(r, c)$. In this form, a contraction is a matrix product. It
is a linear equivalence between tensors and matrices. -/
def sumUnfold [Semiring R] :
    Tensor (Sum.elim κ₁ κ₂) R ≃ₗ[R] Matrix (∀ i, κ₁ i) (∀ j, κ₂ j) R where
  toFun A := Matrix.of fun r c => A ((Equiv.sumPiEquivProdPi _).symm (r, c))
  invFun M := of fun a => M (fun i => a (.inl i)) fun j => a (.inr j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv A := ext fun a => congrArg A ((Equiv.sumPiEquivProdPi _).symm_apply_apply a)
  right_inv _ := rfl

/-- The entries of `Tensor.sumUnfold A` are the entries of $\mathcal{A}$: the entry in the row $r$
and the column $c$ is $\mathcal{A}(r, c)$. -/
@[simp]
theorem sumUnfold_apply [Semiring R] (A : Tensor (Sum.elim κ₁ κ₂) R) (r : ∀ i, κ₁ i)
    (c : ∀ j, κ₂ j) : sumUnfold A r c = A ((Equiv.sumPiEquivProdPi _).symm (r, c)) :=
  rfl

/-- The inverse of `Tensor.sumUnfold` reads a matrix $M$ as a tensor: the entry at the tuple $a$ is
$M$ in the row given by the $\iota_1$-part of $a$ and the column given by the $\iota_2$-part of
$a$. -/
@[simp]
theorem sumUnfold_symm_apply [Semiring R] (M : Matrix (∀ i, κ₁ i) (∀ j, κ₂ j) R)
    (a : ∀ i, Sum.elim κ₁ κ₂ i) :
    sumUnfold.symm M a = M (fun i => a (.inl i)) fun j => a (.inr j) :=
  rfl

/-- The outer product $\mathcal{B} \circ \mathcal{C}$ unfolds to the rank-one matrix $b c^T$ of the
vectorized factors. -/
theorem sumUnfold_outer [Semiring R] (B : Tensor κ₁ R) (C : Tensor κ₂ R) :
    sumUnfold (outer B C) = Matrix.vecMulVec B C :=
  rfl

/-- The **contraction** of tensors ([golub2013matrix], (12.4.12)–(12.4.13)). Let $\mathcal{B}$ have
the modes $\iota_1 \sqcup \iota_2$ and let $\mathcal{C}$ have the modes
$\iota_2 \sqcup \iota_3$, with $\iota_2$ and its index types finite. The contraction is the
tensor with modes $\iota_1 \sqcup \iota_3$ whose unfolding is the product of the unfoldings of
$\mathcal{B}$ and $\mathcal{C}$:
$$\mathcal{A}(i, j) = \sum_k \mathcal{B}(i, k) \, \mathcal{C}(k, j).$$

A contraction over modes in other positions reduces to this one by `Tensor.permute`. -/
def contract [Semiring R] [Fintype ι₂] [DecidableEq ι₂] [∀ j, Fintype (κ₂ j)]
    (B : Tensor (Sum.elim κ₁ κ₂) R) (C : Tensor (Sum.elim κ₂ κ₃) R) :
    Tensor (Sum.elim κ₁ κ₃) R :=
  sumUnfold.symm (sumUnfold B * sumUnfold C)

variable [Semiring R] [Fintype ι₂] [DecidableEq ι₂] [∀ j, Fintype (κ₂ j)]

/-- The contraction unfolds to the product of the unfoldings: the unfolding of the contraction of
$\mathcal{B}$ and $\mathcal{C}$ is the product of the unfoldings of $\mathcal{B}$ and of
$\mathcal{C}$. This is the matrix form that [golub2013matrix] gives after (12.4.13). -/
@[simp]
theorem sumUnfold_contract (B : Tensor (Sum.elim κ₁ κ₂) R) (C : Tensor (Sum.elim κ₂ κ₃) R) :
    sumUnfold (contract B C) = sumUnfold B * sumUnfold C :=
  sumUnfold.apply_symm_apply _

/-- The entries of a contraction ([golub2013matrix], (12.4.12)–(12.4.13)): $\mathcal{A}(i, j) =
\sum_k \mathcal{B}(i, k) \, \mathcal{C}(k, j)$, where $k$ runs over the tuples of indices of the
contracted modes $\iota_2$. -/
theorem contract_apply (B : Tensor (Sum.elim κ₁ κ₂) R) (C : Tensor (Sum.elim κ₂ κ₃) R)
    (x : ∀ i, κ₁ i) (z : ∀ l, κ₃ l) :
    contract B C ((Equiv.sumPiEquivProdPi _).symm (x, z))
      = ∑ y : ∀ j, κ₂ j, B ((Equiv.sumPiEquivProdPi _).symm (x, y))
          * C ((Equiv.sumPiEquivProdPi _).symm (y, z)) := by
  change sumUnfold (contract B C) x z = _
  rw [sumUnfold_contract, Matrix.mul_apply]
  rfl

end Contract

end Tensor
