/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a new `Mathlib.LinearAlgebra.Tensor` directory beside `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.LinearAlgebra.Tensor.Basic

/-!
# Unfoldings and contractions of tensors

An unfolding (matricization) of a tensor `A : Tensor κ R` arranges its entries in a matrix whose
rows are indexed by the indices of some modes and whose columns by the indices of the others
([golub2013matrix] §12.4.5–12.4.6). The unfoldings here are *typed*: the rows of `A.unfold p` are
the tuples `∀ i : {i // p i}, κ i` and its columns the tuples `∀ i : {i // ¬p i}, κ i`
(through `Equiv.piEquivPiSubtypeProd`); the mode-`k` unfolding `A.modeUnfold k` has rows `κ k` and
columns `∀ j : {j // j ≠ k}, κ j` (through `Equiv.piSplitAt`). The order in which a book lists the
row and column modes, and its numbering of the flattened indices, matter only after flattening to
`Fin`, which is left to the consumer.

A tensor whose modes are a disjoint union `ι₁ ⊕ ι₂` has the unfolding `Tensor.sumUnfold` with rows
`∀ i, κ₁ i` and columns `∀ j, κ₂ j`, in which a contraction ([golub2013matrix] §12.4.9) is a matrix
product: `Tensor.contract`.

## Main definitions

* `Tensor.unfold`, `Tensor.unfoldLinearEquiv`: the unfolding along a predicate on the modes.
* `Tensor.modeUnfold`: the mode-`k` unfolding.
* `Tensor.sumUnfold`: the unfolding of a tensor on `ι₁ ⊕ ι₂`.
* `Tensor.contract`: the contraction of two tensors over common modes.

## Main statements

* `Tensor.frobenius_norm_unfold`, `Tensor.frobenius_norm_modeUnfold`: unfoldings are isometries.
* `Tensor.unfold_rankOne`, `Tensor.modeUnfold_rankOne`: unfoldings of rank-one tensors are rank-one
  matrices.
* `Tensor.unfold_outer_eq_kronecker`: the Kronecker product is an unfolding of an outer product.

## References

* [golub2013matrix], §12.4.5–12.4.9.
-/

universe u v w

open scoped Kronecker Matrix

namespace Tensor

variable {ι : Type u} {κ : ι → Type v} {R : Type w}

/-! ### Unfolding along a predicate -/

section Unfold

variable (p : ι → Prop) [DecidablePred p]

/-- The unfolding of `A` with row modes `{i | p i}` and column modes `{i | ¬p i}`
([golub2013matrix] (12.4.8), the book's `𝒜_{r × c}`). -/
def unfold (A : Tensor κ R) : Matrix (∀ i : {i // p i}, κ i) (∀ i : {i // ¬p i}, κ i) R :=
  Matrix.of fun r c => A ((Equiv.piEquivPiSubtypeProd p κ).symm (r, c))

@[simp]
theorem unfold_apply (A : Tensor κ R) (a : ∀ i, κ i) :
    A.unfold p (fun i => a i) (fun i => a i) = A a :=
  congrArg A ((Equiv.piEquivPiSubtypeProd p κ).symm_apply_apply a)

/-- A tensor is determined by any of its unfoldings: `Tensor.unfold` as a linear equivalence. -/
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

@[simp]
theorem unfoldLinearEquiv_apply [Semiring R] (A : Tensor κ R) :
    unfoldLinearEquiv p A = A.unfold p :=
  rfl

end Unfold

/-! ### The mode-`k` unfolding -/

section ModeUnfold

variable [DecidableEq ι]

/-- The mode-`k` unfolding ([golub2013matrix] (12.4.6)): rows indexed by mode `k`, columns by the
other modes; its columns are the mode-`k` fibers. -/
def modeUnfold (A : Tensor κ R) (k : ι) : Matrix (κ k) (∀ j : {j // j ≠ k}, κ j) R :=
  Matrix.of fun x c => A ((Equiv.piSplitAt k κ).symm (x, c))

/-- The entries of the mode-`k` unfolding. -/
@[simp]
theorem modeUnfold_apply (A : Tensor κ R) (k : ι) (a : ∀ i, κ i) :
    A.modeUnfold k (a k) (fun j => a j) = A a :=
  congrArg A ((Equiv.piSplitAt k κ).symm_apply_apply a)

variable {κ : Fin 2 → Type v}

/-- The mode-`0` unfolding of a matrix read as an order-2 tensor is the matrix, up to the
identification of the one-element column tuples with the column indices. -/
theorem modeUnfold_ofMatrix_zero [Semiring R] (M : Matrix (κ 0) (κ 1) R) :
    (ofMatrix M).modeUnfold 0 = M.submatrix id fun c => c ⟨1, one_ne_zero⟩ := by
  ext x c
  simp [modeUnfold, Equiv.piSplitAt_symm_apply]

/-- The mode-`1` unfolding of a matrix read as an order-2 tensor is its transpose, up to the
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

/-- A matrix whose entries are those of a tensor, rearranged along an equivalence of index types,
has the tensor's Frobenius norm. -/
theorem frobenius_norm_of_equiv {m n : Type*} [Fintype m] [Fintype n] (e : (∀ i, κ i) ≃ m × n)
    (A : Tensor κ 𝕜) : ‖(Matrix.of fun r c => A (e.symm (r, c)) : Matrix m n 𝕜)‖ = ‖A‖ := by
  rw [Matrix.frobenius_norm_def, frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  simp_rw [Real.rpow_two, ← Fintype.sum_prod_type', Matrix.of_apply]
  exact Equiv.sum_comp e.symm fun a => ‖A a‖ ^ 2

/-- Unfoldings preserve the Frobenius norm ([golub2013matrix] §12.5.3–12.5.4, used silently). -/
theorem frobenius_norm_unfold (p : ι → Prop) [DecidablePred p] (A : Tensor κ 𝕜) :
    ‖A.unfold p‖ = ‖A‖ :=
  frobenius_norm_of_equiv _ A

/-- The mode-`k` unfolding preserves the Frobenius norm. -/
theorem frobenius_norm_modeUnfold (A : Tensor κ 𝕜) (k : ι) : ‖A.modeUnfold k‖ = ‖A‖ :=
  frobenius_norm_of_equiv _ A

end Norm

/-! ### Unfoldings of rank-one tensors and of outer products -/

section RankOne

variable [Fintype ι] [CommMonoid R]

/-- An unfolding of a rank-one tensor is the rank-one matrix of the rank-one tensors on the row and
the column modes ([golub2013matrix] (12.4.9)–(12.4.10)). -/
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

/-- The mode-`k` unfolding of a rank-one tensor is `z_k (⊗_{j ≠ k} z_j)ᵀ`. -/
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

/-- The Kronecker product is an unfolding of the outer product ([golub2013matrix] §12.4.7,
`𝒜_{[3 1] × [4 2]} = B ⊗ C`): viewing `B`, `C` as order-2 tensors, the unfolding of
`outer (ofMatrix B) (ofMatrix C)` with rows the two row modes and columns the two column modes is
`B ⊗ₖ C`, the mode tuples read as pairs. -/
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

/-- The unfolding of a tensor on `ι₁ ⊕ ι₂` with rows the `ι₁`-tuples and columns the
`ι₂`-tuples, the form in which a contraction is a matrix product. -/
def sumUnfold [Semiring R] :
    Tensor (Sum.elim κ₁ κ₂) R ≃ₗ[R] Matrix (∀ i, κ₁ i) (∀ j, κ₂ j) R where
  toFun A := Matrix.of fun r c => A ((Equiv.sumPiEquivProdPi _).symm (r, c))
  invFun M := of fun a => M (fun i => a (.inl i)) fun j => a (.inr j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv A := ext fun a => congrArg A ((Equiv.sumPiEquivProdPi _).symm_apply_apply a)
  right_inv _ := rfl

@[simp]
theorem sumUnfold_apply [Semiring R] (A : Tensor (Sum.elim κ₁ κ₂) R) (r : ∀ i, κ₁ i)
    (c : ∀ j, κ₂ j) : sumUnfold A r c = A ((Equiv.sumPiEquivProdPi _).symm (r, c)) :=
  rfl

@[simp]
theorem sumUnfold_symm_apply [Semiring R] (M : Matrix (∀ i, κ₁ i) (∀ j, κ₂ j) R)
    (a : ∀ i, Sum.elim κ₁ κ₂ i) :
    sumUnfold.symm M a = M (fun i => a (.inl i)) fun j => a (.inr j) :=
  rfl

/-- The outer product unfolds to a rank-one matrix of the vectorized factors. -/
theorem sumUnfold_outer [Semiring R] (B : Tensor κ₁ R) (C : Tensor κ₂ R) :
    sumUnfold (outer B C) = Matrix.vecMulVec B C :=
  rfl

/-- Tensor contraction ([golub2013matrix] (12.4.12)–(12.4.13)): the modes `ι₂` of `B` are summed
against the modes `ι₂` of `C`. Contractions whose contracted modes sit elsewhere reduce to this one
by `Tensor.permute`. -/
def contract [Semiring R] [Fintype ι₂] [DecidableEq ι₂] [∀ j, Fintype (κ₂ j)]
    (B : Tensor (Sum.elim κ₁ κ₂) R) (C : Tensor (Sum.elim κ₂ κ₃) R) :
    Tensor (Sum.elim κ₁ κ₃) R :=
  sumUnfold.symm (sumUnfold B * sumUnfold C)

variable [Semiring R] [Fintype ι₂] [DecidableEq ι₂] [∀ j, Fintype (κ₂ j)]

/-- The contraction unfolds to the product of the unfoldings (after (12.4.13)). -/
@[simp]
theorem sumUnfold_contract (B : Tensor (Sum.elim κ₁ κ₂) R) (C : Tensor (Sum.elim κ₂ κ₃) R) :
    sumUnfold (contract B C) = sumUnfold B * sumUnfold C :=
  sumUnfold.apply_symm_apply _

/-- [golub2013matrix] (12.4.12)–(12.4.13): `𝒜(i, j) = ∑_k ℬ(i, k) 𝒞(k, j)`. -/
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
