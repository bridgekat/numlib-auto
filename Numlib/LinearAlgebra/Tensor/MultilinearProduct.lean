/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a new `Mathlib.LinearAlgebra.Tensor` directory beside `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.LinearAlgebra.Tensor.Unfolding

/-!
# Multilinear products and mode products

The multilinear (Tucker) product `𝒮 ×₁ M₁ ⋯ ×_d M_d` of a tensor `S : Tensor κ R` by a family of
matrices `M : ∀ i, Matrix (μ i) (κ i) R` ([golub2013matrix] §12.4.10–12.4.11) is the primitive
here: `Tensor.multilinearProd M S := Matrix.piKronecker M *ᵥ S`. Its shape changes from `κ` to `μ`
with no cast, and its vec formulas ((12.4.15), (12.4.19)) are definitional in typed form.

A single mode-`k` product changes the shape only at `k`; in dependent type theory the new family
`Function.update κ k μ` agrees with `κ` off `k` only propositionally. The square mode product
`Tensor.modeProd` is shape-preserving, with clean laws; the rectangular one `Tensor.rectModeProd`
takes a target shape `μ` with equivalences `μ i ≃ κ i` off `k` (`Equiv.cast` for
`Function.update`, `finCongr` on `Fin`-shapes), and its laws are those of the multilinear product,
the shapes being matched by the equivalences.

## Main definitions

* `Tensor.multilinearProd M S`: the multilinear product.
* `Tensor.multilinearProdₗ M`: the multilinear product as a linear map.
* `Tensor.modeProd S k M`: the mode-`k` product with a square matrix; `Tensor.rectModeProd` with a
  rectangular one (`Tensor.rectModeProd_refl`: the square case).

## Main statements

* `Tensor.modeUnfold_multilinearProd`, `Tensor.unfold_multilinearProd`: [golub2013matrix]
  Theorem 12.4.1, `𝒜_(k) = M_k 𝒮_(k) (⊗_{j ≠ k} M_j)ᵀ`, and its version for any unfolding.
* `Tensor.multilinearProd_inv`: the second part of Theorem 12.4.1.
* `Tensor.modeProd_comm`, `Tensor.modeProd_modeProd`: [golub2013matrix] (12.4.16)–(12.4.17)
  (the latter corrected), and their rectangular forms `Tensor.rectModeProd_comm`,
  `Tensor.rectModeProd_rectModeProd`, with `Tensor.modeUnfold_rectModeProd` (12.4.14).
* `Tensor.multilinearProd_eq_modeProd`: the multilinear product is the composite of the mode
  products, in any order.
* `Tensor.frobenius_norm_multilinearProd_of_orthonormal`: multilinear products by matrices with
  orthonormal columns are isometries.
* `Tensor.vecFin_multilinearProd`: the flattened form (12.4.19);
  `Tensor.piKronecker_reindex_finPiFinEquiv_eq_kroneckerFin` and `Tensor.vecFin_rectModeProd`:
  the flattened mode product is `I ⊗ M ⊗ I` (12.4.15).

## References

* [golub2013matrix], §12.4.10–12.4.11.
-/

universe u v v' w

open Matrix
open scoped InnerProductSpace

namespace Tensor

variable {ι : Type u} {κ : ι → Type v} {μ : ι → Type v'} {ν : ι → Type*} {R : Type w}

section Multilinear

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)] [CommSemiring R]

/-- The multilinear product `𝒮 ×₁ M₁ ⋯ ×_d M_d` ([golub2013matrix] (12.4.18)–(12.4.19)):
`piKronecker M *ᵥ S`. -/
def multilinearProd (M : ∀ i, Matrix (μ i) (κ i) R) (S : Tensor κ R) : Tensor μ R :=
  piKronecker M *ᵥ S

/-- [golub2013matrix] (12.4.18): `𝒜(a) = ∑_b (∏ᵢ Mᵢ(aᵢ, bᵢ)) 𝒮(b)`. -/
theorem multilinearProd_apply (M : ∀ i, Matrix (μ i) (κ i) R) (S : Tensor κ R) (a : ∀ i, μ i) :
    multilinearProd M S a = ∑ b, (∏ i, M i (a i) (b i)) * S b :=
  rfl

/-- The multilinear product read as a matrix-vector product on the arrays of entries. -/
theorem of_symm_multilinearProd (M : ∀ i, Matrix (μ i) (κ i) R) (S : Tensor κ R) :
    of.symm (multilinearProd M S) = piKronecker M *ᵥ of.symm S :=
  rfl

/-- The multilinear product is linear in the tensor. -/
theorem multilinearProd_add (M : ∀ i, Matrix (μ i) (κ i) R) (S T : Tensor κ R) :
    multilinearProd M (S + T) = multilinearProd M S + multilinearProd M T :=
  mulVec_add _ _ _

/-- The multilinear product is homogeneous in the tensor. -/
theorem multilinearProd_smul (M : ∀ i, Matrix (μ i) (κ i) R) (c : R) (S : Tensor κ R) :
    multilinearProd M (c • S) = c • multilinearProd M S :=
  mulVec_smul _ _ _

/-- The multilinear product expands the core along the rank-one tensors of the factors' columns
([golub2013matrix] (12.5.7)): `𝒮 ×₁ M₁ ⋯ ×_d M_d = ∑_b 𝒮(b) M₁(:, b₁) ∘ ⋯ ∘ M_d(:, b_d)`. -/
theorem multilinearProd_eq_sum_rankOne (M : ∀ i, Matrix (μ i) (κ i) R) (S : Tensor κ R) :
    multilinearProd M S = ∑ b, S b • rankOne fun i x => M i x (b i) := by
  ext a
  rw [multilinearProd_apply, sum_apply]
  exact Finset.sum_congr rfl fun b _ => by rw [smul_apply, rankOne_apply, smul_eq_mul, mul_comm]

/-- The multilinear product by diagonal matrices scales each entry by the product of the
diagonal entries. -/
theorem multilinearProd_diagonal [∀ i, DecidableEq (κ i)] (d : ∀ i, κ i → R) (S : Tensor κ R) :
    multilinearProd (fun i => diagonal (d i)) S = of fun a => (∏ i, d i (a i)) * S a := by
  ext a
  rw [multilinearProd_apply, of_apply, Finset.sum_eq_single a]
  · simp only [diagonal_apply_eq]
  · intro b _ hb
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hb
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (diagonal_apply_ne (d i) (Ne.symm hi)), zero_mul]
  · simp

/-- The multilinear product as a linear map in the tensor. -/
def multilinearProdₗ (M : ∀ i, Matrix (μ i) (κ i) R) : Tensor κ R →ₗ[R] Tensor μ R where
  toFun := multilinearProd M
  map_add' := multilinearProd_add M
  map_smul' := multilinearProd_smul M

@[simp]
theorem multilinearProdₗ_apply (M : ∀ i, Matrix (μ i) (κ i) R) (S : Tensor κ R) :
    multilinearProdₗ M S = multilinearProd M S :=
  rfl

/-- The multilinear product is additive in the tensor, subtraction form. -/
theorem multilinearProd_sub {R : Type w} [CommRing R] (M : ∀ i, Matrix (μ i) (κ i) R)
    (S T : Tensor κ R) :
    multilinearProd M (S - T) = multilinearProd M S - multilinearProd M T :=
  mulVec_sub _ _ _

/-- The multilinear product by identity matrices is the identity. -/
@[simp]
theorem multilinearProd_one [∀ i, DecidableEq (κ i)] (S : Tensor κ R) :
    multilinearProd (fun i => (1 : Matrix (κ i) (κ i) R)) S = S := by
  apply of.symm.injective
  rw [of_symm_multilinearProd, piKronecker_one, one_mulVec]

/-- Multilinear products compose factorwise: `(𝒮 ×ᵢ Mᵢ) ×ᵢ Nᵢ = 𝒮 ×ᵢ (Nᵢ Mᵢ)`, the family form of
[golub2013matrix] (12.4.16)–(12.4.17). -/
theorem multilinearProd_multilinearProd [∀ i, Fintype (μ i)] (M : ∀ i, Matrix (μ i) (κ i) R)
    (N : ∀ i, Matrix (ν i) (μ i) R) (S : Tensor κ R) :
    multilinearProd N (multilinearProd M S) = multilinearProd (fun i => N i * M i) S := by
  apply of.symm.injective
  rw [of_symm_multilinearProd, of_symm_multilinearProd, of_symm_multilinearProd,
    mulVec_mulVec, piKronecker_mul_piKronecker]

/-- [golub2013matrix] Theorem 12.4.1, second part: if every factor is invertible then the core is
recovered by the multilinear product with the inverses. -/
theorem multilinearProd_inv {R : Type w} [CommRing R] [∀ i, DecidableEq (κ i)]
    {M : ∀ i, Matrix (κ i) (κ i) R} (hM : ∀ i, IsUnit (M i)) {S A : Tensor κ R}
    (h : A = multilinearProd M S) : S = multilinearProd (fun i => (M i)⁻¹) A := by
  subst h
  rw [multilinearProd_multilinearProd]
  simp_rw [nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 (hM _)), multilinearProd_one]

/-- A tensor-valued multilinear product read through an equivalence of index tuples with pairs,
when the Kronecker product factors along the pairs, is a two-sided matrix product. -/
private theorem of_multilinearProd_eq_mul {α β α' β' : Type*} [Fintype α] [Fintype β]
    (e : (∀ i, κ i) ≃ α × β) (e' : (∀ i, μ i) ≃ α' × β') (M : ∀ i, Matrix (μ i) (κ i) R)
    (P : Matrix α' α R) (Q : Matrix β' β R)
    (hPQ : ∀ r c y z, piKronecker M (e'.symm (r, c)) (e.symm (y, z)) = P r y * Q c z)
    (S : Tensor κ R) :
    (Matrix.of fun r c => multilinearProd M S (e'.symm (r, c)) : Matrix α' β' R)
      = P * Matrix.of (fun y z => S (e.symm (y, z))) * Qᵀ := by
  ext r c
  simp only [Matrix.of_apply, multilinearProd, mulVec, dotProduct, mul_apply, transpose_apply]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [hPQ, Finset.sum_mul]
  exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => by ring

/-- [golub2013matrix] P12.4.9's unfolding identity: `𝒜_{r × c} = (⊗_{i ∈ r} Mᵢ) 𝒮_{r × c}
(⊗_{i ∈ c} Mᵢ)ᵀ` for the unfolding along any predicate on the modes. -/
theorem unfold_multilinearProd (p : ι → Prop) [DecidablePred p] (M : ∀ i, Matrix (μ i) (κ i) R)
    (S : Tensor κ R) :
    (multilinearProd M S).unfold p
      = piKronecker (fun i : {i // p i} => M i) * S.unfold p
          * (piKronecker fun i : {i // ¬p i} => M i)ᵀ := by
  refine of_multilinearProd_eq_mul _ _ M _ _ (fun r c y z => ?_) S
  simp only [piKronecker_apply]
  rw [← Fintype.prod_subtype_mul_prod_subtype p]
  congr 1
  · exact Finset.prod_congr rfl fun i _ => by
      simp only [Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_left i.2]
  · exact Finset.prod_congr rfl fun i _ => by
      simp only [Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_right i.2]

/-- **[golub2013matrix] Theorem 12.4.1**, typed: the mode-`k` unfolding of a multilinear product
is `𝒜_(k) = M_k 𝒮_(k) (⊗_{j ≠ k} M_j)ᵀ`. -/
theorem modeUnfold_multilinearProd (M : ∀ i, Matrix (μ i) (κ i) R) (S : Tensor κ R) (k : ι) :
    (multilinearProd M S).modeUnfold k
      = M k * S.modeUnfold k * (piKronecker fun j : {j // j ≠ k} => M j)ᵀ := by
  refine of_multilinearProd_eq_mul _ _ M _ _ (fun x c y z => ?_) S
  simp only [piKronecker_apply]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ k]
  congr 1
  · simp [Equiv.piSplitAt_symm_apply]
  · exact Finset.prod_congr rfl fun j _ => by
      simp only [Equiv.piSplitAt_symm_apply, dite_eq_right j.2]

end Multilinear

/-! ### Mode products -/

section ModeProd

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
  [CommSemiring R]

/-- The mode-`k` product `𝒮 ×_k M` with a square matrix ([golub2013matrix] (12.4.14),
shape-preserving case): the multilinear product with `M` in mode `k` and identities elsewhere. -/
def modeProd (S : Tensor κ R) (k : ι) (M : Matrix (κ k) (κ k) R) : Tensor κ R :=
  multilinearProd (Function.update (fun i => (1 : Matrix (κ i) (κ i) R)) k M) S

/-- [golub2013matrix] (12.4.14): `(𝒮 ×_k M)_(k) = M 𝒮_(k)`. -/
theorem modeUnfold_modeProd (S : Tensor κ R) (k : ι) (M : Matrix (κ k) (κ k) R) :
    (S.modeProd k M).modeUnfold k = M * S.modeUnfold k := by
  rw [modeProd, modeUnfold_multilinearProd, Function.update_self]
  have h : (fun j : {j // j ≠ k} =>
      Function.update (fun i => (1 : Matrix (κ i) (κ i) R)) k M j) = fun j => 1 :=
    funext fun j => Function.update_of_ne j.2 _ _
  rw [h, piKronecker_one, transpose_one, Matrix.mul_one]

omit [Fintype ι] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [CommSemiring R] in
/-- The mode-`k` unfolding evaluated at the column of an index tuple is the entry at that tuple
with its `k`-th index replaced. -/
private theorem modeUnfold_apply_update (S : Tensor κ R) (k : ι) (a : ∀ i, κ i) (y : κ k) :
    S.modeUnfold k y (fun j => a j) = S (Function.update a k y) := by
  rw [← modeUnfold_apply S k (Function.update a k y), Function.update_self]
  congr 1
  funext j
  rw [Function.update_of_ne j.2]

/-- The entries of a mode product: `(𝒮 ×_k M)(a) = ∑_y M(a_k, y) 𝒮(a with a_k := y)`. -/
theorem modeProd_apply (S : Tensor κ R) (k : ι) (M : Matrix (κ k) (κ k) R) (a : ∀ i, κ i) :
    S.modeProd k M a = ∑ y, M (a k) y * S (Function.update a k y) := by
  rw [← modeUnfold_apply (S.modeProd k M) k a, modeUnfold_modeProd, mul_apply]
  simp only [modeUnfold_apply_update]

/-- [golub2013matrix] (12.4.17), corrected: `(𝒮 ×_k F) ×_k G = 𝒮 ×_k (G F)` (the book prints
`F G`). -/
theorem modeProd_modeProd (S : Tensor κ R) (k : ι) (F G : Matrix (κ k) (κ k) R) :
    (S.modeProd k F).modeProd k G = S.modeProd k (G * F) := by
  rw [modeProd, modeProd, multilinearProd_multilinearProd, modeProd]
  congr 1
  funext i
  by_cases h : i = k
  · subst h
    simp
  · simp [h]

/-- [golub2013matrix] (12.4.16): mode products in distinct modes commute. -/
theorem modeProd_comm (S : Tensor κ R) {j k : ι} (hjk : j ≠ k) (F : Matrix (κ k) (κ k) R)
    (G : Matrix (κ j) (κ j) R) :
    (S.modeProd k F).modeProd j G = (S.modeProd j G).modeProd k F := by
  rw [modeProd, modeProd, multilinearProd_multilinearProd, modeProd, modeProd,
    multilinearProd_multilinearProd]
  congr 1
  funext i
  by_cases hj : i = j
  · subst hj
    simp [Function.update_of_ne hjk]
  · by_cases hk : i = k
    · subst hk
      simp [Function.update_of_ne hj]
    · simp [Function.update_of_ne hj, Function.update_of_ne hk]

/-- Applying the mode products along a duplicate-free list of modes is the multilinear product
with the factors on the listed modes and identities elsewhere. -/
theorem foldl_modeProd (M : ∀ i, Matrix (κ i) (κ i) R) {l : List ι} (hl : l.Nodup)
    (S : Tensor κ R) :
    l.foldl (fun T k => T.modeProd k (M k)) S
      = multilinearProd (fun i => if i ∈ l then M i else 1) S := by
  induction l generalizing S with
  | nil => simp
  | cons k l ih =>
    rw [List.foldl_cons, ih (List.nodup_cons.1 hl).2, modeProd, multilinearProd_multilinearProd]
    congr 1
    funext i
    by_cases h : i = k
    · subst h
      simp [(List.nodup_cons.1 hl).1]
    · simp [h]

/-- The multilinear product is the composite of the `d` mode products, in any order
([golub2013matrix] §12.4.11: "their order is immaterial"). -/
theorem multilinearProd_eq_modeProd (M : ∀ i, Matrix (κ i) (κ i) R) {l : List ι}
    (hl : l.Nodup) (hmem : ∀ i, i ∈ l) (S : Tensor κ R) :
    multilinearProd M S = l.foldl (fun T k => T.modeProd k (M k)) S := by
  rw [foldl_modeProd M hl]
  simp [hmem]

end ModeProd

/-! ### Rectangular mode products

A mode-`k` product with a rectangular `M : Matrix (μ k) (κ k) R` changes the shape at `k` only. The
new shape `μ` is any family that agrees with `κ` off `k` along given equivalences
`e i : μ i ≃ κ i` (`i ≠ k`): `Function.update κ k μ'` with `Equiv.cast`, or, on `Fin`-shapes,
`fun i => Fin (Function.update n k m i)` with `finCongr`. Commutation and composition are then
the factorwise composition `Tensor.multilinearProd_multilinearProd`, the shapes being matched by
the equivalences. -/

section RectModeProd

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
  [CommSemiring R]

/-- The factors of a rectangular mode-`k` product into the shape `μ`, which agrees with `κ` off `k`
along `e`: `M` in mode `k`, and off `k` the identity read through `e`. -/
def modeFactors (k : ι) (e : ∀ i, i ≠ k → μ i ≃ κ i) (M : Matrix (μ k) (κ k) R) (i : ι) :
    Matrix (μ i) (κ i) R :=
  if h : i = k then h ▸ M else (1 : Matrix (κ i) (κ i) R).submatrix (e i h) id

omit [Fintype ι] [∀ i, Fintype (κ i)] in
theorem modeFactors_self (k : ι) (e : ∀ i, i ≠ k → μ i ≃ κ i) (M : Matrix (μ k) (κ k) R) :
    modeFactors k e M k = M := by
  simp [modeFactors]

omit [Fintype ι] [∀ i, Fintype (κ i)] in
theorem modeFactors_of_ne {k i : ι} (h : i ≠ k) (e : ∀ i, i ≠ k → μ i ≃ κ i)
    (M : Matrix (μ k) (κ k) R) :
    modeFactors k e M i = (1 : Matrix (κ i) (κ i) R).submatrix (e i h) id := by
  simp [modeFactors, h]

/-- **The rectangular mode-`k` product** `𝒮 ×_k M` ([golub2013matrix] §12.4.10) with
`M : Matrix (μ k) (κ k) R`, of shape `μ` (agreeing with `κ` off `k` along `e`): the multilinear
product with `M` in mode `k` and identities elsewhere. -/
def rectModeProd (S : Tensor κ R) (k : ι) (e : ∀ i, i ≠ k → μ i ≃ κ i)
    (M : Matrix (μ k) (κ k) R) : Tensor μ R :=
  multilinearProd (modeFactors k e M) S

/-- The square mode product is the rectangular one with `μ = κ` and trivial equivalences. -/
theorem rectModeProd_refl (S : Tensor κ R) (k : ι) (M : Matrix (κ k) (κ k) R) :
    S.rectModeProd k (fun _ _ => Equiv.refl _) M = S.modeProd k M := by
  rw [rectModeProd, modeProd]
  congr 1

/-- `(1 : Matrix κ κ R).submatrix e id * N` reads the rows of `N` through `e`. -/
private theorem one_submatrix_mul {α β γ : Type*} [Fintype β] [DecidableEq β] (e : α ≃ β)
    (N : Matrix β γ R) : (1 : Matrix β β R).submatrix e id * N = N.submatrix e id := by
  ext x z
  simp [mul_apply, one_apply]

/-- `N * (1 : Matrix κ κ R).submatrix e id` reads the columns of `N` through `e.symm`. -/
private theorem mul_one_submatrix {α β γ : Type*} [Fintype α] [DecidableEq β] (e : α ≃ β)
    (N : Matrix γ α R) : N * (1 : Matrix β β R).submatrix e id = N.submatrix id e.symm := by
  ext x z
  simp only [mul_apply, submatrix_apply, id, one_apply]
  rw [Finset.sum_eq_single (e.symm z)]
  · simp
  · intro y _ hy
    rw [ite_eq_right_iff.2 fun h => absurd h fun h' => hy (by rw [← h', Equiv.symm_apply_apply]),
      mul_zero]
  · simp

/-- **Composition in one mode** ([golub2013matrix] (12.4.17), corrected, rectangular):
`(𝒮 ×_k F) ×_k G = 𝒮 ×_k (G F)`, the shapes matched by composing the equivalences. -/
theorem rectModeProd_rectModeProd [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)]
    (S : Tensor κ R) (k : ι) (e : ∀ i, i ≠ k → μ i ≃ κ i) (F : Matrix (μ k) (κ k) R)
    (e' : ∀ i, i ≠ k → ν i ≃ μ i) (G : Matrix (ν k) (μ k) R) :
    (S.rectModeProd k e F).rectModeProd k e' G =
      S.rectModeProd k (fun i h => (e' i h).trans (e i h)) (G * F) := by
  rw [rectModeProd, rectModeProd, rectModeProd, multilinearProd_multilinearProd]
  congr 1
  funext i
  by_cases h : i = k
  · subst h
    simp only [modeFactors_self]
  · rw [modeFactors_of_ne h, modeFactors_of_ne h, modeFactors_of_ne h, one_submatrix_mul]
    ext x z
    simp [one_apply]

/-- **Mode products in distinct modes commute** ([golub2013matrix] (12.4.16), rectangular):
`(𝒮 ×_k F) ×_j G = (𝒮 ×_j G') ×_k F'` for `j ≠ k`, where the two routes `κ → μ → ν` (along `e`,
then `e'`) and `κ → λ → ν` (along `f`, then `f'`) agree off `j` and `k`, and `G'`, `F'` are `G`, `F`
read through the equivalences. -/
theorem rectModeProd_comm {ρ : ι → Type*} [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)]
    [∀ i, Fintype (ρ i)] [∀ i, DecidableEq (ρ i)] (S : Tensor κ R) {j k : ι} (hjk : j ≠ k)
    (e : ∀ i, i ≠ k → μ i ≃ κ i) (F : Matrix (μ k) (κ k) R) (e' : ∀ i, i ≠ j → ν i ≃ μ i)
    (G : Matrix (ν j) (μ j) R) (f : ∀ i, i ≠ j → ρ i ≃ κ i) (f' : ∀ i, i ≠ k → ν i ≃ ρ i)
    (hef : ∀ i (hj : i ≠ j) (hk : i ≠ k), (e' i hj).trans (e i hk) = (f' i hk).trans (f i hj)) :
    (S.rectModeProd k e F).rectModeProd j e' G =
      (S.rectModeProd j f (G.submatrix (f' j hjk).symm (e j hjk).symm)).rectModeProd k f'
        (F.submatrix (e' k hjk.symm) (f k hjk.symm)) := by
  rw [rectModeProd, rectModeProd, rectModeProd, rectModeProd, multilinearProd_multilinearProd,
    multilinearProd_multilinearProd]
  congr 1
  funext i
  by_cases hij : i = j
  · subst hij
    rw [modeFactors_self, modeFactors_of_ne hjk, modeFactors_of_ne hjk, modeFactors_self,
      mul_one_submatrix, one_submatrix_mul]
    ext x z
    simp
  · by_cases hik : i = k
    · subst hik
      rw [modeFactors_of_ne hij, modeFactors_self, modeFactors_self, modeFactors_of_ne hij,
        one_submatrix_mul, mul_one_submatrix]
      ext x z
      simp
    · rw [modeFactors_of_ne hij, modeFactors_of_ne hik, modeFactors_of_ne hik,
        modeFactors_of_ne hij, one_submatrix_mul, one_submatrix_mul, submatrix_submatrix,
        submatrix_submatrix]
      have h := congrArg (⇑) (hef i hij hik)
      simp only [Equiv.coe_trans] at h
      rw [h]

/-- [golub2013matrix] (12.4.14), rectangular: `(𝒮 ×_k M)_(k) = M 𝒮_(k)`, the columns read through
the equivalences off `k`. -/
theorem modeUnfold_rectModeProd (S : Tensor κ R) (k : ι) (e : ∀ i, i ≠ k → μ i ≃ κ i)
    (M : Matrix (μ k) (κ k) R) :
    (S.rectModeProd k e M).modeUnfold k =
      (M * S.modeUnfold k).submatrix id fun c j => e j j.2 (c j) := by
  rw [rectModeProd, modeUnfold_multilinearProd, modeFactors_self]
  ext x c
  rw [Matrix.mul_apply]
  simp only [transpose_apply, piKronecker_apply, submatrix_apply, id]
  have hprod : ∀ c' : ∀ j : {j // j ≠ k}, κ j,
      (∏ j : {j // j ≠ k}, modeFactors k e M j (c j) (c' j))
        = if (fun j : {j // j ≠ k} => e j j.2 (c j)) = c' then 1 else 0 := by
    intro c'
    rw [Finset.prod_congr rfl fun j _ => by
      rw [modeFactors_of_ne j.2, submatrix_apply, id, one_apply], Fintype.prod_boole]
    exact if_congr funext_iff.symm rfl rfl
  simp only [hprod, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end RectModeProd

/-! ### Orthonormal factors -/

section Orthonormal

variable {𝕜 : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)]
  [∀ i, DecidableEq (κ i)] [∀ i, Fintype (μ i)]


omit [∀ i, DecidableEq (κ i)] in
/-- The multilinear product by the conjugate transposes is the adjoint of the multilinear
product. -/
theorem inner_multilinearProd_right (U : ∀ i, Matrix (μ i) (κ i) 𝕜) (A : Tensor μ 𝕜)
    (S : Tensor κ 𝕜) :
    ⟪A, multilinearProd U S⟫_𝕜 = ⟪multilinearProd (fun i => (U i)ᴴ) A, S⟫_𝕜 := by
  rw [inner_eq_star_dotProduct, inner_eq_star_dotProduct, of_symm_multilinearProd,
    of_symm_multilinearProd, dotProduct_mulVec, ← conjTranspose_piKronecker, star_mulVec,
    conjTranspose_conjTranspose]

/-- A multilinear product by matrices with orthonormal columns preserves inner products. -/
theorem inner_multilinearProd_of_orthonormal {U : ∀ i, Matrix (μ i) (κ i) 𝕜}
    (hU : ∀ i, (U i)ᴴ * U i = 1) (S T : Tensor κ 𝕜) :
    ⟪multilinearProd U S, multilinearProd U T⟫_𝕜 = ⟪S, T⟫_𝕜 := by
  rw [inner_multilinearProd_right, multilinearProd_multilinearProd]
  simp only [hU, multilinearProd_one]

/-- Multilinear products by matrices with orthonormal columns are isometries ([golub2013matrix]
§12.5.3: "since `U₃ ⊗ U₂ ⊗ U₁` has orthonormal columns"). -/
theorem frobenius_norm_multilinearProd_of_orthonormal {U : ∀ i, Matrix (μ i) (κ i) 𝕜}
    (hU : ∀ i, (U i)ᴴ * U i = 1) (S : Tensor κ 𝕜) : ‖multilinearProd U S‖ = ‖S‖ := by
  rw [@norm_eq_sqrt_re_inner 𝕜, @norm_eq_sqrt_re_inner 𝕜 (Tensor κ 𝕜),
    inner_multilinearProd_of_orthonormal hU]

/-- The multilinear product by the conjugate transposes undoes a multilinear product by matrices
with orthonormal columns. -/
theorem multilinearProd_conjTranspose_multilinearProd {U : ∀ i, Matrix (μ i) (κ i) 𝕜}
    (hU : ∀ i, (U i)ᴴ * U i = 1) (S : Tensor κ 𝕜) :
    multilinearProd (fun i => (U i)ᴴ) (multilinearProd U S) = S := by
  rw [multilinearProd_multilinearProd]
  simp_rw [hU, multilinearProd_one]

end Orthonormal

/-! ### The flattened form -/

section VecFin

variable {d : ℕ} {m n : Fin d → ℕ} [CommSemiring R]

/-- [golub2013matrix] (12.4.19), flattened: `vec(𝒮 ×₁ M₁ ⋯ ×_d M_d) = (M_d ⊗ ⋯ ⊗ M₁) vec(𝒮)`, the
flattened `piKronecker` being the book's reversed Kronecker product by
`Matrix.piKronecker_reindex_finPiFinEquiv`. -/
theorem vecFin_multilinearProd (M : ∀ k, Matrix (Fin (m k)) (Fin (n k)) R)
    (S : Tensor (fun k => Fin (n k)) R) :
    vecFin (multilinearProd M S)
      = (piKronecker M).reindex finPiFinEquiv finPiFinEquiv *ᵥ vecFin S := by
  funext t
  obtain ⟨a, rfl⟩ := finPiFinEquiv.surjective t
  rw [vecFin_apply, multilinearProd_apply]
  simp only [mulVec, dotProduct]
  rw [← finPiFinEquiv.sum_comp]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [vecFin_apply, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, piKronecker_apply]

/-- A product over `Fin d` split at `k`: the factors below `k`, the `k`-th, and those above. -/
private theorem prod_univ_split {α : Type*} [CommMonoid α] (f : Fin d → α) (k : Fin d) :
    ∏ i, f i = (∏ j : Fin k, f (Fin.castLE k.is_lt.le j)) * f k *
      ∏ j : Fin (d - (k + 1)), f ⟨k + 1 + j, by omega⟩ := by
  set g : ℕ → α := fun l => if h : l < d then f ⟨l, h⟩ else 1 with hg
  have h1 : ∏ i, f i = ∏ l ∈ Finset.range d, g l := by
    rw [← Fin.prod_univ_eq_prod_range]
    exact Finset.prod_congr rfl fun l _ => by rw [hg]; simp only [l.2, ↓reduceDIte]
  have hd : d = k + 1 + (d - (k + 1)) := by omega
  rw [h1, show Finset.range d = Finset.range (k + 1 + (d - (k + 1))) by rw [← hd],
    Finset.prod_range_add, Finset.prod_range_succ, ← Fin.prod_univ_eq_prod_range,
    ← Fin.prod_univ_eq_prod_range (fun l => g (k + 1 + l))]
  refine congr_arg₂ (· * ·) (congr_arg₂ (· * ·) ?_ ?_) ?_
  · exact Finset.prod_congr rfl fun j _ => by
      rw [hg]
      simp only [show (j : ℕ) < d by omega, ↓reduceDIte]
      rfl
  · rw [hg]
    simp only [k.2, ↓reduceDIte]
  · exact Finset.prod_congr rfl fun j _ => by
      rw [hg]
      simp only [show (k : ℕ) + 1 + j < d by omega, ↓reduceDIte]

/-- The size of a shape agreeing with `n` off `k`, split at `k`: `(∏_{j > k} n_j) m_k
(∏_{j < k} n_j)`. -/
private theorem prod_eq_upper_mul_mul_lower (k : Fin d)
    (hmn : ∀ i, i ≠ k → m i = n i) :
    ∏ i, m i = (∏ j : Fin (d - (k + 1)), n ⟨k + 1 + j, by omega⟩) * m k *
      ∏ j : Fin k, n (Fin.castLE k.is_lt.le j) := by
  have hL : ∏ j : Fin k, m (Fin.castLE k.is_lt.le j) = ∏ j : Fin k, n (Fin.castLE k.is_lt.le j) :=
    Finset.prod_congr rfl fun j _ => hmn _ (Fin.ne_of_val_ne (by simp; omega))
  have hH : ∏ j : Fin (d - (k + 1)), m ⟨k + 1 + j, by omega⟩ =
      ∏ j : Fin (d - (k + 1)), n ⟨k + 1 + j, by omega⟩ :=
    Finset.prod_congr rfl fun j _ => hmn _ (Fin.ne_of_val_ne (by simp; omega))
  rw [prod_univ_split m k, hL, hH]
  ring

/-- The value of a flattened index tuple does not see a cast of its shape. -/
private theorem finPiFinEquiv_cast_val {e : ℕ} {s t : Fin e → ℕ} (h : ∀ j, s j = t j)
    (x : ∀ j, Fin (s j)) :
    ((finPiFinEquiv fun j => Fin.cast (h j) (x j) : Fin (∏ j, t j)) : ℕ) = finPiFinEquiv x := by
  obtain rfl : s = t := funext h
  rfl

/-- **The flattened mode product is `I ⊗ M ⊗ I`** ([golub2013matrix] (12.4.15)): for a family on
`Fin`-shapes that is `M k` in mode `k` and the value identity `δ_{xy}` elsewhere (the shapes
agreeing off `k`), the flattened `piKronecker` is `I ⊗ M_k ⊗ I` with the identities of the modes
above and below `k`, the higher modes outermost (`finPiFinEquiv` is little-endian). -/
theorem piKronecker_reindex_finPiFinEquiv_eq_kroneckerFin (k : Fin d)
    (M : ∀ i, Matrix (Fin (m i)) (Fin (n i)) R) (hmn : ∀ i, i ≠ k → m i = n i)
    (hM : ∀ i, i ≠ k → ∀ x y, M i x y = if (x : ℕ) = y then 1 else 0) :
    (piKronecker M).reindex finPiFinEquiv finPiFinEquiv =
      (kroneckerFin (kroneckerFin
          (1 : Matrix (Fin (∏ j : Fin (d - (k + 1)), n ⟨k + 1 + j, by omega⟩))
            (Fin (∏ j : Fin (d - (k + 1)), n ⟨k + 1 + j, by omega⟩)) R) (M k))
          (1 : Matrix (Fin (∏ j : Fin k, n (Fin.castLE k.is_lt.le j)))
            (Fin (∏ j : Fin k, n (Fin.castLE k.is_lt.le j))) R)).submatrix
        (finCongr (prod_eq_upper_mul_mul_lower k hmn))
        (finCongr (prod_eq_upper_mul_mul_lower k fun _ _ => rfl)) := by
  have hne_hi : ∀ j : Fin (d - (k + 1)), (⟨k + 1 + j, by omega⟩ : Fin d) ≠ k :=
    fun j => Fin.ne_of_val_ne (by simp; omega)
  have hne_lo : ∀ j : Fin k, Fin.castLE k.is_lt.le j ≠ k :=
    fun j => Fin.ne_of_val_ne (by simp; omega)
  -- the flattened index splits into the digits above `k`, the digit `k` and those below
  have hsplit : ∀ {s : Fin d → ℕ} (hs : ∀ i, i ≠ k → s i = n i) (a : ∀ i, Fin (s i)),
      finCongr (prod_eq_upper_mul_mul_lower k hs) (finPiFinEquiv a) =
        finProdFinEquiv (finProdFinEquiv
          (finPiFinEquiv fun j => Fin.cast (hs _ (hne_hi j)) (a ⟨k + 1 + j, by omega⟩), a k),
          finPiFinEquiv fun j => Fin.cast (hs _ (hne_lo j)) (a (Fin.castLE k.is_lt.le j))) := by
    intro s hs a
    ext
    rw [finCongr_apply, Fin.val_cast, finProdFinEquiv_apply_val, finProdFinEquiv_apply_val,
      finPiFinEquiv_apply_val_split a k, finPiFinEquiv_cast_val, finPiFinEquiv_cast_val]
    have hL : ∏ j : Fin k, s (Fin.castLE k.is_lt.le j) =
        ∏ j : Fin k, n (Fin.castLE k.is_lt.le j) :=
      Finset.prod_congr rfl fun j _ => hs _ (hne_lo j)
    simp only [hL]
  ext I J
  obtain ⟨a, rfl⟩ := finPiFinEquiv.surjective I
  obtain ⟨b, rfl⟩ := finPiFinEquiv.surjective J
  rw [reindex_apply, submatrix_apply, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, piKronecker_apply, hsplit hmn a, hsplit (fun _ _ => rfl) b,
    kroneckerFin_apply, kroneckerFin_apply, one_apply, one_apply,
    Fintype.prod_eq_mul_prod_subtype_ne _ k,
    Finset.prod_congr rfl fun (i : {i // i ≠ k}) _ => hM i i.2 (a i) (b i), Fintype.prod_boole]
  have hiff : (∀ i : {i // i ≠ k}, ((a i : Fin (m i)) : ℕ) = (b i : Fin (n i))) ↔
      ((finPiFinEquiv fun j => Fin.cast (hmn _ (hne_hi j)) (a ⟨k + 1 + j, by omega⟩)) =
          finPiFinEquiv fun j => Fin.cast rfl (b ⟨k + 1 + j, by omega⟩)) ∧
        ((finPiFinEquiv fun j => Fin.cast (hmn _ (hne_lo j)) (a (Fin.castLE k.is_lt.le j))) =
          finPiFinEquiv fun j => Fin.cast rfl (b (Fin.castLE k.is_lt.le j))) := by
    simp only [EmbeddingLike.apply_eq_iff_eq, funext_iff, Fin.ext_iff, Fin.val_cast]
    constructor
    · intro h
      exact ⟨fun j => h ⟨_, hne_hi j⟩, fun j => h ⟨_, hne_lo j⟩⟩
    · rintro ⟨hhi, hlo⟩ ⟨i, hi⟩
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hi) with h | h
      · have := hlo ⟨i, h⟩
        simpa using this
      · have := hhi ⟨i - (k + 1), by omega⟩
        have e : (⟨k + 1 + (i - (k + 1)), by omega⟩ : Fin d) = i := Fin.ext (by simp; omega)
        rw [e] at this
        exact this
  by_cases h : ∀ i : {i // i ≠ k}, ((a i : Fin (m i)) : ℕ) = (b i : Fin (n i))
  · obtain ⟨h1, h2⟩ := hiff.1 h
    simp only [h, h1, h2, implies_true, ↓reduceIte, mul_one, one_mul]
  · rw [ite_eq_right_iff.2 fun h' => absurd h' h, mul_zero]
    rcases not_and_or.1 (mt hiff.2 h) with h1 | h2
    · simp only [h1, ↓reduceIte, zero_mul]
    · simp only [h2, ↓reduceIte, mul_zero]

/-- **[golub2013matrix] (12.4.15)** for the rectangular mode product on `Fin`-shapes:
`vec(𝒮 ×_k M) = (I ⊗ M ⊗ I) vec(𝒮)`, the identities being those of the modes above and below
`k`, up to the identification of the size products. -/
theorem vecFin_rectModeProd
    (S : Tensor (fun i => Fin (n i)) R) (k : Fin d) (hmn : ∀ i, i ≠ k → m i = n i)
    (M : Matrix (Fin (m k)) (Fin (n k)) R) :
    vecFin (S.rectModeProd k (μ := fun i => Fin (m i)) (fun i h => finCongr (hmn i h)) M) =
      (kroneckerFin (kroneckerFin
          (1 : Matrix (Fin (∏ j : Fin (d - (k + 1)), n ⟨k + 1 + j, by omega⟩))
            (Fin (∏ j : Fin (d - (k + 1)), n ⟨k + 1 + j, by omega⟩)) R) M)
          (1 : Matrix (Fin (∏ j : Fin k, n (Fin.castLE k.is_lt.le j)))
            (Fin (∏ j : Fin k, n (Fin.castLE k.is_lt.le j))) R)).submatrix
        (finCongr (prod_eq_upper_mul_mul_lower k hmn))
        (finCongr (prod_eq_upper_mul_mul_lower k fun _ _ => rfl)) *ᵥ vecFin S := by
  rw [rectModeProd, vecFin_multilinearProd,
    piKronecker_reindex_finPiFinEquiv_eq_kroneckerFin k _ hmn fun i hi x y => by
      rw [modeFactors_of_ne hi, submatrix_apply, id, one_apply]
      simp [Fin.ext_iff], modeFactors_self]

end VecFin

end Tensor
