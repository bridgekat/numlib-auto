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
`Function.update κ k μ` agrees with `κ` off `k` only propositionally, so the mode product
`Tensor.modeProd` is defined for square matrices only (shape-preserving, with clean laws), and a
rectangular one is a multilinear product with identity factors.

## Main definitions

* `Tensor.multilinearProd M S`: the multilinear product.
* `Tensor.modeProd S k M`: the mode-`k` product with a square matrix.

## Main statements

* `Tensor.modeUnfold_multilinearProd`, `Tensor.unfold_multilinearProd`: [golub2013matrix]
  Theorem 12.4.1, `𝒜_(k) = M_k 𝒮_(k) (⊗_{j ≠ k} M_j)ᵀ`, and its version for any unfolding.
* `Tensor.multilinearProd_inv`: the second part of Theorem 12.4.1.
* `Tensor.modeProd_comm`, `Tensor.modeProd_modeProd`: [golub2013matrix] (12.4.16)–(12.4.17)
  (the latter corrected).
* `Tensor.multilinearProd_eq_modeProd`: the multilinear product is the composite of the mode
  products, in any order.
* `Tensor.frobenius_norm_multilinearProd_of_orthonormal`: multilinear products by matrices with
  orthonormal columns are isometries.
* `Tensor.vecFin_multilinearProd`: the flattened form (12.4.19).

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

/-! ### Orthonormal factors -/

section Orthonormal

variable {𝕜 : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)]
  [∀ i, DecidableEq (κ i)] [∀ i, Fintype (μ i)]

omit [∀ i, DecidableEq (κ i)] [∀ i, Fintype (μ i)] in
/-- The Frobenius inner product is the dot product with the conjugate. -/
theorem inner_eq_star_dotProduct (A B : Tensor κ 𝕜) :
    ⟪A, B⟫_𝕜 = star (of.symm A) ⬝ᵥ of.symm B :=
  rfl

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

end VecFin

end Tensor
