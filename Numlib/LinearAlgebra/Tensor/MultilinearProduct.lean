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
import Numlib.LinearAlgebra.Tensor.Unfolding

/-!
# Multilinear products and mode products

Let $\mathcal{S}$ be a tensor with mode index types $\kappa_i$, and for each mode $i$ let $M_i$ be a
matrix with rows indexed by $\mu_i$ and columns indexed by $\kappa_i$. The **multilinear (Tucker)
product** $\mathcal{A} = \mathcal{S} \times_1 M_1 \cdots \times_d M_d$ ([golub2013matrix],
§12.4.10–12.4.11) is the tensor with mode index types $\mu_i$ and the entries
$$\mathcal{A}(a) = \sum_b \Bigl(\prod_i M_i(a_i, b_i)\Bigr) \mathcal{S}(b).$$
Its mode-$k$ unfolding is $\mathcal{A}_{(k)} = M_k \mathcal{S}_{(k)} (\bigotimes_{j \neq k} M_j)^T$
(Theorem 12.4.1 of [golub2013matrix]). The mode-$k$ product $\mathcal{S} \times_k M$ is the
multilinear product with $M$ in mode $k$ and identity matrices in the other modes. Mode products in
distinct modes commute, two mode products in the same mode compose, and the multilinear product is
the composite of the $d$ mode products in any order.

The module also proves that multilinear products by matrices with orthonormal columns preserve the
Frobenius norm, and gives the vectorized forms: $\operatorname{vec}(\mathcal{S} \times_1 M_1 \cdots
\times_d M_d) = (M_d \otimes \cdots \otimes M_1) \operatorname{vec}(\mathcal{S})$ (equation
(12.4.19)), and $\operatorname{vec}(\mathcal{S} \times_k M) = (I \otimes M \otimes I)
\operatorname{vec}(\mathcal{S})$ (equation (12.4.15)).

## Main definitions

* `Tensor.multilinearProd`: the multilinear product $\mathcal{S} \times_1 M_1 \cdots \times_d M_d$.
* `Tensor.multilinearProdₗ`: the multilinear product as a linear map in the tensor.
* `Tensor.modeProd`: the mode-$k$ product $\mathcal{S} \times_k M$ with a square matrix $M$.
* `Tensor.rectModeProd`: the mode-$k$ product with a rectangular matrix; `Tensor.rectModeProd_refl`
  shows that the square case is `Tensor.modeProd`.

## Main results

* `Tensor.modeUnfold_multilinearProd`: Theorem 12.4.1 of [golub2013matrix], $\mathcal{A}_{(k)} = M_k
  \mathcal{S}_{(k)} (\bigotimes_{j \neq k} M_j)^T$.
* `Tensor.unfold_multilinearProd`: the same identity for the unfolding along any set of row modes.
* `Tensor.multilinearProd_inv`: the second part of Theorem 12.4.1 of [golub2013matrix]: invertible
  factors can be undone by their inverses.
* `Tensor.modeProd_comm`, `Tensor.modeProd_modeProd`: equations (12.4.16) and (12.4.17) of
  [golub2013matrix], with the order of the product in (12.4.17) corrected.
* `Tensor.rectModeProd_comm`, `Tensor.rectModeProd_rectModeProd`, `Tensor.modeUnfold_rectModeProd`:
  the same laws and equation (12.4.14) for rectangular mode products.
* `Tensor.multilinearProd_eq_modeProd`: the multilinear product is the composite of the $d$ mode
  products, in any order.
* `Tensor.frobenius_norm_multilinearProd_of_orthonormal`: a multilinear product by matrices with
  orthonormal columns preserves the Frobenius norm.
* `Tensor.vecFin_multilinearProd`: the vectorized form (12.4.19) of the multilinear product.
* `Tensor.piKronecker_reindex_finPiFinEquiv_eq_kroneckerFin`, `Tensor.vecFin_rectModeProd`: the
  vectorized mode product is multiplication by $I \otimes M \otimes I$, equation (12.4.15).

## Implementation notes

* The multilinear product is the primitive: `Tensor.multilinearProd M S` is
  `Matrix.piKronecker M *ᵥ S`. Its shape changes from `κ` to `μ` without a cast, and its vectorized
  formulas (12.4.15) and (12.4.19) of [golub2013matrix] hold by definition in the typed form.
* A single mode-$k$ product changes the shape only at $k$. In dependent type theory, the new family
  `Function.update κ k μ` agrees with `κ` outside $k$ only up to a proof of equality. The square
  mode product `Tensor.modeProd` preserves the shape and has simple laws. The rectangular mode
  product `Tensor.rectModeProd` takes a target shape `μ` together with equivalences `μ i ≃ κ i` for
  $i \neq k$, for example `Equiv.cast` for `Function.update`, or `finCongr` for shapes of the form
  `Fin n`. Its laws are those of the multilinear product, with the shapes matched by the
  equivalences.
-/

universe u v v' w

open Matrix
open scoped InnerProductSpace

namespace Tensor

variable {ι : Type u} {κ : ι → Type v} {μ : ι → Type v'} {ν : ι → Type*} {R : Type w}

section Multilinear

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)] [CommSemiring R]

/-- The **multilinear product** $\mathcal{S} \times_1 M_1 \cdots \times_d M_d$ ([golub2013matrix],
(12.4.18)–(12.4.19)). Let $R$ be a commutative semiring, let $\mathcal{S}$ be a tensor with
finite mode index types $\kappa_i$ over a finite set of modes, and let $M_i$ be a matrix with
rows indexed by $\mu_i$ and columns indexed by $\kappa_i$. The product is the tensor with mode
index types $\mu_i$ whose array of entries is
$$\Bigl(\bigotimes_i M_i\Bigr) \mathcal{S},$$
the product of the Kronecker product `Matrix.piKronecker M` of the family $(M_i)$ with the array
of entries of $\mathcal{S}$. -/
def multilinearProd (M : ∀ i, Matrix (μ i) (κ i) R) (S : Tensor κ R) : Tensor μ R :=
  piKronecker M *ᵥ S

/-- Equation (12.4.18) of [golub2013matrix]: the entries of the multilinear product are
$$(\mathcal{S} \times_1 M_1 \cdots \times_d M_d)(a) = \sum_b \Bigl(\prod_i M_i(a_i, b_i)\Bigr)
  \mathcal{S}(b).$$
-/
theorem multilinearProd_apply (M : ∀ i, Matrix (μ i) (κ i) R) (S : Tensor κ R) (a : ∀ i, μ i) :
    multilinearProd M S a = ∑ b, (∏ i, M i (a i) (b i)) * S b :=
  rfl

/-- The array of entries of the multilinear product is the product of the Kronecker product
$\bigotimes_i M_i$ with the array of entries of $\mathcal{S}$. -/
theorem of_symm_multilinearProd (M : ∀ i, Matrix (μ i) (κ i) R) (S : Tensor κ R) :
    of.symm (multilinearProd M S) = piKronecker M *ᵥ of.symm S :=
  rfl

/-- The multilinear product is additive in the tensor: $(\mathcal{S} + \mathcal{T}) \times_i M_i =
\mathcal{S} \times_i M_i + \mathcal{T} \times_i M_i$. -/
theorem multilinearProd_add (M : ∀ i, Matrix (μ i) (κ i) R) (S T : Tensor κ R) :
    multilinearProd M (S + T) = multilinearProd M S + multilinearProd M T :=
  mulVec_add _ _ _

/-- The multilinear product is homogeneous in the tensor: $(c \mathcal{S}) \times_i M_i = c \,
(\mathcal{S} \times_i M_i)$. -/
theorem multilinearProd_smul (M : ∀ i, Matrix (μ i) (κ i) R) (c : R) (S : Tensor κ R) :
    multilinearProd M (c • S) = c • multilinearProd M S :=
  mulVec_smul _ _ _

/-- The multilinear product expands the core along the rank-one tensors of the columns of the
factors ([golub2013matrix], (12.5.7)):
$$\mathcal{S} \times_1 M_1 \cdots \times_d M_d = \sum_b \mathcal{S}(b) \, M_1(:, b_1) \circ
  \cdots \circ M_d(:, b_d).$$
-/
theorem multilinearProd_eq_sum_rankOne (M : ∀ i, Matrix (μ i) (κ i) R) (S : Tensor κ R) :
    multilinearProd M S = ∑ b, S b • rankOne fun i x => M i x (b i) := by
  ext a
  rw [multilinearProd_apply, Tensor.sum_apply]
  exact Finset.sum_congr rfl fun b _ => by rw [Tensor.smul_apply, rankOne_apply, smul_eq_mul,
      mul_comm]

/-- The multilinear product by diagonal matrices $\operatorname{diag}(d_i)$ multiplies each entry by
the product of the diagonal entries: the entry at $a$ is $(\prod_i d_i(a_i)) \, \mathcal{S}(a)$. -/
theorem multilinearProd_diagonal [∀ i, DecidableEq (κ i)] (d : ∀ i, κ i → R) (S : Tensor κ R) :
    multilinearProd (fun i => diagonal (d i)) S = of fun a => (∏ i, d i (a i)) * S a := by
  ext a
  rw [multilinearProd_apply, of_apply, Finset.sum_eq_single a]
  · simp only [diagonal_apply_eq]
  · intro b _ hb
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hb
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (diagonal_apply_ne (d i) (Ne.symm hi)), zero_mul]
  · simp

/-- The multilinear product $\mathcal{S} \mapsto \mathcal{S} \times_1 M_1 \cdots \times_d M_d$ as a
linear map in the tensor. -/
def multilinearProdₗ (M : ∀ i, Matrix (μ i) (κ i) R) : Tensor κ R →ₗ[R] Tensor μ R where
  toFun := multilinearProd M
  map_add' := multilinearProd_add M
  map_smul' := multilinearProd_smul M

/-- The linear map `Tensor.multilinearProdₗ M` is the multilinear product with the factors $M_i$. -/
@[simp]
theorem multilinearProdₗ_apply (M : ∀ i, Matrix (μ i) (κ i) R) (S : Tensor κ R) :
    multilinearProdₗ M S = multilinearProd M S :=
  rfl

/-- Over a commutative ring, the multilinear product respects subtraction: $(\mathcal{S} -
\mathcal{T}) \times_i M_i = \mathcal{S} \times_i M_i - \mathcal{T} \times_i M_i$. -/
theorem multilinearProd_sub {R : Type w} [CommRing R] (M : ∀ i, Matrix (μ i) (κ i) R)
    (S T : Tensor κ R) :
    multilinearProd M (S - T) = multilinearProd M S - multilinearProd M T :=
  mulVec_sub _ _ _

/-- The multilinear product by identity matrices is the identity: $\mathcal{S} \times_1 I \cdots
\times_d I = \mathcal{S}$. -/
@[simp]
theorem multilinearProd_one [∀ i, DecidableEq (κ i)] (S : Tensor κ R) :
    multilinearProd (fun i => (1 : Matrix (κ i) (κ i) R)) S = S := by
  apply of.symm.injective
  rw [of_symm_multilinearProd, piKronecker_one, one_mulVec]

/-- Multilinear products compose factorwise. Let $R$ be a commutative semiring, and let $M_i$ have
rows indexed by $\mu_i$ and columns indexed by $\kappa_i$, and $N_i$ have rows indexed by
$\nu_i$ and columns indexed by $\mu_i$, with all $\mu_i$ finite. Then
$$(\mathcal{S} \times_1 M_1 \cdots \times_d M_d) \times_1 N_1 \cdots \times_d N_d = \mathcal{S}
  \times_1 (N_1 M_1) \cdots \times_d (N_d M_d).$$

This is the form for families of the laws (12.4.16)–(12.4.17) of [golub2013matrix]. -/
theorem multilinearProd_multilinearProd [∀ i, Fintype (μ i)] (M : ∀ i, Matrix (μ i) (κ i) R)
    (N : ∀ i, Matrix (ν i) (μ i) R) (S : Tensor κ R) :
    multilinearProd N (multilinearProd M S) = multilinearProd (fun i => N i * M i) S := by
  apply of.symm.injective
  rw [of_symm_multilinearProd, of_symm_multilinearProd, of_symm_multilinearProd,
    mulVec_mulVec, piKronecker_mul_piKronecker]

/-- **Theorem 12.4.1** of [golub2013matrix], second part. Let $R$ be a commutative ring, and let
every $M_i$ be an invertible square matrix indexed by $\kappa_i$. If $\mathcal{A} = \mathcal{S}
\times_1 M_1 \cdots \times_d M_d$, then
$$\mathcal{S} = \mathcal{A} \times_1 M_1^{-1} \cdots \times_d M_d^{-1}.$$
-/
theorem multilinearProd_inv {R : Type w} [CommRing R] [∀ i, DecidableEq (κ i)]
    {M : ∀ i, Matrix (κ i) (κ i) R} (hM : ∀ i, IsUnit (M i)) {S A : Tensor κ R}
    (h : A = multilinearProd M S) : S = multilinearProd (fun i => (M i)⁻¹) A := by
  subst h
  rw [multilinearProd_multilinearProd]
  simp_rw [nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 (hM _)), multilinearProd_one]

/-- Let $e$ identify the index tuples of $\kappa$ with pairs in $\alpha \times \beta$, and $e'$ the
index tuples of $\mu$ with pairs in $\alpha' \times \beta'$. If the Kronecker product of the
$M_i$ factors along these pairs as $P(r, y) \, Q(c, z)$, then the multilinear product, read as a
matrix through $e'$, is $P S Q^T$, where $S$ is the tensor $\mathcal{S}$ read as a matrix
through $e$. -/
private theorem of_multilinearProd_eq_mul {α β α' β' : Type*} [Fintype α] [Fintype β]
    (e : (∀ i, κ i) ≃ α × β) (e' : (∀ i, μ i) ≃ α' × β') (M : ∀ i, Matrix (μ i) (κ i) R)
    (P : Matrix α' α R) (Q : Matrix β' β R)
    (hPQ : ∀ r c y z, piKronecker M (e'.symm (r, c)) (e.symm (y, z)) = P r y * Q c z)
    (S : Tensor κ R) :
    (Matrix.of fun r c => multilinearProd M S (e'.symm (r, c)) : Matrix α' β' R)
      = P * Matrix.of (fun y z => S (e.symm (y, z))) * Qᵀ := by
  ext r c
  simp only [Matrix.of_apply, multilinearProd, mulVec, dotProduct, Matrix.mul_apply,
      transpose_apply]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [hPQ, Finset.sum_mul]
  exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => by ring

/-- The unfolding identity of [golub2013matrix], P12.4.9. For the unfolding with the row modes
$r = \{i \mid p(i)\}$ and the column modes $c = \{i \mid \neg p(i)\}$,
$$(\mathcal{S} \times_1 M_1 \cdots \times_d M_d)_{r \times c} = \Bigl(\bigotimes_{i \in r}
  M_i\Bigr) \mathcal{S}_{r \times c} \Bigl(\bigotimes_{i \in c} M_i\Bigr)^T.$$
-/
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

/-- **Theorem 12.4.1** of [golub2013matrix], in typed form. Let $R$ be a commutative semiring, let
$\mathcal{S}$ be a tensor over a finite set of modes with finite index types $\kappa_i$, and let
$M_i$ have rows indexed by $\mu_i$ and columns indexed by $\kappa_i$. If $\mathcal{A} =
\mathcal{S} \times_1 M_1 \cdots \times_d M_d$, then for every mode $k$,
$$\mathcal{A}_{(k)} = M_k \, \mathcal{S}_{(k)} \Bigl(\bigotimes_{j \neq k} M_j\Bigr)^T.$$

The Kronecker product $\bigotimes_{j \neq k} M_j$ is `Matrix.piKronecker` of the family
restricted to the modes $j \neq k$, on the index tuples. The book flattens these tuples in a
fixed order; here they stay typed. -/
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

/-- The **mode-$k$ product** $\mathcal{S} \times_k M$ with a square matrix $M$ indexed by $\kappa_k$
([golub2013matrix], (12.4.14), the case that preserves the shape). It is the multilinear product
with $M$ in mode $k$ and the identity matrix in every other mode. -/
def modeProd (S : Tensor κ R) (k : ι) (M : Matrix (κ k) (κ k) R) : Tensor κ R :=
  multilinearProd (Function.update (fun i => (1 : Matrix (κ i) (κ i) R)) k M) S

/-- Equation (12.4.14) of [golub2013matrix]: $(\mathcal{S} \times_k M)_{(k)} = M \,
\mathcal{S}_{(k)}$. -/
theorem modeUnfold_modeProd (S : Tensor κ R) (k : ι) (M : Matrix (κ k) (κ k) R) :
    (S.modeProd k M).modeUnfold k = M * S.modeUnfold k := by
  rw [modeProd, modeUnfold_multilinearProd, Function.update_self]
  have h : (fun j : {j // j ≠ k} =>
      Function.update (fun i => (1 : Matrix (κ i) (κ i) R)) k M j) = fun j => 1 :=
    funext fun j => Function.update_of_ne j.2 _ _
  rw [h, piKronecker_one, transpose_one, Matrix.mul_one]

omit [Fintype ι] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [CommSemiring R] in
/-- The entry of the mode-$k$ unfolding in the row $y$ and the column given by $a$ off $k$ is the
entry of $\mathcal{S}$ at $a$ with its $k$-th index replaced by $y$. -/
private theorem modeUnfold_apply_update (S : Tensor κ R) (k : ι) (a : ∀ i, κ i) (y : κ k) :
    S.modeUnfold k y (fun j => a j) = S (Function.update a k y) := by
  rw [← modeUnfold_apply S k (Function.update a k y), Function.update_self]
  congr 1
  funext j
  rw [Function.update_of_ne j.2]

/-- The entries of a mode product: $(\mathcal{S} \times_k M)(a) = \sum_y M(a_k, y) \,
\mathcal{S}(a')$, where $a'$ is $a$ with its $k$-th index replaced by $y$. -/
theorem modeProd_apply (S : Tensor κ R) (k : ι) (M : Matrix (κ k) (κ k) R) (a : ∀ i, κ i) :
    S.modeProd k M a = ∑ y, M (a k) y * S (Function.update a k y) := by
  rw [← modeUnfold_apply (S.modeProd k M) k a, modeUnfold_modeProd, Matrix.mul_apply]
  simp only [modeUnfold_apply_update]

/-- Two mode products in the same mode compose: $(\mathcal{S} \times_k F) \times_k G = \mathcal{S}
\times_k (GF)$.

Equation (12.4.17) of [golub2013matrix] prints the product $FG$. The correct order is $GF$,
because the second factor acts after the first. -/
theorem modeProd_modeProd (S : Tensor κ R) (k : ι) (F G : Matrix (κ k) (κ k) R) :
    (S.modeProd k F).modeProd k G = S.modeProd k (G * F) := by
  rw [modeProd, modeProd, multilinearProd_multilinearProd, modeProd]
  congr 1
  funext i
  by_cases h : i = k
  · subst h
    simp
  · simp [h]

/-- Mode products in distinct modes commute ([golub2013matrix], (12.4.16)). Let $j \neq k$, let $F$
be a square matrix indexed by $\kappa_k$, and let $G$ be a square matrix indexed by $\kappa_j$.
Then
$$(\mathcal{S} \times_k F) \times_j G = (\mathcal{S} \times_j G) \times_k F.$$
-/
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

/-- Applying the mode products $\times_k M_k$ along a list of distinct modes, in the order of the
list, gives the multilinear product with $M_i$ at the listed modes and the identity matrix at
the other modes. -/
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

/-- The multilinear product is the composite of the $d$ mode products, in any order
([golub2013matrix], §12.4.11: "their order is immaterial"). Let $M_i$ be square matrices indexed
by $\kappa_i$, and let $k_1, \dots, k_d$ be a list of the modes in which every mode appears
exactly once. Then
$$\mathcal{S} \times_1 M_1 \cdots \times_d M_d = (\cdots((\mathcal{S} \times_{k_1} M_{k_1})
  \times_{k_2} M_{k_2}) \cdots) \times_{k_d} M_{k_d}.$$
-/
theorem multilinearProd_eq_modeProd (M : ∀ i, Matrix (κ i) (κ i) R) {l : List ι}
    (hl : l.Nodup) (hmem : ∀ i, i ∈ l) (S : Tensor κ R) :
    multilinearProd M S = l.foldl (fun T k => T.modeProd k (M k)) S := by
  rw [foldl_modeProd M hl]
  simp [hmem]

end ModeProd

/-!
### Rectangular mode products

A mode-$k$ product with a rectangular matrix $M$, with rows indexed by $\mu_k$ and columns indexed
by $\kappa_k$, changes the shape only at $k$. The new shape $\mu$ is any family that agrees with
$\kappa$ outside $k$ along given equivalences $e_i \colon \mu_i \simeq \kappa_i$ for $i \neq k$: for
example `Function.update κ k μ'` with `Equiv.cast`, or, for shapes of the form `Fin n`,
`fun i => Fin (Function.update n k m i)` with `finCongr`. Commutation and composition then follow
from the factorwise composition `Tensor.multilinearProd_multilinearProd`, with the shapes matched by
the equivalences.
-/

section RectModeProd

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
  [CommSemiring R]

/-- The factors of a rectangular mode-$k$ product into the shape $\mu$, which agrees with $\kappa$
outside $k$ along the equivalences $e$: the matrix $M$ in mode $k$, and in each mode $i \neq k$
the identity matrix with its rows read through $e_i$. -/
def modeFactors (k : ι) (e : ∀ i, i ≠ k → μ i ≃ κ i) (M : Matrix (μ k) (κ k) R) (i : ι) :
    Matrix (μ i) (κ i) R :=
  if h : i = k then h ▸ M else (1 : Matrix (κ i) (κ i) R).submatrix (e i h) id

omit [Fintype ι] [∀ i, Fintype (κ i)] in
/-- In mode $k$, the factor of `Tensor.modeFactors` is $M$. -/
theorem modeFactors_self (k : ι) (e : ∀ i, i ≠ k → μ i ≃ κ i) (M : Matrix (μ k) (κ k) R) :
    modeFactors k e M k = M := by
  simp [modeFactors]

omit [Fintype ι] [∀ i, Fintype (κ i)] in
/-- In a mode $i \neq k$, the factor of `Tensor.modeFactors` is the identity matrix with its rows
read through $e_i$. -/
theorem modeFactors_of_ne {k i : ι} (h : i ≠ k) (e : ∀ i, i ≠ k → μ i ≃ κ i)
    (M : Matrix (μ k) (κ k) R) :
    modeFactors k e M i = (1 : Matrix (κ i) (κ i) R).submatrix (e i h) id := by
  simp [modeFactors, h]

/-- The **rectangular mode-$k$ product** $\mathcal{S} \times_k M$ ([golub2013matrix], §12.4.10), for
a matrix $M$ with rows indexed by $\mu_k$ and columns indexed by $\kappa_k$. The result has the
shape $\mu$, which agrees with $\kappa$ outside $k$ along the equivalences
$e_i \colon \mu_i \simeq \kappa_i$. It is the multilinear product with $M$ in mode $k$ and the
identity matrices, read through $e_i$, in the other modes. -/
def rectModeProd (S : Tensor κ R) (k : ι) (e : ∀ i, i ≠ k → μ i ≃ κ i)
    (M : Matrix (μ k) (κ k) R) : Tensor μ R :=
  multilinearProd (modeFactors k e M) S

/-- The square mode product is the rectangular one with $\mu = \kappa$ and the identity
equivalences. -/
theorem rectModeProd_refl (S : Tensor κ R) (k : ι) (M : Matrix (κ k) (κ k) R) :
    S.rectModeProd k (fun _ _ => Equiv.refl _) M = S.modeProd k M := by
  rw [rectModeProd, modeProd]
  congr 1

/-- Multiplying a matrix $N$ on the left by the identity matrix with its rows read through $e$ reads
the rows of $N$ through $e$. -/
private theorem one_submatrix_mul {α β γ : Type*} [Fintype β] [DecidableEq β] (e : α ≃ β)
    (N : Matrix β γ R) : (1 : Matrix β β R).submatrix e id * N = N.submatrix e id := by
  ext x z
  simp [Matrix.mul_apply, Matrix.one_apply]

/-- Multiplying a matrix $N$ on the right by the identity matrix with its rows read through $e$
reads the columns of $N$ through $e^{-1}$. -/
private theorem mul_one_submatrix {α β γ : Type*} [Fintype α] [DecidableEq β] (e : α ≃ β)
    (N : Matrix γ α R) : N * (1 : Matrix β β R).submatrix e id = N.submatrix id e.symm := by
  ext x z
  simp only [Matrix.mul_apply, submatrix_apply, id, Matrix.one_apply]
  rw [Finset.sum_eq_single (e.symm z)]
  · simp
  · intro y _ hy
    rw [ite_eq_right_iff.2 fun h => absurd h fun h' => hy (by rw [← h', Equiv.symm_apply_apply]),
      mul_zero]
  · simp

/-- **Composition in one mode** ([golub2013matrix], (12.4.17), rectangular form). Let $F$ have rows
indexed by $\mu_k$ and columns indexed by $\kappa_k$, with $\mu$ matched to $\kappa$ outside $k$
by $e$, and let $G$ have rows indexed by $\nu_k$ and columns indexed by $\mu_k$, with $\nu$
matched to $\mu$ outside $k$ by $e'$, where all $\mu_i$ are finite. Then
$$(\mathcal{S} \times_k F) \times_k G = \mathcal{S} \times_k (GF),$$
where the right side matches $\nu$ to $\kappa$ by the composites of $e'$ and $e$.

Equation (12.4.17) of [golub2013matrix] prints the product $FG$; the correct order is $GF$. -/
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
    simp [Matrix.one_apply]

/-- **Mode products in distinct modes commute** ([golub2013matrix], (12.4.16), rectangular form).
Let $j \neq k$. Let $F$ act in mode $k$ from the shape $\kappa$ to the shape $\mu$ (matched off
$k$ by $e$), and let $G$ act in mode $j$ from $\mu$ to $\nu$ (matched off $j$ by $e'$). For the
other route, let $\rho$ be a shape matched to $\kappa$ off $j$ by $f$, with $\nu$ matched to
$\rho$ off $k$ by $f'$. If the two composite equivalences from $\nu$ to $\kappa$ agree at every
mode $i \neq j, k$, then
$$(\mathcal{S} \times_k F) \times_j G = (\mathcal{S} \times_j G') \times_k F',$$
where $G'(r, c) = G((f'_j)^{-1} r, e_j^{-1} c)$ and $F'(r, c) = F(e'_k r, f_k c)$. -/
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

/-- Equation (12.4.14) of [golub2013matrix], rectangular form: $(\mathcal{S} \times_k M)_{(k)} = M
\, \mathcal{S}_{(k)}$, with the columns read through the equivalences $e_j$ for $j \neq k$. -/
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
      rw [modeFactors_of_ne j.2, submatrix_apply, id, Matrix.one_apply], Fintype.prod_boole]
    exact if_congr funext_iff.symm rfl rfl
  simp only [hprod, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end RectModeProd

/-! ### Orthonormal factors -/

section Orthonormal

variable {𝕜 : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)]
  [∀ i, DecidableEq (κ i)] [∀ i, Fintype (μ i)]


omit [∀ i, DecidableEq (κ i)] in
/-- Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. The multilinear product by the conjugate
transposes is the adjoint of the multilinear product:
$$\langle \mathcal{A}, \mathcal{S} \times_1 U_1 \cdots \times_d U_d \rangle = \langle
  \mathcal{A} \times_1 U_1^H \cdots \times_d U_d^H, \mathcal{S} \rangle.$$
-/
theorem inner_multilinearProd_right (U : ∀ i, Matrix (μ i) (κ i) 𝕜) (A : Tensor μ 𝕜)
    (S : Tensor κ 𝕜) :
    ⟪A, multilinearProd U S⟫_𝕜 = ⟪multilinearProd (fun i => (U i)ᴴ) A, S⟫_𝕜 := by
  rw [inner_eq_star_dotProduct, inner_eq_star_dotProduct, of_symm_multilinearProd,
    of_symm_multilinearProd, dotProduct_mulVec, ← conjTranspose_piKronecker, star_mulVec,
    conjTranspose_conjTranspose]

/-- Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. If every $U_i$ has orthonormal columns,
$U_i^H U_i = I$, then the multilinear product by the $U_i$ preserves the Frobenius inner
product: $\langle \mathcal{S} \times_i U_i, \mathcal{T} \times_i U_i \rangle = \langle
\mathcal{S}, \mathcal{T} \rangle$. -/
theorem inner_multilinearProd_of_orthonormal {U : ∀ i, Matrix (μ i) (κ i) 𝕜}
    (hU : ∀ i, (U i)ᴴ * U i = 1) (S T : Tensor κ 𝕜) :
    ⟪multilinearProd U S, multilinearProd U T⟫_𝕜 = ⟪S, T⟫_𝕜 := by
  rw [inner_multilinearProd_right, multilinearProd_multilinearProd]
  simp only [hU, multilinearProd_one]

/-- Multilinear products by matrices with orthonormal columns preserve the Frobenius norm. Let
$\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let all mode index types be finite, and let every
$U_i$ have rows indexed by $\mu_i$, columns indexed by $\kappa_i$ and $U_i^H U_i = I$. Then for
every tensor $\mathcal{S}$,
$$\|\mathcal{S} \times_1 U_1 \cdots \times_d U_d\| = \|\mathcal{S}\|.$$

This is the step of [golub2013matrix], §12.5.3, that the book justifies by "since
$U_3 \otimes U_2 \otimes U_1$ has orthonormal columns". -/
theorem frobenius_norm_multilinearProd_of_orthonormal {U : ∀ i, Matrix (μ i) (κ i) 𝕜}
    (hU : ∀ i, (U i)ᴴ * U i = 1) (S : Tensor κ 𝕜) : ‖multilinearProd U S‖ = ‖S‖ := by
  rw [@norm_eq_sqrt_re_inner 𝕜, @norm_eq_sqrt_re_inner 𝕜 (Tensor κ 𝕜),
    inner_multilinearProd_of_orthonormal hU]

/-- If every $U_i$ has orthonormal columns, $U_i^H U_i = I$, then the multilinear product by the
conjugate transposes $U_i^H$ undoes the multilinear product by the $U_i$. -/
theorem multilinearProd_conjTranspose_multilinearProd {U : ∀ i, Matrix (μ i) (κ i) 𝕜}
    (hU : ∀ i, (U i)ᴴ * U i = 1) (S : Tensor κ 𝕜) :
    multilinearProd (fun i => (U i)ᴴ) (multilinearProd U S) = S := by
  rw [multilinearProd_multilinearProd]
  simp_rw [hU, multilinearProd_one]

end Orthonormal

/-! ### The vectorized form -/

section VecFin

variable {d : ℕ} {m n : Fin d → ℕ} [CommSemiring R]

/-- Equation (12.4.19) of [golub2013matrix], in vectorized form. Let $M_k \in R^{m_k \times n_k}$
for $k = 1, \dots, d$, and let $\mathcal{S} \in R^{n_1 \times \cdots \times n_d}$. Then
$$\operatorname{vec}(\mathcal{S} \times_1 M_1 \cdots \times_d M_d) = (M_d \otimes \cdots \otimes
  M_1) \operatorname{vec}(\mathcal{S}).$$

The matrix on the right is `Matrix.piKronecker M` with its rows and columns flattened by
`finPiFinEquiv`. By `Matrix.piKronecker_reindex_finPiFinEquiv`, this is the reversed Kronecker
product $M_d \otimes \cdots \otimes M_1$ of the book. -/
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

/-- A product over $\{0, \dots, d - 1\}$ splits at $k$ into the product of the factors below $k$,
the $k$-th factor, and the product of the factors above $k$. -/
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

/-- If the shape $m$ agrees with $n$ outside $k$, then $\prod_i m_i = (\prod_{j > k} n_j) \, m_k \,
(\prod_{j < k} n_j)$. -/
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

/-- The position of a flattened index tuple does not change when the shape is cast to an equal
shape. -/
private theorem finPiFinEquiv_cast_val {e : ℕ} {s t : Fin e → ℕ} (h : ∀ j, s j = t j)
    (x : ∀ j, Fin (s j)) :
    ((finPiFinEquiv fun j => Fin.cast (h j) (x j) : Fin (∏ j, t j)) : ℕ) = finPiFinEquiv x := by
  obtain rfl : s = t := funext h
  rfl

/-- **The vectorized mode product is $I \otimes M \otimes I$** ([golub2013matrix], (12.4.15)). Let
$M_i \in R^{m_i \times n_i}$ for $i = 0, \dots, d - 1$, where $m_i = n_i$ and $M_i$ is the
identity matrix for every $i \neq k$. Then the Kronecker product `Matrix.piKronecker M`, with
its rows and columns flattened by `finPiFinEquiv`, is
$$I_{N_>} \otimes M_k \otimes I_{N_<}, \qquad N_> = \prod_{j > k} n_j, \quad N_< = \prod_{j < k}
  n_j,$$
up to the identification of the products of the sizes.

The higher modes are outermost, because `finPiFinEquiv` is little-endian. The identity outside
$k$ is stated as $M_i(x, y) = 1$ if $x$ and $y$ have the same value and $0$ otherwise, since the
index types $\{0, \dots, m_i - 1\}$ and $\{0, \dots, n_i - 1\}$ are equal only up to a proof.
The Kronecker products are `Matrix.kroneckerFin`. -/
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
    kroneckerFin_apply, kroneckerFin_apply, Matrix.one_apply, Matrix.one_apply,
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

/-- **Equation (12.4.15)** of [golub2013matrix] for the rectangular mode product. Let $\mathcal{S}
\in R^{n_0 \times \cdots \times n_{d-1}}$, let $m$ agree with $n$ outside $k$, and let
$M \in R^{m_k \times n_k}$. Then
$$\operatorname{vec}(\mathcal{S} \times_k M) = (I_{N_>} \otimes M \otimes I_{N_<})
  \operatorname{vec}(\mathcal{S}), \qquad N_> = \prod_{j > k} n_j, \quad N_< = \prod_{j < k}
  n_j,$$
up to the identification of the products of the sizes.

The shapes are matched outside $k$ by `finCongr`. The Kronecker products are
`Matrix.kroneckerFin`. -/
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
      rw [modeFactors_of_ne hi, submatrix_apply, id, Matrix.one_apply]
      simp [Fin.ext_iff], modeFactors_self]

end VecFin

end Tensor
