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
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.PiTensorProduct.Finsupp
import Numlib.LinearAlgebra.Matrix.Kronecker

/-!
# Concrete tensors

A tensor with a set of modes $\iota$ and an index type $\kappa_i$ for each mode $i$ is an array
$\mathcal{A}$ of entries $\mathcal{A}(a)$, indexed by the tuples $a \in \prod_i \kappa_i$. An
order-$d$ tensor $\mathcal{A} \in \mathbb{R}^{n_1 \times \cdots \times n_d}$ of [golub2013matrix],
§12.4, is the case $\iota = \{1, \dots, d\}$ and $\kappa_k = \{1, \dots, n_k\}$. Over $\mathbb{R}$
or $\mathbb{C}$, tensors form an inner product space with the Frobenius inner product $\langle
\mathcal{A}, \mathcal{B} \rangle = \sum_a \overline{\mathcal{A}(a)} \mathcal{B}(a)$ and the
Frobenius norm $\|\mathcal{A}\| = (\sum_a |\mathcal{A}(a)|^2)^{1/2}$.

This module defines rank-one tensors $z_1 \circ \cdots \circ z_d$, outer products, subtensors
(fibers and slices), transposition of modes, matrices as order-2 tensors, symmetric tensors, and the
column-ordered vectorization of [golub2013matrix], §12.4. It proves that every tensor is a sum of
rank-one tensors, and that the vectorization of an order-$(d + 1)$ tensor stacks the vectorizations
of its slices along the last mode. It also identifies concrete tensors with Mathlib's abstract
tensor product.

## Main definitions

* `Tensor`: the tensors with mode index types $\kappa_i$ and entries in $R$, the functions
  $\prod_i \kappa_i \to R$.
* `Tensor.toEuclidean`: the linear isometry from tensors with the Frobenius norm onto
  `EuclideanSpace 𝕜 (∀ i, κ i)`.
* `Tensor.rankOne`: the rank-one tensor $z_1 \circ \cdots \circ z_d$ with entries
  $\prod_i z_i(a_i)$.
* `Tensor.IsRankOne`: the property of being a rank-one tensor.
* `Tensor.outer`: the outer product of two tensors, on the disjoint union of their modes.
* `Tensor.restrict`: the subtensor obtained by fixing the indices of the modes outside a given set.
* `Tensor.permute`: the transposition of a tensor along a bijection of modes.
* `Tensor.ofMatrix`: a matrix as an order-2 tensor.
* `Tensor.IsSymm`: a tensor whose entries are invariant under every permutation of the modes.
* `Tensor.vecFin`: the column-ordered vectorization of a tensor in
  $\mathbb{R}^{n_1 \times \cdots \times n_d}$.
* `Tensor.equivPiTensorProduct`: the linear equivalence with Mathlib's tensor product
  $\bigotimes_i R^{\kappa_i}$.

## Main results

* `Tensor.frobenius_norm_def`: $\|\mathcal{A}\| = (\sum_a |\mathcal{A}(a)|^2)^{1/2}$.
* `Tensor.eq_sum_rankOne_single`: every tensor is the sum of its entries times the rank-one tensors
  of standard basis vectors.
* `Tensor.vecFin_snoc`: the vectorization of an order-$(d + 1)$ tensor stacks the vectorizations of
  its slices along the last mode.

## Implementation notes

* `Tensor κ R` is the type `(∀ i, κ i) → R`, made a `def` in the same way as `Matrix`. Instance
  search therefore sees no `Pi` structure beyond the algebraic structure given here. In particular,
  the norm of a tensor over `𝕜` is the Frobenius norm, which comes from a global inner product space
  structure, and not the supremum norm of `Pi`.
* The order-$d$ tensor $\mathcal{A} \in \mathbb{R}^{n_1 \times \cdots \times n_d}$ is
  `A : Tensor (fun k : Fin d => Fin (n k)) ℝ`. The entry `A i` is $\mathcal{A}(i)$. Indices are
  0-based.
* Mathlib's abstract tensor product `⨂[R] i, (κ i → R)` (`PiTensorProduct`) is a quotient without
  entries. Numerical statements are about entries, unfoldings and orderings of indices. The two meet
  at `Tensor.equivPiTensorProduct`, which sends `Tensor.rankOne z` to `⨂ₜ i, z i`.
* The vectorization `Tensor.vecFin` uses Mathlib's little-endian equivalence `finPiFinEquiv`, which
  is the index map $\operatorname{col}(i, n)$ of [golub2013matrix], §12.4.
-/

universe u u' v w

open scoped ComplexConjugate InnerProductSpace TensorProduct

/-! ### Finiteness of `![α, β, …]`-shaped index families -/

namespace Matrix

/-- The types of a `vecCons` family of finite types are finite. -/
instance fintypeVecCons {n : ℕ} {α : Type v} {f : Fin n → Type v} [Fintype α]
    [∀ i, Fintype (f i)] (i : Fin (n + 1)) : Fintype (vecCons α f i) :=
  Fin.cases (motive := fun i => Fintype (vecCons α f i)) ‹Fintype α›
    (fun j => (inferInstance : Fintype (f j))) i

/-- The empty family of types is (vacuously) a family of finite types. -/
instance fintypeVecEmpty (i : Fin 0) : Fintype ((vecEmpty : Fin 0 → Type v) i) :=
  i.elim0

/-- The types of a `vecCons` family of types with decidable equality have decidable equality. -/
instance decidableEqVecCons {n : ℕ} {α : Type v} {f : Fin n → Type v} [DecidableEq α]
    [∀ i, DecidableEq (f i)] (i : Fin (n + 1)) : DecidableEq (vecCons α f i) :=
  Fin.cases (motive := fun i => DecidableEq (vecCons α f i)) ‹DecidableEq α›
    (fun j => (inferInstance : DecidableEq (f j))) i

/-- The empty family of types is (vacuously) a family of types with decidable equality. -/
instance decidableEqVecEmpty (i : Fin 0) : DecidableEq ((vecEmpty : Fin 0 → Type v) i) :=
  i.elim0

end Matrix

namespace Sum

/-- The types of a `Sum.elim` family of finite types are finite. -/
instance fintypeElim {α β : Type*} {f : α → Type v} {g : β → Type v} [∀ a, Fintype (f a)]
    [∀ b, Fintype (g b)] (x : α ⊕ β) : Fintype (Sum.elim f g x) :=
  Sum.rec (motive := fun x => Fintype (Sum.elim f g x)) (fun a => (inferInstance : Fintype (f a)))
    (fun b => (inferInstance : Fintype (g b))) x

/-- The types of a `Sum.elim` family of types with decidable equality have decidable equality. -/
instance decidableEqElim {α β : Type*} {f : α → Type v} {g : β → Type v}
    [∀ a, DecidableEq (f a)] [∀ b, DecidableEq (g b)] (x : α ⊕ β) :
    DecidableEq (Sum.elim f g x) :=
  Sum.rec (motive := fun x => DecidableEq (Sum.elim f g x))
    (fun a => (inferInstance : DecidableEq (f a))) (fun b => (inferInstance : DecidableEq (g b))) x

end Sum

namespace Function

/-- The types of a composite family `f ∘ g` of finite types are finite. -/
instance fintypeComp {α β : Type*} {f : β → Type v} [∀ b, Fintype (f b)] (g : α → β) (a : α) :
    Fintype ((f ∘ g) a) :=
  inferInstanceAs (Fintype (f (g a)))

end Function

/-- A **tensor** with modes $\iota$ and mode index types $\kappa_i$ is an array $\mathcal{A}$ of
entries in $R$, indexed by the tuples $a \in \prod_i \kappa_i$ of indices.

The order-$d$ tensor $\mathcal{A} \in \mathbb{R}^{n_1 \times \cdots \times n_d}$ of
[golub2013matrix], §12.4, is `Tensor (fun k : Fin d => Fin (n k)) ℝ`, and its entry
$\mathcal{A}(i)$ is `A i`. -/
def Tensor {ι : Type u} (κ : ι → Type v) (R : Type w) : Type max u v w :=
  (∀ i, κ i) → R

namespace Tensor

variable {ι : Type u} {κ : ι → Type v} {R : Type w} {S : Type*}

/-- The identification of the arrays $\prod_i \kappa_i \to R$ with the tensors. -/
def of : ((∀ i, κ i) → R) ≃ Tensor κ R :=
  Equiv.refl _

/-- The entries of `Tensor.of f` are the values of $f$. -/
@[simp]
theorem of_apply (f : (∀ i, κ i) → R) (a : ∀ i, κ i) : of f a = f a :=
  rfl

/-- The entries of `Tensor.of.symm A` are the entries of $\mathcal{A}$. -/
@[simp]
theorem of_symm_apply (A : Tensor κ R) (a : ∀ i, κ i) : of.symm A a = A a :=
  rfl

/-- Two tensors with the same entries are equal. -/
@[ext]
theorem ext {A B : Tensor κ R} (h : ∀ a, A a = B a) : A = B :=
  funext h

/-! ### Algebraic structure -/

instance [Inhabited R] : Inhabited (Tensor κ R) :=
  inferInstanceAs <| Inhabited ((∀ i, κ i) → R)

instance [Add R] : Add (Tensor κ R) :=
  inferInstanceAs <| Add ((∀ i, κ i) → R)

instance [SMul S R] : SMul S (Tensor κ R) :=
  inferInstanceAs <| SMul S ((∀ i, κ i) → R)

instance [AddSemigroup R] : AddSemigroup (Tensor κ R) :=
  inferInstanceAs <| AddSemigroup ((∀ i, κ i) → R)

instance [AddCommSemigroup R] : AddCommSemigroup (Tensor κ R) :=
  inferInstanceAs <| AddCommSemigroup ((∀ i, κ i) → R)

instance [Zero R] : Zero (Tensor κ R) :=
  inferInstanceAs <| Zero ((∀ i, κ i) → R)

instance [AddZeroClass R] : AddZeroClass (Tensor κ R) :=
  inferInstanceAs <| AddZeroClass ((∀ i, κ i) → R)

instance [AddMonoid R] : AddMonoid (Tensor κ R) :=
  inferInstanceAs <| AddMonoid ((∀ i, κ i) → R)

instance [AddCommMonoid R] : AddCommMonoid (Tensor κ R) :=
  inferInstanceAs <| AddCommMonoid ((∀ i, κ i) → R)

instance [Neg R] : Neg (Tensor κ R) :=
  inferInstanceAs <| Neg ((∀ i, κ i) → R)

instance [Sub R] : Sub (Tensor κ R) :=
  inferInstanceAs <| Sub ((∀ i, κ i) → R)

instance [AddGroup R] : AddGroup (Tensor κ R) :=
  inferInstanceAs <| AddGroup ((∀ i, κ i) → R)

instance [AddCommGroup R] : AddCommGroup (Tensor κ R) :=
  inferInstanceAs <| AddCommGroup ((∀ i, κ i) → R)

instance [Monoid S] [MulAction S R] : MulAction S (Tensor κ R) :=
  inferInstanceAs <| MulAction S ((∀ i, κ i) → R)

instance [Monoid S] [AddMonoid R] [DistribMulAction S R] : DistribMulAction S (Tensor κ R) :=
  inferInstanceAs <| DistribMulAction S ((∀ i, κ i) → R)

instance [Semiring S] [AddCommMonoid R] [Module S R] : Module S (Tensor κ R) :=
  inferInstanceAs <| Module S ((∀ i, κ i) → R)

/-- Every entry of the zero tensor is $0$. -/
@[simp]
theorem zero_apply [AddCommMonoid R] (a : ∀ i, κ i) : (0 : Tensor κ R) a = 0 :=
  rfl

/-- Tensors are added entrywise: $(\mathcal{A} + \mathcal{B})(a) = \mathcal{A}(a) + \mathcal{B}(a)$.
-/
@[simp]
theorem add_apply [AddCommMonoid R] (A B : Tensor κ R) (a : ∀ i, κ i) :
    (A + B) a = A a + B a :=
  rfl

/-- Tensors are negated entrywise: $(-\mathcal{A})(a) = -\mathcal{A}(a)$. -/
@[simp]
theorem neg_apply [AddCommGroup R] (A : Tensor κ R) (a : ∀ i, κ i) : (-A) a = -A a :=
  rfl

/-- Tensors are subtracted entrywise: $(\mathcal{A} - \mathcal{B})(a) = \mathcal{A}(a) -
\mathcal{B}(a)$. -/
@[simp]
theorem sub_apply [AddCommGroup R] (A B : Tensor κ R) (a : ∀ i, κ i) :
    (A - B) a = A a - B a :=
  rfl

/-- Tensors are multiplied by scalars entrywise: $(c \mathcal{A})(a) = c \, \mathcal{A}(a)$. -/
@[simp]
theorem smul_apply [SMul S R] (c : S) (A : Tensor κ R) (a : ∀ i, κ i) : (c • A) a = c • A a :=
  rfl

/-- A finite sum of tensors is taken entrywise: $(\sum_{b \in s} \mathcal{F}_b)(a) = \sum_{b \in s}
\mathcal{F}_b(a)$. -/
@[simp]
theorem sum_apply [AddCommMonoid R] {β : Type*} (s : Finset β) (f : β → Tensor κ R)
    (a : ∀ i, κ i) : (∑ b ∈ s, f b) a = ∑ b ∈ s, f b a :=
  Finset.sum_apply a s f

/-! ### The Frobenius inner product -/

section Inner

variable {𝕜 : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)]

/-- The **Frobenius inner product** of tensors over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ is
$\langle \mathcal{A}, \mathcal{B} \rangle = \sum_a \overline{\mathcal{A}(a)} \mathcal{B}(a)$. -/
instance : Inner 𝕜 (Tensor κ 𝕜) :=
  ⟨fun A B => ∑ a, conj (A a) * B a⟩

/-- The Frobenius inner product is $\langle \mathcal{A}, \mathcal{B} \rangle = \sum_a
\overline{\mathcal{A}(a)} \mathcal{B}(a)$. -/
theorem inner_def (A B : Tensor κ 𝕜) : ⟪A, B⟫_𝕜 = ∑ a, conj (A a) * B a :=
  rfl

/-- The Frobenius inner product $\langle \mathcal{A}, \mathcal{B} \rangle$ is the dot product of the
conjugate of the array of entries of $\mathcal{A}$ with the array of entries of $\mathcal{B}$. -/
theorem inner_eq_star_dotProduct (A B : Tensor κ 𝕜) :
    ⟪A, B⟫_𝕜 = dotProduct (star (of.symm A)) (of.symm B) :=
  rfl

/-- The Frobenius inner product of two tensors is the Euclidean inner product of their arrays of
entries. -/
theorem inner_eq_inner_toLp (A B : Tensor κ 𝕜) :
    ⟪A, B⟫_𝕜 = ⟪WithLp.toLp 2 (of.symm A), WithLp.toLp 2 (of.symm B)⟫_𝕜 := by
  simp [inner_def, PiLp.inner_apply, mul_comm]

instance : InnerProductSpace.Core 𝕜 (Tensor κ 𝕜) where
  toInner := inferInstance
  conj_inner_symm A B := by
    simp only [inner_eq_inner_toLp]
    exact inner_conj_symm _ _
  re_inner_nonneg A := by
    rw [inner_eq_inner_toLp]
    exact inner_self_nonneg
  add_left A B C := by
    simp only [inner_eq_inner_toLp]
    exact inner_add_left _ _ _
  smul_left A B r := by
    simp only [inner_eq_inner_toLp]
    exact inner_smul_left _ _ _
  definite A h := by
    rw [inner_eq_inner_toLp, inner_self_eq_zero] at h
    exact of.symm.injective (WithLp.toLp_injective 2 h)

/-- The Frobenius norm on tensors ([golub2013matrix], §12.4.2), the norm of the Frobenius inner
product. -/
noncomputable instance : NormedAddCommGroup (Tensor κ 𝕜) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := 𝕜)

/-- The inner product space structure on tensors given by the Frobenius inner product. -/
noncomputable instance : InnerProductSpace 𝕜 (Tensor κ 𝕜) :=
  InnerProductSpace.ofCore _

/-- The Frobenius norm of a tensor is the Euclidean norm of its array of entries. -/
theorem norm_toLp (A : Tensor κ 𝕜) : ‖WithLp.toLp 2 (of.symm A)‖ = ‖A‖ := by
  rw [@norm_eq_sqrt_re_inner 𝕜, @norm_eq_sqrt_re_inner 𝕜 (Tensor κ 𝕜), inner_eq_inner_toLp]

/-- The **Frobenius norm** of tensors ([golub2013matrix], §12.4.2). Let $\mathbb{K}$ be $\mathbb{R}$
or $\mathbb{C}$, let $\iota$ and all $\kappa_i$ be finite, and let $\mathcal{A}$ be a tensor
over $\mathbb{K}$. Then
$$\|\mathcal{A}\| = \Bigl(\sum_a |\mathcal{A}(a)|^2\Bigr)^{1/2}.$$
-/
theorem frobenius_norm_def (A : Tensor κ 𝕜) : ‖A‖ = √(∑ a, ‖A a‖ ^ 2) := by
  rw [← norm_toLp, EuclideanSpace.norm_eq]
  rfl

/-- The square of the Frobenius norm is the sum of the squares of the absolute values of the
entries: $\|\mathcal{A}\|^2 = \sum_a |\mathcal{A}(a)|^2$. -/
theorem frobenius_norm_sq (A : Tensor κ 𝕜) : ‖A‖ ^ 2 = ∑ a, ‖A a‖ ^ 2 := by
  rw [frobenius_norm_def, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

/-- A tensor as a Euclidean vector: the linear isometry equivalence of the tensors with the
Frobenius norm with `EuclideanSpace 𝕜 (∀ i, κ i)`, which keeps the entries. -/
noncomputable def toEuclidean : Tensor κ 𝕜 ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (∀ i, κ i) where
  toFun A := WithLp.toLp 2 (of.symm A)
  invFun x := of x.ofLp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' := norm_toLp

/-- `Tensor.toEuclidean` keeps the entries: the entry of `Tensor.toEuclidean A` at $a$ is
$\mathcal{A}(a)$. -/
@[simp]
theorem toEuclidean_apply (A : Tensor κ 𝕜) (a : ∀ i, κ i) : toEuclidean A a = A a :=
  rfl

/-- The inverse of `Tensor.toEuclidean` keeps the entries: the entry of `Tensor.toEuclidean.symm x`
at $a$ is $x_a$. -/
@[simp]
theorem toEuclidean_symm_apply (x : EuclideanSpace 𝕜 (∀ i, κ i)) (a : ∀ i, κ i) :
    toEuclidean.symm x a = x a :=
  rfl

end Inner

/-! ### Rank-one tensors and outer products -/

section RankOne

variable [Fintype ι]

/-- The **rank-one tensor** $z_1 \circ \cdots \circ z_d$ of vectors $z_i \in R^{\kappa_i}$
([golub2013matrix], §12.4.8) is the tensor with the entries
$$(z_1 \circ \cdots \circ z_d)(a) = \prod_i z_i(a_i).$$

The set of modes $\iota$ is finite, and $R$ is a commutative monoid. -/
def rankOne [CommMonoid R] (z : ∀ i, κ i → R) : Tensor κ R :=
  of fun a => ∏ i, z i (a i)

/-- The entries of a rank-one tensor are $(z_1 \circ \cdots \circ z_d)(a) = \prod_i z_i(a_i)$. -/
@[simp]
theorem rankOne_apply [CommMonoid R] (z : ∀ i, κ i → R) (a : ∀ i, κ i) :
    rankOne z a = ∏ i, z i (a i) :=
  rfl

/-- Rescaling the vectors of a rank-one tensor rescales the tensor by the product of the factors:
$(c_1 z_1) \circ \cdots \circ (c_d z_d) = (\prod_i c_i) \, z_1 \circ \cdots \circ z_d$. -/
theorem rankOne_smul [CommMonoid R] (c : ι → R) (z : ∀ i, κ i → R) :
    (rankOne fun i => c i • z i) = (∏ i, c i) • rankOne z := by
  ext a
  simp [rankOne_apply, Finset.prod_mul_distrib, smul_apply]

/-- A tensor is **rank-one** if it is a rank-one tensor $z_1 \circ \cdots \circ z_d$ for some
vectors $z_i$ ([golub2013matrix], §12.4.8). -/
def IsRankOne [CommMonoid R] (A : Tensor κ R) : Prop :=
  ∃ z : ∀ i, κ i → R, A = rankOne z

/-- A rank-one tensor $z_1 \circ \cdots \circ z_d$ is rank-one. -/
theorem isRankOne_rankOne [CommMonoid R] (z : ∀ i, κ i → R) : (rankOne z).IsRankOne :=
  ⟨z, rfl⟩

/-- Replacing the factor $z_k$ by $x$ in the product $\prod_i z_i(a_i)$ gives
$x(a_k) \prod_{i \neq k} z_i(a_i)$. -/
private theorem prod_update_apply [DecidableEq ι] [CommMonoid R] (z : ∀ i, κ i → R) (k : ι)
    (x : κ k → R) (a : ∀ i, κ i) :
    ∏ i, Function.update z k x i (a i) = x (a k) * ∏ i ∈ Finset.univ \ {k}, z i (a i) := by
  have h : ∀ i, Function.update z k x i (a i)
      = Function.update (fun i => z i (a i)) k (x (a k)) i :=
    fun i => Function.apply_update (fun i (g : κ i → R) => g (a i)) z k x i
  simp only [h]
  exact Finset.prod_update_of_mem (Finset.mem_univ k) _ _

/-- A rank-one tensor is additive in each factor: replacing $z_k$ by $x + y$ gives the sum of the
rank-one tensors with $z_k$ replaced by $x$ and by $y$. -/
theorem rankOne_update_add [DecidableEq ι] [CommSemiring R] (z : ∀ i, κ i → R) (k : ι)
    (x y : κ k → R) :
    rankOne (Function.update z k (x + y))
      = rankOne (Function.update z k x) + rankOne (Function.update z k y) := by
  ext a
  simp only [rankOne_apply, add_apply, prod_update_apply, Pi.add_apply, add_mul]

/-- A rank-one tensor is homogeneous in each factor: replacing $z_k$ by $c x$ gives $c$ times the
rank-one tensor with $z_k$ replaced by $x$. -/
theorem rankOne_update_smul [DecidableEq ι] [CommSemiring R] (z : ∀ i, κ i → R) (k : ι) (c : R)
    (x : κ k → R) :
    rankOne (Function.update z k (c • x)) = c • rankOne (Function.update z k x) := by
  ext a
  simp only [rankOne_apply, smul_apply, prod_update_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- The rank-one tensor $z_1 \circ \cdots \circ z_d$, as a multilinear map of the vectors
$z_1, \dots, z_d$. -/
def rankOneMultilinearMap [CommSemiring R] : MultilinearMap R (fun i => κ i → R) (Tensor κ R) where
  toFun := rankOne
  map_update_add' z k x y := rankOne_update_add z k x y
  map_update_smul' z k c x := rankOne_update_smul z k c x

/-- The multilinear map `Tensor.rankOneMultilinearMap` sends $(z_i)_i$ to
$z_1 \circ \cdots \circ z_d$. -/
@[simp]
theorem rankOneMultilinearMap_apply [CommSemiring R] (z : ∀ i, κ i → R) :
    rankOneMultilinearMap z = rankOne z :=
  rfl

variable [DecidableEq ι] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- Let $R$ be a commutative semiring, and let $\iota$ and all $\kappa_i$ be finite. Every tensor is
the sum of its entries times the rank-one tensors of standard basis vectors ([golub2013matrix],
§12.4.8):
$$\mathcal{A} = \sum_a \mathcal{A}(a) \, e_{a_1} \circ \cdots \circ e_{a_d},$$
where $e_{a_i} \in R^{\kappa_i}$ is the standard basis vector $I(:, a_i)$. -/
theorem eq_sum_rankOne_single [CommSemiring R] (A : Tensor κ R) :
    A = ∑ a, A a • rankOne (κ := κ) (fun i => (Pi.single (a i) (1 : R) : κ i → R)) := by
  ext b
  rw [sum_apply, Finset.sum_eq_single b (fun a _ hab => ?_) (by simp)]
  · simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 (Ne.symm hab)
    rw [smul_apply, rankOne_apply, Finset.prod_eq_zero (Finset.mem_univ i)
      (Pi.single_eq_of_ne hi 1), smul_zero]

end RankOne

section Outer

variable {ι₁ ι₂ ι₃ : Type*} {κ₁ : ι₁ → Type v} {κ₂ : ι₂ → Type v} {κ₃ : ι₃ → Type v}

/-- The **outer product** of tensors $\mathcal{B}$ with modes $\iota_1$ and $\mathcal{C}$ with modes
$\iota_2$ ([golub2013matrix], §12.4.7) is the tensor $\mathcal{B} \circ \mathcal{C}$ with modes
$\iota_1 \sqcup \iota_2$ and the entries
$$(\mathcal{B} \circ \mathcal{C})(i, j) = \mathcal{B}(i) \, \mathcal{C}(j).$$
-/
def outer [Mul R] (B : Tensor κ₁ R) (C : Tensor κ₂ R) : Tensor (Sum.elim κ₁ κ₂) R :=
  of fun a => B (fun i => a (.inl i)) * C (fun j => a (.inr j))

/-- The entries of the outer product are $(\mathcal{B} \circ \mathcal{C})(i, j) = \mathcal{B}(i) \,
\mathcal{C}(j)$. -/
@[simp]
theorem outer_apply [Mul R] (B : Tensor κ₁ R) (C : Tensor κ₂ R) (a : ∀ i, Sum.elim κ₁ κ₂ i) :
    outer B C a = B (fun i => a (.inl i)) * C (fun j => a (.inr j)) :=
  rfl

/-- The outer product is associative entrywise: $((\mathcal{A} \circ \mathcal{B}) \circ
\mathcal{C})(x, y, z) = (\mathcal{A} \circ (\mathcal{B} \circ \mathcal{C}))(x, y, z)$. The two
tensors have the modes $(\iota_1 \sqcup \iota_2) \sqcup \iota_3$ and
$\iota_1 \sqcup (\iota_2 \sqcup \iota_3)$. -/
theorem outer_outer_apply [Semigroup R] (A : Tensor κ₁ R) (B : Tensor κ₂ R) (C : Tensor κ₃ R)
    (x : ∀ i, κ₁ i) (y : ∀ i, κ₂ i) (z : ∀ i, κ₃ i) :
    outer (outer A B) C (Sum.rec (Sum.rec x y) z)
      = outer A (outer B C) (Sum.rec x (Sum.rec y z)) :=
  mul_assoc _ _ _

/-- A rank-one tensor with modes $\iota_1 \sqcup \iota_2$ is the outer product of the rank-one
tensors of its vectors on $\iota_1$ and on $\iota_2$. -/
theorem rankOne_eq_outer [CommMonoid R] [Fintype ι₁] [Fintype ι₂]
    (z : ∀ i, Sum.elim κ₁ κ₂ i → R) :
    rankOne z = outer (rankOne fun i => z (.inl i)) (rankOne fun j => z (.inr j)) := by
  ext a
  exact Fintype.prod_sum_type fun i => z i (a i)

end Outer

/-! ### Subtensors and transposition -/

section Restrict

variable (p : ι → Prop) [DecidablePred p]

/-- The **subtensor** of $\mathcal{A}$ obtained by fixing the indices of the modes outside a set $p$
to $c$ ([golub2013matrix], §12.4.2). It has the modes in $p$, and its entry at $r$ is the entry
of $\mathcal{A}$ at the tuple that agrees with $r$ on $p$ and with $c$ outside $p$.

A fiber is `Tensor.restrict (· = k)`, and a slice is `Tensor.restrict (· ∈ {k, l})`. -/
def restrict (c : ∀ i : {i // ¬p i}, κ i) (A : Tensor κ R) : Tensor (fun i : {i // p i} => κ i) R :=
  of fun r => A ((Equiv.piEquivPiSubtypeProd p κ).symm (r, c))

/-- The entries of a subtensor are entries of the tensor: the subtensor with the indices $a_i$ fixed
outside $p$ has the entry $\mathcal{A}(a)$ at the restriction of $a$ to $p$. -/
@[simp]
theorem restrict_apply (A : Tensor κ R) (a : ∀ i, κ i) :
    restrict p (fun i => a i) A (fun i => a i) = A a :=
  congrArg A ((Equiv.piEquivPiSubtypeProd p κ).symm_apply_apply a)

end Restrict

section Permute

variable {ι' : Type u'} {ι'' : Type*}

/-- The **transposition** of a tensor ([golub2013matrix], §12.4.4). For a bijection of modes
$\sigma \colon \iota' \to \iota$, the tensor $\mathcal{A}^{\langle \sigma \rangle}$ has the
modes $\iota'$, with index type $\kappa_{\sigma(k)}$ at mode $k$, and
$$\mathcal{A}^{\langle \sigma \rangle}(a \circ \sigma) = \mathcal{A}(a).$$
-/
def permute (σ : ι' ≃ ι) (A : Tensor κ R) : Tensor (κ ∘ σ) R :=
  of fun b => A (Equiv.piCongrLeft κ σ b)

/-- The entry relation of transposition, $\mathcal{A}^{\langle p \rangle}(j(p)) = \mathcal{A}(j)$ in
[golub2013matrix]: the entry of `Tensor.permute σ A` at $k \mapsto a_{\sigma(k)}$ is
$\mathcal{A}(a)$. -/
@[simp]
theorem permute_apply (σ : ι' ≃ ι) (A : Tensor κ R) (a : ∀ i, κ i) :
    permute σ A (fun k => a (σ k)) = A a := by
  have h : (fun k => a (σ k)) = (Equiv.piCongrLeft κ σ).symm a := by
    funext k
    rw [Equiv.piCongrLeft_symm_apply]
  rw [h, permute, of_apply, Equiv.apply_symm_apply]

/-- Transposition along the identity is the identity. -/
@[simp]
theorem permute_refl (A : Tensor κ R) : permute (Equiv.refl ι) A = A :=
  ext fun a => permute_apply (Equiv.refl ι) A a

/-- Transpositions compose ([golub2013matrix], P12.4.10): transposing along $\tau$ and then along
$\sigma$ is transposing along $\tau \circ \sigma$. -/
theorem permute_trans (σ : ι'' ≃ ι') (τ : ι' ≃ ι) (A : Tensor κ R) :
    permute (σ.trans τ) A = permute σ (permute τ A) := by
  ext b
  obtain ⟨a, rfl⟩ := (Equiv.piCongrLeft κ (σ.trans τ)).symm.surjective b
  have h : (Equiv.piCongrLeft κ (σ.trans τ)).symm a = fun k => a (τ (σ k)) := by
    funext k
    rw [Equiv.piCongrLeft_symm_apply]
    rfl
  rw [h]
  exact (permute_apply (σ.trans τ) A a).trans
    ((permute_apply τ A a).symm.trans (permute_apply σ (permute τ A) fun k => a (τ k)).symm)

variable {𝕜 : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)]
  [Fintype ι'] [DecidableEq ι']

/-- Transposition preserves the Frobenius norm: $\|\mathcal{A}^{\langle \sigma \rangle}\| =
\|\mathcal{A}\|$. -/
theorem frobenius_norm_permute (σ : ι' ≃ ι) (A : Tensor κ 𝕜) : ‖permute σ A‖ = ‖A‖ := by
  rw [frobenius_norm_def, frobenius_norm_def]
  congr 1
  exact Equiv.sum_comp (Equiv.piCongrLeft κ σ) fun a => ‖A a‖ ^ 2

end Permute

/-! ### Matrices as order-2 tensors, and symmetric tensors -/

section Matrix

variable {κ : Fin 2 → Type v}

/-- A matrix $M$ as an order-2 tensor, with the entries $M(a_0, a_1)$. This is a linear equivalence
between the matrices with rows indexed by $\kappa_0$ and columns indexed by $\kappa_1$ and the
order-2 tensors with these index types.

For a rectangular matrix `M : Matrix m n R`, the index types are `![m, n]`. For a square matrix,
they are `fun _ => n`. -/
def ofMatrix [Semiring R] : Matrix (κ 0) (κ 1) R ≃ₗ[R] Tensor κ R where
  toFun M := of fun a => M (a 0) (a 1)
  invFun A := Matrix.of fun i j => A ((piFinTwoEquiv κ).symm (i, j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv A := ext fun a => congrArg A ((piFinTwoEquiv κ).symm_apply_apply a)

/-- The entries of `Tensor.ofMatrix M` are the entries of $M$: the entry at $a$ is $M(a_0, a_1)$. -/
@[simp]
theorem ofMatrix_apply [Semiring R] (M : Matrix (κ 0) (κ 1) R) (a : ∀ i, κ i) :
    ofMatrix M a = M (a 0) (a 1) :=
  rfl

open scoped Matrix.Norms.Frobenius in
/-- The Frobenius norm of a matrix is the Frobenius norm of the corresponding order-2 tensor. -/
theorem norm_ofMatrix {𝕜 : Type*} [RCLike 𝕜] [∀ i, Fintype (κ i)]
    (M : Matrix (κ 0) (κ 1) 𝕜) : ‖ofMatrix M‖ = ‖M‖ := by
  rw [frobenius_norm_def, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  simp_rw [Real.rpow_two, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (piFinTwoEquiv κ) _ _ fun a => rfl

variable {ν : Type v}

/-- A tensor whose modes all have the same index type is **symmetric** if its entries are invariant
under every permutation of the modes ([golub2013matrix], §12.5.7):
$\mathcal{A}(a \circ \sigma) = \mathcal{A}(a)$ for every permutation $\sigma$ of $\iota$ and
every tuple $a$. -/
def IsSymm (A : Tensor (fun _ : ι => ν) R) : Prop :=
  ∀ (σ : Equiv.Perm ι) (a : ι → ν), A (a ∘ σ) = A a

/-- An order-2 tensor `Tensor.ofMatrix M` is symmetric if and only if the square matrix $M$ is
symmetric. -/
theorem isSymm_ofMatrix [Semiring R] (M : Matrix ν ν R) :
    (ofMatrix (κ := fun _ => ν) M).IsSymm ↔ M.IsSymm := by
  constructor
  · intro h
    refine Matrix.IsSymm.ext fun i j => ?_
    simpa using h (Equiv.swap 0 1) ![i, j]
  · intro h σ a
    have h01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
    have hfin : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
    simp only [ofMatrix_apply, Function.comp_apply]
    rcases hfin (σ 0) with h0 | h0 <;> rcases hfin (σ 1) with h1 | h1
    · exact absurd (h0.trans h1.symm) h01
    · rw [h0, h1]
    · rw [h0, h1]
      exact h.apply _ _
    · exact absurd (h0.trans h1.symm) h01

end Matrix

/-! ### Vectorization of tensors of shape $n_1 \times \cdots \times n_d$ -/

section VecFin

variable {d : ℕ}

/-- The **vectorization** $\operatorname{vec}(\mathcal{A})$ of a tensor $\mathcal{A} \in R^{n_1
\times \cdots \times n_d}$ ([golub2013matrix], (12.4.4)–(12.4.5)). It is the vector of length
$n_1 \cdots n_d$ that has the entry $\mathcal{A}(i)$ at the position
$$\operatorname{col}(i, n) - 1 = \sum_k i_k \prod_{j < k} n_j,$$
with 0-based indices.

The position map is Mathlib's little-endian equivalence `finPiFinEquiv`. -/
def vecFin {n : Fin d → ℕ} (A : Tensor (fun k : Fin d => Fin (n k)) R) : Fin (∏ k, n k) → R :=
  fun t => A (finPiFinEquiv.symm t)

/-- Equation (12.4.5) of [golub2013matrix]: $\operatorname{vec}(\mathcal{A})(\operatorname{col}(i,
n)) = \mathcal{A}(i)$. -/
@[simp]
theorem vecFin_apply {n : Fin d → ℕ} (A : Tensor (fun k : Fin d => Fin (n k)) R)
    (i : ∀ k, Fin (n k)) : vecFin A (finPiFinEquiv i) = A i := by
  simp [vecFin]

/-- Let $\mathcal{A} \in R^{n_1 \times \cdots \times n_{d+1}}$, and let $N = n_1 \cdots n_d$. The
vectorization of $\mathcal{A}$ stacks the vectorizations of the slices of $\mathcal{A}$ along
the last mode ([golub2013matrix], (12.4.2)–(12.4.3)): for each index $x$ of the last mode and
each $0 \le t < N$,
$$\operatorname{vec}(\mathcal{A})(xN + t) = \operatorname{vec}(\mathcal{A}(:, \dots, :,
  x))(t).$$

The position $xN + t$ is `finProdFinEquiv (x, t)`, cast to the length $\prod_k n_k$. -/
theorem vecFin_snoc {n : Fin (d + 1) → ℕ} (A : Tensor (fun k => Fin (n k)) R)
    (x : Fin (n (Fin.last d))) (t : Fin (∏ k : Fin d, n k.castSucc)) :
    vecFin A (Fin.cast (by rw [Fin.prod_univ_castSucc, mul_comm]) (finProdFinEquiv (x, t)))
      = vecFin (of fun i => A (Fin.snoc (α := fun k => Fin (n k)) i x) :
          Tensor (fun k : Fin d => Fin (n k.castSucc)) R) t := by
  obtain ⟨i, rfl⟩ := finPiFinEquiv.surjective t
  have h : Fin.cast (by rw [Fin.prod_univ_castSucc, mul_comm])
      (finProdFinEquiv (x, finPiFinEquiv i))
        = finPiFinEquiv (Fin.snoc (α := fun k => Fin (n k)) i x) := by
    ext
    rw [Fin.val_cast, finProdFinEquiv_apply_val, finPiFinEquiv_snoc, mul_comm]
  rw [h, vecFin_apply, vecFin_apply, of_apply]

/-- For an order-2 tensor, `Tensor.vecFin` is the column stacking `Matrix.vecFin` of the matrix, up
to the identification of the lengths $mn = nm$. -/
theorem vecFin_ofMatrix [Semiring R] {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) :
    vecFin (ofMatrix (κ := fun k : Fin 2 => Fin (![m, n] k)) M)
      = Matrix.vecFin M ∘ Fin.cast (by simp [Fin.prod_univ_two, mul_comm]) := by
  funext t
  obtain ⟨a, rfl⟩ := finPiFinEquiv.surjective t
  have h : Fin.cast (by simp [Fin.prod_univ_two, mul_comm]) (finPiFinEquiv a)
      = finProdFinEquiv (a 1, a 0) := by
    ext
    rw [Fin.val_cast, finPiFinEquiv_apply, finProdFinEquiv_apply_val, Fin.sum_univ_two]
    simp
    ring
  rw [vecFin_apply, Function.comp_apply]
  exact ((congrArg (Matrix.vecFin M) h).trans (Matrix.vecFin_apply M (a 1) (a 0))).symm

end VecFin

/-! ### The bridge to `PiTensorProduct` -/

section PiTensorProduct

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)] [CommRing R]

/-- Let $R$ be a commutative ring, and let $\iota$ and all $\kappa_i$ be finite. The tensors with
mode index types $\kappa_i$ are linearly equivalent to Mathlib's abstract tensor product
$\bigotimes_i R^{\kappa_i}$ (`PiTensorProduct`).

The equivalence sends a rank-one tensor to the corresponding elementary tensor; see
`Tensor.equivPiTensorProduct_rankOne`. -/
noncomputable def equivPiTensorProduct : Tensor κ R ≃ₗ[R] ⨂[R] i, (κ i → R) := by
  classical
  exact (Finsupp.linearEquivFunOnFinite R R (∀ i, κ i)).symm ≪≫ₗ
    PiTensorProduct.ofFinsuppEquiv'.symm ≪≫ₗ
    PiTensorProduct.congr fun i => Finsupp.linearEquivFunOnFinite R R (κ i)

/-- The equivalence `Tensor.equivPiTensorProduct` sends the rank-one tensor
$z_1 \circ \cdots \circ z_d$ to the elementary tensor $\bigotimes_i z_i$. -/
theorem equivPiTensorProduct_rankOne (z : ∀ i, κ i → R) :
    equivPiTensorProduct (rankOne z) = ⨂ₜ[R] i, z i := by
  classical
  refine (LinearEquiv.eq_symm_apply _).1 ?_
  ext a
  simp only [equivPiTensorProduct, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    PiTensorProduct.congr_symm_tprod]
  exact (PiTensorProduct.ofFinsuppEquiv'_apply_apply (R := R)
    (fun i => (Finsupp.linearEquivFunOnFinite R R (κ i)).symm (z i)) a).symm

end PiTensorProduct

end Tensor
