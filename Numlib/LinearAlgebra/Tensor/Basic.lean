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

A tensor with modes `ι` and mode index types `κ i` is an array of entries indexed by the tuples
`a : ∀ i, κ i`:

`def Tensor (κ : ι → Type*) (R : Type*) := (∀ i, κ i) → R`.

It is a `def`, as `Matrix` is, so that instance search sees no `Pi` structure beyond the algebraic
one given here: in particular the norm of a tensor over `𝕜` is the Frobenius norm
`‖A‖ = √(∑ a, ‖A a‖ ²)`, coming from a global inner product space structure
`⟪A, B⟫ = ∑ a, conj (A a) * B a`, and not the sup norm of `Pi`. An order-`d` tensor
`𝒜 ∈ ℝ^{n₁ × ⋯ × n_d}` of [golub2013matrix] §12.4 is a `Tensor (fun k : Fin d => Fin (n k)) ℝ`.

Mathlib's abstract tensor product `⨂[R] i, (κ i → R)` (`PiTensorProduct`) is a quotient with no
entries, while numerical statements are about entries, unfoldings and index orderings; the two
meet at `Tensor.equivPiTensorProduct`, which sends the rank-one tensor `Tensor.rankOne z` to
`⨂ₜ i, z i`.

## Main definitions

* `Tensor κ R`, `Tensor.of`, and the Frobenius inner product space structure with the isometry
  `Tensor.toEuclidean` onto `EuclideanSpace 𝕜 (∀ i, κ i)`.
* `Tensor.rankOne z`: the elementary tensor `z₁ ∘ ⋯ ∘ z_d`; `Tensor.IsRankOne`.
* `Tensor.outer`: the outer product of two tensors, on the disjoint union of their modes.
* `Tensor.restrict`: the subtensor obtained by fixing the modes outside a predicate (fibers,
  slices).
* `Tensor.permute`: transposition of modes.
* `Tensor.ofMatrix`: a matrix as an order-2 tensor.
* `Tensor.IsSymm`: symmetric tensors.
* `Tensor.vecFin`: the column-ordered vectorization of a `Fin`-shaped tensor, through Mathlib's
  little-endian `finPiFinEquiv` (the book's `col(i, n)`).
* `Tensor.equivPiTensorProduct`: the bridge to `PiTensorProduct`.

## Main statements

* `Tensor.frobenius_norm_def`: `‖A‖ = √(∑ a, ‖A a‖ ^ 2)`.
* `Tensor.eq_sum_rankOne_single`: every tensor is a sum of rank-one tensors.
* `Tensor.vecFin_snoc`: the vectorization of an order-`(d + 1)` tensor stacks those of its
  last-mode slices.

## References

* [golub2013matrix], §12.4–12.5.
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

/-- A tensor with modes `ι` and mode index types `κ i`: an array `(∀ i, κ i) → R` of entries
indexed by the tuples of indices. The book's order-`d` tensor `𝒜 ∈ ℝ^{n₁ × ⋯ × n_d}`
([golub2013matrix] §12.4) is `Tensor (fun k : Fin d => Fin (n k)) ℝ`, its entry `𝒜(i)` is `A i`. -/
def Tensor {ι : Type u} (κ : ι → Type v) (R : Type w) : Type max u v w :=
  (∀ i, κ i) → R

namespace Tensor

variable {ι : Type u} {κ : ι → Type v} {R : Type w} {S : Type*}

/-- The identification of arrays of entries with tensors. -/
def of : ((∀ i, κ i) → R) ≃ Tensor κ R :=
  Equiv.refl _

@[simp]
theorem of_apply (f : (∀ i, κ i) → R) (a : ∀ i, κ i) : of f a = f a :=
  rfl

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

@[simp]
theorem zero_apply [AddCommMonoid R] (a : ∀ i, κ i) : (0 : Tensor κ R) a = 0 :=
  rfl

@[simp]
theorem add_apply [AddCommMonoid R] (A B : Tensor κ R) (a : ∀ i, κ i) :
    (A + B) a = A a + B a :=
  rfl

@[simp]
theorem neg_apply [AddCommGroup R] (A : Tensor κ R) (a : ∀ i, κ i) : (-A) a = -A a :=
  rfl

@[simp]
theorem sub_apply [AddCommGroup R] (A B : Tensor κ R) (a : ∀ i, κ i) :
    (A - B) a = A a - B a :=
  rfl

@[simp]
theorem smul_apply [SMul S R] (c : S) (A : Tensor κ R) (a : ∀ i, κ i) : (c • A) a = c • A a :=
  rfl

@[simp]
theorem sum_apply [AddCommMonoid R] {β : Type*} (s : Finset β) (f : β → Tensor κ R)
    (a : ∀ i, κ i) : (∑ b ∈ s, f b) a = ∑ b ∈ s, f b a :=
  Finset.sum_apply a s f

/-! ### The Frobenius inner product -/

section Inner

variable {𝕜 : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)]

/-- The Frobenius inner product `⟪A, B⟫ = ∑ a, conj (A a) * B a`. -/
instance : Inner 𝕜 (Tensor κ 𝕜) :=
  ⟨fun A B => ∑ a, conj (A a) * B a⟩

theorem inner_def (A B : Tensor κ 𝕜) : ⟪A, B⟫_𝕜 = ∑ a, conj (A a) * B a :=
  rfl

/-- The Frobenius inner product is the Euclidean inner product of the arrays of entries. -/
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

/-- The Frobenius norm on tensors ([golub2013matrix] §12.4.2). -/
noncomputable instance : NormedAddCommGroup (Tensor κ 𝕜) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := 𝕜)

/-- The Frobenius inner product space structure on tensors. -/
noncomputable instance : InnerProductSpace 𝕜 (Tensor κ 𝕜) :=
  InnerProductSpace.ofCore _

/-- The Frobenius norm is the Euclidean norm of the array of entries. -/
theorem norm_toLp (A : Tensor κ 𝕜) : ‖WithLp.toLp 2 (of.symm A)‖ = ‖A‖ := by
  rw [@norm_eq_sqrt_re_inner 𝕜, @norm_eq_sqrt_re_inner 𝕜 (Tensor κ 𝕜), inner_eq_inner_toLp]

/-- The Frobenius norm ([golub2013matrix] §12.4.2): `‖A‖ = √(∑ a, ‖A a‖ ^ 2)`. -/
theorem frobenius_norm_def (A : Tensor κ 𝕜) : ‖A‖ = √(∑ a, ‖A a‖ ^ 2) := by
  rw [← norm_toLp, EuclideanSpace.norm_eq]
  rfl

/-- The square of the Frobenius norm is the sum of the squares of the entries. -/
theorem frobenius_norm_sq (A : Tensor κ 𝕜) : ‖A‖ ^ 2 = ∑ a, ‖A a‖ ^ 2 := by
  rw [frobenius_norm_def, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

/-- A tensor as a Euclidean vector: the linear isometry equivalence with
`EuclideanSpace 𝕜 (∀ i, κ i)`. -/
noncomputable def toEuclidean : Tensor κ 𝕜 ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (∀ i, κ i) where
  toFun A := WithLp.toLp 2 (of.symm A)
  invFun x := of x.ofLp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' := norm_toLp

@[simp]
theorem toEuclidean_apply (A : Tensor κ 𝕜) (a : ∀ i, κ i) : toEuclidean A a = A a :=
  rfl

@[simp]
theorem toEuclidean_symm_apply (x : EuclideanSpace 𝕜 (∀ i, κ i)) (a : ∀ i, κ i) :
    toEuclidean.symm x a = x a :=
  rfl

end Inner

/-! ### Rank-one tensors and outer products -/

section RankOne

variable [Fintype ι]

/-- The rank-one (elementary) tensor `z₁ ∘ ⋯ ∘ z_d` ([golub2013matrix] §12.4.8):
`rankOne z a = ∏ i, z i (a i)`. -/
def rankOne [CommMonoid R] (z : ∀ i, κ i → R) : Tensor κ R :=
  of fun a => ∏ i, z i (a i)

@[simp]
theorem rankOne_apply [CommMonoid R] (z : ∀ i, κ i → R) (a : ∀ i, κ i) :
    rankOne z a = ∏ i, z i (a i) :=
  rfl

/-- A tensor is rank-one if it is an elementary tensor ([golub2013matrix] §12.4.8). -/
def IsRankOne [CommMonoid R] (A : Tensor κ R) : Prop :=
  ∃ z : ∀ i, κ i → R, A = rankOne z

theorem isRankOne_rankOne [CommMonoid R] (z : ∀ i, κ i → R) : (rankOne z).IsRankOne :=
  ⟨z, rfl⟩

/-- The product defining an entry of a rank-one tensor, with one factor replaced. -/
private theorem prod_update_apply [DecidableEq ι] [CommMonoid R] (z : ∀ i, κ i → R) (k : ι)
    (x : κ k → R) (a : ∀ i, κ i) :
    ∏ i, Function.update z k x i (a i) = x (a k) * ∏ i ∈ Finset.univ \ {k}, z i (a i) := by
  have h : ∀ i, Function.update z k x i (a i)
      = Function.update (fun i => z i (a i)) k (x (a k)) i :=
    fun i => Function.apply_update (fun i (g : κ i → R) => g (a i)) z k x i
  simp only [h]
  exact Finset.prod_update_of_mem (Finset.mem_univ k) _ _

/-- A rank-one tensor is additive in each factor. -/
theorem rankOne_update_add [DecidableEq ι] [CommSemiring R] (z : ∀ i, κ i → R) (k : ι)
    (x y : κ k → R) :
    rankOne (Function.update z k (x + y))
      = rankOne (Function.update z k x) + rankOne (Function.update z k y) := by
  ext a
  simp only [rankOne_apply, add_apply, prod_update_apply, Pi.add_apply, add_mul]

/-- A rank-one tensor is homogeneous in each factor. -/
theorem rankOne_update_smul [DecidableEq ι] [CommSemiring R] (z : ∀ i, κ i → R) (k : ι) (c : R)
    (x : κ k → R) :
    rankOne (Function.update z k (c • x)) = c • rankOne (Function.update z k x) := by
  ext a
  simp only [rankOne_apply, smul_apply, prod_update_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- The rank-one tensor as a multilinear map of its factors. -/
def rankOneMultilinearMap [CommSemiring R] : MultilinearMap R (fun i => κ i → R) (Tensor κ R) where
  toFun := rankOne
  map_update_add' z k x y := rankOne_update_add z k x y
  map_update_smul' z k c x := rankOne_update_smul z k c x

@[simp]
theorem rankOneMultilinearMap_apply [CommSemiring R] (z : ∀ i, κ i → R) :
    rankOneMultilinearMap z = rankOne z :=
  rfl

variable [DecidableEq ι] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- Every tensor is a sum of rank-one tensors along the standard basis ([golub2013matrix] §12.4.8,
`𝒜 = ∑_i 𝒜(i) I(:, i₁) ∘ ⋯ ∘ I(:, i_d)`). -/
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

/-- The outer product of two tensors ([golub2013matrix] §12.4.7, `𝒜(i, j) = ℬ(i) 𝒞(j)`), on the
disjoint union of their modes. -/
def outer [Mul R] (B : Tensor κ₁ R) (C : Tensor κ₂ R) : Tensor (Sum.elim κ₁ κ₂) R :=
  of fun a => B (fun i => a (.inl i)) * C (fun j => a (.inr j))

@[simp]
theorem outer_apply [Mul R] (B : Tensor κ₁ R) (C : Tensor κ₂ R) (a : ∀ i, Sum.elim κ₁ κ₂ i) :
    outer B C a = B (fun i => a (.inl i)) * C (fun j => a (.inr j)) :=
  rfl

/-- The outer product is associative, entrywise: `((A ∘ B) ∘ C)(x, y, z) = (A ∘ (B ∘ C))(x, y, z)`
(the two tensors live on `(ι₁ ⊕ ι₂) ⊕ ι₃` and `ι₁ ⊕ (ι₂ ⊕ ι₃)`). -/
theorem outer_outer_apply [Semigroup R] (A : Tensor κ₁ R) (B : Tensor κ₂ R) (C : Tensor κ₃ R)
    (x : ∀ i, κ₁ i) (y : ∀ i, κ₂ i) (z : ∀ i, κ₃ i) :
    outer (outer A B) C (Sum.rec (Sum.rec x y) z)
      = outer A (outer B C) (Sum.rec x (Sum.rec y z)) :=
  mul_assoc _ _ _

/-- A rank-one tensor on `ι₁ ⊕ ι₂` is the outer product of its two halves. -/
theorem rankOne_eq_outer [CommMonoid R] [Fintype ι₁] [Fintype ι₂]
    (z : ∀ i, Sum.elim κ₁ κ₂ i → R) :
    rankOne z = outer (rankOne fun i => z (.inl i)) (rankOne fun j => z (.inr j)) := by
  ext a
  exact Fintype.prod_sum_type fun i => z i (a i)

end Outer

/-! ### Subtensors and transposition -/

section Restrict

variable (p : ι → Prop) [DecidablePred p]

/-- The subtensor obtained by fixing the modes outside `p` to the indices `c` ([golub2013matrix]
§12.4.2): a fiber is `restrict (· = k)`, a slice `restrict (· ∈ {k, l})`. -/
def restrict (c : ∀ i : {i // ¬p i}, κ i) (A : Tensor κ R) : Tensor (fun i : {i // p i} => κ i) R :=
  of fun r => A ((Equiv.piEquivPiSubtypeProd p κ).symm (r, c))

/-- The entries of a subtensor are entries of the tensor. -/
@[simp]
theorem restrict_apply (A : Tensor κ R) (a : ∀ i, κ i) :
    restrict p (fun i => a i) A (fun i => a i) = A a :=
  congrArg A ((Equiv.piEquivPiSubtypeProd p κ).symm_apply_apply a)

end Restrict

section Permute

variable {ι' : Type u'} {ι'' : Type*}

/-- Tensor transposition ([golub2013matrix] §12.4.4): the modes are renamed along `σ : ι' ≃ ι`,
`permute σ A (fun k => a (σ k)) = A a`. -/
def permute (σ : ι' ≃ ι) (A : Tensor κ R) : Tensor (κ ∘ σ) R :=
  of fun b => A (Equiv.piCongrLeft κ σ b)

/-- The book's `𝒜^{<p>}(j(p)) = 𝒜(j)`. -/
@[simp]
theorem permute_apply (σ : ι' ≃ ι) (A : Tensor κ R) (a : ∀ i, κ i) :
    permute σ A (fun k => a (σ k)) = A a := by
  have h : (fun k => a (σ k)) = (Equiv.piCongrLeft κ σ).symm a := by
    funext k
    rw [Equiv.piCongrLeft_symm_apply]
  rw [h, permute, of_apply, Equiv.apply_symm_apply]

@[simp]
theorem permute_refl (A : Tensor κ R) : permute (Equiv.refl ι) A = A :=
  ext fun a => permute_apply (Equiv.refl ι) A a

/-- Transpositions compose ([golub2013matrix] P12.4.10). -/
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

/-- Transposition preserves the Frobenius norm. -/
theorem frobenius_norm_permute (σ : ι' ≃ ι) (A : Tensor κ 𝕜) : ‖permute σ A‖ = ‖A‖ := by
  rw [frobenius_norm_def, frobenius_norm_def]
  congr 1
  exact Equiv.sum_comp (Equiv.piCongrLeft κ σ) fun a => ‖A a‖ ^ 2

end Permute

/-! ### Matrices as order-2 tensors, and symmetric tensors -/

section Matrix

variable {κ : Fin 2 → Type v}

/-- A matrix as an order-2 tensor: `ofMatrix M a = M (a 0) (a 1)`. The mode index types are any
`κ : Fin 2 → Type*`: `![m, n]` for a rectangular `M : Matrix m n R`, `fun _ => n` for a square
one. -/
def ofMatrix [Semiring R] : Matrix (κ 0) (κ 1) R ≃ₗ[R] Tensor κ R where
  toFun M := of fun a => M (a 0) (a 1)
  invFun A := Matrix.of fun i j => A ((piFinTwoEquiv κ).symm (i, j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv A := ext fun a => congrArg A ((piFinTwoEquiv κ).symm_apply_apply a)

@[simp]
theorem ofMatrix_apply [Semiring R] (M : Matrix (κ 0) (κ 1) R) (a : ∀ i, κ i) :
    ofMatrix M a = M (a 0) (a 1) :=
  rfl

open scoped Matrix.Norms.Frobenius in
/-- The Frobenius norms of a matrix and of the corresponding order-2 tensor agree. -/
theorem norm_ofMatrix {𝕜 : Type*} [RCLike 𝕜] [∀ i, Fintype (κ i)]
    (M : Matrix (κ 0) (κ 1) 𝕜) : ‖ofMatrix M‖ = ‖M‖ := by
  rw [frobenius_norm_def, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  simp_rw [Real.rpow_two, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (piFinTwoEquiv κ) _ _ fun a => rfl

variable {ν : Type v}

/-- A tensor all of whose modes have the same index type is symmetric if its entries are invariant
under every permutation of the modes ([golub2013matrix] §12.5.7). -/
def IsSymm (A : Tensor (fun _ : ι => ν) R) : Prop :=
  ∀ (σ : Equiv.Perm ι) (a : ι → ν), A (a ∘ σ) = A a

/-- An order-2 tensor is symmetric iff it is a symmetric matrix. -/
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

/-! ### Vectorization of `Fin`-shaped tensors -/

section VecFin

variable {d : ℕ}

/-- The book's `vec` of a `Fin`-shaped tensor ([golub2013matrix] (12.4.4)–(12.4.5)): entry `i`
sits at position `col(i, n) − 1 = ∑ k, i k * ∏_{j < k} n j` (0-based), Mathlib's little-endian
`finPiFinEquiv`. -/
def vecFin {n : Fin d → ℕ} (A : Tensor (fun k : Fin d => Fin (n k)) R) : Fin (∏ k, n k) → R :=
  fun t => A (finPiFinEquiv.symm t)

/-- [golub2013matrix] (12.4.5): `vec(𝒜)(col(i, n)) = 𝒜(i)`. -/
@[simp]
theorem vecFin_apply {n : Fin d → ℕ} (A : Tensor (fun k : Fin d => Fin (n k)) R)
    (i : ∀ k, Fin (n k)) : vecFin A (finPiFinEquiv i) = A i := by
  simp [vecFin]

/-- The vectorization of an order-`(d + 1)` tensor stacks the vectorizations of its slices along
the last mode ([golub2013matrix] (12.4.2)–(12.4.3)): its block `x` in the positional layout
`finProdFinEquiv` is `vecFin` of the slice `𝒜(:, …, :, x)`. -/
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

/-- For an order-2 tensor, `vecFin` is the column stacking of the matrix
(`Matrix.vecFin`), up to the identification of the sizes `m * n = n * m`. -/
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

/-- Concrete tensors are Mathlib's abstract tensor product `⨂[R] i, (κ i → R)`. -/
noncomputable def equivPiTensorProduct : Tensor κ R ≃ₗ[R] ⨂[R] i, (κ i → R) := by
  classical
  exact (Finsupp.linearEquivFunOnFinite R R (∀ i, κ i)).symm ≪≫ₗ
    PiTensorProduct.ofFinsuppEquiv'.symm ≪≫ₗ
    PiTensorProduct.congr fun i => Finsupp.linearEquivFunOnFinite R R (κ i)

/-- A rank-one tensor is an elementary tensor `⨂ₜ i, z i`. -/
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
