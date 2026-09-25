/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a new `Mathlib.LinearAlgebra.Tensor` directory beside `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.LinearAlgebra.Tensor.Unfolding

/-!
# Variational singular values of tensors

The multilinear form `𝒜(u₁, …, u_d) = ∑_a 𝒜(a) ∏ᵢ uᵢ(aᵢ)` of a tensor and its Rayleigh quotient
`ψ_𝒜(u) = 𝒜(u₁, …, u_d) / ∏ ‖uᵢ‖` ([golub2013matrix] §12.5.6–12.5.7; Lim 2005, Qi 2005). The
critical points of `ψ_𝒜` are characterized by the equations `𝒜_(k) (⊗_{j ≠ k} u_j) = ψ u_k` at
unit vectors, which the book takes as the definition of a tensor singular value
(`Tensor.IsSingularValue`). All modal unfoldings of a symmetric tensor agree
(`Tensor.IsSymm.modeUnfold_eq`).

## Main definitions

* `Tensor.multilinearForm`, `Tensor.multilinearRayleigh`.
* `Tensor.IsSingularValue`.

## Main statements

* `Tensor.multilinearForm_eq_modeUnfold`: the book's `u₁ᵀ 𝒜_(1) (u₃ ⊗ u₂)`, typed.
* `Tensor.IsSymm.modeUnfold_eq`: the modal unfoldings of a symmetric tensor agree.

## References

* [golub2013matrix], §12.5.6–12.5.7.
-/

universe u v w

open Matrix

namespace Tensor

variable {ι : Type u} {κ : ι → Type v} {R : Type w}

section Form

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)] [CommSemiring R]

/-- The multilinear form of a tensor ([golub2013matrix] §12.5.6, the numerator of `ψ_𝒜`):
`𝒜(u₁, …, u_d) = ∑_a 𝒜(a) ∏ᵢ uᵢ(aᵢ)`. -/
def multilinearForm (A : Tensor κ R) (u : ∀ i, κ i → R) : R :=
  ∑ a, A a * ∏ i, u i (a i)

/-- The multilinear form through the mode-`k` unfolding ([golub2013matrix] §12.5.6, the book's
`u₁ᵀ 𝒜_(1) (u₃ ⊗ u₂)` and its two siblings, typed): `𝒜(u) = u_kᵀ 𝒜_(k) (⊗_{j ≠ k} u_j)`. -/
theorem multilinearForm_eq_modeUnfold (A : Tensor κ R) (u : ∀ i, κ i → R) (k : ι) :
    multilinearForm A u
      = u k ⬝ᵥ (A.modeUnfold k *ᵥ rankOne fun j : {j // j ≠ k} => u j) := by
  rw [multilinearForm, ← (Equiv.piSplitAt k κ).symm.sum_comp, Fintype.sum_prod_type]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ k]
  simp only [Equiv.piSplitAt_symm_apply, dite_true, modeUnfold, Matrix.of_apply, rankOne_apply]
  rw [Finset.prod_congr rfl fun j _ => by rw [dite_eq_right j.2]]
  ring

/-- For a matrix, the multilinear form is the bilinear form `uᵀ M v`
([golub2013matrix] (12.5.22)). -/
theorem multilinearForm_ofMatrix {κ : Fin 2 → Type v} [∀ i, Fintype (κ i)]
    (M : Matrix (κ 0) (κ 1) R) (u : ∀ i, κ i → R) :
    multilinearForm (ofMatrix M) u = u 0 ⬝ᵥ (M *ᵥ u 1) := by
  rw [multilinearForm, ← (piFinTwoEquiv κ).symm.sum_comp, Fintype.sum_prod_type]
  simp only [dotProduct, mulVec, Finset.mul_sum, Fin.prod_univ_two, ofMatrix_apply,
    piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

end Form

section Real

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)]

/-- The multilinear Rayleigh quotient ([golub2013matrix] §12.5.6):
`ψ_𝒜(u) = 𝒜(u₁, …, u_d) / ∏ ‖uᵢ‖` on Euclidean vectors. -/
noncomputable def multilinearRayleigh (A : Tensor κ ℝ) (u : ∀ i, EuclideanSpace ℝ (κ i)) : ℝ :=
  multilinearForm A (fun i => (u i).ofLp) / ∏ i, ‖u i‖

/-- A tensor singular value ([golub2013matrix] §12.5.6, "we will call `ψ_𝒜(u₁, u₂, u₃)` a
singular value of the tensor"): `σ` with unit vectors `u` such that
`𝒜_(k) (⊗_{j ≠ k} u_j) = σ u_k` for every mode `k`. -/
def IsSingularValue (A : Tensor κ ℝ) (σ : ℝ) : Prop :=
  ∃ u : ∀ i, EuclideanSpace ℝ (κ i), (∀ i, ‖u i‖ = 1) ∧
    ∀ k, A.modeUnfold k *ᵥ (rankOne fun j : {j // j ≠ k} => (u j).ofLp) = σ • (u k).ofLp

/-- A tensor singular value is the value of the Rayleigh quotient at its singular vectors. -/
theorem IsSingularValue.exists_eq_multilinearRayleigh [Nonempty ι] {A : Tensor κ ℝ} {σ : ℝ}
    (h : A.IsSingularValue σ) :
    ∃ u : ∀ i, EuclideanSpace ℝ (κ i), (∀ i, ‖u i‖ = 1) ∧ σ = multilinearRayleigh A u := by
  obtain ⟨u, hu, heq⟩ := h
  obtain ⟨k⟩ := ‹Nonempty ι›
  refine ⟨u, hu, ?_⟩
  rw [multilinearRayleigh, Finset.prod_eq_one fun i _ => hu i, div_one,
    multilinearForm_eq_modeUnfold _ _ k, heq k, dotProduct_smul, smul_eq_mul]
  have h1 : (u k).ofLp ⬝ᵥ (u k).ofLp = 1 := by
    have := EuclideanSpace.inner_eq_star_dotProduct (u k) (u k)
    rw [real_inner_self_eq_norm_sq, hu k] at this
    simpa [dotProduct_comm] using this.symm
  rw [h1, mul_one]

end Real

/-! ### Symmetric tensors -/

section Symm

variable [DecidableEq ι] {ν : Type v}

/-- The equivalence of the column tuples of the mode-`k` and mode-`l` unfoldings of a tensor with
equal mode index types, induced by the transposition of `k` and `l`. -/
def swapColEquiv (k l : ι) : ({j // j ≠ k} → ν) ≃ ({j // j ≠ l} → ν) :=
  Equiv.arrowCongr ((Equiv.swap k l).subtypeEquiv fun j => by
    rw [ne_eq, ne_eq, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]) (Equiv.refl ν)

/-- All modal unfoldings of a symmetric tensor agree ([golub2013matrix] §12.5.7): up to the
relabelling of the column tuples induced by the transposition of the two modes. -/
theorem IsSymm.modeUnfold_eq {C : Tensor (fun _ : ι => ν) R} (hC : C.IsSymm) (k l : ι) :
    C.modeUnfold l = (C.modeUnfold k).submatrix id (swapColEquiv k l).symm := by
  ext x c
  simp only [modeUnfold, Matrix.of_apply, submatrix_apply, id_eq]
  refine (hC (Equiv.swap k l) _).symm.trans (congrArg C ?_)
  funext i
  simp only [Function.comp_apply, Equiv.piSplitAt_symm_apply, swapColEquiv,
    Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl,
    Function.comp_apply, id_eq, Equiv.symm_symm, Equiv.subtypeEquiv_apply]
  by_cases hik : i = k
  · subst hik
    simp
  · by_cases hil : i = l
    · subst hil
      simp [hik, Ne.symm hik]
    · simp [hik, hil, Equiv.swap_apply_of_ne_of_ne hik hil]

end Symm

end Tensor
