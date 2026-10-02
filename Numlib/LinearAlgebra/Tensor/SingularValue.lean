/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a new `Mathlib.LinearAlgebra.Tensor` directory beside `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Numlib.LinearAlgebra.Matrix.SVD
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

* `Tensor.multilinearForm`, `Tensor.multilinearRayleigh`, `Tensor.symmetricRayleigh`.
* `Tensor.IsSingularValue`.

## Main statements

* `Tensor.multilinearForm_eq_modeUnfold`: the book's `u₁ᵀ 𝒜_(1) (u₃ ⊗ u₂)`, typed.
* `Tensor.IsSymm.modeUnfold_eq`: the modal unfoldings of a symmetric tensor agree.
* `Tensor.fderiv_multilinearRayleigh_single`: the partial derivatives of `ψ_𝒜`, computed along
  the line `t ↦ u + t e_k w`, on which the numerator is affine and one norm varies.
* `Tensor.hasFDerivAt_multilinearRayleigh_eq_zero_iff`: the critical points of `ψ_𝒜` are the
  singular vectors (normalized).
* `Tensor.hasFDerivAt_symmetricRayleigh_eq_zero_iff`: the critical points of `φ_𝒞` for a symmetric
  `𝒞` are its eigenvectors; `φ_𝒞 = ψ_𝒞 ∘ diag` and the `d` partial derivatives agree by symmetry.
* `Matrix.bilinearRayleigh_eq_multilinearRayleigh`: the order-two case is the bilinear Rayleigh
  quotient `ψ_A(u, v) = ⟪u, A v⟫ / (‖u‖ ‖v‖)` of a matrix ([golub2013matrix] (12.5.22)), whose
  critical points (`Matrix.fderiv_bilinearRayleigh_eq_zero_iff`) are the singular triples
  (`Matrix.abs_critical_bilinearRayleigh_mem_colSingularValues`).

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

/-! ### Critical points of the Rayleigh quotients -/

section Critical

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)]

/-- The multilinear form of a real tensor as a continuous multilinear map on the Euclidean spaces
of its modes. -/
noncomputable def multilinearFormL (A : Tensor κ ℝ) :
    ContinuousMultilinearMap ℝ (fun i => EuclideanSpace ℝ (κ i)) ℝ :=
  ∑ a : ∀ i, κ i, A a • (ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℝ).compContinuousLinearMap
    fun i => EuclideanSpace.proj (a i)

theorem multilinearFormL_apply (A : Tensor κ ℝ) (u : ∀ i, EuclideanSpace ℝ (κ i)) :
    multilinearFormL A u = multilinearForm A fun i => (u i).ofLp := by
  simp [multilinearFormL, multilinearForm, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]

theorem multilinearRayleigh_eq (A : Tensor κ ℝ) :
    multilinearRayleigh A = fun u => multilinearFormL A u / ∏ i, ‖u i‖ := by
  funext u
  rw [multilinearRayleigh, multilinearFormL_apply]

/-- The multilinear Rayleigh quotient is differentiable where no vector vanishes. -/
theorem differentiableAt_multilinearRayleigh (A : Tensor κ ℝ) {u : ∀ i, EuclideanSpace ℝ (κ i)}
    (hu : ∀ i, u i ≠ 0) : DifferentiableAt ℝ (multilinearRayleigh A) u := by
  have e : multilinearRayleigh A = fun u => multilinearFormL A u * (∏ i, ‖u i‖)⁻¹ := by
    rw [multilinearRayleigh_eq]
    simp only [div_eq_mul_inv]
  rw [e]
  exact ((multilinearFormL A).hasFDerivAt u).differentiableAt.mul
    ((HasFDerivAt.finsetProd (u := Finset.univ) fun i _ =>
      ((differentiableAt_apply i u).norm ℝ (hu i)).hasFDerivAt).differentiableAt.fun_inv
      (Finset.prod_ne_zero_iff.2 fun i _ => norm_ne_zero_iff.2 (hu i)))

/-- The multilinear form with the `k`-th vector replaced by `v` is `vᵀ 𝒜_(k) (⊗_{j ≠ k} u_j)`. -/
private theorem multilinearForm_update (A : Tensor κ ℝ) (u : ∀ i, EuclideanSpace ℝ (κ i)) (k : ι)
    (v : EuclideanSpace ℝ (κ k)) :
    multilinearForm A (fun i => (Function.update u k v i).ofLp)
      = v.ofLp ⬝ᵥ (A.modeUnfold k *ᵥ rankOne fun j : {j // j ≠ k} => (u j).ofLp) := by
  have h : (fun j : {j // j ≠ k} => (Function.update u k v j).ofLp)
      = fun j : {j // j ≠ k} => (u j).ofLp :=
    funext fun j => by rw [Function.update_of_ne j.2]
  rw [multilinearForm_eq_modeUnfold _ _ k]
  simp only [Function.update_self, h]

/-- **The partial derivatives of the multilinear Rayleigh quotient** ([golub2013matrix] §12.5.6):
in the direction `w` of the `k`-th vector, the derivative of `ψ_𝒜` at `u` (no `u i` zero) is
`wᵀ 𝒜_(k) (⊗_{j ≠ k} u_j) / ∏ ‖u_i‖ − ψ_𝒜(u) ⟪u_k, w⟫ / ‖u_k‖²`. Along the line
`t ↦ u + t e_k w` the numerator is affine and only the `k`-th norm varies. -/
theorem fderiv_multilinearRayleigh_single (A : Tensor κ ℝ) {u : ∀ i, EuclideanSpace ℝ (κ i)}
    (hu : ∀ i, u i ≠ 0) (k : ι) (w : EuclideanSpace ℝ (κ k)) :
    fderiv ℝ (multilinearRayleigh A) u (Pi.single k w)
      = w.ofLp ⬝ᵥ (A.modeUnfold k *ᵥ rankOne fun j : {j // j ≠ k} => (u j).ofLp) / ∏ i, ‖u i‖
        - multilinearRayleigh A u * (inner ℝ (u k) w / ‖u k‖ ^ 2) := by
  set g := A.modeUnfold k *ᵥ rankOne fun j : {j // j ≠ k} => (u j).ofLp
  set c := ∏ j : {j // j ≠ k}, ‖u j‖
  have hc : 0 < c := Finset.prod_pos fun j _ => norm_pos_iff.2 (hu j)
  have hk : 0 < ‖u k‖ := norm_pos_iff.2 (hu k)
  have hnorm : ∀ v, ∏ i, ‖Function.update u k v i‖ = ‖v‖ * c := fun v => by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ k, Function.update_self]
    exact congrArg _ (Finset.prod_congr rfl fun j _ => by rw [Function.update_of_ne j.2])
  have hN : ∏ i, ‖u i‖ = ‖u k‖ * c := by
    rw [← hnorm, Function.update_eq_self]
  have hF : multilinearForm A (fun i => (u i).ofLp) = (u k).ofLp ⬝ᵥ g := by
    rw [← multilinearForm_update, Function.update_eq_self]
  set e : ∀ i, EuclideanSpace ℝ (κ i) := Pi.single k w with he
  have hline : ∀ t : ℝ, u + t • e = Function.update u k (u k + t • w) := fun t => by
    funext j
    by_cases h : j = k
    · subst h
      simp [he]
    · simp [he, h]
  have hφ : (fun t : ℝ => multilinearRayleigh A (u + t • e))
      = fun t => ((u k).ofLp ⬝ᵥ g + t * (w.ofLp ⬝ᵥ g)) / (c * ‖u k + t • w‖) := by
    funext t
    rw [hline, multilinearRayleigh, multilinearForm_update, hnorm, WithLp.ofLp_add,
      WithLp.ofLp_smul, add_dotProduct, smul_dotProduct, smul_eq_mul, mul_comm c]
  have hL : HasDerivAt (fun t : ℝ => u + t • e) e 0 := by
    have := HasDerivAt.const_add u (HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) e)
    rw [one_smul] at this
    exact this
  have h1 := (differentiableAt_multilinearRayleigh A hu).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) hL (by simp)
  have hn2 : HasDerivAt (fun t : ℝ => ‖u k + t • w‖ ^ 2) (2 * inner ℝ (u k) w) 0 := by
    have := HasDerivAt.norm_sq
      (HasDerivAt.const_add (u k) (HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) w))
    convert this using 1 <;> simp
  have hn : HasDerivAt (fun t : ℝ => ‖u k + t • w‖) (inner ℝ (u k) w / ‖u k‖) 0 := by
    have := hn2.sqrt (by simpa using hu k)
    convert this using 1
    · funext t
      rw [Real.sqrt_sq (norm_nonneg _)]
    · simp only [zero_smul, add_zero, Real.sqrt_sq (norm_nonneg _)]
      field_simp
  have h2 := HasDerivAt.div (HasDerivAt.const_add ((u k).ofLp ⬝ᵥ g)
    (HasDerivAt.mul_const (hasDerivAt_id (0 : ℝ)) (w.ofLp ⬝ᵥ g))) (HasDerivAt.const_mul c hn)
    (by rw [zero_smul, add_zero]; exact (mul_pos hc hk).ne')
  simp only [Function.comp_def] at h1
  rw [hφ] at h1
  rw [h1.unique h2, multilinearRayleigh, hF, hN]
  simp only [id_eq, zero_smul, add_zero, zero_mul, one_mul]
  field_simp

/-- The partial derivative of `ψ_𝒜` in the `k`-th vector vanishes iff the `k`-th equation of a
tensor singular value holds at the normalized vectors `û_i = u_i / ‖u_i‖`. -/
theorem forall_fderiv_multilinearRayleigh_single_eq_zero_iff (A : Tensor κ ℝ)
    {u : ∀ i, EuclideanSpace ℝ (κ i)} (hu : ∀ i, u i ≠ 0) (k : ι) :
    (∀ w, fderiv ℝ (multilinearRayleigh A) u (Pi.single k w) = 0) ↔
      A.modeUnfold k *ᵥ rankOne (fun j : {j // j ≠ k} => (‖u j‖⁻¹ • u j).ofLp)
        = multilinearRayleigh A u • (‖u k‖⁻¹ • u k).ofLp := by
  set g := A.modeUnfold k *ᵥ rankOne fun j : {j // j ≠ k} => (u j).ofLp with hg
  set c := ∏ j : {j // j ≠ k}, ‖u j‖ with hcdef
  set ψ := multilinearRayleigh A u
  have hc : 0 < c := Finset.prod_pos fun j _ => norm_pos_iff.2 (hu j)
  have hk : 0 < ‖u k‖ := norm_pos_iff.2 (hu k)
  have hN : ∏ i, ‖u i‖ = ‖u k‖ * c := Fintype.prod_eq_mul_prod_subtype_ne _ k
  have hlhs : A.modeUnfold k *ᵥ rankOne (fun j : {j // j ≠ k} => (‖u j‖⁻¹ • u j).ofLp)
      = c⁻¹ • g := by
    funext a
    simp only [hg, hcdef, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, rankOne_apply,
      WithLp.ofLp_smul, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hdiff : ∀ w : EuclideanSpace ℝ (κ k),
      fderiv ℝ (multilinearRayleigh A) u (Pi.single k w)
        = (‖u k‖⁻¹) * (w.ofLp ⬝ᵥ (c⁻¹ • g - (ψ * ‖u k‖⁻¹) • (u k).ofLp)) := fun w => by
    rw [fderiv_multilinearRayleigh_single A hu, ← hg, hN,
      EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_sub, dotProduct_smul,
      dotProduct_smul, smul_eq_mul, smul_eq_mul]
    field_simp
    ring
  rw [hlhs, WithLp.ofLp_smul, smul_smul, ← sub_eq_zero]
  simp only [hdiff, mul_eq_zero, inv_eq_zero, norm_eq_zero, hu k, false_or]
  constructor
  · intro h
    exact dotProduct_self_eq_zero.1 (h (WithLp.toLp 2 (c⁻¹ • g - (ψ * ‖u k‖⁻¹) • (u k).ofLp)))
  · intro h w
    rw [h, dotProduct_zero]

/-- **The critical points of the multilinear Rayleigh quotient** ([golub2013matrix] §12.5.6,
"the equation `∇ψ_𝒜 = 0`"): for `u` with no `u i` zero, the Fréchet derivative of
`ψ_𝒜(u) = 𝒜(u₁, …, u_d) / ∏ ‖u_i‖` vanishes at `u` iff, with `û_i = u_i / ‖u_i‖`,
`𝒜_(k) (⊗_{j ≠ k} û_j) = ψ_𝒜(u) û_k` for every mode `k`: the normalized vectors are singular
vectors in the sense of `Tensor.IsSingularValue`. The partial derivatives are
`Tensor.fderiv_multilinearRayleigh_single`. -/
theorem hasFDerivAt_multilinearRayleigh_eq_zero_iff (A : Tensor κ ℝ)
    {u : ∀ i, EuclideanSpace ℝ (κ i)} (hu : ∀ i, u i ≠ 0) :
    HasFDerivAt (multilinearRayleigh A) (0 : (∀ i, EuclideanSpace ℝ (κ i)) →L[ℝ] ℝ) u ↔
      ∀ k, A.modeUnfold k *ᵥ rankOne (fun j : {j // j ≠ k} => (‖u j‖⁻¹ • u j).ofLp)
        = multilinearRayleigh A u • (‖u k‖⁻¹ • u k).ofLp := by
  have hd := (differentiableAt_multilinearRayleigh A hu).hasFDerivAt
  simp only [← forall_fderiv_multilinearRayleigh_single_eq_zero_iff A hu]
  constructor
  · intro h k w
    rw [hd.unique h, _root_.zero_apply]
  · intro h
    convert hd using 1
    refine (ContinuousLinearMap.ext fun v => ?_).symm
    rw [← Finset.univ_sum_single v, map_sum, _root_.zero_apply]
    exact Finset.sum_eq_zero fun k _ => h k (v k)

variable {ν : Type*} [Fintype ν]

/-- The Rayleigh quotient of a symmetric tensor ([golub2013matrix] (12.5.24)):
`φ_𝒞(x) = 𝒞(x, …, x) / ‖x‖ ^ d`. -/
noncomputable def symmetricRayleigh (C : Tensor (fun _ : ι => ν) ℝ) (x : EuclideanSpace ℝ ν) :
    ℝ :=
  multilinearForm C (fun _ => x.ofLp) / ‖x‖ ^ Fintype.card ι

theorem symmetricRayleigh_eq (C : Tensor (fun _ : ι => ν) ℝ) (x : EuclideanSpace ℝ ν) :
    symmetricRayleigh C x = multilinearRayleigh C fun _ => x := by
  rw [symmetricRayleigh, multilinearRayleigh, Finset.prod_const, Finset.card_univ]

/-- The unfoldings of a symmetric tensor agree on the rank-one tensors of a repeated vector. -/
private theorem IsSymm.modeUnfold_mulVec_rankOne {C : Tensor (fun _ : ι => ν) ℝ} (hC : C.IsSymm)
    (k l : ι) (z : ν → ℝ) :
    C.modeUnfold l *ᵥ rankOne (fun _ : {j // j ≠ l} => z)
      = C.modeUnfold k *ᵥ rankOne (fun _ : {j // j ≠ k} => z) := by
  rw [hC.modeUnfold_eq k l]
  funext x
  simp only [mulVec, dotProduct, submatrix_apply, id_eq]
  refine Fintype.sum_equiv (swapColEquiv k l).symm _ _ fun c => congrArg _ ?_
  simp only [rankOne_apply, swapColEquiv, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply,
    Equiv.refl_symm, Equiv.coe_refl, Function.comp_apply, id_eq]
  exact (Equiv.prod_comp _ fun j => z (c j)).symm

/-- **The critical points of the Rayleigh quotient of a symmetric tensor** ([golub2013matrix]
(12.5.23)–(12.5.24)): for a symmetric `𝒞` with a mode `k` and `x ≠ 0`, the Fréchet derivative of
`φ_𝒞(x) = 𝒞(x, …, x) / ‖x‖ ^ d` vanishes at `x` iff, with `x̂ = x / ‖x‖`,
`𝒞_(k) (x̂ ⊗ ⋯ ⊗ x̂) = φ_𝒞(x) x̂` (all unfoldings agree, `Tensor.IsSymm.modeUnfold_eq`). The
derivative of `φ_𝒞 = ψ_𝒞 ∘ diag` in the direction `w` is the sum of the `d` partial derivatives
of `ψ_𝒞` in the direction `w`, which by symmetry are equal. (The book's gradient omits the factor
`d`, harmless at zero.) -/
theorem hasFDerivAt_symmetricRayleigh_eq_zero_iff {C : Tensor (fun _ : ι => ν) ℝ}
    (hC : C.IsSymm) {x : EuclideanSpace ℝ ν} (hx : x ≠ 0) (k : ι) :
    HasFDerivAt (symmetricRayleigh C) (0 : EuclideanSpace ℝ ν →L[ℝ] ℝ) x ↔
      C.modeUnfold k *ᵥ rankOne (fun _ : {j // j ≠ k} => (‖x‖⁻¹ • x).ofLp)
        = symmetricRayleigh C x • (‖x‖⁻¹ • x).ofLp := by
  set diag : EuclideanSpace ℝ ν →L[ℝ] (ι → EuclideanSpace ℝ ν) :=
    ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ _
  have hu : ∀ i : ι, (fun _ : ι => x) i ≠ 0 := fun _ => hx
  have hψ := (differentiableAt_multilinearRayleigh C hu).hasFDerivAt
  have hφ : HasFDerivAt (symmetricRayleigh C)
      ((fderiv ℝ (multilinearRayleigh C) fun _ => x).comp diag) x := by
    have e : symmetricRayleigh C = multilinearRayleigh C ∘ diag :=
      funext fun y => symmetricRayleigh_eq C y
    rw [e]
    exact hψ.comp x diag.hasFDerivAt
  -- the derivative in the direction `w` is `d` times the `k`-th partial derivative
  have hsum : ∀ w, ((fderiv ℝ (multilinearRayleigh C) fun _ => x).comp diag) w
      = Fintype.card ι * fderiv ℝ (multilinearRayleigh C) (fun _ => x) (Pi.single k w) := by
    intro w
    have hw : diag w = ∑ l, Pi.single l w := (Finset.univ_sum_single fun _ => w).symm
    rw [ContinuousLinearMap.comp_apply, hw, map_sum, ← Finset.card_univ, ← nsmul_eq_mul,
      ← Finset.sum_const]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [fderiv_multilinearRayleigh_single C hu, fderiv_multilinearRayleigh_single C hu,
      hC.modeUnfold_mulVec_rankOne k l]
  have : Nonempty ι := ⟨k⟩
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [symmetricRayleigh_eq, ← forall_fderiv_multilinearRayleigh_single_eq_zero_iff C hu k]
  constructor
  · intro h w
    have := congrArg (· w) (hφ.unique h)
    simp only [hsum, _root_.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hcard
  · intro h
    convert hφ using 1
    refine (ContinuousLinearMap.ext fun w => ?_).symm
    rw [hsum, h, mul_zero, _root_.zero_apply]

end Critical

end Tensor

/-! ### Matrices: the bilinear Rayleigh quotient

A matrix is a tensor of order two (`Tensor.ofMatrix`), and its multilinear Rayleigh quotient is
the bilinear one `ψ_A(u, v) = ⟪u, A v⟫ / (‖u‖ ‖v‖)` of [golub2013matrix] (12.5.22)
(`Matrix.bilinearRayleigh_eq_multilinearRayleigh`). Its critical points are therefore read off
`Tensor.hasFDerivAt_multilinearRayleigh_eq_zero_iff`: the two modal equations are
`A v̂ = ψ û` and `Aᵀ û = ψ v̂`, and `|ψ|` is a singular value. -/

namespace Matrix

section BilinearRayleigh

variable {m n : Type v} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/- The two mode index types of a matrix read as a tensor of order two, with the length of the
vector fixed to `2` so that every occurrence elaborates to the same term. -/
set_option hygiene false in
local notation "κmn" => (![m, n] : Fin 2 → Type v)

/-- The **bilinear Rayleigh quotient** `ψ_A(u, v) = ⟪u, A v⟫ / (‖u‖ ‖v‖)` of a real matrix
([golub2013matrix] (12.5.22)), on `EuclideanSpace ℝ m × EuclideanSpace ℝ n`. It is the multilinear
Rayleigh quotient of `A` as a tensor (`Matrix.bilinearRayleigh_eq_multilinearRayleigh`), and its
stationary values are the singular values
(`Matrix.abs_critical_bilinearRayleigh_mem_colSingularValues`). -/
noncomputable def bilinearRayleigh (A : Matrix m n ℝ)
    (x : EuclideanSpace ℝ m × EuclideanSpace ℝ n) : ℝ :=
  inner ℝ x.1 (toEuclideanLin A x.2) / (‖x.1‖ * ‖x.2‖)

variable (A : Matrix m n ℝ)

omit [DecidableEq m] [DecidableEq n] in
/-- The multilinear form of a real matrix read as a tensor of order two is `uᵀ A v`, the
`ℝ`-instance form of `Tensor.multilinearForm_ofMatrix`. -/
private theorem multilinearForm_ofMatrix_real (u : ∀ i : Fin 2, κmn i → ℝ) :
    Tensor.multilinearForm (Tensor.ofMatrix (κ := κmn) A) u = u 0 ⬝ᵥ (A *ᵥ u 1) :=
  Tensor.multilinearForm_ofMatrix A u

omit [DecidableEq m] in
/-- **The bilinear Rayleigh quotient is the multilinear one of the matrix as a tensor**
([golub2013matrix] (12.5.22)): `ψ_A(u, v) = ψ_𝒜(u, v)` for `𝒜 = ofMatrix A`, the pair read as a
tuple over `Fin 2`. -/
theorem bilinearRayleigh_eq_multilinearRayleigh :
    bilinearRayleigh A = Tensor.multilinearRayleigh (Tensor.ofMatrix (κ := κmn) A) ∘
      (ContinuousLinearEquiv.piFinTwo ℝ fun i => EuclideanSpace ℝ (κmn i)).symm := by
  funext x
  simp only [ContinuousLinearEquiv.piFinTwo_symm_apply, bilinearRayleigh]
  congr 1
  · rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm,
      multilinearForm_ofMatrix_real]
    rfl
  · rw [Fin.prod_univ_two]
    rfl

omit [DecidableEq m] [DecidableEq n] in
/-- The mode-`0` unfolding of a matrix acts on the rank-one tensors of the other mode as the
matrix itself. -/
private theorem modeUnfold_zero_ofMatrix_mulVec (z : ∀ i : Fin 2, κmn i → ℝ) :
    (Tensor.ofMatrix (κ := κmn) A).modeUnfold 0 *ᵥ
      Tensor.rankOne (fun j : {j // j ≠ (0 : Fin 2)} => z j) = A *ᵥ z 1 := by
  classical
  refine funext fun x => ?_
  have hz : (fun j : {j // j ≠ (0 : Fin 2)} => Function.update z 0 (Pi.single x 1) j) =
      fun j : {j // j ≠ (0 : Fin 2)} => z j := funext fun j => Function.update_of_ne j.2 _ _
  have h := Tensor.multilinearForm_eq_modeUnfold (Tensor.ofMatrix (κ := κmn) A)
    (Function.update z 0 (Pi.single x 1)) 0
  rw [multilinearForm_ofMatrix_real, Function.update_self, hz,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), single_one_dotProduct,
    single_one_dotProduct] at h
  exact h.symm

omit [DecidableEq m] [DecidableEq n] in
/-- The mode-`1` unfolding of a matrix acts on the rank-one tensors of the other mode as the
transpose. -/
private theorem modeUnfold_one_ofMatrix_mulVec (z : ∀ i : Fin 2, κmn i → ℝ) :
    (Tensor.ofMatrix (κ := κmn) A).modeUnfold 1 *ᵥ
      Tensor.rankOne (fun j : {j // j ≠ (1 : Fin 2)} => z j) = Aᵀ *ᵥ z 0 := by
  classical
  refine funext fun x => ?_
  have hz : (fun j : {j // j ≠ (1 : Fin 2)} => Function.update z 1 (Pi.single x 1) j) =
      fun j : {j // j ≠ (1 : Fin 2)} => z j := funext fun j => Function.update_of_ne j.2 _ _
  have h := Tensor.multilinearForm_eq_modeUnfold (Tensor.ofMatrix (κ := κmn) A)
    (Function.update z 1 (Pi.single x 1)) 1
  rw [multilinearForm_ofMatrix_real, Function.update_self, hz,
    Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), single_one_dotProduct] at h
  rw [← h]
  have key : ∀ (w : m → ℝ) (y : n), w ⬝ᵥ (A *ᵥ Pi.single y 1) = (Aᵀ *ᵥ w) y := fun w y => by
    rw [dotProduct_mulVec, dotProduct_single_one, mulVec_transpose]
  exact key (z 0) x

/-- **The critical points of the bilinear Rayleigh quotient** ([golub2013matrix] (12.5.22) and the
gradient display after it): at nonzero `(u, v)`, with `û = u / ‖u‖`, `v̂ = v / ‖v‖` and
`ψ = ψ_A(u, v)`, the derivative of `ψ_A` vanishes if and only if `A v̂ = ψ û` and `Aᵀ û = ψ v̂`.
These are the two modal equations of `Tensor.hasFDerivAt_multilinearRayleigh_eq_zero_iff` for
`A` as a tensor. -/
theorem fderiv_bilinearRayleigh_eq_zero_iff {u : EuclideanSpace ℝ m} {v : EuclideanSpace ℝ n}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    fderiv ℝ (bilinearRayleigh A) (u, v) = 0 ↔
      toEuclideanLin A (‖v‖⁻¹ • v) = bilinearRayleigh A (u, v) • ‖u‖⁻¹ • u ∧
        toEuclideanLin Aᵀ (‖u‖⁻¹ • u) = bilinearRayleigh A (u, v) • ‖v‖⁻¹ • v := by
  set e := ContinuousLinearEquiv.piFinTwo ℝ fun i => EuclideanSpace ℝ (κmn i)
  set T := Tensor.ofMatrix (κ := κmn) A
  set y : ∀ i : Fin 2, EuclideanSpace ℝ (κmn i) := e.symm (u, v) with hydef
  have hy0 : y 0 = u := rfl
  have hy1 : y 1 = v := rfl
  have hy : ∀ i, y i ≠ 0 := Fin.forall_fin_two.2 ⟨hu, hv⟩
  have hψ := bilinearRayleigh_eq_multilinearRayleigh A
  have hval : Tensor.multilinearRayleigh T y = bilinearRayleigh A (u, v) := by rw [hψ]; rfl
  have hdiff : DifferentiableAt ℝ (bilinearRayleigh A) (u, v) := by
    rw [hψ]
    exact (Tensor.differentiableAt_multilinearRayleigh T hy).comp (u, v)
      e.symm.differentiableAt
  have h0 : fderiv ℝ (bilinearRayleigh A) (u, v) = 0 ↔
      HasFDerivAt (Tensor.multilinearRayleigh T)
        (0 : (∀ i : Fin 2, EuclideanSpace ℝ (κmn i)) →L[ℝ] ℝ) y := by
    constructor
    · intro h
      have h1 : HasFDerivAt (bilinearRayleigh A) 0 (u, v) := h ▸ hdiff.hasFDerivAt
      rw [hψ] at h1
      exact (e.symm.comp_right_hasFDerivAt_iff'.1 h1).congr_fderiv (by ext w; rfl)
    · intro h
      have h2 : HasFDerivAt (Tensor.multilinearRayleigh T ∘ e.symm) 0 (u, v) :=
        e.symm.comp_right_hasFDerivAt_iff'.2 (h.congr_fderiv (by ext w; rfl))
      rw [← hψ] at h2
      exact h2.fderiv
  rw [h0, Tensor.hasFDerivAt_multilinearRayleigh_eq_zero_iff T hy, Fin.forall_fin_two, hval,
    modeUnfold_zero_ofMatrix_mulVec A fun i => (‖y i‖⁻¹ • y i).ofLp,
    modeUnfold_one_ofMatrix_mulVec A fun i => (‖y i‖⁻¹ • y i).ofLp, hy0, hy1]
  refine and_congr ?_ ?_ <;>
  · rw [← (WithLp.ofLp_injective 2).eq_iff]
    exact Iff.rfl

omit [DecidableEq m] in
/-- **Singular values are the stationary values of the bilinear Rayleigh quotient**
([golub2013matrix] (12.5.22)): at a critical point `(u, v)` of `ψ_A(u, v) = ⟪u, A v⟫ / (‖u‖ ‖v‖)`
with `u, v ≠ 0`, `|ψ_A(u, v)|` is a singular value of `A` (column-indexed,
`Matrix.colSingularValues`): the critical-point equations `A v̂ = ψ û`, `Aᵀ û = ψ v̂` give
`Aᵀ A v̂ = ψ² v̂`. Conversely every singular triple is a critical point, by
`Matrix.fderiv_bilinearRayleigh_eq_zero_iff`. -/
theorem abs_critical_bilinearRayleigh_mem_colSingularValues {u : EuclideanSpace ℝ m}
    {v : EuclideanSpace ℝ n} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : fderiv ℝ (bilinearRayleigh A) (u, v) = 0) :
    ∃ i, |bilinearRayleigh A (u, v)| = A.colSingularValues i := by
  classical
  obtain ⟨h1, h2⟩ := (A.fderiv_bilinearRayleigh_eq_zero_iff hu hv).1 h
  set ψ := bilinearRayleigh A (u, v)
  have hv' : ‖v‖⁻¹ • v ≠ 0 := smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 hv)) hv
  have heig : toEuclideanLin (Aᴴ * A) (‖v‖⁻¹ • v) = (ψ ^ 2) • (‖v‖⁻¹ • v) := by
    rw [toEuclideanLin_mul_apply, h1, map_smul, conjTranspose_eq_transpose_of_trivial, h2,
      smul_smul, sq]
  have hH := isHermitian_conjTranspose_mul_self A
  have hev : Module.End.HasEigenvalue (toEuclideanLin (Aᴴ * A)) (ψ ^ 2) :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 heig, hv'⟩
  obtain ⟨i, hi⟩ := (hH.hasEigenvalue_toEuclideanLin_iff (ψ ^ 2)).1 hev
  refine ⟨i, ?_⟩
  rw [colSingularValues, show hH.eigenvalues i = ψ ^ 2 from hi, Real.sqrt_sq_eq_abs]

end BilinearRayleigh

end Matrix
