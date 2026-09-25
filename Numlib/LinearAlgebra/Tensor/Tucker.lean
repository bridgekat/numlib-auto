/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a new `Mathlib.LinearAlgebra.Tensor` directory beside `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.LinearAlgebra.Tensor.HOSVD

/-!
# The Tucker format and the Tucker approximation problem

A tensor is in Tucker format with multilinear rank at most `r` when it is a multilinear product
`S ×₁ U₁ ⋯ ×_d U_d` of a core `S : Tensor (fun k => Fin (r k)) 𝕜` by factors `U k` with orthonormal
columns ([golub2013matrix] §12.5.3). The Tucker approximation problem (12.5.12)–(12.5.13) asks for
the best such approximation of a given tensor; for given factors the best core is
`A ×₁ U₁ᴴ ⋯ ×_d U_dᴴ`, and the problem becomes the maximization of `‖A ×₁ U₁ᴴ ⋯ ×_d U_dᴴ‖`, which
can be read through any modal unfolding. The alternating (ALS) iteration of the book is an
unnumbered "Repeat" framework with no convergence theorem; what each of its updates solves is
recorded here.

## Main statements

* `Tensor.multilinearRank_le_iff`: the Tucker format characterizes the multilinear rank.
* `Tensor.norm_sub_multilinearProd_sq`: the best core for given factors.
* `Tensor.norm_multilinearProd_conjTranspose_eq_modeUnfold`: the objective through an unfolding.

## References

* [golub2013matrix], §12.5.3.
-/

universe u v

open Matrix
open scoped InnerProductSpace Matrix.Norms.Frobenius

namespace Tensor

variable {ι : Type u} {κ : ι → Type v} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)]
  {𝕜 : Type*} [RCLike 𝕜] {r : ι → ℕ}

open scoped ComplexOrder in
/-- The Tucker format characterizes the multilinear rank ([golub2013matrix] §12.5.2–12.5.3): `A`
has multilinear rank at most `r` iff `A = S ×₁ U₁ ⋯ ×_d U_d` with a core of size `r` and factors
with orthonormal columns (when `r k ≤ card (κ k)`, so that such factors exist). The factors are
chosen among the HOSVD factors, keeping a set of `r k` directions containing every nonzero singular
value of `A_(k)`; the truncated HOSVD is then exact. -/
theorem multilinearRank_le_iff (A : Tensor κ 𝕜) (hr : ∀ k, r k ≤ Fintype.card (κ k)) :
    (∀ k, multilinearRank A k ≤ r k) ↔
      ∃ (U : ∀ k, Matrix (κ k) (Fin (r k)) 𝕜) (S : Tensor (fun k => Fin (r k)) 𝕜),
        (∀ k, (U k)ᴴ * U k = 1) ∧ A = multilinearProd U S := by
  classical
  constructor
  · intro h
    have hT : ∀ k, ∃ T : Finset (κ k),
        (∀ i, (A.modeUnfold k)ᴴ.singularValues i ≠ 0 → i ∈ T) ∧ T.card = r k := by
      intro k
      obtain ⟨T, hsub, -, hcard⟩ := Finset.exists_subsuperset_card_eq (n := r k)
        (Finset.subset_univ (Finset.univ.filter fun i => (A.modeUnfold k)ᴴ.singularValues i ≠ 0))
        (by
          rw [← Fintype.card_subtype, card_singularValues_ne_zero,
            rank_conjTranspose]
          exact h k)
        (by simpa using hr k)
      exact ⟨T, fun i hi => hsub (by simpa using hi), hcard⟩
    choose T hTsub hTcard using hT
    let eqv : ∀ k, Fin (r k) ≃ T k :=
      fun k => (finCongr (hTcard k).symm).trans (T k).equivFin.symm
    let U : ∀ k, Matrix (κ k) (Fin (r k)) 𝕜 :=
      fun k => (hosvdFactor A k).submatrix id fun j => (eqv k j : κ k)
    have hinj : ∀ k, Function.Injective fun j => (eqv k j : κ k) :=
      fun k => Subtype.val_injective.comp (eqv k).injective
    have hU : ∀ k, (U k)ᴴ * U k = 1 := by
      intro k
      simp only [U]
      rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ id _ Function.bijective_id,
        conjTranspose_hosvdFactor_mul_hosvdFactor, submatrix_one _ (hinj k)]
    have hproj : ∀ k, U k * (U k)ᴴ = hosvdFactor A k
        * diagonal (fun i => if i ∈ T k then 1 else 0) * (hosvdFactor A k)ᴴ := by
      intro k
      ext x y
      rw [mul_apply, mul_apply]
      simp only [U, submatrix_apply, id_eq, conjTranspose_apply, mul_diagonal, mul_ite, mul_one,
        mul_zero, ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_coe_sort (T k)]
      exact Fintype.sum_equiv (eqv k) _ _ fun _ => rfl
    have hA : A = truncatedHOSVD A T := by
      have hle := norm_sub_truncatedHOSVD_sq_le A T
      have hzero : ∑ k, ∑ i ∈ (T k)ᶜ, (A.modeUnfold k)ᴴ.singularValues i ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i hi => ?_
        by_contra hne
        exact (Finset.mem_compl.1 hi) (hTsub k i fun h0 => hne (by rw [h0]; ring))
      rw [hzero] at hle
      exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1
        (le_antisymm hle (sq_nonneg _))))
    refine ⟨U, multilinearProd (fun k => (U k)ᴴ) A, hU, ?_⟩
    rw [multilinearProd_multilinearProd]
    simp_rw [hproj]
    exact hA
  · rintro ⟨U, S, -, rfl⟩ k
    rw [multilinearRank, modeUnfold_multilinearProd]
    calc _ ≤ (U k * S.modeUnfold k).rank := rank_mul_le_left _ _
      _ ≤ (U k).rank := rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin (r k)) := rank_le_card_width _
      _ = r k := Fintype.card_fin _

/-- **The best core** ([golub2013matrix] §12.5.3, the display after "the best `𝒮` given any
triplet"): for factors with orthonormal columns,
`‖A − S ×ᵢ Uᵢ‖² = ‖A‖² − ‖A ×ᵢ Uᵢᴴ‖² + ‖S − A ×ᵢ Uᵢᴴ‖²`. -/
theorem norm_sub_multilinearProd_sq {U : ∀ k, Matrix (κ k) (Fin (r k)) 𝕜}
    (hU : ∀ k, (U k)ᴴ * U k = 1) (A : Tensor κ 𝕜) (S : Tensor (fun k => Fin (r k)) 𝕜) :
    ‖A - multilinearProd U S‖ ^ 2
      = ‖A‖ ^ 2 - ‖multilinearProd (fun k => (U k)ᴴ) A‖ ^ 2
        + ‖S - multilinearProd (fun k => (U k)ᴴ) A‖ ^ 2 := by
  classical
  rw [norm_sub_sq (𝕜 := 𝕜), norm_sub_sq (𝕜 := 𝕜) S, inner_multilinearProd_right,
    frobenius_norm_multilinearProd_of_orthonormal hU, inner_re_symm (𝕜 := 𝕜) S]
  ring

/-- The Tucker objective read through any unfolding ([golub2013matrix] §12.5.3, the three-line
display): `‖A ×ᵢ Uᵢᴴ‖ = ‖U_kᴴ A_(k) (⊗_{j ≠ k} U_jᴴ)ᵀ‖`. -/
theorem norm_multilinearProd_conjTranspose_eq_modeUnfold (U : ∀ k, Matrix (κ k) (Fin (r k)) 𝕜)
    (A : Tensor κ 𝕜) (k : ι) :
    ‖multilinearProd (fun k => (U k)ᴴ) A‖
      = ‖(U k)ᴴ * A.modeUnfold k * (piKronecker fun j : {j // j ≠ k} => (U j)ᴴ)ᵀ‖ := by
  rw [← frobenius_norm_modeUnfold, modeUnfold_multilinearProd]

end Tensor
