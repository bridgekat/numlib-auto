/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.ContDiff.Operations`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.MultivariateTaylor.LinearComp

/-!
# Functions of one coordinate of `EuclideanSpace ℝ ι`

For `g : ℝ → ℝ` and the function `w ↦ g(w_i)` on `EuclideanSpace ℝ ι`: its smoothness
(`ContDiffAt.comp_coord`) and its derivative tensors
(`ContDiffAt.iteratedFDeriv_comp_coord_apply`, `ContDiffAt.norm_iteratedFDeriv_comp_coord_le`).
-/

open Finset

section Coord

variable {ι : Type*} [Fintype ι] {g : ℝ → ℝ} {v : EuclideanSpace ℝ ι} {k : ℕ}

/-- A coordinate projection of `EuclideanSpace ℝ ι` has norm at most `1`. -/
theorem EuclideanSpace.norm_proj_le (i : ι) :
    ‖(EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  rw [one_mul]
  simpa using PiLp.norm_apply_le w i

/-- `|w_i| ≤ ‖w‖` in `EuclideanSpace ℝ ι`. -/
theorem EuclideanSpace.abs_apply_le_norm (w : EuclideanSpace ℝ ι) (i : ι) : |w i| ≤ ‖w‖ := by
  simpa using PiLp.norm_apply_le w i

/-- `w ↦ g(w_i)` is `C^n` at `v` if `g` is `C^n` at `v_i`. -/
theorem ContDiffAt.comp_coord {n : WithTop ℕ∞} (i : ι) (hg : ContDiffAt ℝ n g (v i)) :
    ContDiffAt ℝ n (fun w : EuclideanSpace ℝ ι => g (w i)) v :=
  hg.comp v (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).contDiff.contDiffAt

/-- `∇^k (w ↦ g(w_i))(v)` as a composition with the projection, for `g` of class `C^k` at
`v_i`. -/
theorem ContDiffAt.iteratedFDeriv_comp_coord (i : ι) (hg : ContDiffAt ℝ k g (v i)) :
    iteratedFDeriv ℝ k (fun w : EuclideanSpace ℝ ι => g (w i)) v =
      (iteratedFDeriv ℝ k g (v i)).compContinuousLinearMap
        fun _ => (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
  hg.iteratedFDeriv_comp_continuousLinearMap (EuclideanSpace.proj i) le_rfl

/-- `∇^k (w ↦ g(w_i))(v)[m_1, …, m_k] = g^{(k)}(v_i) ∏_j (m_j)_i` for `g` of class `C^k` at
`v_i`. -/
theorem ContDiffAt.iteratedFDeriv_comp_coord_apply (i : ι) (hg : ContDiffAt ℝ k g (v i))
    (m : Fin k → EuclideanSpace ℝ ι) :
    iteratedFDeriv ℝ k (fun w : EuclideanSpace ℝ ι => g (w i)) v m =
      iteratedDeriv k g (v i) * ∏ j, m j i := by
  rw [hg.iteratedFDeriv_comp_coord i, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul, mul_comm]
  rfl

/-- `∇^k (w ↦ g(w_i))(v)[h]^k = g^{(k)}(v_i) h_i^k` for `g` of class `C^k` at `v_i`. -/
theorem ContDiffAt.iteratedFDeriv_comp_coord_apply_const (i : ι) (hg : ContDiffAt ℝ k g (v i))
    (h : EuclideanSpace ℝ ι) :
    iteratedFDeriv ℝ k (fun w : EuclideanSpace ℝ ι => g (w i)) v (fun _ => h) =
      iteratedDeriv k g (v i) * h i ^ k := by
  rw [hg.iteratedFDeriv_comp_coord_apply i, prod_const, card_univ, Fintype.card_fin]

/-- `‖∇^k (w ↦ g(w_i))(v)‖ ≤ |g^{(k)}(v_i)|` for `g` of class `C^k` at `v_i`. -/
theorem ContDiffAt.norm_iteratedFDeriv_comp_coord_le (i : ι) (hg : ContDiffAt ℝ k g (v i)) :
    ‖iteratedFDeriv ℝ k (fun w : EuclideanSpace ℝ ι => g (w i)) v‖ ≤
      |iteratedDeriv k g (v i)| := by
  rw [hg.iteratedFDeriv_comp_coord i]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [prod_const, card_univ, Fintype.card_fin, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (EuclideanSpace.norm_proj_le i))

end Coord
