import Numlib.Analysis.Calculus.TaylorModel
import Numlib.Analysis.Calculus.LipschitzDerivative
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Derivatives and sharp gradient errors of quadratic Taylor models

Second-order Schwarz symmetry under finite `C²` regularity identifies the actual
model derivative. The variation of the genuine second derivative then controls
the gradient error with its sharp factor one half.
-/

namespace TaylorModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual derivative of the quadratic Taylor polynomial. -/
noncomputable def quadraticDerivative (f : E → ℝ) (x s : E) : E →L[ℝ] ℝ :=
  fderiv ℝ f x + fderiv ℝ (fderiv ℝ f) x s

/-- Explicit quadratic model formula in terms of actual first and second derivatives. -/
theorem eval_two_eq (f : E → ℝ) (x s : E) :
    eval f 2 x s = f x + fderiv ℝ f x s + fderiv ℝ (fderiv ℝ f) x s s / 2 := by
  rw [eval_eq_sum]
  norm_num [Finset.sum_range_succ, smul_eq_mul, iteratedFDeriv_one_apply,
    iteratedFDeriv_two_apply]
  ring

/-- Finite `C²` regularity suffices for the genuine derivative of the quadratic model. -/
theorem hasFDerivAt_eval_two {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (s : E) :
    HasFDerivAt (eval f 2 x) (quadraticDerivative f x s) s := by
  let B := fderiv ℝ (fderiv ℝ f) x
  have hsym := hf.isSymmSndFDerivAt (by norm_num)
  have hb := B.hasFDerivAt.clm_apply (hasFDerivAt_id s)
  have hd := ((hasFDerivAt_const (f x) s).add (fderiv ℝ f x).hasFDerivAt).add
    (hb.mul_const ((2 : ℝ)⁻¹))
  have heq : (fun y => f x + fderiv ℝ f x y + B y y * (2 : ℝ)⁻¹) = eval f 2 x := by
    ext y
    simp only [eval_two_eq, div_eq_mul_inv, B]
  change HasFDerivAt (fun y => f x + fderiv ℝ f x y + B y y * (2 : ℝ)⁻¹) _ s at hd
  rw [heq] at hd
  convert hd using 1
  ext v
  simp only [add_apply, zero_add, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, smul_apply, smul_eq_mul,
    quadraticDerivative]
  change fderiv ℝ f x v + B s v = fderiv ℝ f x v + (2 : ℝ)⁻¹ * (B s v + B v s)
  rw [show B v s = B s v from hsym v s]
  ring

/-- The curried second-derivative variation is bounded by the genuine
multilinear tensor variation. -/
theorem norm_secondDerivative_sub_le (f : E → ℝ) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤
      ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ := by
  let B := fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y
  let T := iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y
  refine B.opNorm_le_bound (norm_nonneg T) (fun u => ?_)
  refine (B u).opNorm_le_bound (by positivity) (fun v => ?_)
  have h := (iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y).le_opNorm ![u, v]
  simp only [sub_apply, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.prod_univ_two] at h
  simpa only [B, sub_apply, mul_assoc] using h

/-- Sharp first-derivative error of the actual quadratic Taylor model. -/
theorem norm_fderiv_sub_quadraticDerivative_le {f : E → ℝ} {L : ℝ}
    (hf : ContDiff ℝ 2 f)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (x s : E) :
    ‖fderiv ℝ f (x + s) - quadraticDerivative f x s‖ ≤ L * ‖s‖ ^ 2 / 2 := by
  have hg : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hb := norm_sub_sub_fderiv_le_half_of_lipschitz_bound
    (fun y => (hg.differentiable (by norm_num) y).hasFDerivAt)
    (fun y z => (norm_secondDerivative_sub_le f y z).trans (hlip y z)) x s
  simpa only [quadraticDerivative, sub_add_eq_sub_sub] using hb

end TaylorModel
