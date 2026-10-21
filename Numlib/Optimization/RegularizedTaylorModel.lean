import Numlib.Analysis.Calculus.TaylorSegment
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Regularized Taylor models

The Taylor polynomial uses the iterated Fréchet derivatives of the original map, for both
scalar objectives and vector residuals. Scalar models add an independently normalized radial
power. Smoothness of the original function is unnecessary for the polynomial itself to be
smooth; smoothness enters only when relating it to the original function.
-/

open scoped Nat ContDiff

namespace Optimization.RegularizedTaylorModel

section Taylor

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The degree-`p` Taylor polynomial of `f` at `x`, evaluated at the displacement `s`. -/
noncomputable def taylorModel (f : E → F) (p : ℕ) (x s : E) : F :=
  ∑ j ∈ Finset.range (p + 1), (j ! : ℝ)⁻¹ • iteratedFDeriv ℝ j f x (fun _ ↦ s)

@[simp] theorem taylorModel_zero_degree (f : E → F) (x s : E) :
    taylorModel f 0 x s = f x := by
  simp [taylorModel]

/-- Increasing the model degree adds exactly its highest homogeneous term. -/
theorem taylorModel_succ (f : E → F) (p : ℕ) (x s : E) :
    taylorModel f (p + 1) x s = taylorModel f p x s +
      ((p + 1)! : ℝ)⁻¹ • iteratedFDeriv ℝ (p + 1) f x (fun _ ↦ s) := by
  exact Finset.sum_range_succ _ _

@[simp] theorem taylorModel_zero (f : E → F) (p : ℕ) (x : E) :
    taylorModel f p x 0 = f x := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [taylorModel_succ, ih]
    rw [(iteratedFDeriv ℝ (p + 1) f x).map_coord_zero (0 : Fin (p + 1)) rfl]
    simp

/-- Restricting the model to a line gives the usual scalar powers of the line parameter. -/
theorem taylorModel_smul (f : E → F) (p : ℕ) (x s : E) (t : ℝ) :
    taylorModel f p x (t • s) =
      ∑ j ∈ Finset.range (p + 1), (t ^ j / (j ! : ℝ)) •
        iteratedFDeriv ℝ j f x (fun _ ↦ s) := by
  unfold taylorModel
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_smul]
  congr 1
  ring

/-- For a scalar domain, the canonical model is the usual one-variable Taylor polynomial. -/
theorem taylorModel_real (f : ℝ → F) (p : ℕ) (x s : ℝ) :
    taylorModel f p x s = ∑ j ∈ Finset.range (p + 1),
      (s ^ j / (j ! : ℝ)) • iteratedDeriv j f x := by
  unfold taylorModel
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_smul]
  congr 1
  ring

/-- The first-order model is the value plus the Fréchet derivative applied to the step. -/
@[simp] theorem taylorModel_one (f : E → F) (x s : E) :
    taylorModel f 1 x s = f x + fderiv ℝ f x s := by
  rw [show 1 = 0 + 1 from rfl, taylorModel_succ]
  simp

/-- A Taylor model is smooth of every order, regardless of regularity of its coefficients. -/
theorem contDiff_taylorModel (f : E → F) (p : ℕ) (x : E) (n : ℕ∞ω) :
    ContDiff ℝ n (taylorModel f p x) := by
  unfold taylorModel
  apply ContDiff.sum
  intro j _
  exact ((iteratedFDeriv ℝ j f x).contDiff.comp
    (contDiff_pi.mpr fun _ : Fin j ↦ contDiff_id)).const_smul _

/-- Each homogeneous term differentiates by placing the direction in each slot in turn. -/
theorem hasFDerivAt_taylorModel (f : E → F) (p : ℕ) (x s : E) :
    HasFDerivAt (taylorModel f p x)
      (∑ j ∈ Finset.range (p + 1), (j ! : ℝ)⁻¹ •
        ∑ i : Fin j, (iteratedFDeriv ℝ j f x).toContinuousLinearMap (fun _ ↦ s) i) s := by
  apply HasFDerivAt.fun_sum
  intro j _
  have h := (HasFDerivAt.multilinear_comp (iteratedFDeriv ℝ j f x)
    (fun _ : Fin j ↦ hasFDerivAt_id s)).const_smul ((j ! : ℝ)⁻¹)
  convert h using 1
  · ext y
    rfl
  · simp

/-- The derivative of the finite Taylor polynomial, with no smoothness assumption on `f`. -/
theorem fderiv_taylorModel (f : E → F) (p : ℕ) (x s : E) :
    fderiv ℝ (taylorModel f p x) s =
      ∑ j ∈ Finset.range (p + 1), (j ! : ℝ)⁻¹ •
        ∑ i : Fin j, (iteratedFDeriv ℝ j f x).toContinuousLinearMap (fun _ ↦ s) i :=
  (hasFDerivAt_taylorModel f p x s).fderiv

/-- Differentiating an increase in truncation degree adds the derivative of its top term. -/
theorem fderiv_taylorModel_succ (f : E → F) (p : ℕ) (x s : E) :
    fderiv ℝ (taylorModel f (p + 1) x) s = fderiv ℝ (taylorModel f p x) s +
      ((p + 1)! : ℝ)⁻¹ • ∑ i : Fin (p + 1),
        (iteratedFDeriv ℝ (p + 1) f x).toContinuousLinearMap (fun _ ↦ s) i := by
  rw [fderiv_taylorModel, Finset.sum_range_succ, ← fderiv_taylorModel]

/-- The original function and its Taylor model satisfy the existing segment remainder bound. -/
theorem norm_sub_taylorModel_le {f : E → F} {p : ℕ} {x s : E} {M : ℝ}
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ (p + 1) f (x + t • s))
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (p + 1) f (x + t • s)‖ ≤ M) :
    ‖f (x + s) - taylorModel f p x s‖ ≤ M * ‖s‖ ^ (p + 1) / (p + 1)! :=
  norm_sub_taylorSum_segment_le hf hM

end Taylor

section Regularization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A scalar Taylor model with radial regularization. Positivity requirements belong to the
estimates using the model, leaving the normalization available for different conventions. -/
noncomputable def regularizedModel (f : E → ℝ) (p : ℕ) (x : E)
    (sigma c r : ℝ) (s : E) : ℝ :=
  taylorModel f p x s + sigma / c * ‖s‖ ^ r

/-- The regularized model at the zero step is the objective value, for positive powers. -/
@[simp] theorem regularizedModel_zero (f : E → ℝ) (p : ℕ) (x : E)
    (sigma c : ℝ) {r : ℝ} (hr : 0 < r) :
    regularizedModel f p x sigma c r 0 = f x := by
  simp [regularizedModel, Real.zero_rpow hr.ne']

/-- Model decrease pays for the full regularization term in the Taylor decrease. -/
theorem taylor_decrease_of_model_decrease {f : E → ℝ} {p : ℕ} {x s : E}
    {sigma c r : ℝ} (hr : 0 < r)
    (h : regularizedModel f p x sigma c r s ≤ regularizedModel f p x sigma c r 0) :
    sigma / c * ‖s‖ ^ r ≤ taylorModel f p x 0 - taylorModel f p x s := by
  rw [regularizedModel_zero _ _ _ _ _ hr] at h
  rw [taylorModel_zero]
  unfold regularizedModel at h
  linarith

/-- Strict model decrease gives strict Taylor decrease over the regularization term. -/
theorem taylor_decrease_of_model_decrease_strict {f : E → ℝ} {p : ℕ} {x s : E}
    {sigma c r : ℝ} (hr : 0 < r)
    (h : regularizedModel f p x sigma c r s < regularizedModel f p x sigma c r 0) :
    sigma / c * ‖s‖ ^ r < taylorModel f p x 0 - taylorModel f p x s := by
  rw [regularizedModel_zero _ _ _ _ _ hr] at h
  rw [taylorModel_zero]
  unfold regularizedModel at h
  linarith

end Regularization

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The regularized model has the derivative of the Taylor polynomial plus the radial derivative.
Mathlib's radial derivative theorem includes the origin whenever `r > 1`. -/
theorem fderiv_regularizedModel (f : E → ℝ) (p : ℕ) (x s : E)
    (sigma c : ℝ) {r : ℝ} (hr : 1 < r) :
    fderiv ℝ (regularizedModel f p x sigma c r) s =
      fderiv ℝ (taylorModel f p x) s +
        (sigma / c) • fderiv ℝ (fun z : E ↦ ‖z‖ ^ r) s := by
  have hT := (hasFDerivAt_taylorModel f p x s).differentiableAt.hasFDerivAt
  rw [fderiv_norm_rpow s hr]
  exact (hT.add ((hasFDerivAt_norm_rpow s hr).const_smul (sigma / c))).fderiv

/-- A gradient remainder and a model residual control the derivative at the trial point.
The radial contribution is explicit, including the normalization `c`. -/
theorem fderiv_step_lower_bound {f : E → ℝ} {p : ℕ} {x s : E}
    {sigma c r A beta theta : ℝ} (hsigma : 0 ≤ sigma) (hc : 0 < c) (hr : 1 < r)
    (hrem : ‖fderiv ℝ f (x + s) - fderiv ℝ (taylorModel f p x) s‖ ≤
      A * ‖s‖ ^ ((p : ℝ) + beta - 1))
    (hres : ‖fderiv ℝ (regularizedModel f p x sigma c r) s‖ ≤
      theta * ‖s‖ ^ (r - 1)) :
    ‖fderiv ℝ f (x + s)‖ ≤ A * ‖s‖ ^ ((p : ℝ) + beta - 1) +
      (sigma / c * r + theta) * ‖s‖ ^ (r - 1) := by
  have hrad : ‖(sigma / c) • fderiv ℝ (fun z : E ↦ ‖z‖ ^ r) s‖ =
      (sigma / c * r) * ‖s‖ ^ (r - 1) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hsigma hc.le),
      norm_fderiv_norm_id_rpow s hr]
    ring
  have hdecomp : fderiv ℝ f (x + s) =
      (fderiv ℝ f (x + s) - fderiv ℝ (taylorModel f p x) s) +
      (fderiv ℝ (regularizedModel f p x sigma c r) s -
        (sigma / c) • fderiv ℝ (fun z : E ↦ ‖z‖ ^ r) s) := by
    rw [fderiv_regularizedModel _ _ _ _ _ _ hr]
    abel
  calc
    ‖fderiv ℝ f (x + s)‖ ≤
        ‖fderiv ℝ f (x + s) - fderiv ℝ (taylorModel f p x) s‖ +
          ‖fderiv ℝ (regularizedModel f p x sigma c r) s -
            (sigma / c) • fderiv ℝ (fun z : E ↦ ‖z‖ ^ r) s‖ := by
      nth_rw 1 [hdecomp]
      exact norm_add_le _ _
    _ ≤ A * ‖s‖ ^ ((p : ℝ) + beta - 1) +
        (theta * ‖s‖ ^ (r - 1) + (sigma / c * r) * ‖s‖ ^ (r - 1)) := by
      exact add_le_add hrem ((norm_sub_le _ _).trans (add_le_add hres hrad.le))
    _ = _ := by ring

variable [CompleteSpace E]

/-- A Taylor gradient remainder and model gradient residual give the gradient bound at `x+s`. -/
theorem gradient_step_lower_bound {f : E → ℝ} {p : ℕ} {x s : E}
    {sigma c r A beta theta : ℝ} (hsigma : 0 ≤ sigma) (hc : 0 < c) (hr : 1 < r)
    (hrem : ‖gradient f (x + s) - gradient (taylorModel f p x) s‖ ≤
      A * ‖s‖ ^ ((p : ℝ) + beta - 1))
    (hres : ‖gradient (regularizedModel f p x sigma c r) s‖ ≤
      theta * ‖s‖ ^ (r - 1)) :
    ‖gradient f (x + s)‖ ≤ A * ‖s‖ ^ ((p : ℝ) + beta - 1) +
      (sigma / c * r + theta) * ‖s‖ ^ (r - 1) := by
  have hnorm (g : E → ℝ) (y : E) : ‖gradient g y‖ = ‖fderiv ℝ g y‖ := by
    simp [gradient]
  have hdiff : ‖gradient f (x + s) - gradient (taylorModel f p x) s‖ =
      ‖fderiv ℝ f (x + s) - fderiv ℝ (taylorModel f p x) s‖ := by
    simp only [gradient, ← map_sub]
    exact (InnerProductSpace.toDual ℝ E).symm.norm_map _
  rw [hnorm]
  rw [hdiff] at hrem
  rw [hnorm] at hres
  exact fderiv_step_lower_bound hsigma hc hr hrem hres

end InnerProduct

end Optimization.RegularizedTaylorModel
