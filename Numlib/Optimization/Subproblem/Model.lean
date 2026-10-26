import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Positive
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.NormPow

/-!
# Quadratic and regularized quadratic models

The quadratic model `m(s) = ⟪g, s⟫ + ½ ⟪s, H s⟫` of a step `s` and its regularization
`m^R(s) = m(s) + σ/r ‖s‖^r`, on a real inner product space `E`, for a continuous linear operator
`H : E →L[ℝ] E` (symmetric wherever it matters) and a vector `g : E`
([cartis2022evaluation] (8.1.1), (8.1.4)). The book's scaling norm `‖·‖_M` is absorbed into the
inner product of `E`.

The algebraic heart of the subproblem theory is the *shifted-system identity*
`quadModel_sub_eq_of_shifted`: if `(H + μ) s = -g` then for every `u`
`m(u) - m(s) = ½ ⟪u - s, (H + μ)(u - s)⟫ + μ/2 (‖s‖² - ‖u‖²)`. The global optimality, uniqueness
and value formulas of the trust-region and regularization subproblems are corollaries of it.

## Main definitions

* `Subproblem.quadModel g H s`: the quadratic model.
* `Subproblem.regModel g H σ r s`: the regularized model (`‖s‖ ^ r` is `Real.rpow`).
* `Subproblem.regModelHessian H σ r s`: the Hessian `H + λ I + (r-2) λ (s/‖s‖)(s/‖s‖)ᵀ` of the
  regularized model, `λ = σ ‖s‖^{r-2}`; it is the derivative of the gradient for `r > 2`
  (`hasFDerivAt_gradient_regModel`), and at `s = 0` it reduces to `H` only for `r > 2`.

## Main statements

* `Subproblem.hasGradientAt_quadModel`, `Subproblem.hasGradientAt_regModel`,
  `Subproblem.hasFDerivAt_gradient_regModel`: gradients and Hessian ([cartis2022evaluation]
  (8.2.34)).
* `Subproblem.inner_regModelHessian_ge`: the rank-one part of the Hessian is positive semidefinite.
* `Subproblem.quadModel_sub_eq_of_shifted`: the shifted-system identity.
* `Subproblem.quadModel_eq_of_shifted`, `Subproblem.regModel_eq_of_shifted`,
  `Subproblem.regModel_eq_of_shifted_general`: model values at a solution of a shifted system.
-/

open Filter Topology Asymptotics
open scoped RealInnerProductSpace

noncomputable section

namespace Subproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **quadratic model** `m(s) = ⟪g, s⟫ + ½ ⟪s, H s⟫` ([cartis2022evaluation] (8.1.1)). -/
def quadModel (g : E) (H : E →L[ℝ] E) (s : E) : ℝ := ⟪g, s⟫ + (1 / 2) * ⟪s, H s⟫

/-- The **regularized model** `m^R(s) = m(s) + σ/r ‖s‖^r` with a real exponent `r`
([cartis2022evaluation] (8.1.4), the scaling norm absorbed into the inner product). -/
def regModel (g : E) (H : E →L[ℝ] E) (σ r : ℝ) (s : E) : ℝ := quadModel g H s + σ / r * ‖s‖ ^ r

/-- Unfolding lemma for `quadModel`. -/
theorem quadModel_def (g : E) (H : E →L[ℝ] E) (s : E) :
    quadModel g H s = ⟪g, s⟫ + (1 / 2) * ⟪s, H s⟫ := rfl

/-- Unfolding lemma for `regModel`. -/
theorem regModel_def (g : E) (H : E →L[ℝ] E) (σ r : ℝ) (s : E) :
    regModel g H σ r s = quadModel g H s + σ / r * ‖s‖ ^ r := rfl

@[simp]
theorem quadModel_zero (g : E) (H : E →L[ℝ] E) : quadModel g H 0 = 0 := by simp [quadModel]

@[simp]
theorem regModel_zero (g : E) (H : E →L[ℝ] E) (σ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    regModel g H σ r 0 = 0 := by simp [regModel, Real.zero_rpow hr]

/-- The quadratic model is continuous. -/
theorem continuous_quadModel (g : E) (H : E →L[ℝ] E) : Continuous (quadModel g H) := by
  unfold quadModel; fun_prop

/-- The regularized model is continuous for a nonnegative exponent. -/
theorem continuous_regModel (g : E) (H : E →L[ℝ] E) (σ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Continuous (regModel g H σ r) := by
  unfold regModel
  exact (continuous_quadModel g H).add
    (continuous_const.mul (continuous_norm.rpow_const fun _ => Or.inr hr))

section Symmetric

variable {g : E} {H : E →L[ℝ] E}

/-- Symmetry of `H` in the form `⟪H x, y⟫ = ⟪x, H y⟫` without coercions. -/
theorem inner_apply_comm_of_isSymmetric (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (x y : E) :
    ⟪H x, y⟫ = ⟪x, H y⟫ :=
  hH x y

/-- Exact second-order expansion of the quadratic model:
`m(s + h) = m(s) + ⟪g + H s, h⟫ + ½ ⟪h, H h⟫` for symmetric `H`. -/
theorem quadModel_add (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (s h : E) :
    quadModel g H (s + h) = quadModel g H s + ⟪g + H s, h⟫ + (1 / 2) * ⟪h, H h⟫ := by
  have hs : ⟪h, H s⟫ = ⟪H s, h⟫ := real_inner_comm _ _
  have hs' : ⟪s, H h⟫ = ⟪H s, h⟫ := (inner_apply_comm_of_isSymmetric hH s h).symm
  simp only [quadModel, map_add, inner_add_left, inner_add_right, hs, hs']
  ring

/-- Exact expansion along a line: `m(s + t v) = m(s) + t ⟪g + H s, v⟫ + t²/2 ⟪v, H v⟫`. -/
theorem quadModel_add_smul (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (s v : E) (t : ℝ) :
    quadModel g H (s + t • v) =
      quadModel g H s + t * ⟪g + H s, v⟫ + t ^ 2 / 2 * ⟪v, H v⟫ := by
  rw [quadModel_add hH, map_smul, inner_smul_right, inner_smul_left, inner_smul_right]
  simp only [conj_trivial]
  ring

/-- The quadratic model has derivative `⟪g + H s, ·⟫` at `s` (no completeness needed). -/
theorem hasFDerivAt_quadModel (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (s : E) :
    HasFDerivAt (quadModel g H) (innerSL ℝ (g + H s)) s := by
  have h₁ : HasFDerivAt (fun u : E => ⟪g, u⟫) (innerSL ℝ g) s := (innerSL ℝ g).hasFDerivAt
  have h₂ : HasFDerivAt (fun u : E => ⟪u, H u⟫)
      ((fderivInnerCLM ℝ (s, H s)).comp ((ContinuousLinearMap.id ℝ E).prod H)) s :=
    (hasFDerivAt_id s).inner ℝ H.hasFDerivAt
  refine (h₁.add (h₂.const_mul (1 / 2))).congr_fderiv ?_
  ext h
  have hs : ⟪h, H s⟫ = ⟪H s, h⟫ := real_inner_comm _ _
  have hs' : ⟪s, H h⟫ = ⟪H s, h⟫ := (inner_apply_comm_of_isSymmetric hH s h).symm
  simp [fderivInnerCLM_apply, hs, hs']
  ring

/-- A derivative of the form `⟪v, ·⟫` is the gradient `v`. -/
theorem hasGradientAt_of_hasFDerivAt_innerSL [CompleteSpace E] {f : E → ℝ} {v x : E}
    (hf : HasFDerivAt f (innerSL ℝ v) x) : HasGradientAt f v x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hf using 1
  ext y
  simp [InnerProductSpace.toDual_apply_apply]

/-- The gradient of the quadratic model is `g + H s` ([cartis2022evaluation] (8.2.34) with
`σ = 0`). -/
theorem hasGradientAt_quadModel [CompleteSpace E] (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (s : E) :
    HasGradientAt (quadModel g H) (g + H s) s :=
  hasGradientAt_of_hasFDerivAt_innerSL (hasFDerivAt_quadModel hH s)

/-- The regularized model has derivative `⟪g + H s + σ ‖s‖^{r-2} s, ·⟫` at `s`, for `1 < r`. -/
theorem hasFDerivAt_regModel (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (σ : ℝ) {r : ℝ} (hr : 1 < r)
    (s : E) :
    HasFDerivAt (regModel g H σ r) (innerSL ℝ (g + H s + (σ * ‖s‖ ^ (r - 2)) • s)) s := by
  refine ((hasFDerivAt_quadModel (g := g) hH s).add
    ((hasFDerivAt_norm_rpow s hr).const_mul (σ / r))).congr_fderiv ?_
  have hr0 : r ≠ 0 := by linarith
  ext h
  simp
  field_simp

/-- The gradient of the regularized model is `g + H s + σ ‖s‖^{r-2} s` for `1 < r`
([cartis2022evaluation] (8.2.34), first line, with `λ = σ ‖s‖^{r-2}`; at `s = 0` the last term
is `0`). -/
theorem hasGradientAt_regModel [CompleteSpace E] (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (σ : ℝ)
    {r : ℝ} (hr : 1 < r) (s : E) :
    HasGradientAt (regModel g H σ r) (g + H s + (σ * ‖s‖ ^ (r - 2)) • s) s :=
  hasGradientAt_of_hasFDerivAt_innerSL (hasFDerivAt_regModel hH σ hr s)

end Symmetric

/-- The **Hessian of the regularized model** at `s`,
`H + λ I + (r - 2) λ (s/‖s‖)(s/‖s‖)ᵀ` with `λ = σ ‖s‖^{r-2}` ([cartis2022evaluation] (8.2.34),
second line), written as `H + (σ ‖s‖^{r-2}) • 1 + ((r - 2) σ ‖s‖^{r-4}) • s ⟪s, ·⟫`. At `s = 0`
it equals `H` when `r > 2` (`regModelHessian_zero`). -/
def regModelHessian (H : E →L[ℝ] E) (σ r : ℝ) (s : E) : E →L[ℝ] E :=
  H + (σ * ‖s‖ ^ (r - 2)) • (1 : E →L[ℝ] E) +
    ((r - 2) * σ * ‖s‖ ^ (r - 4)) • (innerSL ℝ s).smulRight s

/-- The Hessian of the regularized model applied to a vector. -/
theorem regModelHessian_apply (H : E →L[ℝ] E) (σ r : ℝ) (s v : E) :
    regModelHessian H σ r s v =
      H v + (σ * ‖s‖ ^ (r - 2)) • v + ((r - 2) * σ * ‖s‖ ^ (r - 4) * ⟪s, v⟫) • s := by
  simp [regModelHessian, mul_smul]

/-- At the origin the Hessian of the regularized model is `H`, for `r > 2`. -/
theorem regModelHessian_zero (H : E →L[ℝ] E) (σ : ℝ) {r : ℝ} (hr : 2 < r) :
    regModelHessian H σ r 0 = H := by
  ext v
  simp [regModelHessian_apply, Real.zero_rpow (show r - 2 ≠ 0 by linarith)]

/-- The derivative of the regularization part `s ↦ σ ‖s‖^{r-2} s` of the gradient vanishes at the
origin when `r > 2`. -/
theorem hasFDerivAt_norm_rpow_smul_self_zero (σ : ℝ) {r : ℝ} (hr : 2 < r) :
    HasFDerivAt (fun s : E => (σ * ‖s‖ ^ (r - 2)) • s) (0 : E →L[ℝ] E) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, norm_zero, smul_zero, sub_zero, zero_apply]
  have hc : Continuous fun s : E => σ * ‖s‖ ^ (r - 2) :=
    continuous_const.mul (continuous_norm.rpow_const fun _ => Or.inr (by linarith))
  have ht : Tendsto (fun s : E => σ * ‖s‖ ^ (r - 2)) (𝓝 0) (𝓝 0) := by
    have := hc.tendsto 0
    simpa [Real.zero_rpow (show r - 2 ≠ 0 by linarith)] using this
  have h := (isLittleO_one_iff ℝ).mpr ht |>.smul_isBigO (isBigO_refl (fun s : E => s) (𝓝 0))
  simpa using h

/-- The regularization part `s ↦ σ ‖s‖^{r-2} s` of the gradient has derivative
`σ ‖s‖^{r-2} I + (r - 2) σ ‖s‖^{r-4} s ⟪s, ·⟫` at every `s`, for `r > 2`. -/
theorem hasFDerivAt_norm_rpow_smul_self (σ : ℝ) {r : ℝ} (hr : 2 < r) (s : E) :
    HasFDerivAt (fun s : E => (σ * ‖s‖ ^ (r - 2)) • s)
      ((σ * ‖s‖ ^ (r - 2)) • (1 : E →L[ℝ] E) +
        ((r - 2) * σ * ‖s‖ ^ (r - 4)) • (innerSL ℝ s).smulRight s) s := by
  rcases eq_or_ne s 0 with rfl | hs
  · convert hasFDerivAt_norm_rpow_smul_self_zero (E := E) σ hr using 1
    simp [Real.zero_rpow (show r - 2 ≠ 0 by linarith)]
  · have hn := (hasFDerivAt_norm_rpow_of_ne_zero hs (r - 2)).const_mul σ
    refine (hn.smul (hasFDerivAt_id s)).congr_fderiv ?_
    rw [show r - 2 - 2 = r - 4 by ring]
    ext v
    simp only [add_apply, smul_apply,
      one_apply_eq_self, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, id_eq]
    module

/-- The gradient map `s ↦ g + H s + σ ‖s‖^{r-2} s` of the regularized model has derivative
`regModelHessian H σ r s` at every `s`, for `r > 2` (including `s = 0`); together with
`hasGradientAt_regModel`, `regModelHessian` is the Hessian of `regModel`
([cartis2022evaluation] (8.2.34)). -/
theorem hasFDerivAt_gradient_regModel (g : E) (H : E →L[ℝ] E) (σ : ℝ) {r : ℝ} (hr : 2 < r)
    (s : E) :
    HasFDerivAt (fun u : E => g + H u + (σ * ‖u‖ ^ (r - 2)) • u) (regModelHessian H σ r s) s := by
  have h := ((hasFDerivAt_const g s).add H.hasFDerivAt).add
    (hasFDerivAt_norm_rpow_smul_self σ hr s)
  convert h using 1
  simp [regModelHessian, add_assoc]

/-- The rank-one part of the Hessian of the regularized model is positive semidefinite:
`⟪v, ∇²m^R(s) v⟫ ≥ ⟪v, (H + σ ‖s‖^{r-2} I) v⟫` for `σ ≥ 0`, `r ≥ 2`. -/
theorem inner_regModelHessian_ge (H : E →L[ℝ] E) {σ r : ℝ} (hσ : 0 ≤ σ) (hr : 2 ≤ r) (s v : E) :
    ⟪v, (H + (σ * ‖s‖ ^ (r - 2)) • (1 : E →L[ℝ] E)) v⟫ ≤ ⟪v, regModelHessian H σ r s v⟫ := by
  rw [regModelHessian_apply]
  simp only [add_apply, smul_apply,
    one_apply_eq_self, inner_add_right, inner_smul_right]
  have h1 : 0 ≤ (r - 2) * σ * ‖s‖ ^ (r - 4) :=
    mul_nonneg (mul_nonneg (by linarith) hσ) (Real.rpow_nonneg (norm_nonneg _) _)
  have h2 : 0 ≤ (r - 2) * σ * ‖s‖ ^ (r - 4) * ⟪s, v⟫ * ⟪v, s⟫ := by
    rw [real_inner_comm v s, mul_assoc]
    exact mul_nonneg h1 (mul_self_nonneg _)
  linarith

section Shifted

variable {g : E} {H : E →L[ℝ] E}

/-- A solution of `(H + μ I) s = -g` makes the gradient `g + H s` of the quadratic model equal to
`-μ s`. -/
theorem add_apply_eq_of_shifted {μ : ℝ} {s : E} (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) :
    g + H s = -(μ • s) := by
  have hg : g = -(H s + μ • s) := by
    rw [← neg_neg g, ← hs]; simp
  rw [hg]; abel

/-- **Shifted-system identity.** If `(H + μ I) s = -g` with `H` symmetric, then for every `u`,
`m(u) - m(s) = ½ ⟪u - s, (H + μ I)(u - s)⟫ + μ/2 (‖s‖² - ‖u‖²)`. -/
theorem quadModel_sub_eq_of_shifted (hH : (H : E →ₗ[ℝ] E).IsSymmetric) {μ : ℝ} {s : E}
    (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) (u : E) :
    quadModel g H u - quadModel g H s =
      (1 / 2) * ⟪u - s, (H + μ • (1 : E →L[ℝ] E)) (u - s)⟫ + μ / 2 * (‖s‖ ^ 2 - ‖u‖ ^ 2) := by
  have hg := add_apply_eq_of_shifted hs
  have hu : u = s + (u - s) := by abel
  conv_lhs => rw [hu, quadModel_add hH, hg]
  rw [hu]
  simp only [add_sub_cancel_left, add_apply, smul_apply,
    one_apply_eq_self, inner_add_right, inner_smul_right, inner_neg_left,
    inner_smul_left, conj_trivial, ← real_inner_self_eq_norm_sq, inner_add_left]
  rw [real_inner_comm s (u - s)]
  ring

/-- If `(H + μ I) s = -g` with `H` symmetric, then `⟪g, s⟫ = -⟪s, (H + μ I) s⟫`. -/
theorem inner_eq_of_shifted {μ : ℝ} {s : E} (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) :
    ⟪g, s⟫ = -⟪s, (H + μ • (1 : E →L[ℝ] E)) s⟫ := by
  rw [hs, inner_neg_right, real_inner_comm, neg_neg]

/-- The value of the quadratic model at a solution of `(H + μ I) s = -g`:
`m(s) = ½ (⟪g, s⟫ - μ ‖s‖²)` (via [cartis2022evaluation] (8.3.4); the first step of the proof of
(8.3.5)). -/
theorem quadModel_eq_of_shifted {μ : ℝ} {s : E} (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) :
    quadModel g H s = (1 / 2) * (⟪g, s⟫ - μ * ‖s‖ ^ 2) := by
  have h := inner_eq_of_shifted hs
  simp only [add_apply, smul_apply,
    one_apply_eq_self, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq] at h
  rw [quadModel]
  linarith

omit [InnerProductSpace ℝ E] in
/-- `σ/r ‖s‖^r = ‖s‖² (σ/r ‖s‖^{r-2})`, for every real `r` (both sides vanish when `r = 0`). -/
theorem div_mul_norm_rpow_eq (σ r : ℝ) (s : E) :
    σ / r * ‖s‖ ^ r = ‖s‖ ^ 2 * (σ / r * ‖s‖ ^ (r - 2)) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · rw [show r = (r - 2) + 2 by ring, Real.rpow_add' (norm_nonneg _) (by simpa using hr)]
    norm_num
    ring

/-- The value of the regularized model at a solution of `(H + λ I) s = -g` with
`λ = σ ‖s‖^{r-2}` and `r ≠ 0`: `m^R(s) = ½ (⟪g, s⟫ - (r - 2)/r λ ‖s‖²)` (the first step of the
proof of [cartis2022evaluation] (8.3.3)). -/
theorem regModel_eq_of_shifted {σ r : ℝ} (hr : r ≠ 0) {s : E}
    (hs : (H + (σ * ‖s‖ ^ (r - 2)) • (1 : E →L[ℝ] E)) s = -g) :
    regModel g H σ r s =
      (1 / 2) * (⟪g, s⟫ - ((r - 2) / r) * (σ * ‖s‖ ^ (r - 2)) * ‖s‖ ^ 2) := by
  rw [regModel, quadModel_eq_of_shifted hs, div_mul_norm_rpow_eq]
  field_simp
  ring

/-- The value of the regularized model at a solution of `(H + μ I) s = -g`, for any `μ` (not
necessarily `σ ‖s‖^{r-2}`):
`m^R(s) = -½ ⟪s, (H + μ I) s⟫ + ‖s‖² (σ/r ‖s‖^{r-2} - μ/2)` ([cartis2022evaluation], proof of
Theorem 9.3.2). -/
theorem regModel_eq_of_shifted_general (σ r : ℝ) {μ : ℝ} {s : E}
    (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) :
    regModel g H σ r s =
      -(1 / 2) * ⟪s, (H + μ • (1 : E →L[ℝ] E)) s⟫ +
        ‖s‖ ^ 2 * (σ / r * ‖s‖ ^ (r - 2) - μ / 2) := by
  have h := inner_eq_of_shifted hs
  rw [regModel, div_mul_norm_rpow_eq, quadModel, h]
  simp only [add_apply, smul_apply,
    one_apply_eq_self, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
  ring

/-- At a solution of `(H + μ I) s = -g`, the gradient of the regularized model is
`(σ ‖s‖^{r-2} - μ) s` ([cartis2022evaluation], proof of Theorem 9.3.2). -/
theorem hasGradientAt_regModel_of_shifted [CompleteSpace E] (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (σ : ℝ) {r : ℝ} (hr : 1 < r) {μ : ℝ} {s : E} (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) :
    HasGradientAt (regModel g H σ r) ((σ * ‖s‖ ^ (r - 2) - μ) • s) s := by
  convert hasGradientAt_regModel hH σ hr s using 1
  rw [add_apply_eq_of_shifted hs, sub_smul]
  abel

/-- Two shifts solving the same shifted system at the same point differ by a multiple killing it:
if `(H + μ I) s = -g` and `(H + μ' I) s = -g` then `(μ - μ') • s = 0`. -/
theorem sub_smul_eq_zero_of_shifted {μ μ' : ℝ} {s : E} (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g)
    (hs' : (H + μ' • (1 : E →L[ℝ] E)) s = -g) : (μ - μ') • s = 0 := by
  have h := hs.trans hs'.symm
  simp only [add_apply, smul_apply, one_apply_eq_self] at h
  rw [sub_smul, sub_eq_zero]
  exact add_left_cancel h

end Shifted

end Subproblem

end
