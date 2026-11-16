/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Positive
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.NormPow

/-!
# Quadratic and regularized quadratic models

Let $E$ be a real inner product space, let $H : E \to E$ be a continuous linear operator, and let
$g \in E$. The **quadratic model** of a step $s \in E$ is
$$m(s) = \langle g, s \rangle + \tfrac12 \langle s, H s \rangle,$$
and for real numbers $\sigma$ and $r$ the **regularized model** is
$m^R(s) = m(s) + \frac{\sigma}{r} \|s\|^r$. These are (8.1.1) and (8.1.4) of [cartis2022evaluation].
The file gives their gradients, the Hessian of $m^R$, and their values at a solution of a shifted
linear system. Most results need $H$ to be symmetric.

The central algebraic fact of the subproblem theory is the **shifted-system identity**: if
$(H + \mu I) s = -g$ and $H$ is symmetric, then for every $u \in E$
$$m(u) - m(s) = \tfrac12 \langle u - s, (H + \mu I)(u - s) \rangle + \tfrac{\mu}{2} \left(\|s\|^2 -
  \|u\|^2\right).$$
The global optimality, uniqueness and value formulas for the trust-region and regularization
subproblems follow from it.

## Main definitions

* `Subproblem.quadModel`: the quadratic model $m(s) = \langle g, s \rangle + \frac12 \langle s, H s
  \rangle$.
* `Subproblem.regModel`: the regularized model $m^R(s) = m(s) + \frac{\sigma}{r} \|s\|^r$.
* `Subproblem.regModelHessian`: the operator $H + \lambda I + (r - 2) \lambda \, \hat s \hat s^T$
  with $\lambda = \sigma \|s\|^{r-2}$ and $\hat s = s / \|s\|$, which is the Hessian of $m^R$ at $s$
  for $r > 2$.

## Main results

* `Subproblem.hasGradientAt_quadModel`: for symmetric $H$, the gradient of $m$ at $s$ is $g + H s$.
* `Subproblem.hasGradientAt_regModel`: for symmetric $H$ and $r > 1$, the gradient of $m^R$ at $s$
  is $g + H s + \sigma \|s\|^{r-2} s$.
* `Subproblem.hasFDerivAt_gradient_regModel`: for $r > 2$, the derivative of the gradient map of
  $m^R$ at every $s$, including $s = 0$, is `Subproblem.regModelHessian`.
* `Subproblem.inner_regModelHessian_ge`: for $\sigma \ge 0$ and $r \ge 2$, the rank-one part of the
  Hessian of $m^R$ is positive semidefinite.
* `Subproblem.quadModel_sub_eq_of_shifted`: the shifted-system identity.
* `Subproblem.quadModel_eq_of_shifted`: if $(H + \mu I) s = -g$, then $m(s) = \frac12 (\langle g, s
  \rangle - \mu \|s\|^2)$.
* `Subproblem.regModel_eq_of_shifted` and `Subproblem.regModel_eq_of_shifted_general`: the value of
  $m^R$ at a solution of a shifted system.
* `Subproblem.hasGradientAt_regModel_of_shifted`: at a solution of $(H + \mu I) s = -g$, the
  gradient of $m^R$ is $(\sigma \|s\|^{r-2} - \mu) s$.

## Implementation notes

* The source measures steps in a scaling norm $\|\cdot\|_M$. Here that norm is absorbed into the
  inner product of $E$.
* The exponent $r$ is real, and $\|s\|^r$ is `Real.rpow`. The conventions $0^0 = 1$ and $0^x = 0$
  for $x \neq 0$ fix the values at $s = 0$.
* The gradient results need $E$ to be complete, so that a derivative $\langle v, \cdot \rangle$ is
  represented by the vector $v$. The derivative results do not.
-/

open Filter Topology Asymptotics
open scoped RealInnerProductSpace

noncomputable section

namespace Subproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **quadratic model** of a step $s \in E$, for $g \in E$ and a continuous linear operator $H$
on $E$:
$$m(s) = \langle g, s \rangle + \tfrac12 \langle s, H s \rangle.$$

This is (8.1.1) of [cartis2022evaluation]. -/
def quadModel (g : E) (H : E →L[ℝ] E) (s : E) : ℝ := ⟪g, s⟫ + (1 / 2) * ⟪s, H s⟫

/-- The **regularized model** of a step $s \in E$, for $g \in E$, a continuous linear operator $H$
on $E$, and real numbers $\sigma$ and $r$:
$$m^R(s) = m(s) + \frac{\sigma}{r} \|s\|^r,$$
where $m$ is the quadratic model `Subproblem.quadModel`.

This is (8.1.4) of [cartis2022evaluation], with the scaling norm of the source absorbed into the
inner product of $E$. The power $\|s\|^r$ is `Real.rpow`. For $r = 0$ the term $\sigma / r$ is
$0$ in Lean, so $m^R = m$. -/
def regModel (g : E) (H : E →L[ℝ] E) (σ r : ℝ) (s : E) : ℝ := quadModel g H s + σ / r * ‖s‖ ^ r

/-- The quadratic model is $m(s) = \langle g, s \rangle + \frac12 \langle s, H s \rangle$, by
definition. -/
theorem quadModel_def (g : E) (H : E →L[ℝ] E) (s : E) :
    quadModel g H s = ⟪g, s⟫ + (1 / 2) * ⟪s, H s⟫ := rfl

/-- The regularized model is $m^R(s) = m(s) + \frac{\sigma}{r} \|s\|^r$, by definition. -/
theorem regModel_def (g : E) (H : E →L[ℝ] E) (σ r : ℝ) (s : E) :
    regModel g H σ r s = quadModel g H s + σ / r * ‖s‖ ^ r := rfl

/-- The quadratic model vanishes at the origin: $m(0) = 0$. -/
@[simp]
theorem quadModel_zero (g : E) (H : E →L[ℝ] E) : quadModel g H 0 = 0 := by simp [quadModel]

/-- For $r \neq 0$, the regularized model vanishes at the origin: $m^R(0) = 0$. -/
@[simp]
theorem regModel_zero (g : E) (H : E →L[ℝ] E) (σ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    regModel g H σ r 0 = 0 := by simp [regModel, Real.zero_rpow hr]

/-- The quadratic model $m$ is continuous on $E$. -/
theorem continuous_quadModel (g : E) (H : E →L[ℝ] E) : Continuous (quadModel g H) := by
  unfold quadModel; fun_prop

/-- For $r \ge 0$, the regularized model $m^R$ is continuous on $E$. -/
theorem continuous_regModel (g : E) (H : E →L[ℝ] E) (σ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Continuous (regModel g H σ r) := by
  unfold regModel
  exact (continuous_quadModel g H).add
    (continuous_const.mul (continuous_norm.rpow_const fun _ => Or.inr hr))

section Symmetric

variable {g : E} {H : E →L[ℝ] E}

/-- If $H$ is symmetric, then $\langle H x, y \rangle = \langle x, H y \rangle$ for all
$x, y \in E$, stated for the continuous linear operator $H$ without coercion to a linear map. -/
theorem inner_apply_comm_of_isSymmetric (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (x y : E) :
    ⟪H x, y⟫ = ⟪x, H y⟫ :=
  hH x y

/-- Exact second-order expansion of the quadratic model: if $H$ is symmetric, then for all
$s, h \in E$
$$m(s + h) = m(s) + \langle g + H s, h \rangle + \tfrac12 \langle h, H h \rangle.$$
-/
theorem quadModel_add (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (s h : E) :
    quadModel g H (s + h) = quadModel g H s + ⟪g + H s, h⟫ + (1 / 2) * ⟪h, H h⟫ := by
  have hs : ⟪h, H s⟫ = ⟪H s, h⟫ := real_inner_comm _ _
  have hs' : ⟪s, H h⟫ = ⟪H s, h⟫ := (inner_apply_comm_of_isSymmetric hH s h).symm
  simp only [quadModel, map_add, inner_add_left, inner_add_right, hs, hs']
  ring

/-- Exact expansion of the quadratic model along a line: if $H$ is symmetric, then for all
$s, v \in E$ and $t \in \mathbb{R}$
$$m(s + t v) = m(s) + t \langle g + H s, v \rangle + \frac{t^2}{2} \langle v, H v \rangle.$$
-/
theorem quadModel_add_smul (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (s v : E) (t : ℝ) :
    quadModel g H (s + t • v) =
      quadModel g H s + t * ⟪g + H s, v⟫ + t ^ 2 / 2 * ⟪v, H v⟫ := by
  rw [quadModel_add hH, map_smul, inner_smul_right, inner_smul_left, inner_smul_right]
  simp only [conj_trivial]
  ring

/-- If $H$ is symmetric, then the quadratic model $m$ has the Fréchet derivative
$h \mapsto \langle g + H s, h \rangle$ at every $s \in E$. The space $E$ need not be complete. -/
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

/-- Let $E$ be a real Hilbert space and $f : E \to \mathbb{R}$. If $f$ has the Fréchet derivative
$h \mapsto \langle v, h \rangle$ at $x$, then $f$ has the gradient $v$ at $x$. -/
theorem hasGradientAt_of_hasFDerivAt_innerSL [CompleteSpace E] {f : E → ℝ} {v x : E}
    (hf : HasFDerivAt f (innerSL ℝ v) x) : HasGradientAt f v x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hf using 1
  ext y
  simp [InnerProductSpace.toDual_apply_apply]

/-- Let $E$ be a real Hilbert space and let $H$ be symmetric. Then the gradient of the quadratic
model at every $s \in E$ is
$$\nabla m(s) = g + H s.$$

This is (8.2.34) of [cartis2022evaluation] with $\sigma = 0$. -/
theorem hasGradientAt_quadModel [CompleteSpace E] (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (s : E) :
    HasGradientAt (quadModel g H) (g + H s) s :=
  hasGradientAt_of_hasFDerivAt_innerSL (hasFDerivAt_quadModel hH s)

/-- Let $H$ be symmetric and $r > 1$. Then the regularized model $m^R$ has the Fréchet derivative $h
\mapsto \langle g + H s + \sigma \|s\|^{r-2} s, h \rangle$ at every $s \in E$. -/
theorem hasFDerivAt_regModel (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (σ : ℝ) {r : ℝ} (hr : 1 < r)
    (s : E) :
    HasFDerivAt (regModel g H σ r) (innerSL ℝ (g + H s + (σ * ‖s‖ ^ (r - 2)) • s)) s := by
  refine ((hasFDerivAt_quadModel (g := g) hH s).add
    ((hasFDerivAt_norm_rpow s hr).const_mul (σ / r))).congr_fderiv ?_
  have hr0 : r ≠ 0 := by linarith
  ext h
  simp
  field_simp

/-- Let $E$ be a real Hilbert space, let $H$ be symmetric, and let $\sigma \in \mathbb{R}$ and
$r > 1$. Then the gradient of the regularized model at every $s \in E$ is
$$\nabla m^R(s) = g + H s + \sigma \|s\|^{r-2} s.$$

This is the first line of (8.2.34) of [cartis2022evaluation], where
$\lambda = \sigma \|s\|^{r-2}$. At $s = 0$ the last term is $0$. -/
theorem hasGradientAt_regModel [CompleteSpace E] (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (σ : ℝ)
    {r : ℝ} (hr : 1 < r) (s : E) :
    HasGradientAt (regModel g H σ r) (g + H s + (σ * ‖s‖ ^ (r - 2)) • s) s :=
  hasGradientAt_of_hasFDerivAt_innerSL (hasFDerivAt_regModel hH σ hr s)

end Symmetric

/-- The **Hessian of the regularized model** at $s \in E$, for a continuous linear operator $H$ on
$E$ and real numbers $\sigma$ and $r$:
$$\nabla^2 m^R(s) = H + \lambda I + (r - 2) \lambda \frac{s}{\|s\|}
  \left(\frac{s}{\|s\|}\right)^T, \qquad \lambda = \sigma \|s\|^{r-2}.$$

This is the second line of (8.2.34) of [cartis2022evaluation]. The definition writes the
operator as $H + \sigma \|s\|^{r-2} I + (r - 2) \sigma \|s\|^{r-4} \, s \langle s, \cdot
\rangle$, with the powers given by `Real.rpow`. At $s = 0$ the value is $H + \sigma I$ for
$r = 2$ and $H$ for every other $r$. `Subproblem.hasFDerivAt_gradient_regModel` shows that it is
the derivative of the gradient for $r > 2$. -/
def regModelHessian (H : E →L[ℝ] E) (σ r : ℝ) (s : E) : E →L[ℝ] E :=
  H + (σ * ‖s‖ ^ (r - 2)) • (1 : E →L[ℝ] E) +
    ((r - 2) * σ * ‖s‖ ^ (r - 4)) • (innerSL ℝ s).smulRight s

/-- The Hessian of the regularized model applied to $v \in E$ is
$$\nabla^2 m^R(s) v = H v + \sigma \|s\|^{r-2} v + (r - 2) \sigma \|s\|^{r-4} \langle s, v
  \rangle s.$$
-/
theorem regModelHessian_apply (H : E →L[ℝ] E) (σ r : ℝ) (s v : E) :
    regModelHessian H σ r s v =
      H v + (σ * ‖s‖ ^ (r - 2)) • v + ((r - 2) * σ * ‖s‖ ^ (r - 4) * ⟪s, v⟫) • s := by
  simp [regModelHessian, mul_smul]

/-- For $r > 2$, the Hessian of the regularized model at the origin is $H$. -/
theorem regModelHessian_zero (H : E →L[ℝ] E) (σ : ℝ) {r : ℝ} (hr : 2 < r) :
    regModelHessian H σ r 0 = H := by
  ext v
  simp [regModelHessian_apply, Real.zero_rpow (show r - 2 ≠ 0 by linarith)]

/-- For $r > 2$, the map $s \mapsto \sigma \|s\|^{r-2} s$, which is the regularization part of the
gradient of $m^R$, has the Fréchet derivative $0$ at the origin. -/
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

/-- For $r > 2$, the map $s \mapsto \sigma \|s\|^{r-2} s$, which is the regularization part of the
gradient of $m^R$, has at every $s \in E$ the Fréchet derivative
$$\sigma \|s\|^{r-2} I + (r - 2) \sigma \|s\|^{r-4} \, s \langle s, \cdot \rangle.$$
-/
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

/-- Let $g \in E$, let $H$ be a continuous linear operator on $E$, and let $\sigma \in \mathbb{R}$
and $r > 2$. Then at every $s \in E$, including $s = 0$, the map
$u \mapsto g + H u + \sigma \|u\|^{r-2} u$ has the Fréchet derivative $\nabla^2 m^R(s)$, the
operator `Subproblem.regModelHessian H σ r s`.

For symmetric $H$ on a Hilbert space, this map is the gradient of $m^R$ by
`Subproblem.hasGradientAt_regModel`. So `Subproblem.regModelHessian` is the Hessian of $m^R$, as
in (8.2.34) of [cartis2022evaluation]. -/
theorem hasFDerivAt_gradient_regModel (g : E) (H : E →L[ℝ] E) (σ : ℝ) {r : ℝ} (hr : 2 < r)
    (s : E) :
    HasFDerivAt (fun u : E => g + H u + (σ * ‖u‖ ^ (r - 2)) • u) (regModelHessian H σ r s) s := by
  have h := ((hasFDerivAt_const g s).add H.hasFDerivAt).add
    (hasFDerivAt_norm_rpow_smul_self σ hr s)
  convert h using 1
  simp [regModelHessian, add_assoc]

/-- Let $H$ be a continuous linear operator on $E$, and let $\sigma \ge 0$ and $r \ge 2$. Then for
all $s, v \in E$
$$\langle v, (H + \sigma \|s\|^{r-2} I) v \rangle \le \langle v, \nabla^2 m^R(s) v \rangle.$$
That is, the rank-one part of the Hessian of the regularized model is positive semidefinite. -/
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

/-- If $(H + \mu I) s = -g$, then the gradient $g + H s$ of the quadratic model at $s$ equals
$-\mu s$. -/
theorem add_apply_eq_of_shifted {μ : ℝ} {s : E} (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) :
    g + H s = -(μ • s) := by
  have hg : g = -(H s + μ • s) := by
    rw [← neg_neg g, ← hs]; simp
  rw [hg]; abel

/-- The **shifted-system identity.** Let $H$ be symmetric, let $\mu \in \mathbb{R}$, and let
$s \in E$ satisfy $(H + \mu I) s = -g$. Then for every $u \in E$
$$m(u) - m(s) = \tfrac12 \langle u - s, (H + \mu I)(u - s) \rangle + \frac{\mu}{2}
  \left(\|s\|^2 - \|u\|^2\right).$$
-/
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

/-- If $(H + \mu I) s = -g$, then $\langle g, s \rangle = -\langle s, (H + \mu I) s \rangle$. -/
theorem inner_eq_of_shifted {μ : ℝ} {s : E} (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) :
    ⟪g, s⟫ = -⟪s, (H + μ • (1 : E →L[ℝ] E)) s⟫ := by
  rw [hs, inner_neg_right, real_inner_comm, neg_neg]

/-- Let $\mu \in \mathbb{R}$ and let $s \in E$ satisfy $(H + \mu I) s = -g$. Then the value of the
quadratic model at $s$ is
$$m(s) = \tfrac12 \left(\langle g, s \rangle - \mu \|s\|^2\right).$$

This uses (8.3.4) of [cartis2022evaluation] and is the first step of the proof of (8.3.5). The
operator $H$ need not be symmetric. -/
theorem quadModel_eq_of_shifted {μ : ℝ} {s : E} (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) :
    quadModel g H s = (1 / 2) * (⟪g, s⟫ - μ * ‖s‖ ^ 2) := by
  have h := inner_eq_of_shifted hs
  simp only [add_apply, smul_apply,
    one_apply_eq_self, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq] at h
  rw [quadModel]
  linarith

omit [InnerProductSpace ℝ E] in
/-- For all real $\sigma$ and $r$ and every vector $s$ of a normed space,
$$\frac{\sigma}{r} \|s\|^r = \|s\|^2 \left(\frac{\sigma}{r} \|s\|^{r-2}\right).$$
For $r = 0$ both sides are $0$, because $\sigma / 0 = 0$ in Lean. -/
theorem div_mul_norm_rpow_eq (σ r : ℝ) (s : E) :
    σ / r * ‖s‖ ^ r = ‖s‖ ^ 2 * (σ / r * ‖s‖ ^ (r - 2)) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · rw [show r = (r - 2) + 2 by ring, Real.rpow_add' (norm_nonneg _) (by simpa using hr)]
    norm_num
    ring

/-- Let $\sigma \in \mathbb{R}$ and $r \neq 0$, and let $s \in E$ satisfy $(H + \lambda I) s = -g$
with $\lambda = \sigma \|s\|^{r-2}$. Then the value of the regularized model at $s$ is
$$m^R(s) = \tfrac12 \left(\langle g, s \rangle - \frac{r - 2}{r} \lambda \|s\|^2\right).$$

This is the first step of the proof of (8.3.3) of [cartis2022evaluation]. -/
theorem regModel_eq_of_shifted {σ r : ℝ} (hr : r ≠ 0) {s : E}
    (hs : (H + (σ * ‖s‖ ^ (r - 2)) • (1 : E →L[ℝ] E)) s = -g) :
    regModel g H σ r s =
      (1 / 2) * (⟪g, s⟫ - ((r - 2) / r) * (σ * ‖s‖ ^ (r - 2)) * ‖s‖ ^ 2) := by
  rw [regModel, quadModel_eq_of_shifted hs, div_mul_norm_rpow_eq]
  field_simp
  ring

/-- Let $\sigma, r, \mu \in \mathbb{R}$ and let $s \in E$ satisfy $(H + \mu I) s = -g$, where $\mu$
need not equal $\sigma \|s\|^{r-2}$. Then the value of the regularized model at $s$ is
$$m^R(s) = -\tfrac12 \langle s, (H + \mu I) s \rangle + \|s\|^2 \left(\frac{\sigma}{r}
  \|s\|^{r-2} - \frac{\mu}{2}\right).$$

This is used in the proof of Theorem 9.3.2 of [cartis2022evaluation]. -/
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

/-- Let $E$ be a real Hilbert space, let $H$ be symmetric, let $\sigma \in \mathbb{R}$ and $r > 1$,
and let $s \in E$ satisfy $(H + \mu I) s = -g$. Then the gradient of the regularized model at
$s$ is
$$\nabla m^R(s) = (\sigma \|s\|^{r-2} - \mu) s.$$

This is used in the proof of Theorem 9.3.2 of [cartis2022evaluation]. -/
theorem hasGradientAt_regModel_of_shifted [CompleteSpace E] (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (σ : ℝ) {r : ℝ} (hr : 1 < r) {μ : ℝ} {s : E} (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) :
    HasGradientAt (regModel g H σ r) ((σ * ‖s‖ ^ (r - 2) - μ) • s) s := by
  convert hasGradientAt_regModel hH σ hr s using 1
  rw [add_apply_eq_of_shifted hs, sub_smul]
  abel

/-- If $(H + \mu I) s = -g$ and $(H + \mu' I) s = -g$, then $(\mu - \mu') s = 0$. So two shifts that
solve the same shifted system at the same nonzero point are equal. -/
theorem sub_smul_eq_zero_of_shifted {μ μ' : ℝ} {s : E} (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g)
    (hs' : (H + μ' • (1 : E →L[ℝ] E)) s = -g) : (μ - μ') • s = 0 := by
  have h := hs.trans hs'.symm
  simp only [add_apply, smul_apply, one_apply_eq_self] at h
  rw [sub_smul, sub_eq_zero]
  exact add_left_cancel h

end Shifted

end Subproblem

end
