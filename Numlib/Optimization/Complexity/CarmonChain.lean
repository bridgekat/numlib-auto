/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Numlib.Analysis.Calculus.LipschitzIteratedFDeriv
import Numlib.Optimization.Complexity.ResistingOracle

/-!
# The hard zero chain of Carmon, Duchi, Hinder and Sidford

This module constructs the difficult function of (4.2.6) and Lemma 4.2.5 of [cartis2022evaluation],
and proves the resulting lower bound for $p$-th order methods, Theorem 4.2.6 of
[cartis2022evaluation]. The construction follows Carmon, Duchi, Hinder and Sidford, *Lower bounds
for finding stationary points I*, §3.2, Lemmas 1–3. On $\mathbb{R}^T$, with coordinates
$x_0, \dots, x_{T-1}$, the function is
$$\mathrm{chain}_T(x) = -\Psi(1) \Phi(x_0) + \sum_{i=1}^{T-1} \big[ \Psi(-x_{i-1}) \Phi(-x_i) -
  \Psi(x_{i-1}) \Phi(x_i) \big],$$
where $\Psi(y) = 0$ for $y \le 1/2$, $\Psi(y) = \exp(1 - (2y - 1)^{-2})$ for $y > 1/2$, and
$$\Phi(y) = e^{1/2} \int_{-\infty}^y e^{-t^2/2} \, dt.$$
The first term $-\Psi(1) \Phi(x_0)$, with $\Psi(1) = 1$, is the one of Carmon et al. It makes the
gradient nonzero at $x = 0$, as Lemma 4.2.5(ii) requires.

The function is a zero chain: a method that only sees derivatives discovers at most one new
coordinate per iteration. Its gradient has norm greater than $1$ as long as some coordinate has
absolute value less than $1$, the gap $\mathrm{chain}_T(0) - \inf \mathrm{chain}_T$ is at most
$12T$, and its $(p + 1)$-st derivative is bounded independently of $T$. Scaling the chain then gives
a function in the class $\mathcal{F}(\Delta, p)$ on which every method needs many iterations.

## Main definitions

* `Optimization.CarmonChain.psi` and `Optimization.CarmonChain.phi`: the functions $\Psi$ and $\Phi$
  of (4.2.6), smooth, with bounded derivatives of every order.
* `Optimization.CarmonChain.chain`: the function $\mathrm{chain}_T$.
* `Optimization.CarmonChain.lipschitzConst`: an explicit bound on
  $\|\nabla^{p+1} \mathrm{chain}_T\|$ that does not depend on $T$.

## Main results

* `Optimization.CarmonChain.isZeroChain_chain`: Lemma 4.2.5(i), $\mathrm{chain}_T$ is a zero chain
  of every order.
* `Optimization.CarmonChain.exists_abs_partial_chain_gt_one`: Lemma 4.2.5(ii), the gradient has norm
  greater than $1$ when some $|x_i| < 1$.
* `Optimization.CarmonChain.chain_zero_sub_iInf_le`: Lemma 4.2.5(iii), $\mathrm{chain}_T(0) - \inf
  \mathrm{chain}_T \le 12T$.
* `Optimization.CarmonChain.norm_iteratedFDeriv_chain_le` and
  `Optimization.CarmonChain.lipschitzOn_iteratedFDeriv_chain`: Lemma 4.2.5(iv),
  $\nabla^p \mathrm{chain}_T$ is Lipschitz continuous with the constant
  `Optimization.CarmonChain.lipschitzConst p`, which does not depend on $T$.
* `Optimization.CarmonChain.lipschitzConst_le_exp`: the growth bound
  $\exp(\tfrac52 p \log p + c_1 p)$ on that constant in Lemma 4.2.5(iv), with $c_1 = 20$
  (`Optimization.CarmonChain.lipschitzConst_le_exp_twenty`).
* `Optimization.CarmonChain.le_classComplexity_smoothClass`: the lower bound of Theorem 4.2.6.

## Proof outline

The growth bound comes from bounds on the sums of the absolute values of the coefficients of the
polynomials that describe the derivatives of $\Psi$ and $\Phi$, together with $x^k e^{-x} \le k!$.
-/

open Real Polynomial Filter Topology Set MeasureTheory ContDiff

namespace Optimization

namespace CarmonChain

/-! ### The flat function $s \mapsto \exp(-s^{-2})$ -/

/-- The **flat function**: $\mathrm{flat}(s) = \exp(-1/s^2)$ for $s > 0$ and $\mathrm{flat}(s) = 0$
for $s \le 0$. It is smooth, and all its derivatives vanish at $0$, so it glues smoothly to $0$. -/
noncomputable def flat (s : ℝ) : ℝ :=
  if s ≤ 0 then 0 else exp (-(s ^ 2)⁻¹)

/-- $\mathrm{flat}(s) = 0$ for $s \le 0$. -/
theorem flat_of_nonpos {s : ℝ} (hs : s ≤ 0) : flat s = 0 := by simp [flat, hs]

/-- $\mathrm{flat}(s) = \exp(-1/s^2)$ for $s > 0$. -/
theorem flat_of_pos {s : ℝ} (hs : 0 < s) : flat s = exp (-(s ^ 2)⁻¹) := by
  simp [flat, not_le.2 hs]

/-- $\mathrm{flat}(s) \ge 0$. -/
theorem flat_nonneg (s : ℝ) : 0 ≤ flat s := by
  rcases le_or_gt s 0 with hs | hs
  · rw [flat_of_nonpos hs]
  · rw [flat_of_pos hs]; exact (exp_pos _).le

/-- $\mathrm{flat}(s) \le 1$. -/
theorem flat_le_one (s : ℝ) : flat s ≤ 1 := by
  rcases le_or_gt s 0 with hs | hs
  · rw [flat_of_nonpos hs]; exact zero_le_one
  · rw [flat_of_pos hs, exp_le_one_iff, neg_nonpos]; positivity

/-- For $s \le 1$, $\mathrm{flat}(s)$ is at most Mathlib's glue function `expNegInvGlue`, which is
$\exp(-1/s)$ for $s > 0$ and $0$ otherwise. -/
theorem flat_le_expNegInvGlue {s : ℝ} (hs : s ≤ 1) : flat s ≤ expNegInvGlue s := by
  rcases le_or_gt s 0 with h0 | h0
  · rw [flat_of_nonpos h0]; exact expNegInvGlue.nonneg s
  · simp only [flat_of_pos h0, expNegInvGlue, not_le.2 h0, ↓reduceIte]
    rw [exp_le_exp, neg_le_neg_iff]
    rw [inv_le_inv₀ h0 (by positivity)]
    nlinarith

/-- For every real polynomial $P$, $P(1/s) \, \mathrm{flat}(s) \to 0$ as $s \to 0$. -/
theorem tendsto_polynomial_inv_mul_flat (P : ℝ[X]) :
    Tendsto (fun s => P.eval s⁻¹ * flat s) (𝓝 0) (𝓝 0) := by
  have h := (expNegInvGlue.tendsto_polynomial_inv_mul_zero P).norm
  rw [norm_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with s hs
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (flat_nonneg s),
    Real.norm_of_nonneg (expNegInvGlue.nonneg s)]
  exact mul_le_mul_of_nonneg_left (flat_le_expNegInvGlue hs.le) (norm_nonneg _)

/-- The polynomial of the derivative: for a real polynomial $P$, the polynomial $2X^3 P - X^2 P'$,
so that
$$\frac{d}{ds} \big[ P(1/s) \, \mathrm{flat}(s) \big] = (2X^3 P - X^2 P')(1/s) \,
  \mathrm{flat}(s).$$
-/
noncomputable def flatDerivPoly (P : ℝ[X]) : ℝ[X] := 2 * X ^ 3 * P - X ^ 2 * derivative P

/-- For every real polynomial $P$ and every $x$, the map $s \mapsto P(1/s) \, \mathrm{flat}(s)$ has
the derivative $(2X^3 P - X^2 P')(1/x) \, \mathrm{flat}(x)$ at $x$. -/
theorem hasDerivAt_polynomial_inv_mul_flat (P : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun s => P.eval s⁻¹ * flat s) ((flatDerivPoly P).eval x⁻¹ * flat x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [flat_of_nonpos hx.le, mul_zero]
    refine (hasDerivAt_const _ 0).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds hx] with y hy
    rw [flat_of_nonpos hy.le, mul_zero]
  · rw [flat_of_nonpos le_rfl, mul_zero, hasDerivAt_iff_tendsto_slope]
    refine ((tendsto_polynomial_inv_mul_flat (P * X)).mono_left inf_le_left).congr fun y => ?_
    simp [slope_def_field, flat_of_nonpos, div_eq_mul_inv, mul_right_comm]
  · have h1 : HasDerivAt (fun s : ℝ => -(s ^ 2)⁻¹) (2 * (x ^ 3)⁻¹) x := by
      have := ((hasDerivAt_pow 2 x).inv (by positivity)).neg
      convert this using 1
      field_simp
      ring
    have h2 := ((P.hasDerivAt x⁻¹).comp x (hasDerivAt_inv hx.ne')).mul h1.exp
    refine (h2.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [lt_mem_nhds hx] with y hy
      simp [flat_of_pos hy]
    · simp only [flatDerivPoly, flat_of_pos hx, eval_sub, eval_mul, eval_pow, eval_X,
        eval_ofNat, Function.comp_apply]
      field_simp
      ring

/-- For every real polynomial $P$, the map $s \mapsto P(1/s) \, \mathrm{flat}(s)$ is $C^n$ for every
$n \in \mathbb{N} \cup \{\infty\}$. -/
theorem contDiff_polynomial_inv_mul_flat {n : ℕ∞} (P : ℝ[X]) :
    ContDiff ℝ n (fun s => P.eval s⁻¹ * flat s) := by
  apply contDiff_all_iff_nat.2 (fun m => ?_) n
  induction m generalizing P with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x =>
      (hasDerivAt_polynomial_inv_mul_flat P x).continuousAt)
  | succ m ihm =>
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = m + 1 from rfl]
    refine contDiff_succ_iff_deriv.2 ⟨fun x =>
      (hasDerivAt_polynomial_inv_mul_flat P x).differentiableAt, by simp, ?_⟩
    convert ihm (flatDerivPoly P) using 2
    exact (hasDerivAt_polynomial_inv_mul_flat P _).deriv

/-- For every real polynomial $P$, the map $s \mapsto P(1/s) \, \mathrm{flat}(s)$ is bounded on
$\mathbb{R}$. -/
theorem exists_abs_polynomial_inv_mul_flat_le (P : ℝ[X]) :
    ∃ C, ∀ s, |P.eval s⁻¹ * flat s| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (contDiff_polynomial_inv_mul_flat (n := 0) P).continuous.continuousOn
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (P.continuous (R := ℝ)).continuousOn
  refine ⟨max C₁ C₂, fun s => ?_⟩
  rcases le_or_gt s 0 with h0 | h0
  · rw [flat_of_nonpos h0, mul_zero, abs_zero]
    exact le_max_of_le_left ((norm_nonneg _).trans (hC₁ 0 ⟨le_rfl, zero_le_one⟩))
  rcases le_or_gt s 1 with h1 | h1
  · exact le_max_of_le_left (hC₁ s ⟨h0.le, h1⟩)
  · refine le_max_of_le_right ?_
    rw [abs_mul, abs_of_nonneg (flat_nonneg s)]
    have hP := hC₂ s⁻¹ ⟨by positivity, inv_le_one_of_one_le₀ h1.le⟩
    rw [Real.norm_eq_abs] at hP
    calc |P.eval s⁻¹| * flat s ≤ C₂ * 1 :=
          mul_le_mul hP (flat_le_one s) (flat_nonneg s) ((abs_nonneg _).trans hP)
      _ = C₂ := mul_one _

/-! ### The function $\Psi$ -/

/-- The function $\Psi$ of (4.2.6) of [cartis2022evaluation]:
$$\Psi(y) = \begin{cases} 0 & \text{if } y \le 1/2, \\ \exp\big(1 - (2y - 1)^{-2}\big) &
  \text{if } y > 1/2. \end{cases}$$
-/
noncomputable def psi (y : ℝ) : ℝ :=
  if y ≤ 1 / 2 then 0 else exp (1 - ((2 * y - 1) ^ 2)⁻¹)

/-- $\Psi(y) = e \, \mathrm{flat}(2y - 1)$. -/
theorem psi_eq (y : ℝ) : psi y = exp 1 * flat (2 * y - 1) := by
  rcases le_or_gt y (1 / 2) with hy | hy
  · simp only [psi, hy, ↓reduceIte, flat_of_nonpos (by linarith : 2 * y - 1 ≤ 0), mul_zero]
  · simp only [psi, not_le.2 hy, ↓reduceIte]
    rw [flat_of_pos (by linarith), ← exp_add]
    ring_nf

/-- $\Psi(y) = 0$ for $y \le 1/2$. -/
theorem psi_of_le {y : ℝ} (hy : y ≤ 1 / 2) : psi y = 0 := by simp only [psi, hy, ↓reduceIte]

/-- $\Psi(1) = 1$. -/
@[simp]
theorem psi_one : psi 1 = 1 := by norm_num [psi]

/-- $\Psi(y) \ge 0$. -/
theorem psi_nonneg (y : ℝ) : 0 ≤ psi y := by
  rw [psi_eq]; exact mul_nonneg (exp_pos 1).le (flat_nonneg _)

/-- $\Psi(y) \le e$. -/
theorem psi_le (y : ℝ) : psi y ≤ exp 1 := by
  rw [psi_eq]
  calc exp 1 * flat (2 * y - 1) ≤ exp 1 * 1 :=
        mul_le_mul_of_nonneg_left (flat_le_one _) (exp_pos 1).le
    _ = exp 1 := mul_one _

/-- The flat function is monotone. -/
theorem flat_monotone : Monotone flat := by
  intro s t hst
  rcases le_or_gt s 0 with hs | hs
  · rw [flat_of_nonpos hs]; exact flat_nonneg t
  · rw [flat_of_pos hs, flat_of_pos (hs.trans_le hst), exp_le_exp, neg_le_neg_iff,
      inv_le_inv₀ (pow_pos (hs.trans_le hst) 2) (pow_pos hs 2)]
    exact pow_le_pow_left₀ hs.le hst 2

/-- $\Psi$ is monotone. -/
theorem psi_monotone : Monotone psi := by
  intro y y' h
  rw [psi_eq, psi_eq]
  exact mul_le_mul_of_nonneg_left (flat_monotone (by linarith)) (exp_pos 1).le

/-- $\Psi(y) \ge 1$ for $y \ge 1$. -/
theorem one_le_psi {y : ℝ} (hy : 1 ≤ y) : 1 ≤ psi y := psi_one ▸ psi_monotone hy

/-- The polynomials $P_j$ of the derivatives of the flat function: $P_0 = 1$ and
$P_{j+1} = 2X^3 P_j - X^2 P_j'$, so that the $j$-th derivative of $\mathrm{flat}$ is
$s \mapsto P_j(1/s) \, \mathrm{flat}(s)$. -/
noncomputable def flatPoly : ℕ → ℝ[X]
  | 0 => 1
  | j + 1 => flatDerivPoly (flatPoly j)

/-- The $j$-th derivative of $\Psi$, written as $y \mapsto e \, 2^j P_j\big(1/(2y - 1)\big) \,
\mathrm{flat}(2y - 1)$, where $P_j$ is `Optimization.CarmonChain.flatPoly j`. -/
noncomputable def psiDeriv (j : ℕ) (y : ℝ) : ℝ :=
  exp 1 * 2 ^ j * ((flatPoly j).eval (2 * y - 1)⁻¹ * flat (2 * y - 1))

/-- The derivative of the $j$-th derivative formula of $\Psi$ is the $(j + 1)$-st one. -/
theorem hasDerivAt_psiDeriv (j : ℕ) (y : ℝ) : HasDerivAt (psiDeriv j) (psiDeriv (j + 1) y) y := by
  have h1 : HasDerivAt (fun y : ℝ => 2 * y - 1) 2 y := by
    simpa using ((hasDerivAt_id y).const_mul 2).sub_const 1
  have := ((hasDerivAt_polynomial_inv_mul_flat (flatPoly j) (2 * y - 1)).comp y h1).const_mul
    (exp 1 * 2 ^ j)
  convert this using 1
  · funext y; simp only [psiDeriv, Function.comp_apply]
  · simp only [psiDeriv, flatPoly, pow_succ]
    ring

/-- The $j$-th derivative of $\Psi$ is `Optimization.CarmonChain.psiDeriv j`. -/
theorem iteratedDeriv_psi (j : ℕ) : iteratedDeriv j psi = psiDeriv j := by
  induction j with
  | zero =>
    funext y
    simp [psiDeriv, flatPoly, psi_eq]
  | succ j ih =>
    funext y
    rw [iteratedDeriv_succ, ih]
    exact (hasDerivAt_psiDeriv j y).deriv

/-- $\Psi$ is $C^n$ for every $n \in \mathbb{N} \cup \{\infty\}$. -/
theorem contDiff_psi {n : ℕ∞} : ContDiff ℝ n psi := by
  have h : psi = fun y => exp 1 * ((1 : ℝ[X]).eval (2 * y - 1)⁻¹ * flat (2 * y - 1)) := by
    funext y; simp [psi_eq]
  rw [h]
  exact contDiff_const.mul ((contDiff_polynomial_inv_mul_flat 1).comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const))

/-- $\Psi'(y) \ge 0$ for every $y$. -/
theorem deriv_psi_nonneg (y : ℝ) : 0 ≤ deriv psi y := by
  rw [← iteratedDeriv_one, iteratedDeriv_psi]
  simp only [psiDeriv, flatPoly, flatDerivPoly, derivative_one, mul_zero, sub_zero, mul_one,
    eval_mul, eval_pow, eval_X, eval_ofNat, pow_one]
  rcases le_or_gt (2 * y - 1) 0 with h | h
  · rw [flat_of_nonpos h]; simp
  · have := flat_nonneg (2 * y - 1)
    positivity

/-- Every derivative of $\Psi$ is bounded: for every $j$ there is $C$ with $|\Psi^{(j)}(y)| \le C$
for all $y$. -/
theorem exists_abs_iteratedDeriv_psi_le (j : ℕ) : ∃ C, ∀ y, |iteratedDeriv j psi y| ≤ C := by
  obtain ⟨C, hC⟩ := exists_abs_polynomial_inv_mul_flat_le (flatPoly j)
  refine ⟨exp 1 * 2 ^ j * C, fun y => ?_⟩
  rw [iteratedDeriv_psi, psiDeriv, abs_mul, abs_of_pos (by positivity)]
  exact mul_le_mul_of_nonneg_left (hC _) (by positivity)

/-! ### The function $\Phi$ -/

/-- The Gaussian $t \mapsto e^{-t^2/2}$ is integrable on $\mathbb{R}$. -/
theorem integrable_gauss : Integrable fun t : ℝ => exp (-t ^ 2 / 2) := by
  have := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
  convert this using 2
  ring_nf

/-- The Gaussian $t \mapsto e^{-t^2/2}$ is continuous. -/
theorem continuous_gauss : Continuous fun t : ℝ => exp (-t ^ 2 / 2) := by fun_prop

/-- The function $\Phi$ of (4.2.6) of [cartis2022evaluation]:
$$\Phi(y) = e^{1/2} \int_{-\infty}^y e^{-t^2/2} \, dt.$$
-/
noncomputable def phi (y : ℝ) : ℝ :=
  exp (1 / 2) * ∫ t in Iic y, exp (-t ^ 2 / 2)

/-- $\Phi(y) = e^{1/2} \big( \int_{-\infty}^0 e^{-t^2/2} \, dt + \int_0^y e^{-t^2/2} \, dt \big)$.
-/
theorem phi_eq (y : ℝ) : phi y = exp (1 / 2) *
    ((∫ t in Iic 0, exp (-t ^ 2 / 2)) + ∫ t in (0 : ℝ)..y, exp (-t ^ 2 / 2)) := by
  rw [phi, ← intervalIntegral.integral_Iic_sub_Iic integrable_gauss.integrableOn
    integrable_gauss.integrableOn]
  ring

/-- $\Phi$ has the derivative $e^{1/2} e^{-y^2/2}$ at every $y$. -/
theorem hasDerivAt_phi (y : ℝ) : HasDerivAt phi (exp (1 / 2) * exp (-y ^ 2 / 2)) y := by
  have h := intervalIntegral.integral_hasDerivAt_right
    (continuous_gauss.intervalIntegrable 0 y)
    (continuous_gauss.stronglyMeasurableAtFilter volume _) continuous_gauss.continuousAt
  have := (h.const_add (∫ t in Iic 0, exp (-t ^ 2 / 2))).const_mul (exp (1 / 2))
  exact this.congr_of_eventuallyEq (Eventually.of_forall fun y => phi_eq y)

/-- $\Phi'(y) = e^{1/2} e^{-y^2/2}$. -/
theorem deriv_phi : deriv phi = fun y => exp (1 / 2) * exp (-y ^ 2 / 2) :=
  funext fun y => (hasDerivAt_phi y).deriv

/-- $\Phi(y) \ge 0$. -/
theorem phi_nonneg (y : ℝ) : 0 ≤ phi y :=
  mul_nonneg (exp_pos _).le (setIntegral_nonneg measurableSet_Iic fun _ _ => (exp_pos _).le)

/-- $\Phi(y) \le e^{1/2} \sqrt{2\pi} = \sqrt{2 \pi e}$. -/
theorem phi_le (y : ℝ) : phi y ≤ exp (1 / 2) * √(2 * π) := by
  refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
  refine (setIntegral_le_integral integrable_gauss
    (Eventually.of_forall fun t => (exp_pos _).le)).trans_eq ?_
  have := integral_gaussian (1 / 2)
  convert this using 2
  · ext t; ring_nf
  · ring_nf

/-- $\Phi$ is monotone. -/
theorem monotone_phi : Monotone phi := by
  intro y y' h
  rw [phi_eq, phi_eq]
  refine mul_le_mul_of_nonneg_left ((add_le_add_iff_left _).2 ?_) (exp_pos _).le
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := y)
    (continuous_gauss.intervalIntegrable 0 y) (continuous_gauss.intervalIntegrable y y')]
  have : 0 ≤ ∫ t in y..y', exp (-t ^ 2 / 2) :=
    intervalIntegral.integral_nonneg h fun t _ => (exp_pos _).le
  linarith

/-- $\Phi'(y) = e^{1/2} e^{-y^2/2} > 1$ for $|y| < 1$. -/
theorem one_lt_deriv_phi {y : ℝ} (hy : |y| < 1) : 1 < deriv phi y := by
  rw [deriv_phi]
  dsimp only
  rw [← exp_add]
  refine Real.one_lt_exp_iff.2 ?_
  have : y ^ 2 < 1 := by
    have := sq_lt_sq' (abs_lt.1 hy).1 (abs_lt.1 hy).2
    simpa using this
  linarith

/-- $\Phi'(y) > 0$ for every $y$. -/
theorem deriv_phi_pos (y : ℝ) : 0 < deriv phi y := by
  rw [deriv_phi]; positivity

/-- The polynomials $H_j$ of the derivatives of the Gaussian $y \mapsto e^{-y^2/2}$: $H_0 = 1$ and
$H_{j+1} = H_j' - X H_j$, so that the $j$-th derivative of the Gaussian is
$y \mapsto H_j(y) e^{-y^2/2}$. -/
noncomputable def gaussPoly : ℕ → ℝ[X]
  | 0 => 1
  | j + 1 => derivative (gaussPoly j) - X * gaussPoly j

/-- For every real polynomial $H$ and every $y$, the map $y \mapsto H(y) e^{-y^2/2}$ has the
derivative $(H' - XH)(y) e^{-y^2/2}$ at $y$. -/
theorem hasDerivAt_polynomial_mul_gauss (H : ℝ[X]) (y : ℝ) :
    HasDerivAt (fun y => H.eval y * exp (-y ^ 2 / 2))
      ((derivative H - X * H).eval y * exp (-y ^ 2 / 2)) y := by
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-y) y := by
    have := ((hasDerivAt_pow 2 y).neg).div_const 2
    convert this using 1; ring
  have := (H.hasDerivAt y).mul h1.exp
  convert this using 1
  simp only [eval_sub, eval_mul, eval_X]
  ring

/-- For every $j$, the $(j + 1)$-st derivative of $\Phi$ is $y \mapsto e^{1/2} H_j(y) e^{-y^2/2}$,
where $H_j$ is `Optimization.CarmonChain.gaussPoly j`. -/
theorem iteratedDeriv_succ_phi (j : ℕ) :
    iteratedDeriv (j + 1) phi =
      fun y => exp (1 / 2) * ((gaussPoly j).eval y * exp (-y ^ 2 / 2)) := by
  induction j with
  | zero =>
    rw [iteratedDeriv_one, deriv_phi]
    funext y; simp [gaussPoly]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    exact ((hasDerivAt_polynomial_mul_gauss (gaussPoly j) y).const_mul _).deriv

/-- $\Phi$ is $C^n$ for every $n \in \mathbb{N} \cup \{\infty\}$. -/
theorem contDiff_phi {n : ℕ∞} : ContDiff ℝ n phi := by
  refine (contDiff_infty_iff_deriv.2 ⟨fun y => (hasDerivAt_phi y).differentiableAt, ?_⟩).of_le
    (by exact_mod_cast le_top)
  rw [deriv_phi]
  fun_prop

/-- For every real polynomial $H$, the map $y \mapsto H(y) e^{-y^2/2}$ is bounded on $\mathbb{R}$.
-/
theorem exists_abs_polynomial_mul_gauss_le (H : ℝ[X]) :
    ∃ C, ∀ y, |H.eval y * exp (-y ^ 2 / 2)| ≤ C := by
  -- far from the origin the Gaussian beats `exp(-|y|)`
  have key : ∀ Q : ℝ[X], ∃ R, ∀ y, R ≤ y → |Q.eval y * exp (-y ^ 2 / 2)| ≤ 1 := by
    intro Q
    obtain ⟨R, hR⟩ := eventually_atTop.1 ((Q.tendsto_div_exp_atTop.abs).eventually
      (ge_mem_nhds (by norm_num : |(0 : ℝ)| < 1)))
    refine ⟨max R 2, fun y hy => ?_⟩
    have h1 := hR y (le_of_max_le_left hy)
    have hy2 : 2 ≤ y := le_of_max_le_right hy
    rw [abs_div, abs_of_pos (exp_pos y)] at h1
    rw [abs_mul, abs_of_pos (exp_pos _)]
    calc |Q.eval y| * exp (-y ^ 2 / 2) ≤ |Q.eval y| * exp (-y) :=
          mul_le_mul_of_nonneg_left (exp_le_exp.2 (by nlinarith)) (abs_nonneg _)
      _ = |Q.eval y| / exp y := by rw [exp_neg, div_eq_mul_inv]
      _ ≤ 1 := h1
  obtain ⟨R₁, hR₁⟩ := key H
  obtain ⟨R₂, hR₂⟩ := key (H.comp (-X))
  set R := max |R₁| |R₂|
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    (show Continuous fun y => H.eval y * exp (-y ^ 2 / 2) from
      (H.continuous (R := ℝ)).mul continuous_gauss).continuousOn
  refine ⟨max C 1, fun y => ?_⟩
  rcases le_or_gt y (-R) with hy | hy
  · have := hR₂ (-y) (by
      have := le_abs_self R₂; have := le_max_right |R₁| |R₂|; linarith)
    simp only [eval_comp, eval_neg, eval_X, neg_neg, even_two, Even.neg_pow] at this
    exact le_max_of_le_right this
  rcases le_or_gt y R with hy' | hy'
  · exact le_max_of_le_left (hC y ⟨hy.le, hy'⟩)
  · exact le_max_of_le_right (hR₁ y (by
      have := le_abs_self R₁; have := le_max_left |R₁| |R₂|; linarith))

/-- Every derivative of $\Phi$ is bounded: for every $j$ there is $C$ with $|\Phi^{(j)}(y)| \le C$
for all $y$. -/
theorem exists_abs_iteratedDeriv_phi_le (j : ℕ) : ∃ C, ∀ y, |iteratedDeriv j phi y| ≤ C := by
  rcases j with _ | j
  · refine ⟨exp (1 / 2) * √(2 * π), fun y => ?_⟩
    rw [iteratedDeriv_zero, abs_of_nonneg (phi_nonneg y)]
    exact phi_le y
  · obtain ⟨C, hC⟩ := exists_abs_polynomial_mul_gauss_le (gaussPoly j)
    refine ⟨exp (1 / 2) * C, fun y => ?_⟩
    rw [iteratedDeriv_succ_phi, abs_mul, abs_of_pos (exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hC y) (exp_pos _).le

/-! ### Uniform bounds on the derivatives of $\Psi$ and $\Phi$ -/

/-- The supremum $\sup_y |\Psi^{(j)}(y)|$ of the $j$-th derivative of $\Psi$. -/
noncomputable def psiBound (j : ℕ) : ℝ := ⨆ y, |iteratedDeriv j psi y|

/-- The supremum $\sup_y |\Phi^{(j)}(y)|$ of the $j$-th derivative of $\Phi$. -/
noncomputable def phiBound (j : ℕ) : ℝ := ⨆ y, |iteratedDeriv j phi y|

/-- $|\Psi^{(j)}(y)| \le \sup_y |\Psi^{(j)}|$ for every $y$. -/
theorem abs_iteratedDeriv_psi_le (j : ℕ) (y : ℝ) : |iteratedDeriv j psi y| ≤ psiBound j := by
  obtain ⟨C, hC⟩ := exists_abs_iteratedDeriv_psi_le j
  exact le_ciSup (f := fun y => |iteratedDeriv j psi y|) ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩ y

/-- $|\Phi^{(j)}(y)| \le \sup_y |\Phi^{(j)}|$ for every $y$. -/
theorem abs_iteratedDeriv_phi_le (j : ℕ) (y : ℝ) : |iteratedDeriv j phi y| ≤ phiBound j := by
  obtain ⟨C, hC⟩ := exists_abs_iteratedDeriv_phi_le j
  exact le_ciSup (f := fun y => |iteratedDeriv j phi y|) ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩ y

/-- $\sup_y |\Psi^{(j)}(y)| \ge 0$. -/
theorem psiBound_nonneg (j : ℕ) : 0 ≤ psiBound j :=
  (abs_nonneg _).trans (abs_iteratedDeriv_psi_le j 0)

/-- $\sup_y |\Phi^{(j)}(y)| \ge 0$. -/
theorem phiBound_nonneg (j : ℕ) : 0 ≤ phiBound j :=
  (abs_nonneg _).trans (abs_iteratedDeriv_phi_le j 0)

/-- Let $E$ be a real normed space, let $g \colon \mathbb{R} \to \mathbb{R}$ be smooth, and let
$L \colon E \to \mathbb{R}$ be a continuous linear form with $\|L\| \le 1$. Then for every $i$
and every $z \in E$,
$$\|\nabla^i (g \circ L)(z)\| \le |g^{(i)}(L z)|.$$
-/
theorem norm_iteratedFDeriv_comp_clm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {L : E →L[ℝ] ℝ} (hL : ‖L‖ ≤ 1) (i : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ i (g ∘ L) z‖ ≤ |iteratedDeriv i g (L z)| := by
  rw [L.iteratedFDeriv_comp_right hg z (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  calc |iteratedDeriv i g (L z)| * ∏ _ : Fin i, ‖L‖
        ≤ |iteratedDeriv i g (L z)| * ∏ _ : Fin i, 1 := by gcongr with m
    _ = _ := by simp

/-! ### The pair terms -/

/-- The first projection $\mathbb{R} \times \mathbb{R} \to \mathbb{R}$ has norm at most $1$. -/
theorem norm_fst_clm_le : ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by simpa using norm_fst_le z

/-- The second projection $\mathbb{R} \times \mathbb{R} \to \mathbb{R}$ has norm at most $1$. -/
theorem norm_snd_clm_le : ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by simpa using norm_snd_le z

/-- One link of the chain: $\mathrm{pair}(a, b) = \Psi(-a) \Phi(-b) - \Psi(a) \Phi(b)$. -/
noncomputable def pair (z : ℝ × ℝ) : ℝ := psi (-z.1) * phi (-z.2) - psi z.1 * phi z.2

/-- The bound
$$\mathrm{pairBound}(q) = 2 \sum_{i=0}^q \binom{q}{i} \sup |\Psi^{(i)}| \, \sup |\Phi^{(q-i)}|$$
on the $q$-th derivative of a link. -/
noncomputable def pairBound (q : ℕ) : ℝ :=
  2 * ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * psiBound i * phiBound (q - i)

/-- A link of the chain is $C^n$ for every $n \in \mathbb{N} \cup \{\infty\}$. -/
theorem contDiff_pair {n : ℕ∞} : ContDiff ℝ n pair := by
  unfold pair
  have h1 : ContDiff ℝ n psi := contDiff_psi
  have h2 : ContDiff ℝ n phi := contDiff_phi
  fun_prop

/-- Let $L_1, L_2 \colon \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ be continuous linear forms of
norm at most $1$. Then for every $q$ and every $z$, the $q$-th derivative of
$z \mapsto \Psi(L_1 z) \Phi(L_2 z)$ at $z$ has norm at most $\sum_{i=0}^q \binom{q}{i} \sup
|\Psi^{(i)}| \, \sup |\Phi^{(q-i)}|$.
-/
theorem norm_iteratedFDeriv_prod_le {L₁ L₂ : ℝ × ℝ →L[ℝ] ℝ} (h₁ : ‖L₁‖ ≤ 1) (h₂ : ‖L₂‖ ≤ 1)
    (q : ℕ) (z : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ q (fun z => psi (L₁ z) * phi (L₂ z)) z‖ ≤
      ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * psiBound i * phiBound (q - i) := by
  refine (norm_iteratedFDeriv_mul_le (N := ∞) (contDiff_psi.comp L₁.contDiff)
    (contDiff_phi.comp L₂.contDiff) z (by exact_mod_cast le_top)).trans ?_
  gcongr with i hi
  · exact mul_nonneg (Nat.cast_nonneg _) (psiBound_nonneg i)
  · exact (norm_iteratedFDeriv_comp_clm_le contDiff_psi h₁ i z).trans
      (abs_iteratedDeriv_psi_le i _)
  · exact (norm_iteratedFDeriv_comp_clm_le contDiff_phi h₂ _ z).trans
      (abs_iteratedDeriv_phi_le _ _)

/-- The $q$-th derivative of a link has norm at most $\mathrm{pairBound}(q)$ at every point. -/
theorem norm_iteratedFDeriv_pair_le (q : ℕ) (z : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ q pair z‖ ≤ pairBound q := by
  have hf : pair = (fun z => psi ((-ContinuousLinearMap.fst ℝ ℝ ℝ) z) *
      phi ((-ContinuousLinearMap.snd ℝ ℝ ℝ) z)) -
      (fun z => psi (ContinuousLinearMap.fst ℝ ℝ ℝ z) * phi (ContinuousLinearMap.snd ℝ ℝ ℝ z)) := by
    funext z; simp [pair]
  have hA : ContDiff ℝ q (fun z => psi ((-ContinuousLinearMap.fst ℝ ℝ ℝ) z) *
      phi ((-ContinuousLinearMap.snd ℝ ℝ ℝ) z)) :=
    (contDiff_psi.comp (-ContinuousLinearMap.fst ℝ ℝ ℝ).contDiff).mul
      (contDiff_phi.comp (-ContinuousLinearMap.snd ℝ ℝ ℝ).contDiff)
  have hB : ContDiff ℝ q (fun z => psi (ContinuousLinearMap.fst ℝ ℝ ℝ z) *
      phi (ContinuousLinearMap.snd ℝ ℝ ℝ z)) :=
    (contDiff_psi.comp (ContinuousLinearMap.fst ℝ ℝ ℝ).contDiff).mul
      (contDiff_phi.comp (ContinuousLinearMap.snd ℝ ℝ ℝ).contDiff)
  rw [hf, iteratedFDeriv_sub_apply hA.contDiffAt hB.contDiffAt, pairBound, two_mul]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · exact norm_iteratedFDeriv_prod_le (by rw [norm_neg]; exact norm_fst_clm_le)
      (by rw [norm_neg]; exact norm_snd_clm_le) q z
  · exact norm_iteratedFDeriv_prod_le (norm_fst_clm_le)
      (norm_snd_clm_le) q z

/-! ### Coordinates -/

variable {T : ℕ}

/-- Coordinate $i$ of $x \in \mathbb{R}^T$ as a continuous linear form: $x \mapsto x_i$ for $i < T$,
and the zero form for $i \ge T$. -/
noncomputable def coord (T i : ℕ) : EuclideanSpace ℝ (Fin T) →L[ℝ] ℝ :=
  if h : i < T then EuclideanSpace.proj (⟨i, h⟩ : Fin T) else 0

/-- For $i < T$, coordinate $i$ of $x$ is $x_i$. -/
theorem coord_apply_of_lt {i : ℕ} (h : i < T) (x : EuclideanSpace ℝ (Fin T)) :
    coord T i x = x ⟨i, h⟩ := by
  simp [coord, h]

/-- For $j \in \{0, \dots, T - 1\}$, coordinate $j$ of $x$ is $x_j$. -/
@[simp]
theorem coord_apply_fin (j : Fin T) (x : EuclideanSpace ℝ (Fin T)) : coord T j x = x j :=
  coord_apply_of_lt j.2 x

/-- For $i \ge T$, coordinate $i$ of $x$ is $0$. -/
theorem coord_apply_of_le {i : ℕ} (h : T ≤ i) (x : EuclideanSpace ℝ (Fin T)) :
    coord T i x = 0 := by
  simp [coord, not_lt.2 h]

/-- $|x_i| \le \|x\|$ for every coordinate $i$. -/
theorem abs_coord_le (i : ℕ) (x : EuclideanSpace ℝ (Fin T)) : |coord T i x| ≤ ‖x‖ := by
  rcases lt_or_ge i T with h | h
  · rw [coord_apply_of_lt h, ← Real.norm_eq_abs]; exact PiLp.norm_apply_le x _
  · rw [coord_apply_of_le h, abs_zero]; exact norm_nonneg x

/-- Every coordinate form has norm at most $1$. -/
theorem norm_coord_le (i : ℕ) : ‖coord T i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul, Real.norm_eq_abs]; exact abs_coord_le i x

/-- For $x \in \mathbb{R}^T$, $\sum_{i < T} x_i^2 = \|x\|^2$. -/
theorem sum_range_coord_sq (x : EuclideanSpace ℝ (Fin T)) :
    ∑ i ∈ Finset.range T, coord T i x ^ 2 = ‖x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, ← Fin.sum_univ_eq_sum_range (fun i => coord T i x ^ 2)]
  simp [Real.norm_eq_abs, sq_abs]

/-- The pair of consecutive coordinates $x \mapsto (x_{l-1}, x_l)$, as a continuous linear map
$\mathbb{R}^T \to \mathbb{R} \times \mathbb{R}$. -/
noncomputable def pairMap (T l : ℕ) : EuclideanSpace ℝ (Fin T) →L[ℝ] ℝ × ℝ :=
  (coord T (l - 1)).prod (coord T l)

/-- The pair map sends $x$ to $(x_{l-1}, x_l)$. -/
@[simp]
theorem pairMap_apply (l : ℕ) (x : EuclideanSpace ℝ (Fin T)) :
    pairMap T l x = (coord T (l - 1) x, coord T l x) := rfl

/-- $\|(x_{l-1}, x_l)\| \le \|x\|$, where $\mathbb{R} \times \mathbb{R}$ carries the max norm. -/
theorem norm_pairMap_apply_le (l : ℕ) (x : EuclideanSpace ℝ (Fin T)) : ‖pairMap T l x‖ ≤ ‖x‖ := by
  rw [pairMap_apply, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (abs_coord_le _ x) (abs_coord_le _ x)

/-- For $x \in \mathbb{R}^T$, $\sum_{l=1}^{T-1} \|(x_{l-1}, x_l)\|^2 \le 2 \|x\|^2$, where
$\mathbb{R} \times \mathbb{R}$ carries the max norm. -/
theorem sum_sq_norm_pairMap_le (x : EuclideanSpace ℝ (Fin T)) :
    ∑ l ∈ Finset.Ico 1 T, ‖pairMap T l x‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 := by
  have h1 : ∀ l, ‖pairMap T l x‖ ^ 2 ≤ coord T (l - 1) x ^ 2 + coord T l x ^ 2 := by
    intro l
    rw [pairMap_apply, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs]
    rcases max_choice |coord T (l - 1) x| |coord T l x| with h | h <;> rw [h, sq_abs] <;>
      nlinarith [sq_nonneg (coord T (l - 1) x), sq_nonneg (coord T l x)]
  have h2 : ∑ l ∈ Finset.Ico 1 T, coord T (l - 1) x ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range, ← sum_range_coord_sq x]
    simp only [add_tsub_cancel_left]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      fun _ _ _ => sq_nonneg _
  have h3 : ∑ l ∈ Finset.Ico 1 T, coord T l x ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← sum_range_coord_sq x]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun l hl => by
      simp only [Finset.mem_Ico, Finset.mem_range] at hl ⊢; omega) fun _ _ _ => sq_nonneg _
  calc ∑ l ∈ Finset.Ico 1 T, ‖pairMap T l x‖ ^ 2
      ≤ ∑ l ∈ Finset.Ico 1 T, (coord T (l - 1) x ^ 2 + coord T l x ^ 2) :=
        Finset.sum_le_sum fun l _ => h1 l
    _ ≤ 2 * ‖x‖ ^ 2 := by rw [Finset.sum_add_distrib]; linarith

/-- The estimate without dependence on the dimension behind Lemma 4.2.5(iv). Let $q \ge 2$ and
$v_0, \dots, v_{q-1} \in \mathbb{R}^T$. Then
$$\sum_{l=1}^{T-1} \prod_{m} \big\| \big( (v_m)_{l-1}, (v_m)_l \big) \big\| \le 2 \prod_m
  \|v_m\|,$$
where $\mathbb{R} \times \mathbb{R}$ carries the max norm.

The proof applies the Cauchy–Schwarz inequality to the first two factors. -/
theorem sum_prod_norm_pairMap_le {q : ℕ} (hq : 2 ≤ q) (v : Fin q → EuclideanSpace ℝ (Fin T)) :
    ∑ l ∈ Finset.Ico 1 T, ∏ m, ‖pairMap T l (v m)‖ ≤ 2 * ∏ m, ‖v m‖ := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
  simp only [Fin.prod_univ_succ]
  set R := ∏ m : Fin q, ‖v m.succ.succ‖
  have hR : ∀ l, ∏ m : Fin q, ‖pairMap T l (v m.succ.succ)‖ ≤ R := fun l => by
    simp only [R]
    gcongr with m
    exact norm_pairMap_apply_le l _
  have hR0 : 0 ≤ R := Finset.prod_nonneg fun _ _ => norm_nonneg _
  set a := fun l => ‖pairMap T l (v 0)‖
  set b := fun l => ‖pairMap T l (v 1)‖
  have hab : ∑ l ∈ Finset.Ico 1 T, a l * b l ≤ 2 * (‖v 0‖ * ‖v 1‖) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ico 1 T) a b
    have ha := sum_sq_norm_pairMap_le (v 0)
    have hb := sum_sq_norm_pairMap_le (v 1)
    have hS : 0 ≤ ∑ l ∈ Finset.Ico 1 T, a l * b l :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have h0 : 0 ≤ ‖v 0‖ * ‖v 1‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsq : (∑ l ∈ Finset.Ico 1 T, a l * b l) ^ 2 ≤ (2 * (‖v 0‖ * ‖v 1‖)) ^ 2 := by
      calc _ ≤ (∑ l ∈ Finset.Ico 1 T, a l ^ 2) * ∑ l ∈ Finset.Ico 1 T, b l ^ 2 := hcs
        _ ≤ (2 * ‖v 0‖ ^ 2) * (2 * ‖v 1‖ ^ 2) :=
          mul_le_mul ha hb (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        _ = (2 * (‖v 0‖ * ‖v 1‖)) ^ 2 := by ring
    nlinarith
  calc ∑ l ∈ Finset.Ico 1 T, a l * (b l * ∏ m : Fin q, ‖pairMap T l (v m.succ.succ)‖)
      ≤ ∑ l ∈ Finset.Ico 1 T, a l * b l * R := Finset.sum_le_sum fun l _ => by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left (hR l) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (∑ l ∈ Finset.Ico 1 T, a l * b l) * R := by rw [Finset.sum_mul]
    _ ≤ 2 * (‖v 0‖ * ‖v 1‖) * R := mul_le_mul_of_nonneg_right hab hR0
    _ = 2 * (‖v 0‖ * (‖v 1‖ * R)) := by ring

/-! ### The chain -/

/-- The hard zero chain of (4.2.6) of [cartis2022evaluation] on $\mathbb{R}^T$:
$$\mathrm{chain}_T(x) = -\Psi(1) \Phi(x_0) + \sum_{l=1}^{T-1} \big[ \Psi(-x_{l-1}) \Phi(-x_l) -
  \Psi(x_{l-1}) \Phi(x_l) \big].$$

The first term $-\Psi(1) \Phi(x_0)$ is the one of Carmon, Duchi, Hinder and Sidford. Coordinate
$i$ is `Optimization.CarmonChain.coord T i`. For $T = 0$ the function is the constant
$-\Phi(0)$. -/
noncomputable def chain (T : ℕ) (x : EuclideanSpace ℝ (Fin T)) : ℝ :=
  -(psi 1 * phi (coord T 0 x)) + ∑ l ∈ Finset.Ico 1 T, pair (pairMap T l x)

/-- $\mathrm{chain}_T(x) = -\Phi(x_0) + \sum_{l=1}^{T-1} \mathrm{pair}(x_{l-1}, x_l)$. -/
theorem chain_eq (x : EuclideanSpace ℝ (Fin T)) :
    chain T x = -phi (coord T 0 x) + ∑ l ∈ Finset.Ico 1 T, pair (pairMap T l x) := by
  rw [chain, psi_one, one_mul]

/-- $\mathrm{chain}_T$ is the sum of $-\Phi \circ x_0$ and the links
$x \mapsto \mathrm{pair}(x_{l-1}, x_l)$ for $1 \le l \le T - 1$, as an equality of functions. -/
theorem chain_eq_add :
    chain T = -(phi ∘ coord T 0) + fun x => ∑ l ∈ Finset.Ico 1 T, (pair ∘ pairMap T l) x :=
  funext fun x => by rw [chain_eq]; rfl

/-- $\mathrm{chain}_T$ is $C^n$ for every $n \in \mathbb{N} \cup \{\infty\}$. -/
theorem contDiff_chain {n : ℕ∞} : ContDiff ℝ n (chain T) := by
  rw [chain_eq_add]
  exact (contDiff_phi.comp (coord T 0).contDiff).neg.add
    (ContDiff.sum fun l _ => contDiff_pair.comp (pairMap T l).contDiff)

/-- The explicit bound on $\|\nabla^{p+1} \mathrm{chain}_T\|$ that does not depend on $T$:
$$L^D_p = 1 + \sup |\Phi^{(p+1)}| + 2 \, \mathrm{pairBound}(p + 1).$$
-/
noncomputable def lipschitzConst (p : ℕ) : ℝ := 1 + phiBound (p + 1) + 2 * pairBound (p + 1)

/-- The constant $L^D_p$ is positive. -/
theorem lipschitzConst_pos (p : ℕ) : 0 < lipschitzConst p := by
  have := phiBound_nonneg (p + 1)
  have : 0 ≤ pairBound (p + 1) := (norm_nonneg _).trans (norm_iteratedFDeriv_pair_le _ 0)
  unfold lipschitzConst; positivity

/-- **Lemma 4.2.5(iv)** of [cartis2022evaluation], uniform bound. Let $p \ge 1$. Then for every $T$
and every $x \in \mathbb{R}^T$,
$$\|\nabla^{p+1} \mathrm{chain}_T(x)\| \le L^D_p,$$
where $L^D_p$ is `Optimization.CarmonChain.lipschitzConst p`, which does not depend on $T$. -/
theorem norm_iteratedFDeriv_chain_le {p : ℕ} (hp : 1 ≤ p) (x : EuclideanSpace ℝ (Fin T)) :
    ‖iteratedFDeriv ℝ (p + 1) (chain T) x‖ ≤ lipschitzConst p := by
  have h1 : ContDiff ℝ ∞ (-(phi ∘ coord T 0)) := (contDiff_phi.comp (coord T 0).contDiff).neg
  have h2 : ContDiff ℝ ∞ fun x => ∑ l ∈ Finset.Ico 1 T, (pair ∘ pairMap T l) x :=
    ContDiff.sum fun l _ => contDiff_pair.comp (pairMap T l).contDiff
  rw [chain_eq_add, iteratedFDeriv_add_apply (h1.contDiffAt.of_le (by exact_mod_cast le_top))
    (h2.contDiffAt.of_le (by exact_mod_cast le_top)), lipschitzConst, add_assoc]
  refine (norm_add_le _ _).trans (le_add_of_nonneg_of_le zero_le_one (add_le_add ?_ ?_))
  · rw [iteratedFDeriv_neg_apply, norm_neg]
    exact (norm_iteratedFDeriv_comp_clm_le contDiff_phi (norm_coord_le 0) _ x).trans
      (abs_iteratedDeriv_phi_le _ _)
  · rw [iteratedFDeriv_sum fun l _ =>
      (contDiff_pair.comp (pairMap T l).contDiff : ContDiff ℝ (p + 1) _)]
    have hB : 0 ≤ pairBound (p + 1) := (norm_nonneg _).trans (norm_iteratedFDeriv_pair_le _ 0)
    refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
    rw [Finset.sum_apply, sum_apply, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ l, |iteratedFDeriv ℝ (p + 1) (pair ∘ pairMap T l) x v| ≤
        pairBound (p + 1) * ∏ m, ‖pairMap T l (v m)‖ := by
      intro l
      rw [(pairMap T l).iteratedFDeriv_comp_right contDiff_pair x (by exact_mod_cast le_top),
        ContinuousMultilinearMap.compContinuousLinearMap_apply, ← Real.norm_eq_abs]
      exact ((iteratedFDeriv ℝ (p + 1) pair (pairMap T l x)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (norm_iteratedFDeriv_pair_le _ _)
          (Finset.prod_nonneg fun _ _ => norm_nonneg _))
    calc ∑ l ∈ Finset.Ico 1 T, |iteratedFDeriv ℝ (p + 1) (pair ∘ pairMap T l) x v|
        ≤ ∑ l ∈ Finset.Ico 1 T, pairBound (p + 1) * ∏ m, ‖pairMap T l (v m)‖ :=
          Finset.sum_le_sum fun l _ => hterm l
      _ = pairBound (p + 1) * ∑ l ∈ Finset.Ico 1 T, ∏ m, ‖pairMap T l (v m)‖ := by
          rw [Finset.mul_sum]
      _ ≤ pairBound (p + 1) * (2 * ∏ m, ‖v m‖) :=
          mul_le_mul_of_nonneg_left (sum_prod_norm_pairMap_le (by simp; omega) v) hB
      _ = 2 * pairBound (p + 1) * ∏ m, ‖v m‖ := by ring

/-- **Lemma 4.2.5(iv)** of [cartis2022evaluation]. Let $p \ge 1$. Then for every $T$,
$\nabla^p \mathrm{chain}_T$ is Lipschitz continuous on $\mathbb{R}^T$ with the constant $L^D_p$
of `Optimization.CarmonChain.lipschitzConst`, which does not depend on $T$:
$$\|\nabla^p \mathrm{chain}_T(x) - \nabla^p \mathrm{chain}_T(y)\| \le L^D_p \|x - y\| \quad
  \text{for all } x, y \in \mathbb{R}^T.$$
-/
theorem lipschitzOn_iteratedFDeriv_chain {p : ℕ} (hp : 1 ≤ p) :
    IteratedFDerivLipschitzOn (chain T) p (lipschitzConst p) univ :=
  iteratedFDerivLipschitzOn_of_norm_le convex_univ
    (fun _ _ => contDiff_chain.contDiffAt) fun x _ => norm_iteratedFDeriv_chain_le hp x

/-! ### Lemma 4.2.5 (i): the zero-chain property -/

/-- $\mathrm{pair}(a, b) = 0$ when $|a| \le 1/2$. -/
theorem pair_eq_zero {z : ℝ × ℝ} (hz : |z.1| ≤ 1 / 2) : pair z = 0 := by
  have h1 : psi z.1 = 0 := psi_of_le (le_trans (le_abs_self _) hz)
  have h2 : psi (-z.1) = 0 := psi_of_le (le_trans (neg_le_abs _) hz)
  simp [pair, h1, h2]

/-- Coordinate $k$ of the unit vector $e_i$ is $1$ if $k = i$ and $0$ otherwise. -/
theorem coord_single (k : ℕ) (i : Fin T) :
    coord T k (EuclideanSpace.single i (1 : ℝ)) = if k = i then 1 else 0 := by
  rcases lt_or_ge k T with hk | hk
  · rw [coord_apply_of_lt hk, PiLp.single_apply]
    simp only [Fin.ext_iff]
  · rw [coord_apply_of_le hk, ite_eq_right (by have := i.2; omega)]

/-- The linear map $y \mapsto y - y_i e_i$ on $\mathbb{R}^T$, which sets coordinate $i$ to zero. -/
noncomputable def zeroCoord (i : Fin T) : EuclideanSpace ℝ (Fin T) →L[ℝ] EuclideanSpace ℝ (Fin T) :=
  ContinuousLinearMap.id ℝ _ - (coord T i).smulRight (EuclideanSpace.single i (1 : ℝ))

/-- Coordinate $k$ of $y - y_i e_i$ is $0$ if $k = i$ and $y_k$ otherwise. -/
theorem coord_zeroCoord (i : Fin T) (k : ℕ) (y : EuclideanSpace ℝ (Fin T)) :
    coord T k (zeroCoord i y) = if k = i then 0 else coord T k y := by
  simp only [zeroCoord, sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, map_sub, map_smul, coord_single, smul_eq_mul]
  split_ifs with h
  · subst h; simp
  · simp

/-- Let $1 \le i < T$ and let $y \in \mathbb{R}^T$ with $|y_{i-1}| \le 1/2$ and $|y_i| \le 1/2$.
Then setting coordinate $i$ to zero does not change the chain: $\mathrm{chain}_T(y - y_i e_i) =
\mathrm{chain}_T(y)$. -/
theorem chain_comp_zeroCoord {i : Fin T} (hi : 1 ≤ (i : ℕ)) {y : EuclideanSpace ℝ (Fin T)}
    (h1 : |coord T (i - 1) y| ≤ 1 / 2) (h2 : |coord T i y| ≤ 1 / 2) :
    chain T (zeroCoord i y) = chain T y := by
  rw [chain_eq, chain_eq, coord_zeroCoord, ite_eq_right (by omega)]
  congr 1
  refine Finset.sum_congr rfl fun l hl => ?_
  simp only [pairMap_apply, coord_zeroCoord]
  by_cases hl1 : l = (i : ℕ)
  · subst hl1
    rw [ite_eq_right (by omega), ite_eq_left rfl]
    rw [pair_eq_zero h1, pair_eq_zero h1]
  by_cases hl2 : l - 1 = (i : ℕ)
  · rw [ite_eq_left hl2, ite_eq_right hl1, pair_eq_zero (by simp),
      pair_eq_zero (by rw [hl2]; exact h2)]
  · rw [ite_eq_right hl2, ite_eq_right hl1]

/-- **Lemma 4.2.5(i)** of [cartis2022evaluation]. For every $T$ and every $p$, $\mathrm{chain}_T$ is
a $p$-th order zero chain in the sense of `Optimization.IsZeroChain`: if $x_i = 0$ for all
$i \ge j$, then for every order $q \in \{1, \dots, p\}$ the unit vectors $e_i$ with $i > j$ are
null directions of $\nabla^q \mathrm{chain}_T(x)$. -/
theorem isZeroChain_chain (p : ℕ) : IsZeroChain (chain T) p := by
  intro x j hx q _ _ i hji
  have hi1 : 1 ≤ (i : ℕ) := by omega
  have hxi : coord T i x = 0 := by rw [coord_apply_fin]; exact hx i hji.le
  have hxi' : coord T (i - 1) x = 0 := by
    rw [coord_apply_of_lt (by omega)]; exact hx _ (by simp; omega)
  have hU : ∀ᶠ y in 𝓝 x, |coord T (i - 1) y| < 1 / 2 ∧ |coord T i y| < 1 / 2 := by
    refine ((((coord T (i - 1)).continuous.abs.tendsto x).eventually (gt_mem_nhds ?_)).and
      (((coord T i).continuous.abs.tendsto x).eventually (gt_mem_nhds ?_)))
    · rw [hxi', abs_zero]; norm_num
    · rw [hxi, abs_zero]; norm_num
  have hfx : chain T =ᶠ[𝓝 x] chain T ∘ zeroCoord i := by
    filter_upwards [hU] with y hy
    exact (chain_comp_zeroCoord hi1 hy.1.le hy.2.le).symm
  refine isNullDirection_iteratedFDeriv_of_eventuallyEq_comp (N := ∞) contDiff_chain hfx ?_
    (by exact_mod_cast le_top)
  · ext k
    have := coord_zeroCoord i k (EuclideanSpace.single i (1 : ℝ))
    rw [coord_single] at this
    rw [← coord_apply_fin, this]
    split_ifs with h1 <;> simp_all

/-! ### Lemma 4.2.5 (ii): large gradient -/

/-- The derivative of a link of the chain at $(a, b)$ in the direction $(u, w)$:
$$-u \Psi'(-a) \Phi(-b) - w \Psi(-a) \Phi'(-b) - u \Psi'(a) \Phi(b) - w \Psi(a) \Phi'(b).$$
-/
noncomputable def dpair (a b u w : ℝ) : ℝ :=
  -(u * deriv psi (-a) * phi (-b)) - w * psi (-a) * deriv phi (-b) -
    u * deriv psi a * phi b - w * psi a * deriv phi b

/-- $\Psi$ has the derivative $\Psi'(y)$ at every $y$. -/
theorem hasDerivAt_psi (y : ℝ) : HasDerivAt psi (deriv psi y) y :=
  ((contDiff_psi (n := 1)).differentiable one_ne_zero y).hasDerivAt

/-- The map $t \mapsto \mathrm{pair}(a + tu, b + tw)$ has the derivative
`Optimization.CarmonChain.dpair a b u w` at $t = 0$. -/
theorem hasDerivAt_pair_line (a b u w : ℝ) :
    HasDerivAt (fun t : ℝ => pair (a + t * u, b + t * w)) (dpair a b u w) 0 := by
  have hl : ∀ c v : ℝ, HasDerivAt (fun t : ℝ => c + t * v) v 0 := fun c v => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v).const_add c
  have hn : ∀ c v : ℝ, HasDerivAt (fun t : ℝ => -(c + t * v)) (-v) 0 := fun c v => (hl c v).neg
  have A := ((hasDerivAt_psi (-(a + 0 * u))).comp 0 (hn a u)).mul
    ((hasDerivAt_phi (-(b + 0 * w))).comp 0 (hn b w))
  have B := ((hasDerivAt_psi (a + 0 * u)).comp 0 (hl a u)).mul
    ((hasDerivAt_phi (b + 0 * w)).comp 0 (hl b w))
  have := A.sub B
  simp only [zero_mul, add_zero] at this
  convert this using 1
  · funext t; simp [pair, Function.comp_apply]
  · simp only [dpair, deriv_phi, Function.comp_apply, zero_mul, add_zero]
    ring_nf

/-- For $u \ge 0$ and $w \ge 0$, the derivative of a link at $(a, b)$ in the direction $(u, w)$ is
at most $0$. -/
theorem dpair_nonpos (a b : ℝ) {u w : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) : dpair a b u w ≤ 0 := by
  have := deriv_psi_nonneg a; have := deriv_psi_nonneg (-a)
  have := deriv_phi_pos b; have := deriv_phi_pos (-b)
  have := phi_nonneg b; have := phi_nonneg (-b); have := psi_nonneg a; have := psi_nonneg (-a)
  unfold dpair
  have h1 : 0 ≤ u * deriv psi (-a) * phi (-b) := by positivity
  have h2 : 0 ≤ w * psi (-a) * deriv phi (-b) := by positivity
  have h3 : 0 ≤ u * deriv psi a * phi b := by positivity
  have h4 : 0 ≤ w * psi a * deriv phi b := by positivity
  linarith

/-- The derivative of $\mathrm{chain}_T$ at $x$ in the direction $v$: the map
$t \mapsto \mathrm{chain}_T(x + tv)$ has, at $t = 0$, the derivative
$$-v_0 \Phi'(x_0) + \sum_{l=1}^{T-1} \mathrm{dpair}(x_{l-1}, x_l, v_{l-1}, v_l),$$
where $\mathrm{dpair}$ is `Optimization.CarmonChain.dpair`. -/
theorem hasDerivAt_chain_line (x v : EuclideanSpace ℝ (Fin T)) :
    HasDerivAt (fun t : ℝ => chain T (x + t • v))
      (-(coord T 0 v * deriv phi (coord T 0 x)) + ∑ l ∈ Finset.Ico 1 T,
        dpair (coord T (l - 1) x) (coord T l x) (coord T (l - 1) v) (coord T l v)) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => coord T 0 x + t * coord T 0 v) (coord T 0 v) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (coord T 0 v)).const_add (coord T 0 x)
  have h0 : HasDerivAt (fun t : ℝ => phi (coord T 0 x + t * coord T 0 v))
      (deriv phi (coord T 0 x) * coord T 0 v) 0 := by
    have := (hasDerivAt_phi (coord T 0 x + 0 * coord T 0 v)).comp 0 hlin
    rw [zero_mul, add_zero] at this
    rw [deriv_phi]
    exact this
  have hs := HasDerivAt.fun_sum (u := Finset.Ico 1 T) fun l _ =>
    hasDerivAt_pair_line (coord T (l - 1) x) (coord T l x) (coord T (l - 1) v) (coord T l v)
  convert h0.neg.add hs using 1
  · funext t
    simp only [chain_eq, map_add, map_smul, smul_eq_mul, pairMap_apply, Prod.smul_mk,
      Prod.mk_add_mk, Pi.add_apply, Pi.neg_apply]
  · ring

/-- $\nabla \mathrm{chain}_T(x) v = -v_0 \Phi'(x_0) + \sum_{l=1}^{T-1} \mathrm{dpair}(x_{l-1}, x_l,
v_{l-1}, v_l)$. -/
theorem fderiv_chain_apply (x v : EuclideanSpace ℝ (Fin T)) :
    fderiv ℝ (chain T) x v = -(coord T 0 v * deriv phi (coord T 0 x)) + ∑ l ∈ Finset.Ico 1 T,
      dpair (coord T (l - 1) x) (coord T l x) (coord T (l - 1) v) (coord T l v) := by
  have hd : HasFDerivAt (chain T) (fderiv ℝ (chain T) x) x :=
    ((contDiff_chain (n := 1)).differentiable one_ne_zero x).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hd' : HasFDerivAt (chain T) (fderiv ℝ (chain T) x) (x + (0 : ℝ) • v) := by
    simpa using hd
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) hline
  exact h1.unique (hasDerivAt_chain_line x v)

/-- **Lemma 4.2.5(ii)** of [cartis2022evaluation], which is Lemma 2 of Carmon, Duchi, Hinder and
Sidford. Let $x \in \mathbb{R}^T$ and let $i \in \{0, \dots, T - 1\}$ with $|x_i| < 1$. Then
there is $j \le i$ with $|x_j| < 1$ and
$$\big| \partial_j \mathrm{chain}_T(x) \big| > 1, \quad\text{hence}\quad \|\nabla
  \mathrm{chain}_T(x)\| > 1.$$

The partial derivative $\partial_j$ is the derivative applied to the unit vector
`EuclideanSpace.single j 1`. -/
theorem exists_abs_partial_chain_gt_one {x : EuclideanSpace ℝ (Fin T)} {i : Fin T}
    (hi : |x i| < 1) : ∃ j : Fin T, j ≤ i ∧ |x j| < 1 ∧
      1 < |fderiv ℝ (chain T) x (EuclideanSpace.single j 1)| ∧ 1 < ‖fderiv ℝ (chain T) x‖ := by
  classical
  have hex : ∃ k, k < T ∧ |coord T k x| < 1 := ⟨i, i.2, by rwa [coord_apply_fin]⟩
  set k := Nat.find hex with hk
  obtain ⟨hkT, hkx⟩ := Nat.find_spec hex
  have hmin : ∀ k' < k, 1 ≤ |coord T k' x| := fun k' hk' => by
    have := Nat.find_min hex hk'
    push Not at this
    exact this (by omega)
  have hki : k ≤ i := Nat.find_min' hex ⟨i.2, by rwa [coord_apply_fin]⟩
  set j : Fin T := ⟨k, hkT⟩
  -- every term of `∂_j` is nonpositive and one is below `-1`
  have hD : fderiv ℝ (chain T) x (EuclideanSpace.single j 1) < -1 := by
    rw [fderiv_chain_apply]
    simp only [coord_single]
    have hterms : ∀ l ∈ Finset.Ico 1 T, dpair (coord T (l - 1) x) (coord T l x)
        (if l - 1 = (j : ℕ) then 1 else 0) (if l = (j : ℕ) then 1 else 0) ≤ 0 :=
      fun l _ => dpair_nonpos _ _ (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · have hj0 : (j : ℕ) = 0 := hk0
      have h1 := one_lt_deriv_phi (y := coord T 0 x) (by rw [← hj0]; exact hkx)
      have e : (if (0 : ℕ) = (j : ℕ) then (1 : ℝ) else 0) = 1 := by simp [hj0]
      rw [e]
      have := Finset.sum_nonpos hterms
      linarith
    · have hj1 : 1 ≤ (j : ℕ) := hk0
      have hjT : (j : ℕ) ∈ Finset.Ico 1 T := Finset.mem_Ico.2 ⟨hk0, hkT⟩
      have hj0 : (0 : ℕ) ≠ (j : ℕ) := by omega
      simp only [hj0, ↓reduceIte, zero_mul, neg_zero, zero_add]
      have hsplit := Finset.sum_erase_add _ (fun l => dpair (coord T (l - 1) x)
        (coord T l x) (if l - 1 = (j : ℕ) then 1 else 0) (if l = (j : ℕ) then 1 else 0)) hjT
      rw [← hsplit]
      have hrest := Finset.sum_nonpos (s := (Finset.Ico 1 T).erase (j : ℕ))
        fun l hl => hterms l (Finset.mem_of_mem_erase hl)
      have hjj : dpair (coord T (j - 1) x) (coord T j x) (if (j : ℕ) - 1 = (j : ℕ) then 1 else 0)
          (if (j : ℕ) = (j : ℕ) then 1 else 0) < -1 := by
        have hjj' : (j : ℕ) - 1 ≠ (j : ℕ) := by omega
        simp only [hjj', ↓reduceIte, dpair]
        have hprev := hmin (k - 1) (by omega)
        have hcur : |coord T j x| < 1 := hkx
        have := psi_nonneg (coord T (j - 1) x); have := psi_nonneg (-coord T (j - 1) x)
        have := deriv_phi_pos (coord T j x); have := deriv_phi_pos (-coord T j x)
        rcases le_abs'.1 hprev with hneg | hpos
        · have hps := one_le_psi (y := -coord T (j - 1) x) (by linarith)
          have hph := one_lt_deriv_phi (y := -coord T j x) (by rwa [abs_neg])
          have : 1 < psi (-coord T (j - 1) x) * deriv phi (-coord T j x) := by nlinarith
          nlinarith
        · have hps := one_le_psi (y := coord T (j - 1) x) hpos
          have hph := one_lt_deriv_phi (y := coord T j x) hcur
          have : 1 < psi (coord T (j - 1) x) * deriv phi (coord T j x) := by nlinarith
          nlinarith
      linarith
  have habs : 1 < |fderiv ℝ (chain T) x (EuclideanSpace.single j 1)| := by
    rw [abs_of_neg (by linarith)]; linarith
  refine ⟨j, hki, by rw [← coord_apply_fin]; exact hkx, habs, ?_⟩
  calc 1 < |fderiv ℝ (chain T) x (EuclideanSpace.single j 1)| := habs
    _ = ‖fderiv ℝ (chain T) x (EuclideanSpace.single j 1)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ (chain T) x‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ :=
        (fderiv ℝ (chain T) x).le_opNorm _
    _ = ‖fderiv ℝ (chain T) x‖ := by simp

/-! ### Lemma 4.2.5 (iii): the range of values -/

/-- $e \cdot e^{1/2} \sqrt{2\pi} \le 12$. -/
theorem exp_one_mul_phi_bound_le : exp 1 * (exp (1 / 2) * √(2 * π)) ≤ 12 := by
  have h3 : exp 1 ^ 3 < 2.7182818286 ^ 3 := by
    gcongr; exact Real.exp_one_lt_d9
  have hπ := Real.pi_lt_d2
  have hv : 0 ≤ exp 1 * (exp (1 / 2) * √(2 * π)) := by positivity
  have hsq : (exp 1 * (exp (1 / 2) * √(2 * π))) ^ 2 = exp 1 ^ 3 * (2 * π) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul, ← Real.exp_nat_mul,
      ← Real.exp_nat_mul]
    rw [mul_left_comm, ← mul_assoc, ← Real.exp_add]
    norm_num
  have : (exp 1 * (exp (1 / 2) * √(2 * π))) ^ 2 ≤ 144 := by
    rw [hsq]; nlinarith [Real.pi_pos]
  nlinarith

/-- $e^{1/2} \sqrt{2\pi} \le 12$. -/
theorem phi_bound_le : exp (1 / 2) * √(2 * π) ≤ 12 := by
  refine le_trans ?_ exp_one_mul_phi_bound_le
  exact le_mul_of_one_le_left (by positivity) (Real.one_le_exp zero_le_one)

/-- $\mathrm{pair}(z) \ge -12$ for every $z$. -/
theorem pair_ge (z : ℝ × ℝ) : -12 ≤ pair z := by
  have h1 : 0 ≤ psi (-z.1) * phi (-z.2) := mul_nonneg (psi_nonneg _) (phi_nonneg _)
  have h2 : psi z.1 * phi z.2 ≤ exp 1 * (exp (1 / 2) * √(2 * π)) :=
    mul_le_mul (psi_le _) (phi_le _) (phi_nonneg _) (exp_pos 1).le
  have := exp_one_mul_phi_bound_le
  unfold pair; linarith

/-- $\mathrm{chain}_T(0) = -\Phi(0)$. -/
theorem chain_zero : chain T 0 = -phi 0 := by
  rw [chain_eq, map_zero, Finset.sum_eq_zero fun l _ => pair_eq_zero (by simp), add_zero]

/-- $\mathrm{chain}_T(0) - 12T \le \mathrm{chain}_T(x)$ for every $x \in \mathbb{R}^T$. -/
theorem chain_zero_sub_le (x : EuclideanSpace ℝ (Fin T)) : chain T 0 - 12 * T ≤ chain T x := by
  rw [chain_zero, chain_eq]
  have hs : -12 * ((Finset.Ico 1 T).card : ℝ) ≤ ∑ l ∈ Finset.Ico 1 T, pair (pairMap T l x) := by
    have := Finset.card_nsmul_le_sum (Finset.Ico 1 T) (fun l => pair (pairMap T l x)) (-12)
      fun l _ => pair_ge _
    simpa [nsmul_eq_mul, mul_comm] using this
  rw [Nat.card_Ico] at hs
  have h0 := phi_nonneg 0
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp [coord_apply_of_le le_rfl] at hs ⊢
  · have hc := phi_le (coord T 0 x)
    have := phi_bound_le
    have hcast : ((T - 1 : ℕ) : ℝ) = T - 1 := by rw [Nat.cast_sub hT]; simp
    rw [hcast] at hs
    linarith

/-- **Lemma 4.2.5(iii)** of [cartis2022evaluation], which is Lemma 3(i) of Carmon, Duchi, Hinder and
Sidford. For every $T$, $\mathrm{chain}_T$ is bounded below on $\mathbb{R}^T$ and
$$\mathrm{chain}_T(0) - \inf_x \mathrm{chain}_T(x) \le 12T.$$
-/
theorem chain_zero_sub_iInf_le :
    BddBelow (range (chain T)) ∧ chain T 0 - ⨅ x, chain T x ≤ 12 * T := by
  refine ⟨⟨chain T 0 - 12 * T, by rintro _ ⟨x, rfl⟩; exact chain_zero_sub_le x⟩, ?_⟩
  have : chain T 0 - 12 * T ≤ ⨅ x, chain T x := le_ciInf chain_zero_sub_le
  linarith

/-! ### Theorem 4.2.6: the lower bound -/

section LowerBound

variable {p : ℕ} {c μ : ℝ}

/-- The scaled chain $x \mapsto c \, \mathrm{chain}_T(\mu^{-1} x)$. -/
noncomputable def scaledChain (T : ℕ) (c μ : ℝ) (x : EuclideanSpace ℝ (Fin T)) : ℝ :=
  c * chain T (μ⁻¹ • x)

/-- The scaled chain is $C^n$ for every $n \in \mathbb{N} \cup \{\infty\}$. -/
theorem contDiff_scaledChain {n : ℕ∞} : ContDiff ℝ n (scaledChain T c μ) :=
  contDiff_const.mul (contDiff_chain.comp (contDiff_const_smul _))

/-- For $c \ge 0$, $\mu > 0$, every $q$ and every $x$, the $q$-th derivative of the scaled chain
$x \mapsto c \, \mathrm{chain}_T(\mu^{-1} x)$ satisfies
$$\|\nabla^q (c \, \mathrm{chain}_T(\mu^{-1} \cdot))(x)\| \le c \mu^{-q} \|\nabla^q
  \mathrm{chain}_T(\mu^{-1} x)\|.$$
-/
theorem norm_iteratedFDeriv_scaledChain_le (hc : 0 ≤ c) (hμ : 0 < μ) (q : ℕ)
    (x : EuclideanSpace ℝ (Fin T)) : ‖iteratedFDeriv ℝ q (scaledChain T c μ) x‖ ≤
      c * μ⁻¹ ^ q * ‖iteratedFDeriv ℝ q (chain T) (μ⁻¹ • x)‖ := by
  set S : EuclideanSpace ℝ (Fin T) →L[ℝ] EuclideanSpace ℝ (Fin T) :=
    μ⁻¹ • ContinuousLinearMap.id ℝ _
  have hS : ∀ y, S y = μ⁻¹ • y := fun y => rfl
  have hSn : ‖S‖ ≤ μ⁻¹ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
    rw [hS, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hf : scaledChain T c μ = fun x => c • (chain T ∘ S) x := by
    funext y; simp [scaledChain, hS, smul_eq_mul]
  rw [hf, iteratedFDeriv_const_smul_apply' ((contDiff_chain (n := q)).comp S.contDiff).contDiffAt,
    norm_smul, Real.norm_of_nonneg hc, S.iteratedFDeriv_comp_right contDiff_chain x
      (by exact_mod_cast le_top), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [mul_comm, hS]
  gcongr
  calc ∏ _ : Fin q, ‖S‖ ≤ ∏ _ : Fin q, μ⁻¹ := by gcongr
    _ = μ⁻¹ ^ q := by simp

/-- For $c \ge 0$ and $\mu > 0$, the gradient of the scaled chain satisfies $\|\nabla (c \,
\mathrm{chain}_T(\mu^{-1} \cdot))(x)\| = c \mu^{-1} \|\nabla \mathrm{chain}_T(\mu^{-1} x)\|$. -/
theorem norm_fderiv_scaledChain (hc : 0 ≤ c) (hμ : 0 < μ) (x : EuclideanSpace ℝ (Fin T)) :
    ‖fderiv ℝ (scaledChain T c μ) x‖ = c * μ⁻¹ * ‖fderiv ℝ (chain T) (μ⁻¹ • x)‖ := by
  have hd : HasFDerivAt (chain T) (fderiv ℝ (chain T) (μ⁻¹ • x)) (μ⁻¹ • x) :=
    ((contDiff_chain (n := 1)).differentiable one_ne_zero _).hasFDerivAt
  have h := (hd.comp x ((hasFDerivAt_id x).const_smul μ⁻¹)).const_mul c
  have h' : HasFDerivAt (scaledChain T c μ)
      (c • (fderiv ℝ (chain T) (μ⁻¹ • x)).comp (μ⁻¹ • ContinuousLinearMap.id ℝ _)) x := h
  rw [h'.fderiv]
  have : c • (fderiv ℝ (chain T) (μ⁻¹ • x)).comp (μ⁻¹ • ContinuousLinearMap.id ℝ _) =
      (c * μ⁻¹) • fderiv ℝ (chain T) (μ⁻¹ • x) := by
    ext v; simp [mul_assoc]
  rw [this, norm_smul, Real.norm_of_nonneg (by positivity)]

/-- **Theorem 4.2.6** of [cartis2022evaluation], lower bound, in a form that holds for every class
of methods. Let $p \ge 1$ and $\Delta, L, \epsilon > 0$, let $L^D_p$ be
`Optimization.CarmonChain.lipschitzConst p`, and let
$$\bar{k} = \left\lfloor \frac{\Delta}{12} \Big( \frac{L}{L^D_p} \Big)^{1/p} \epsilon^{-(p+1)/p}
  \right\rfloor.$$
Then for every set $\mathcal{M}$ of $p$-th order methods,
$$\#_\epsilon(\mathcal{M}_{\mathrm{ZR}}(p), \mathcal{F}(\Delta, p)) \ge \bar{k}
  \quad\text{and}\quad \#_\epsilon(\mathcal{M}, \mathcal{F}(\Delta, p)) \ge \bar{k},$$
where $\mathcal{F}(\Delta, p)$ is the class `Optimization.smoothClass Δ L p` of the infinitely
differentiable functions $f \colon \mathbb{R}^n \to \mathbb{R}$, of any dimension $n$, that are
bounded below, satisfy $f(0) - \inf f \le \Delta$ and have an $L$-Lipschitz $p$-th derivative,
$\mathcal{M}_{\mathrm{ZR}}(p)$ is the class `Optimization.zeroRespectingClass p` of
zero-respecting methods, and $\#_\epsilon$ is the complexity `Optimization.classComplexity`.

The hard function is $x \mapsto \mu^{p+1} (L / L^D_p) \, \mathrm{chain}_{\bar{k}}(x / \mu)$ with
$\mu = (L^D_p \epsilon / L)^{1/p}$, as in (4.2.8). For the second bound, rotated copies of it on
$\mathbb{R}^{2\bar{k}}$ are used. The second bound applies in particular to $\mathcal{M}(p)$
(`Optimization.CarmonChain.le_classComplexity_smoothClass_methodClass`). Both classes are
nonempty (`Optimization.zeroRespectingClass_nonempty` and `Optimization.methodClass_nonempty`),
so the bounds are not vacuous. The floor is `Nat.floor`, and the complexities are in `ℕ∞`. -/
theorem le_classComplexity_smoothClass (hp : 1 ≤ p) {Δ L ε : ℝ} (hΔ : 0 < Δ) (hL : 0 < L)
    (hε : 0 < ε) (𝓜 : Set (JetMethod p)) :
    ((⌊Δ / 12 * (L / lipschitzConst p) ^ (1 / p : ℝ) * ε ^ (-((p + 1 : ℝ) / p))⌋₊ : ℕ) : ℕ∞) ≤
        classComplexity (zeroRespectingClass p) (smoothClass Δ L p) ε ∧
      ((⌊Δ / 12 * (L / lipschitzConst p) ^ (1 / p : ℝ) * ε ^ (-((p + 1 : ℝ) / p))⌋₊ : ℕ) : ℕ∞) ≤
        classComplexity 𝓜 (smoothClass Δ L p) ε := by
  set ℓ := lipschitzConst p
  have hℓ : 0 < ℓ := lipschitzConst_pos p
  set Y := Δ / 12 * (L / ℓ) ^ (1 / p : ℝ) * ε ^ (-((p + 1 : ℝ) / p))
  set k := ⌊Y⌋₊
  set μ := (ℓ * ε / L) ^ (1 / p : ℝ)
  set c := μ ^ (p + 1) * (L / ℓ)
  have hp0 : (p : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hμ : 0 < μ := Real.rpow_pos_of_pos (by positivity) _
  have hμp : μ ^ p = ℓ * ε / L := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), one_div_mul_cancel hp0,
      Real.rpow_one]
  have hc0 : 0 ≤ c := by positivity
  have hcμ : c * μ⁻¹ = ε := by
    simp only [c, pow_succ, hμp]
    field_simp
  have hcμq : c * μ⁻¹ ^ (p + 1) = L / ℓ := by
    simp only [c]
    rw [inv_pow]
    field_simp
  have hY : 0 ≤ Y := by positivity
  have hXc : Y * (12 * c) = Δ := by
    have hc : c = ε * μ := by
      simp only [c, pow_succ, hμp]; field_simp
    have hμ' : μ = (ℓ / L) ^ (1 / p : ℝ) * ε ^ (1 / p : ℝ) := by
      simp only [μ]
      rw [mul_div_right_comm, Real.mul_rpow (by positivity) hε.le]
    have h1 : (L / ℓ) ^ (1 / p : ℝ) * (ℓ / L) ^ (1 / p : ℝ) = 1 := by
      rw [← Real.mul_rpow (by positivity) (by positivity), div_mul_div_cancel₀ hℓ.ne',
        div_self hL.ne', Real.one_rpow]
    have h2 : ε ^ (-((p + 1 : ℝ) / p)) * ε * ε ^ (1 / p : ℝ) = 1 := by
      have hε1 : ε * ε ^ (1 / p : ℝ) = ε ^ (1 + 1 / p : ℝ) := by
        rw [Real.rpow_add hε, Real.rpow_one]
      rw [mul_assoc, hε1, ← Real.rpow_add hε]
      have : -((p + 1 : ℝ) / p) + (1 + 1 / p) = 0 := by field_simp; ring
      rw [this, Real.rpow_zero]
    rw [hc, hμ']
    calc Y * (12 * (ε * ((ℓ / L) ^ (1 / p : ℝ) * ε ^ (1 / p : ℝ))))
        = Δ * ((L / ℓ) ^ (1 / p : ℝ) * (ℓ / L) ^ (1 / p : ℝ)) *
            (ε ^ (-((p + 1 : ℝ) / p)) * ε * ε ^ (1 / p : ℝ)) := by simp only [Y]; ring
      _ = Δ := by rw [h1, h2, mul_one, mul_one]
  have hkc : 12 * k * c ≤ Δ :=
    calc 12 * (k : ℝ) * c = k * (12 * c) := by ring
      _ ≤ Y * (12 * c) := mul_le_mul_of_nonneg_right (Nat.floor_le hY) (by positivity)
      _ = Δ := hXc
  set f := scaledChain k c μ
  -- `f ∈ 𝓕(Δ, p)`
  have hlow : ∀ x, f 0 - 12 * k * c ≤ f x := by
    intro x
    have := chain_zero_sub_le (T := k) (μ⁻¹ • x)
    simp only [f, scaledChain, smul_zero]
    nlinarith
  have hmem : (⟨k, f⟩ : Σ n, EuclideanSpace ℝ (Fin n) → ℝ) ∈ smoothClass Δ L p := by
    refine ⟨contDiff_scaledChain, ?_, ⟨f 0 - 12 * k * c, by rintro _ ⟨x, rfl⟩; exact hlow x⟩, ?_⟩
    · refine iteratedFDerivLipschitzOn_of_norm_le convex_univ
        (fun _ _ => contDiff_scaledChain.contDiffAt) fun x _ => ?_
      refine (norm_iteratedFDeriv_scaledChain_le hc0 hμ _ x).trans ?_
      rw [hcμq]
      calc L / ℓ * ‖iteratedFDeriv ℝ (p + 1) (chain k) (μ⁻¹ • x)‖ ≤ L / ℓ * ℓ :=
            mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_chain_le hp _) (by positivity)
        _ = L := by field_simp
    · have : f 0 - 12 * k * c ≤ ⨅ x, f x := le_ciInf hlow
      dsimp only
      linarith
  have hzc : IsZeroChain f p := (isZeroChain_chain p).comp_smul c hμ.ne'
  have hgrad : ∀ (hn : 0 < k) (x : EuclideanSpace ℝ (Fin k)), x ⟨k - 1, by omega⟩ = 0 →
      ε < ‖fderiv ℝ f x‖ := by
    intro hn x hx
    have hy : |(μ⁻¹ • x) ⟨k - 1, by omega⟩| < 1 := by
      rw [PiLp.smul_apply, hx, smul_zero, abs_zero]; exact zero_lt_one
    obtain ⟨-, -, -, -, hg⟩ := exists_abs_partial_chain_gt_one hy
    rw [norm_fderiv_scaledChain hc0 hμ, hcμ]
    calc ε = ε * 1 := (mul_one ε).symm
      _ < ε * ‖fderiv ℝ (chain k) (μ⁻¹ • x)‖ := mul_lt_mul_of_pos_left hg hε
  obtain ⟨h1, h2⟩ := le_classComplexity_of_isZeroChain hzc hgrad hmem
  exact ⟨h2, le_classComplexity_of_comp_adjoint_mem 𝓜 contDiff_scaledChain
    ((contDiff_scaledChain (n := 1)).differentiable one_ne_zero) h1
    fun U => comp_adjoint_mem_smoothClass hL.le hmem U⟩

/-- **Theorem 4.2.6** of [cartis2022evaluation]. Let $p \ge 1$ and $\Delta, L, \epsilon > 0$, let
$L^D_p$ be `Optimization.CarmonChain.lipschitzConst p`, and let
$$\bar{k} = \left\lfloor \frac{\Delta}{12} \Big( \frac{L}{L^D_p} \Big)^{1/p} \epsilon^{-(p+1)/p}
  \right\rfloor.$$
Then
$$\#_\epsilon(\mathcal{M}_{\mathrm{ZR}}(p), \mathcal{F}(\Delta, p)) \ge \bar{k}
  \quad\text{and}\quad \#_\epsilon(\mathcal{M}(p), \mathcal{F}(\Delta, p)) \ge \bar{k}.$$

This is `Optimization.CarmonChain.le_classComplexity_smoothClass` for the class $\mathcal{M}(p)$
of `Optimization.methodClass p`. -/
theorem le_classComplexity_smoothClass_methodClass (hp : 1 ≤ p) {Δ L ε : ℝ} (hΔ : 0 < Δ)
    (hL : 0 < L) (hε : 0 < ε) :
    ((⌊Δ / 12 * (L / lipschitzConst p) ^ (1 / p : ℝ) * ε ^ (-((p + 1 : ℝ) / p))⌋₊ : ℕ) : ℕ∞) ≤
        classComplexity (zeroRespectingClass p) (smoothClass Δ L p) ε ∧
      ((⌊Δ / 12 * (L / lipschitzConst p) ^ (1 / p : ℝ) * ε ^ (-((p + 1 : ℝ) / p))⌋₊ : ℕ) : ℕ∞) ≤
        classComplexity (methodClass p) (smoothClass Δ L p) ε :=
  le_classComplexity_smoothClass hp hΔ hL hε (methodClass p)

end LowerBound

/-! ### Explicit growth of the constant $L^D_p$ -/

/-- The sum $\sum_m |a_m|$ of the absolute values of the coefficients $a_m$ of a real polynomial. -/
noncomputable def coeffAbsSum (P : ℝ[X]) : ℝ :=
  ∑ m ∈ Finset.range (P.natDegree + 1), |P.coeff m|

/-- If $\deg P < N$, the sum of the absolute values of the coefficients of $P$ can be taken over
$m < N$. -/
theorem coeffAbsSum_eq_sum_range {P : ℝ[X]} {N : ℕ} (h : P.natDegree < N) :
    coeffAbsSum P = ∑ m ∈ Finset.range N, |P.coeff m| := by
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun m _ hm => ?_
  rw [Finset.mem_range, not_lt] at hm
  rw [coeff_eq_zero_of_natDegree_lt (by omega), abs_zero]

/-- The sum of the absolute values of the coefficients is nonnegative. -/
theorem coeffAbsSum_nonneg (P : ℝ[X]) : 0 ≤ coeffAbsSum P :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The sum of the absolute values of the coefficients is subadditive: for $P + Q$ it is at most
that of $P$ plus that of $Q$. -/
theorem coeffAbsSum_add_le (P Q : ℝ[X]) :
    coeffAbsSum (P + Q) ≤ coeffAbsSum P + coeffAbsSum Q := by
  have hP : P.natDegree < max P.natDegree Q.natDegree + 1 := by omega
  have hQ : Q.natDegree < max P.natDegree Q.natDegree + 1 := by omega
  have hPQ : (P + Q).natDegree < max P.natDegree Q.natDegree + 1 :=
    (natDegree_add_le P Q).trans_lt (by omega)
  rw [coeffAbsSum_eq_sum_range hP, coeffAbsSum_eq_sum_range hQ, coeffAbsSum_eq_sum_range hPQ,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun m _ => by rw [coeff_add]; exact abs_add_le _ _

/-- $P$ and $-P$ have the same sum of the absolute values of the coefficients. -/
theorem coeffAbsSum_neg (P : ℝ[X]) : coeffAbsSum (-P) = coeffAbsSum P := by
  simp [coeffAbsSum, natDegree_neg]

/-- For $P - Q$, the sum of the absolute values of the coefficients is at most that of $P$ plus that
of $Q$. -/
theorem coeffAbsSum_sub_le (P Q : ℝ[X]) :
    coeffAbsSum (P - Q) ≤ coeffAbsSum P + coeffAbsSum Q := by
  rw [sub_eq_add_neg, ← coeffAbsSum_neg Q]
  exact coeffAbsSum_add_le _ _

/-- Multiplication by $X^k$ shifts the coefficients, so it does not change the sum of their absolute
values. -/
theorem coeffAbsSum_X_pow_mul (k : ℕ) (P : ℝ[X]) :
    coeffAbsSum (X ^ k * P) = coeffAbsSum P := by
  have h : (X ^ k * P).natDegree < k + (P.natDegree + 1) :=
    (natDegree_mul_le.trans (Nat.add_le_add_right (natDegree_X_pow_le k) _)).trans_lt (by omega)
  rw [coeffAbsSum_eq_sum_range h, Finset.sum_range_add, coeffAbsSum]
  have h0 : ∑ m ∈ Finset.range k, |(X ^ k * P).coeff m| = 0 :=
    Finset.sum_eq_zero fun m hm => by
      have : ¬ k ≤ m := by simp at hm; omega
      simp [coeff_X_pow_mul', this]
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [coeff_X_pow_mul']

/-- For the derivative of a real polynomial $P$, $\sum_m |a_m(P')| \le \deg P \cdot \sum_m
|a_m(P)|$.
-/
theorem coeffAbsSum_derivative_le (P : ℝ[X]) :
    coeffAbsSum (derivative P) ≤ P.natDegree * coeffAbsSum P := by
  have h : (derivative P).natDegree < P.natDegree + 1 :=
    (natDegree_derivative_le P).trans_lt (by omega)
  rw [coeffAbsSum_eq_sum_range h, coeffAbsSum_eq_sum_range (N := P.natDegree + 1 + 1) (by omega),
    Finset.sum_range_succ' (fun m => |P.coeff m|), mul_add, Finset.mul_sum]
  have hle : ∀ m ∈ Finset.range (P.natDegree + 1),
      |(derivative P).coeff m| ≤ P.natDegree * |P.coeff (m + 1)| := by
    intro m _
    rw [coeff_derivative, abs_mul]
    by_cases hc : P.coeff (m + 1) = 0
    · simp [hc]
    · have := le_natDegree_of_ne_zero hc
      rw [mul_comm, abs_of_nonneg (by positivity)]
      gcongr
      exact_mod_cast this
  exact (Finset.sum_le_sum hle).trans
    (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)))

/-- If $\deg P \le d$, then $|P(y)| \le \big( \sum_m |a_m(P)| \big) (1 + |y|^d)$ for every $y$. -/
theorem abs_eval_le_coeffAbsSum {P : ℝ[X]} {d : ℕ} (hd : P.natDegree ≤ d) (y : ℝ) :
    |P.eval y| ≤ coeffAbsSum P * (1 + |y| ^ d) := by
  rw [eval_eq_sum_range, coeffAbsSum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [abs_mul, abs_pow]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rcases le_or_gt |y| 1 with h | h
  · have := pow_le_one₀ (n := m) (abs_nonneg y) h
    have := pow_nonneg (abs_nonneg y) d
    linarith
  · have := pow_le_pow_right₀ h.le (show m ≤ d by simp at hm; omega)
    linarith

/-- $2X^3 P - X^2 P' = X^3 P + X^3 P - X^2 P'$. -/
theorem flatDerivPoly_eq (P : ℝ[X]) :
    flatDerivPoly P = X ^ 3 * P + X ^ 3 * P - X ^ 2 * derivative P := by
  rw [flatDerivPoly]; ring

/-- The polynomials of the derivatives of the flat function satisfy $\deg P_j \le 3j$. -/
theorem natDegree_flatPoly_le (j : ℕ) : (flatPoly j).natDegree ≤ 3 * j := by
  induction j with
  | zero => simp [flatPoly]
  | succ j ih =>
    rw [flatPoly, flatDerivPoly_eq]
    have h3 := natDegree_X_pow_le (R := ℝ) 3
    have h2 := natDegree_X_pow_le (R := ℝ) 2
    have hd := natDegree_derivative_le (flatPoly j)
    have h1 : (X ^ 3 * flatPoly j).natDegree ≤ 3 * (j + 1) :=
      natDegree_mul_le.trans (by omega)
    have h2 : (X ^ 2 * derivative (flatPoly j)).natDegree ≤ 3 * (j + 1) :=
      natDegree_mul_le.trans (by omega)
    exact (natDegree_sub_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le h1 h1)) h2)

/-- The polynomials of the derivatives of the flat function satisfy $\sum_m |a_m(P_j)| \le 3^j j!$.
The proof uses $P_{j+1} = 2X^3 P_j - X^2 P_j'$. -/
theorem coeffAbsSum_flatPoly_le (j : ℕ) : coeffAbsSum (flatPoly j) ≤ 3 ^ j * j.factorial := by
  induction j with
  | zero => simp [flatPoly, coeffAbsSum]
  | succ j ih =>
    rw [flatPoly, flatDerivPoly_eq]
    have hd := coeffAbsSum_derivative_le (flatPoly j)
    have hdeg : ((flatPoly j).natDegree : ℝ) ≤ 3 * j := by exact_mod_cast natDegree_flatPoly_le j
    have h0 := coeffAbsSum_nonneg (flatPoly j)
    calc _ ≤ coeffAbsSum (X ^ 3 * flatPoly j) + coeffAbsSum (X ^ 3 * flatPoly j) +
          coeffAbsSum (X ^ 2 * derivative (flatPoly j)) :=
by
            have := coeffAbsSum_sub_le (X ^ 3 * flatPoly j + X ^ 3 * flatPoly j)
              (X ^ 2 * derivative (flatPoly j))
            have := coeffAbsSum_add_le (X ^ 3 * flatPoly j) (X ^ 3 * flatPoly j)
            linarith
      _ ≤ (3 * (j + 1)) * coeffAbsSum (flatPoly j) := by
          simp only [coeffAbsSum_X_pow_mul]; nlinarith
      _ ≤ (3 * (j + 1)) * (3 ^ j * j.factorial) := by gcongr
      _ = 3 ^ (j + 1) * (j + 1).factorial := by
          rw [Nat.factorial_succ]; push_cast; ring

/-- The polynomials of the derivatives of the Gaussian satisfy $\deg H_k \le k$. -/
theorem natDegree_gaussPoly_le (k : ℕ) : (gaussPoly k).natDegree ≤ k := by
  induction k with
  | zero => simp [gaussPoly]
  | succ k ih =>
    rw [gaussPoly]
    have hd := natDegree_derivative_le (gaussPoly k)
    have h1 : (X * gaussPoly k).natDegree ≤ k + 1 :=
      natDegree_mul_le.trans (by have := natDegree_X_le (R := ℝ); omega)
    exact (natDegree_sub_le _ _).trans (max_le (by omega) h1)

/-- The polynomials of the derivatives of the Gaussian satisfy $\sum_m |a_m(H_k)| \le k!$. The proof
uses $H_{k+1} = H_k' - X H_k$. -/
theorem coeffAbsSum_gaussPoly_le (k : ℕ) : coeffAbsSum (gaussPoly k) ≤ k.factorial := by
  induction k with
  | zero => simp [gaussPoly, coeffAbsSum]
  | succ k ih =>
    rw [gaussPoly]
    have hd := coeffAbsSum_derivative_le (gaussPoly k)
    have hdeg : ((gaussPoly k).natDegree : ℝ) ≤ k := by exact_mod_cast natDegree_gaussPoly_le k
    have h0 := coeffAbsSum_nonneg (gaussPoly k)
    have hX : coeffAbsSum (X * gaussPoly k) = coeffAbsSum (gaussPoly k) := by
      simpa using coeffAbsSum_X_pow_mul 1 (gaussPoly k)
    calc _ ≤ coeffAbsSum (derivative (gaussPoly k)) + coeffAbsSum (X * gaussPoly k) :=
          coeffAbsSum_sub_le _ _
      _ ≤ (k + 1) * coeffAbsSum (gaussPoly k) := by rw [hX]; nlinarith
      _ ≤ (k + 1) * k.factorial := by gcongr
      _ = (k + 1).factorial := by rw [Nat.factorial_succ]; push_cast; ring

/-- $x^k e^{-x} \le k!$ for every $x \ge 0$ and every $k$. -/
theorem pow_mul_exp_neg_le_factorial {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    x ^ k * exp (-x) ≤ k.factorial := by
  have := Real.pow_div_factorial_le_exp x hx k
  rw [div_le_iff₀ (by positivity)] at this
  rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _)]
  linarith [mul_comm (exp x) (k.factorial : ℝ)]

/-- $|t|^{3j} e^{-t^2} \le \sqrt{(3j)!}$ for every $t$ and every $j$. -/
theorem abs_pow_mul_exp_neg_sq_le (t : ℝ) (j : ℕ) :
    |t| ^ (3 * j) * exp (-t ^ 2) ≤ √((3 * j).factorial) := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  have h := pow_mul_exp_neg_le_factorial (x := 2 * t ^ 2) (by positivity) (3 * j)
  calc (|t| ^ (3 * j) * exp (-t ^ 2)) ^ 2 = (t ^ 2) ^ (3 * j) * exp (-(2 * t ^ 2)) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 1
        · rw [← pow_mul, mul_comm, pow_mul, sq_abs]
        · push_cast; ring_nf
    _ ≤ (2 * t ^ 2) ^ (3 * j) * exp (-(2 * t ^ 2)) := by
        gcongr; nlinarith [sq_nonneg t]
    _ ≤ _ := h

/-- $|y|^k e^{-y^2/2} \le \sqrt{k!}$ for every $y$ and every $k$. -/
theorem abs_pow_mul_gauss_le (y : ℝ) (k : ℕ) :
    |y| ^ k * exp (-y ^ 2 / 2) ≤ √(k.factorial) := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  have h := pow_mul_exp_neg_le_factorial (x := y ^ 2) (by positivity) k
  calc (|y| ^ k * exp (-y ^ 2 / 2)) ^ 2 = (y ^ 2) ^ k * exp (-(y ^ 2)) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 1
        · rw [← pow_mul, mul_comm, pow_mul, sq_abs]
        · push_cast; ring_nf
    _ ≤ _ := h

/-- For all natural numbers $a$ and $b$, $a! \, (1 + \sqrt{b!}) \le 2 \sqrt{(a!)^2 \, b!}$. -/
theorem factorial_mul_one_add_sqrt_le (a b : ℕ) :
    (a.factorial : ℝ) * (1 + √(b.factorial)) ≤ 2 * √((a.factorial ^ 2 * b.factorial : ℕ)) := by
  have hb : (1 : ℝ) ≤ √(b.factorial) :=
    Real.one_le_sqrt.2 (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero b))
  have ha : (0 : ℝ) ≤ a.factorial := Nat.cast_nonneg _
  have : √((a.factorial ^ 2 * b.factorial : ℕ) : ℝ) = a.factorial * √(b.factorial) := by
    push_cast
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ha]
  rw [this]
  nlinarith

/-- The growth scale $\sqrt{q^{5q}}$. -/
noncomputable def growthScale (q : ℕ) : ℝ := √((q : ℝ) ^ (5 * q))

/-- The growth scale is at least $1$. -/
theorem one_le_growthScale (q : ℕ) : 1 ≤ growthScale q := by
  refine Real.one_le_sqrt.2 ?_
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · exact one_le_pow₀ (by exact_mod_cast hq)

/-- For $i \le q$, $\sqrt{i^{5i}} \sqrt{(q - i)^{5(q - i)}} \le \sqrt{q^{5q}}$. -/
theorem growthScale_mul_le {i q : ℕ} (hi : i ≤ q) :
    growthScale i * growthScale (q - i) ≤ growthScale q := by
  rw [growthScale, growthScale, growthScale, ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  calc (i : ℝ) ^ (5 * i) * ((q - i : ℕ) : ℝ) ^ (5 * (q - i))
      ≤ (q : ℝ) ^ (5 * i) * (q : ℝ) ^ (5 * (q - i)) := by
        gcongr
        exact_mod_cast Nat.sub_le q i
    _ = (q : ℝ) ^ (5 * q) := by rw [← pow_add]; congr 1; omega

/-- The square of the growth scale is $q^{5q}$. -/
theorem growthScale_sq (q : ℕ) : growthScale q ^ 2 = (q : ℝ) ^ (5 * q) :=
  Real.sq_sqrt (by positivity)

/-- $\big| \Psi^{(j)}(y) \big| \le e \, 6^j \, j! \, \big( 1 + \sqrt{(3j)!} \big)$ for every $y$ and
every $j$, with $\Psi^{(j)}$ written as `Optimization.CarmonChain.psiDeriv j`. -/
theorem abs_psiDeriv_le (j : ℕ) (y : ℝ) :
    |psiDeriv j y| ≤ exp 1 * 6 ^ j * (j.factorial * (1 + √((3 * j).factorial))) := by
  rw [psiDeriv, abs_mul, abs_of_pos (by positivity), show (6 : ℝ) ^ j = 2 ^ j * 3 ^ j by
    rw [← mul_pow]; norm_num, mul_assoc (exp 1), mul_assoc (exp 1)]
  refine mul_le_mul_of_nonneg_left ?_ (exp_pos 1).le
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  set s := 2 * y - 1
  rcases le_or_gt s 0 with hs | hs
  · rw [flat_of_nonpos hs, mul_zero, abs_zero]; positivity
  rw [flat_of_pos hs, abs_mul, abs_of_pos (exp_pos _)]
  set t := s⁻¹
  have ht : (s ^ 2)⁻¹ = t ^ 2 := by rw [inv_pow]
  rw [ht]
  have h1 := abs_eval_le_coeffAbsSum (natDegree_flatPoly_le j) t
  have h2 := coeffAbsSum_flatPoly_le j
  have h3 := abs_pow_mul_exp_neg_sq_le t j
  have h4 : exp (-t ^ 2) ≤ 1 := exp_le_one_iff.2 (by nlinarith [sq_nonneg t])
  have h5 := coeffAbsSum_nonneg (flatPoly j)
  calc |(flatPoly j).eval t| * exp (-t ^ 2)
      ≤ coeffAbsSum (flatPoly j) * (1 + |t| ^ (3 * j)) * exp (-t ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (exp_pos _).le
    _ = coeffAbsSum (flatPoly j) * (exp (-t ^ 2) + |t| ^ (3 * j) * exp (-t ^ 2)) := by ring
    _ ≤ (3 ^ j * j.factorial) * (1 + √((3 * j).factorial)) := by
        gcongr
    _ = _ := by ring

/-- $\sup |\Psi^{(j)}| \le 6 \cdot 36^j \sqrt{j^{5j}}$. -/
theorem psiBound_le (j : ℕ) : psiBound j ≤ 6 * 36 ^ j * growthScale j := by
  have hnat : j.factorial ^ 2 * (3 * j).factorial ≤ 36 ^ j * j ^ (5 * j) :=
    calc j.factorial ^ 2 * (3 * j).factorial ≤ (j ^ j) ^ 2 * (3 * j) ^ (3 * j) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.factorial_le_pow j) 2) (Nat.factorial_le_pow _)
      _ = 27 ^ j * j ^ (5 * j) := by
          rw [mul_pow, show (3 : ℕ) ^ (3 * j) = 27 ^ j by rw [pow_mul]; norm_num]; ring
      _ ≤ 36 ^ j * j ^ (5 * j) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) j)
  have hW : √((j.factorial ^ 2 * (3 * j).factorial : ℕ) : ℝ) ≤ 6 ^ j * growthScale j := by
    calc √((j.factorial ^ 2 * (3 * j).factorial : ℕ) : ℝ) ≤ √((36 ^ j * j ^ (5 * j) : ℕ) : ℝ) :=
          Real.sqrt_le_sqrt (by exact_mod_cast hnat)
      _ = 6 ^ j * growthScale j := by
          push_cast
          rw [Real.sqrt_mul (by positivity), growthScale,
            show (36 : ℝ) ^ j = (6 ^ j) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
            Real.sqrt_sq (by positivity)]
  have he : exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans_le (by norm_num)).le
  refine ciSup_le fun y => ?_
  rw [iteratedDeriv_psi]
  refine (abs_psiDeriv_le j y).trans ?_
  have := factorial_mul_one_add_sqrt_le j (3 * j)
  have hg := one_le_growthScale j
  calc exp 1 * 6 ^ j * (j.factorial * (1 + √((3 * j).factorial)))
      ≤ 3 * 6 ^ j * (2 * (6 ^ j * growthScale j)) :=
        mul_le_mul (by gcongr) (this.trans (by linarith)) (by positivity) (by positivity)
    _ = 6 * 36 ^ j * growthScale j := by
        rw [show (36 : ℝ) ^ j = 6 ^ j * 6 ^ j by rw [← mul_pow]; norm_num]; ring

/-- $\sup |\Phi^{(k)}| \le 12 \sqrt{k^{5k}}$. This is a crude bound, enough for the growth estimate.
-/
theorem phiBound_le (k : ℕ) : phiBound k ≤ 12 * growthScale k := by
  rcases k with _ | k
  · refine ciSup_le fun y => ?_
    rw [iteratedDeriv_zero, abs_of_nonneg (phi_nonneg y), growthScale]
    simpa using (phi_le y).trans phi_bound_le
  have hnat : k.factorial ^ 2 * k.factorial ≤ (k + 1) ^ (5 * (k + 1)) :=
    calc k.factorial ^ 2 * k.factorial = k.factorial ^ 3 := by ring
      _ ≤ ((k + 1) ^ (k + 1)) ^ 3 := Nat.pow_le_pow_left ((Nat.factorial_le_pow k).trans
          ((Nat.pow_le_pow_left k.le_succ k).trans (Nat.pow_le_pow_right k.succ_pos k.le_succ))) 3
      _ ≤ (k + 1) ^ (5 * (k + 1)) := by
          rw [← pow_mul]; exact Nat.pow_le_pow_right k.succ_pos (by omega)
  have he : exp (1 / 2) ≤ 3 :=
    ((exp_le_exp.2 (by norm_num : (1 : ℝ) / 2 ≤ 1)).trans Real.exp_one_lt_d9.le).trans
      (by norm_num)
  refine ciSup_le fun y => ?_
  rw [iteratedDeriv_succ_phi, abs_mul, abs_of_pos (exp_pos _), abs_mul, abs_of_pos (exp_pos _)]
  have h1 := abs_eval_le_coeffAbsSum (natDegree_gaussPoly_le k) y
  have h2 := coeffAbsSum_gaussPoly_le k
  have h3 := abs_pow_mul_gauss_le y k
  have h4 : exp (-y ^ 2 / 2) ≤ 1 := exp_le_one_iff.2 (by nlinarith [sq_nonneg y])
  have h5 := coeffAbsSum_nonneg (gaussPoly k)
  have h6 := factorial_mul_one_add_sqrt_le k k
  have h7 : √((k.factorial ^ 2 * k.factorial : ℕ) : ℝ) ≤ growthScale (k + 1) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hnat)
  calc exp (1 / 2) * (|(gaussPoly k).eval y| * exp (-y ^ 2 / 2))
      ≤ 3 * (coeffAbsSum (gaussPoly k) * (1 + |y| ^ k) * exp (-y ^ 2 / 2)) := by
        gcongr
    _ = 3 * (coeffAbsSum (gaussPoly k) * (exp (-y ^ 2 / 2) + |y| ^ k * exp (-y ^ 2 / 2))) := by
        ring
    _ ≤ 3 * (k.factorial * (1 + √(k.factorial))) := by gcongr
    _ ≤ 3 * (2 * growthScale (k + 1)) :=
        mul_le_mul_of_nonneg_left (h6.trans (by linarith)) (by norm_num)
    _ ≤ 12 * growthScale (k + 1) := by nlinarith [one_le_growthScale (k + 1)]

/-- $\mathrm{pairBound}(q) \le 144 \cdot 72^q \sqrt{q^{5q}}$. -/
theorem pairBound_le (q : ℕ) : pairBound q ≤ 144 * 72 ^ q * growthScale q := by
  have hW := one_le_growthScale q
  have hterm : ∀ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * psiBound i * phiBound (q - i) ≤
      (q.choose i : ℝ) * (72 * 36 ^ q * growthScale q) := by
    intro i hi
    have hi : i ≤ q := by simp at hi; omega
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have h36 : (36 : ℝ) ^ i ≤ 36 ^ q := pow_le_pow_right₀ (by norm_num) hi
    have hg := growthScale_mul_le hi
    calc psiBound i * phiBound (q - i)
        ≤ (6 * 36 ^ i * growthScale i) * (12 * growthScale (q - i)) :=
          mul_le_mul (psiBound_le i) (phiBound_le _) (phiBound_nonneg _)
            (by have := one_le_growthScale i; positivity)
      _ = 72 * 36 ^ i * (growthScale i * growthScale (q - i)) := by ring
      _ ≤ 72 * 36 ^ q * growthScale q := by
          gcongr
          exact mul_nonneg (by linarith [one_le_growthScale i])
            (by linarith [one_le_growthScale (q - i)])
  have hchoose : ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) = 2 ^ q := by
    exact_mod_cast Nat.sum_range_choose q
  rw [pairBound]
  calc 2 * ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * psiBound i * phiBound (q - i)
      ≤ 2 * ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * (72 * 36 ^ q * growthScale q) := by
        gcongr 2 * ?_; exact Finset.sum_le_sum hterm
    _ = 144 * 72 ^ q * growthScale q := by
        rw [← Finset.sum_mul, hchoose, show (72 : ℝ) ^ q = 2 ^ q * 36 ^ q by
          rw [← mul_pow]; norm_num]
        ring

/-- $L^D_p \le 301 \cdot 72^{p+1} \sqrt{(p + 1)^{5(p+1)}}$. -/
theorem lipschitzConst_le_growthScale (p : ℕ) :
    lipschitzConst p ≤ 301 * 72 ^ (p + 1) * growthScale (p + 1) := by
  have h1 := phiBound_le (p + 1)
  have h2 := pairBound_le (p + 1)
  have hW := one_le_growthScale (p + 1)
  have h72 : (1 : ℝ) ≤ 72 ^ (p + 1) := one_le_pow₀ (by norm_num)
  rw [lipschitzConst]
  nlinarith

/-- The arithmetic step: for every natural number $p \ge 1$,
$$301^2 \cdot 72^{2(p+1)} (p + 1)^{5(p+1)} \le (301^2 \cdot 72^4 \cdot 32^3)^p \, p^{5p}.$$
-/
theorem lipschitzConst_nat_aux {p : ℕ} (hp : 1 ≤ p) :
    301 ^ 2 * 72 ^ (2 * (p + 1)) * (p + 1) ^ (5 * (p + 1)) ≤
      (301 ^ 2 * 72 ^ 4 * 32 ^ 3) ^ p * p ^ (5 * p) := by
  have h5 : p ^ 5 ≤ 32 ^ p := by
    calc p ^ 5 ≤ (2 ^ p) ^ 5 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 5
      _ = 32 ^ p := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h1 : (p + 1) ^ (5 * (p + 1)) ≤ 32 ^ (p + 1) * 32 ^ p * p ^ (5 * p) :=
    calc (p + 1) ^ (5 * (p + 1)) ≤ (2 * p) ^ (5 * (p + 1)) := Nat.pow_le_pow_left (by omega) _
      _ = 32 ^ (p + 1) * p ^ 5 * p ^ (5 * p) := by
          rw [mul_pow, pow_mul 2 5 (p + 1)]; norm_num; ring
      _ ≤ 32 ^ (p + 1) * 32 ^ p * p ^ (5 * p) := by gcongr
  have ha : 301 ^ 2 ≤ 301 ^ (2 * p) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb : 72 ^ (2 * (p + 1)) ≤ 72 ^ (4 * p) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hc : 32 ^ (p + 1) * 32 ^ p ≤ 32 ^ (3 * p) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 301 ^ 2 * 72 ^ (2 * (p + 1)) * (p + 1) ^ (5 * (p + 1))
      ≤ 301 ^ 2 * 72 ^ (2 * (p + 1)) * (32 ^ (p + 1) * 32 ^ p * p ^ (5 * p)) := by gcongr
    _ ≤ 301 ^ (2 * p) * 72 ^ (4 * p) * (32 ^ (3 * p) * p ^ (5 * p)) := by gcongr
    _ = (301 ^ 2 * 72 ^ 4 * 32 ^ 3) ^ p * p ^ (5 * p) := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]; ring

/-- For $p \ge 1$, $(L^D_p)^2 \le Q^p p^{5p}$ with $Q = 301^2 \cdot 72^4 \cdot 32^3$. Note that
$Q \le e^{40}$. -/
theorem lipschitzConst_sq_le {p : ℕ} (hp : 1 ≤ p) :
    lipschitzConst p ^ 2 ≤ ((301 ^ 2 * 72 ^ 4 * 32 ^ 3 : ℕ) : ℝ) ^ p * (p : ℝ) ^ (5 * p) := by
  have h := lipschitzConst_le_growthScale p
  have h0 := (lipschitzConst_pos p).le
  calc lipschitzConst p ^ 2 ≤ (301 * 72 ^ (p + 1) * growthScale (p + 1)) ^ 2 := by gcongr
    _ = ((301 ^ 2 * 72 ^ (2 * (p + 1)) * (p + 1) ^ (5 * (p + 1)) : ℕ) : ℝ) := by
        rw [mul_pow, mul_pow, growthScale_sq, ← pow_mul, mul_comm (p + 1) 2]; push_cast; ring
    _ ≤ (((301 ^ 2 * 72 ^ 4 * 32 ^ 3) ^ p * p ^ (5 * p) : ℕ) : ℝ) := by
        exact_mod_cast lipschitzConst_nat_aux hp
    _ = _ := by push_cast; ring

/-- **Lemma 4.2.5(iv)** of [cartis2022evaluation], explicit growth with $c_1 = 20$, after Lemma 3 of
Carmon, Duchi, Hinder and Sidford. For every $p \ge 1$,
$$L^D_p \le \exp\Big( \frac{5}{2} p \log p + 20 p \Big),$$
where $L^D_p$ is `Optimization.CarmonChain.lipschitzConst p`. -/
theorem lipschitzConst_le_exp_twenty {p : ℕ} (hp : 1 ≤ p) :
    lipschitzConst p ≤ exp (5 / 2 * p * log p + 20 * p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hQ : ((301 ^ 2 * 72 ^ 4 * 32 ^ 3 : ℕ) : ℝ) ≤ exp 40 := by
    have h := Real.exp_one_gt_d9
    have : (2.7182818283 : ℝ) ^ 40 ≤ exp 1 ^ 40 := by gcongr
    rw [← Real.exp_nat_mul] at this
    norm_num at this ⊢
    linarith
  have hsq : lipschitzConst p ^ 2 ≤ exp (5 / 2 * p * log p + 20 * p) ^ 2 := by
    refine (lipschitzConst_sq_le hp).trans ?_
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (5 / 2 * p * log p + 20 * p) =
      (5 * p : ℕ) * log p + p * 40 by push_cast; ring, exp_add, Real.exp_nat_mul,
      Real.exp_log hp0, Real.exp_nat_mul, mul_comm]
    gcongr
  exact (pow_le_pow_iff_left₀ (lipschitzConst_pos p).le (exp_pos _).le two_ne_zero).1 hsq

/-- **Lemma 4.2.5(iv)** of [cartis2022evaluation], explicit growth, after Lemma 3(iii) of Carmon,
Duchi, Hinder and Sidford. There is an absolute constant $c_1 > 0$ such that for every $p \ge 1$
$$L^D_p \le \exp\Big( \frac{5}{2} p \log p + c_1 p \Big),$$
where $L^D_p$ is `Optimization.CarmonChain.lipschitzConst p`.

The constant $c_1 = 20$ works (`Optimization.CarmonChain.lipschitzConst_le_exp_twenty`). -/
theorem lipschitzConst_le_exp :
    ∃ c₁ > 0, ∀ p : ℕ, 1 ≤ p → lipschitzConst p ≤ exp (5 / 2 * p * log p + c₁ * p) :=
  ⟨20, by norm_num, fun _ hp => lipschitzConst_le_exp_twenty hp⟩

end CarmonChain

end Optimization
