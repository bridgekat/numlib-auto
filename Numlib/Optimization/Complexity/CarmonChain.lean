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

The difficult function of [cartis2022evaluation], (4.2.6) and Lemma 4.2.5, after Carmon, Duchi,
Hinder and Sidford (*Lower bounds for finding stationary points I*, §3.2, Lemmas 1–3), and the
resulting lower bound for `p`-th order methods (Theorem 4.2.6).

On `ℝ^T` (coordinates `x_0, …, x_{T-1}`):
`chain T x = -Ψ(1) Φ(x_0) + ∑_{i=1}^{T-1} [Ψ(-x_{i-1}) Φ(-x_i) - Ψ(x_{i-1}) Φ(x_i)]`, with
`Ψ y = 0` for `y ≤ 1/2`, `Ψ y = exp(1 - (2y-1)^{-2})` otherwise, and
`Φ y = e^{1/2} ∫_{-∞}^y exp(-t²/2) dt`.

The first term `-Ψ(1) Φ(x_0)` (with `Ψ(1) = 1`) is that of Carmon et al.; it makes the gradient
nonzero at `x = 0`, as Lemma 4.2.5 (ii) requires.

## Main results

* `psi`, `phi`: the functions `Ψ`, `Φ`, smooth, with bounded derivatives of every order.
* `isZeroChain_chain`: Lemma 4.2.5 (i).
* `exists_abs_partial_chain_gt_one`: Lemma 4.2.5 (ii).
* `chain_zero_sub_iInf_le`: Lemma 4.2.5 (iii).
* `norm_iteratedFDeriv_chain_le`, `lipschitzOn_iteratedFDeriv_chain`: Lemma 4.2.5 (iv), with an
  explicit constant `lipschitzConst p` independent of the dimension `T`.
* `lipschitzConst_le_exp`: the growth `lipschitzConst p ≤ exp (5/2 p log p + c₁ p)` of
  Lemma 4.2.5 (iv), with `c₁ = 20` (`lipschitzConst_le_exp_twenty`), via coefficient bounds for
  the polynomials of the derivatives of `Ψ` and `Φ` and `x^k e^{-x} ≤ k!`.
* `le_classComplexity_smoothClass`: the lower bound of Theorem 4.2.6.
-/

open Real Polynomial Filter Topology Set MeasureTheory ContDiff

namespace Optimization

namespace CarmonChain

/-! ### The flat function `s ↦ exp(-s⁻²)` -/

/-- `flat s = exp(-1/s²)` for `s > 0` and `0` for `s ≤ 0`: a flat, smooth glue function. -/
noncomputable def flat (s : ℝ) : ℝ :=
  if s ≤ 0 then 0 else exp (-(s ^ 2)⁻¹)

theorem flat_of_nonpos {s : ℝ} (hs : s ≤ 0) : flat s = 0 := by simp [flat, hs]

theorem flat_of_pos {s : ℝ} (hs : 0 < s) : flat s = exp (-(s ^ 2)⁻¹) := by
  simp [flat, not_le.2 hs]

theorem flat_nonneg (s : ℝ) : 0 ≤ flat s := by
  rcases le_or_gt s 0 with hs | hs
  · rw [flat_of_nonpos hs]
  · rw [flat_of_pos hs]; exact (exp_pos _).le

theorem flat_le_one (s : ℝ) : flat s ≤ 1 := by
  rcases le_or_gt s 0 with hs | hs
  · rw [flat_of_nonpos hs]; exact zero_le_one
  · rw [flat_of_pos hs, exp_le_one_iff, neg_nonpos]; positivity

theorem flat_le_expNegInvGlue {s : ℝ} (hs : s ≤ 1) : flat s ≤ expNegInvGlue s := by
  rcases le_or_gt s 0 with h0 | h0
  · rw [flat_of_nonpos h0]; exact expNegInvGlue.nonneg s
  · simp only [flat_of_pos h0, expNegInvGlue, not_le.2 h0, ↓reduceIte]
    rw [exp_le_exp, neg_le_neg_iff]
    rw [inv_le_inv₀ h0 (by positivity)]
    nlinarith

/-- `P(1/s) flat(s) → 0` as `s → 0`, for every polynomial `P`. -/
theorem tendsto_polynomial_inv_mul_flat (P : ℝ[X]) :
    Tendsto (fun s => P.eval s⁻¹ * flat s) (𝓝 0) (𝓝 0) := by
  have h := (expNegInvGlue.tendsto_polynomial_inv_mul_zero P).norm
  rw [norm_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with s hs
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (flat_nonneg s),
    Real.norm_of_nonneg (expNegInvGlue.nonneg s)]
  exact mul_le_mul_of_nonneg_left (flat_le_expNegInvGlue hs.le) (norm_nonneg _)

/-- The polynomial of the derivative: `d/ds [P(1/s) flat(s)] = (2X³P - X²P')(1/s) flat(s)`. -/
noncomputable def flatDerivPoly (P : ℝ[X]) : ℝ[X] := 2 * X ^ 3 * P - X ^ 2 * derivative P

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

/-- `P(1/s) flat(s)` is bounded on `ℝ`. -/
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

/-! ### The function `Ψ` -/

/-- `Ψ(y) = 0` for `y ≤ 1/2` and `Ψ(y) = exp(1 - (2y - 1)^{-2})` otherwise
([cartis2022evaluation], (4.2.6)). -/
noncomputable def psi (y : ℝ) : ℝ :=
  if y ≤ 1 / 2 then 0 else exp (1 - ((2 * y - 1) ^ 2)⁻¹)

theorem psi_eq (y : ℝ) : psi y = exp 1 * flat (2 * y - 1) := by
  rcases le_or_gt y (1 / 2) with hy | hy
  · simp only [psi, hy, ↓reduceIte, flat_of_nonpos (by linarith : 2 * y - 1 ≤ 0), mul_zero]
  · simp only [psi, not_le.2 hy, ↓reduceIte]
    rw [flat_of_pos (by linarith), ← exp_add]
    ring_nf

theorem psi_of_le {y : ℝ} (hy : y ≤ 1 / 2) : psi y = 0 := by simp only [psi, hy, ↓reduceIte]

@[simp]
theorem psi_one : psi 1 = 1 := by norm_num [psi]

theorem psi_nonneg (y : ℝ) : 0 ≤ psi y := by
  rw [psi_eq]; exact mul_nonneg (exp_pos 1).le (flat_nonneg _)

theorem psi_le (y : ℝ) : psi y ≤ exp 1 := by
  rw [psi_eq]
  calc exp 1 * flat (2 * y - 1) ≤ exp 1 * 1 :=
        mul_le_mul_of_nonneg_left (flat_le_one _) (exp_pos 1).le
    _ = exp 1 := mul_one _

theorem flat_monotone : Monotone flat := by
  intro s t hst
  rcases le_or_gt s 0 with hs | hs
  · rw [flat_of_nonpos hs]; exact flat_nonneg t
  · rw [flat_of_pos hs, flat_of_pos (hs.trans_le hst), exp_le_exp, neg_le_neg_iff,
      inv_le_inv₀ (pow_pos (hs.trans_le hst) 2) (pow_pos hs 2)]
    exact pow_le_pow_left₀ hs.le hst 2

theorem psi_monotone : Monotone psi := by
  intro y y' h
  rw [psi_eq, psi_eq]
  exact mul_le_mul_of_nonneg_left (flat_monotone (by linarith)) (exp_pos 1).le

theorem one_le_psi {y : ℝ} (hy : 1 ≤ y) : 1 ≤ psi y := psi_one ▸ psi_monotone hy

/-- The polynomials of the derivatives of `flat`. -/
noncomputable def flatPoly : ℕ → ℝ[X]
  | 0 => 1
  | j + 1 => flatDerivPoly (flatPoly j)

/-- The `j`-th derivative of `Ψ`, `y ↦ e 2^j P_j(1/(2y-1)) flat(2y-1)`. -/
noncomputable def psiDeriv (j : ℕ) (y : ℝ) : ℝ :=
  exp 1 * 2 ^ j * ((flatPoly j).eval (2 * y - 1)⁻¹ * flat (2 * y - 1))

theorem hasDerivAt_psiDeriv (j : ℕ) (y : ℝ) : HasDerivAt (psiDeriv j) (psiDeriv (j + 1) y) y := by
  have h1 : HasDerivAt (fun y : ℝ => 2 * y - 1) 2 y := by
    simpa using ((hasDerivAt_id y).const_mul 2).sub_const 1
  have := ((hasDerivAt_polynomial_inv_mul_flat (flatPoly j) (2 * y - 1)).comp y h1).const_mul
    (exp 1 * 2 ^ j)
  convert this using 1
  · funext y; simp only [psiDeriv, Function.comp_apply]
  · simp only [psiDeriv, flatPoly, pow_succ]
    ring

theorem iteratedDeriv_psi (j : ℕ) : iteratedDeriv j psi = psiDeriv j := by
  induction j with
  | zero =>
    funext y
    simp [psiDeriv, flatPoly, psi_eq]
  | succ j ih =>
    funext y
    rw [iteratedDeriv_succ, ih]
    exact (hasDerivAt_psiDeriv j y).deriv

theorem contDiff_psi {n : ℕ∞} : ContDiff ℝ n psi := by
  have h : psi = fun y => exp 1 * ((1 : ℝ[X]).eval (2 * y - 1)⁻¹ * flat (2 * y - 1)) := by
    funext y; simp [psi_eq]
  rw [h]
  exact contDiff_const.mul ((contDiff_polynomial_inv_mul_flat 1).comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const))

theorem deriv_psi_nonneg (y : ℝ) : 0 ≤ deriv psi y := by
  rw [← iteratedDeriv_one, iteratedDeriv_psi]
  simp only [psiDeriv, flatPoly, flatDerivPoly, derivative_one, mul_zero, sub_zero, mul_one,
    eval_mul, eval_pow, eval_X, eval_ofNat, pow_one]
  rcases le_or_gt (2 * y - 1) 0 with h | h
  · rw [flat_of_nonpos h]; simp
  · have := flat_nonneg (2 * y - 1)
    positivity

/-- All derivatives of `Ψ` are bounded. -/
theorem exists_abs_iteratedDeriv_psi_le (j : ℕ) : ∃ C, ∀ y, |iteratedDeriv j psi y| ≤ C := by
  obtain ⟨C, hC⟩ := exists_abs_polynomial_inv_mul_flat_le (flatPoly j)
  refine ⟨exp 1 * 2 ^ j * C, fun y => ?_⟩
  rw [iteratedDeriv_psi, psiDeriv, abs_mul, abs_of_pos (by positivity)]
  exact mul_le_mul_of_nonneg_left (hC _) (by positivity)

/-! ### The function `Φ` -/

theorem integrable_gauss : Integrable fun t : ℝ => exp (-t ^ 2 / 2) := by
  have := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
  convert this using 2
  ring_nf

theorem continuous_gauss : Continuous fun t : ℝ => exp (-t ^ 2 / 2) := by fun_prop

/-- `Φ(y) = e^{1/2} ∫_{-∞}^y exp(-t²/2) dt` ([cartis2022evaluation], (4.2.6)). -/
noncomputable def phi (y : ℝ) : ℝ :=
  exp (1 / 2) * ∫ t in Iic y, exp (-t ^ 2 / 2)

theorem phi_eq (y : ℝ) : phi y = exp (1 / 2) *
    ((∫ t in Iic 0, exp (-t ^ 2 / 2)) + ∫ t in (0 : ℝ)..y, exp (-t ^ 2 / 2)) := by
  rw [phi, ← intervalIntegral.integral_Iic_sub_Iic integrable_gauss.integrableOn
    integrable_gauss.integrableOn]
  ring

theorem hasDerivAt_phi (y : ℝ) : HasDerivAt phi (exp (1 / 2) * exp (-y ^ 2 / 2)) y := by
  have h := intervalIntegral.integral_hasDerivAt_right
    (continuous_gauss.intervalIntegrable 0 y)
    (continuous_gauss.stronglyMeasurableAtFilter volume _) continuous_gauss.continuousAt
  have := (h.const_add (∫ t in Iic 0, exp (-t ^ 2 / 2))).const_mul (exp (1 / 2))
  exact this.congr_of_eventuallyEq (Eventually.of_forall fun y => phi_eq y)

theorem deriv_phi : deriv phi = fun y => exp (1 / 2) * exp (-y ^ 2 / 2) :=
  funext fun y => (hasDerivAt_phi y).deriv

theorem phi_nonneg (y : ℝ) : 0 ≤ phi y :=
  mul_nonneg (exp_pos _).le (setIntegral_nonneg measurableSet_Iic fun _ _ => (exp_pos _).le)

/-- `Φ ≤ √(2π e)`. -/
theorem phi_le (y : ℝ) : phi y ≤ exp (1 / 2) * √(2 * π) := by
  refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
  refine (setIntegral_le_integral integrable_gauss
    (Eventually.of_forall fun t => (exp_pos _).le)).trans_eq ?_
  have := integral_gaussian (1 / 2)
  convert this using 2
  · ext t; ring_nf
  · ring_nf

theorem monotone_phi : Monotone phi := by
  intro y y' h
  rw [phi_eq, phi_eq]
  refine mul_le_mul_of_nonneg_left ((add_le_add_iff_left _).2 ?_) (exp_pos _).le
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := y)
    (continuous_gauss.intervalIntegrable 0 y) (continuous_gauss.intervalIntegrable y y')]
  have : 0 ≤ ∫ t in y..y', exp (-t ^ 2 / 2) :=
    intervalIntegral.integral_nonneg h fun t _ => (exp_pos _).le
  linarith

/-- `Φ'(y) = e^{1/2} exp(-y²/2) > 1` for `|y| < 1`. -/
theorem one_lt_deriv_phi {y : ℝ} (hy : |y| < 1) : 1 < deriv phi y := by
  rw [deriv_phi]
  dsimp only
  rw [← exp_add]
  refine Real.one_lt_exp_iff.2 ?_
  have : y ^ 2 < 1 := by
    have := sq_lt_sq' (abs_lt.1 hy).1 (abs_lt.1 hy).2
    simpa using this
  linarith

theorem deriv_phi_pos (y : ℝ) : 0 < deriv phi y := by
  rw [deriv_phi]; positivity

/-- The polynomials of the derivatives of `y ↦ exp(-y²/2)`. -/
noncomputable def gaussPoly : ℕ → ℝ[X]
  | 0 => 1
  | j + 1 => derivative (gaussPoly j) - X * gaussPoly j

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

/-- The derivatives of `Φ`. -/
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

theorem contDiff_phi {n : ℕ∞} : ContDiff ℝ n phi := by
  refine (contDiff_infty_iff_deriv.2 ⟨fun y => (hasDerivAt_phi y).differentiableAt, ?_⟩).of_le
    (by exact_mod_cast le_top)
  rw [deriv_phi]
  fun_prop

/-- `P(y) exp(-y²/2)` is bounded on `ℝ`. -/
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

/-- All derivatives of `Φ` are bounded. -/
theorem exists_abs_iteratedDeriv_phi_le (j : ℕ) : ∃ C, ∀ y, |iteratedDeriv j phi y| ≤ C := by
  rcases j with _ | j
  · refine ⟨exp (1 / 2) * √(2 * π), fun y => ?_⟩
    rw [iteratedDeriv_zero, abs_of_nonneg (phi_nonneg y)]
    exact phi_le y
  · obtain ⟨C, hC⟩ := exists_abs_polynomial_mul_gauss_le (gaussPoly j)
    refine ⟨exp (1 / 2) * C, fun y => ?_⟩
    rw [iteratedDeriv_succ_phi, abs_mul, abs_of_pos (exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hC y) (exp_pos _).le

/-! ### Uniform bounds on the derivatives of `Ψ` and `Φ` -/

/-- `sup_y |Ψ^{(j)}(y)|`. -/
noncomputable def psiBound (j : ℕ) : ℝ := ⨆ y, |iteratedDeriv j psi y|

/-- `sup_y |Φ^{(j)}(y)|`. -/
noncomputable def phiBound (j : ℕ) : ℝ := ⨆ y, |iteratedDeriv j phi y|

theorem abs_iteratedDeriv_psi_le (j : ℕ) (y : ℝ) : |iteratedDeriv j psi y| ≤ psiBound j := by
  obtain ⟨C, hC⟩ := exists_abs_iteratedDeriv_psi_le j
  exact le_ciSup (f := fun y => |iteratedDeriv j psi y|) ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩ y

theorem abs_iteratedDeriv_phi_le (j : ℕ) (y : ℝ) : |iteratedDeriv j phi y| ≤ phiBound j := by
  obtain ⟨C, hC⟩ := exists_abs_iteratedDeriv_phi_le j
  exact le_ciSup (f := fun y => |iteratedDeriv j phi y|) ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩ y

theorem psiBound_nonneg (j : ℕ) : 0 ≤ psiBound j :=
  (abs_nonneg _).trans (abs_iteratedDeriv_psi_le j 0)

theorem phiBound_nonneg (j : ℕ) : 0 ≤ phiBound j :=
  (abs_nonneg _).trans (abs_iteratedDeriv_phi_le j 0)

/-- A derivative of `g ∘ L`, `g : ℝ → ℝ`, `‖L‖ ≤ 1`, is bounded by the derivative of `g`. -/
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

theorem norm_fst_clm_le : ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by simpa using norm_fst_le z

theorem norm_snd_clm_le : ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by simpa using norm_snd_le z

/-- One link of the chain: `pair (a, b) = Ψ(-a) Φ(-b) - Ψ(a) Φ(b)`. -/
noncomputable def pair (z : ℝ × ℝ) : ℝ := psi (-z.1) * phi (-z.2) - psi z.1 * phi z.2

/-- The bound `2 ∑_i C(q, i) sup|Ψ^{(i)}| sup|Φ^{(q-i)}|` on the `q`-th derivative of `pair`. -/
noncomputable def pairBound (q : ℕ) : ℝ :=
  2 * ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * psiBound i * phiBound (q - i)

theorem contDiff_pair {n : ℕ∞} : ContDiff ℝ n pair := by
  unfold pair
  have h1 : ContDiff ℝ n psi := contDiff_psi
  have h2 : ContDiff ℝ n phi := contDiff_phi
  fun_prop

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

/-- Coordinate `i` of `x ∈ ℝ^T` as a continuous linear form (`0` for `i ≥ T`). -/
noncomputable def coord (T i : ℕ) : EuclideanSpace ℝ (Fin T) →L[ℝ] ℝ :=
  if h : i < T then EuclideanSpace.proj (⟨i, h⟩ : Fin T) else 0

theorem coord_apply_of_lt {i : ℕ} (h : i < T) (x : EuclideanSpace ℝ (Fin T)) :
    coord T i x = x ⟨i, h⟩ := by
  simp [coord, h]

@[simp]
theorem coord_apply_fin (j : Fin T) (x : EuclideanSpace ℝ (Fin T)) : coord T j x = x j :=
  coord_apply_of_lt j.2 x

theorem coord_apply_of_le {i : ℕ} (h : T ≤ i) (x : EuclideanSpace ℝ (Fin T)) :
    coord T i x = 0 := by
  simp [coord, not_lt.2 h]

theorem abs_coord_le (i : ℕ) (x : EuclideanSpace ℝ (Fin T)) : |coord T i x| ≤ ‖x‖ := by
  rcases lt_or_ge i T with h | h
  · rw [coord_apply_of_lt h, ← Real.norm_eq_abs]; exact PiLp.norm_apply_le x _
  · rw [coord_apply_of_le h, abs_zero]; exact norm_nonneg x

theorem norm_coord_le (i : ℕ) : ‖coord T i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul, Real.norm_eq_abs]; exact abs_coord_le i x

/-- `∑_{i < T} x_i² = ‖x‖²`. -/
theorem sum_range_coord_sq (x : EuclideanSpace ℝ (Fin T)) :
    ∑ i ∈ Finset.range T, coord T i x ^ 2 = ‖x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, ← Fin.sum_univ_eq_sum_range (fun i => coord T i x ^ 2)]
  simp [Real.norm_eq_abs, sq_abs]

/-- The pair of consecutive coordinates `(x_{l-1}, x_l)`. -/
noncomputable def pairMap (T l : ℕ) : EuclideanSpace ℝ (Fin T) →L[ℝ] ℝ × ℝ :=
  (coord T (l - 1)).prod (coord T l)

@[simp]
theorem pairMap_apply (l : ℕ) (x : EuclideanSpace ℝ (Fin T)) :
    pairMap T l x = (coord T (l - 1) x, coord T l x) := rfl

theorem norm_pairMap_apply_le (l : ℕ) (x : EuclideanSpace ℝ (Fin T)) : ‖pairMap T l x‖ ≤ ‖x‖ := by
  rw [pairMap_apply, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (abs_coord_le _ x) (abs_coord_le _ x)

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

/-- The dimension-free estimate behind Lemma 4.2.5 (iv): for `q ≥ 2` vectors,
`∑_l ∏_m ‖(v_m)_{l-1}, (v_m)_l‖ ≤ 2 ∏_m ‖v_m‖` (Cauchy–Schwarz on the first two factors). -/
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

/-- The hard zero chain of [cartis2022evaluation], (4.2.6) (with first term
`-Ψ(1) Φ(x_0)`, as in Carmon et al.), on `ℝ^T` with `coord T i x = x_i`:
`chain T x = -Ψ(1) Φ(x_0) + ∑_{l=1}^{T-1} [Ψ(-x_{l-1}) Φ(-x_l) - Ψ(x_{l-1}) Φ(x_l)]`.
(For `T = 0` it is the constant `-Φ(0)`.) -/
noncomputable def chain (T : ℕ) (x : EuclideanSpace ℝ (Fin T)) : ℝ :=
  -(psi 1 * phi (coord T 0 x)) + ∑ l ∈ Finset.Ico 1 T, pair (pairMap T l x)

theorem chain_eq (x : EuclideanSpace ℝ (Fin T)) :
    chain T x = -phi (coord T 0 x) + ∑ l ∈ Finset.Ico 1 T, pair (pairMap T l x) := by
  rw [chain, psi_one, one_mul]

theorem chain_eq_add :
    chain T = -(phi ∘ coord T 0) + fun x => ∑ l ∈ Finset.Ico 1 T, (pair ∘ pairMap T l) x :=
  funext fun x => by rw [chain_eq]; rfl

theorem contDiff_chain {n : ℕ∞} : ContDiff ℝ n (chain T) := by
  rw [chain_eq_add]
  exact (contDiff_phi.comp (coord T 0).contDiff).neg.add
    (ContDiff.sum fun l _ => contDiff_pair.comp (pairMap T l).contDiff)

/-- The explicit dimension-free bound on `‖∇^{p+1} chain T‖`. -/
noncomputable def lipschitzConst (p : ℕ) : ℝ := 1 + phiBound (p + 1) + 2 * pairBound (p + 1)

theorem lipschitzConst_pos (p : ℕ) : 0 < lipschitzConst p := by
  have := phiBound_nonneg (p + 1)
  have : 0 ≤ pairBound (p + 1) := (norm_nonneg _).trans (norm_iteratedFDeriv_pair_le _ 0)
  unfold lipschitzConst; positivity

/-- **Lemma 4.2.5 (iv) of [cartis2022evaluation]**, uniform part: `‖∇^{p+1} chain T(x)‖` is
bounded by `lipschitzConst p`, independently of the dimension `T` (`p ≥ 1`). -/
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

/-- **Lemma 4.2.5 (iv) of [cartis2022evaluation]**: `∇^p chain T` is Lipschitz continuous with the
dimension-free constant `lipschitzConst p` (`p ≥ 1`). -/
theorem lipschitzOn_iteratedFDeriv_chain {p : ℕ} (hp : 1 ≤ p) :
    IteratedFDerivLipschitzOn (chain T) p (lipschitzConst p) univ :=
  iteratedFDerivLipschitzOn_of_norm_le convex_univ
    (fun _ _ => contDiff_chain.contDiffAt) fun x _ => norm_iteratedFDeriv_chain_le hp x

/-! ### Lemma 4.2.5 (i): the zero-chain property -/

theorem pair_eq_zero {z : ℝ × ℝ} (hz : |z.1| ≤ 1 / 2) : pair z = 0 := by
  have h1 : psi z.1 = 0 := psi_of_le (le_trans (le_abs_self _) hz)
  have h2 : psi (-z.1) = 0 := psi_of_le (le_trans (neg_le_abs _) hz)
  simp [pair, h1, h2]

theorem coord_single (k : ℕ) (i : Fin T) :
    coord T k (EuclideanSpace.single i (1 : ℝ)) = if k = i then 1 else 0 := by
  rcases lt_or_ge k T with hk | hk
  · rw [coord_apply_of_lt hk, PiLp.single_apply]
    simp only [Fin.ext_iff]
  · rw [coord_apply_of_le hk, ite_eq_right (by have := i.2; omega)]

/-- The map zeroing coordinate `i`. -/
noncomputable def zeroCoord (i : Fin T) : EuclideanSpace ℝ (Fin T) →L[ℝ] EuclideanSpace ℝ (Fin T) :=
  ContinuousLinearMap.id ℝ _ - (coord T i).smulRight (EuclideanSpace.single i (1 : ℝ))

theorem coord_zeroCoord (i : Fin T) (k : ℕ) (y : EuclideanSpace ℝ (Fin T)) :
    coord T k (zeroCoord i y) = if k = i then 0 else coord T k y := by
  simp only [zeroCoord, sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, map_sub, map_smul, coord_single, smul_eq_mul]
  split_ifs with h
  · subst h; simp
  · simp

/-- Near a point whose coordinates `i - 1` and `i` are small, `chain T` does not depend on the
coordinate `i ≥ 1`. -/
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

/-- **Lemma 4.2.5 (i) of [cartis2022evaluation]**: `chain T` is a `p`-th order zero chain for
every `p`. -/
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

/-- The directional derivative of a link `pair` along `(u, w)`. -/
noncomputable def dpair (a b u w : ℝ) : ℝ :=
  -(u * deriv psi (-a) * phi (-b)) - w * psi (-a) * deriv phi (-b) -
    u * deriv psi a * phi b - w * psi a * deriv phi b

theorem hasDerivAt_psi (y : ℝ) : HasDerivAt psi (deriv psi y) y :=
  ((contDiff_psi (n := 1)).differentiable one_ne_zero y).hasDerivAt

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

/-- The directional derivative of `chain T` along `v`. -/
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

/-- **Lemma 4.2.5 (ii) of [cartis2022evaluation]** (Carmon–Duchi–Hinder–Sidford, Lemma 2): if
`|x_i| < 1` for some
coordinate `i`, then there is `j ≤ i` with `|x_j| < 1` and `|∂_j chain T(x)| > 1`; in particular
`‖∇ chain T(x)‖ > 1`. -/
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

theorem phi_bound_le : exp (1 / 2) * √(2 * π) ≤ 12 := by
  refine le_trans ?_ exp_one_mul_phi_bound_le
  exact le_mul_of_one_le_left (by positivity) (Real.one_le_exp zero_le_one)

theorem pair_ge (z : ℝ × ℝ) : -12 ≤ pair z := by
  have h1 : 0 ≤ psi (-z.1) * phi (-z.2) := mul_nonneg (psi_nonneg _) (phi_nonneg _)
  have h2 : psi z.1 * phi z.2 ≤ exp 1 * (exp (1 / 2) * √(2 * π)) :=
    mul_le_mul (psi_le _) (phi_le _) (phi_nonneg _) (exp_pos 1).le
  have := exp_one_mul_phi_bound_le
  unfold pair; linarith

theorem chain_zero : chain T 0 = -phi 0 := by
  rw [chain_eq, map_zero, Finset.sum_eq_zero fun l _ => pair_eq_zero (by simp), add_zero]

/-- `chain T 0 - 12 T ≤ chain T x` for all `x`. -/
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

/-- **Lemma 4.2.5 (iii) of [cartis2022evaluation]** (Carmon–Duchi–Hinder–Sidford, Lemma 3 (i)):
`chain T` is bounded
below and `chain T 0 - inf chain T ≤ 12 T`. -/
theorem chain_zero_sub_iInf_le :
    BddBelow (range (chain T)) ∧ chain T 0 - ⨅ x, chain T x ≤ 12 * T := by
  refine ⟨⟨chain T 0 - 12 * T, by rintro _ ⟨x, rfl⟩; exact chain_zero_sub_le x⟩, ?_⟩
  have : chain T 0 - 12 * T ≤ ⨅ x, chain T x := le_ciInf chain_zero_sub_le
  linarith

/-! ### Theorem 4.2.6: the lower bound -/

section LowerBound

variable {p : ℕ} {c μ : ℝ}

/-- The scaled chain `x ↦ c chain T(μ⁻¹ x)`. -/
noncomputable def scaledChain (T : ℕ) (c μ : ℝ) (x : EuclideanSpace ℝ (Fin T)) : ℝ :=
  c * chain T (μ⁻¹ • x)

theorem contDiff_scaledChain {n : ℕ∞} : ContDiff ℝ n (scaledChain T c μ) :=
  contDiff_const.mul (contDiff_chain.comp (contDiff_const_smul _))

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

/-- **Theorem 4.2.6 of [cartis2022evaluation]** (lower bound, backbone form). For `p ≥ 1`,
`Δ, L, ε > 0` and `k̄ = ⌊Δ / 12 (L / L^D_p)^{1/p} ε^{-(p+1)/p}⌋` with `L^D_p = lipschitzConst p`,
`#_ε(𝓜_ZR(p), 𝓕(Δ, p)) ≥ k̄` and `#_ε(𝓜(p), 𝓕(Δ, p)) ≥ k̄`. The hard function is
`x ↦ μ^{p+1} (L / L^D_p) chain k̄ (x / μ)` with `μ = (L^D_p ε / L)^{1/p}` ((4.2.8)); for `𝓜(p)` its
rotated copies on `ℝ^{2 k̄}` are used. The second bound holds for every class of methods `𝓜`
(in particular `𝓜(p)`, see `le_classComplexity_smoothClass_methodClass`). Both classes are
nonempty (`zeroRespectingClass_nonempty`, `methodClass_nonempty`), so the bounds are not
vacuous. -/
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

/-- **Theorem 4.2.6 of [cartis2022evaluation]** for the book's classes:
`#_ε(𝓜_ZR(p), 𝓕(Δ, p)) ≥ k̄` and `#_ε(𝓜(p), 𝓕(Δ, p)) ≥ k̄`
(`le_classComplexity_smoothClass` with `𝓜 = 𝓜(p)`). -/
theorem le_classComplexity_smoothClass_methodClass (hp : 1 ≤ p) {Δ L ε : ℝ} (hΔ : 0 < Δ)
    (hL : 0 < L) (hε : 0 < ε) :
    ((⌊Δ / 12 * (L / lipschitzConst p) ^ (1 / p : ℝ) * ε ^ (-((p + 1 : ℝ) / p))⌋₊ : ℕ) : ℕ∞) ≤
        classComplexity (zeroRespectingClass p) (smoothClass Δ L p) ε ∧
      ((⌊Δ / 12 * (L / lipschitzConst p) ^ (1 / p : ℝ) * ε ^ (-((p + 1 : ℝ) / p))⌋₊ : ℕ) : ℕ∞) ≤
        classComplexity (methodClass p) (smoothClass Δ L p) ε :=
  le_classComplexity_smoothClass hp hΔ hL hε (methodClass p)

end LowerBound

/-! ### Explicit growth of `lipschitzConst p` -/

/-- The sum `∑ₘ |aₘ|` of the absolute values of the coefficients of a real polynomial. -/
noncomputable def coeffAbsSum (P : ℝ[X]) : ℝ :=
  ∑ m ∈ Finset.range (P.natDegree + 1), |P.coeff m|

/-- `coeffAbsSum P` may be computed over any range containing the support. -/
theorem coeffAbsSum_eq_sum_range {P : ℝ[X]} {N : ℕ} (h : P.natDegree < N) :
    coeffAbsSum P = ∑ m ∈ Finset.range N, |P.coeff m| := by
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun m _ hm => ?_
  rw [Finset.mem_range, not_lt] at hm
  rw [coeff_eq_zero_of_natDegree_lt (by omega), abs_zero]

theorem coeffAbsSum_nonneg (P : ℝ[X]) : 0 ≤ coeffAbsSum P :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem coeffAbsSum_add_le (P Q : ℝ[X]) :
    coeffAbsSum (P + Q) ≤ coeffAbsSum P + coeffAbsSum Q := by
  have hP : P.natDegree < max P.natDegree Q.natDegree + 1 := by omega
  have hQ : Q.natDegree < max P.natDegree Q.natDegree + 1 := by omega
  have hPQ : (P + Q).natDegree < max P.natDegree Q.natDegree + 1 :=
    (natDegree_add_le P Q).trans_lt (by omega)
  rw [coeffAbsSum_eq_sum_range hP, coeffAbsSum_eq_sum_range hQ, coeffAbsSum_eq_sum_range hPQ,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun m _ => by rw [coeff_add]; exact abs_add_le _ _

theorem coeffAbsSum_neg (P : ℝ[X]) : coeffAbsSum (-P) = coeffAbsSum P := by
  simp [coeffAbsSum, natDegree_neg]

theorem coeffAbsSum_sub_le (P Q : ℝ[X]) :
    coeffAbsSum (P - Q) ≤ coeffAbsSum P + coeffAbsSum Q := by
  rw [sub_eq_add_neg, ← coeffAbsSum_neg Q]
  exact coeffAbsSum_add_le _ _

/-- Multiplying by `X^k` shifts the coefficients. -/
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

/-- `∑ |coeff P'| ≤ deg P · ∑ |coeff P|`. -/
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

/-- `|P(y)| ≤ (∑ₘ |aₘ|) (1 + |y|^d)` when `deg P ≤ d`. -/
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

theorem flatDerivPoly_eq (P : ℝ[X]) :
    flatDerivPoly P = X ^ 3 * P + X ^ 3 * P - X ^ 2 * derivative P := by
  rw [flatDerivPoly]; ring

/-- `deg P_j ≤ 3j` for the polynomials of the derivatives of `flat`. -/
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

/-- `∑ |coeff P_j| ≤ 3^j j!`, from `P_{j+1} = 2X³P_j - X²P_j'`. -/
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

/-- `deg H_k ≤ k` for the polynomials of the derivatives of the Gaussian. -/
theorem natDegree_gaussPoly_le (k : ℕ) : (gaussPoly k).natDegree ≤ k := by
  induction k with
  | zero => simp [gaussPoly]
  | succ k ih =>
    rw [gaussPoly]
    have hd := natDegree_derivative_le (gaussPoly k)
    have h1 : (X * gaussPoly k).natDegree ≤ k + 1 :=
      natDegree_mul_le.trans (by have := natDegree_X_le (R := ℝ); omega)
    exact (natDegree_sub_le _ _).trans (max_le (by omega) h1)

/-- `∑ |coeff H_k| ≤ k!`, from `H_{k+1} = H_k' - X H_k`. -/
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

/-- `x^k e^{-x} ≤ k!` for `x ≥ 0`. -/
theorem pow_mul_exp_neg_le_factorial {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    x ^ k * exp (-x) ≤ k.factorial := by
  have := Real.pow_div_factorial_le_exp x hx k
  rw [div_le_iff₀ (by positivity)] at this
  rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _)]
  linarith [mul_comm (exp x) (k.factorial : ℝ)]

/-- `t^{3j} e^{-t²} ≤ √((3j)!)`. -/
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

/-- `|y|^k e^{-y²/2} ≤ √(k!)`. -/
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

/-- `a! (1 + √(b!)) ≤ 2 √((a!)² b!)`. -/
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

/-- The growth scale `√(q^{5q})`. -/
noncomputable def growthScale (q : ℕ) : ℝ := √((q : ℝ) ^ (5 * q))

theorem one_le_growthScale (q : ℕ) : 1 ≤ growthScale q := by
  refine Real.one_le_sqrt.2 ?_
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · exact one_le_pow₀ (by exact_mod_cast hq)

theorem growthScale_mul_le {i q : ℕ} (hi : i ≤ q) :
    growthScale i * growthScale (q - i) ≤ growthScale q := by
  rw [growthScale, growthScale, growthScale, ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  calc (i : ℝ) ^ (5 * i) * ((q - i : ℕ) : ℝ) ^ (5 * (q - i))
      ≤ (q : ℝ) ^ (5 * i) * (q : ℝ) ^ (5 * (q - i)) := by
        gcongr
        exact_mod_cast Nat.sub_le q i
    _ = (q : ℝ) ^ (5 * q) := by rw [← pow_add]; congr 1; omega

theorem growthScale_sq (q : ℕ) : growthScale q ^ 2 = (q : ℝ) ^ (5 * q) :=
  Real.sq_sqrt (by positivity)

/-- `|Ψ^{(j)}(y)| ≤ e 6^j j! (1 + √((3j)!))`. -/
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

/-- `sup |Ψ^{(j)}| ≤ 6 · 36^j √(j^{5j})`. -/
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

/-- `sup |Φ^{(k)}| ≤ 12 √(k^{5k})` (a crude bound, enough for the growth estimate). -/
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

/-- `pairBound q ≤ 144 · 72^q √(q^{5q})`. -/
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

/-- `lipschitzConst p ≤ 301 · 72^{p+1} √((p+1)^{5(p+1)})`. -/
theorem lipschitzConst_le_growthScale (p : ℕ) :
    lipschitzConst p ≤ 301 * 72 ^ (p + 1) * growthScale (p + 1) := by
  have h1 := phiBound_le (p + 1)
  have h2 := pairBound_le (p + 1)
  have hW := one_le_growthScale (p + 1)
  have h72 : (1 : ℝ) ≤ 72 ^ (p + 1) := one_le_pow₀ (by norm_num)
  rw [lipschitzConst]
  nlinarith

/-- The arithmetic step `301² 72^{2(p+1)} (p+1)^{5(p+1)} ≤ (301² 72⁴ 32³)^p p^{5p}`. -/
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

/-- `(lipschitzConst p)² ≤ Q^p p^{5p}` with `Q = 301² 72⁴ 32³ ≤ e^{40}`. -/
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

/-- **Lemma 4.2.5 (iv) of [cartis2022evaluation]**, explicit growth with `c₁ = 20`
([Carmon–Duchi–Hinder–Sidford, Lemma 3]): `lipschitzConst p ≤ exp (5/2 p log p + 20 p)`. -/
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

/-- **Lemma 4.2.5 (iv) of [cartis2022evaluation]**, explicit growth ([77, Lemma 3 (iii)]): there
is an absolute constant `c₁ > 0` with `lipschitzConst p ≤ exp (5/2 p log p + c₁ p)` for `p ≥ 1`. -/
theorem lipschitzConst_le_exp :
    ∃ c₁ > 0, ∀ p : ℕ, 1 ≤ p → lipschitzConst p ≤ exp (5 / 2 * p * log p + c₁ * p) :=
  ⟨20, by norm_num, fun _ hp => lipschitzConst_le_exp_twenty hp⟩

end CarmonChain

end Optimization
