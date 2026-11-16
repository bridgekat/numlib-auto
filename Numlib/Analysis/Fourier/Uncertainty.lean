/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Heisenberg uncertainty principle

For a Schwartz function $g \colon \mathbb{R} \to \mathbb{C}$, the time spread
$\int t^2 |g(t)|^2 \, dt$ and the frequency spread $\int \nu^2 |\hat{g}(\nu)|^2 \, d\nu$ cannot both
be small:
$$\Bigl(\int |g(t)|^2 \, dt\Bigr)^2 \le 16 \pi^2 \Bigl(\int t^2 |g(t)|^2 \, dt\Bigr) \Bigl(\int
  \nu^2 |\hat{g}(\nu)|^2 \, d\nu\Bigr).$$
Here $\hat{g}(\nu) = \int g(t) e^{-2 \pi i \nu t} \, dt$. Equivalently, with the angular frequency
$\omega = 2 \pi \nu$ and $G(\omega) = \hat{g}(\omega / 2\pi)$, the resolutions
$$\Delta t = \Bigl(\frac{\int t^2 |g(t)|^2 \, dt}{\int |g(t)|^2 \, dt}\Bigr)^{1/2}, \qquad \Delta
  \omega = \Bigl(\frac{\int \omega^2 |G(\omega)|^2 \, d\omega}{\int |G(\omega)|^2 \,
  d\omega}\Bigr)^{1/2}$$
satisfy $\Delta t \, \Delta \omega \ge 1/2$. This is (10.88) of [quarteroni2000numerical].

## Main results

* `SchwartzMap.integral_norm_sq_add_two_mul_re`: the integration by parts identity $\int
  \bigl(|g|^2 + 2t \operatorname{Re}(g' \bar{g})\bigr) = 0$.
* `SchwartzMap.heisenberg_uncertainty_deriv`: $(\int |g|^2)^2 \le 4 (\int t^2 |g|^2) (\int |g'|^2)$.
* `SchwartzMap.integral_norm_sq_deriv`: $\int |g'|^2 = 4 \pi^2 \int \nu^2 |\hat{g}|^2$.
* `SchwartzMap.heisenberg_uncertainty`: $(\int |g|^2)^2 \le 16 \pi^2 (\int t^2 |g|^2) (\int \nu^2
  |\hat{g}|^2)$.

## Proof outline

The proof is the classical one. Integration by parts on the whole line, applied to
$t \mapsto t \, g(t) \overline{g(t)}$, which tends to $0$ at both ends because $g$ is a Schwartz
function, gives
$$\int |g|^2 = -2 \int t \operatorname{Re}\bigl(g'(t) \overline{g(t)}\bigr) \, dt.$$
The Cauchy–Schwarz inequality (Hölder's inequality with $p = q = 2$) bounds the right side by
$2 (\int t^2 |g|^2)^{1/2} (\int |g'|^2)^{1/2}$. Plancherel's theorem together with
$\widehat{g'}(\nu) = 2 \pi i \nu \, \hat{g}(\nu)$ turns $\int |g'|^2$ into
$4 \pi^2 \int \nu^2 |\hat{g}|^2$.

## Implementation notes

* Mathlib does not state the uncertainty principle, but it has every ingredient, in particular
  `SchwartzMap.integral_norm_sq_fourier` (Plancherel's theorem for Schwartz functions) and
  `Real.fourier_deriv`.
* A Schwartz function is `g : 𝓢(ℝ, ℂ)`, its derivative $g'$ is `deriv g`, and its Fourier transform
  $\hat{g}$ is `𝓕 g`.
-/

open MeasureTheory Real Complex Filter Topology Set

open scoped FourierTransform ComplexConjugate

namespace SchwartzMap

/-- Let $g, h \colon \mathbb{R} \to \mathbb{C}$ be Schwartz functions and let $k \in \mathbb{N}$.
Then the function $t \mapsto |t|^k |g(t)| |h(t)|$ is integrable on $\mathbb{R}$.

The factor $|h(t)|$ is bounded, and $|t|^k |g(t)|$ is integrable by
`SchwartzMap.integrable_pow_mul`. -/
theorem integrable_pow_norm_mul_norm (g h : 𝓢(ℝ, ℂ)) (k : ℕ) :
    Integrable (fun t : ℝ => ‖t‖ ^ k * (‖g t‖ * ‖h t‖)) := by
  obtain ⟨C, hC0, hC⟩ := h.decay 0 0
  simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul] at hC
  refine Integrable.mono' ((g.integrable_pow_mul volume k).const_mul C)
    ((continuous_norm.pow k).mul (g.continuous.norm.mul h.continuous.norm)).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_of_nonneg (by positivity)]
  calc ‖t‖ ^ k * (‖g t‖ * ‖h t‖) ≤ ‖t‖ ^ k * (‖g t‖ * C) := by
        gcongr
        exact hC t
    _ = C * (‖t‖ ^ k * ‖g t‖) := by ring

/-- For a Schwartz function $g \colon \mathbb{R} \to \mathbb{C}$, the function $t \mapsto |g(t)|^2$
is integrable on $\mathbb{R}$. -/
theorem integrable_norm_sq (g : 𝓢(ℝ, ℂ)) : Integrable (fun t : ℝ => ‖g t‖ ^ 2) := by
  refine (integrable_pow_norm_mul_norm g g 0).congr (Filter.Eventually.of_forall fun t => ?_)
  simp [sq]

/-- For a Schwartz function $g \colon \mathbb{R} \to \mathbb{C}$, the function
$t \mapsto t^2 |g(t)|^2$ is integrable on $\mathbb{R}$: the time spread of $g$ is finite. -/
theorem integrable_sq_mul_norm_sq (g : 𝓢(ℝ, ℂ)) :
    Integrable (fun t : ℝ => t ^ 2 * ‖g t‖ ^ 2) := by
  refine (integrable_pow_norm_mul_norm g g 2).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  ring

/-! ### Integration by parts -/

/-- For a Schwartz function $g \colon \mathbb{R} \to \mathbb{C}$,
$$t \, g(t) \overline{g(t)} \to 0 \quad \text{as } |t| \to \infty.$$

The function $|t| |g(t)|$ is bounded, and $g(t) \to 0$. This is the boundary term of the
integration by parts below. -/
theorem tendsto_mul_mul_conj (g : 𝓢(ℝ, ℂ)) :
    Tendsto (fun t : ℝ => (t : ℂ) * (g t * conj (g t))) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := g.decay 1 0
  simp only [norm_iteratedFDeriv_zero, pow_one] at hC
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_)
    (by simpa using g.tendsto_cocompact.norm.const_mul C)
  calc ‖(t : ℂ) * (g t * conj (g t))‖ = (‖t‖ * ‖g t‖) * ‖g t‖ := by
        simp only [norm_mul, RCLike.norm_conj, Complex.norm_real]
        ring
    _ ≤ C * ‖g t‖ := by
        gcongr
        exact hC t

/-- For a Schwartz function $g \colon \mathbb{R} \to \mathbb{C}$ and $t \in \mathbb{R}$, the
function $s \mapsto s \, g(s) \overline{g(s)}$ has at $t$ the derivative
$$|g(t)|^2 + 2t \operatorname{Re}\bigl(g'(t) \overline{g(t)}\bigr),$$
which is a real number.

The proof uses the product rule, $z \bar{z} = |z|^2$ and $w + \bar{w} = 2 \operatorname{Re} w$. -/
theorem hasDerivAt_mul_mul_conj (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (s : ℂ) * (g s * conj (g s)))
      (((‖g t‖ ^ 2 + 2 * t * (deriv (g : ℝ → ℂ) t * conj (g t)).re : ℝ) : ℂ)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    have h := Complex.ofRealCLM.hasDerivAt (x := t)
    simp only [Complex.ofRealCLM_apply] at h
    exact h
  have hg : HasDerivAt (g : ℝ → ℂ) (deriv (g : ℝ → ℂ) t) t := (g.differentiableAt).hasDerivAt
  have hc : HasDerivAt (fun s : ℝ => conj (g s)) (conj (deriv (g : ℝ → ℂ) t)) t := hg.star
  have h3 : HasDerivAt (fun s : ℝ => (s : ℂ) * (g s * conj (g s)))
      (1 * (g t * conj (g t)) + (t : ℂ) * (deriv (g : ℝ → ℂ) t * conj (g t)
        + g t * conj (deriv (g : ℝ → ℂ) t))) t :=
    h1.fun_mul (hg.fun_mul hc)
  refine h3.congr_deriv ?_
  have e1 : g t * conj (g t) = ((‖g t‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.mul_conj]
    norm_cast
  have e2 : deriv (g : ℝ → ℂ) t * conj (g t) + g t * conj (deriv (g : ℝ → ℂ) t)
      = ((2 * (deriv (g : ℝ → ℂ) t * conj (g t)).re : ℝ) : ℂ) := by
    have e3 : g t * conj (deriv (g : ℝ → ℂ) t)
        = conj (deriv (g : ℝ → ℂ) t * conj (g t)) := by
      rw [map_mul, Complex.conj_conj, mul_comm]
    rw [e3, Complex.add_conj]
  rw [e1, e2]
  push_cast
  ring

/-- For a Schwartz function $g \colon \mathbb{R} \to \mathbb{C}$, the function $t \mapsto 2t
\operatorname{Re}(g'(t) \overline{g(t)})$ is integrable on $\mathbb{R}$.

The derivative $g'$ is bounded, and $t \mapsto |t| |g(t)|$ is integrable. -/
theorem integrable_two_mul_re (g : 𝓢(ℝ, ℂ)) :
    Integrable (fun t : ℝ => 2 * t * (deriv (g : ℝ → ℂ) t * conj (g t)).re) := by
  obtain ⟨C, hC0, hC⟩ := (derivCLM ℝ (F := ℂ) g).decay 0 0
  simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul, derivCLM_apply] at hC
  refine Integrable.mono' ((g.integrable_pow_mul volume 1).const_mul (2 * C)) (by fun_prop) ?_
  filter_upwards with t
  have hre : |(deriv (g : ℝ → ℂ) t * conj (g t)).re| ≤ ‖deriv (g : ℝ → ℂ) t‖ * ‖g t‖ := by
    calc |(deriv (g : ℝ → ℂ) t * conj (g t)).re|
        ≤ ‖deriv (g : ℝ → ℂ) t * conj (g t)‖ := Complex.abs_re_le_norm _
      _ = ‖deriv (g : ℝ → ℂ) t‖ * ‖g t‖ := by rw [norm_mul, RCLike.norm_conj]
  calc ‖2 * t * (deriv (g : ℝ → ℂ) t * conj (g t)).re‖
      = 2 * ‖t‖ * |(deriv (g : ℝ → ℂ) t * conj (g t)).re| := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        norm_num
    _ ≤ 2 * ‖t‖ * (‖deriv (g : ℝ → ℂ) t‖ * ‖g t‖) := by gcongr
    _ ≤ 2 * ‖t‖ * (C * ‖g t‖) := by gcongr; exact hC t
    _ = 2 * C * (‖t‖ ^ 1 * ‖g t‖) := by rw [pow_one]; ring

/-- **Integration by parts on the whole line**: for a Schwartz function
$g \colon \mathbb{R} \to \mathbb{C}$,
$$\int_{\mathbb{R}} \Bigl(|g(t)|^2 + 2t \operatorname{Re}\bigl(g'(t) \overline{g(t)}\bigr)\Bigr)
  \, dt = 0.$$

The integrand is the derivative of $t \mapsto t \, g(t) \overline{g(t)}$. It is integrable, and
this function tends to $0$ at both ends of the line. -/
theorem integral_norm_sq_add_two_mul_re (g : 𝓢(ℝ, ℂ)) :
    ∫ t : ℝ, (‖g t‖ ^ 2 + 2 * t * (deriv (g : ℝ → ℂ) t * conj (g t)).re) = 0 := by
  set F : ℝ → ℂ := fun s : ℝ => (s : ℂ) * (g s * conj (g s)) with hF
  set u : ℝ → ℝ := fun t => ‖g t‖ ^ 2 + 2 * t * (deriv (g : ℝ → ℂ) t * conj (g t)).re with hu
  have hderiv : ∀ t, HasDerivAt F ((u t : ℂ)) t := hasDerivAt_mul_mul_conj g
  have hbound : Integrable u := (integrable_norm_sq g).add (integrable_two_mul_re g)
  have hFint : Integrable fun t : ℝ => ((u t : ℂ)) := hbound.ofReal
  have htop : Tendsto F atTop (𝓝 0) :=
    (tendsto_mul_mul_conj g).mono_left (by rw [cocompact_eq_atBot_atTop]; exact le_sup_right)
  have hbot : Tendsto F atBot (𝓝 0) :=
    (tendsto_mul_mul_conj g).mono_left (by rw [cocompact_eq_atBot_atTop]; exact le_sup_left)
  have h1 : ∫ t in Ioi (0 : ℝ), ((u t : ℂ)) = 0 - F 0 :=
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hderiv x) hFint.integrableOn htop
  have h2 : ∫ t in Iic (0 : ℝ), ((u t : ℂ)) = F 0 - 0 :=
    integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hderiv x) hFint.integrableOn hbot
  have h3 : ∫ t : ℝ, ((u t : ℂ)) = 0 := by
    rw [← intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ)) hFint.integrableOn
      hFint.integrableOn, h1, h2]
    ring
  rw [integral_complex_ofReal] at h3
  exact_mod_cast h3

/-- For a Schwartz function $g \colon \mathbb{R} \to \mathbb{C}$, the Schwartz function
`SchwartzMap.derivCLM ℝ g`, read as a function, is the derivative $g'$ of $g$. -/
theorem coe_derivCLM (g : 𝓢(ℝ, ℂ)) : ((derivCLM ℝ (F := ℂ) g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
    = deriv (g : ℝ → ℂ) := funext fun t => derivCLM_apply ℝ g t

/-- For a Schwartz function $g \colon \mathbb{R} \to \mathbb{C}$, the function
$t \mapsto |t| |g(t)| |g'(t)|$ is integrable on $\mathbb{R}$. -/
theorem integrable_abs_mul_norm_mul_norm_deriv (g : 𝓢(ℝ, ℂ)) :
    Integrable (fun t : ℝ => |t| * ‖g t‖ * ‖deriv (g : ℝ → ℂ) t‖) := by
  refine (integrable_pow_norm_mul_norm g (derivCLM ℝ (F := ℂ) g) 1).congr
    (Filter.Eventually.of_forall fun t => ?_)
  simp only [pow_one, Real.norm_eq_abs, derivCLM_apply]
  ring

/-- The integration by parts identity in the form that the uncertainty principle uses: for a
Schwartz function $g \colon \mathbb{R} \to \mathbb{C}$,
$$\int |g(t)|^2 \, dt \le 2 \int |t| |g(t)| |g'(t)| \, dt.$$
-/
theorem integral_norm_sq_le_two_mul (g : 𝓢(ℝ, ℂ)) :
    ∫ t : ℝ, ‖g t‖ ^ 2 ≤ 2 * ∫ t : ℝ, |t| * ‖g t‖ * ‖deriv (g : ℝ → ℂ) t‖ := by
  have hsplit : (∫ t : ℝ, ‖g t‖ ^ 2)
      + ∫ t : ℝ, 2 * t * (deriv (g : ℝ → ℂ) t * conj (g t)).re = 0 := by
    rw [← integral_add (integrable_norm_sq g) (integrable_two_mul_re g)]
    exact integral_norm_sq_add_two_mul_re g
  have hb : |∫ t : ℝ, 2 * t * (deriv (g : ℝ → ℂ) t * conj (g t)).re|
      ≤ 2 * ∫ t : ℝ, |t| * ‖g t‖ * ‖deriv (g : ℝ → ℂ) t‖ := by
    calc |∫ t : ℝ, 2 * t * (deriv (g : ℝ → ℂ) t * conj (g t)).re|
        ≤ ∫ t : ℝ, |2 * t * (deriv (g : ℝ → ℂ) t * conj (g t)).re| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ t : ℝ, 2 * (|t| * ‖g t‖ * ‖deriv (g : ℝ → ℂ) t‖) := by
          refine integral_mono (integrable_two_mul_re g).abs
            ((integrable_abs_mul_norm_mul_norm_deriv g).const_mul 2) fun t => ?_
          have hre : |(deriv (g : ℝ → ℂ) t * conj (g t)).re| ≤ ‖deriv (g : ℝ → ℂ) t‖ * ‖g t‖ := by
            calc |(deriv (g : ℝ → ℂ) t * conj (g t)).re|
                ≤ ‖deriv (g : ℝ → ℂ) t * conj (g t)‖ := Complex.abs_re_le_norm _
              _ = ‖deriv (g : ℝ → ℂ) t‖ * ‖g t‖ := by rw [norm_mul, RCLike.norm_conj]
          calc |2 * t * (deriv (g : ℝ → ℂ) t * conj (g t)).re|
              = 2 * |t| * |(deriv (g : ℝ → ℂ) t * conj (g t)).re| := by
                rw [abs_mul, abs_mul]; norm_num
            _ ≤ 2 * |t| * (‖deriv (g : ℝ → ℂ) t‖ * ‖g t‖) := by gcongr
            _ = 2 * (|t| * ‖g t‖ * ‖deriv (g : ℝ → ℂ) t‖) := by ring
      _ = 2 * ∫ t : ℝ, |t| * ‖g t‖ * ‖deriv (g : ℝ → ℂ) t‖ := integral_const_mul _ _
  have := abs_le.mp hb
  linarith [hsplit, this.1, this.2]

/-- **The uncertainty principle in terms of the derivative**: for a Schwartz function
$g \colon \mathbb{R} \to \mathbb{C}$,
$$\Bigl(\int |g(t)|^2 \, dt\Bigr)^2 \le 4 \Bigl(\int t^2 |g(t)|^2 \, dt\Bigr) \Bigl(\int
  |g'(t)|^2 \, dt\Bigr).$$

Integration by parts bounds $\int |g|^2$ by $2 \int |t| |g| |g'|$. The Cauchy–Schwarz
inequality, which is Hölder's inequality with $p = q = 2$, bounds this by
$2 (\int t^2 |g|^2)^{1/2} (\int |g'|^2)^{1/2}$. -/
theorem heisenberg_uncertainty_deriv (g : 𝓢(ℝ, ℂ)) :
    (∫ t : ℝ, ‖g t‖ ^ 2) ^ 2
      ≤ 4 * (∫ t : ℝ, t ^ 2 * ‖g t‖ ^ 2) * ∫ t : ℝ, ‖deriv (g : ℝ → ℂ) t‖ ^ 2 := by
  set A := ∫ t : ℝ, t ^ 2 * ‖g t‖ ^ 2 with hA
  set D := ∫ t : ℝ, ‖deriv (g : ℝ → ℂ) t‖ ^ 2 with hD
  have hA0 : 0 ≤ A := integral_nonneg fun t => by positivity
  have hD0 : 0 ≤ D := integral_nonneg fun t => by positivity
  have hmem1 : MemLp (fun t : ℝ => |t| * ‖g t‖) 2 volume := by
    refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
    refine (integrable_sq_mul_norm_sq g).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [mul_pow, sq_abs]
  have hmem2 : MemLp (fun t : ℝ => ‖deriv (g : ℝ → ℂ) t‖) 2 volume := by
    refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
    refine (integrable_norm_sq (derivCLM ℝ (F := ℂ) g)).congr
      (Filter.Eventually.of_forall fun t => ?_)
    simp only [derivCLM_apply]
  have hcs := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume)
    Real.HolderConjugate.two_two
    (f := fun t : ℝ => |t| * ‖g t‖) (g := fun t : ℝ => ‖deriv (g : ℝ → ℂ) t‖)
    (Filter.Eventually.of_forall fun t => by positivity)
    (Filter.Eventually.of_forall fun t => by positivity)
    (by simpa using hmem1) (by simpa using hmem2)
  have hrw1 : ∫ t : ℝ, (|t| * ‖g t‖) ^ (2 : ℝ) = A := by
    rw [hA]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Real.rpow_two, mul_pow, sq_abs]
  have hrw2 : ∫ t : ℝ, ‖deriv (g : ℝ → ℂ) t‖ ^ (2 : ℝ) = D := by
    rw [hD]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Real.rpow_two]
  rw [hrw1, hrw2, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hcs
  have hN := integral_norm_sq_le_two_mul g
  have hN0 : 0 ≤ ∫ t : ℝ, ‖g t‖ ^ 2 := integral_nonneg fun t => by positivity
  have hle : ∫ t : ℝ, ‖g t‖ ^ 2 ≤ 2 * (√A * √D) := by linarith
  calc (∫ t : ℝ, ‖g t‖ ^ 2) ^ 2 ≤ (2 * (√A * √D)) ^ 2 := by
        exact pow_le_pow_left₀ hN0 hle 2
    _ = 4 * A * D := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hD0]
        ring

/-- **Plancherel's theorem for the derivative**: for a Schwartz function
$g \colon \mathbb{R} \to \mathbb{C}$,
$$\int |g'(t)|^2 \, dt = 4 \pi^2 \int \nu^2 |\hat{g}(\nu)|^2 \, d\nu.$$

The proof combines $\widehat{g'}(\nu) = 2 \pi i \nu \, \hat{g}(\nu)$ (`Real.fourier_deriv`) with
Plancherel's theorem `SchwartzMap.integral_norm_sq_fourier`. -/
theorem integral_norm_sq_deriv (g : 𝓢(ℝ, ℂ)) :
    ∫ t : ℝ, ‖deriv (g : ℝ → ℂ) t‖ ^ 2
      = 4 * π ^ 2 * ∫ v : ℝ, v ^ 2 * ‖𝓕 (g : ℝ → ℂ) v‖ ^ 2 := by
  have hint : Integrable (deriv (g : ℝ → ℂ)) := by
    have h : Integrable (⇑(derivCLM ℝ (F := ℂ) g)) volume := (derivCLM ℝ (F := ℂ) g).integrable
    rwa [coe_derivCLM g] at h
  have hfd : 𝓕 (deriv (g : ℝ → ℂ)) = fun v : ℝ => (2 * π * Complex.I * v) • 𝓕 (g : ℝ → ℂ) v :=
    Real.fourier_deriv g.integrable g.differentiable hint
  have hpl := SchwartzMap.integral_norm_sq_fourier (derivCLM ℝ (F := ℂ) g)
  rw [SchwartzMap.fourier_coe, coe_derivCLM g, hfd] at hpl
  rw [← hpl]
  calc ∫ v : ℝ, ‖(2 * π * Complex.I * v) • 𝓕 (g : ℝ → ℂ) v‖ ^ 2
      = ∫ v : ℝ, 4 * π ^ 2 * (v ^ 2 * ‖𝓕 (g : ℝ → ℂ) v‖ ^ 2) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        simp only [norm_smul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat,
          mul_one, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
    _ = 4 * π ^ 2 * ∫ v : ℝ, v ^ 2 * ‖𝓕 (g : ℝ → ℂ) v‖ ^ 2 := integral_const_mul _ _

/-- **The Heisenberg uncertainty principle**: for a Schwartz function
$g \colon \mathbb{R} \to \mathbb{C}$,
$$\Bigl(\int |g(t)|^2 \, dt\Bigr)^2 \le 16 \pi^2 \Bigl(\int t^2 |g(t)|^2 \, dt\Bigr) \Bigl(\int
  \nu^2 |\hat{g}(\nu)|^2 \, d\nu\Bigr),$$
where $\hat{g}(\nu) = \int g(t) e^{-2 \pi i \nu t} \, dt$. This is (10.88) of
[quarteroni2000numerical].

Normalize $\int |g|^2 = 1$ and pass to the angular frequency $\omega = 2 \pi \nu$, in which the
frequency spread is $4 \pi^2$ times the frequency spread in $\nu$. Then the inequality reads
$\Delta t \, \Delta \omega \ge 1/2$: a signal cannot be localized in time and in frequency at
the same time. -/
theorem heisenberg_uncertainty (g : 𝓢(ℝ, ℂ)) :
    (∫ t : ℝ, ‖g t‖ ^ 2) ^ 2
      ≤ 16 * π ^ 2 * (∫ t : ℝ, t ^ 2 * ‖g t‖ ^ 2)
        * ∫ v : ℝ, v ^ 2 * ‖𝓕 (g : ℝ → ℂ) v‖ ^ 2 := by
  have h := heisenberg_uncertainty_deriv g
  rw [integral_norm_sq_deriv g] at h
  calc (∫ t : ℝ, ‖g t‖ ^ 2) ^ 2
      ≤ 4 * (∫ t : ℝ, t ^ 2 * ‖g t‖ ^ 2) * (4 * π ^ 2 * ∫ v : ℝ, v ^ 2 * ‖𝓕 (g : ℝ → ℂ) v‖ ^ 2) :=
        h
    _ = 16 * π ^ 2 * (∫ t : ℝ, t ^ 2 * ‖g t‖ ^ 2) * ∫ v : ℝ, v ^ 2 * ‖𝓕 (g : ℝ → ℂ) v‖ ^ 2 := by
        ring

end SchwartzMap
