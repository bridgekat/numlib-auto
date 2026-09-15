import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Heisenberg uncertainty principle

For a Schwartz function `g : 𝓢(ℝ, ℂ)` the *time spread* `∫ t² |g|²` and the *frequency spread*
`∫ ν² |𝓕g|²` cannot both be small: their product is at least `(∫ |g|²)² / (16 π²)`. Equivalently,
with `ω = 2πν` the angular frequency, the resolutions `Δt = (∫ t²|g|²/∫|g|²)^{1/2}` and
`Δω = (∫ ω²|G(ω)|²/∫|G(ω)|²)^{1/2}` satisfy `Δt Δω ≥ 1/2`.

The proof is the classical one. Integration by parts on the whole line applied to
`t ↦ t g(t) conj(g(t))`, whose value tends to `0` at both ends because `g` is Schwartz, gives

`∫ |g|² = -2 ∫ t Re(g'(t) conj(g(t)))`;

Cauchy–Schwarz (Hölder with `p = q = 2`) bounds the right-hand side by
`2 (∫ t²|g|²)^{1/2} (∫ |g'|²)^{1/2}`; and Plancherel together with
`𝓕(g')(ν) = 2πiν 𝓕g(ν)` turns `∫ |g'|²` into `4π² ∫ ν² |𝓕g|²`.

Mathlib has no uncertainty principle (checked by grep for `Heisenberg` and `uncertainty`); it does
have every ingredient, in particular `SchwartzMap.integral_norm_sq_fourier` (Plancherel for
Schwartz functions) and `Real.fourier_deriv`.

## Main results

* `SchwartzMap.integral_norm_sq_add_two_mul_re` — the integration by parts identity
  `∫ (|g|² + 2t Re(g' conj g)) = 0`.
* `SchwartzMap.heisenberg_uncertainty_deriv` — `(∫ |g|²)² ≤ 4 (∫ t²|g|²) (∫ |g'|²)`.
* `SchwartzMap.heisenberg_uncertainty` — `(∫ |g|²)² ≤ 16 π² (∫ t²|g|²) (∫ ν²|𝓕g|²)`.

Reference: [quarteroni2000numerical] (10.88).
-/

open MeasureTheory Real Complex Filter Topology Set

open scoped FourierTransform ComplexConjugate

namespace SchwartzMap

/-- `t ↦ ‖t‖^k ‖g t‖ ‖h t‖` is integrable for Schwartz `g` and `h`: the factor `‖h t‖` is bounded
and `‖t‖^k ‖g t‖` is integrable (`SchwartzMap.integrable_pow_mul`). -/
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

/-- `t ↦ ‖g t‖²` is integrable for a Schwartz function. -/
theorem integrable_norm_sq (g : 𝓢(ℝ, ℂ)) : Integrable (fun t : ℝ => ‖g t‖ ^ 2) := by
  refine (integrable_pow_norm_mul_norm g g 0).congr (Filter.Eventually.of_forall fun t => ?_)
  simp [sq]

/-- `t ↦ t² ‖g t‖²` is integrable for a Schwartz function: the time spread is finite. -/
theorem integrable_sq_mul_norm_sq (g : 𝓢(ℝ, ℂ)) :
    Integrable (fun t : ℝ => t ^ 2 * ‖g t‖ ^ 2) := by
  refine (integrable_pow_norm_mul_norm g g 2).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  ring

/-! ### Integration by parts -/

/-- `t ↦ t g(t) conj(g(t))` tends to `0` at infinity: `‖t‖ ‖g t‖` is bounded and `‖g t‖ → 0`. This
is the boundary term of the integration by parts below. -/
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

/-- The derivative of `t ↦ t g(t) conj(g(t))` is `‖g t‖² + 2t Re(g'(t) conj(g(t)))`, a real
quantity: the product rule, `z conj z = ‖z‖²` and `w + conj w = 2 Re w`. -/
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

/-- **Integration by parts on the whole line.** For a Schwartz function `g`,

`∫ (‖g t‖² + 2t Re(g'(t) conj(g(t)))) dt = 0`,

because the integrand is the derivative of `t ↦ t g(t) conj(g(t))`, which is integrable and tends
to `0` at both ends of the line. -/
theorem integral_norm_sq_add_two_mul_re (g : 𝓢(ℝ, ℂ)) :
    ∫ t : ℝ, (‖g t‖ ^ 2 + 2 * t * (deriv (g : ℝ → ℂ) t * conj (g t)).re) = 0 := by
  set F : ℝ → ℂ := fun s : ℝ => (s : ℂ) * (g s * conj (g s)) with hF
  set u : ℝ → ℝ := fun t => ‖g t‖ ^ 2 + 2 * t * (deriv (g : ℝ → ℂ) t * conj (g t)).re with hu
  have hderiv : ∀ t, HasDerivAt F ((u t : ℂ)) t := hasDerivAt_mul_mul_conj g
  have hbound : Integrable u := by
    refine Integrable.add (integrable_norm_sq g) ?_
    obtain ⟨C, hC0, hC⟩ := (derivCLM ℝ (F := ℂ) g).decay 0 0
    simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul, derivCLM_apply] at hC
    refine Integrable.mono' ((g.integrable_pow_mul volume 1).const_mul (2 * C))
      (by fun_prop) ?_
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

/-- The Schwartz map `derivCLM ℝ g` is the derivative of `g` as a function. -/
theorem coe_derivCLM (g : 𝓢(ℝ, ℂ)) : ((derivCLM ℝ (F := ℂ) g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
    = deriv (g : ℝ → ℂ) := funext fun t => derivCLM_apply ℝ g t

/-- `t ↦ 2t Re(g'(t) conj(g(t)))` is integrable: `‖g'‖` is bounded and `‖t‖ ‖g t‖` is
integrable. -/
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

/-- `t ↦ |t| ‖g t‖ ‖g'(t)‖` is integrable. -/
theorem integrable_abs_mul_norm_mul_norm_deriv (g : 𝓢(ℝ, ℂ)) :
    Integrable (fun t : ℝ => |t| * ‖g t‖ * ‖deriv (g : ℝ → ℂ) t‖) := by
  refine (integrable_pow_norm_mul_norm g (derivCLM ℝ (F := ℂ) g) 1).congr
    (Filter.Eventually.of_forall fun t => ?_)
  simp only [pow_one, Real.norm_eq_abs, derivCLM_apply]
  ring

/-- The integration by parts identity in the form used below:
`∫ ‖g‖² ≤ 2 ∫ |t| ‖g t‖ ‖g'(t)‖`. -/
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

/-- **The uncertainty principle, in terms of the derivative.** For a Schwartz function `g`,

`(∫ ‖g t‖² dt)² ≤ 4 (∫ t² ‖g t‖² dt) (∫ ‖g'(t)‖² dt)`.

Integration by parts bounds `∫ ‖g‖²` by `2 ∫ |t| ‖g‖ ‖g'‖`, and Cauchy–Schwarz — Hölder's
inequality at `p = q = 2` — bounds that by `2 (∫ t²‖g‖²)^{1/2} (∫ ‖g'‖²)^{1/2}`. -/
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

/-- **Plancherel for the derivative:** `∫ ‖g'(t)‖² dt = 4π² ∫ ν² ‖𝓕g(ν)‖² dν`, from
`𝓕(g')(ν) = 2πiν 𝓕g(ν)` (`Real.fourier_deriv`) and `SchwartzMap.integral_norm_sq_fourier`. -/
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

/-- **The Heisenberg uncertainty principle.** For a Schwartz function `g : 𝓢(ℝ, ℂ)`,

`(∫ ‖g t‖² dt)² ≤ 16 π² (∫ t² ‖g t‖² dt) (∫ ν² ‖𝓕g(ν)‖² dν)`.

Normalising `∫ ‖g‖² = 1` and passing to the angular frequency `ω = 2πν`, in which the frequency
spread is `4π²` times the one in `ν`, this reads `Δt Δω ≥ 1/2`: a signal cannot be localised
simultaneously in time and in frequency.

Reference: [quarteroni2000numerical] (10.88). -/
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
