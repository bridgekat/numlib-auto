/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Fourier.AddCircle`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The Dirichlet kernel and pointwise convergence of Fourier series

Mathlib has the `L²` theory of Fourier series on the circle and the uniform convergence of an
absolutely summable series, but no Dirichlet kernel and no pointwise convergence criterion. This
file supplies both, for a `2 π`-periodic, interval-integrable `f : ℝ → ℝ`. [Atkinson and
Han][han2009theoretical] state the kernel as (3.7.6)–(3.7.8) and the partial sums as
(4.1.1)–(4.1.3). Their Theorem 4.1.1 — convergence to the mean of the one-sided limits at a point
where the one-sided derivatives exist — is the criterion `tendsto_fourierPartialSum_of_dini` applied
to that mean; `tendsto_fourierPartialSum_of_hasDerivAt` is its corollary at a point of
differentiability.

## Main definitions

* `dirichletKernel n t = 1 / 2 + ∑_{j = 1}^{n} cos (j t)`, the kernel of the `n`-th partial-sum
  operator;
* `fourierCoeffCos` and `fourierCoeffSin`, the real Fourier coefficients `a_j` and `b_j`;
* `fourierPartialSum f n x = a₀ / 2 + ∑_{j = 1}^{n} (a_j cos (j x) + b_j sin (j x))`, the `n`-th
  partial sum of the real Fourier series.

## Main statements

* `dirichletKernel_eq_sin_div`, the closed form `sin ((n + 1/2) t) / (2 sin (t / 2))`;
* `fourierPartialSum_eq_integral`, the kernel representation
  `fourierPartialSum f n x = (1 / π) * ∫ t in -π..π, f (x + t) * dirichletKernel n t`;
* `tendsto_fourierPartialSum_of_dini`, **Dini's criterion**: if
  `t ↦ (f (x + t) + f (x - t) - 2 L) / t` is interval-integrable on `[0, π]` then
  `fourierPartialSum f n x → L`.

## Implementation notes

Everything is stated for a function on `ℝ` rather than on `AddCircle (2 π)`, because the
hypotheses of a pointwise convergence theorem are about one-sided limits at a real point.

The proof of Dini's criterion is the classical one: the difference `S_n f x - L` is
`(1 / π) ∫_0^π g t * sin ((n + 1/2) t)` for
`g t = (f (x + t) + f (x - t) - 2 L) / (2 sin (t / 2))`, which is integrable under the Dini
hypothesis because `2 sin (t / 2) ≥ 2 t / π` on `[0, π]`; the Riemann–Lebesgue lemma finishes.
Mathlib states that lemma for the Fourier integral over `ℝ`
(`Real.tendsto_integral_exp_smul_cocompact`), so the form needed here — the integral of
`g t * sin (r t)` over an interval tends to `0` as `r → ∞` — is obtained by extending `g` by zero,
which is `tendsto_intervalIntegral_mul_sin`.
-/

open MeasureTheory Filter Topology

open scoped Real FourierTransform

/-! ### The Dirichlet kernel -/

/-- The Dirichlet kernel `D_n t = 1 / 2 + ∑_{j = 1}^{n} cos (j t)`, the kernel of the `n`-th
partial-sum operator of a Fourier series. -/
noncomputable def dirichletKernel (n : ℕ) (t : ℝ) : ℝ :=
  1 / 2 + ∑ j ∈ Finset.Icc 1 n, Real.cos (j * t)

theorem dirichletKernel_apply (n : ℕ) (t : ℝ) :
    dirichletKernel n t = 1 / 2 + ∑ j ∈ Finset.Icc 1 n, Real.cos (j * t) :=
  rfl

@[simp]
theorem dirichletKernel_zero (t : ℝ) : dirichletKernel 0 t = 1 / 2 := by
  simp [dirichletKernel_apply]

theorem dirichletKernel_succ (n : ℕ) (t : ℝ) :
    dirichletKernel (n + 1) t = dirichletKernel n t + Real.cos ((n + 1) * t) := by
  rw [dirichletKernel_apply, dirichletKernel_apply, Finset.sum_Icc_succ_top (by omega),
    ← add_assoc]
  norm_num

@[simp]
theorem dirichletKernel_neg (n : ℕ) (t : ℝ) : dirichletKernel n (-t) = dirichletKernel n t := by
  simp [dirichletKernel_apply, mul_neg]

theorem dirichletKernel_periodic (n : ℕ) : Function.Periodic (dirichletKernel n) (2 * π) := by
  intro t
  simp only [dirichletKernel_apply]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [mul_add]
  simp

@[fun_prop]
theorem continuous_dirichletKernel (n : ℕ) : Continuous (dirichletKernel n) := by
  have h : dirichletKernel n = fun t => 1 / 2 + ∑ j ∈ Finset.Icc 1 n, Real.cos (j * t) := rfl
  rw [h]
  fun_prop

/-- The telescoping identity behind the closed form of the Dirichlet kernel. -/
theorem two_mul_sin_half_mul_dirichletKernel (n : ℕ) (t : ℝ) :
    2 * Real.sin (t / 2) * dirichletKernel n t = Real.sin ((n + 1 / 2) * t) := by
  induction n with
  | zero =>
    rw [dirichletKernel_zero, show (((0 : ℕ) : ℝ) + 1 / 2) * t = t / 2 by push_cast; ring]
    ring
  | succ n ih =>
    have hstep : 2 * Real.sin (t / 2) * Real.cos (((n : ℝ) + 1) * t)
        = Real.sin (((n : ℝ) + 1 + 1 / 2) * t) - Real.sin (((n : ℝ) + 1 / 2) * t) := by
      rw [show ((n : ℝ) + 1 + 1 / 2) * t = t / 2 + ((n : ℝ) + 1) * t by ring, Real.sin_add,
        show ((n : ℝ) + 1 / 2) * t = ((n : ℝ) + 1) * t - t / 2 by ring, Real.sin_sub]
      ring
    rw [dirichletKernel_succ, mul_add, ih]
    push_cast
    rw [hstep]
    ring

/-- The closed form of the Dirichlet kernel (Atkinson and Han, *Theoretical Numerical Analysis*,
(3.7.8)). The hypothesis `sin (t / 2) ≠ 0` says exactly that `t` is not an integer multiple of
`2 π`. -/
theorem dirichletKernel_eq_sin_div {n : ℕ} {t : ℝ} (ht : Real.sin (t / 2) ≠ 0) :
    dirichletKernel n t = Real.sin ((n + 1 / 2) * t) / (2 * Real.sin (t / 2)) := by
  rw [← two_mul_sin_half_mul_dirichletKernel n t]
  field_simp

/-- The Dirichlet kernel has mean `1 / 2` over half a period (Atkinson and Han, *Theoretical
Numerical Analysis*, Exercise 4.1.4 (b)). -/
theorem integral_dirichletKernel (n : ℕ) :
    (1 / π) * ∫ t in (0 : ℝ)..π, dirichletKernel n t = 1 / 2 := by
  have hcos : ∀ c : ℝ, c ≠ 0 → Real.sin (c * π) = 0 →
      ∫ t in (0 : ℝ)..π, Real.cos (c * t) = 0 := by
    intro c hc hs
    rw [intervalIntegral.integral_comp_mul_left Real.cos hc, integral_cos]
    simp [hs]
  have hint : ∀ m : ℕ, ∫ t in (0 : ℝ)..π, dirichletKernel m t = π / 2 := by
    intro m
    induction m with
    | zero =>
      simp
      ring
    | succ m ih =>
      have hc : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hs : Real.sin (((m : ℝ) + 1) * π) = 0 := by
        have h := Real.sin_nat_mul_pi (m + 1)
        push_cast at h
        exact h
      have hI1 : IntervalIntegrable (dirichletKernel m) volume 0 π :=
        (continuous_dirichletKernel m).intervalIntegrable _ _
      have hI2 : IntervalIntegrable (fun t : ℝ => Real.cos (((m : ℝ) + 1) * t)) volume 0 π :=
        (by fun_prop : Continuous fun t : ℝ => Real.cos (((m : ℝ) + 1) * t)).intervalIntegrable _ _
      simp only [dirichletKernel_succ]
      rw [intervalIntegral.integral_add hI1 hI2, ih, hcos _ hc hs, add_zero]
  rw [hint n]
  field_simp

/-- The Dirichlet kernel has mean `1 / 2` over the other half period, by evenness. -/
theorem integral_dirichletKernel_neg (n : ℕ) :
    (1 / π) * ∫ t in -π..(0 : ℝ), dirichletKernel n t = 1 / 2 := by
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π) (dirichletKernel n)
  simp only [dirichletKernel_neg, neg_zero] at h
  rw [← h, integral_dirichletKernel]

/-- The Dirichlet kernel has mean `1` over a full period. -/
theorem integral_dirichletKernel_neg_pi_pi (n : ℕ) :
    (1 / π) * ∫ t in -π..π, dirichletKernel n t = 1 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ))
      ((continuous_dirichletKernel n).intervalIntegrable _ _)
      ((continuous_dirichletKernel n).intervalIntegrable _ _),
    mul_add, integral_dirichletKernel_neg, integral_dirichletKernel]
  norm_num

private theorem integral_fold_neg {H : ℝ → ℝ} (h₁ : IntervalIntegrable H volume (-π) 0)
    (h₂ : IntervalIntegrable H volume 0 π) :
    ∫ t in -π..π, H t = ∫ t in (0 : ℝ)..π, (H t + H (-t)) := by
  have h₃ : IntervalIntegrable (fun t => H (-t)) volume 0 π := by
    simpa using ((IntervalIntegrable.iff_comp_neg (a := -π) (b := 0)).mp h₁).symm
  rw [intervalIntegral.integral_add h₂ h₃, intervalIntegral.integral_comp_neg H, neg_zero,
    add_comm, intervalIntegral.integral_add_adjacent_intervals h₁ h₂]

/-! ### The partial sums of a Fourier series -/

/-- The cosine coefficient `a_j = (1 / π) ∫_{-π}^{π} f t cos (j t) dt` of the Fourier series of a
`2 π`-periodic `f : ℝ → ℝ` (Atkinson and Han, *Theoretical Numerical Analysis*, (4.1.2)). -/
noncomputable def fourierCoeffCos (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  (1 / π) * ∫ t in -π..π, f t * Real.cos (j * t)

/-- The sine coefficient `b_j = (1 / π) ∫_{-π}^{π} f t sin (j t) dt` of the Fourier series of a
`2 π`-periodic `f : ℝ → ℝ` (Atkinson and Han, *Theoretical Numerical Analysis*, (4.1.3)). -/
noncomputable def fourierCoeffSin (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  (1 / π) * ∫ t in -π..π, f t * Real.sin (j * t)

/-- The `n`-th partial sum `a₀ / 2 + ∑_{j = 1}^{n} (a_j cos (j x) + b_j sin (j x))` of the real
Fourier series of a `2 π`-periodic `f : ℝ → ℝ` (Atkinson and Han, *Theoretical Numerical
Analysis*, (4.1.1)). -/
noncomputable def fourierPartialSum (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  fourierCoeffCos f 0 / 2 + ∑ j ∈ Finset.Icc 1 n,
    (fourierCoeffCos f j * Real.cos (j * x) + fourierCoeffSin f j * Real.sin (j * x))

private theorem intervalIntegral_periodic_shift {G : ℝ → ℝ} (hG : Function.Periodic G (2 * π))
    (c : ℝ) : ∫ t in (c + -π)..(c + π), G t = ∫ t in -π..π, G t := by
  have h := hG.intervalIntegral_add_eq (c + -π) (-π)
  rw [show c + -π + 2 * π = c + π by ring, show -π + 2 * π = π by ring] at h
  exact h

section Periodic

variable {f : ℝ → ℝ} (hf : Function.Periodic f (2 * π))
  (hfi : IntervalIntegrable f volume (-π) π)

include hf hfi

/-- A `2 π`-periodic function that is interval-integrable over one period is interval-integrable
over every interval. -/
theorem intervalIntegrable_of_periodic (a b : ℝ) : IntervalIntegrable f volume a b :=
  hf.intervalIntegrable (by positivity) (t := -π) (by rw [show -π + 2 * π = π by ring]; exact hfi)
    a b

omit hf hfi in
theorem fourierPartialSum_succ (n : ℕ) (x : ℝ) :
    fourierPartialSum f (n + 1) x = fourierPartialSum f n x
      + (fourierCoeffCos f (n + 1) * Real.cos ((n + 1 : ℕ) * x)
        + fourierCoeffSin f (n + 1) * Real.sin ((n + 1 : ℕ) * x)) := by
  simp only [fourierPartialSum]
  rw [Finset.sum_Icc_succ_top (by omega)]
  ring

/-- **The kernel representation of the partial sums** (Atkinson and Han, *Theoretical Numerical
Analysis*, (3.7.6) and Exercise 4.1.4): the `n`-th partial sum of the Fourier series of `f` at `x`
is the mean of `f` against the Dirichlet kernel recentered at `x`. -/
theorem fourierPartialSum_eq_integral (n : ℕ) (x : ℝ) :
    fourierPartialSum f n x = (1 / π) * ∫ t in -π..π, f (x + t) * dirichletKernel n t := by
  have hall := intervalIntegrable_of_periodic hf hfi
  have hmul : ∀ g : ℝ → ℝ, Continuous g →
      IntervalIntegrable (fun t => f t * g t) volume (-π) π :=
    fun g hg => (hall (-π) π).mul_continuousOn hg.continuousOn
  have hstep : ∀ m : ℕ, ∫ t in -π..π, f t * dirichletKernel m (t - x)
      = π * fourierPartialSum f m x := by
    intro m
    induction m with
    | zero =>
      have e0 : ∫ t in -π..π, f t * dirichletKernel 0 (t - x)
          = (∫ t in -π..π, f t * Real.cos ((0 : ℕ) * t)) / 2 := by
        rw [← intervalIntegral.integral_div]
        exact intervalIntegral.integral_congr fun t _ => by simp; ring
      have hIcc : (Finset.Icc 1 0 : Finset ℕ) = ∅ := by simp
      rw [e0, fourierPartialSum, hIcc, Finset.sum_empty, add_zero, fourierCoeffCos]
      field_simp
    | succ m ih =>
      have hexp : ∀ t : ℝ, f t * dirichletKernel (m + 1) (t - x)
          = f t * dirichletKernel m (t - x) + f t * Real.cos (((m : ℝ) + 1) * (t - x)) := by
        intro t
        rw [dirichletKernel_succ]
        ring
      have e0 : ∫ t in -π..π, f t * dirichletKernel (m + 1) (t - x)
          = ∫ t in -π..π, (f t * dirichletKernel m (t - x)
              + f t * Real.cos (((m : ℝ) + 1) * (t - x))) :=
        intervalIntegral.integral_congr fun t _ => hexp t
      have hsplit : ∫ t in -π..π, f t * Real.cos (((m : ℝ) + 1) * (t - x))
          = Real.cos (((m : ℝ) + 1) * x) * (∫ t in -π..π, f t * Real.cos (((m : ℝ) + 1) * t))
            + Real.sin (((m : ℝ) + 1) * x)
              * (∫ t in -π..π, f t * Real.sin (((m : ℝ) + 1) * t)) := by
        have e1 : ∫ t in -π..π, f t * Real.cos (((m : ℝ) + 1) * (t - x))
            = ∫ t in -π..π, (Real.cos (((m : ℝ) + 1) * x) * (f t * Real.cos (((m : ℝ) + 1) * t))
                + Real.sin (((m : ℝ) + 1) * x) * (f t * Real.sin (((m : ℝ) + 1) * t))) :=
          intervalIntegral.integral_congr fun t _ => by
            rw [show ((m : ℝ) + 1) * (t - x) = ((m : ℝ) + 1) * t - ((m : ℝ) + 1) * x by ring,
              Real.cos_sub]
            ring
        rw [e1, intervalIntegral.integral_add ((hmul _ (by fun_prop)).const_mul _)
            ((hmul _ (by fun_prop)).const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      rw [e0, intervalIntegral.integral_add (hmul _ (by fun_prop)) (hmul _ (by fun_prop)), ih,
        hsplit, fourierPartialSum_succ]
      simp only [fourierCoeffCos, fourierCoeffSin]
      push_cast
      field_simp
  have hper : Function.Periodic (fun t => f t * dirichletKernel n (t - x)) (2 * π) := by
    intro t
    dsimp only
    rw [show t + 2 * π - x = t - x + 2 * π by ring, hf t, dirichletKernel_periodic n (t - x)]
  have hshift : ∫ t in -π..π, f (x + t) * dirichletKernel n t
      = ∫ t in -π..π, f t * dirichletKernel n (t - x) := by
    have e0 : ∫ t in -π..π, f (x + t) * dirichletKernel n t
        = ∫ t in -π..π, (fun u => f u * dirichletKernel n (u - x)) (x + t) :=
      intervalIntegral.integral_congr fun t _ => by simp
    rw [e0, intervalIntegral.integral_comp_add_left (fun u => f u * dirichletKernel n (u - x)) x]
    exact intervalIntegral_periodic_shift hper x
  rw [hshift, hstep]
  field_simp

end Periodic

/-! ### The Riemann–Lebesgue lemma over an interval -/

/-- The Riemann–Lebesgue lemma in the form the Dirichlet-kernel argument needs: the integral of
`g t * sin (r t)` over an interval tends to `0` as `r → ∞`. Obtained from Mathlib's
`Real.tendsto_integral_exp_smul_cocompact` by extending `g` by zero. -/
theorem tendsto_intervalIntegral_mul_sin {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b) :
    Tendsto (fun r : ℝ => ∫ t in a..b, g t * Real.sin (r * t)) atTop (𝓝 0) := by
  set G : ℝ → ℂ := fun t => ((Set.indicator (Set.Ioc a b) g t : ℝ) : ℂ) with hGdef
  have hind : Integrable (Set.indicator (Set.Ioc a b) g) volume := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hg
  have hGi : Integrable G := by
    rw [hGdef]
    exact hind.ofReal
  have hbdd : ∀ w : ℝ, Integrable (fun v : ℝ => ((𝐞 (-(v * w)) : Circle) : ℂ) * G v) := by
    intro w
    refine Integrable.bdd_mul (c := 1) hGi ?_ (Filter.Eventually.of_forall fun v => ?_)
    · fun_prop
    · exact le_of_eq (Circle.norm_coe _)
  have key := Real.tendsto_integral_exp_smul_cocompact G
  simp only [Circle.smul_def] at key
  have him : Tendsto (fun w : ℝ => (∫ v : ℝ, ((𝐞 (-(v * w)) : Circle) : ℂ) * G v).im)
      (cocompact ℝ) (𝓝 0) := by
    have h := (Complex.continuous_im.tendsto (0 : ℂ)).comp key
    rw [Complex.zero_im] at h
    exact h
  have hval : ∀ w : ℝ, (∫ v : ℝ, ((𝐞 (-(v * w)) : Circle) : ℂ) * G v).im
      = -∫ t in a..b, g t * Real.sin (2 * π * w * t) := by
    intro w
    have h := ContinuousLinearMap.integral_comp_comm Complex.imCLM (hbdd w)
    simp only [Complex.imCLM_apply] at h
    rw [← h]
    have hpt : ∀ v : ℝ, (((𝐞 (-(v * w)) : Circle) : ℂ) * G v).im
        = -(Real.sin (2 * π * w * v) * Set.indicator (Set.Ioc a b) g v) := by
      intro v
      rw [Real.fourierChar_apply]
      simp only [hGdef, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero]
      rw [show ((2 * π * -(v * w) : ℝ) : ℂ) * Complex.I
          = ((-(2 * π * w * v) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_ofReal_mul_I_im, Real.sin_neg]
      ring
    simp only [hpt]
    rw [MeasureTheory.integral_neg]
    congr 1
    rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_indicator measurableSet_Ioc]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    by_cases hv : v ∈ Set.Ioc a b
    · simp [Set.indicator_of_mem hv, mul_comm]
    · simp [Set.indicator_of_notMem hv]
  simp only [hval] at him
  have hneg : Tendsto (fun w : ℝ => ∫ t in a..b, g t * Real.sin (2 * π * w * t))
      (cocompact ℝ) (𝓝 0) := by simpa using him.neg
  have hcomp : Tendsto (fun r : ℝ => r / (2 * π)) atTop (cocompact ℝ) :=
    Tendsto.mono_right (Filter.Tendsto.atTop_div_const (by positivity) tendsto_id)
      (by rw [cocompact_eq_atBot_atTop]; exact le_sup_right)
  refine (hneg.comp hcomp).congr fun r => ?_
  simp only [Function.comp_apply]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  congr 2
  field_simp

/-! ### Dini's criterion -/

section Dini

variable {f : ℝ → ℝ} (hf : Function.Periodic f (2 * π))
  (hfi : IntervalIntegrable f volume (-π) π)

include hf hfi

/-- **Dini's criterion** for the pointwise convergence of a Fourier series: if the symmetrized
difference quotient `t ↦ (f (x + t) + f (x - t) - 2 L) / t` is interval-integrable on `[0, π]`,
then the Fourier partial sums of `f` at `x` converge to `L`. Every hypothesis under which
Atkinson and Han, *Theoretical Numerical Analysis*, Theorem 4.1.1 asserts convergence — one-sided
derivatives, Hölder continuity at `x`, differentiability at `x` — implies it. -/
theorem tendsto_fourierPartialSum_of_dini {x L : ℝ}
    (hdini : IntervalIntegrable (fun t => (f (x + t) + f (x - t) - 2 * L) / t) volume 0 π) :
    Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 L) := by
  have hall := intervalIntegrable_of_periodic hf hfi
  have hshift : ∀ a b : ℝ, IntervalIntegrable (fun t => f (x + t)) volume a b := fun a b => by
    simpa using (hall (x + a) (x + b)).comp_add_left x
  -- Step 1: `S_n f x - L` is the mean of the symmetrized difference against the kernel
  have step1 : ∀ n : ℕ, fourierPartialSum f n x - L
      = (1 / π) * ∫ t in (0 : ℝ)..π, (f (x + t) + f (x - t) - 2 * L) * dirichletKernel n t := by
    intro n
    have hDc : Continuous (dirichletKernel n) := continuous_dirichletKernel n
    have hI : ∀ a b : ℝ, IntervalIntegrable
        (fun t => f (x + t) * dirichletKernel n t - L * dirichletKernel n t) volume a b :=
      fun a b => ((hshift a b).mul_continuousOn hDc.continuousOn).sub
        ((hDc.intervalIntegrable a b).const_mul _)
    have hL : L = (1 / π) * ∫ t in -π..π, L * dirichletKernel n t := by
      rw [intervalIntegral.integral_const_mul, ← mul_assoc, mul_comm (1 / π) L, mul_assoc,
        integral_dirichletKernel_neg_pi_pi, mul_one]
    rw [fourierPartialSum_eq_integral hf hfi]
    nth_rewrite 1 [hL]
    rw [← mul_sub, ← intervalIntegral.integral_sub
      ((hshift _ _).mul_continuousOn hDc.continuousOn)
      ((hDc.intervalIntegrable _ _).const_mul _)]
    congr 1
    rw [integral_fold_neg (hI (-π) 0) (hI 0 π)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [dirichletKernel_neg, show ∀ s : ℝ, x + -s = x - s from fun s => by ring]
    ring
  -- Step 2: the integrand is `g t * sin ((n + 1/2) t)` with `g` integrable
  have hsin : ∀ t ∈ Set.Ioc (0 : ℝ) π, Real.sin (t / 2) ≠ 0 := by
    intro t ht
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2,
      Real.pi_pos]))
  have hbound : ∀ t ∈ Set.Ioc (0 : ℝ) π, ‖t / (2 * Real.sin (t / 2))‖ ≤ π / 2 := by
    intro t ht
    have h1 : 0 < t := ht.1
    have h2 : t ≤ π := ht.2
    have hjordan : 2 / π * (t / 2) ≤ Real.sin (t / 2) :=
      Real.mul_le_sin (by linarith) (by linarith)
    have hπ : 0 < π := Real.pi_pos
    have hs : 0 < Real.sin (t / 2) := lt_of_lt_of_le (by positivity) hjordan
    have hkey : t ≤ Real.sin (t / 2) * π := by
      rw [← div_le_iff₀ hπ]
      calc t / π = 2 / π * (t / 2) := by ring
        _ ≤ Real.sin (t / 2) := hjordan
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    linarith
  have hgi : IntervalIntegrable
      (fun t => (f (x + t) + f (x - t) - 2 * L) / (2 * Real.sin (t / 2))) volume 0 π := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le]
    have hprod : IntegrableOn
        (fun t => ((f (x + t) + f (x - t) - 2 * L) / t) * (t / (2 * Real.sin (t / 2))))
        (Set.Ioc 0 π) := by
      refine Integrable.mul_bdd (c := π / 2)
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mp hdini) ?_ ?_
      · exact (measurable_id.div (measurable_const.mul
          (Real.continuous_sin.comp (continuous_id.div_const 2)).measurable)).aestronglyMeasurable
      · exact (ae_restrict_iff' measurableSet_Ioc).2
          (Filter.Eventually.of_forall fun t ht => hbound t ht)
    refine hprod.congr ((ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall fun t ht => ?_))
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    field_simp
  -- Step 3: Riemann–Lebesgue
  have hRL := tendsto_intervalIntegral_mul_sin (g := fun t =>
    (f (x + t) + f (x - t) - 2 * L) / (2 * Real.sin (t / 2))) Real.pi_pos.le hgi
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1 / 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hfin := hRL.comp hnat
  have heq : ∀ n : ℕ, fourierPartialSum f n x - L
      = (1 / π) * ∫ t in (0 : ℝ)..π,
        (f (x + t) + f (x - t) - 2 * L) / (2 * Real.sin (t / 2))
          * Real.sin (((n : ℝ) + 1 / 2) * t) := by
    intro n
    rw [step1 n]
    congr 1
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Set.uIoc_of_le Real.pi_pos.le] at ht
    rw [dirichletKernel_eq_sin_div (hsin t ht)]
    ring
  have : Tendsto (fun n : ℕ => fourierPartialSum f n x - L) atTop (𝓝 0) := by
    simp only [heq]
    simpa using hfin.const_mul (1 / π)
  have hfinal := this.add_const L
  simpa using hfinal

/-- The consumer form of Dini's criterion: a `2 π`-periodic, interval-integrable function that is
differentiable at `x` has its Fourier series converging to `f x` there.

This is the corollary at a point of differentiability of Atkinson and Han, *Theoretical Numerical
Analysis*, Theorem 4.1.1; the theorem itself asks only for the two one-sided derivatives and
concludes convergence to `(f (x-) + f (x+)) / 2`, which is
`tendsto_fourierPartialSum_of_dini` applied to that mean. -/
theorem tendsto_fourierPartialSum_of_hasDerivAt {x c : ℝ} (hd : HasDerivAt f c x) :
    Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 (f x)) := by
  have hall := intervalIntegrable_of_periodic hf hfi
  have hshift : ∀ a b : ℝ, IntervalIntegrable (fun t => f (x + t)) volume a b := fun a b => by
    simpa using (hall (x + a) (x + b)).comp_add_left x
  have hrefl : ∀ a b : ℝ, IntervalIntegrable (fun t => f (x - t)) volume a b := fun a b => by
    simpa using (hall (x - a) (x - b)).comp_sub_left x
  have hφ : ∀ a b : ℝ,
      IntervalIntegrable (fun t => f (x + t) + f (x - t) - 2 * f x) volume a b := fun a b =>
    ((hshift a b).add (hrefl a b)).sub intervalIntegrable_const
  have hlim : Tendsto (fun t : ℝ => (f (x + t) + f (x - t) - 2 * f x) / t)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have h1 : HasDerivAt (fun t : ℝ => f (x + t)) c 0 :=
      HasDerivAt.comp_const_add x 0 (by simpa using hd)
    have h2 : HasDerivAt (fun t : ℝ => f (x - t)) (-c) 0 :=
      HasDerivAt.comp_const_sub x 0 (by simpa using hd)
    have hsum := (hasDerivAt_iff_tendsto_slope.mp h1).add (hasDerivAt_iff_tendsto_slope.mp h2)
    rw [show c + -c = 0 by ring] at hsum
    refine hsum.congr fun t => ?_
    simp only [slope, vsub_eq_sub, smul_eq_mul, sub_zero, add_zero]
    rw [← mul_add, div_eq_inv_mul]
    ring_nf
  obtain ⟨δ, hδ0, hδ⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim 1 one_pos
  have hδ₀0 : 0 < min (δ / 2) π := lt_min (by linarith) Real.pi_pos
  have hδ₀π : min (δ / 2) π ≤ π := min_le_right _ _
  have hbound : ∀ t ∈ Set.Ioc (0 : ℝ) (min (δ / 2) π),
      ‖(f (x + t) + f (x - t) - 2 * f x) / t‖ ≤ 1 := by
    intro t ht
    have hdist : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
      calc t ≤ min (δ / 2) π := ht.2
        _ ≤ δ / 2 := min_le_left _ _
        _ < δ := by linarith
    have h := hδ (by simpa using ne_of_gt ht.1) hdist
    rw [Real.dist_eq, sub_zero] at h
    exact h.le
  have hq1 : IntervalIntegrable (fun t => (f (x + t) + f (x - t) - 2 * f x) / t) volume 0
      (min (δ / 2) π) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hδ₀0.le]
    have hm := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδ₀0.le).mp
      (hφ 0 (min (δ / 2) π))).aestronglyMeasurable
    refine Integrable.mono' (integrable_const 1)
      (hm.aemeasurable.div aemeasurable_id).aestronglyMeasurable ?_
    exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hbound)
  have hq2 : IntervalIntegrable (fun t => (f (x + t) + f (x - t) - 2 * f x) / t) volume
      (min (δ / 2) π) π := by
    have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc (min (δ / 2) π) π) := by
      refine ContinuousOn.inv₀ continuousOn_id fun t ht => ?_
      rw [Set.uIcc_of_le hδ₀π] at ht
      exact ne_of_gt (lt_of_lt_of_le hδ₀0 ht.1)
    have heq : (fun t => (f (x + t) + f (x - t) - 2 * f x) / t)
        = fun t => (f (x + t) + f (x - t) - 2 * f x) * t⁻¹ :=
      funext fun t => div_eq_mul_inv _ _
    rw [heq]
    exact (hφ (min (δ / 2) π) π).mul_continuousOn hcont
  exact tendsto_fourierPartialSum_of_dini hf hfi (hq1.trans hq2)

end Dini
