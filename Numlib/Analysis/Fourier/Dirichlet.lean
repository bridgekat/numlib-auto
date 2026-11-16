/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
import Numlib.Analysis.SpecialFunctions.Trigonometric.CosSum
import Numlib.MeasureTheory.Integral.IntervalIntegral

/-!
# The Dirichlet kernel and pointwise convergence of Fourier series

Let $f : \mathbb{R} \to \mathbb{R}$ be $2\pi$-periodic and integrable over one period. Its real
Fourier coefficients are
$$a_j = \frac{1}{\pi} \int_{-\pi}^{\pi} f(t) \cos(jt) \, dt, \qquad b_j = \frac{1}{\pi}
  \int_{-\pi}^{\pi} f(t) \sin(jt) \, dt,$$
and its partial sums are $S_n f(x) = a_0/2 + \sum_{j=1}^n (a_j \cos(jx) + b_j \sin(jx))$. This file
defines the Dirichlet kernel $D_n(t) = 1/2 + \sum_{j=1}^n \cos(jt)$, proves its closed form
$D_n(t) = \sin((n + 1/2)t)/(2 \sin(t/2))$, and proves the kernel representation
$$S_n f(x) = \frac{1}{\pi} \int_{-\pi}^{\pi} f(x + t) D_n(t) \, dt.$$
It then proves Dini's criterion for pointwise convergence: if
$t \mapsto (f(x + t) + f(x - t) - 2L)/t$ is integrable on $[0, \pi]$, then $S_n f(x) \to L$. In
particular $S_n f(x) \to f(x)$ at every point where $f$ is differentiable. The kernel is
(3.7.6)–(3.7.8) of [han2009theoretical], and the partial sums are (4.1.1)–(4.1.3) there. Theorem
4.1.1 of [han2009theoretical] states the convergence to the mean $(f(x-) + f(x+))/2$ of the
one-sided limits at a point where the two one-sided derivatives exist. It is Dini's criterion
`tendsto_fourierPartialSum_of_dini` applied to that mean, and
`tendsto_fourierPartialSum_of_hasDerivAt` is its corollary at a point of differentiability.

## Main definitions

* `dirichletKernel`: the Dirichlet kernel $D_n(t) = 1/2 + \sum_{j=1}^n \cos(jt)$, the kernel of the
  operator $f \mapsto S_n f$.
* `fourierCoeffCos` and `fourierCoeffSin`: the real Fourier coefficients $a_j$ and $b_j$.
* `fourierPartialSum`: the partial sum $S_n f(x) = a_0/2 + \sum_{j=1}^n (a_j \cos(jx) + b_j
  \sin(jx))$ of the real Fourier series.

## Main results

* `dirichletKernel_eq_sin_div`: $D_n(t) = \sin((n + 1/2)t)/(2 \sin(t/2))$ where $\sin(t/2) \ne 0$.
* `fourierPartialSum_eq_integral`: $S_n f(x) = \pi^{-1} \int_{-\pi}^{\pi} f(x + t) D_n(t) \, dt$.
* `tendsto_intervalIntegral_mul_sin`: the Riemann–Lebesgue lemma on an interval.
* `tendsto_fourierPartialSum_of_dini`: **Dini's criterion**, $S_n f(x) \to L$ if
  $t \mapsto (f(x + t) + f(x - t) - 2L)/t$ is integrable on $[0, \pi]$.
* `tendsto_fourierPartialSum_of_hasDerivAt`: $S_n f(x) \to f(x)$ at a point where $f$ is
  differentiable.

## Proof outline

The proof of Dini's criterion is the classical one. The difference $S_n f(x) - L$ is $\pi^{-1}
\int_0^\pi g(t) \sin((n + 1/2)t) \, dt$ with $g(t) = (f(x + t) + f(x - t) - 2L)/(2 \sin(t/2))$. The
function $g$ is integrable under the hypothesis of Dini, because $2 \sin(t/2) \ge 2t/\pi$ on
$[0, \pi]$. The Riemann–Lebesgue lemma then gives the limit $0$.

## Implementation notes

* Mathlib has the $L^2$ theory of Fourier series on the circle and the uniform convergence of an
  absolutely summable Fourier series, but no Dirichlet kernel and no criterion for pointwise
  convergence.
* Everything is stated for a function on $\mathbb{R}$, not on `AddCircle (2 * π)`, because the
  hypotheses of a theorem on pointwise convergence are about one-sided limits at a real point.
* Mathlib states the Riemann–Lebesgue lemma for the Fourier integral over $\mathbb{R}$
  (`Real.tendsto_integral_exp_smul_cocompact`). The form needed here,
  $\int_a^b g(t) \sin(rt) \, dt \to 0$ as $r \to \infty$, is `tendsto_intervalIntegral_mul_sin`,
  which extends $g$ by zero.
-/

open MeasureTheory Filter Topology

open scoped Real FourierTransform

/-! ### The Dirichlet kernel -/

/-- The **Dirichlet kernel** of order $n$:
$$D_n(t) = \frac{1}{2} + \sum_{j=1}^n \cos(jt).$$
It is the kernel of the operator that maps a $2\pi$-periodic function to the $n$-th partial sum
of its Fourier series. -/
noncomputable def dirichletKernel (n : ℕ) (t : ℝ) : ℝ :=
  1 / 2 + ∑ j ∈ Finset.Icc 1 n, Real.cos (j * t)

/-- The defining formula of the Dirichlet kernel: $D_n(t) = 1/2 + \sum_{j=1}^n \cos(jt)$. -/
theorem dirichletKernel_apply (n : ℕ) (t : ℝ) :
    dirichletKernel n t = 1 / 2 + ∑ j ∈ Finset.Icc 1 n, Real.cos (j * t) :=
  rfl

/-- The Dirichlet kernel of order $0$ is the constant $1/2$. -/
@[simp]
theorem dirichletKernel_zero (t : ℝ) : dirichletKernel 0 t = 1 / 2 := by
  simp [dirichletKernel_apply]

/-- The recursion of the Dirichlet kernel: $D_{n+1}(t) = D_n(t) + \cos((n + 1)t)$. -/
theorem dirichletKernel_succ (n : ℕ) (t : ℝ) :
    dirichletKernel (n + 1) t = dirichletKernel n t + Real.cos ((n + 1) * t) := by
  rw [dirichletKernel_apply, dirichletKernel_apply, Finset.sum_Icc_succ_top (by omega),
    ← add_assoc]
  norm_num

/-- The Dirichlet kernel is even: $D_n(-t) = D_n(t)$. -/
@[simp]
theorem dirichletKernel_neg (n : ℕ) (t : ℝ) : dirichletKernel n (-t) = dirichletKernel n t := by
  simp [dirichletKernel_apply, mul_neg]

/-- The Dirichlet kernel is $2\pi$-periodic. -/
theorem dirichletKernel_periodic (n : ℕ) : Function.Periodic (dirichletKernel n) (2 * π) := by
  intro t
  simp only [dirichletKernel_apply]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [mul_add]
  simp

/-- The Dirichlet kernel is continuous. -/
@[fun_prop]
theorem continuous_dirichletKernel (n : ℕ) : Continuous (dirichletKernel n) := by
  have h : dirichletKernel n = fun t => 1 / 2 + ∑ j ∈ Finset.Icc 1 n, Real.cos (j * t) := rfl
  rw [h]
  fun_prop

/-- The Dirichlet kernel is bounded by its value at the origin: $|D_n(t)| \le n + 1/2$ for every
$t$, because $D_n$ is a sum of $n$ cosines and $1/2$. -/
theorem abs_dirichletKernel_le (n : ℕ) (t : ℝ) : |dirichletKernel n t| ≤ (n : ℝ) + 1 / 2 := by
  rw [dirichletKernel_apply]
  refine (abs_add_le _ _).trans ?_
  have h2 : |∑ j ∈ Finset.Icc 1 n, Real.cos (j * t)| ≤ (n : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Finset.Icc 1 n, |Real.cos (j * t)|
        ≤ ∑ _j ∈ Finset.Icc 1 n, (1 : ℝ) := Finset.sum_le_sum fun j _ => Real.abs_cos_le_one _
      _ = (n : ℝ) := by simp
  linarith

/-- For every $n$ and $t$,
$$2 \sin(t/2) \, D_n(t) = \sin((n + 1/2)t).$$
This is a telescoping identity, Lagrange's trigonometric identity
`Real.two_mul_sin_half_mul_sum_range_cos`, and it gives the closed form of the Dirichlet kernel. -/
theorem two_mul_sin_half_mul_dirichletKernel (n : ℕ) (t : ℝ) :
    2 * Real.sin (t / 2) * dirichletKernel n t = Real.sin ((n + 1 / 2) * t) := by
  have hs : ∑ j ∈ Finset.Icc 1 n, Real.cos (j * t) =
      ∑ k ∈ Finset.range n, Real.cos ((k + 1) * t) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun k _ => by push_cast; ring_nf
  rw [dirichletKernel_apply, hs, mul_add, Real.two_mul_sin_half_mul_sum_range_cos,
    show ((n : ℝ) + 1 / 2) * t = (2 * n + 1) * (t / 2) by ring]
  ring

/-- The **closed form of the Dirichlet kernel** ((3.7.8) of [han2009theoretical]). For
$t \in \mathbb{R}$ with $\sin(t/2) \ne 0$,
$$D_n(t) = \frac{\sin((n + 1/2)t)}{2 \sin(t/2)}.$$

The hypothesis $\sin(t/2) \ne 0$ says exactly that $t$ is not an integer multiple of $2\pi$. -/
theorem dirichletKernel_eq_sin_div {n : ℕ} {t : ℝ} (ht : Real.sin (t / 2) ≠ 0) :
    dirichletKernel n t = Real.sin ((n + 1 / 2) * t) / (2 * Real.sin (t / 2)) := by
  rw [← two_mul_sin_half_mul_dirichletKernel n t]
  field_simp

/-- The Dirichlet kernel has mean $1/2$ over half a period (Exercise 4.1.4(b) of
[han2009theoretical]): for every $n$,
$$\frac{1}{\pi} \int_0^\pi D_n(t) \, dt = \frac{1}{2}.$$
-/
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

/-- The Dirichlet kernel has mean $1/2$ over the other half period:
$\pi^{-1} \int_{-\pi}^0 D_n(t) \, dt = 1/2$. This follows from the evenness of $D_n$. -/
theorem integral_dirichletKernel_neg (n : ℕ) :
    (1 / π) * ∫ t in -π..(0 : ℝ), dirichletKernel n t = 1 / 2 := by
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π) (dirichletKernel n)
  simp only [dirichletKernel_neg, neg_zero] at h
  rw [← h, integral_dirichletKernel]

/-- The Dirichlet kernel has mean $1$ over a full period:
$\pi^{-1} \int_{-\pi}^{\pi} D_n(t) \, dt = 1$. -/
theorem integral_dirichletKernel_neg_pi_pi (n : ℕ) :
    (1 / π) * ∫ t in -π..π, dirichletKernel n t = 1 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ))
      ((continuous_dirichletKernel n).intervalIntegrable _ _)
      ((continuous_dirichletKernel n).intervalIntegrable _ _),
    mul_add, integral_dirichletKernel_neg, integral_dirichletKernel]
  norm_num

/-! ### The partial sums of a Fourier series -/

/-- The **cosine coefficient** of the Fourier series of a $2\pi$-periodic function
$f : \mathbb{R} \to \mathbb{R}$ ((4.1.2) of [han2009theoretical]):
$$a_j = \frac{1}{\pi} \int_{-\pi}^{\pi} f(t) \cos(jt) \, dt.$$
-/
noncomputable def fourierCoeffCos (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  (1 / π) * ∫ t in -π..π, f t * Real.cos (j * t)

/-- The **sine coefficient** of the Fourier series of a $2\pi$-periodic function
$f : \mathbb{R} \to \mathbb{R}$ ((4.1.3) of [han2009theoretical]):
$$b_j = \frac{1}{\pi} \int_{-\pi}^{\pi} f(t) \sin(jt) \, dt.$$
-/
noncomputable def fourierCoeffSin (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  (1 / π) * ∫ t in -π..π, f t * Real.sin (j * t)

/-- The **$n$-th partial sum** of the real Fourier series of a $2\pi$-periodic function
$f : \mathbb{R} \to \mathbb{R}$ ((4.1.1) of [han2009theoretical]):
$$S_n f(x) = \frac{a_0}{2} + \sum_{j=1}^n \bigl(a_j \cos(jx) + b_j \sin(jx)\bigr),$$
where $a_j$ and $b_j$ are the coefficients `fourierCoeffCos f j` and `fourierCoeffSin f j`. -/
noncomputable def fourierPartialSum (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  fourierCoeffCos f 0 / 2 + ∑ j ∈ Finset.Icc 1 n,
    (fourierCoeffCos f j * Real.cos (j * x) + fourierCoeffSin f j * Real.sin (j * x))

section Periodic

variable {f : ℝ → ℝ} (hf : Function.Periodic f (2 * π))
  (hfi : IntervalIntegrable f volume (-π) π)

include hf hfi

/-- A $2\pi$-periodic function $f : \mathbb{R} \to \mathbb{R}$ that is integrable on $[-\pi, \pi]$
is integrable on every bounded interval $[a, b]$. -/
theorem intervalIntegrable_of_periodic (a b : ℝ) : IntervalIntegrable f volume a b :=
  hf.intervalIntegrable (by positivity) (t := -π) (by rw [show -π + 2 * π = π by ring]; exact hfi)
    a b

omit hf hfi in
/-- The recursion of the partial sums: $S_{n+1} f(x) = S_n f(x) + a_{n+1} \cos((n + 1)x) + b_{n+1}
\sin((n + 1)x)$. -/
theorem fourierPartialSum_succ (n : ℕ) (x : ℝ) :
    fourierPartialSum f (n + 1) x = fourierPartialSum f n x
      + (fourierCoeffCos f (n + 1) * Real.cos ((n + 1 : ℕ) * x)
        + fourierCoeffSin f (n + 1) * Real.sin ((n + 1 : ℕ) * x)) := by
  simp only [fourierPartialSum]
  rw [Finset.sum_Icc_succ_top (by omega)]
  ring

/-- **The kernel representation of the partial sums** ((3.7.6) and Exercise 4.1.4 of
[han2009theoretical]). Let $f : \mathbb{R} \to \mathbb{R}$ be $2\pi$-periodic and integrable on
$[-\pi, \pi]$. For every $n$ and $x$,
$$S_n f(x) = \frac{1}{\pi} \int_{-\pi}^{\pi} f(x + t) D_n(t) \, dt.$$
So the $n$-th partial sum at $x$ is the mean of $f$ against the Dirichlet kernel centered at
$x$. -/
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
    have h := hper.intervalIntegral_add_eq (x + -π) (-π)
    rwa [show x + -π + 2 * π = x + π by ring, show -π + 2 * π = π by ring] at h
  rw [hshift, hstep]
  field_simp

end Periodic

/-! ### The Riemann–Lebesgue lemma over an interval -/

/-- The **Riemann–Lebesgue lemma** on an interval, in the form that the argument with the Dirichlet
kernel needs. Let $a \le b$, and let $g : \mathbb{R} \to \mathbb{R}$ be integrable on $[a, b]$.
Then
$$\int_a^b g(t) \sin(rt) \, dt \to 0 \qquad (r \to \infty).$$

The proof extends $g$ by zero outside $[a, b]$ and applies Mathlib's
`Real.tendsto_integral_exp_smul_cocompact`. -/
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

/-- **Dini's criterion** for the pointwise convergence of a Fourier series. Let
$f : \mathbb{R} \to \mathbb{R}$ be $2\pi$-periodic and integrable on $[-\pi, \pi]$, and let
$x, L \in \mathbb{R}$. If the function
$$t \mapsto \frac{f(x + t) + f(x - t) - 2L}{t}$$
is integrable on $[0, \pi]$, then the partial sums $S_n f(x)$ of the Fourier series of $f$
converge to $L$ as $n \to \infty$.

Each hypothesis under which Theorem 4.1.1 of [han2009theoretical] asserts convergence implies
the hypothesis of Dini: the existence of the one-sided derivatives, Hölder continuity at $x$,
and differentiability at $x$. -/
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
    rw [intervalIntegral.integral_fold_neg (hI (-π) 0) (hI 0 π)]
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

/-- **Pointwise convergence at a point of differentiability.** Let $f : \mathbb{R} \to \mathbb{R}$
be $2\pi$-periodic and integrable on $[-\pi, \pi]$. If $f$ is differentiable at $x$, then the
partial sums $S_n f(x)$ of the Fourier series of $f$ converge to $f(x)$.

This is the corollary of Theorem 4.1.1 of [han2009theoretical] at a point of differentiability.
The theorem itself asks only for the two one-sided derivatives, and concludes that $S_n f(x)$
converges to $(f(x-) + f(x+))/2$; this is `tendsto_fourierPartialSum_of_dini` applied to that
mean. The derivative at $x$ is given as `HasDerivAt f c x` for some $c$. -/
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
