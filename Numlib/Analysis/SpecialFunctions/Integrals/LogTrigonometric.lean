/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Integrability.Log
import Mathlib.Analysis.SpecialFunctions.Integrals.Log
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Integrals of $\log|\sin x|$ and of $\log|\cos x - \cos y|$

Mathlib's `integral_log_sin_zero_pi` computes $\int_0^\pi \log(\sin x)\,dx = -\pi \log 2$. This file
proves that $\log|\sin|$ is integrable on every interval and, since it has period $\pi$, that its
integral over every interval of length $\pi$ is $-\pi \log 2$. As a consequence, the row integral of
the logarithmic kernel is constant:
$$\int_0^\pi \log|\cos x - \cos y|\,dy = -\pi \log 2 \qquad \text{for every } x \in \mathbb{R}.$$
This is the reason why the integral equation $u(x) - \int_0^\pi u(y) \log|\cos x - \cos y|\,dy =
f(x)$ with a constant $f$ has a constant solution ([han2009theoretical], Example 12.5.3).

## Main results

* `intervalIntegrable_log_abs_sin`: $\log|\sin|$ is integrable on every interval.
* `periodic_log_abs_sin`: $\log|\sin|$ has period $\pi$.
* `integral_log_abs_sin_add_pi`: $\int_a^{a+\pi} \log|\sin u|\,du = -\pi \log 2$ for every $a$.
* `integral_log_abs_cos_sub_cos`: $\int_0^\pi \log|\cos x - \cos y|\,dy = -\pi \log 2$ for every
  $x$.
-/

open MeasureTheory Set

open scoped Interval Real

/-- For all $a, b \in \mathbb{R}$, the function $u \mapsto \log|\sin u|$ is integrable on the
interval between $a$ and $b$.

By `Real.log_abs` the function equals $\log \circ \sin$, with the Lean convention
$\log x = \log|x|$. -/
theorem intervalIntegrable_log_abs_sin (a b : ℝ) :
    IntervalIntegrable (fun u => Real.log |Real.sin u|) volume a b := by
  simpa [Function.comp_def, Real.log_abs] using (intervalIntegrable_log_sin (a := a) (b := b))

/-- The function $u \mapsto \log|\sin u|$ has period $\pi$. -/
theorem periodic_log_abs_sin :
    Function.Periodic (fun u => Real.log |Real.sin u|) π := by
  intro u
  simp only
  rw [Real.sin_add_pi, abs_neg]

/-- For every $a \in \mathbb{R}$,
$$\int_a^{a+\pi} \log|\sin u|\,du = -\pi \log 2.$$

By periodicity the integral equals the integral over $[0, \pi]$, where $|\sin| = \sin$. -/
theorem integral_log_abs_sin_add_pi (a : ℝ) :
    (∫ u in a..(a + π), Real.log |Real.sin u|) = -(π * Real.log 2) := by
  rw [periodic_log_abs_sin.intervalIntegral_add_eq a 0, zero_add]
  have h : (∫ u in (0 : ℝ)..π, Real.log |Real.sin u|)
      = ∫ u in (0 : ℝ)..π, Real.log (Real.sin u) :=
    intervalIntegral.integral_congr fun u _ => by rw [Real.log_abs]
  rw [h, integral_log_sin_zero_pi]
  ring

/-- For $x, c \in \mathbb{R}$, the function $y \mapsto \sin((x + cy)/2)$ is analytic on every set,
so the logarithm of its absolute value is integrable. -/
private theorem analytic_sin_shift (x c : ℝ) (s : Set ℝ) :
    AnalyticOnNhd ℝ (fun y : ℝ => Real.sin ((x + c * y) / 2)) s := by
  refine Real.analyticOnNhd_sin.comp ?_ (Set.mapsTo_univ _ _)
  exact (analyticOnNhd_const.add (analyticOnNhd_const.mul analyticOnNhd_id)).div_const

private theorem intervalIntegrable_log_abs_sin_shift (x c a b : ℝ) :
    IntervalIntegrable (fun y : ℝ => Real.log |Real.sin ((x + c * y) / 2)|) volume a b := by
  have h : MeromorphicOn (fun y : ℝ => Real.sin ((x + c * y) / 2)) [[a, b]] :=
    (analytic_sin_shift x c _).meromorphicOn
  simpa [Real.norm_eq_abs] using h.intervalIntegrable_log_norm

/-- The **row integral of the logarithmic kernel** $\log|\cos x - \cos y|$ is constant: for every
$x \in \mathbb{R}$,
$$\int_0^\pi \log|\cos x - \cos y|\,dy = -\pi \log 2.$$
This is the kernel of (12.5.21) in Example 12.5.3 of [han2009theoretical].

Since $\cos x - \cos y = -2 \sin((x + y)/2) \sin((x - y)/2)$, the integrand equals $\log 2 +
\log|\sin((x + y)/2)| + \log|\sin((x - y)/2)|$ except at the finitely many points of $[0, \pi]$
where a factor vanishes. The substitutions $u = (x \pm y)/2$ turn the last two integrals into
$2 \int \log|\sin|$ over the two halves of an interval of length $\pi$ centred at $x/2$. Since
$\log|\sin|$ has period $\pi$ and $\int_0^\pi \log(\sin u)\,du = -\pi \log 2$, the total is
$\pi \log 2 - 2\pi \log 2 = -\pi \log 2$. -/
theorem integral_log_abs_cos_sub_cos (x : ℝ) :
    (∫ y in (0 : ℝ)..π, Real.log |Real.cos x - Real.cos y|) = -(π * Real.log 2) := by
  set S : Set ℝ := {y | Real.sin ((x + y) / 2) = 0} ∪ {y | Real.sin ((x - y) / 2) = 0} with hS
  have hcount : S.Countable := by
    refine Set.Countable.union ?_ ?_
    · refine Set.Countable.mono (s₂ := Set.range fun n : ℤ => 2 * (n : ℝ) * π - x) ?_
        (Set.countable_range _)
      intro y hy
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hy
      exact ⟨n, by linarith⟩
    · refine Set.Countable.mono (s₂ := Set.range fun n : ℤ => x - 2 * (n : ℝ) * π) ?_
        (Set.countable_range _)
      intro y hy
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hy
      exact ⟨n, by linarith⟩
  have hae : ∀ᵐ y : ℝ, y ∉ S := by
    rw [MeasureTheory.ae_iff]
    simpa using hcount.measure_zero volume
  have hsplit : (∫ y in (0 : ℝ)..π, Real.log |Real.cos x - Real.cos y|)
      = ∫ y in (0 : ℝ)..π, (Real.log 2 + Real.log |Real.sin ((x + 1 * y) / 2)|
          + Real.log |Real.sin ((x + (-1) * y) / 2)|) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with y hy _
    have h1 : Real.sin ((x + y) / 2) ≠ 0 := fun h => hy (Or.inl h)
    have h2 : Real.sin ((x - y) / 2) ≠ 0 := fun h => hy (Or.inr h)
    rw [Real.cos_sub_cos, one_mul, show x + -1 * y = x - y by ring,
      show -2 * Real.sin ((x + y) / 2) * Real.sin ((x - y) / 2)
        = -(2 * (Real.sin ((x + y) / 2) * Real.sin ((x - y) / 2))) by ring,
      abs_neg, abs_mul, abs_mul, Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (abs_ne_zero.2 h1) (abs_ne_zero.2 h2)]
    simp only [Real.log_abs]
    ring
  rw [hsplit, intervalIntegral.integral_add
      ((intervalIntegrable_const).add (intervalIntegrable_log_abs_sin_shift x 1 0 π))
      (intervalIntegrable_log_abs_sin_shift x (-1) 0 π),
    intervalIntegral.integral_add intervalIntegrable_const
      (intervalIntegrable_log_abs_sin_shift x 1 0 π)]
  have hA : (∫ y in (0 : ℝ)..π, Real.log |Real.sin ((x + 1 * y) / 2)|)
      = 2 * ∫ u in (x / 2)..(x / 2 + π / 2), Real.log |Real.sin u| := by
    have h := intervalIntegral.integral_comp_mul_add
      (a := (0 : ℝ)) (b := π) (c := (1 : ℝ) / 2) (d := x / 2)
      (fun u : ℝ => Real.log |Real.sin u|) (by norm_num)
    rw [show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num, show (1 : ℝ) / 2 * 0 + x / 2 = x / 2 by ring,
      show (1 : ℝ) / 2 * π + x / 2 = x / 2 + π / 2 by ring, smul_eq_mul] at h
    rw [← h]
    exact intervalIntegral.integral_congr fun y _ => by
      rw [show (x + 1 * y) / 2 = 1 / 2 * y + x / 2 by ring]
  have hB : (∫ y in (0 : ℝ)..π, Real.log |Real.sin ((x + (-1) * y) / 2)|)
      = 2 * ∫ u in (x / 2 - π / 2)..(x / 2), Real.log |Real.sin u| := by
    have h := intervalIntegral.integral_comp_mul_add
      (a := (0 : ℝ)) (b := π) (c := -((1 : ℝ) / 2)) (d := x / 2)
      (fun u : ℝ => Real.log |Real.sin u|) (by norm_num)
    rw [show (-((1 : ℝ) / 2))⁻¹ = -2 by norm_num,
      show -((1 : ℝ) / 2) * 0 + x / 2 = x / 2 by ring,
      show -((1 : ℝ) / 2) * π + x / 2 = x / 2 - π / 2 by ring, smul_eq_mul] at h
    have h2 : (∫ y in (0 : ℝ)..π, Real.log |Real.sin ((x + (-1) * y) / 2)|)
        = -2 * ∫ u in (x / 2)..(x / 2 - π / 2), Real.log |Real.sin u| := by
      rw [← h]
      exact intervalIntegral.integral_congr fun y _ => by
        rw [show (x + (-1) * y) / 2 = -(1 / 2) * y + x / 2 by ring]
    rw [h2, intervalIntegral.integral_symm (x / 2 - π / 2) (x / 2)]
    ring
  rw [hA, hB]
  have hglue : (∫ u in (x / 2 - π / 2)..(x / 2), Real.log |Real.sin u|)
      + ∫ u in (x / 2)..(x / 2 + π / 2), Real.log |Real.sin u|
      = ∫ u in (x / 2 - π / 2)..(x / 2 - π / 2 + π), Real.log |Real.sin u| := by
    rw [show x / 2 - π / 2 + π = x / 2 + π / 2 by ring]
    exact intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_log_abs_sin _ _) (intervalIntegrable_log_abs_sin _ _)
  have hval := integral_log_abs_sin_add_pi (x / 2 - π / 2)
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  linarith [hglue, hval]
