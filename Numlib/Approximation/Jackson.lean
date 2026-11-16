/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Analysis.Fourier.TrigonometricPolynomial
import Numlib.Analysis.MeanInequalities
import Numlib.Approximation.Chebyshev

/-!
# Jackson's theorem through the Fejér–Korovkin kernel

**Jackson's theorem** bounds the error of the best uniform approximation of a smooth $2\pi$-periodic
function by trigonometric polynomials of degree at most $n$. Write $\mathcal{T}_n$ for the space of
these trigonometric polynomials, $\rho_n(g) = \operatorname{dist}(g, \mathcal{T}_n)$ for the error
of best uniform approximation, $\theta_n = \pi/(n + 2)$, and $A_n = \pi \sin(\theta_n / 2) = \pi
\sin(\pi/(2n + 4))$. This file builds the Fejér–Korovkin kernel and proves the theorem first for a
Hölder continuous function,
$$\rho_n(g) \le M A_n^\alpha \le \frac{M (\pi^2/2)^\alpha}{n^\alpha} \qquad \text{when } |g(u) -
  g(v)| \le M |u - v|^\alpha,$$
and then, for a function with $k$ continuous derivatives whose $k$-th derivative is $\alpha$-Hölder
with constant $M$, in the classical form $\rho_n(g) \le (1 + \pi^2/2)^{k+1} M / n^{k+\alpha}$ for
$n \ge 1$. Through the substitution $x = \cos\theta$, the Hölder bound holds unchanged for the best
approximation on $[-1, 1]$ by algebraic polynomials of degree at most $n$; the bound for $k$
derivatives holds for $n > k$, with an extra factor $d$ that compensates the lower degrees $n - i$
along the recursion. Theorems 3.7.1 and 3.7.2 of [han2009theoretical] state these results with the
constant $(1 + \pi^2/2)^{k+1}$ and refer to [meinardus1967approximation] for the proof.

The kernel is $K_n(r) = |\sum_{k \le n} c_k e^{ikr}|^2$ with
$c_k = \sqrt{2/(n + 2)} \sin((k + 1)\theta_n)$. It is nonnegative, it has total mass $2\pi$ over a
period, and its first cosine coefficient is $\cos\theta_n$, the largest that such a kernel of degree
$n$ can have. This makes its second moment as small as $2\pi A_n^2$, and hence its first absolute
moment at most $2\pi A_n$; this moment is exactly the error constant. The Fejér kernel and its
powers give a worse constant.

## Main definitions

* `Jackson.angle`: the angle $\theta_n = \pi/(n + 2)$.
* `Jackson.coeff`: the coefficients $c_k = \sqrt{2/(n + 2)} \sin((k + 1)\theta_n)$.
* `Jackson.kernel`: the Fejér–Korovkin kernel $K_n(r) = |\sum_{k \le n} c_k e^{ikr}|^2$.
* `Jackson.approx`: the Fejér–Korovkin approximation $L_n g(x) = (2\pi)^{-1} \int_{-\pi}^{\pi}
  K_n(r)\, g(x - r)\, dr$, a trigonometric polynomial of degree at most $n$.
* `Jackson.rem`: the remainder $R_n g = g - L_n g$.
* `Jackson.cosCM`, `Jackson.sinCM`: the functions $x \mapsto \cos(mx)$ and $x \mapsto \sin(mx)$ on
  the circle of circumference $2\pi$.

## Main results

* `Jackson.integral_kernel`, `Jackson.integral_cos_mul_kernel`: the kernel has mass $2\pi$ and first
  cosine coefficient $\cos\theta_n$.
* `Jackson.integral_sq_mul_kernel_le`, `Jackson.integral_abs_mul_kernel_le`: the second moment of
  the kernel is at most $2\pi A_n^2$, and the first absolute moment is at most $2\pi A_n$.
* `Jackson.abs_sub_approx_le_of_holder`, `Jackson.infDist_le_of_holder`: Jackson's theorem for a
  Hölder function, pointwise and as a bound on $\rho_n$. This is the case $k = 0$.
* `Jackson.hasDerivAt_approx`: the Fejér–Korovkin operator commutes with differentiation.
* `Jackson.abs_iterate_rem_le`: each application of the remainder to a derivative costs one factor
  $A_n$.
* `Jackson.infDist_le_of_holder_deriv`: Jackson's theorem with the constant $A_n^{k+\alpha} M$.
* `Jackson.infDist_le_of_holder_deriv'`: Jackson's theorem in the classical form $\rho_n(g) \le (1 +
  \pi^2/2)^{k+1} M / n^{k+\alpha}$.
* `Jackson.exists_degree_le_eval_cos`: the even part of a trigonometric polynomial of degree at most
  $n$ is $P(\cos\theta)$ for an algebraic polynomial $P$ of degree at most $n$.
* `Jackson.infDist_polyLE_le_infDist_trigPolyLE`: the best algebraic approximation on $[-1, 1]$ is
  at least as good as the best trigonometric approximation of the pullback along $\cos$.
* `Jackson.infDist_polyLE_le_of_holder`, `Jackson.infDist_le_of_holder_poly`: Jackson's theorem for
  algebraic polynomials, in the Hölder case and in the $C^{k,\alpha}$ case.

## Proof outline

The mass and the first cosine coefficient of the kernel come from the sums $\sum_k c_k^2 = 1$ and
$\sum_k c_k c_{k+1} = \cos\theta_n$, which are telescoping trigonometric sums at the angle
$\theta_n$. Jordan's inequality gives $r^2 \le \pi^2 (1 - \cos r)/2$ on a period, which bounds the
second moment, and the first absolute moment follows from $|r| \le r^2/(2s) + s/2$, a Cauchy–Schwarz
step done by hand. For a Hölder function, the error $g - L_n g$ is a kernel average of the
increments of $g$, and a tangent-line bound for the concave function $r \mapsto r^\alpha$ reduces it
to the first absolute moment, which gives $M A_n^\alpha$. For a smooth function, the operator
commutes with differentiation (integration by parts on each Fourier coefficient), so the iterates of
the remainder $R_n$ can be estimated one derivative at a time; each iterate removes a trigonometric
polynomial of degree at most $n$ and costs one factor $A_n$. On $[-1, 1]$, the antiderivative of a
polynomial of degree at most $n$ is a polynomial of degree at most $n + 1$, and the recursion
$\rho_{n+1}(u) \le A_{n+1} \rho_n(u')$ goes down the tower of derivatives.

## Implementation notes

* The kernel is written as the sum of the squares of the real and the imaginary parts of
  $\sum_k c_k e^{ikr}$, so that its nonnegativity is immediate. `Jackson.kernel_eq_sum` expands it
  as $\sum_{k, l} c_k c_l \cos((k - l) r)$, which gives the moments and the degree.
* The approximation `Jackson.approx` is written out in the real trigonometric system `trigFun`, so
  that it is a trigonometric polynomial of degree at most $n$ by construction. `Jackson.approx_coe`
  identifies it with the convolution.
* The derivatives are given as a tower `D 0 = g`, `D (j + 1) = (D j)'` and not as `iteratedDeriv`. A
  caller that already has the derivatives, or that produces them from `ContDiff`, can use either
  form.
* The Hölder exponent $\alpha$ may be $0$; the results hold for $0 \le \alpha \le 1$.
* The algebraic case is proved with the constant $(\pi^2/2)^{k+1}$ times a factor $d$ that
  compensates the degrees $n - i$ along the recursion; see `Jackson.infDist_le_of_holder_poly`.
-/

open Finset MeasureTheory Real

open scoped Real

namespace Jackson

/-! ### The angle $\theta = \pi/(n + 2)$ -/

/-- The angle $\theta_n = \pi/(n + 2)$ at which the Fejér–Korovkin kernel of degree $n$ is built. -/
noncomputable def angle (n : ℕ) : ℝ := π / (n + 2)

/-- The angle is positive: $\theta_n > 0$. -/
theorem angle_pos (n : ℕ) : 0 < angle n := by
  rw [angle]
  positivity

/-- The angle is less than $\pi$: $\theta_n < \pi$. -/
theorem angle_lt_pi (n : ℕ) : angle n < π := by
  rw [angle, div_lt_iff₀ (by positivity)]
  nlinarith [pi_pos, Nat.cast_nonneg (α := ℝ) n]

/-- The sine of the angle is positive: $\sin\theta_n > 0$. -/
theorem sin_angle_pos (n : ℕ) : 0 < Real.sin (angle n) :=
  Real.sin_pos_of_pos_of_lt_pi (angle_pos n) (angle_lt_pi n)

/-- The defining property of the angle: $(n + 2)\, \theta_n = \pi$. -/
theorem cast_mul_angle (n : ℕ) : ((n : ℝ) + 2) * angle n = π := by
  rw [angle]
  field_simp

/-! ### Two trigonometric sums at that angle -/

/-- At $\theta = \theta_n = \pi/(n + 2)$,
$$\sum_{j=0}^{n} \cos((2j + 1)\theta) = -\cos\theta.$$
The sum telescopes against $2 \sin\theta$ to $\sin((2n + 2)\theta) = \sin(2\pi - 2\theta) =
-\sin(2\theta)$. -/
theorem sum_cos_odd_angle (n : ℕ) :
    ∑ j ∈ range (n + 1), Real.cos ((2 * (j : ℝ) + 1) * angle n) = -Real.cos (angle n) := by
  have hs : Real.sin (angle n) ≠ 0 := (sin_angle_pos n).ne'
  set θ := angle n with hθ
  have key : ∀ j : ℕ, 2 * Real.sin θ * Real.cos ((2 * (j : ℝ) + 1) * θ)
      = Real.sin (2 * ((j : ℝ) + 1) * θ) - Real.sin (2 * (j : ℝ) * θ) := by
    intro j
    have h1 : 2 * ((j : ℝ) + 1) * θ = (2 * (j : ℝ) + 1) * θ + θ := by ring
    have h2 : 2 * (j : ℝ) * θ = (2 * (j : ℝ) + 1) * θ - θ := by ring
    rw [h1, h2, Real.sin_add, Real.sin_sub]
    ring
  have htel : ∑ j ∈ range (n + 1),
      (Real.sin (2 * ((j : ℝ) + 1) * θ) - Real.sin (2 * (j : ℝ) * θ))
      = Real.sin (2 * ((n : ℝ) + 1) * θ) - Real.sin (2 * (0 : ℝ) * θ) := by
    have h := Finset.sum_range_sub (fun j : ℕ => Real.sin (2 * (j : ℝ) * θ)) (n + 1)
    simpa using h
  have hend : Real.sin (2 * ((n : ℝ) + 1) * θ) = -Real.sin (2 * θ) := by
    have h : 2 * ((n : ℝ) + 1) * θ = 2 * π - 2 * θ := by
      rw [← cast_mul_angle n, ← hθ]; ring
    rw [h, Real.sin_sub]
    simp
  have hsum : 2 * Real.sin θ * ∑ j ∈ range (n + 1), Real.cos ((2 * (j : ℝ) + 1) * θ)
      = -(2 * Real.sin θ * Real.cos θ) := by
    rw [Finset.mul_sum]
    simp only [key]
    rw [htel, hend, Real.sin_two_mul]
    simp
  have h2 : (2 : ℝ) * Real.sin θ ≠ 0 := mul_ne_zero two_ne_zero hs
  refine mul_left_cancel₀ h2 ?_
  rw [hsum]
  ring

/-- At $\theta = \theta_n = \pi/(n + 2)$,
$$\sum_{j=1}^{n+1} \cos(2j\theta) = -1.$$
The sum telescopes against $2 \sin\theta$ to $\sin((2n + 3)\theta) - \sin\theta = -2
\sin\theta$. -/
theorem sum_cos_even_angle (n : ℕ) :
    ∑ j ∈ range (n + 1), Real.cos (2 * ((j : ℝ) + 1) * angle n) = -1 := by
  have hs : Real.sin (angle n) ≠ 0 := (sin_angle_pos n).ne'
  set θ := angle n with hθ
  have key : ∀ j : ℕ, 2 * Real.sin θ * Real.cos (2 * ((j : ℝ) + 1) * θ)
      = Real.sin ((2 * ((j : ℝ) + 1) + 1) * θ) - Real.sin ((2 * (j : ℝ) + 1) * θ) := by
    intro j
    have h1 : (2 * ((j : ℝ) + 1) + 1) * θ = 2 * ((j : ℝ) + 1) * θ + θ := by ring
    have h2 : (2 * (j : ℝ) + 1) * θ = 2 * ((j : ℝ) + 1) * θ - θ := by ring
    rw [h1, h2, Real.sin_add, Real.sin_sub]
    ring
  have htel : ∑ j ∈ range (n + 1),
      (Real.sin ((2 * ((j : ℝ) + 1) + 1) * θ) - Real.sin ((2 * (j : ℝ) + 1) * θ))
      = Real.sin ((2 * ((n : ℝ) + 1) + 1) * θ) - Real.sin ((2 * (0 : ℝ) + 1) * θ) := by
    have h := Finset.sum_range_sub (fun j : ℕ => Real.sin ((2 * (j : ℝ) + 1) * θ)) (n + 1)
    simpa using h
  have hend : Real.sin ((2 * ((n : ℝ) + 1) + 1) * θ) = -Real.sin θ := by
    have h : (2 * ((n : ℝ) + 1) + 1) * θ = 2 * π - θ := by
      rw [← cast_mul_angle n, ← hθ]; ring
    rw [h, Real.sin_sub]
    simp
  have hsum : 2 * Real.sin θ * ∑ j ∈ range (n + 1), Real.cos (2 * ((j : ℝ) + 1) * θ)
      = 2 * Real.sin θ * (-1) := by
    rw [Finset.mul_sum]
    simp only [key]
    rw [htel, hend]
    simp
    ring
  exact mul_left_cancel₀ (mul_ne_zero two_ne_zero hs) hsum

/-- At $\theta = \theta_n = \pi/(n + 2)$, $\sum_{k=0}^{n} \sin^2((k + 1)\theta) = (n + 2)/2$. -/
theorem sum_sin_sq_angle (n : ℕ) :
    ∑ k ∈ range (n + 1), Real.sin (((k : ℝ) + 1) * angle n) ^ 2 = ((n : ℝ) + 2) / 2 := by
  set θ := angle n with hθ
  have hsq : ∀ y : ℝ, Real.sin y ^ 2 = (1 - Real.cos (2 * y)) / 2 := by
    intro y
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq y]
  have hcongr : ∀ k : ℕ, Real.sin (((k : ℝ) + 1) * θ) ^ 2
      = (1 - Real.cos (2 * ((k : ℝ) + 1) * θ)) / 2 := by
    intro k
    rw [hsq]
    ring_nf
  rw [Finset.sum_congr rfl fun k _ => hcongr k]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, sum_cos_even_angle n]
  simp
  ring

/-- At $\theta = \theta_n = \pi/(n + 2)$, $\sum_{k=0}^{n-1} \sin((k + 1)\theta) \sin((k +
2)\theta) = (n + 2) \cos\theta / 2$. -/
theorem sum_sin_mul_sin_angle (n : ℕ) :
    ∑ k ∈ range n, Real.sin (((k : ℝ) + 1) * angle n) * Real.sin (((k : ℝ) + 2) * angle n)
      = ((n : ℝ) + 2) * Real.cos (angle n) / 2 := by
  set θ := angle n with hθ
  have hprod : ∀ k : ℕ, Real.sin (((k : ℝ) + 1) * θ) * Real.sin (((k : ℝ) + 2) * θ)
      = (Real.cos θ - Real.cos ((2 * ((k : ℝ) + 1) + 1) * θ)) / 2 := by
    intro k
    have hc : Real.cos (((k : ℝ) + 2) * θ - ((k : ℝ) + 1) * θ)
        - Real.cos (((k : ℝ) + 2) * θ + ((k : ℝ) + 1) * θ)
        = 2 * (Real.sin (((k : ℝ) + 1) * θ) * Real.sin (((k : ℝ) + 2) * θ)) := by
      rw [Real.cos_sub, Real.cos_add]
      ring
    have h2 : ((k : ℝ) + 2) * θ - ((k : ℝ) + 1) * θ = θ := by ring
    have h3 : ((k : ℝ) + 2) * θ + ((k : ℝ) + 1) * θ = (2 * ((k : ℝ) + 1) + 1) * θ := by ring
    rw [h2, h3] at hc
    linarith
  have hshift : ∑ k ∈ range n, Real.cos ((2 * ((k : ℝ) + 1) + 1) * θ)
      = -2 * Real.cos θ := by
    have h := Finset.sum_range_succ' (fun j : ℕ => Real.cos ((2 * (j : ℝ) + 1) * θ)) n
    rw [sum_cos_odd_angle n] at h
    simp only [Nat.cast_add, Nat.cast_one] at h
    have h0 : Real.cos ((2 * ((0 : ℕ) : ℝ) + 1) * θ) = Real.cos θ := by norm_num
    rw [h0] at h
    linarith [h]
  rw [Finset.sum_congr rfl fun k _ => hprod k, ← Finset.sum_div, Finset.sum_sub_distrib, hshift]
  simp
  ring

/-! ### The coefficients of the Fejér–Korovkin kernel -/

/-- The $k$-th coefficient of the Fejér–Korovkin kernel of degree $n$:
$$c_k = \sqrt{\frac{2}{n + 2}}\, \sin\Bigl(\frac{(k + 1)\pi}{n + 2}\Bigr).$$

The normalization gives $\sum_{k \le n} c_k^2 = 1$ (`Jackson.sum_coeff_sq`). The choice gives
$\sum_{k < n} c_k c_{k+1} = \cos(\pi/(n + 2))$ (`Jackson.sum_coeff_mul_coeff_succ`), which is as
close to $1$ as a nonnegative trigonometric polynomial of degree $n$ allows. -/
noncomputable def coeff (n k : ℕ) : ℝ :=
  Real.sqrt (2 / ((n : ℝ) + 2)) * Real.sin (((k : ℝ) + 1) * angle n)

private theorem sq_sqrt_two_div (n : ℕ) :
    Real.sqrt (2 / ((n : ℝ) + 2)) ^ 2 = 2 / ((n : ℝ) + 2) :=
  Real.sq_sqrt (by positivity)

/-- The coefficients are normalized: $\sum_{k=0}^{n} c_k^2 = 1$. -/
theorem sum_coeff_sq (n : ℕ) : ∑ k ∈ range (n + 1), coeff n k ^ 2 = 1 := by
  have hn : ((n : ℝ) + 2) ≠ 0 := by positivity
  simp only [coeff, mul_pow, sq_sqrt_two_div]
  rw [← Finset.mul_sum, sum_sin_sq_angle n]
  field_simp

/-- The consecutive products of the coefficients sum to $\cos\theta_n$: $\sum_{k=0}^{n-1} c_k
c_{k+1} = \cos(\pi/(n + 2))$. -/
theorem sum_coeff_mul_coeff_succ (n : ℕ) :
    ∑ k ∈ range n, coeff n k * coeff n (k + 1) = Real.cos (angle n) := by
  have hn : ((n : ℝ) + 2) ≠ 0 := by positivity
  have hcongr : ∀ k : ℕ, coeff n k * coeff n (k + 1)
      = 2 / ((n : ℝ) + 2) *
        (Real.sin (((k : ℝ) + 1) * angle n) * Real.sin (((k : ℝ) + 2) * angle n)) := by
    intro k
    have hcast : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
    simp only [coeff, hcast]
    linear_combination (Real.sin (((k : ℝ) + 1) * angle n) *
      Real.sin (((k : ℝ) + 2) * angle n)) * sq_sqrt_two_div n
  rw [Finset.sum_congr rfl fun k _ => hcongr k, ← Finset.mul_sum, sum_sin_mul_sin_angle n]
  field_simp

/-! ### The kernel -/

/-- The **Fejér–Korovkin kernel** of degree $n$:
$$K_n(r) = \Bigl(\sum_{k=0}^{n} c_k \cos(kr)\Bigr)^2 + \Bigl(\sum_{k=0}^{n} c_k
  \sin(kr)\Bigr)^2 = \Bigl|\sum_{k=0}^{n} c_k e^{ikr}\Bigr|^2.$$

It is a nonnegative trigonometric polynomial of degree at most $n$ with
$(2\pi)^{-1} \int_{-\pi}^{\pi} K_n = 1$. Its first cosine coefficient $\cos(\pi/(n + 2))$ is the
largest that such a kernel can have, and this makes its second moment small. The definition uses
the sum of the squares of the real and the imaginary parts, so that the nonnegativity is
immediate. -/
noncomputable def kernel (n : ℕ) (r : ℝ) : ℝ :=
  (∑ k ∈ range (n + 1), coeff n k * Real.cos ((k : ℝ) * r)) ^ 2
    + (∑ k ∈ range (n + 1), coeff n k * Real.sin ((k : ℝ) * r)) ^ 2

/-- The Fejér–Korovkin kernel is nonnegative: $K_n(r) \ge 0$. -/
theorem kernel_nonneg (n : ℕ) (r : ℝ) : 0 ≤ kernel n r := by
  rw [kernel]
  positivity

/-- The Fejér–Korovkin kernel is a continuous function of $r$. -/
theorem continuous_kernel (n : ℕ) : Continuous (kernel n) := by
  have h : kernel n = fun r : ℝ =>
      (∑ k ∈ range (n + 1), coeff n k * Real.cos ((k : ℝ) * r)) ^ 2
        + (∑ k ∈ range (n + 1), coeff n k * Real.sin ((k : ℝ) * r)) ^ 2 := rfl
  rw [h]
  exact ((continuous_finsetSum _ fun k _ => continuous_const.mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).pow 2).add
    ((continuous_finsetSum _ fun k _ => continuous_const.mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).pow 2)

/-- The Fejér–Korovkin kernel as a double sum of cosines: for all real $r$,
$$K_n(r) = \sum_{k=0}^{n} \sum_{l=0}^{n} c_k c_l \cos((k - l) r).$$

This form gives the moments, and it shows that $K_n$ is a trigonometric polynomial of degree at
most $n$. -/
theorem kernel_eq_sum (n : ℕ) (r : ℝ) :
    kernel n r = ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1),
      coeff n k * coeff n l * Real.cos (((k : ℝ) - (l : ℝ)) * r) := by
  rw [kernel, pow_two, pow_two, Finset.sum_mul_sum, Finset.sum_mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show ((k : ℝ) - (l : ℝ)) * r = (k : ℝ) * r - (l : ℝ) * r by ring, Real.cos_sub]
  ring

/-! ### The moments of the kernel -/

private theorem integral_cos_intCast_mul_cos (m : ℤ) :
    (∫ r in -π..π, Real.cos ((m : ℝ) * r) * Real.cos r)
      = (if m + 1 = 0 then π else 0) + (if m - 1 = 0 then π else 0) := by
  have hsplit : ∀ r : ℝ, Real.cos ((m : ℝ) * r) * Real.cos r
      = (Real.cos (((m + 1 : ℤ) : ℝ) * r) + Real.cos (((m - 1 : ℤ) : ℝ) * r)) / 2 := by
    intro r
    have h1 : ((m + 1 : ℤ) : ℝ) * r = (m : ℝ) * r + r := by push_cast; ring
    have h2 : ((m - 1 : ℤ) : ℝ) * r = (m : ℝ) * r - r := by push_cast; ring
    rw [h1, h2, Real.cos_add, Real.cos_sub]
    ring
  have hi : ∀ j : ℤ, IntervalIntegrable (fun r : ℝ => Real.cos ((j : ℝ) * r)) volume (-π) π :=
    fun j => (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  simp only [hsplit]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hi (m + 1)) (hi (m - 1)),
    integral_cos_int_mul_neg_pi_pi (m + 1),
    integral_cos_int_mul_neg_pi_pi (m - 1)]
  split_ifs <;> ring

/-- The double sum $\sum_{k, l \le n} c_k c_l [l = k + 1]$ equals $\cos\theta_n$. -/
private theorem sum_sum_coeff_ite (n : ℕ) :
    ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1),
      coeff n k * coeff n l * (if l = k + 1 then (1 : ℝ) else 0) = Real.cos (angle n) := by
  have hinner : ∀ k : ℕ, (∑ l ∈ range (n + 1),
      coeff n k * coeff n l * (if l = k + 1 then (1 : ℝ) else 0))
      = if k + 1 ∈ range (n + 1) then coeff n k * coeff n (k + 1) else 0 := by
    intro k
    rw [← Finset.sum_ite_eq' (range (n + 1)) (k + 1) fun l => coeff n k * coeff n l]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun k _ => hinner k, Finset.sum_range_succ]
  rw [ite_eq_right (by simp), add_zero, ← sum_coeff_mul_coeff_succ n]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  rw [ite_eq_left (Finset.mem_range.2 (by omega : k + 1 < n + 1))]

/-- The Fejér–Korovkin kernel has mass $2\pi$ over a period:
$$\int_{-\pi}^{\pi} K_n(r)\, dr = 2\pi.$$
So $(2\pi)^{-1} K_n$ is a probability density on a period. -/
theorem integral_kernel (n : ℕ) : (∫ r in -π..π, kernel n r) = 2 * π := by
  have hcast : ∀ k l : ℕ, (((k : ℤ) - (l : ℤ) : ℤ) : ℝ) = (k : ℝ) - (l : ℝ) := by
    intro k l; push_cast; ring
  have hint : ∀ k l : ℕ, IntervalIntegrable
      (fun r => coeff n k * coeff n l * Real.cos (((k : ℝ) - (l : ℝ)) * r)) volume (-π) π :=
    fun k l => (continuous_const.mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  simp only [kernel_eq_sum]
  rw [intervalIntegral.integral_finsetSum
    (f := fun k : ℕ => fun r : ℝ => ∑ l ∈ range (n + 1),
      coeff n k * coeff n l * Real.cos (((k : ℝ) - (l : ℝ)) * r))
    fun k _ => (continuous_finsetSum _ fun l _ => continuous_const.mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _]
  have hk : ∀ k ∈ range (n + 1), (∫ r in -π..π, ∑ l ∈ range (n + 1),
      coeff n k * coeff n l * Real.cos (((k : ℝ) - (l : ℝ)) * r))
      = coeff n k ^ 2 * (2 * π) := by
    intro k hk
    rw [intervalIntegral.integral_finsetSum
      (f := fun l : ℕ => fun r : ℝ => coeff n k * coeff n l * Real.cos (((k : ℝ) - (l : ℝ)) * r))
      fun l _ => hint k l]
    have hterm : ∀ l : ℕ, (∫ r in -π..π,
        coeff n k * coeff n l * Real.cos (((k : ℝ) - (l : ℝ)) * r))
        = coeff n k * coeff n l * (if (k : ℤ) - (l : ℤ) = 0 then 2 * π else 0) := by
      intro l
      rw [intervalIntegral.integral_const_mul, ← hcast k l, integral_cos_int_mul_neg_pi_pi]
    rw [Finset.sum_congr rfl fun l _ => hterm l,
      Finset.sum_eq_single k (fun l _ hlk => by
        rw [ite_eq_right (by omega : (k : ℤ) - (l : ℤ) ≠ 0), mul_zero])
        fun h => absurd hk h]
    rw [ite_eq_left (by omega : (k : ℤ) - (k : ℤ) = 0)]
    ring
  rw [Finset.sum_congr rfl hk, ← Finset.sum_mul, sum_coeff_sq n, one_mul]

/-- The first cosine coefficient of the Fejér–Korovkin kernel is $\cos\theta_n$:
$$\int_{-\pi}^{\pi} \cos r\, K_n(r)\, dr = 2\pi \cos\theta_n.$$
-/
theorem integral_cos_mul_kernel (n : ℕ) :
    (∫ r in -π..π, Real.cos r * kernel n r) = 2 * π * Real.cos (angle n) := by
  have hcast : ∀ k l : ℕ, (((k : ℤ) - (l : ℤ) : ℤ) : ℝ) = (k : ℝ) - (l : ℝ) := by
    intro k l; push_cast; ring
  have hint : ∀ k l : ℕ, IntervalIntegrable
      (fun r => coeff n k * coeff n l * (Real.cos (((k : ℝ) - (l : ℝ)) * r) * Real.cos r))
      volume (-π) π :=
    fun k l => (continuous_const.mul ((Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).mul Real.continuous_cos)).intervalIntegrable _ _
  have hrw : ∀ r : ℝ, Real.cos r * kernel n r = ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1),
      coeff n k * coeff n l * (Real.cos (((k : ℝ) - (l : ℝ)) * r) * Real.cos r) := by
    intro r
    rw [kernel_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [hrw]
  rw [intervalIntegral.integral_finsetSum
    (f := fun k : ℕ => fun r : ℝ => ∑ l ∈ range (n + 1),
      coeff n k * coeff n l * (Real.cos (((k : ℝ) - (l : ℝ)) * r) * Real.cos r))
    fun k _ => (continuous_finsetSum _ fun l _ => continuous_const.mul
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
        Real.continuous_cos)).intervalIntegrable _ _]
  have hk : ∀ k ∈ range (n + 1), (∫ r in -π..π, ∑ l ∈ range (n + 1),
      coeff n k * coeff n l * (Real.cos (((k : ℝ) - (l : ℝ)) * r) * Real.cos r))
      = ∑ l ∈ range (n + 1), coeff n k * coeff n l *
        ((if l = k + 1 then π else 0) + (if k = l + 1 then π else 0)) := by
    intro k _
    rw [intervalIntegral.integral_finsetSum
      (f := fun l : ℕ => fun r : ℝ =>
        coeff n k * coeff n l * (Real.cos (((k : ℝ) - (l : ℝ)) * r) * Real.cos r))
      fun l _ => hint k l]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [intervalIntegral.integral_const_mul, ← hcast k l, integral_cos_intCast_mul_cos]
    congr 2
    · exact if_congr (by omega) rfl rfl
    · exact if_congr (by omega) rfl rfl
  rw [Finset.sum_congr rfl hk]
  have hsplit : ∀ k l : ℕ, coeff n k * coeff n l *
      ((if l = k + 1 then π else 0) + (if k = l + 1 then π else 0))
      = π * (coeff n k * coeff n l * (if l = k + 1 then (1 : ℝ) else 0))
        + π * (coeff n l * coeff n k * (if k = l + 1 then (1 : ℝ) else 0)) := by
    intro k l
    split_ifs <;> ring
  simp only [hsplit]
  have hstep : ∀ k ∈ range (n + 1), (∑ l ∈ range (n + 1),
      (π * (coeff n k * coeff n l * (if l = k + 1 then (1 : ℝ) else 0))
        + π * (coeff n l * coeff n k * (if k = l + 1 then (1 : ℝ) else 0))))
      = π * (∑ l ∈ range (n + 1), coeff n k * coeff n l * (if l = k + 1 then (1 : ℝ) else 0))
        + π * (∑ l ∈ range (n + 1),
            coeff n l * coeff n k * (if k = l + 1 then (1 : ℝ) else 0)) := by
    intro k _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  have hB : ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1),
      coeff n l * coeff n k * (if k = l + 1 then (1 : ℝ) else 0) = Real.cos (angle n) := by
    rw [Finset.sum_comm]
    exact sum_sum_coeff_ite n
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_sum_coeff_ite n, hB]
  ring

/-! ### The first absolute moment -/

private theorem sin_sq_half (y : ℝ) : Real.sin (y / 2) ^ 2 = (1 - Real.cos y) / 2 := by
  have h : Real.cos (2 * (y / 2)) = 2 * Real.cos (y / 2) ^ 2 - 1 := Real.cos_two_mul _
  rw [show 2 * (y / 2) = y by ring] at h
  nlinarith [Real.sin_sq_add_cos_sq (y / 2)]

/-- **Jordan's inequality** in the form that the second moment needs: if $|r| \le \pi$, then
$r^2 \le \pi^2 (1 - \cos r)/2$. -/
private theorem sq_le_one_sub_cos {r : ℝ} (hr : |r| ≤ π) :
    r ^ 2 ≤ π ^ 2 * ((1 - Real.cos r) / 2) := by
  have habs : (0 : ℝ) ≤ |r| := abs_nonneg r
  have h3 : 2 / π * (|r| / 2) ≤ Real.sin (|r| / 2) :=
    Real.mul_le_sin (by linarith) (by linarith)
  have heq : 2 / π * (|r| / 2) = |r| / π := by field_simp
  have h4 : |r| / π ≤ Real.sin (|r| / 2) := by linarith [heq ▸ h3]
  have h5 : Real.sin (|r| / 2) ^ 2 = Real.sin (r / 2) ^ 2 := by
    rcases abs_cases r with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · rw [h, show -r / 2 = -(r / 2) by ring, Real.sin_neg]
      ring
  have h6 : (|r| / π) ^ 2 ≤ Real.sin (|r| / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h4 2
  rw [div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < π ^ 2)] at h6
  rw [← sin_sq_half r, ← h5, ← sq_abs r]
  nlinarith [h6]

/-- The second moment of the Fejér–Korovkin kernel:
$$\int_{-\pi}^{\pi} r^2 K_n(r)\, dr \le 2\pi \cdot \frac{\pi^2 (1 - \cos\theta_n)}{2}.$$

Since $\pi^2 (1 - \cos\theta_n)/2 = (\pi \sin(\theta_n/2))^2$, the root mean square of $r$
against the probability density $(2\pi)^{-1} K_n$ is at most $\pi \sin(\theta_n/2)$. -/
theorem integral_sq_mul_kernel_le (n : ℕ) :
    (∫ r in -π..π, r ^ 2 * kernel n r)
      ≤ 2 * π * (π ^ 2 * ((1 - Real.cos (angle n)) / 2)) := by
  have hpi := Real.pi_pos
  have hf : IntervalIntegrable (fun r : ℝ => r ^ 2 * kernel n r) volume (-π) π :=
    ((continuous_pow 2).mul (continuous_kernel n)).intervalIntegrable _ _
  have hg : IntervalIntegrable
      (fun r : ℝ => π ^ 2 * ((1 - Real.cos r) / 2) * kernel n r) volume (-π) π :=
    ((continuous_const.mul
      ((continuous_const.sub Real.continuous_cos).div_const 2)).mul
        (continuous_kernel n)).intervalIntegrable _ _
  have hle : ∀ r ∈ Set.Icc (-π) π,
      r ^ 2 * kernel n r ≤ π ^ 2 * ((1 - Real.cos r) / 2) * kernel n r := fun r hr =>
    mul_le_mul_of_nonneg_right (sq_le_one_sub_cos (abs_le.2 ⟨hr.1, hr.2⟩)) (kernel_nonneg n r)
  have h := intervalIntegral.integral_mono_on (by linarith : (-π : ℝ) ≤ π) hf hg hle
  have h1 : IntervalIntegrable (fun r : ℝ => π ^ 2 / 2 * kernel n r) volume (-π) π :=
    (continuous_const.mul (continuous_kernel n)).intervalIntegrable _ _
  have h2 : IntervalIntegrable
      (fun r : ℝ => π ^ 2 / 2 * (Real.cos r * kernel n r)) volume (-π) π :=
    (continuous_const.mul (Real.continuous_cos.mul (continuous_kernel n))).intervalIntegrable _ _
  have hcalc : (∫ r in -π..π, π ^ 2 * ((1 - Real.cos r) / 2) * kernel n r)
      = 2 * π * (π ^ 2 * ((1 - Real.cos (angle n)) / 2)) := by
    have hsplit : ∀ r : ℝ, π ^ 2 * ((1 - Real.cos r) / 2) * kernel n r
        = π ^ 2 / 2 * kernel n r - π ^ 2 / 2 * (Real.cos r * kernel n r) := fun r => by ring
    simp only [hsplit]
    rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_kernel n, integral_cos_mul_kernel n]
    ring
  rwa [hcalc] at h

/-- The half angle $\theta_n / 2 = \pi/(2(n + 2))$ has positive sine. -/
theorem sin_half_angle_pos (n : ℕ) : 0 < Real.sin (angle n / 2) := by
  have h1 := angle_pos n
  have h2 := angle_lt_pi n
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

/-- **The first absolute moment of the Fejér–Korovkin kernel**:
$$\int_{-\pi}^{\pi} |r|\, K_n(r)\, dr \le 2\pi \cdot \pi \sin(\theta_n/2).$$

With $s = \pi \sin(\theta_n/2)$, the kernel has mass $2\pi$ and second moment at most
$2\pi s^2$. Pointwise $|r| \le r^2/(2s) + s/2$, so the first moment is at most
$2\pi (s/2 + s/2) = 2\pi s$. -/
theorem integral_abs_mul_kernel_le (n : ℕ) :
    (∫ r in -π..π, |r| * kernel n r) ≤ 2 * π * (π * Real.sin (angle n / 2)) := by
  have hpi := Real.pi_pos
  have hs : 0 < π * Real.sin (angle n / 2) := mul_pos hpi (sin_half_angle_pos n)
  set s : ℝ := π * Real.sin (angle n / 2) with hsdef
  have hsq : s ^ 2 = π ^ 2 * ((1 - Real.cos (angle n)) / 2) := by
    rw [hsdef, mul_pow, sin_sq_half]
  have hf : IntervalIntegrable (fun r : ℝ => |r| * kernel n r) volume (-π) π :=
    (continuous_abs.mul (continuous_kernel n)).intervalIntegrable _ _
  have hg : IntervalIntegrable
      (fun r : ℝ => (r ^ 2 / (2 * s) + s / 2) * kernel n r) volume (-π) π :=
    ((((continuous_pow 2).div_const (2 * s)).add continuous_const).mul
      (continuous_kernel n)).intervalIntegrable _ _
  have hle : ∀ r ∈ Set.Icc (-π) π,
      |r| * kernel n r ≤ (r ^ 2 / (2 * s) + s / 2) * kernel n r := by
    intro r _
    refine mul_le_mul_of_nonneg_right ?_ (kernel_nonneg n r)
    have h3 : 2 * s * |r| ≤ r ^ 2 + s ^ 2 := by
      nlinarith [sq_nonneg (|r| - s), sq_abs r]
    have heq : r ^ 2 / (2 * s) + s / 2 - |r| = (r ^ 2 + s ^ 2 - 2 * s * |r|) / (2 * s) := by
      field_simp
    have hnn : 0 ≤ (r ^ 2 + s ^ 2 - 2 * s * |r|) / (2 * s) :=
      div_nonneg (by linarith) (by positivity)
    linarith [heq, hnn]
  have h := intervalIntegral.integral_mono_on (by linarith : (-π : ℝ) ≤ π) hf hg hle
  have h1 : IntervalIntegrable (fun r : ℝ => (2 * s)⁻¹ * (r ^ 2 * kernel n r))
      volume (-π) π :=
    (continuous_const.mul ((continuous_pow 2).mul (continuous_kernel n))).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun r : ℝ => s / 2 * kernel n r) volume (-π) π :=
    (continuous_const.mul (continuous_kernel n)).intervalIntegrable _ _
  have hcalc : (∫ r in -π..π, (r ^ 2 / (2 * s) + s / 2) * kernel n r)
      = (2 * s)⁻¹ * (∫ r in -π..π, r ^ 2 * kernel n r) + s / 2 * (2 * π) := by
    have hsplit : ∀ r : ℝ, (r ^ 2 / (2 * s) + s / 2) * kernel n r
        = (2 * s)⁻¹ * (r ^ 2 * kernel n r) + s / 2 * kernel n r := fun r => by
      field_simp
    simp only [hsplit]
    rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_kernel n]
  rw [hcalc] at h
  have hbound := integral_sq_mul_kernel_le n
  rw [← hsq] at hbound
  have hstep : (2 * s)⁻¹ * (∫ r in -π..π, r ^ 2 * kernel n r)
      ≤ (2 * s)⁻¹ * (2 * π * s ^ 2) := mul_le_mul_of_nonneg_left hbound (by positivity)
  have hfin : (2 * s)⁻¹ * (2 * π * s ^ 2) + s / 2 * (2 * π) = 2 * π * s := by
    field_simp
    ring
  linarith [h, hstep, hfin]

/-- The first absolute moment is of order $1/n$: $\pi \sin(\theta_n/2) \le \pi^2/(2(n + 2))$. This
bound gives the constant $1 + \pi^2/2$ of Jackson's theorem. -/
theorem pi_mul_sin_half_angle_le (n : ℕ) :
    π * Real.sin (angle n / 2) ≤ π ^ 2 / (2 * ((n : ℝ) + 2)) := by
  have hpi := Real.pi_pos
  have h1 : Real.sin (angle n / 2) ≤ angle n / 2 :=
    (Real.sin_lt (by linarith [angle_pos n])).le
  have h2 : angle n / 2 = π / (2 * ((n : ℝ) + 2)) := by
    rw [angle]
    field_simp
  calc π * Real.sin (angle n / 2) ≤ π * (angle n / 2) := by nlinarith
    _ = π ^ 2 / (2 * ((n : ℝ) + 2)) := by rw [h2]; field_simp

/-! ### Trigonometric monomials on the circle of circumference $2\pi$ -/

/-- The function $x \mapsto \cos(mx)$, for an integer $m$, as a continuous function on the circle of
circumference $2\pi$.

It is built from the real trigonometric system `trigFun`, so that its membership in `trigPolyLE`
is immediate. -/
noncomputable def cosCM (m : ℤ) : C(AddCircle (2 * π), ℝ) :=
  if m = 0 then 1 else (√2 : ℝ)⁻¹ • trigFun (2 * π) |m|

/-- The function $x \mapsto \sin(mx)$, for an integer $m$, as a continuous function on the circle of
circumference $2\pi$.

It is built from the real trigonometric system `trigFun`, and it is $0$ for $m = 0$. -/
noncomputable def sinCM (m : ℤ) : C(AddCircle (2 * π), ℝ) :=
  if 0 < m then (√2 : ℝ)⁻¹ • trigFun (2 * π) (-m)
  else if m < 0 then -((√2 : ℝ)⁻¹ • trigFun (2 * π) m) else 0

/-- The value of `Jackson.cosCM m` at the class of a real number $x$ is $\cos(mx)$. -/
@[simp]
theorem cosCM_coe (m : ℤ) (x : ℝ) :
    cosCM m ((x : ℝ) : AddCircle (2 * π)) = Real.cos ((m : ℝ) * x) := by
  have h2 : (√2 : ℝ) ≠ 0 := by positivity
  rcases lt_trichotomy m 0 with hm | hm | hm
  · rw [cosCM, ite_eq_right hm.ne, abs_of_neg hm, ContinuousMap.smul_apply, smul_eq_mul,
      trigFun_coe_of_pos (by omega : (0 : ℤ) < -m) x]
    push_cast
    rw [show -(m : ℝ) * x = -((m : ℝ) * x) by ring, Real.cos_neg]
    field_simp
  · rw [cosCM, ite_eq_left hm, hm]
    simp
  · rw [cosCM, ite_eq_right hm.ne', abs_of_pos hm, ContinuousMap.smul_apply, smul_eq_mul,
      trigFun_coe_of_pos hm x]
    field_simp

/-- The value of `Jackson.sinCM m` at the class of a real number $x$ is $\sin(mx)$. -/
@[simp]
theorem sinCM_coe (m : ℤ) (x : ℝ) :
    sinCM m ((x : ℝ) : AddCircle (2 * π)) = Real.sin ((m : ℝ) * x) := by
  have h2 : (√2 : ℝ) ≠ 0 := by positivity
  rcases lt_trichotomy m 0 with hm | hm | hm
  · rw [sinCM, ite_eq_right (by omega : ¬ (0 : ℤ) < m), ite_eq_left hm,
      ContinuousMap.neg_apply, ContinuousMap.smul_apply, smul_eq_mul, trigFun_coe_of_neg hm x]
    rw [show -(m : ℝ) * x = -((m : ℝ) * x) by ring, Real.sin_neg]
    field_simp
  · rw [sinCM, ite_eq_right (by omega : ¬ (0 : ℤ) < m), ite_eq_right (by omega : ¬ m < 0), hm]
    simp
  · rw [sinCM, ite_eq_left hm, ContinuousMap.smul_apply, smul_eq_mul,
      trigFun_coe_of_neg (by omega : (-m : ℤ) < 0) x]
    push_cast
    field_simp

/-- If $|m| \le n$, then $x \mapsto \cos(mx)$ is a trigonometric polynomial of degree at most $n$.
-/
theorem cosCM_mem {m : ℤ} {n : ℕ} (hm : m.natAbs ≤ n) : cosCM m ∈ trigPolyLE (2 * π) n := by
  rw [cosCM]
  split_ifs with h
  · rw [show (1 : C(AddCircle (2 * π), ℝ)) = trigFun (2 * π) 0 from trigFun_zero.symm]
    exact trigFun_mem_trigPolyLE (by simp)
  · exact Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE (by rwa [Int.natAbs_abs]))

/-- If $|m| \le n$, then $x \mapsto \sin(mx)$ is a trigonometric polynomial of degree at most $n$.
-/
theorem sinCM_mem {m : ℤ} {n : ℕ} (hm : m.natAbs ≤ n) : sinCM m ∈ trigPolyLE (2 * π) n := by
  rw [sinCM]
  split_ifs with h1 h2
  · exact Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE (by rwa [Int.natAbs_neg]))
  · exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE hm))
  · exact Submodule.zero_mem _

/-! ### The Fejér–Korovkin operator -/

/-- The integral of a $2\pi$-periodic function over a period does not change under the substitution
$r \mapsto x - r$. -/
private theorem integral_comp_sub_of_periodic {φ : ℝ → ℝ} (hp : Function.Periodic φ (2 * π))
    (x : ℝ) : (∫ r in -π..π, φ (x - r)) = ∫ y in -π..π, φ y := by
  rw [intervalIntegral.integral_comp_sub_left φ x, show x - -π = x + π from by ring]
  have h := hp.intervalIntegral_add_eq (x - π) (-π)
  rw [show x - π + 2 * π = x + π by ring, show -π + 2 * π = π by ring] at h
  exact h

/-- For a continuous $2\pi$-periodic $g$, the integral of $\cos(mr)\, g(x - r)$ over a period is
$\cos(mx) a_m + \sin(mx) b_m$, where $a_m$ and $b_m$ are the integrals of $\cos(my)\, g(y)$ and
$\sin(my)\, g(y)$ over a period. -/
private theorem integral_cos_mul_comp_sub {g : ℝ → ℝ} (hc : Continuous g)
    (hp : Function.Periodic g (2 * π)) (m : ℤ) (x : ℝ) :
    (∫ r in -π..π, Real.cos ((m : ℝ) * r) * g (x - r))
      = Real.cos ((m : ℝ) * x) * (∫ y in -π..π, Real.cos ((m : ℝ) * y) * g y)
        + Real.sin ((m : ℝ) * x) * (∫ y in -π..π, Real.sin ((m : ℝ) * y) * g y) := by
  have hφ1c : Continuous fun y : ℝ => Real.cos ((m : ℝ) * y) * g y :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul hc
  have hφ2c : Continuous fun y : ℝ => Real.sin ((m : ℝ) * y) * g y :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul hc
  have hφ1p : Function.Periodic (fun y : ℝ => Real.cos ((m : ℝ) * y) * g y) (2 * π) := by
    intro y
    have h1 : (m : ℝ) * (y + 2 * π) = (m : ℝ) * y + (m : ℤ) * (2 * π) := by ring
    simp only []
    rw [h1, Real.cos_add_int_mul_two_pi, hp y]
  have hφ2p : Function.Periodic (fun y : ℝ => Real.sin ((m : ℝ) * y) * g y) (2 * π) := by
    intro y
    have h1 : (m : ℝ) * (y + 2 * π) = (m : ℝ) * y + (m : ℤ) * (2 * π) := by ring
    simp only []
    rw [h1, Real.sin_add_int_mul_two_pi, hp y]
  have hstep : ∀ r : ℝ, Real.cos ((m : ℝ) * r) * g (x - r)
      = Real.cos ((m : ℝ) * x) * (Real.cos ((m : ℝ) * (x - r)) * g (x - r))
        + Real.sin ((m : ℝ) * x) * (Real.sin ((m : ℝ) * (x - r)) * g (x - r)) := by
    intro r
    rw [show (m : ℝ) * r = (m : ℝ) * x - (m : ℝ) * (x - r) by ring, Real.cos_sub]
    ring
  have hi1 : IntervalIntegrable
      (fun r : ℝ => Real.cos ((m : ℝ) * x) * (Real.cos ((m : ℝ) * (x - r)) * g (x - r)))
      volume (-π) π :=
    (continuous_const.mul (hφ1c.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _
  have hi2 : IntervalIntegrable
      (fun r : ℝ => Real.sin ((m : ℝ) * x) * (Real.sin ((m : ℝ) * (x - r)) * g (x - r)))
      volume (-π) π :=
    (continuous_const.mul (hφ2c.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _
  have e1 : (∫ r in -π..π, Real.cos ((m : ℝ) * (x - r)) * g (x - r))
      = ∫ y in -π..π, Real.cos ((m : ℝ) * y) * g y := integral_comp_sub_of_periodic hφ1p x
  have e2 : (∫ r in -π..π, Real.sin ((m : ℝ) * (x - r)) * g (x - r))
      = ∫ y in -π..π, Real.sin ((m : ℝ) * y) * g y := integral_comp_sub_of_periodic hφ2p x
  simp only [hstep]
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, e1, e2]

/-- The **Fejér–Korovkin approximation** of a function $g : \mathbb{R} \to \mathbb{R}$: the
trigonometric polynomial of degree at most $n$
$$L_n g = (2\pi)^{-1} \sum_{k=0}^{n} \sum_{l=0}^{n} c_k c_l \bigl(a_{k-l} \cos((k - l)\,\cdot) +
  b_{k-l} \sin((k - l)\,\cdot)\bigr),$$
where $a_m = \int_{-\pi}^{\pi} \cos(my)\, g(y)\, dy$ and
$b_m = \int_{-\pi}^{\pi} \sin(my)\, g(y)\, dy$.

For a continuous $2\pi$-periodic $g$, the value at $x$ is the convolution $(2\pi)^{-1}
\int_{-\pi}^{\pi} K_n(r)\, g(x - r)\, dr$ (`Jackson.approx_coe`). The definition is written out
in the real trigonometric system, so that the membership in `trigPolyLE (2 * π) n` is immediate.
For a function $g$ that is not integrable on $[-\pi, \pi]$, the integrals take the value $0$. -/
noncomputable def approx (n : ℕ) (g : ℝ → ℝ) : C(AddCircle (2 * π), ℝ) :=
  (2 * π)⁻¹ • ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1),
    (coeff n k * coeff n l) •
      ((∫ y in -π..π, Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * y) * g y) •
          cosCM ((k : ℤ) - (l : ℤ))
        + (∫ y in -π..π, Real.sin ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * y) * g y) •
            sinCM ((k : ℤ) - (l : ℤ)))

/-- For every $g : \mathbb{R} \to \mathbb{R}$, the Fejér–Korovkin approximation $L_n g$ is a
trigonometric polynomial of degree at most $n$. -/
theorem approx_mem (n : ℕ) (g : ℝ → ℝ) : approx n g ∈ trigPolyLE (2 * π) n := by
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k hk => Submodule.sum_mem _ fun l hl => ?_)
  have hkn := Finset.mem_range.1 hk
  have hln := Finset.mem_range.1 hl
  have hm : ((k : ℤ) - (l : ℤ)).natAbs ≤ n := by omega
  exact Submodule.smul_mem _ _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (cosCM_mem hm)) (Submodule.smul_mem _ _ (sinCM_mem hm)))

/-- **The Fejér–Korovkin approximation is the convolution of $g$ with the kernel.** If $g$ is
continuous and $2\pi$-periodic, then for all real $x$
$$L_n g(x) = (2\pi)^{-1} \int_{-\pi}^{\pi} K_n(r)\, g(x - r)\, dr.$$
-/
theorem approx_coe {g : ℝ → ℝ} (hc : Continuous g) (hp : Function.Periodic g (2 * π)) (n : ℕ)
    (x : ℝ) :
    approx n g ((x : ℝ) : AddCircle (2 * π))
      = (2 * π)⁻¹ * ∫ r in -π..π, kernel n r * g (x - r) := by
  have hgc : Continuous fun r : ℝ => g (x - r) := hc.comp (continuous_const.sub continuous_id)
  have hcast : ∀ k l : ℕ, ((((k : ℤ) - (l : ℤ)) : ℤ) : ℝ) = (k : ℝ) - (l : ℝ) := by
    intro k l; push_cast; ring
  have hexp : ∀ r : ℝ, kernel n r * g (x - r)
      = ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1),
        coeff n k * coeff n l *
          (Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * r) * g (x - r)) := by
    intro r
    rw [kernel_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hcast k l]
    ring
  have hintkl : ∀ k l : ℕ, IntervalIntegrable
      (fun r : ℝ => coeff n k * coeff n l *
        (Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * r) * g (x - r))) volume (-π) π :=
    fun k l => (continuous_const.mul
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
        hgc)).intervalIntegrable _ _
  simp only [approx, ContinuousMap.smul_apply, ContinuousMap.coe_sum, Finset.sum_apply,
    ContinuousMap.add_apply, smul_eq_mul, cosCM_coe, sinCM_coe]
  simp only [hexp]
  rw [intervalIntegral.integral_finsetSum
      (f := fun k : ℕ => fun r : ℝ => ∑ l ∈ range (n + 1), coeff n k * coeff n l *
        (Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * r) * g (x - r)))
      fun k _ => (continuous_finsetSum _ fun l _ => continuous_const.mul
        ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
          hgc)).intervalIntegrable _ _]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_finsetSum
      (f := fun l : ℕ => fun r : ℝ => coeff n k * coeff n l *
        (Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * r) * g (x - r)))
      fun l _ => hintkl k l]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_cos_mul_comp_sub hc hp ((k : ℤ) - (l : ℤ)) x]
  ring

/-! ### The approximation error -/

/-- **The error of the Fejér–Korovkin approximation is bounded by the kernel average of the
increments of $g$.** If $g$ is continuous and $2\pi$-periodic, then for all real $x$
$$|g(x) - L_n g(x)| \le (2\pi)^{-1} \int_{-\pi}^{\pi} K_n(r)\, |g(x) - g(x - r)|\, dr.$$
-/
theorem abs_sub_approx_le {g : ℝ → ℝ} (hc : Continuous g) (hp : Function.Periodic g (2 * π))
    (n : ℕ) (x : ℝ) :
    |g x - approx n g ((x : ℝ) : AddCircle (2 * π))|
      ≤ (2 * π)⁻¹ * ∫ r in -π..π, kernel n r * |g x - g (x - r)| := by
  have hpi := Real.pi_pos
  have hgc : Continuous fun r : ℝ => g (x - r) := hc.comp (continuous_const.sub continuous_id)
  have h1 : IntervalIntegrable (fun r : ℝ => kernel n r * g x) volume (-π) π :=
    ((continuous_kernel n).mul continuous_const).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun r : ℝ => kernel n r * g (x - r)) volume (-π) π :=
    ((continuous_kernel n).mul hgc).intervalIntegrable _ _
  have hsplit : (∫ r in -π..π, kernel n r * (g x - g (x - r)))
      = 2 * π * g x - ∫ r in -π..π, kernel n r * g (x - r) := by
    have hpt : ∀ r : ℝ, kernel n r * (g x - g (x - r))
        = kernel n r * g x - kernel n r * g (x - r) := fun r => by ring
    simp only [hpt]
    rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_mul_const,
      integral_kernel n]
  have hkey : g x - approx n g ((x : ℝ) : AddCircle (2 * π))
      = (2 * π)⁻¹ * ∫ r in -π..π, kernel n r * (g x - g (x - r)) := by
    rw [hsplit, approx_coe hc hp n x]
    field_simp
  rw [hkey, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc |∫ r in -π..π, kernel n r * (g x - g (x - r))|
      ≤ ∫ r in -π..π, |kernel n r * (g x - g (x - r))| :=
        intervalIntegral.abs_integral_le_integral_abs (by linarith)
    _ = ∫ r in -π..π, kernel n r * |g x - g (x - r)| :=
        intervalIntegral.integral_congr fun r _ => by
          rw [abs_mul, abs_of_nonneg (kernel_nonneg n r)]

/-- **The Fejér–Korovkin error for a Hölder function.** Let $g$ be continuous and $2\pi$-periodic,
and let $M \ge 0$ and $0 \le \alpha \le 1$ be such that $|g(u) - g(v)| \le M |u - v|^\alpha$ for
all real $u$ and $v$. Then for every $n$ and every real $x$
$$|g(x) - L_n g(x)| \le M \bigl(\pi \sin(\pi/(2n + 4))\bigr)^\alpha.$$
-/
theorem abs_sub_approx_le_of_holder {g : ℝ → ℝ} (hc : Continuous g)
    (hp : Function.Periodic g (2 * π)) {M α : ℝ} (hM : 0 ≤ M) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hg : ∀ u v : ℝ, |g u - g v| ≤ M * |u - v| ^ α) (n : ℕ) (x : ℝ) :
    |g x - approx n g ((x : ℝ) : AddCircle (2 * π))|
      ≤ M * (π * Real.sin (angle n / 2)) ^ α := by
  have hpi := Real.pi_pos
  have hs : 0 < π * Real.sin (angle n / 2) := mul_pos hpi (sin_half_angle_pos n)
  set s : ℝ := π * Real.sin (angle n / 2) with hsdef
  have hgc : Continuous fun r : ℝ => g (x - r) := hc.comp (continuous_const.sub continuous_id)
  have hf : IntervalIntegrable (fun r : ℝ => kernel n r * |g x - g (x - r)|) volume (-π) π :=
    ((continuous_kernel n).mul (continuous_const.sub hgc).abs).intervalIntegrable _ _
  have hgb : IntervalIntegrable
      (fun r : ℝ => kernel n r * (M * (α * s ^ (α - 1) * |r| + (1 - α) * s ^ α)))
      volume (-π) π :=
    ((continuous_kernel n).mul (continuous_const.mul
      ((continuous_const.mul continuous_abs).add continuous_const))).intervalIntegrable _ _
  have hle : ∀ r ∈ Set.Icc (-π) π, kernel n r * |g x - g (x - r)|
      ≤ kernel n r * (M * (α * s ^ (α - 1) * |r| + (1 - α) * s ^ α)) := by
    intro r _
    refine mul_le_mul_of_nonneg_left ?_ (kernel_nonneg n r)
    refine (hg x (x - r)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hM
    have habs : |x - (x - r)| = |r| := by rw [show x - (x - r) = r by ring]
    rw [habs]
    exact Real.rpow_le_tangent (abs_nonneg r) hs hα0 hα1
  have hmono := intervalIntegral.integral_mono_on (by linarith : (-π : ℝ) ≤ π) hf hgb hle
  have hi1 : IntervalIntegrable
      (fun r : ℝ => M * (α * s ^ (α - 1)) * (kernel n r * |r|)) volume (-π) π :=
    (continuous_const.mul ((continuous_kernel n).mul continuous_abs)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable
      (fun r : ℝ => M * ((1 - α) * s ^ α) * kernel n r) volume (-π) π :=
    (continuous_const.mul (continuous_kernel n)).intervalIntegrable _ _
  have hcalc : (∫ r in -π..π, kernel n r * (M * (α * s ^ (α - 1) * |r| + (1 - α) * s ^ α)))
      = M * (α * s ^ (α - 1)) * (∫ r in -π..π, |r| * kernel n r)
        + M * ((1 - α) * s ^ α) * (2 * π) := by
    have hpt : ∀ r : ℝ, kernel n r * (M * (α * s ^ (α - 1) * |r| + (1 - α) * s ^ α))
        = M * (α * s ^ (α - 1)) * (kernel n r * |r|) + M * ((1 - α) * s ^ α) * kernel n r :=
      fun r => by ring
    simp only [hpt]
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_kernel n]
    congr 2
    exact intervalIntegral.integral_congr fun r _ => by ring
  rw [hcalc] at hmono
  have hmoment := integral_abs_mul_kernel_le n
  have hcoef : (0 : ℝ) ≤ M * (α * s ^ (α - 1)) := by
    positivity
  have hstep : M * (α * s ^ (α - 1)) * (∫ r in -π..π, |r| * kernel n r)
      ≤ M * (α * s ^ (α - 1)) * (2 * π * s) := mul_le_mul_of_nonneg_left hmoment hcoef
  have hfin : M * (α * s ^ (α - 1)) * (2 * π * s) + M * ((1 - α) * s ^ α) * (2 * π)
      = 2 * π * (M * s ^ α) := by
    have hsα : s ^ (α - 1) * s = s ^ α := by
      rw [Real.rpow_sub hs, Real.rpow_one, div_mul_cancel₀ _ hs.ne']
    linear_combination (2 * π * M * α) * hsα
  have hbound : (∫ r in -π..π, kernel n r * |g x - g (x - r)|) ≤ 2 * π * (M * s ^ α) := by
    linarith [hmono, hstep, hfin]
  refine (abs_sub_approx_le hc hp n x).trans ?_
  have h2π : (0 : ℝ) < (2 * π)⁻¹ := by positivity
  calc (2 * π)⁻¹ * ∫ r in -π..π, kernel n r * |g x - g (x - r)|
      ≤ (2 * π)⁻¹ * (2 * π * (M * s ^ α)) := mul_le_mul_of_nonneg_left hbound h2π.le
    _ = M * s ^ α := by field_simp

/-! ### Jackson's theorem for a Hölder continuous periodic function -/

/-- The $2\pi$-periodic real function $x \mapsto G(x)$ that underlies a continuous function $G$ on
the circle of circumference $2\pi$. -/
noncomputable abbrev lift (G : C(AddCircle (2 * π), ℝ)) : ℝ → ℝ := fun x => G ↑x

/-- The real function that underlies a continuous function on the circle is continuous. -/
theorem continuous_lift (G : C(AddCircle (2 * π), ℝ)) : Continuous (lift G) :=
  G.continuous.comp (AddCircle.continuous_mk' (2 * π))

/-- The real function that underlies a continuous function on the circle is $2\pi$-periodic. -/
theorem periodic_lift (G : C(AddCircle (2 * π), ℝ)) :
    Function.Periodic (lift G) (2 * π) := fun t => by
  simp only [lift]
  rw [AddCircle.coe_add_period]

/-- **Jackson's theorem for a Hölder function**, the case $k = 0$. Let $G$ be a continuous function
on the circle of circumference $2\pi$, and let $M \ge 0$ and $0 \le \alpha \le 1$ be such that
$|G(u) - G(v)| \le M |u - v|^\alpha$ for all real $u$ and $v$. Then for every $n$
$$\operatorname{dist}(G, \mathcal{T}_n) \le M \bigl(\pi \sin(\pi/(2n + 4))\bigr)^\alpha,$$
where $\mathcal{T}_n$ is the space of trigonometric polynomials of degree at most $n$ and the
distance is uniform.

Since $\pi \sin(\pi/(2n + 4)) \le \pi^2/(2(n + 2))$, the bound is at most
$M (\pi^2/2)^\alpha / n^\alpha$. This is the origin of the constant $1 + \pi^2/2$ of the
classical statement. The space $\mathcal{T}_n$ is `trigPolyLE (2 * π) n`, and the Hölder
condition is stated for `Jackson.lift G`. -/
theorem infDist_le_of_holder {G : C(AddCircle (2 * π), ℝ)} {M α : ℝ} (hM : 0 ≤ M)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hg : ∀ u v : ℝ, |lift G u - lift G v| ≤ M * |u - v| ^ α) (n : ℕ) :
    Metric.infDist G (trigPolyLE (2 * π) n : Set C(AddCircle (2 * π), ℝ))
      ≤ M * (π * Real.sin (angle n / 2)) ^ α := by
  have hs : 0 < π * Real.sin (angle n / 2) := mul_pos Real.pi_pos (sin_half_angle_pos n)
  have hnn : 0 ≤ M * (π * Real.sin (angle n / 2)) ^ α :=
    mul_nonneg hM (Real.rpow_nonneg hs.le α)
  have hnorm : ‖G - approx n (lift G)‖ ≤ M * (π * Real.sin (angle n / 2)) ^ α := by
    rw [ContinuousMap.norm_le _ hnn]
    intro z
    induction z using QuotientAddGroup.induction_on with
    | _ x =>
      simpa [Real.norm_eq_abs] using
        abs_sub_approx_le_of_holder (continuous_lift G) (periodic_lift G) hM hα0 hα1 hg n x
  calc Metric.infDist G (trigPolyLE (2 * π) n : Set C(AddCircle (2 * π), ℝ))
      ≤ dist G (approx n (lift G)) :=
        Metric.infDist_le_dist_of_mem (approx_mem n (lift G))
    _ = ‖G - approx n (lift G)‖ := dist_eq_norm _ _
    _ ≤ _ := hnorm

/-! ### The operator commutes with differentiation -/

/-- The Fejér–Korovkin approximation, evaluated at a real number $x$, as the trigonometric sum
$(2\pi)^{-1} \sum_{k, l \le n} c_k c_l (a_{k-l} \cos((k - l) x) + b_{k-l} \sin((k - l) x))$. -/
theorem approx_coe_eq_sum (n : ℕ) (g : ℝ → ℝ) (x : ℝ) :
    approx n g ((x : ℝ) : AddCircle (2 * π))
      = (2 * π)⁻¹ * ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1),
        coeff n k * coeff n l *
          ((∫ y in -π..π, Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * y) * g y) *
              Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * x)
            + (∫ y in -π..π, Real.sin ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * y) * g y) *
              Real.sin ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * x)) := by
  simp only [approx, ContinuousMap.smul_apply, ContinuousMap.coe_sum, Finset.sum_apply,
    ContinuousMap.add_apply, smul_eq_mul, cosCM_coe, sinCM_coe]

/-- The derivative of a trigonometric double sum of the form of `Jackson.approx` is the termwise
derivative. -/
private theorem hasDerivAt_trigDoubleSum (n : ℕ) (a b : ℕ → ℕ → ℝ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => (2 * π)⁻¹ * ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1),
        coeff n k * coeff n l *
          (a k l * Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * y)
            + b k l * Real.sin ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * y)))
      ((2 * π)⁻¹ * ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1),
        coeff n k * coeff n l *
          (a k l * (-Real.sin ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * x) *
              (((k : ℤ) - (l : ℤ) : ℤ) : ℝ))
            + b k l * (Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * x) *
              (((k : ℤ) - (l : ℤ) : ℤ) : ℝ)))) x := by
  have hterm : ∀ k l : ℕ, HasDerivAt
      (fun y : ℝ => coeff n k * coeff n l *
        (a k l * Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * y)
          + b k l * Real.sin ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * y)))
      (coeff n k * coeff n l *
        (a k l * (-Real.sin ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * x) *
            (((k : ℤ) - (l : ℤ) : ℤ) : ℝ))
          + b k l * (Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * x) *
            (((k : ℤ) - (l : ℤ) : ℤ) : ℝ)))) x := by
    intro k l
    have h1 : HasDerivAt (fun t : ℝ => (((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * t)
        ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ)) x := by
      simpa using (hasDerivAt_id x).const_mul ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ))
    exact HasDerivAt.const_mul _
      ((HasDerivAt.const_mul (a k l) h1.cos).add (HasDerivAt.const_mul (b k l) h1.sin))
  have hinner : ∀ k : ℕ, HasDerivAt
      (fun y : ℝ => ∑ l ∈ range (n + 1), coeff n k * coeff n l *
        (a k l * Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * y)
          + b k l * Real.sin ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * y)))
      (∑ l ∈ range (n + 1), coeff n k * coeff n l *
        (a k l * (-Real.sin ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * x) *
            (((k : ℤ) - (l : ℤ) : ℤ) : ℝ))
          + b k l * (Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * x) *
            (((k : ℤ) - (l : ℤ) : ℤ) : ℝ)))) x := by
    intro k
    exact HasDerivAt.fun_sum fun l _ => hterm k l
  have houter : HasDerivAt
      (fun y : ℝ => ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1), coeff n k * coeff n l *
        (a k l * Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * y)
          + b k l * Real.sin ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * y)))
      (∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1), coeff n k * coeff n l *
        (a k l * (-Real.sin ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * x) *
            (((k : ℤ) - (l : ℤ) : ℤ) : ℝ))
          + b k l * (Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * x) *
            (((k : ℤ) - (l : ℤ) : ℤ) : ℝ)))) x := by
    exact HasDerivAt.fun_sum fun k _ => hinner k
  exact HasDerivAt.const_mul _ houter

/-- **Integration by parts against the cosines.** If $g$ is $2\pi$-periodic and differentiable with
a continuous derivative $g'$, then $\int_{-\pi}^{\pi} \cos(my)\, g'(y)\, dy = m
\int_{-\pi}^{\pi} \sin(my)\, g(y)\, dy$. -/
private theorem integral_cos_mul_deriv {g g' : ℝ → ℝ} (hd : ∀ x, HasDerivAt g (g' x) x)
    (hc' : Continuous g') (hp : Function.Periodic g (2 * π)) (m : ℤ) :
    (∫ y in -π..π, Real.cos ((m : ℝ) * y) * g' y)
      = (m : ℝ) * ∫ y in -π..π, Real.sin ((m : ℝ) * y) * g y := by
  have hlin : ∀ y : ℝ, HasDerivAt (fun t : ℝ => (m : ℝ) * t) (m : ℝ) y := fun y => by
    simpa using (hasDerivAt_id y).const_mul (m : ℝ)
  have hu : ∀ y ∈ Set.uIcc (-π) π, HasDerivAt (fun t : ℝ => Real.cos ((m : ℝ) * t))
      (-Real.sin ((m : ℝ) * y) * (m : ℝ)) y := fun y _ => (hlin y).cos
  have hv : ∀ y ∈ Set.uIcc (-π) π, HasDerivAt g (g' y) y := fun y _ => hd y
  have hu' : IntervalIntegrable (fun y : ℝ => -Real.sin ((m : ℝ) * y) * (m : ℝ))
      volume (-π) π :=
    (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).neg).mul
      continuous_const).intervalIntegrable _ _
  have hv' : IntervalIntegrable g' volume (-π) π := hc'.intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hbdry : Real.cos ((m : ℝ) * π) * g π - Real.cos ((m : ℝ) * -π) * g (-π) = 0 := by
    have hg : g π = g (-π) := by
      have := hp (-π)
      rw [show -π + 2 * π = π by ring] at this
      exact this
    rw [hg, show (m : ℝ) * -π = -((m : ℝ) * π) by ring, Real.cos_neg]
    ring
  rw [hbdry] at hibp
  have hrw : (∫ y in -π..π, -Real.sin ((m : ℝ) * y) * (m : ℝ) * g y)
      = -((m : ℝ) * ∫ y in -π..π, Real.sin ((m : ℝ) * y) * g y) := by
    have h1 : (∫ y in -π..π, -Real.sin ((m : ℝ) * y) * (m : ℝ) * g y)
        = ∫ y in -π..π, (-(m : ℝ)) * (Real.sin ((m : ℝ) * y) * g y) :=
      intervalIntegral.integral_congr fun y _ => by ring
    rw [h1, intervalIntegral.integral_const_mul]
    ring
  rw [hrw] at hibp
  linarith [hibp]

/-- **Integration by parts against the sines.** If $g$ is differentiable with a continuous
derivative $g'$, then $\int_{-\pi}^{\pi} \sin(my)\, g'(y)\, dy = -m \int_{-\pi}^{\pi} \cos(my)\,
g(y)\, dy$. -/
private theorem integral_sin_mul_deriv {g g' : ℝ → ℝ} (hd : ∀ x, HasDerivAt g (g' x) x)
    (hc' : Continuous g') (m : ℤ) :
    (∫ y in -π..π, Real.sin ((m : ℝ) * y) * g' y)
      = -(m : ℝ) * ∫ y in -π..π, Real.cos ((m : ℝ) * y) * g y := by
  have hlin : ∀ y : ℝ, HasDerivAt (fun t : ℝ => (m : ℝ) * t) (m : ℝ) y := fun y => by
    simpa using (hasDerivAt_id y).const_mul (m : ℝ)
  have hu : ∀ y ∈ Set.uIcc (-π) π, HasDerivAt (fun t : ℝ => Real.sin ((m : ℝ) * t))
      (Real.cos ((m : ℝ) * y) * (m : ℝ)) y := fun y _ => (hlin y).sin
  have hv : ∀ y ∈ Set.uIcc (-π) π, HasDerivAt g (g' y) y := fun y _ => hd y
  have hu' : IntervalIntegrable (fun y : ℝ => Real.cos ((m : ℝ) * y) * (m : ℝ))
      volume (-π) π :=
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
      continuous_const).intervalIntegrable _ _
  have hv' : IntervalIntegrable g' volume (-π) π := hc'.intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hbdry : Real.sin ((m : ℝ) * π) * g π - Real.sin ((m : ℝ) * -π) * g (-π) = 0 := by
    have h1 : Real.sin ((m : ℝ) * π) = 0 := Real.sin_int_mul_pi m
    have h2 : Real.sin ((m : ℝ) * -π) = 0 := by
      rw [show (m : ℝ) * -π = -((m : ℝ) * π) by ring, Real.sin_neg, h1, neg_zero]
    rw [h1, h2]
    ring
  rw [hbdry] at hibp
  have hrw : (∫ y in -π..π, Real.cos ((m : ℝ) * y) * (m : ℝ) * g y)
      = (m : ℝ) * ∫ y in -π..π, Real.cos ((m : ℝ) * y) * g y := by
    have h1 : (∫ y in -π..π, Real.cos ((m : ℝ) * y) * (m : ℝ) * g y)
        = ∫ y in -π..π, (m : ℝ) * (Real.cos ((m : ℝ) * y) * g y) :=
      intervalIntegral.integral_congr fun y _ => by ring
    rw [h1, intervalIntegral.integral_const_mul]
  rw [hrw] at hibp
  linarith [hibp]

/-- **The Fejér–Korovkin operator commutes with differentiation.** Let $g$ be $2\pi$-periodic and
differentiable at every point, with a continuous derivative $g'$. Then for every $n$ the
function $y \mapsto L_n g(y)$ is differentiable at every real $x$, with derivative
$$(L_n g)'(x) = L_n g'(x).$$

The proof is integration by parts on each Fourier coefficient of $g$ in the definition of
$L_n g$. -/
theorem hasDerivAt_approx {g g' : ℝ → ℝ} (hd : ∀ x, HasDerivAt g (g' x) x) (hc' : Continuous g')
    (hp : Function.Periodic g (2 * π)) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => approx n g ((y : ℝ) : AddCircle (2 * π)))
      (approx n g' ((x : ℝ) : AddCircle (2 * π))) x := by
  have hfun : (fun y : ℝ => approx n g ((y : ℝ) : AddCircle (2 * π)))
      = fun y : ℝ => (2 * π)⁻¹ * ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1),
        coeff n k * coeff n l *
          ((∫ z in -π..π, Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * z) * g z) *
              Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * y)
            + (∫ z in -π..π, Real.sin ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * z) * g z) *
              Real.sin ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * y)) := by
    funext y
    exact approx_coe_eq_sum n g y
  have hval : (2 * π)⁻¹ * ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1),
      coeff n k * coeff n l *
        ((∫ z in -π..π, Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * z) * g z) *
            (-Real.sin ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * x) * (((k : ℤ) - (l : ℤ) : ℤ) : ℝ))
          + (∫ z in -π..π, Real.sin ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * z) * g z) *
            (Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * x) * (((k : ℤ) - (l : ℤ) : ℤ) : ℝ)))
      = approx n g' ((x : ℝ) : AddCircle (2 * π)) := by
    rw [approx_coe_eq_sum n g' x]
    congr 1
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [integral_cos_mul_deriv hd hc' hp ((k : ℤ) - (l : ℤ)),
      integral_sin_mul_deriv hd hc' ((k : ℤ) - (l : ℤ))]
    ring
  rw [hfun, ← hval]
  exact hasDerivAt_trigDoubleSum n
    (fun k l => ∫ z in -π..π, Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * z) * g z)
    (fun k l => ∫ z in -π..π, Real.sin ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * z) * g z) x

/-! ### The remainder operator and the $C^{k,\alpha}$ case -/

/-- The **Fejér–Korovkin remainder** $R_n g = g - L_n g$, as a function on $\mathbb{R}$.

Jackson's theorem for a $k$ times differentiable function is proved through the iterates of
$R_n$. Each application removes a trigonometric polynomial of degree at most $n$, and each
application commutes with differentiation. -/
noncomputable def rem (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => g x - approx n g ((x : ℝ) : AddCircle (2 * π))

/-- If $g$ is continuous, then the remainder $R_n g$ is continuous. -/
theorem continuous_rem (n : ℕ) {g : ℝ → ℝ} (hc : Continuous g) : Continuous (rem n g) :=
  hc.sub ((approx n g).continuous.comp (AddCircle.continuous_mk' (2 * π)))

/-- If $g$ is $2\pi$-periodic, then the remainder $R_n g$ is $2\pi$-periodic. -/
theorem periodic_rem (n : ℕ) {g : ℝ → ℝ} (hp : Function.Periodic g (2 * π)) :
    Function.Periodic (rem n g) (2 * π) := by
  intro x
  simp only [rem]
  rw [hp x, AddCircle.coe_add_period]

/-- The remainder commutes with differentiation: if $g$ is $2\pi$-periodic and differentiable at
every point, with a continuous derivative $g'$, then $(R_n g)' = R_n g'$ at every point. -/
theorem hasDerivAt_rem {g g' : ℝ → ℝ} (hd : ∀ x, HasDerivAt g (g' x) x) (hc' : Continuous g')
    (hp : Function.Periodic g (2 * π)) (n : ℕ) (x : ℝ) :
    HasDerivAt (rem n g) (rem n g' x) x :=
  (hd x).sub (hasDerivAt_approx hd hc' hp n x)

/-- The derivative of a periodic function is periodic: if $f$ is $T$-periodic and has the derivative
$f'(x)$ at every $x$, then $f'$ is $T$-periodic. -/
theorem periodic_deriv {f f' : ℝ → ℝ} {T : ℝ} (hp : Function.Periodic f T)
    (hd : ∀ x, HasDerivAt f (f' x) x) : Function.Periodic f' T := by
  intro x
  have h2 : HasDerivAt (fun y : ℝ => f (y + T)) (f' (x + T)) x :=
    HasDerivAt.comp_add_const x T (hd (x + T))
  rw [funext fun y => hp y] at h2
  exact h2.unique (hd x)

/-- If $g$ is continuous, then every iterate $R_n^j g$ of the remainder is continuous. -/
theorem continuous_iterate_rem (n : ℕ) : ∀ (j : ℕ) {g : ℝ → ℝ}, Continuous g →
    Continuous ((rem n)^[j] g)
  | 0, _, hc => hc
  | j + 1, g, hc => by
    rw [Function.iterate_succ_apply]
    exact continuous_iterate_rem n j (continuous_rem n hc)

/-- If $g$ is $2\pi$-periodic, then every iterate $R_n^j g$ of the remainder is $2\pi$-periodic. -/
theorem periodic_iterate_rem (n : ℕ) : ∀ (j : ℕ) {g : ℝ → ℝ}, Function.Periodic g (2 * π) →
    Function.Periodic ((rem n)^[j] g) (2 * π)
  | 0, _, hp => hp
  | j + 1, g, hp => by
    rw [Function.iterate_succ_apply]
    exact periodic_iterate_rem n j (periodic_rem n hp)

/-- Every iterate of the remainder commutes with differentiation: if $g$ and $g'$ are continuous,
$g$ is $2\pi$-periodic, and $g$ has the derivative $g'(x)$ at every $x$, then
$(R_n^j g)' = R_n^j g'$ at every point. -/
theorem hasDerivAt_iterate_rem (n : ℕ) : ∀ (j : ℕ) {g g' : ℝ → ℝ}, Continuous g →
    Continuous g' → Function.Periodic g (2 * π) → (∀ x, HasDerivAt g (g' x) x) →
    ∀ x, HasDerivAt ((rem n)^[j] g) ((rem n)^[j] g' x) x
  | 0, _, _, _, _, _, hd, x => hd x
  | j + 1, g, g', hc, hc', hp, hd, x => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact hasDerivAt_iterate_rem n j (continuous_rem n hc) (continuous_rem n hc')
      (periodic_rem n hp) (fun y => hasDerivAt_rem hd hc' hp n y) x

/-- For every $j$ and every function $g : \mathbb{R} \to \mathbb{R}$, there is a trigonometric
polynomial $q$ of degree at most $n$ with
$$g(x) - R_n^j g(x) = q(x) \qquad \text{for all real } x.$$
Each application of the remainder subtracts a trigonometric polynomial of degree at most $n$. -/
theorem sub_iterate_rem_mem (n : ℕ) : ∀ (j : ℕ) (g : ℝ → ℝ),
    ∃ q ∈ trigPolyLE (2 * π) n, ∀ x : ℝ,
      g x - (rem n)^[j] g x = q ((x : ℝ) : AddCircle (2 * π))
  | 0, g => ⟨0, Submodule.zero_mem _, fun x => by simp⟩
  | j + 1, g => by
    obtain ⟨q, hq, hqx⟩ := sub_iterate_rem_mem n j g
    refine ⟨q + approx n ((rem n)^[j] g),
      Submodule.add_mem _ hq (approx_mem n ((rem n)^[j] g)), fun x => ?_⟩
    rw [Function.iterate_succ_apply']
    have h : rem n ((rem n)^[j] g) x
        = (rem n)^[j] g x - approx n ((rem n)^[j] g) ((x : ℝ) : AddCircle (2 * π)) := rfl
    rw [h, ContinuousMap.add_apply, ← hqx x]
    ring

/-- Let $u$ be continuous and $2\pi$-periodic, with derivative $u'(x)$ at every $x$, and let
$L \ge 0$ be such that $|u'| \le L$. Then the remainder is at most the first absolute moment of
the kernel times $L$: $|R_n u(x)| \le \pi \sin(\theta_n/2)\, L$ for all real $x$. -/
theorem abs_rem_le_of_deriv_bound {u u' : ℝ → ℝ} (hc : Continuous u)
    (hp : Function.Periodic u (2 * π)) (hd : ∀ x, HasDerivAt u (u' x) x) {L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ x, |u' x| ≤ L) (n : ℕ) (x : ℝ) :
    |rem n u x| ≤ π * Real.sin (angle n / 2) * L := by
  have hlip : ∀ a b : ℝ, |u a - u b| ≤ L * |a - b| ^ (1 : ℝ) := by
    intro a b
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := u) (f' := u') (s := Set.univ) (C := L)
      (fun y _ => (hd y).hasDerivWithinAt) (fun y _ => by simpa [Real.norm_eq_abs] using hb y)
      convex_univ (Set.mem_univ b) (Set.mem_univ a)
    rw [Real.rpow_one]
    simpa [Real.norm_eq_abs] using h
  have h := abs_sub_approx_le_of_holder hc hp hL zero_le_one le_rfl hlip n x
  rw [Real.rpow_one] at h
  calc |rem n u x| = |u x - approx n u ((x : ℝ) : AddCircle (2 * π))| := rfl
    _ ≤ L * (π * Real.sin (angle n / 2)) := h
    _ = π * Real.sin (angle n / 2) * L := by ring

/-- **The iterated remainder of a $k$ times differentiable periodic function.** Let
$D_0, \dots, D_k$ be continuous functions on $\mathbb{R}$, with $D_0$ $2\pi$-periodic and
$D_{j+1}(x)$ the derivative of $D_j$ at $x$ for all $j < k$ and all $x$. Let $C \ge 0$ be such
that $|R_n D_k(x)| \le C$ for all $x$. Then for all real $x$
$$|R_n^{k+1} D_0(x)| \le \bigl(\pi \sin(\theta_n/2)\bigr)^k C.$$

Each of the first $k$ applications of the remainder costs one factor of the first absolute
moment $\pi \sin(\theta_n/2)$ of the kernel, by `Jackson.abs_rem_le_of_deriv_bound`, because the
remainder commutes with differentiation. -/
theorem abs_iterate_rem_le (n : ℕ) : ∀ (k : ℕ) (D : ℕ → ℝ → ℝ), (∀ j ≤ k, Continuous (D j)) →
    Function.Periodic (D 0) (2 * π) → (∀ j < k, ∀ x, HasDerivAt (D j) (D (j + 1) x) x) →
    ∀ C : ℝ, 0 ≤ C → (∀ x, |rem n (D k) x| ≤ C) →
    ∀ x, |(rem n)^[k + 1] (D 0) x| ≤ (π * Real.sin (angle n / 2)) ^ k * C
  | 0, D, _, _, _, C, _, hC, x => by simpa using hC x
  | k + 1, D, hDc, hDp, hDd, C, hC0, hC, x => by
    have hA : 0 < π * Real.sin (angle n / 2) := mul_pos Real.pi_pos (sin_half_angle_pos n)
    -- the shifted tower `D 1, …, D (k+1)` has height `k`
    have hshiftp : Function.Periodic (D 1) (2 * π) :=
      periodic_deriv hDp (hDd 0 (by omega))
    have hIH := abs_iterate_rem_le n k (fun j => D (j + 1))
      (fun j hj => hDc (j + 1) (by omega)) hshiftp
      (fun j hj y => hDd (j + 1) (by omega) y) C hC0 hC
    -- the outer remainder, applied to `u = R^[k+1] (D 0)` with derivative `R^[k+1] (D 1)`
    have hu : Continuous ((rem n)^[k + 1] (D 0)) :=
      continuous_iterate_rem n (k + 1) (hDc 0 (by omega))
    have hup : Function.Periodic ((rem n)^[k + 1] (D 0)) (2 * π) :=
      periodic_iterate_rem n (k + 1) hDp
    have hud : ∀ y, HasDerivAt ((rem n)^[k + 1] (D 0)) ((rem n)^[k + 1] (D 1) y) y :=
      hasDerivAt_iterate_rem n (k + 1) (hDc 0 (by omega)) (hDc 1 (by omega)) hDp
        (hDd 0 (by omega))
    have hbound : ∀ y, |(rem n)^[k + 1] (D 1) y| ≤ (π * Real.sin (angle n / 2)) ^ k * C :=
      fun y => hIH y
    have hLnn : (0 : ℝ) ≤ (π * Real.sin (angle n / 2)) ^ k * C := by positivity
    have hstep := abs_rem_le_of_deriv_bound hu hup hud hLnn hbound n x
    rw [Function.iterate_succ_apply' (rem n) (k + 1)]
    calc |rem n ((rem n)^[k + 1] (D 0)) x|
        ≤ π * Real.sin (angle n / 2) * ((π * Real.sin (angle n / 2)) ^ k * C) := hstep
      _ = (π * Real.sin (angle n / 2)) ^ (k + 1) * C := by ring

/-! ### Jackson's theorem -/

/-- **Jackson's theorem**, in terms of the first absolute moment $A_n = \pi \sin(\pi/(2n + 4))$ of
the kernel. Let $G$ be a continuous function on the circle of circumference $2\pi$, and let
$D_0, \dots, D_k$ be continuous functions on $\mathbb{R}$ with $D_0 = G$ (as a $2\pi$-periodic
function) and $D_{j+1}(x)$ the derivative of $D_j$ at $x$ for all $j < k$ and all $x$. Let
$M \ge 0$ and $0 \le \alpha \le 1$ be such that $|D_k(u) - D_k(v)| \le M |u - v|^\alpha$ for all
real $u$ and $v$. Then for every $n$
$$\operatorname{dist}(G, \mathcal{T}_n) \le A_n^k \cdot M A_n^\alpha,$$
where $\mathcal{T}_n$ is the space of trigonometric polynomials of degree at most $n$ and the
distance is uniform.

The derivatives are given as a tower `D 0 = Jackson.lift G`, `D (j + 1) = (D j)'`, which is the
form that the iterated remainder uses. `Jackson.infDist_le_of_holder_deriv'` states the bound
with the classical constant. -/
theorem infDist_le_of_holder_deriv {G : C(AddCircle (2 * π), ℝ)} {k n : ℕ} {M α : ℝ}
    {D : ℕ → ℝ → ℝ} (hD0 : D 0 = lift G) (hDc : ∀ j ≤ k, Continuous (D j))
    (hDd : ∀ j < k, ∀ x, HasDerivAt (D j) (D (j + 1) x) x)
    (hM : 0 ≤ M) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hhol : ∀ u v : ℝ, |D k u - D k v| ≤ M * |u - v| ^ α) :
    Metric.infDist G (trigPolyLE (2 * π) n : Set C(AddCircle (2 * π), ℝ))
      ≤ (π * Real.sin (angle n / 2)) ^ k * (M * (π * Real.sin (angle n / 2)) ^ α) := by
  have hA : 0 < π * Real.sin (angle n / 2) := mul_pos Real.pi_pos (sin_half_angle_pos n)
  have hDp : Function.Periodic (D 0) (2 * π) := hD0 ▸ periodic_lift G
  have hDjp : ∀ j ≤ k, Function.Periodic (D j) (2 * π) := by
    intro j
    induction j with
    | zero => intro _; exact hDp
    | succ i ih => intro hi; exact periodic_deriv (ih (by omega)) (hDd i (by omega))
  have hC0 : (0 : ℝ) ≤ M * (π * Real.sin (angle n / 2)) ^ α :=
    mul_nonneg hM (Real.rpow_nonneg hA.le _)
  have hCtop : ∀ x, |rem n (D k) x| ≤ M * (π * Real.sin (angle n / 2)) ^ α := fun x =>
    abs_sub_approx_le_of_holder (hDc k le_rfl) (hDjp k le_rfl) hM hα0 hα1 hhol n x
  have hmain := abs_iterate_rem_le n k D hDc hDp hDd _ hC0 hCtop
  obtain ⟨q, hq, hqx⟩ := sub_iterate_rem_mem n (k + 1) (D 0)
  have hnorm : ‖G - q‖ ≤ (π * Real.sin (angle n / 2)) ^ k *
      (M * (π * Real.sin (angle n / 2)) ^ α) := by
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun z => ?_
    induction z using QuotientAddGroup.induction_on with
    | _ x =>
      have h := hqx x
      have hG : G ((x : ℝ) : AddCircle (2 * π)) = D 0 x := by rw [hD0]
      have hval : (G - q) ((x : ℝ) : AddCircle (2 * π)) = (rem n)^[k + 1] (D 0) x := by
        rw [ContinuousMap.sub_apply, hG]
        linarith [h]
      rw [Real.norm_eq_abs, hval]
      exact hmain x
  calc Metric.infDist G (trigPolyLE (2 * π) n : Set C(AddCircle (2 * π), ℝ))
      ≤ dist G q := Metric.infDist_le_dist_of_mem hq
    _ = ‖G - q‖ := dist_eq_norm _ _
    _ ≤ _ := hnorm

/-- For $n \ge 1$, $M \ge 0$ and $0 \le \alpha \le 1$, the bound of
`Jackson.infDist_le_of_holder_deriv` is at most the classical one:
$$A_n^k \cdot M A_n^\alpha \le \frac{(1 + \pi^2/2)^{k+1} M}{n^{k+\alpha}}, \qquad A_n = \pi
  \sin(\theta_n/2).$$
The first absolute moment satisfies $n A_n \le \pi^2/2 < 1 + \pi^2/2$. -/
theorem moment_pow_le (n k : ℕ) (hn : 1 ≤ n) {M α : ℝ} (hM : 0 ≤ M) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) :
    (π * Real.sin (angle n / 2)) ^ k * (M * (π * Real.sin (angle n / 2)) ^ α)
      ≤ (1 + π ^ 2 / 2) ^ (k + 1) * M / (n : ℝ) ^ ((k : ℝ) + α) := by
  have hpi := Real.pi_pos
  have hA : 0 < π * Real.sin (angle n / 2) := mul_pos hpi (sin_half_angle_pos n)
  set A : ℝ := π * Real.sin (angle n / 2) with hAdef
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hc1 : (1 : ℝ) ≤ 1 + π ^ 2 / 2 := by nlinarith
  have hKnn : (0 : ℝ) ≤ (k : ℝ) + α := by positivity
  -- `n A ≤ π² / 2`
  have hnA : (n : ℝ) * A ≤ π ^ 2 / 2 := by
    have h := pi_mul_sin_half_angle_le n
    rw [← hAdef] at h
    have h2 : (n : ℝ) * A ≤ (n : ℝ) * (π ^ 2 / (2 * ((n : ℝ) + 2))) := by
      exact mul_le_mul_of_nonneg_left h hn0.le
    have h3 : (n : ℝ) * (π ^ 2 / (2 * ((n : ℝ) + 2))) ≤ π ^ 2 / 2 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
      nlinarith [Real.pi_pos, sq_nonneg π, hn0]
    linarith
  -- the whole constant, in rpow form
  have hpow : A ^ k * A ^ α = A ^ ((k : ℝ) + α) := by
    rw [Real.rpow_add hA, Real.rpow_natCast]
  have hmul : (A * (n : ℝ)) ^ ((k : ℝ) + α) = A ^ ((k : ℝ) + α) * (n : ℝ) ^ ((k : ℝ) + α) :=
    Real.mul_rpow hA.le hn0.le
  have hstep : (A * (n : ℝ)) ^ ((k : ℝ) + α) ≤ (1 + π ^ 2 / 2) ^ ((k : ℝ) + α) := by
    refine Real.rpow_le_rpow (by positivity) ?_ hKnn
    calc A * (n : ℝ) = (n : ℝ) * A := by ring
      _ ≤ π ^ 2 / 2 := hnA
      _ ≤ 1 + π ^ 2 / 2 := by linarith
  have hstep2 : (1 + π ^ 2 / 2) ^ ((k : ℝ) + α) ≤ (1 + π ^ 2 / 2) ^ ((k : ℝ) + 1) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by linarith)
  have hstep3 : (1 + π ^ 2 / 2) ^ ((k : ℝ) + 1) = (1 + π ^ 2 / 2) ^ (k + 1) := by
    rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hfinal : A ^ ((k : ℝ) + α) * (n : ℝ) ^ ((k : ℝ) + α) ≤ (1 + π ^ 2 / 2) ^ (k + 1) := by
    rw [← hmul, ← hstep3]
    exact hstep.trans hstep2
  have hnpos : (0 : ℝ) < (n : ℝ) ^ ((k : ℝ) + α) := Real.rpow_pos_of_pos hn0 _
  rw [le_div_iff₀ hnpos]
  calc A ^ k * (M * A ^ α) * (n : ℝ) ^ ((k : ℝ) + α)
      = M * (A ^ ((k : ℝ) + α) * (n : ℝ) ^ ((k : ℝ) + α)) := by rw [← hpow]; ring
    _ ≤ M * (1 + π ^ 2 / 2) ^ (k + 1) := mul_le_mul_of_nonneg_left hfinal hM
    _ = (1 + π ^ 2 / 2) ^ (k + 1) * M := by ring

/-- **Jackson's theorem.** Let $G$ be a continuous function on the circle of circumference $2\pi$,
and let $D_0, \dots, D_k$ be continuous functions on $\mathbb{R}$ with $D_0 = G$ (as a
$2\pi$-periodic function) and $D_{j+1}(x)$ the derivative of $D_j$ at $x$ for all $j < k$ and
all $x$. Let $M \ge 0$ and $0 \le \alpha \le 1$ be such that the $k$-th derivative satisfies the
Hölder condition $|D_k(u) - D_k(v)| \le M |u - v|^\alpha$ for all real $u$ and $v$. Then for
every $n \ge 1$ the error of the best uniform approximation of $G$ by trigonometric polynomials
of degree at most $n$ satisfies
$$\rho_n(G) = \operatorname{dist}(G, \mathcal{T}_n) \le \frac{c^{k+1} M}{n^{k+\alpha}}, \qquad
  c = 1 + \frac{\pi^2}{2}.$$
This is Theorem 3.7.1 of [han2009theoretical].

The space $\mathcal{T}_n$ is `trigPolyLE (2 * π) n`, and the tower of derivatives starts with
`D 0 = Jackson.lift G`. The proof uses the Fejér–Korovkin kernel: its first absolute moment is
$A_n \le \pi^2/(2n + 4)$, each of the $k$ applications of the remainder `Jackson.rem` costs a
factor $A_n$ because the operator commutes with differentiation, and the last application costs
$M A_n^\alpha$. -/
theorem infDist_le_of_holder_deriv' {G : C(AddCircle (2 * π), ℝ)} {k n : ℕ} {M α : ℝ}
    {D : ℕ → ℝ → ℝ} (hn : 1 ≤ n) (hD0 : D 0 = lift G) (hDc : ∀ j ≤ k, Continuous (D j))
    (hDd : ∀ j < k, ∀ x, HasDerivAt (D j) (D (j + 1) x) x)
    (hM : 0 ≤ M) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hhol : ∀ u v : ℝ, |D k u - D k v| ≤ M * |u - v| ^ α) :
    Metric.infDist G (trigPolyLE (2 * π) n : Set C(AddCircle (2 * π), ℝ))
      ≤ (1 + π ^ 2 / 2) ^ (k + 1) * M / (n : ℝ) ^ ((k : ℝ) + α) :=
  (infDist_le_of_holder_deriv hD0 hDc hDd hM hα0 hα1 hhol).trans
    (moment_pow_le n k hn hM hα0 hα1)

/-!
### Jackson's theorem for algebraic polynomials

The uniform approximation of a function on $[-1, 1]$ by algebraic polynomials reduces to the
periodic problem through $x = \cos\theta$. A continuous $f$ on $[-1, 1]$ pulls back to the even
periodic function $\theta \mapsto f(\cos\theta)$, and the even part of a trigonometric polynomial of
degree at most $n$ is $p(\cos\theta)$ for an algebraic polynomial $p$ of degree at most $n$
(`Jackson.exists_degree_le_eval_cos`). So the best algebraic approximation on $[-1, 1]$ is at least
as good as the best trigonometric approximation of the pullback. The Hölder constant does not
change, because $\cos$ is $1$-Lipschitz.
-/

section Algebraic

open scoped Polynomial

/-- The point $\cos\theta$ of $[-1, 1]$. -/
noncomputable def cosIcc (θ : ℝ) : Set.Icc (-1 : ℝ) 1 :=
  ⟨Real.cos θ, ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩⟩

/-- The point `Jackson.cosIcc θ` is the real number $\cos\theta$. -/
@[simp]
theorem cosIcc_coe (θ : ℝ) : (cosIcc θ : ℝ) = Real.cos θ := rfl

/-- The point $\cos\theta$ of $[-1, 1]$ is even in $\theta$: $\cos(-\theta) = \cos\theta$. -/
@[simp]
theorem cosIcc_neg (θ : ℝ) : cosIcc (-θ) = cosIcc θ := Subtype.ext (Real.cos_neg θ)

/-- **The Chebyshev correspondence.** Let $q$ be a trigonometric polynomial of degree at most $n$ on
the circle of circumference $2\pi$. Then there is an algebraic polynomial $P$ of degree at most
$n$ with
$$P(\cos\theta) = \frac{q(\theta) + q(-\theta)}{2} \qquad \text{for all real } \theta.$$

The members of the real trigonometric system `trigFun` of positive index are
$\sqrt{2}\, T_j \circ \cos$, those of negative index are odd, and the constant is
$T_0 \circ \cos$. -/
theorem exists_degree_le_eval_cos {n : ℕ} {q : C(AddCircle (2 * π), ℝ)}
    (hq : q ∈ trigPolyLE (2 * π) n) :
    ∃ P : ℝ[X], P.degree ≤ (n : ℕ) ∧
      ∀ θ : ℝ, P.eval (Real.cos θ) = (q ↑θ + q ↑(-θ)) / 2 := by
  induction hq using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨m, hm, rfl⟩ := hv
    rw [mem_Icc_iff_natAbs_le] at hm
    rcases lt_trichotomy m 0 with hneg | rfl | hpos
    · refine ⟨0, by simp, fun θ => ?_⟩
      rw [Polynomial.eval_zero, trigFun_coe_of_neg hneg, trigFun_coe_of_neg hneg,
        show -(m : ℝ) * -θ = -(-(m : ℝ) * θ) by ring, Real.sin_neg]
      ring
    · refine ⟨1, by simp, fun θ => ?_⟩
      rw [Polynomial.eval_one, trigFun_zero]
      norm_num
    · refine ⟨(√2 : ℝ) • Polynomial.Chebyshev.T ℝ m, ?_, fun θ => ?_⟩
      · refine (Polynomial.degree_smul_le _ _).trans ?_
        rw [Polynomial.Chebyshev.degree_T]
        exact_mod_cast hm
      · rw [Polynomial.eval_smul, Polynomial.Chebyshev.T_real_cos, smul_eq_mul,
          trigFun_coe_of_pos hpos, trigFun_coe_of_pos hpos,
          show (m : ℝ) * -θ = -((m : ℝ) * θ) by ring, Real.cos_neg]
        ring
  | zero => exact ⟨0, by simp, fun θ => by simp⟩
  | add v w _ _ hv hw =>
    obtain ⟨P, hPdeg, hPval⟩ := hv
    obtain ⟨Q, hQdeg, hQval⟩ := hw
    refine ⟨P + Q, (Polynomial.degree_add_le _ _).trans (max_le hPdeg hQdeg), fun θ => ?_⟩
    rw [Polynomial.eval_add, hPval, hQval]
    simp only [ContinuousMap.add_apply]
    ring
  | smul c v _ hv =>
    obtain ⟨P, hPdeg, hPval⟩ := hv
    refine ⟨c • P, (Polynomial.degree_smul_le _ _).trans hPdeg, fun θ => ?_⟩
    rw [Polynomial.eval_smul, hPval, smul_eq_mul]
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    ring

/-- **The best algebraic approximation on $[-1, 1]$ is at least as good as the best trigonometric
approximation of the pullback along $\cos$.** Let $f$ be continuous on $[-1, 1]$, and let $G$ be
a continuous function on the circle of circumference $2\pi$ with $G(\theta) = f(\cos\theta)$ for
all real $\theta$. Then
$$\operatorname{dist}(f, \mathcal{P}_n) \le \operatorname{dist}(G, \mathcal{T}_n),$$
where $\mathcal{P}_n$ is the space of polynomials of degree at most $n$ on $[-1, 1]$,
$\mathcal{T}_n$ is the space of trigonometric polynomials of degree at most $n$, and both
distances are uniform.

The spaces are `polyLE (Set.Icc (-1) 1) n` and `trigPolyLE (2 * π) n`. -/
theorem infDist_polyLE_le_infDist_trigPolyLE {n : ℕ} {f : C(Set.Icc (-1 : ℝ) 1, ℝ)}
    {G : C(AddCircle (2 * π), ℝ)} (hG : ∀ θ : ℝ, G ↑θ = f (cosIcc θ)) :
    Metric.infDist f (polyLE (Set.Icc (-1 : ℝ) 1) n : Set C(Set.Icc (-1 : ℝ) 1, ℝ))
      ≤ Metric.infDist G (trigPolyLE (2 * π) n : Set C(AddCircle (2 * π), ℝ)) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨q, hq, hdist⟩ :=
    (Metric.infDist_lt_iff (s := (trigPolyLE (2 * π) n : Set C(AddCircle (2 * π), ℝ)))
      ⟨0, (trigPolyLE (2 * π) n).zero_mem⟩).1 (lt_add_of_pos_right _ hε)
  obtain ⟨P, hPdeg, hPval⟩ := exists_degree_le_eval_cos hq
  set p : C(Set.Icc (-1 : ℝ) 1, ℝ) := P.toContinuousMapOn (Set.Icc (-1 : ℝ) 1) with hpdef
  have hpmem : p ∈ polyLE (Set.Icc (-1 : ℝ) 1) n :=
    mem_polyLE_iff.2 ⟨P, hPdeg, fun t => rfl⟩
  have hbound : ∀ x : Set.Icc (-1 : ℝ) 1, |f x - p x| ≤ ‖G - q‖ := by
    intro x
    have hx : Real.cos (Real.arccos (x : ℝ)) = (x : ℝ) := Real.cos_arccos x.2.1 x.2.2
    set θ := Real.arccos (x : ℝ) with hθ
    have hxeq : x = cosIcc θ := Subtype.ext hx.symm
    have hGθ : G ↑θ = f x := by rw [hG θ, hxeq]
    have hGnθ : G ↑(-θ) = f x := by rw [hG (-θ), cosIcc_neg, hxeq]
    have hpx : p x = (q ↑θ + q ↑(-θ)) / 2 := by
      rw [hpdef]
      change P.eval (x : ℝ) = _
      rw [← hx, hPval θ]
    have hq1 : |G ↑θ - q ↑θ| ≤ ‖G - q‖ := by
      simpa [Real.norm_eq_abs] using (G - q).norm_coe_le_norm (↑θ : AddCircle (2 * π))
    have hq2 : |G ↑(-θ) - q ↑(-θ)| ≤ ‖G - q‖ := by
      simpa [Real.norm_eq_abs] using (G - q).norm_coe_le_norm (↑(-θ) : AddCircle (2 * π))
    have hsplit : f x - p x
        = ((G ↑θ - q ↑θ) + (G ↑(-θ) - q ↑(-θ))) / 2 := by
      rw [hpx, hGθ, hGnθ]
      ring
    rw [hsplit]
    calc |((G ↑θ - q ↑θ) + (G ↑(-θ) - q ↑(-θ))) / 2|
        ≤ (|G ↑θ - q ↑θ| + |G ↑(-θ) - q ↑(-θ)|) / 2 := by
          rw [abs_div, abs_two]
          exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
      _ ≤ ‖G - q‖ := by linarith
  calc Metric.infDist f (polyLE (Set.Icc (-1 : ℝ) 1) n : Set C(Set.Icc (-1 : ℝ) 1, ℝ))
      ≤ dist f p := Metric.infDist_le_dist_of_mem hpmem
    _ = ‖f - p‖ := dist_eq_norm _ _
    _ ≤ ‖G - q‖ := by
        rw [ContinuousMap.norm_le _ (norm_nonneg _)]
        intro x
        simpa [Real.norm_eq_abs] using hbound x
    _ = dist G q := (dist_eq_norm _ _).symm
    _ ≤ _ := hdist.le

/-- **Jackson's theorem for algebraic polynomials, the Hölder case.** Let $f$ be continuous on
$[-1, 1]$, and let $M \ge 0$ and $0 \le \alpha \le 1$ be such that
$|f(u) - f(v)| \le M |u - v|^\alpha$ for all $u, v \in [-1, 1]$. Then for every $n$
$$\operatorname{dist}(f, \mathcal{P}_n) \le M \bigl(\pi \sin(\pi/(2n + 4))\bigr)^\alpha,$$
where $\mathcal{P}_n$ is the space of polynomials of degree at most $n$ on $[-1, 1]$ and the
distance is uniform.

This is the same bound as in the periodic case: the pullback $\theta \mapsto f(\cos\theta)$ has
the same Hölder constant, because $\cos$ is $1$-Lipschitz. -/
theorem infDist_polyLE_le_of_holder {f : C(Set.Icc (-1 : ℝ) 1, ℝ)} {M α : ℝ} (hM : 0 ≤ M)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hf : ∀ u v : Set.Icc (-1 : ℝ) 1, |f u - f v| ≤ M * |(u : ℝ) - (v : ℝ)| ^ α) (n : ℕ) :
    Metric.infDist f (polyLE (Set.Icc (-1 : ℝ) 1) n : Set C(Set.Icc (-1 : ℝ) 1, ℝ))
      ≤ M * (π * Real.sin (angle n / 2)) ^ α := by
  have hcont : Continuous fun θ : ℝ => f (cosIcc θ) :=
    f.continuous.comp (Real.continuous_cos.subtype_mk _)
  have hper : Function.Periodic (fun θ : ℝ => f (cosIcc θ)) (2 * π) := fun θ => by
    simp only []
    congr 1
    exact Subtype.ext (Real.cos_add_two_pi θ)
  set G : C(AddCircle (2 * π), ℝ) := ⟨hper.lift, continuous_quot_lift _ hcont⟩ with hGdef
  have hG : ∀ θ : ℝ, G ↑θ = f (cosIcc θ) := fun θ => hper.lift_coe θ
  refine (infDist_polyLE_le_infDist_trigPolyLE hG).trans ?_
  refine infDist_le_of_holder hM hα0 hα1 (fun u v => ?_) n
  have hcos : |Real.cos u - Real.cos v| ≤ |u - v| := by
    simpa [Real.dist_eq] using
      (Real.lipschitzWith_cos.dist_le_mul u v)
  calc |lift G u - lift G v| = |f (cosIcc u) - f (cosIcc v)| := by
        simp only [lift, hG]
    _ ≤ M * |(cosIcc u : ℝ) - (cosIcc v : ℝ)| ^ α := hf _ _
    _ ≤ M * |u - v| ^ α := by
        refine mul_le_mul_of_nonneg_left ?_ hM
        exact Real.rpow_le_rpow (abs_nonneg _) hcos hα0

/-!
### The step down in the degree

For algebraic polynomials, the antiderivative of a polynomial of degree at most $n - 1$ is a
polynomial of degree at most $n$. No mean has to be subtracted, as it has to be in the periodic
case, so the recursion $\rho_n(u) \le c\, \rho_{n-1}(u')/n$ loses nothing.
-/

/-- **A polynomial has a polynomial antiderivative** of degree one higher: if $Q$ is a real
polynomial of degree at most $m$, then there is a real polynomial $R$ of degree at most $m + 1$
with $R' = Q$. -/
theorem exists_derivative_eq {Q : ℝ[X]} {m : ℕ} (hQ : Q.degree ≤ (m : ℕ)) :
    ∃ R : ℝ[X], R.degree ≤ ((m + 1 : ℕ) : ℕ) ∧ Polynomial.derivative R = Q := by
  refine ⟨∑ i ∈ Finset.range (m + 1),
    Polynomial.C (Q.coeff i / (i + 1)) * Polynomial.X ^ (i + 1), ?_, ?_⟩
  · refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun i hi => ?_)
    have hi' : i + 1 ≤ m + 1 := Nat.succ_le_succ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    calc (Polynomial.C (Q.coeff i / (i + 1)) * Polynomial.X ^ (i + 1)).degree
        ≤ (Polynomial.C (Q.coeff i / (i + 1)) : ℝ[X]).degree
            + (Polynomial.X ^ (i + 1) : ℝ[X]).degree := Polynomial.degree_mul_le _ _
      _ ≤ 0 + ((i + 1 : ℕ) : WithBot ℕ) := by
          gcongr
          · exact Polynomial.degree_C_le
          · rw [Polynomial.degree_X_pow]
      _ = ((i + 1 : ℕ) : WithBot ℕ) := zero_add _
      _ ≤ ((m + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast hi'
  · have hnat : Q.natDegree < m + 1 :=
      Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_degree_le.2 hQ)
    have hQsum : ∑ i ∈ Finset.range (m + 1), Polynomial.C (Q.coeff i) * Polynomial.X ^ i = Q :=
      (Polynomial.as_sum_range_C_mul_X_pow' Q hnat).symm
    rw [map_sum]
    conv_rhs => rw [← hQsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hne : ((i : ℝ) + 1) ≠ 0 := by positivity
    rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow, Nat.add_sub_cancel,
      ← mul_assoc, ← Polynomial.C_mul]
    congr 2
    push_cast
    field_simp

/-- **Translation by a member of a subspace does not change the distance to it.** Let $S$ be a
subspace of a real normed space $V$, and let $w \in S$. Then $\operatorname{dist}(u - w, S) =
\operatorname{dist}(u, S)$ for every $u \in V$. -/
theorem infDist_sub_mem {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : Submodule ℝ V} {w : V}
    (hw : w ∈ S) (u : V) :
    Metric.infDist (u - w) (S : Set V) = Metric.infDist u (S : Set V) := by
  have key : ∀ a b : V, b ∈ S →
      Metric.infDist (a - b) (S : Set V) ≤ Metric.infDist a (S : Set V) := by
    intro a b hb
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨s, hs, hlt⟩ := (Metric.infDist_lt_iff (s := (S : Set V)) ⟨0, S.zero_mem⟩).1
      (lt_add_of_pos_right (Metric.infDist a (S : Set V)) hε)
    calc Metric.infDist (a - b) (S : Set V) ≤ dist (a - b) (s - b) :=
          Metric.infDist_le_dist_of_mem (S.sub_mem hs hb)
      _ = dist a s := by rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right]
      _ ≤ _ := hlt.le
  refine le_antisymm (key u w hw) ?_
  simpa using key (u - w) (-w) (S.neg_mem hw)

/-- A function $u$ that is continuous on $[-1, 1]$, as a continuous function on the compact space
$[-1, 1]$. -/
noncomputable def restrictIcc {u : ℝ → ℝ} (hu : ContinuousOn u (Set.Icc (-1 : ℝ) 1)) :
    C(Set.Icc (-1 : ℝ) 1, ℝ) :=
  ⟨fun x => u x, hu.domRestrict⟩

/-- The value of `Jackson.restrictIcc hu` at a point $x$ of $[-1, 1]$ is $u(x)$. -/
@[simp]
theorem restrictIcc_apply {u : ℝ → ℝ} (hu : ContinuousOn u (Set.Icc (-1 : ℝ) 1))
    (x : Set.Icc (-1 : ℝ) 1) : restrictIcc hu x = u x := rfl

/-- **One step of the recursion in Jackson's theorem on $[-1, 1]$.** Let $u$ and $u'$ be continuous
on $[-1, 1]$, and let $u'(x)$ be the derivative of $u$ within $[-1, 1]$ at every
$x \in [-1, 1]$. Then for every $n$
$$\operatorname{dist}(u, \mathcal{P}_{n+1}) \le \pi \sin(\theta_{n+1}/2)\,
  \operatorname{dist}(u', \mathcal{P}_n),$$
where $\mathcal{P}_n$ is the space of polynomials of degree at most $n$ on $[-1, 1]$,
$\theta_{n+1} = \pi/(n + 3)$, and the distances are uniform.

The antiderivative $R$ of a best approximation $q$ of $u'$ is a polynomial of degree at most
$n + 1$. By the mean value theorem, $u - R$ is Lipschitz with constant $\|u' - q\|$, so the
Hölder case applies to it with exponent $1$. -/
theorem infDist_restrictIcc_le_step {u u' : ℝ → ℝ}
    (hu : ContinuousOn u (Set.Icc (-1 : ℝ) 1)) (hu' : ContinuousOn u' (Set.Icc (-1 : ℝ) 1))
    (hd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, HasDerivWithinAt u (u' x) (Set.Icc (-1 : ℝ) 1) x) (n : ℕ) :
    Metric.infDist (restrictIcc hu)
        (polyLE (Set.Icc (-1 : ℝ) 1) (n + 1) : Set C(Set.Icc (-1 : ℝ) 1, ℝ))
      ≤ (π * Real.sin (angle (n + 1) / 2)) *
          Metric.infDist (restrictIcc hu')
            (polyLE (Set.Icc (-1 : ℝ) 1) n : Set C(Set.Icc (-1 : ℝ) 1, ℝ)) := by
  set c : ℝ := π * Real.sin (angle (n + 1) / 2) with hcdef
  have hc : 0 < c := mul_pos Real.pi_pos (sin_half_angle_pos _)
  set E : ℝ := Metric.infDist (restrictIcc hu')
    (polyLE (Set.Icc (-1 : ℝ) 1) n : Set C(Set.Icc (-1 : ℝ) 1, ℝ)) with hEdef
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨q, hq, hlt⟩ :=
    (Metric.infDist_lt_iff (s := (polyLE (Set.Icc (-1 : ℝ) 1) n : Set C(Set.Icc (-1 : ℝ) 1, ℝ)))
      ⟨0, Submodule.zero_mem _⟩).1 (lt_add_of_pos_right E (by positivity : (0 : ℝ) < ε / c))
  obtain ⟨Q, hQdeg, hQval⟩ := mem_polyLE_iff.1 hq
  obtain ⟨R, hRdeg, hRd⟩ := exists_derivative_eq hQdeg
  set K : ℝ := dist (restrictIcc hu') q with hKdef
  have hK0 : 0 ≤ K := dist_nonneg
  have hRcont : ContinuousOn (fun x : ℝ => R.eval x) (Set.Icc (-1 : ℝ) 1) :=
    R.continuous_aeval.continuousOn
  have hvc : ContinuousOn (fun x : ℝ => u x - R.eval x) (Set.Icc (-1 : ℝ) 1) := hu.sub hRcont
  have hvd : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun t : ℝ => u t - R.eval t) (u' x - Q.eval x)
        (Set.Icc (-1 : ℝ) 1) x := by
    intro x hx
    have hR : HasDerivWithinAt (fun t : ℝ => R.eval t) (Q.eval x) (Set.Icc (-1 : ℝ) 1) x := by
      have h := R.hasDerivAt (𝕜 := ℝ) x
      rw [hRd] at h
      exact h.hasDerivWithinAt
    exact (hd x hx).sub hR
  have hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖u' x - Q.eval x‖ ≤ K := by
    intro x hx
    have h := (restrictIcc hu' - q).norm_coe_le_norm ⟨x, hx⟩
    rw [hKdef, dist_eq_norm]
    simpa [Real.norm_eq_abs, hQval ⟨x, hx⟩] using h
  have hlip : ∀ a b : Set.Icc (-1 : ℝ) 1,
      |restrictIcc hvc a - restrictIcc hvc b| ≤ K * |(a : ℝ) - (b : ℝ)| ^ (1 : ℝ) := by
    intro a b
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f' := fun x => u' x - Q.eval x)
      hvd hbound (convex_Icc (-1 : ℝ) 1) b.2 a.2
    rw [Real.rpow_one]
    simpa [Real.norm_eq_abs] using h
  have hmain := infDist_polyLE_le_of_holder (f := restrictIcc hvc) hK0 zero_le_one le_rfl
    hlip (n + 1)
  rw [Real.rpow_one] at hmain
  have hRmem : R.toContinuousMapOn (Set.Icc (-1 : ℝ) 1) ∈ polyLE (Set.Icc (-1 : ℝ) 1) (n + 1) :=
    mem_polyLE_iff.2 ⟨R, by exact_mod_cast hRdeg, fun t => rfl⟩
  have hsub : restrictIcc hvc = restrictIcc hu - R.toContinuousMapOn (Set.Icc (-1 : ℝ) 1) := by
    ext x
    simp only [restrictIcc_apply, ContinuousMap.sub_apply, Polynomial.toContinuousMapOn_apply,
      Polynomial.toContinuousMap_apply]
  rw [hsub, infDist_sub_mem hRmem] at hmain
  calc Metric.infDist (restrictIcc hu)
        (polyLE (Set.Icc (-1 : ℝ) 1) (n + 1) : Set C(Set.Icc (-1 : ℝ) 1, ℝ))
      ≤ K * c := hmain
    _ ≤ (E + ε / c) * c := by
        exact mul_le_mul_of_nonneg_right hlt.le hc.le
    _ = c * E + ε := by field_simp

/-- **The recursion iterated.** Let $k \le n$, and let $D_0, \dots, D_k$ be continuous on $[-1, 1]$,
with $D_{j+1}(x)$ the derivative of $D_j$ within $[-1, 1]$ at every $x \in [-1, 1]$, for all
$j < k$. Then
$$\operatorname{dist}(D_0, \mathcal{P}_n) \le \Bigl(\prod_{i=0}^{k-1} \pi
  \sin(\theta_{n-i}/2)\Bigr) \operatorname{dist}(D_k, \mathcal{P}_{n-k}),$$
where $\mathcal{P}_m$ is the space of polynomials of degree at most $m$ on $[-1, 1]$ and the
distances are uniform. -/
theorem infDist_restrictIcc_le_prod : ∀ (k n : ℕ) (_ : k ≤ n) (D : ℕ → ℝ → ℝ)
    (hDc : ∀ j ≤ k, ContinuousOn (D j) (Set.Icc (-1 : ℝ) 1))
    (_ : ∀ j < k, ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      HasDerivWithinAt (D j) (D (j + 1) x) (Set.Icc (-1 : ℝ) 1) x),
    Metric.infDist (restrictIcc (hDc 0 (Nat.zero_le k)))
        (polyLE (Set.Icc (-1 : ℝ) 1) n : Set C(Set.Icc (-1 : ℝ) 1, ℝ))
      ≤ (∏ i ∈ Finset.range k, (π * Real.sin (angle (n - i) / 2))) *
          Metric.infDist (restrictIcc (hDc k le_rfl))
            (polyLE (Set.Icc (-1 : ℝ) 1) (n - k) : Set C(Set.Icc (-1 : ℝ) 1, ℝ)) := by
  intro k
  induction k with
  | zero => intro n _ D hDc _; simp
  | succ k ih =>
    intro n hkn D hDc hDd
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
    have hkm : k ≤ m := by omega
    have hD'c : ∀ j ≤ k, ContinuousOn (D (j + 1)) (Set.Icc (-1 : ℝ) 1) := fun j hj =>
      hDc (j + 1) (by omega)
    have hD'd : ∀ j < k, ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        HasDerivWithinAt (D (j + 1)) (D (j + 1 + 1) x) (Set.Icc (-1 : ℝ) 1) x := fun j hj =>
      hDd (j + 1) (by omega)
    have hstep := infDist_restrictIcc_le_step (hDc 0 (Nat.zero_le _)) (hDc 1 (by omega))
      (hDd 0 (by omega)) m
    have hrec := ih m hkm (fun j => D (j + 1)) hD'c hD'd
    have hprod : ∏ i ∈ Finset.range (k + 1), (π * Real.sin (angle (m + 1 - i) / 2))
        = (π * Real.sin (angle (m + 1) / 2)) *
            ∏ i ∈ Finset.range k, (π * Real.sin (angle (m - i) / 2)) := by
      rw [Finset.prod_range_succ' (fun i => π * Real.sin (angle (m + 1 - i) / 2)) k]
      simp only [Nat.sub_zero, Nat.succ_sub_succ]
      ring
    have hnn : (0 : ℝ) ≤ π * Real.sin (angle (m + 1) / 2) :=
      (mul_pos Real.pi_pos (sin_half_angle_pos _)).le
    rw [hprod, show m + 1 - (k + 1) = m - k from Nat.succ_sub_succ m k, mul_assoc]
    exact hstep.trans (mul_le_mul_of_nonneg_left hrec hnn)

/-- **Jackson's theorem for algebraic polynomials.** Let $k < n$, and let $D_0, \dots, D_k$ be
continuous on $[-1, 1]$, with $D_{j+1}(x)$ the derivative of $D_j$ within $[-1, 1]$ at every
$x \in [-1, 1]$, for all $j < k$. Let $M \ge 0$ and $0 \le \alpha \le 1$ be such that
$|D_k(u) - D_k(v)| \le M |u - v|^\alpha$ for all $u, v \in [-1, 1]$. Let $f$ be the continuous
function on $[-1, 1]$ with $f = D_0$ there, and let
$$d \ge \frac{n^{k+\alpha}}{n (n - 1) \cdots (n - k + 1)\, (n - k)^\alpha}.$$
Then the error of the best uniform approximation of $f$ by polynomials of degree at most $n$
satisfies
$$\rho_n(f) = \operatorname{dist}(f, \mathcal{P}_n) \le \frac{d\, c^{k+1} M}{n^{k+\alpha}},
  \qquad c = 1 + \frac{\pi^2}{2}.$$

The proof is the recursion `Jackson.infDist_restrictIcc_le_prod` down the tower, which costs
$\pi \sin(\theta_{n-i}/2) \le (\pi^2/2)/(n - i)$ per step, and the Hölder case at degree $n - k$
closes it. So the constant that is actually proved is $(\pi^2/2)^{k+1}$, smaller than the
classical $(1 + \pi^2/2)^{k+1}$. -/
theorem infDist_le_of_holder_poly {k n : ℕ} {M α d : ℝ} {D : ℕ → ℝ → ℝ}
    {f : C(Set.Icc (-1 : ℝ) 1, ℝ)} (hf : ∀ x : Set.Icc (-1 : ℝ) 1, f x = D 0 x)
    (hDc : ∀ j ≤ k, ContinuousOn (D j) (Set.Icc (-1 : ℝ) 1))
    (hDd : ∀ j < k, ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      HasDerivWithinAt (D j) (D (j + 1) x) (Set.Icc (-1 : ℝ) 1) x)
    (hM : 0 ≤ M) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hhol : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      |D k u - D k v| ≤ M * |u - v| ^ α)
    (hkn : k < n)
    (hd : (n : ℝ) ^ ((k : ℝ) + α) /
        ((∏ i ∈ Finset.range k, ((n : ℝ) - i)) * ((n : ℝ) - k) ^ α) ≤ d) :
    Metric.infDist f (polyLE (Set.Icc (-1 : ℝ) 1) n : Set C(Set.Icc (-1 : ℝ) 1, ℝ))
      ≤ d * (1 + π ^ 2 / 2) ^ (k + 1) * M / (n : ℝ) ^ ((k : ℝ) + α) := by
  have hpi := Real.pi_pos
  have hpi2 : (1 : ℝ) ≤ π ^ 2 / 2 := by nlinarith [Real.two_le_pi]
  have hkR : (k : ℝ) < n := by exact_mod_cast hkn
  have hnk : (0 : ℝ) < (n : ℝ) - k := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (Nat.cast_nonneg k) hkR
  have hfac : ∀ i ∈ Finset.range k, (0 : ℝ) < (n : ℝ) - i := by
    intro i hi
    have : (i : ℝ) < n := by exact_mod_cast lt_trans (Finset.mem_range.1 hi) hkn
    linarith
  set P : ℝ := ∏ i ∈ Finset.range k, ((n : ℝ) - i) with hPdef
  have hP : 0 < P := Finset.prod_pos hfac
  set S : ℝ := ((n : ℝ) - k) ^ α with hSdef
  have hS : 0 < S := Real.rpow_pos_of_pos hnk α
  -- the size of one step of the recursion
  have hc : ∀ m : ℕ, 0 < m → π * Real.sin (angle m / 2) ≤ π ^ 2 / 2 / (m : ℝ) := by
    intro m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    refine (pi_mul_sin_half_angle_le m).trans ?_
    rw [div_le_div_iff₀ (by positivity) hm']
    nlinarith
  have hcast : ∀ i : ℕ, i ≤ n → ((n - i : ℕ) : ℝ) = (n : ℝ) - i := fun i hi => by
    push_cast [Nat.cast_sub hi]
    ring
  -- the recursion, closed by the Hölder case at the bottom
  have hfeq : f = restrictIcc (hDc 0 (Nat.zero_le k)) := by
    ext x
    exact hf x
  have hhol' : ∀ a b : Set.Icc (-1 : ℝ) 1,
      |restrictIcc (hDc k le_rfl) a - restrictIcc (hDc k le_rfl) b|
        ≤ M * |(a : ℝ) - (b : ℝ)| ^ α := fun a b => hhol a a.2 b b.2
  have hPnn : (0 : ℝ) ≤ ∏ i ∈ Finset.range k, (π * Real.sin (angle (n - i) / 2)) :=
    Finset.prod_nonneg fun i _ => (mul_pos hpi (sin_half_angle_pos _)).le
  have hstep1 : Metric.infDist f
        (polyLE (Set.Icc (-1 : ℝ) 1) n : Set C(Set.Icc (-1 : ℝ) 1, ℝ))
      ≤ (∏ i ∈ Finset.range k, (π * Real.sin (angle (n - i) / 2))) *
          (M * (π * Real.sin (angle (n - k) / 2)) ^ α) := by
    rw [hfeq]
    exact (infDist_restrictIcc_le_prod k n hkn.le D hDc hDd).trans
      (mul_le_mul_of_nonneg_left
        (infDist_polyLE_le_of_holder hM hα0 hα1 hhol' (n - k)) hPnn)
  -- the product of the steps
  have hprodbd : (∏ i ∈ Finset.range k, (π * Real.sin (angle (n - i) / 2)))
      ≤ (π ^ 2 / 2) ^ k / P := by
    have hterm : ∀ i ∈ Finset.range k,
        π * Real.sin (angle (n - i) / 2) ≤ π ^ 2 / 2 / ((n : ℝ) - i) := by
      intro i hi
      have hik : i < k := Finset.mem_range.1 hi
      have hin : i ≤ n := by omega
      have h := hc (n - i) (by omega)
      rwa [hcast i hin] at h
    calc ∏ i ∈ Finset.range k, (π * Real.sin (angle (n - i) / 2))
        ≤ ∏ i ∈ Finset.range k, (π ^ 2 / 2 / ((n : ℝ) - i)) :=
          Finset.prod_le_prod₀ (fun i _ => (mul_pos hpi (sin_half_angle_pos _)).le) hterm
      _ = (π ^ 2 / 2) ^ k / P := by
          rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range, hPdef]
  -- the last, Hölder, step
  have hbasebd : (π * Real.sin (angle (n - k) / 2)) ^ α ≤ π ^ 2 / 2 / S := by
    have h := hc (n - k) (by omega)
    rw [hcast k hkn.le] at h
    calc (π * Real.sin (angle (n - k) / 2)) ^ α
        ≤ (π ^ 2 / 2 / ((n : ℝ) - k)) ^ α :=
          Real.rpow_le_rpow (mul_pos hpi (sin_half_angle_pos _)).le h hα0
      _ = (π ^ 2 / 2) ^ α / S := by rw [hSdef, Real.div_rpow (by positivity) hnk.le]
      _ ≤ π ^ 2 / 2 / S := by
          gcongr
          calc (π ^ 2 / 2) ^ α ≤ (π ^ 2 / 2) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hpi2 hα1
            _ = π ^ 2 / 2 := Real.rpow_one _
  -- put the pieces together
  have hnpos : (0 : ℝ) < (n : ℝ) ^ ((k : ℝ) + α) := Real.rpow_pos_of_pos hn0 _
  have hdmul : (n : ℝ) ^ ((k : ℝ) + α) ≤ d * (P * S) := by
    rw [div_le_iff₀ (by positivity)] at hd
    exact hd
  calc Metric.infDist f (polyLE (Set.Icc (-1 : ℝ) 1) n : Set C(Set.Icc (-1 : ℝ) 1, ℝ))
      ≤ (∏ i ∈ Finset.range k, (π * Real.sin (angle (n - i) / 2))) *
          (M * (π * Real.sin (angle (n - k) / 2)) ^ α) := hstep1
    _ ≤ ((π ^ 2 / 2) ^ k / P) * (M * (π ^ 2 / 2 / S)) := by
        refine mul_le_mul hprodbd (mul_le_mul_of_nonneg_left hbasebd hM) ?_ (by positivity)
        exact mul_nonneg hM (Real.rpow_nonneg (mul_pos hpi (sin_half_angle_pos _)).le _)
    _ = (π ^ 2 / 2) ^ (k + 1) * M / (P * S) := by
        rw [pow_succ]
        field_simp
        ring
    _ ≤ (1 + π ^ 2 / 2) ^ (k + 1) * M / (P * S) := by
        have hb0 : (π ^ 2 / 2) ^ (k + 1) ≤ (1 + π ^ 2 / 2) ^ (k + 1) := by
          gcongr
          nlinarith [sq_nonneg π]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb0 hM) (by positivity)
    _ ≤ d * (1 + π ^ 2 / 2) ^ (k + 1) * M / (n : ℝ) ^ ((k : ℝ) + α) := by
        rw [div_le_div_iff₀ (by positivity) hnpos]
        have hA : (0 : ℝ) ≤ (1 + π ^ 2 / 2) ^ (k + 1) * M := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hdmul hA]

end Algebraic

end Jackson
