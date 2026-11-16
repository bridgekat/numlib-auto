/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Fourier.Dirichlet
import Numlib.Analysis.Fourier.TrigonometricBasis
import NumlibSurface.AtkinsonHan.Chapter01.Section02
import NumlibSurface.AtkinsonHan.Chapter02.Section04

/-!
# Atkinson and Han, Section 4.1: Fourier series

This module formalizes §4.1 of [han2009theoretical]. For a $2\pi$-periodic function $f$ the Fourier
series is
$$f(x) \sim \frac{a_0}{2} + \sum_{j=1}^{\infty} (a_j \cos(jx) + b_j \sin(jx)), \qquad
  a_j = \frac{1}{\pi} \int_{-\pi}^{\pi} f(x) \cos(jx)\, dx, \quad
  b_j = \frac{1}{\pi} \int_{-\pi}^{\pi} f(x) \sin(jx)\, dx,$$
and $S_n f$ is its $n$-th partial sum (4.1.1)–(4.1.3). The module relates $a_j$ and $b_j$ to the
complex coefficients $c_j$ and to the coefficients against an orthonormal system, and states the
sine and cosine series of odd and even functions. It proves pointwise convergence of $S_n f(x)$ to
$(f(x-) + f(x+))/2$ where $f$ has one-sided derivatives (Theorem 4.1.1), the criterion for $L^p$
convergence by uniform boundedness (Theorem 4.1.2), Parseval's equality (4.1.13), and the $L^2$ and
uniform truncation errors (4.1.14)–(4.1.15). Examples 4.1.3–4.1.5 compute three Fourier series in
closed form.

The proofs specialize the Dirichlet kernel theory of `Numlib.Analysis.Fourier.Dirichlet` and the
real trigonometric system of `Numlib.Analysis.Fourier.TrigonometricBasis`.

## Main results

* Equation (4.1.2), `AtkinsonHan.Chapter04.equation_4_1_3_const` and
  `AtkinsonHan.Chapter04.equation_4_1_3_cos`: $a_0$ and $a_j$ are $2$ and $\sqrt 2$ times the
  coefficients against the orthonormal system.
* Equation (4.1.3), `AtkinsonHan.Chapter04.equation_4_1_3_sin`: $b_j$ is $\sqrt 2$ times the
  coefficient against the orthonormal system.
* Equation (4.1.5), `AtkinsonHan.Chapter04.equation_4_1_5`: $c_j = (2\pi)^{-1} \int_{-\pi}^{\pi}
  f(x) e^{-ijx}\, dx$.
* Equation (4.1.6), `AtkinsonHan.Chapter04.equation_4_1_6_const`,
  `AtkinsonHan.Chapter04.equation_4_1_6_cos` and `AtkinsonHan.Chapter04.equation_4_1_6_sin`:
  $a_0 = 2 \operatorname{Re} c_0$, $a_j = 2 \operatorname{Re} c_j$ and
  $b_j = -2 \operatorname{Im} c_j$.
* Equations (4.1.7)–(4.1.10), `AtkinsonHan.Chapter04.equation_4_1_10_odd` and
  `AtkinsonHan.Chapter04.equation_4_1_10_even`: an odd function has a sine series and an even
  function has a cosine series.
* Theorem 4.1.1, `AtkinsonHan.Chapter04.theorem_4_1_1` and
  `AtkinsonHan.Chapter04.theorem_4_1_1_continuous`: $S_n f(x)$ converges to the mean of the
  one-sided limits, and to $f(x)$ where $f$ is differentiable.
* Theorem 4.1.2, `AtkinsonHan.Chapter04.theorem_4_1_2`: a sequence of bounded operators on $L^p$
  that converges to the identity on trigonometric polynomials converges to the identity on $L^p$ if
  and only if it is uniformly bounded.
* Equation (4.1.13), `AtkinsonHan.Chapter04.equation_4_1_13`: Parseval's equality
  $\|f\|^2_{L^2(-\pi, \pi)} = \pi (a_0^2/2 + \sum_{j \ge 1} (a_j^2 + b_j^2))$.
* Example 4.1.3, `AtkinsonHan.Chapter04.example_4_1_3`: the Fourier series of a step function.
* Example 4.1.4, `AtkinsonHan.Chapter04.example_4_1_4`: the Fourier series of $|x|/\pi$.
* Example 4.1.5, `AtkinsonHan.Chapter04.example_4_1_5`: the Fourier series of
  $(\pi^2 - x^2)^2/\pi^4$.
* Equation (4.1.14), `AtkinsonHan.Chapter04.equation_4_1_14`: $\|f - S_n f\|^2_{L^2(-\pi, \pi)} =
  \pi \sum_{j > n} (a_j^2 + b_j^2)$.
* Equation (4.1.15), `AtkinsonHan.Chapter04.equation_4_1_15`: $|f(x) - S_n f(x)| \le \sum_{j > n}
  (|a_j| + |b_j|)$ for an absolutely convergent Fourier series.

## Conventions

* The book works on $(-\pi, \pi)$ and always means the $2\pi$-periodic extension. So
  $L^p(-\pi, \pi)$ is $L^p$ of the circle `AddCircle (2 * π)` with its probability Haar measure
  `AddCircle.haarAddCircle`, and a function `g` on the circle is the $2\pi$-periodic function
  `fun x : ℝ => g ↑x` on $\mathbb{R}$. The integrals for the two measures differ by the factor
  $2\pi$ (`AtkinsonHan.Chapter04.integral_intervalIntegral_eq`).
* The coefficients $a_j$ and $b_j$ of (4.1.2)–(4.1.3) are the backbone's `fourierCoeffCos f j` and
  `fourierCoeffSin f j`, and $S_n f(x)$ of (4.1.1) is `fourierPartialSum f n x`.
* The names `AtkinsonHan.Chapter04.equation_4_1_3_const`, `AtkinsonHan.Chapter04.equation_4_1_3_cos`
  and `AtkinsonHan.Chapter04.equation_4_1_3_sin` cover both displays (4.1.2) and (4.1.3).

## Implementation notes

* The surface adds the relation between the book's $a_j$, $b_j$ and the two coefficient families
  used for the $L^2$ theory: `realFourierCoeff` against the orthonormal system `trigFun`, and
  Mathlib's complex `fourierCoeff`.
* Each of Examples 4.1.3–4.1.5 is about the $2\pi$-periodic extension of a function given on one
  period. So its $f$ is described by hypotheses, `Function.Periodic f (2 * π)` together with the
  book's formula on $[-\pi, 0)$ and $[0, \pi)$ or on $[-\pi, \pi]$, rather than written as a closed
  term. These hypotheses determine $f$ everywhere.
* In the examples, the convergence of the book's series is stated as the ordered convergence
  $\sum_{i < n} v_i \to s$ of Definition 1.2.17 (`AtkinsonHan.Chapter01.definition_1_2_17`).
  Mathlib's `HasSum` would be the wrong statement, because the series of Example 4.1.3 converges
  only conditionally and so has no unordered sum. The convergence itself is always Theorem 4.1.1.

## Deviations from the source

* **Theorem 4.1.1** (generalization). The book assumes $f$ piecewise continuous. The library assumes
  only that $f$ is integrable over one period, which is all the proof uses. See
  `AtkinsonHan.Chapter04.theorem_4_1_1`.
* **Theorem 4.1.2** (generalization). The book states the theorem for the Fourier partial sum
  operators $S_N$ on $L^p$. The library states it for any sequence of bounded operators on $L^p$
  that converges to the identity on trigonometric polynomials. See
  `AtkinsonHan.Chapter04.theorem_4_1_2`.
* **(4.1.15)** (reading). The book's hypotheses "the Fourier series is absolutely convergent" and
  "$f$ is continuous after a change on a set of measure zero" are read as summability of
  $|a_j| + |b_j|$ and convergence of $S_n f(x)$ to $f(x)$ at every $x$. See
  `AtkinsonHan.Chapter04.equation_4_1_15`.

## Not formalized

* **The Gibbs phenomenon beside Example 4.1.3.** The book asserts the overshoot
  $(2/\pi) \operatorname{Si}(\pi) |f(x+) - f(x-)|$, with
  $(2/\pi) \operatorname{Si}(\pi) \approx 1.17898$, without proof and refers the reader elsewhere.
* **The $L^p$ boundedness (4.1.12) of the partial sum operators for $1 < p < \infty$.** It is the M.
  Riesz theorem, which is not in Mathlib. For this reason Theorem 4.1.2 takes the operators as data.
-/

open Filter MeasureTheory Topology

open scoped ENNReal Real

namespace AtkinsonHan.Chapter04

/-! ### The circle and the interval -/

/-- **The identification of $L^p(-\pi, \pi)$ with $L^p$ of the circle.** For every
$g : \mathbb{R}/2\pi\mathbb{Z} \to \mathbb{R}$, the integral of $g$ for the probability Haar
measure of the circle is
$$\int g\, d\mu = \frac{1}{2\pi} \int_{-\pi}^{\pi} g(x)\, dx,$$
where on the right $g$ is read as a $2\pi$-periodic function on $\mathbb{R}$. All statements of
this module that mix the book's normalization with the backbone's use this identity. -/
theorem integral_intervalIntegral_eq (g : AddCircle (2 * π) → ℝ) :
    ∫ b : AddCircle (2 * π), g b ∂AddCircle.haarAddCircle
      = (2 * π)⁻¹ * ∫ x in -π..π, g ↑x := by
  rw [AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2 * π) (-π) g, smul_eq_mul,
    show -π + 2 * π = π by ring]

/-- The real Fourier coefficient of $g$ on the circle is $(2\pi)^{-1}$ times the integral of
$\varphi_n g$ over $(-\pi, \pi)$. -/
private theorem realFourierCoeff_eq_intervalIntegral (g : AddCircle (2 * π) → ℝ) (n : ℤ) :
    realFourierCoeff g n = (2 * π)⁻¹ * ∫ x in -π..π, trigFun (2 * π) n ↑x * g ↑x := by
  rw [realFourierCoeff_apply]
  exact integral_intervalIntegral_eq (fun b => trigFun (2 * π) n b * g b)

/-! ### The real coefficients (4.1.1)–(4.1.3) -/

/-- **Equation (4.1.2)** of [han2009theoretical], case $j = 0$. Let $g$ be a real function on the
circle $\mathbb{R}/2\pi\mathbb{Z}$, read as a $2\pi$-periodic function on $\mathbb{R}$. Then the
book's coefficient $a_0 = \pi^{-1} \int_{-\pi}^{\pi} g(x)\, dx$ is twice the coefficient of $g$
against the constant member $\varphi_0 = 1$ of the orthonormal system:
$$a_0 = 2 \int g\, \varphi_0\, d\mu,$$
for the probability Haar measure $\mu$ of the circle.

The coefficient against $\varphi_m$ is `realFourierCoeff g m`. -/
theorem equation_4_1_3_const (g : AddCircle (2 * π) → ℝ) :
    fourierCoeffCos (fun x : ℝ => g ↑x) 0 = 2 * realFourierCoeff g 0 := by
  have h1 : ∀ t : ℝ, g ↑t * Real.cos (((0 : ℕ) : ℝ) * t) = g ↑t := by
    intro t; norm_num
  have h2 : ∀ t : ℝ, trigFun (2 * π) 0 (↑t : AddCircle (2 * π)) * g ↑t = g ↑t := by
    intro t; rw [trigFun_zero]; simp
  simp only [fourierCoeffCos, realFourierCoeff_eq_intervalIntegral]
  rw [intervalIntegral.integral_congr (fun t _ => h1 t),
    intervalIntegral.integral_congr (fun t _ => h2 t)]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **Equation (4.1.2)** of [han2009theoretical]. Let $g$ be a real function on the circle
$\mathbb{R}/2\pi\mathbb{Z}$, read as a $2\pi$-periodic function on $\mathbb{R}$, and let
$j \ge 1$. Then the book's coefficient $a_j = \pi^{-1} \int_{-\pi}^{\pi} g(x) \cos(jx)\, dx$ is
$\sqrt 2$ times the coefficient of $g$ against the member $\varphi_j = \sqrt 2 \cos(jx)$ of the
orthonormal system:
$$a_j = \sqrt 2 \int g\, \varphi_j\, d\mu,$$
for the probability Haar measure $\mu$ of the circle.

The member $\varphi_j$ is `trigFun (2 * π) j`. -/
theorem equation_4_1_3_cos (g : AddCircle (2 * π) → ℝ) {j : ℕ} (hj : 0 < j) :
    fourierCoeffCos (fun x : ℝ => g ↑x) j = √2 * realFourierCoeff g j := by
  have hj' : (0 : ℤ) < (j : ℤ) := by exact_mod_cast hj
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have h2 : ∀ t : ℝ, trigFun (2 * π) (j : ℤ) (↑t : AddCircle (2 * π)) * g ↑t
      = √2 * (g ↑t * Real.cos ((j : ℝ) * t)) := by
    intro t
    rw [trigFun_coe_of_pos hj', Int.cast_natCast]
    ring
  simp only [fourierCoeffCos, realFourierCoeff_eq_intervalIntegral]
  rw [intervalIntegral.integral_congr (fun t _ => h2 t), intervalIntegral.integral_const_mul]
  obtain ⟨I, hI⟩ : ∃ I : ℝ, (∫ t in -π..π, g ↑t * Real.cos ((j : ℝ) * t)) = I := ⟨_, rfl⟩
  rw [hI]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- **Equation (4.1.3)** of [han2009theoretical]. Let $g$ be a real function on the circle
$\mathbb{R}/2\pi\mathbb{Z}$, read as a $2\pi$-periodic function on $\mathbb{R}$, and let
$j \ge 1$. Then the book's coefficient $b_j = \pi^{-1} \int_{-\pi}^{\pi} g(x) \sin(jx)\, dx$ is
$\sqrt 2$ times the coefficient of $g$ against the member $\varphi_{-j} = \sqrt 2 \sin(jx)$ of
the orthonormal system:
$$b_j = \sqrt 2 \int g\, \varphi_{-j}\, d\mu,$$
for the probability Haar measure $\mu$ of the circle.

The member $\varphi_{-j}$ is `trigFun (2 * π) (-j)`. -/
theorem equation_4_1_3_sin (g : AddCircle (2 * π) → ℝ) {j : ℕ} (hj : 0 < j) :
    fourierCoeffSin (fun x : ℝ => g ↑x) j = √2 * realFourierCoeff g (-j) := by
  have hj' : (-(j : ℤ)) < 0 := by exact_mod_cast Int.neg_neg_of_pos (by exact_mod_cast hj)
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have h2 : ∀ t : ℝ, trigFun (2 * π) (-(j : ℤ)) (↑t : AddCircle (2 * π)) * g ↑t
      = √2 * (g ↑t * Real.sin ((j : ℝ) * t)) := by
    intro t
    rw [trigFun_coe_of_neg hj']
    push_cast
    ring_nf
  simp only [fourierCoeffSin, realFourierCoeff_eq_intervalIntegral]
  rw [intervalIntegral.integral_congr (fun t _ => h2 t), intervalIntegral.integral_const_mul]
  obtain ⟨I, hI⟩ : ∃ I : ℝ, (∫ t in -π..π, g ↑t * Real.sin ((j : ℝ) * t)) = I := ⟨_, rfl⟩
  rw [hI]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-! ### The complex form (4.1.4)–(4.1.6) -/

/-- **Equation (4.1.5)** of [han2009theoretical]. Let $g$ be a real function on the circle
$\mathbb{R}/2\pi\mathbb{Z}$, read as a $2\pi$-periodic function on $\mathbb{R}$, and let
$j \in \mathbb{Z}$. Then the complex Fourier coefficient of $g$ is
$$c_j = \frac{1}{2\pi} \int_{-\pi}^{\pi} g(x) e^{-ijx}\, dx.$$

Here $c_j$ is Mathlib's `fourierCoeff` on `AddCircle (2 * π)`, whose character
$e^{2\pi i j x / T}$ is $e^{ijx}$ at $T = 2\pi$. -/
theorem equation_4_1_5 (g : AddCircle (2 * π) → ℝ) (j : ℤ) :
    fourierCoeff (fun b => ((g b : ℝ) : ℂ)) j
      = ((2 * π)⁻¹ : ℝ) • ∫ x in -π..π, Complex.exp (-(j * x) * Complex.I) * (g ↑x : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := fourierCoeff_eq_intervalIntegral (fun b => ((g b : ℝ) : ℂ)) j (-π)
  rw [show -π + 2 * π = π by ring] at h
  rw [h, one_div]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [fourier_coe_apply, smul_eq_mul]
  congr 2
  push_cast
  field_simp

/-- **Equation (4.1.6)** of [han2009theoretical], case $j = 0$. Let $g$ be a real function on the
circle $\mathbb{R}/2\pi\mathbb{Z}$ that is integrable for its Haar measure. Then
$a_0 = 2 \operatorname{Re} c_0$.

The book writes $a_0 = 2 c_0$; the coefficient $c_0$ is real for a real $g$. -/
theorem equation_4_1_6_const {g : AddCircle (2 * π) → ℝ}
    (hg : Integrable g AddCircle.haarAddCircle) :
    fourierCoeffCos (fun x : ℝ => g ↑x) 0 = 2 * (fourierCoeff (fun b => ((g b : ℝ) : ℂ)) 0).re := by
  rw [equation_4_1_3_const, realFourierCoeff_eq_fourierCoeff hg 0]
  simp

/-- **Equation (4.1.6)** of [han2009theoretical], cosine coefficients. Let $g$ be a real function on
the circle $\mathbb{R}/2\pi\mathbb{Z}$ that is integrable for its Haar measure, and let
$j \ge 1$. Then $a_j = 2 \operatorname{Re} c_j$. -/
theorem equation_4_1_6_cos {g : AddCircle (2 * π) → ℝ}
    (hg : Integrable g AddCircle.haarAddCircle) {j : ℕ} (hj : 0 < j) :
    fourierCoeffCos (fun x : ℝ => g ↑x) j = 2 * (fourierCoeff (fun b => ((g b : ℝ) : ℂ)) j).re := by
  have hj' : (0 : ℤ) < (j : ℤ) := by exact_mod_cast hj
  rw [equation_4_1_3_cos g hj, realFourierCoeff_of_pos hg hj', ← mul_assoc,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- **Equation (4.1.6)** of [han2009theoretical], sine coefficients. Let $g$ be a real function on
the circle $\mathbb{R}/2\pi\mathbb{Z}$ that is integrable for its Haar measure, and let
$j \ge 1$. Then $b_j = -2 \operatorname{Im} c_j$. -/
theorem equation_4_1_6_sin {g : AddCircle (2 * π) → ℝ}
    (hg : Integrable g AddCircle.haarAddCircle) {j : ℕ} (hj : 0 < j) :
    fourierCoeffSin (fun x : ℝ => g ↑x) j
      = -(2 * (fourierCoeff (fun b => ((g b : ℝ) : ℂ)) j).im) := by
  have hj' : (-(j : ℤ)) < 0 := by exact_mod_cast Int.neg_neg_of_pos (by exact_mod_cast hj)
  rw [equation_4_1_3_sin g hj, realFourierCoeff_of_neg hg hj', fourierCoeff_ofReal_neg,
    Complex.conj_im, ← mul_assoc, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-! ### Sine and cosine series (4.1.7)–(4.1.10) -/

/-- The interval $[-\pi, 0]$ is contained in $[-\pi, \pi]$. -/
private theorem uIcc_subset_left : Set.uIcc (-π) (0 : ℝ) ⊆ Set.uIcc (-π) π := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
  exact Set.Icc_subset_Icc le_rfl (by linarith)

/-- The interval $[0, \pi]$ is contained in $[-\pi, \pi]$. -/
private theorem uIcc_subset_right : Set.uIcc (0 : ℝ) π ⊆ Set.uIcc (-π) π := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
  exact Set.Icc_subset_Icc (by linarith) le_rfl

/-- An odd function that is integrable on $[-\pi, \pi]$ has integral $0$ over $[-\pi, \pi]$. -/
private theorem intervalIntegral_of_odd {g : ℝ → ℝ} (hg : ∀ t, g (-t) = -g t)
    (hgi : IntervalIntegrable g volume (-π) π) : (∫ t in -π..π, g t) = 0 := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hgi.mono_set uIcc_subset_left) (hgi.mono_set uIcc_subset_right)
  have hflip : (∫ t in -π..(0 : ℝ), g t) = -∫ t in (0 : ℝ)..π, g t := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π) g
    rw [neg_zero] at h
    rw [← h, ← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun t _ => hg t
  rw [← hsplit, hflip]
  ring

/-- An even function that is integrable on $[-\pi, \pi]$ has integral over $[-\pi, \pi]$ equal to
twice its integral over $[0, \pi]$. -/
private theorem intervalIntegral_of_even {g : ℝ → ℝ} (hg : ∀ t, g (-t) = g t)
    (hgi : IntervalIntegrable g volume (-π) π) :
    (∫ t in -π..π, g t) = 2 * ∫ t in (0 : ℝ)..π, g t := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hgi.mono_set uIcc_subset_left) (hgi.mono_set uIcc_subset_right)
  have hsame : (∫ t in -π..(0 : ℝ), g t) = ∫ t in (0 : ℝ)..π, g t := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π) g
    rw [neg_zero] at h
    rw [← h]
    exact intervalIntegral.integral_congr fun t _ => hg t
  rw [← hsplit, hsame]
  ring

/-- **Equations (4.1.7)–(4.1.8)** of [han2009theoretical] (Exercise 4.1.2). Let
$f : \mathbb{R} \to \mathbb{R}$ be odd and integrable on $[-\pi, \pi]$. Then for every
$j \ge 0$,
$$a_j = 0 \quad \text{and} \quad b_j = \frac{2}{\pi} \int_0^\pi f(x) \sin(jx)\, dx.$$
So the Fourier series of $f$ is a sine series. For the odd extension of a function given on
$(0, \pi)$, this is the book's sine series of that function. -/
theorem equation_4_1_10_odd {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x)
    (hfi : IntervalIntegrable f volume (-π) π) (j : ℕ) :
    fourierCoeffCos f j = 0 ∧
      fourierCoeffSin f j = 2 / π * ∫ x in (0 : ℝ)..π, f x * Real.sin (j * x) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  refine ⟨?_, ?_⟩
  · have h0 := intervalIntegral_of_odd (g := fun t => f t * Real.cos ((j : ℝ) * t))
      (fun t => by rw [mul_neg, Real.cos_neg, hodd t]; ring)
      (hfi.mul_continuousOn (Continuous.continuousOn (by fun_prop)))
    simp only [fourierCoeffCos, h0, mul_zero]
  · have h0 := intervalIntegral_of_even (g := fun t => f t * Real.sin ((j : ℝ) * t))
      (fun t => by rw [mul_neg, Real.sin_neg, hodd t]; ring)
      (hfi.mul_continuousOn (Continuous.continuousOn (by fun_prop)))
    simp only [fourierCoeffSin, h0]
    field_simp

/-- **Equations (4.1.9)–(4.1.10)** of [han2009theoretical] (Exercise 4.1.3). Let
$f : \mathbb{R} \to \mathbb{R}$ be even and integrable on $[-\pi, \pi]$. Then for every
$j \ge 0$,
$$b_j = 0 \quad \text{and} \quad a_j = \frac{2}{\pi} \int_0^\pi f(x) \cos(jx)\, dx.$$
So the Fourier series of $f$ is a cosine series. -/
theorem equation_4_1_10_even {f : ℝ → ℝ} (heven : ∀ x, f (-x) = f x)
    (hfi : IntervalIntegrable f volume (-π) π) (j : ℕ) :
    fourierCoeffSin f j = 0 ∧
      fourierCoeffCos f j = 2 / π * ∫ x in (0 : ℝ)..π, f x * Real.cos (j * x) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  refine ⟨?_, ?_⟩
  · have h0 := intervalIntegral_of_odd (g := fun t => f t * Real.sin ((j : ℝ) * t))
      (fun t => by rw [mul_neg, Real.sin_neg, heven t]; ring)
      (hfi.mul_continuousOn (Continuous.continuousOn (by fun_prop)))
    simp only [fourierCoeffSin, h0, mul_zero]
  · have h0 := intervalIntegral_of_even (g := fun t => f t * Real.cos ((j : ℝ) * t))
      (fun t => by rw [mul_neg, Real.cos_neg, heven t])
      (hfi.mul_continuousOn (Continuous.continuousOn (by fun_prop)))
    simp only [fourierCoeffCos, h0]
    field_simp

/-! ### Pointwise convergence (Theorem 4.1.1) -/

/-- **Theorem 4.1.1** of [han2009theoretical]. Let $f : \mathbb{R} \to \mathbb{R}$ be
$2\pi$-periodic and integrable on $[-\pi, \pi]$, and let $x, f_L, f_R, c_L, c_R \in \mathbb{R}$.
Assume that, as $t \to 0^+$,
$$\frac{f(x + t) - f_R}{t} \to c_R \quad \text{and} \quad \frac{f(x - t) - f_L}{t} \to c_L.$$
Then the Fourier partial sums converge at $x$ to the mean of the one-sided limits:
$$S_n f(x) \to \frac{f_L + f_R}{2} \quad (n \to \infty).$$

**Generalization.** The book assumes $f$ piecewise continuous. The statement assumes only that
$f$ is integrable over one period, which is all the book's proof uses.

The two hypotheses say that $f$ has the one-sided limits $f(x-) = f_L$ and $f(x+) = f_R$ and
one-sided derivatives at $x$. The proof is Dini's criterion `tendsto_fourierPartialSum_of_dini`.
Its integrability hypothesis holds because the symmetrized quotient
$(f(x + t) - f_R)/t + (f(x - t) - f_L)/t$ is bounded near $0$. -/
theorem theorem_4_1_1 {f : ℝ → ℝ} (hf : Function.Periodic f (2 * π))
    (hfi : IntervalIntegrable f volume (-π) π) {x fL fR cL cR : ℝ}
    (hR : Tendsto (fun t : ℝ => (f (x + t) - fR) / t) (𝓝[>] 0) (𝓝 cR))
    (hL : Tendsto (fun t : ℝ => (f (x - t) - fL) / t) (𝓝[>] 0) (𝓝 cL)) :
    Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 ((fL + fR) / 2)) := by
  have hall := intervalIntegrable_of_periodic hf hfi
  have hshift : ∀ a b : ℝ, IntervalIntegrable (fun t => f (x + t)) volume a b := fun a b => by
    simpa using (hall (x + a) (x + b)).comp_add_left x
  have hrefl : ∀ a b : ℝ, IntervalIntegrable (fun t => f (x - t)) volume a b := fun a b => by
    simpa using (hall (x - a) (x - b)).comp_sub_left x
  have hφ : ∀ a b : ℝ,
      IntervalIntegrable (fun t => f (x + t) + f (x - t) - 2 * ((fL + fR) / 2)) volume a b :=
    fun a b => ((hshift a b).add (hrefl a b)).sub intervalIntegrable_const
  have hlim : Tendsto (fun t : ℝ => (f (x + t) + f (x - t) - 2 * ((fL + fR) / 2)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (cR + cL)) := by
    refine Filter.Tendsto.congr (fun t => ?_) (hR.add hL)
    rw [← add_div]
    congr 1
    ring
  obtain ⟨δ, hδ0, hδ⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim 1 one_pos
  have hδ₀0 : 0 < min (δ / 2) π := lt_min (by linarith) Real.pi_pos
  have hδ₀π : min (δ / 2) π ≤ π := min_le_right _ _
  have hbound : ∀ t ∈ Set.Ioc (0 : ℝ) (min (δ / 2) π),
      ‖(f (x + t) + f (x - t) - 2 * ((fL + fR) / 2)) / t‖ ≤ |cR + cL| + 1 := by
    intro t ht
    have hdist : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
      calc t ≤ min (δ / 2) π := ht.2
        _ ≤ δ / 2 := min_le_left _ _
        _ < δ := by linarith
    have h := hδ (Set.mem_Ioi.2 ht.1) hdist
    rw [Real.dist_eq] at h
    have habs := abs_sub_abs_le_abs_sub
      ((f (x + t) + f (x - t) - 2 * ((fL + fR) / 2)) / t) (cR + cL)
    rw [Real.norm_eq_abs]
    linarith
  have hq1 : IntervalIntegrable
      (fun t => (f (x + t) + f (x - t) - 2 * ((fL + fR) / 2)) / t) volume 0
      (min (δ / 2) π) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hδ₀0.le]
    have hm := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδ₀0.le).mp
      (hφ 0 (min (δ / 2) π))).aestronglyMeasurable
    refine Integrable.mono' (integrable_const (|cR + cL| + 1))
      (hm.aemeasurable.div aemeasurable_id).aestronglyMeasurable ?_
    exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hbound)
  have hq2 : IntervalIntegrable
      (fun t => (f (x + t) + f (x - t) - 2 * ((fL + fR) / 2)) / t) volume
      (min (δ / 2) π) π := by
    have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc (min (δ / 2) π) π) := by
      refine ContinuousOn.inv₀ continuousOn_id fun t ht => ?_
      rw [Set.uIcc_of_le hδ₀π] at ht
      exact ne_of_gt (lt_of_lt_of_le hδ₀0 ht.1)
    have heq : (fun t => (f (x + t) + f (x - t) - 2 * ((fL + fR) / 2)) / t)
        = fun t => (f (x + t) + f (x - t) - 2 * ((fL + fR) / 2)) * t⁻¹ :=
      funext fun t => div_eq_mul_inv _ _
    rw [heq]
    exact (hφ (min (δ / 2) π) π).mul_continuousOn hcont
  exact tendsto_fourierPartialSum_of_dini hf hfi (hq1.trans hq2)

/-- **Theorem 4.1.1** of [han2009theoretical], at points of differentiability. Let
$f : \mathbb{R} \to \mathbb{R}$ be $2\pi$-periodic and integrable on $[-\pi, \pi]$, and let $f$
be differentiable at $x$. Then $S_n f(x) \to f(x)$ as $n \to \infty$. -/
theorem theorem_4_1_1_continuous {f : ℝ → ℝ} (hf : Function.Periodic f (2 * π))
    (hfi : IntervalIntegrable f volume (-π) π) {x c : ℝ} (hd : HasDerivAt f c x) :
    Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 (f x)) :=
  tendsto_fourierPartialSum_of_hasDerivAt hf hfi hd

/-! ### $L^p$ convergence (Theorem 4.1.2) -/

/-- Let $1 \le p < \infty$. The trigonometric polynomials are dense in $L^p$ of the circle
$\mathbb{R}/2\pi\mathbb{Z}$, for its probability Haar measure.

The trigonometric polynomials are dense in $C(\mathbb{R}/2\pi\mathbb{Z})$ by Corollary 3.1.4,
which is the backbone's `span_trigFun_closure_eq_top`, and the continuous functions are dense in
$L^p$. -/
theorem dense_image_toLp_trigSpan {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    Dense (ContinuousMap.toLp (E := ℝ) p
        (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) ℝ ''
      (Submodule.span ℝ (Set.range (trigFun (2 * π))) : Set C(AddCircle (2 * π), ℝ))) := by
  have hWdense : Dense (Submodule.span ℝ (Set.range (trigFun (2 * π))) :
      Set C(AddCircle (2 * π), ℝ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2 span_trigFun_closure_eq_top
  have hTd := ContinuousMap.toLp_denseRange ℝ
    (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) ℝ hp (p := p)
  have hsub : Set.range (ContinuousMap.toLp (E := ℝ) p
      (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) ℝ) ⊆
      closure (ContinuousMap.toLp (E := ℝ) p
        (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) ℝ ''
        (Submodule.span ℝ (Set.range (trigFun (2 * π))) : Set C(AddCircle (2 * π), ℝ))) := by
    rintro _ ⟨q, rfl⟩
    refine image_closure_subset_closure_image (map_continuous _) ⟨q, ?_, rfl⟩
    rw [hWdense.closure_eq]
    trivial
  exact fun x => closure_minimal hsub isClosed_closure (hTd x)

/-- **Theorem 4.1.2** of [han2009theoretical], with (4.1.11)–(4.1.12). Let $1 \le p < \infty$, and
let $S_0, S_1, \ldots$ be bounded linear operators on $L^p(-\pi, \pi)$ such that $S_N q \to q$
for every trigonometric polynomial $q$. Then $\|S_N f - f\|_{L^p} \to 0$ for every
$f \in L^p(-\pi, \pi)$ if and only if there is a constant $C$ with $\|S_N\| \le C$ for all $N$.

**Generalization.** The book states the theorem for the Fourier partial sum operators $S_N$.
These converge to the identity on trigonometric polynomials, because each trigonometric
polynomial is fixed by $S_N$ for all large $N$, and each $S_N$ is bounded on $L^p$. The
statement takes the operators as data, since Mathlib has no partial sum operator on $L^p$.

The forward direction is the principle of uniform boundedness (Theorem 2.4.4,
`AtkinsonHan.Chapter02.theorem_2_4_4`). The backward direction is the density of the
trigonometric polynomials (Corollary 3.1.4, `AtkinsonHan.Chapter03.corollary_3_1_4`) with the
backbone's density criterion. At $p = 2$ the uniform bound holds with $C = 1$ by Bessel's
inequality, and the resulting convergence is `AtkinsonHan.Chapter04.equation_4_1_13`.
$L^p(-\pi, \pi)$ is $L^p$ of the circle for its probability Haar measure. -/
theorem theorem_4_1_2 {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (S : ℕ → Lp ℝ p (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) →L[ℝ]
      Lp ℝ p (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))))
    (hS : ∀ q ∈ Submodule.span ℝ (Set.range (trigFun (2 * π))),
      Tendsto (fun N => S N (ContinuousMap.toLp (E := ℝ) p AddCircle.haarAddCircle ℝ q)) atTop
        (𝓝 (ContinuousMap.toLp (E := ℝ) p AddCircle.haarAddCircle ℝ q))) :
    (∀ f, Tendsto (fun N => ‖S N f - f‖) atTop (𝓝 0)) ↔ ∃ C : ℝ, ∀ N, ‖S N‖ ≤ C := by
  constructor
  · intro h
    refine AtkinsonHan.Chapter02.theorem_2_4_4 S fun v => ?_
    have hv : Tendsto (fun N => S N v) atTop (𝓝 v) := tendsto_iff_norm_sub_tendsto_zero.2 (h v)
    obtain ⟨M, hM⟩ := hv.norm.bddAbove_range
    exact ⟨M, fun N => hM ⟨N, rfl⟩⟩
  · rintro ⟨C, hC⟩ f
    have hon : ∀ w ∈ (ContinuousMap.toLp (E := ℝ) p
        (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) ℝ ''
        (Submodule.span ℝ (Set.range (trigFun (2 * π))) : Set C(AddCircle (2 * π), ℝ))),
        Tendsto (fun N => S N w) atTop
          (𝓝 (ContinuousLinearMap.id ℝ
            (Lp ℝ p (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))) w)) := by
      rintro w ⟨q, hq, rfl⟩
      simpa using hS q hq
    have hid := ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded
      (dense_image_toLp_trigSpan (p := p) hp) hC hon f
    rw [ContinuousLinearMap.id_apply] at hid
    exact tendsto_iff_norm_sub_tendsto_zero.1 hid

/-! ### Parseval's equality (4.1.13) -/

/-- An absolutely convergent sum over $\mathbb{Z}$, folded onto $\mathbb{N}$ by pairing $n$ with
$-n$: the term $0$ stays alone and the $j$-th term is $c_j + c_{-j}$. -/
private theorem hasSum_int_fold {c : ℤ → ℝ} {S : ℝ} (h : HasSum c S) :
    HasSum (fun j : ℕ => if j = 0 then c 0 else c j + c (-j)) S := by
  have h1 : HasSum (fun n : ℕ => c n + c (-n)) (S + c 0) := h.nat_add_neg
  have h2 := h1.update 0 (c 0)
  have hfun : Function.update (fun n : ℕ => c ↑n + c (-↑n)) 0 (c 0)
      = fun j : ℕ => if j = 0 then c 0 else c j + c (-j) := by
    funext j
    rw [Function.update_apply]
  have hval : c 0 - ((fun n : ℕ => c ↑n + c (-↑n)) 0) + (S + c 0) = S := by
    simp only [Nat.cast_zero, neg_zero]
    ring
  rw [hfun, hval] at h2
  exact h2

/-- The squared $L^2$ norm for the probability Haar measure of the circle is $(2\pi)^{-1}$ times the
integral of the square over $(-\pi, \pi)$. -/
private theorem norm_sq_eq_intervalIntegral
    (F : Lp ℝ 2 (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))) :
    ‖F‖ ^ 2 = (2 * π)⁻¹ * ∫ x in -π..π, (F : AddCircle (2 * π) → ℝ) ↑x ^ 2 := by
  rw [← integral_intervalIntegral_eq (fun b => (F : AddCircle (2 * π) → ℝ) b ^ 2),
    ← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  dsimp only
  rw [RCLike.inner_apply]
  simp [sq]

/-- For $j \ge 1$, the square of the coefficient against $\varphi_j$ is $a_j^2/2$. -/
private theorem sq_realFourierCoeff_cos (G : AddCircle (2 * π) → ℝ) {j : ℕ} (hj : 0 < j) :
    realFourierCoeff G j ^ 2 = fourierCoeffCos (fun x : ℝ => G ↑x) j ^ 2 / 2 := by
  rw [equation_4_1_3_cos G hj, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- For $j \ge 1$, the square of the coefficient against $\varphi_{-j}$ is $b_j^2/2$. -/
private theorem sq_realFourierCoeff_sin (G : AddCircle (2 * π) → ℝ) {j : ℕ} (hj : 0 < j) :
    realFourierCoeff G (-j) ^ 2 = fourierCoeffSin (fun x : ℝ => G ↑x) j ^ 2 / 2 := by
  rw [equation_4_1_3_sin G hj, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- **Equation (4.1.13)** of [han2009theoretical] (Parseval's equality). Let $f \in L^2(-\pi, \pi)$,
with Fourier coefficients $a_j$ and $b_j$. Then
$$\int_{-\pi}^{\pi} f(x)^2\, dx = \pi \Bigl( \frac{a_0^2}{2} + \sum_{j=1}^{\infty} (a_j^2 +
  b_j^2) \Bigr).$$

The sum is stated as an unordered sum (`HasSum`) over $j \in \mathbb{N}$ whose term $j = 0$ is
$\pi a_0^2/2$. The proof is `tsum_sq_realFourierCoeff`, Parseval's equality for the orthonormal
system, transported by the relations `AtkinsonHan.Chapter04.equation_4_1_3_const`,
`AtkinsonHan.Chapter04.equation_4_1_3_cos` and `AtkinsonHan.Chapter04.equation_4_1_3_sin` and by
`AtkinsonHan.Chapter04.integral_intervalIntegral_eq`. The function $f$ is a representative of an
element of $L^2$ of the circle for its probability Haar measure. -/
theorem equation_4_1_13 (F : Lp ℝ 2 (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))) :
    HasSum (fun j : ℕ =>
        if j = 0 then π * fourierCoeffCos (fun x : ℝ => (F : AddCircle (2 * π) → ℝ) ↑x) 0 ^ 2 / 2
        else π * (fourierCoeffCos (fun x : ℝ => (F : AddCircle (2 * π) → ℝ) ↑x) j ^ 2
          + fourierCoeffSin (fun x : ℝ => (F : AddCircle (2 * π) → ℝ) ↑x) j ^ 2))
      (∫ x in -π..π, (F : AddCircle (2 * π) → ℝ) ↑x ^ 2) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  obtain ⟨G, hG⟩ : ∃ G : AddCircle (2 * π) → ℝ, (F : AddCircle (2 * π) → ℝ) = G := ⟨_, rfl⟩
  rw [hG]
  -- Parseval for the orthonormal system
  have hA : HasSum (fun n : ℤ => realFourierCoeff G n ^ 2) (‖F‖ ^ 2) := by
    have h := (trigBasis (2 * π)).hasSum_inner_mul_inner F F
    have hfe : (fun n : ℤ => inner ℝ F ((trigBasis (2 * π)) n) * inner ℝ ((trigBasis (2 * π)) n) F)
        = fun n : ℤ => realFourierCoeff G n ^ 2 := by
      funext n
      rw [coe_trigBasis, real_inner_comm, inner_trigLp, hG]
      ring
    rw [hfe, real_inner_self_eq_norm_sq] at h
    exact h
  -- the `L²` norm against the probability measure, and against the book's interval
  have hnorm : ‖F‖ ^ 2 = (2 * π)⁻¹ * ∫ x in -π..π, G ↑x ^ 2 := by
    rw [← hG]
    exact norm_sq_eq_intervalIntegral F
  -- the coefficient dictionary
  have hc0 : realFourierCoeff G 0 = fourierCoeffCos (fun x : ℝ => G ↑x) 0 / 2 := by
    rw [equation_4_1_3_const]; ring
  have hcj : ∀ j : ℕ, 0 < j →
      realFourierCoeff G j ^ 2 = fourierCoeffCos (fun x : ℝ => G ↑x) j ^ 2 / 2 :=
    fun j hj => sq_realFourierCoeff_cos G hj
  have hsj : ∀ j : ℕ, 0 < j →
      realFourierCoeff G (-j) ^ 2 = fourierCoeffSin (fun x : ℝ => G ↑x) j ^ 2 / 2 :=
    fun j hj => sq_realFourierCoeff_sin G hj
  -- fold the sum over `ℤ` onto `ℕ`, then rescale
  have hB := (hasSum_int_fold hA).mul_left (2 * π)
  have hfun : (fun j : ℕ => 2 * π *
        if j = 0 then realFourierCoeff G 0 ^ 2
        else realFourierCoeff G j ^ 2 + realFourierCoeff G (-j) ^ 2)
      = fun j : ℕ =>
        if j = 0 then π * fourierCoeffCos (fun x : ℝ => G ↑x) 0 ^ 2 / 2
        else π * (fourierCoeffCos (fun x : ℝ => G ↑x) j ^ 2
          + fourierCoeffSin (fun x : ℝ => G ↑x) j ^ 2) := by
    funext j
    rcases eq_or_ne j 0 with rfl | hj
    · rw [ite_eq_left rfl, ite_eq_left rfl, hc0]
      ring
    · rw [ite_eq_right hj, ite_eq_right hj, hcj j (Nat.pos_of_ne_zero hj),
        hsj j (Nat.pos_of_ne_zero hj)]
      ring
  rw [hfun] at hB
  have hval : 2 * π * ‖F‖ ^ 2 = ∫ x in -π..π, G ↑x ^ 2 := by
    rw [hnorm]
    field_simp
  rwa [hval] at hB

/-! ### Examples 4.1.3–4.1.5: three concrete Fourier series -/

/-- The partial sum $S_n f$ is $2\pi$-periodic, because its terms are $\cos(jx)$ and $\sin(jx)$ with
integer $j$. -/
private theorem fourierPartialSum_periodic (f : ℝ → ℝ) (n : ℕ) :
    Function.Periodic (fourierPartialSum f n) (2 * π) := by
  intro x
  simp only [fourierPartialSum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (j : ℝ) * (x + 2 * π) = (j : ℝ) * x + (j : ℕ) * (2 * π) by ring,
    Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]

/-- Every real number $x$ has an integer $k$ with $x - 2\pi k \in [-\pi, \pi)$. -/
private theorem exists_int_sub_mem_Ico (x : ℝ) :
    ∃ k : ℤ, x - k * (2 * π) ∈ Set.Ico (-π) π := by
  refine ⟨toIcoDiv Real.two_pi_pos (-π) x, ?_⟩
  have hmem := toIcoMod_mem_Ico Real.two_pi_pos (-π) x
  have heq := toIcoMod_sub_self Real.two_pi_pos (-π) x
  rw [zsmul_eq_mul] at heq
  rw [show -π + 2 * π = π by ring] at hmem
  have hrw : toIcoMod Real.two_pi_pos (-π) x
      = x - (toIcoDiv Real.two_pi_pos (-π) x : ℤ) * (2 * π) := by
    push_cast at heq
    linarith
  rwa [hrw] at hmem

/-- For $j \ge 1$, $\int_{-\pi}^{0} \cos(jt)\, dt = 0$. -/
private theorem integral_cos_neg_pi_zero {j : ℕ} (hj : 0 < j) :
    (∫ t in -π..(0 : ℝ), Real.cos ((j : ℝ) * t)) = 0 := by
  have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  have hd : ∀ t ∈ Set.uIcc (-π) (0 : ℝ),
      HasDerivAt (fun s : ℝ => Real.sin ((j : ℝ) * s) / j) (Real.cos ((j : ℝ) * t)) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => (j : ℝ) * s) (j : ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul (j : ℝ)
    have h2 := (Real.hasDerivAt_sin ((j : ℝ) * t)).comp t h1
    simpa [Function.comp_def, mul_div_assoc, div_self hj0] using h2.div_const (j : ℝ)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ => Real.cos ((j : ℝ) * t)).intervalIntegrable _ _)]
  simp [mul_neg, Real.sin_nat_mul_pi]

/-- For $j \ge 1$, $\int_{-\pi}^{0} \sin(jt)\, dt = ((-1)^j - 1)/j$. -/
private theorem integral_sin_neg_pi_zero {j : ℕ} (hj : 0 < j) :
    (∫ t in -π..(0 : ℝ), Real.sin ((j : ℝ) * t)) = ((-1 : ℝ) ^ j - 1) / j := by
  have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  have hd : ∀ t ∈ Set.uIcc (-π) (0 : ℝ),
      HasDerivAt (fun s : ℝ => -(Real.cos ((j : ℝ) * s) / j)) (Real.sin ((j : ℝ) * t)) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => (j : ℝ) * s) (j : ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul (j : ℝ)
    have h2 : HasDerivAt (fun s : ℝ => Real.cos ((j : ℝ) * s))
        (-Real.sin ((j : ℝ) * t) * (j : ℝ)) t :=
      (Real.hasDerivAt_cos ((j : ℝ) * t)).comp t h1
    have h3 := (h2.div_const (j : ℝ)).neg
    have hv : -(-Real.sin ((j : ℝ) * t) * (j : ℝ) / (j : ℝ)) = Real.sin ((j : ℝ) * t) := by
      field_simp
    rwa [hv] at h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ => Real.sin ((j : ℝ) * t)).intervalIntegrable _ _)]
  rw [mul_zero, Real.cos_zero, show (j : ℝ) * -π = -((j : ℝ) * π) by ring, Real.cos_neg,
    Real.cos_nat_mul_pi]
  field_simp
  ring

/-- If $f$ is $2\pi$-periodic and $S_n f(y) \to f(y)$ for every $y \in [-\pi, \pi)$, then
$S_n f(x) \to f(x)$ for every $x \in \mathbb{R}$. -/
private theorem tendsto_fourierPartialSum_of_Ico {f : ℝ → ℝ}
    (hper : Function.Periodic f (2 * π))
    (h : ∀ y ∈ Set.Ico (-π) π, Tendsto (fun n : ℕ => fourierPartialSum f n y) atTop (𝓝 (f y)))
    (x : ℝ) : Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 (f x)) := by
  obtain ⟨k, hk⟩ := exists_int_sub_mem_Ico x
  rw [← hper.sub_int_mul_eq (x := x) k]
  exact (h _ hk).congr fun n => (fourierPartialSum_periodic f n).sub_int_mul_eq k

/-- If $(g(t) - c)/t = q(t)$ for $t \in (0, \pi)$ and $q(t) \to d$ as $t \to 0^+$, then
$(g(t) - c)/t \to d$ as $t \to 0^+$. -/
private theorem tendsto_quotient_of_eventually_eq {g q : ℝ → ℝ} {c d : ℝ}
    (h : ∀ t ∈ Set.Ioo (0 : ℝ) π, (g t - c) / t = q t) (hq : Tendsto q (𝓝[>] 0) (𝓝 d)) :
    Tendsto (fun t : ℝ => (g t - c) / t) (𝓝[>] 0) (𝓝 d) := by
  refine hq.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with t ht
  exact (h t ht).symm

/-- If $(g(t) - c)/t = d$ for $t \in (0, \pi)$, then $(g(t) - c)/t \to d$ as $t \to 0^+$. -/
private theorem tendsto_quotient_of_eventually_const {g : ℝ → ℝ} {c d : ℝ}
    (h : ∀ t ∈ Set.Ioo (0 : ℝ) π, (g t - c) / t = d) :
    Tendsto (fun t : ℝ => (g t - c) / t) (𝓝[>] 0) (𝓝 d) :=
  tendsto_quotient_of_eventually_eq h tendsto_const_nhds

/-- A function that agrees on $[-\pi, \pi]$ with a continuous function is integrable on
$[-\pi, \pi]$. -/
private theorem intervalIntegrable_of_eqOn {f F : ℝ → ℝ} (hF : Continuous F)
    (hval : ∀ x ∈ Set.Icc (-π) π, f x = F x) : IntervalIntegrable f volume (-π) π := by
  refine (hF.intervalIntegrable _ _).congr fun t ht => ?_
  rw [Set.uIoc_of_le (by linarith [Real.pi_pos]), Set.mem_Ioc] at ht
  exact (hval t ⟨ht.1.le, ht.2⟩).symm

/-- If $f = F$ on $[-\pi, \pi]$, then $\int_{-\pi}^{\pi} f g = \int_{-\pi}^{\pi} F g$ for every $g$.
-/
private theorem integral_congr_of_eqOn {f F : ℝ → ℝ}
    (hval : ∀ x ∈ Set.Icc (-π) π, f x = F x) (g : ℝ → ℝ) :
    (∫ t in -π..π, f t * g t) = ∫ t in -π..π, F t * g t := by
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
  rw [hval t ht]

/-! ### Example 4.1.3: a step function -/

/-- For the step function of Example 4.1.3 and a continuous $g$, the product $fg$ is integrable on
$[-\pi, \pi]$ and $\int_{-\pi}^{\pi} f g = \int_{-\pi}^{0} g$. -/
private theorem step_integral {f : ℝ → ℝ} (hneg : ∀ x ∈ Set.Ico (-π) 0, f x = 1)
    (hpos : ∀ x ∈ Set.Ico (0 : ℝ) π, f x = 0) {g : ℝ → ℝ} (hg : Continuous g) :
    IntervalIntegrable (fun t => f t * g t) volume (-π) π ∧
      (∫ t in -π..π, f t * g t) = ∫ t in -π..(0 : ℝ), g t := by
  have hπ := Real.pi_pos
  have h1 : Set.EqOn g (fun t => f t * g t) (Set.uIoo (-π) 0) := by
    intro t ht
    rw [Set.uIoo_of_le (by linarith), Set.mem_Ioo] at ht
    simp [hneg t ⟨ht.1.le, ht.2⟩]
  have h2 : Set.EqOn (fun _ : ℝ => (0 : ℝ)) (fun t => f t * g t) (Set.uIoo 0 π) := by
    intro t ht
    rw [Set.uIoo_of_le hπ.le, Set.mem_Ioo] at ht
    simp [hpos t ⟨ht.1.le, ht.2⟩]
  have hi1 : IntervalIntegrable (fun t => f t * g t) volume (-π) 0 :=
    (hg.intervalIntegrable _ _).congr_uIoo h1
  have hi2 : IntervalIntegrable (fun t => f t * g t) volume 0 π :=
    (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo h2
  refine ⟨hi1.trans hi2, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
    ← intervalIntegral.integral_congr_uIoo h1, ← intervalIntegral.integral_congr_uIoo h2]
  simp

/-- The step function of Example 4.1.3 is integrable on $[-\pi, \pi]$. -/
private theorem step_intervalIntegrable {f : ℝ → ℝ} (hneg : ∀ x ∈ Set.Ico (-π) 0, f x = 1)
    (hpos : ∀ x ∈ Set.Ico (0 : ℝ) π, f x = 0) : IntervalIntegrable f volume (-π) π := by
  simpa using (step_integral hneg hpos (g := fun _ => (1 : ℝ)) continuous_const).1

/-- The cosine coefficients of the step function of Example 4.1.3 are $a_0 = 1$ and $a_j = 0$ for
$j \ge 1$. -/
private theorem step_fourierCoeffCos {f : ℝ → ℝ} (hneg : ∀ x ∈ Set.Ico (-π) 0, f x = 1)
    (hpos : ∀ x ∈ Set.Ico (0 : ℝ) π, f x = 0) :
    fourierCoeffCos f 0 = 1 ∧ ∀ j : ℕ, 0 < j → fourierCoeffCos f j = 0 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  constructor
  · have hval : (∫ t in -π..(0 : ℝ), Real.cos (((0 : ℕ) : ℝ) * t)) = π := by simp
    rw [fourierCoeffCos, (step_integral hneg hpos (g := fun t => Real.cos (((0 : ℕ) : ℝ) * t))
      (by fun_prop)).2, hval]
    field_simp
  · intro j hj
    rw [fourierCoeffCos, (step_integral hneg hpos (g := fun t => Real.cos ((j : ℝ) * t))
      (by fun_prop)).2, integral_cos_neg_pi_zero hj, mul_zero]

/-- The sine coefficients of the step function of Example 4.1.3 are $b_j = -(1 - (-1)^j)/(\pi j)$
for $j \ge 1$. -/
private theorem step_fourierCoeffSin {f : ℝ → ℝ} (hneg : ∀ x ∈ Set.Ico (-π) 0, f x = 1)
    (hpos : ∀ x ∈ Set.Ico (0 : ℝ) π, f x = 0) (j : ℕ) (hj : 0 < j) :
    fourierCoeffSin f j = -(1 - (-1 : ℝ) ^ j) / (π * j) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  rw [fourierCoeffSin, (step_integral hneg hpos (g := fun t => Real.sin ((j : ℝ) * t))
    (by fun_prop)).2, integral_sin_neg_pi_zero hj]
  field_simp
  ring

/-- With the coefficients of the step function of Example 4.1.3, $S_{2n} f(x) = 1/2 - (2/\pi)
\sum_{i < n} \sin((2i + 1)x)/(2i + 1)$. -/
private theorem step_fourierPartialSum {f : ℝ → ℝ} (hcos0 : fourierCoeffCos f 0 = 1)
    (hcos : ∀ j : ℕ, 0 < j → fourierCoeffCos f j = 0)
    (hsin : ∀ j : ℕ, 0 < j → fourierCoeffSin f j = -(1 - (-1 : ℝ) ^ j) / (π * j)) (n : ℕ)
    (x : ℝ) :
    fourierPartialSum f (2 * n) x
      = 1 / 2 - 2 / π * ∑ i ∈ Finset.range n, Real.sin ((2 * i + 1) * x) / (2 * i + 1) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  induction n with
  | zero => simp [fourierPartialSum, hcos0]
  | succ n ih =>
      have hstep : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      have hodd : ((-1 : ℝ)) ^ (2 * n + 1) = -1 := by
        rw [pow_succ, pow_mul]; norm_num
      have heven : ((-1 : ℝ)) ^ (2 * n + 1 + 1) = 1 := by
        rw [pow_succ, hodd]; norm_num
      have hne : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      rw [hstep, fourierPartialSum_succ, fourierPartialSum_succ, ih, Finset.sum_range_succ,
        hcos (2 * n + 1) (by omega), hcos (2 * n + 1 + 1) (by omega),
        hsin (2 * n + 1) (by omega), hsin (2 * n + 1 + 1) (by omega), hodd, heven]
      set S := ∑ i ∈ Finset.range n, Real.sin ((2 * (i : ℝ) + 1) * x) / (2 * (i : ℝ) + 1) with hS
      simp only [sub_self, neg_zero, zero_div, zero_mul, add_zero, zero_add]
      push_cast
      field_simp
      ring

/-- The step function of Example 4.1.3 has derivative $0$ at every point that is not a multiple of
$\pi$. -/
private theorem step_hasDerivAt {f : ℝ → ℝ} (hper : Function.Periodic f (2 * π))
    (hneg : ∀ x ∈ Set.Ico (-π) 0, f x = 1) (hpos : ∀ x ∈ Set.Ico (0 : ℝ) π, f x = 0) {x : ℝ}
    (hx : ∀ k : ℤ, x ≠ k * π) : HasDerivAt f 0 x := by
  have hπ := Real.pi_pos
  obtain ⟨k, hk⟩ := exists_int_sub_mem_Ico x
  have hval : ∀ t : ℝ, f t = f (t - k * (2 * π)) := fun t =>
    (hper.sub_int_mul_eq (x := t) k).symm
  have hy0 : x - k * (2 * π) ≠ 0 := fun h => hx (2 * k) (by push_cast; linarith)
  have hyπ : -π < x - k * (2 * π) :=
    lt_of_le_of_ne hk.1 fun h => hx (2 * k - 1) (by push_cast; linarith)
  rcases lt_or_gt_of_ne hy0 with hlt | hgt
  · have hnb : ∀ᶠ t in 𝓝 x, f t = 1 := by
      have hopen : Set.Ioo (-π + k * (2 * π)) (0 + k * (2 * π)) ∈ 𝓝 x :=
        isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
      filter_upwards [hopen] with t ht
      exact (hval t).trans (hneg _ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    exact (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq hnb
  · have hnb : ∀ᶠ t in 𝓝 x, f t = 0 := by
      have hopen : Set.Ioo (0 + k * (2 * π)) (π + k * (2 * π)) ∈ 𝓝 x :=
        isOpen_Ioo.mem_nhds ⟨by linarith, by linarith [hk.2]⟩
      filter_upwards [hopen] with t ht
      exact (hval t).trans (hpos _ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hnb

/-- At every multiple of $\pi$, the Fourier partial sums of the step function of Example 4.1.3
converge to $1/2$. -/
private theorem step_tendsto_at_pi {f : ℝ → ℝ} (hper : Function.Periodic f (2 * π))
    (hneg : ∀ x ∈ Set.Ico (-π) 0, f x = 1) (hpos : ∀ x ∈ Set.Ico (0 : ℝ) π, f x = 0) (k : ℤ) :
    Tendsto (fun n : ℕ => fourierPartialSum f n ((k : ℝ) * π)) atTop (𝓝 (1 / 2)) := by
  have hπ := Real.pi_pos
  have hval : ∀ (t : ℝ) (m : ℤ), f t = f (t - m * (2 * π)) := fun t m =>
    (hper.sub_int_mul_eq (x := t) m).symm
  obtain ⟨fL, fR, hLval, hRval, hmean⟩ :
      ∃ fL fR : ℝ, (∀ t ∈ Set.Ioo (0 : ℝ) π, f ((k : ℝ) * π - t) = fL) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) π, f ((k : ℝ) * π + t) = fR) ∧ (fL + fR) / 2 = 1 / 2 := by
    rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      refine ⟨1, 0, fun t ht => ?_, fun t ht => ?_, by norm_num⟩
      · rw [hval _ m]
        refine hneg _ ⟨?_, ?_⟩ <;> push_cast <;> linarith [ht.1, ht.2]
      · rw [hval _ m]
        refine hpos _ ⟨?_, ?_⟩ <;> push_cast <;> linarith [ht.1, ht.2]
    · subst hm
      refine ⟨0, 1, fun t ht => ?_, fun t ht => ?_, by norm_num⟩
      · rw [hval _ m]
        refine hpos _ ⟨?_, ?_⟩ <;> push_cast <;> linarith [ht.1, ht.2]
      · rw [hval _ (m + 1)]
        refine hneg _ ⟨?_, ?_⟩ <;> push_cast <;> linarith [ht.1, ht.2]
  rw [← hmean]
  exact theorem_4_1_1 hper (step_intervalIntegrable hneg hpos)
    (tendsto_quotient_of_eventually_const (d := 0)
      fun t ht => by rw [hRval t ht, sub_self, zero_div])
    (tendsto_quotient_of_eventually_const (d := 0)
      fun t ht => by rw [hLval t ht, sub_self, zero_div])

/-- **Example 4.1.3** of [han2009theoretical]. Let $f : \mathbb{R} \to \mathbb{R}$ be
$2\pi$-periodic with $f(x) = 1$ for $x \in [-\pi, 0)$ and $f(x) = 0$ for $x \in [0, \pi)$. Then

* $a_0 = 1$, $a_j = 0$ for $j \ge 1$, and $b_j = -(1 - (-1)^j)/(\pi j)$ for $j \ge 1$;
* for all $n \ge 0$ and $x \in \mathbb{R}$, $S_{2n} f(x) = \dfrac{1}{2} - \dfrac{2}{\pi}
  \sum_{i=0}^{n-1} \dfrac{\sin((2i + 1)x)}{2i + 1}$;
* $S_n f(x) \to f(x)$ at every $x$ that is not a multiple of $\pi$;
* $S_n f(k\pi) \to 1/2$ for every $k \in \mathbb{Z}$, the mean of the one-sided limits at the
  jump;
* at every $x$ that is not a multiple of $\pi$, the series $\sum_{i \ge 0} -\frac{2}{\pi}
  \frac{\sin((2i + 1)x)}{2i + 1}$ converges to $f(x) - 1/2$.

The even coefficients $b_{2i}$ vanish, so the partial sums have only odd harmonics. The book
indexes the sum from $j = 1$ to $n$ with terms $\sin((2j - 1)x)/(2j - 1)$, which is the same
sum. The last part is the book's $F(x) = f(x)$, with the series convergence of Definition
1.2.17. The convergence is Theorem 4.1.1.

The Gibbs phenomenon that the book discusses beside this example is not stated: the book asserts
the overshoot $(2/\pi) \operatorname{Si}(\pi) |f(x+) - f(x-)|$, with
$(2/\pi) \operatorname{Si}(\pi) \approx 1.17898$, without proof. Note that
`AtkinsonHan.Chapter04.equation_4_1_3_const`, `AtkinsonHan.Chapter04.equation_4_1_3_cos` and
`AtkinsonHan.Chapter04.equation_4_1_3_sin` are the book's displayed equations (4.1.2)–(4.1.3) on
the real Fourier coefficients, and are not about this example. -/
theorem example_4_1_3 {f : ℝ → ℝ} (hper : Function.Periodic f (2 * π))
    (hneg : ∀ x ∈ Set.Ico (-π) 0, f x = 1) (hpos : ∀ x ∈ Set.Ico (0 : ℝ) π, f x = 0) :
    fourierCoeffCos f 0 = 1 ∧
      (∀ j : ℕ, 0 < j → fourierCoeffCos f j = 0) ∧
      (∀ j : ℕ, 0 < j → fourierCoeffSin f j = -(1 - (-1 : ℝ) ^ j) / (π * j)) ∧
      (∀ (n : ℕ) (x : ℝ), fourierPartialSum f (2 * n) x
        = 1 / 2 - 2 / π * ∑ i ∈ Finset.range n, Real.sin ((2 * i + 1) * x) / (2 * i + 1)) ∧
      (∀ x : ℝ, (∀ k : ℤ, x ≠ (k : ℝ) * π) →
        Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 (f x))) ∧
      (∀ k : ℤ, Tendsto (fun n : ℕ => fourierPartialSum f n ((k : ℝ) * π)) atTop (𝓝 (1 / 2))) ∧
      ∀ x : ℝ, (∀ k : ℤ, x ≠ (k : ℝ) * π) →
        Chapter01.definition_1_2_17
          (fun i : ℕ => -(2 / π) * (Real.sin ((2 * i + 1) * x) / (2 * i + 1))) (f x - 1 / 2) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  obtain ⟨hcos0, hcos⟩ := step_fourierCoeffCos hneg hpos
  have hsin := step_fourierCoeffSin hneg hpos
  have hpartial := step_fourierPartialSum hcos0 hcos hsin
  have hconv : ∀ x : ℝ, (∀ k : ℤ, x ≠ (k : ℝ) * π) →
      Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 (f x)) := fun x hx =>
    theorem_4_1_1_continuous hper (step_intervalIntegrable hneg hpos)
      (step_hasDerivAt hper hneg hpos hx)
  refine ⟨hcos0, hcos, hsin, hpartial, hconv, step_tendsto_at_pi hper hneg hpos, fun x hx => ?_⟩
  have hdouble : Tendsto (fun n : ℕ => fourierPartialSum f (2 * n) x) atTop (𝓝 (f x)) :=
    (hconv x hx).comp (Filter.tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩)
  have hclosed : Tendsto (fun n : ℕ =>
      1 / 2 - 2 / π * ∑ i ∈ Finset.range n, Real.sin ((2 * i + 1) * x) / (2 * i + 1)) atTop
      (𝓝 (f x)) := hdouble.congr fun n => hpartial n x
  refine (Chapter01.definition_1_2_17_iff _ _).mpr ((hclosed.sub_const (1 / 2)).congr fun n => ?_)
  rw [← Finset.mul_sum]
  ring

/-! ### Example 4.1.4: $|x|/\pi$ -/

/-- For $j \ge 1$, $\int_0^\pi t \cos(jt)\, dt = ((-1)^j - 1)/j^2$. -/
private theorem integral_mul_cos_zero_pi {j : ℕ} (hj : 0 < j) :
    (∫ t in (0 : ℝ)..π, t * Real.cos ((j : ℝ) * t)) = ((-1 : ℝ) ^ j - 1) / j ^ 2 := by
  have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) π,
      HasDerivAt (fun s : ℝ => s * Real.sin ((j : ℝ) * s) / j + Real.cos ((j : ℝ) * s) / j ^ 2)
        (t * Real.cos ((j : ℝ) * t)) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => (j : ℝ) * s) (j : ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul (j : ℝ)
    have hs : HasDerivAt (fun s : ℝ => Real.sin ((j : ℝ) * s))
        (Real.cos ((j : ℝ) * t) * (j : ℝ)) t := (Real.hasDerivAt_sin _).comp t h1
    have hc : HasDerivAt (fun s : ℝ => Real.cos ((j : ℝ) * s))
        (-Real.sin ((j : ℝ) * t) * (j : ℝ)) t := (Real.hasDerivAt_cos _).comp t h1
    have h2 : HasDerivAt (fun s : ℝ => s * Real.sin ((j : ℝ) * s) / j
          + Real.cos ((j : ℝ) * s) / j ^ 2)
        ((1 * Real.sin ((j : ℝ) * t) + t * (Real.cos ((j : ℝ) * t) * (j : ℝ))) / (j : ℝ)
          + -Real.sin ((j : ℝ) * t) * (j : ℝ) / (j : ℝ) ^ 2) t :=
      (((hasDerivAt_id t).mul hs).div_const (j : ℝ)).add (hc.div_const ((j : ℝ) ^ 2))
    have hv : (1 * Real.sin ((j : ℝ) * t) + t * (Real.cos ((j : ℝ) * t) * (j : ℝ))) / (j : ℝ)
          + -Real.sin ((j : ℝ) * t) * (j : ℝ) / (j : ℝ) ^ 2 = t * Real.cos ((j : ℝ) * t) := by
      field_simp
      ring
    rwa [hv] at h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ => t * Real.cos ((j : ℝ) * t)).intervalIntegrable _ _),
    Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, zero_div, zero_add]
  rw [div_sub_div_same]

/-- The Fourier coefficients of $|x|/\pi$ are $b_j = 0$, $a_0 = 1$ and
$a_j = 2((-1)^j - 1)/(\pi^2 j^2)$ for $j \ge 1$. -/
private theorem abs_fourierCoeff {f : ℝ → ℝ} (hval : ∀ x ∈ Set.Icc (-π) π, f x = |x| / π) :
    (∀ j : ℕ, fourierCoeffSin f j = 0) ∧ fourierCoeffCos f 0 = 1 ∧
      ∀ j : ℕ, 0 < j → fourierCoeffCos f j = 2 * ((-1 : ℝ) ^ j - 1) / (π ^ 2 * j ^ 2) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hπ0 := Real.pi_pos
  refine ⟨fun j => ?_, ?_, fun j hj => ?_⟩
  · rw [fourierCoeffSin, integral_congr_of_eqOn hval _,
      intervalIntegral_of_odd (g := fun t => |t| / π * Real.sin ((j : ℝ) * t))
        (fun t => by rw [abs_neg, mul_neg, Real.sin_neg]; ring)
        ((by fun_prop : Continuous fun t : ℝ =>
          |t| / π * Real.sin ((j : ℝ) * t)).intervalIntegrable _ _), mul_zero]
  · have hEq : ∀ t ∈ Set.uIcc (0 : ℝ) π, |t| / π = t / π := by
      intro t ht
      rw [Set.uIcc_of_le hπ0.le, Set.mem_Icc] at ht
      rw [abs_of_nonneg ht.1]
    have heven : (∫ t in -π..π, |t| / π * Real.cos (((0 : ℕ) : ℝ) * t))
        = 2 * ∫ t in (0 : ℝ)..π, |t| / π * Real.cos (((0 : ℕ) : ℝ) * t) :=
      intervalIntegral_of_even (fun t => by rw [abs_neg, mul_neg, Real.cos_neg])
        ((by fun_prop : Continuous fun t : ℝ =>
          |t| / π * Real.cos (((0 : ℕ) : ℝ) * t)).intervalIntegrable _ _)
    rw [fourierCoeffCos, integral_congr_of_eqOn hval _, heven]
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one]
    rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_div, integral_id]
    field_simp
    ring
  · have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
    have hEq : ∀ t ∈ Set.uIcc (0 : ℝ) π,
        |t| / π * Real.cos ((j : ℝ) * t) = t * Real.cos ((j : ℝ) * t) / π := by
      intro t ht
      rw [Set.uIcc_of_le hπ0.le, Set.mem_Icc] at ht
      rw [abs_of_nonneg ht.1]
      ring
    have heven : (∫ t in -π..π, |t| / π * Real.cos ((j : ℝ) * t))
        = 2 * ∫ t in (0 : ℝ)..π, |t| / π * Real.cos ((j : ℝ) * t) :=
      intervalIntegral_of_even (fun t => by rw [abs_neg, mul_neg, Real.cos_neg])
        ((by fun_prop : Continuous fun t : ℝ =>
          |t| / π * Real.cos ((j : ℝ) * t)).intervalIntegrable _ _)
    rw [fourierCoeffCos, integral_congr_of_eqOn hval _, heven,
      intervalIntegral.integral_congr hEq, intervalIntegral.integral_div,
      integral_mul_cos_zero_pi hj]
    field_simp

/-- With the coefficients of $|x|/\pi$, $S_{2n} f(x) = 1/2 - (4/\pi^2) \sum_{i < n} \cos((2i +
1)x)/(2i + 1)^2$. -/
private theorem abs_fourierPartialSum {f : ℝ → ℝ} (hsin : ∀ j : ℕ, fourierCoeffSin f j = 0)
    (hcos0 : fourierCoeffCos f 0 = 1)
    (hcos : ∀ j : ℕ, 0 < j → fourierCoeffCos f j = 2 * ((-1 : ℝ) ^ j - 1) / (π ^ 2 * j ^ 2))
    (n : ℕ) (x : ℝ) :
    fourierPartialSum f (2 * n) x
      = 1 / 2 - 4 / π ^ 2 * ∑ i ∈ Finset.range n,
          Real.cos ((2 * i + 1) * x) / (2 * i + 1) ^ 2 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  induction n with
  | zero => simp [fourierPartialSum, hcos0]
  | succ n ih =>
      have hstep : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      have hodd : ((-1 : ℝ)) ^ (2 * n + 1) = -1 := by
        rw [pow_succ, pow_mul]; norm_num
      have heven : ((-1 : ℝ)) ^ (2 * n + 1 + 1) = 1 := by
        rw [pow_succ, hodd]; norm_num
      have hne : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      rw [hstep, fourierPartialSum_succ, fourierPartialSum_succ, ih, Finset.sum_range_succ,
        hcos (2 * n + 1) (by omega), hcos (2 * n + 1 + 1) (by omega), hsin (2 * n + 1),
        hsin (2 * n + 1 + 1), hodd, heven]
      set S := ∑ i ∈ Finset.range n, Real.cos ((2 * (i : ℝ) + 1) * x) / (2 * (i : ℝ) + 1) ^ 2
        with hS
      simp only [sub_self, mul_zero, zero_div, zero_mul, add_zero]
      push_cast
      field_simp
      ring

/-- The Fourier series of the periodic extension of $|x|/\pi$ converges to it at every real point,
by Theorem 4.1.1. -/
private theorem abs_tendsto {f : ℝ → ℝ} (hper : Function.Periodic f (2 * π))
    (hval : ∀ x ∈ Set.Icc (-π) π, f x = |x| / π) (x : ℝ) :
    Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 (f x)) := by
  have hπ := Real.pi_pos
  have hπ' : π ≠ 0 := Real.pi_ne_zero
  have hfi := intervalIntegrable_of_eqOn (F := fun x : ℝ => |x| / π) (by fun_prop) hval
  refine tendsto_fourierPartialSum_of_Ico hper (fun y hy => ?_) x
  rcases eq_or_lt_of_le hy.1 with hyl | hyl
  · -- `y = -π`: the peak of the periodic extension
    subst hyl
    have hfy : f (-π) = 1 := by
      rw [hval _ ⟨le_rfl, by linarith⟩, abs_neg, abs_of_pos hπ]
      field_simp
    have hR : ∀ t ∈ Set.Ioo (0 : ℝ) π, (f (-π + t) - 1) / t = -(1 / π) := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      rw [hval _ ⟨by linarith [ht.1], by linarith [ht.2]⟩,
        abs_of_nonpos (by linarith [ht.2] : -π + t ≤ 0)]
      field_simp
      ring
    have hL : ∀ t ∈ Set.Ioo (0 : ℝ) π, (f (-π - t) - 1) / t = -(1 / π) := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      rw [← hper.sub_int_mul_eq (x := -π - t) (-1),
        hval _ ⟨by push_cast; linarith [ht.2], by push_cast; linarith [ht.1]⟩,
        abs_of_nonneg (by push_cast; linarith [ht.2] :
          (0 : ℝ) ≤ -π - t - ((-1 : ℤ) : ℝ) * (2 * π))]
      push_cast
      field_simp
      ring
    have hconv := theorem_4_1_1 hper hfi (tendsto_quotient_of_eventually_const hR)
      (tendsto_quotient_of_eventually_const hL)
    rw [hfy]
    rwa [show ((1 : ℝ) + 1) / 2 = 1 by norm_num] at hconv
  rcases lt_trichotomy y 0 with hlt | heq | hgt
  · -- `y ∈ (-π, 0)`: the extension is `-y/π` near `y`
    have hnb : ∀ᶠ t in 𝓝 y, f t = -t / π := by
      filter_upwards [isOpen_Ioo.mem_nhds (⟨hyl, hlt⟩ : y ∈ Set.Ioo (-π) 0)] with t ht
      rw [hval t ⟨ht.1.le, by linarith [ht.2]⟩, abs_of_neg ht.2]
    have hderiv : HasDerivAt (fun t : ℝ => -t / π) (-1 / π) y :=
      ((hasDerivAt_id y).neg).div_const π
    exact theorem_4_1_1_continuous hper hfi (hderiv.congr_of_eventuallyEq hnb)
  · -- `y = 0`: the corner at the bottom
    subst heq
    have hfy : f 0 = 0 := by rw [hval _ ⟨by linarith, by linarith⟩]; simp
    have hR : ∀ t ∈ Set.Ioo (0 : ℝ) π, (f (0 + t) - 0) / t = 1 / π := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      rw [zero_add, hval _ ⟨by linarith [ht.1], ht.2.le⟩, abs_of_pos ht.1]
      field_simp
      ring
    have hL : ∀ t ∈ Set.Ioo (0 : ℝ) π, (f (0 - t) - 0) / t = 1 / π := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      rw [zero_sub, hval _ ⟨by linarith [ht.2], by linarith [ht.1]⟩, abs_neg, abs_of_pos ht.1]
      field_simp
      ring
    have hconv := theorem_4_1_1 hper hfi (tendsto_quotient_of_eventually_const hR)
      (tendsto_quotient_of_eventually_const hL)
    rw [hfy]
    rwa [show ((0 : ℝ) + 0) / 2 = 0 by norm_num] at hconv
  · -- `y ∈ (0, π)`: the extension is `y/π` near `y`
    have hnb : ∀ᶠ t in 𝓝 y, f t = t / π := by
      filter_upwards [isOpen_Ioo.mem_nhds (⟨hgt, hy.2⟩ : y ∈ Set.Ioo 0 π)] with t ht
      rw [hval t ⟨by linarith [ht.1], ht.2.le⟩, abs_of_pos ht.1]
    have hderiv : HasDerivAt (fun t : ℝ => t / π) (1 / π) y := (hasDerivAt_id y).div_const π
    exact theorem_4_1_1_continuous hper hfi (hderiv.congr_of_eventuallyEq hnb)

/-- **Example 4.1.4** of [han2009theoretical]. Let $f : \mathbb{R} \to \mathbb{R}$ be
$2\pi$-periodic with $f(x) = |x|/\pi$ for $x \in [-\pi, \pi]$. Then

* $b_j = 0$ for all $j$, $a_0 = 1$, and $a_j = 2((-1)^j - 1)/(\pi^2 j^2)$ for $j \ge 1$;
* for all $n \ge 0$ and $x \in \mathbb{R}$, $S_{2n} f(x) = \dfrac{1}{2} - \dfrac{4}{\pi^2}
  \sum_{i=0}^{n-1} \dfrac{\cos((2i + 1)x)}{(2i + 1)^2}$;
* $S_n f(x) \to f(x)$ for every $x \in \mathbb{R}$;
* for every $x$, the series $\sum_{i \ge 0} -\frac{4}{\pi^2} \frac{\cos((2i + 1)x)}{(2i + 1)^2}$
  converges to $f(x) - 1/2$.

The extension is continuous because $f(-\pi) = f(\pi)$. The function is even, so its series has
no sine terms, and $a_j = 0$ for even $j \ge 2$. The book indexes the sum from $j = 1$ to $n$
with terms $\cos((2j - 1)x)/(2j - 1)^2$, which is the same sum. The extension is differentiable
off the multiples of $\pi$ and has equal one-sided difference quotients at the corners, so the
series converges everywhere by Theorem 4.1.1. The last part is the book's $F(x) = f(x)$, with
the series convergence of Definition 1.2.17. The book's other claim here, convergence in
$L^2(-\pi, \pi)$, is `AtkinsonHan.Chapter04.equation_4_1_14` for this $f$. -/
theorem example_4_1_4 {f : ℝ → ℝ} (hper : Function.Periodic f (2 * π))
    (hval : ∀ x ∈ Set.Icc (-π) π, f x = |x| / π) :
    (∀ j : ℕ, fourierCoeffSin f j = 0) ∧
      fourierCoeffCos f 0 = 1 ∧
      (∀ j : ℕ, 0 < j → fourierCoeffCos f j = 2 * ((-1 : ℝ) ^ j - 1) / (π ^ 2 * j ^ 2)) ∧
      (∀ (n : ℕ) (x : ℝ), fourierPartialSum f (2 * n) x
        = 1 / 2 - 4 / π ^ 2 * ∑ i ∈ Finset.range n,
            Real.cos ((2 * i + 1) * x) / (2 * i + 1) ^ 2) ∧
      (∀ x : ℝ, Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 (f x))) ∧
      ∀ x : ℝ, Chapter01.definition_1_2_17
        (fun i : ℕ => -(4 / π ^ 2) * (Real.cos ((2 * i + 1) * x) / (2 * i + 1) ^ 2))
        (f x - 1 / 2) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  obtain ⟨hsin, hcos0, hcos⟩ := abs_fourierCoeff hval
  have hpartial := abs_fourierPartialSum hsin hcos0 hcos
  have hconv := abs_tendsto hper hval
  refine ⟨hsin, hcos0, hcos, hpartial, hconv, fun x => ?_⟩
  have hdouble : Tendsto (fun n : ℕ => fourierPartialSum f (2 * n) x) atTop (𝓝 (f x)) :=
    (hconv x).comp (Filter.tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩)
  have hclosed : Tendsto (fun n : ℕ => 1 / 2 - 4 / π ^ 2 * ∑ i ∈ Finset.range n,
      Real.cos ((2 * i + 1) * x) / (2 * i + 1) ^ 2) atTop (𝓝 (f x)) :=
    hdouble.congr fun n => hpartial n x
  refine (Chapter01.definition_1_2_17_iff _ _).mpr ((hclosed.sub_const (1 / 2)).congr fun n => ?_)
  rw [← Finset.mul_sum]
  ring

/-! ### Example 4.1.5: $(\pi^2 - x^2)^2/\pi^4$ -/

/-- The derivative of $s \mapsto P(s) \sin(ws)$ at $t$ is $c \sin(wt) + P(t) w \cos(wt)$, where
$c = P'(t)$. -/
private theorem hasDerivAt_mul_sin {P : ℝ → ℝ} {c w t : ℝ} (hP : HasDerivAt P c t) :
    HasDerivAt (fun s => P s * Real.sin (w * s))
      (c * Real.sin (w * t) + P t * (Real.cos (w * t) * w)) t :=
  hP.mul ((Real.hasDerivAt_sin (w * t)).comp t (by simpa using (hasDerivAt_id t).const_mul w))

/-- The derivative of $s \mapsto P(s) \cos(ws)$ at $t$ is $c \cos(wt) - P(t) w \sin(wt)$, where
$c = P'(t)$. -/
private theorem hasDerivAt_mul_cos {P : ℝ → ℝ} {c w t : ℝ} (hP : HasDerivAt P c t) :
    HasDerivAt (fun s => P s * Real.cos (w * s))
      (c * Real.cos (w * t) + P t * (-Real.sin (w * t) * w)) t :=
  hP.mul ((Real.hasDerivAt_cos (w * t)).comp t (by simpa using (hasDerivAt_id t).const_mul w))

/-- The derivative of a polynomial of degree at most $5$. -/
private theorem hasDerivAt_quintic (a b c d e g t : ℝ) :
    HasDerivAt (fun s : ℝ => a * s ^ 5 + b * s ^ 4 + c * s ^ 3 + d * s ^ 2 + e * s + g)
      (5 * a * t ^ 4 + 4 * b * t ^ 3 + 3 * c * t ^ 2 + 2 * d * t + e) t := by
  refine HasDerivAt.congr_deriv
    (((((((hasDerivAt_pow 5 t).const_mul a).add ((hasDerivAt_pow 4 t).const_mul b)).add
      ((hasDerivAt_pow 3 t).const_mul c)).add ((hasDerivAt_pow 2 t).const_mul d)).add
      ((hasDerivAt_id t).const_mul e)).add_const g) ?_
  push_cast
  ring

/-- The derivative of $(\pi^2 - x^2)^2/\pi^4$ is $(4x^3 - 4\pi^2 x)/\pi^4$. -/
private theorem hasDerivAt_quarticNorm (y : ℝ) :
    HasDerivAt (fun t : ℝ => (π ^ 2 - t ^ 2) ^ 2 / π ^ 4)
      ((4 * y ^ 3 - 4 * π ^ 2 * y) / π ^ 4) y := by
  refine HasDerivAt.congr_deriv
    ((((hasDerivAt_pow 2 y).const_sub (π ^ 2)).pow 2).div_const (π ^ 4)) ?_
  push_cast
  ring

/-- The derivative of $(4x^3 - 4\pi^2 x)/\pi^4$ is $(12x^2 - 4\pi^2)/\pi^4$. -/
private theorem hasDerivAt_quarticNorm' (y : ℝ) :
    HasDerivAt (fun t : ℝ => (4 * t ^ 3 - 4 * π ^ 2 * t) / π ^ 4)
      ((12 * y ^ 2 - 4 * π ^ 2) / π ^ 4) y := by
  refine HasDerivAt.congr_deriv
    ((((hasDerivAt_pow 3 y).const_mul (4 : ℝ)).sub
      ((hasDerivAt_id y).const_mul (4 * π ^ 2))).div_const (π ^ 4)) ?_
  push_cast
  ring

/-- $\int_{-\pi}^{\pi} (\pi^2 - t^2)^2\, dt = 16\pi^5/15$. -/
private theorem integral_quartic : (∫ t in -π..π, (π ^ 2 - t ^ 2) ^ 2) = 16 * π ^ 5 / 15 := by
  have hd : ∀ t ∈ Set.uIcc (-π) π,
      HasDerivAt (fun s : ℝ => (1 / 5) * s ^ 5 + 0 * s ^ 4 + (-(2 * π ^ 2) / 3) * s ^ 3
          + 0 * s ^ 2 + π ^ 4 * s + 0)
        ((π ^ 2 - t ^ 2) ^ 2) t := fun t _ =>
    (hasDerivAt_quintic (1 / 5) 0 (-(2 * π ^ 2) / 3) 0 (π ^ 4) 0 t).congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ => (π ^ 2 - t ^ 2) ^ 2).intervalIntegrable _ _)]
  ring

/-- For $j \ge 1$, $\int_{-\pi}^{\pi} (\pi^2 - t^2)^2 \cos(jt)\, dt = -48\pi (-1)^j / j^4$, by four
integrations by parts. -/
private theorem integral_quartic_mul_cos {j : ℕ} (hj : 0 < j) :
    (∫ t in -π..π, (π ^ 2 - t ^ 2) ^ 2 * Real.cos ((j : ℝ) * t))
      = -48 * π * (-1 : ℝ) ^ j / j ^ 4 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  have hd : ∀ t ∈ Set.uIcc (-π) π,
      HasDerivAt (fun s : ℝ =>
          ((0 * s ^ 5 + (j : ℝ) ^ 4 * s ^ 4 + 0 * s ^ 3
                + (-(2 * π ^ 2 * (j : ℝ) ^ 4) - 12 * (j : ℝ) ^ 2) * s ^ 2 + 0 * s
                + (π ^ 4 * (j : ℝ) ^ 4 + 4 * π ^ 2 * (j : ℝ) ^ 2 + 24)) * Real.sin ((j : ℝ) * s)
            + (0 * s ^ 5 + 0 * s ^ 4 + 4 * (j : ℝ) ^ 3 * s ^ 3 + 0 * s ^ 2
                + (-(4 * π ^ 2 * (j : ℝ) ^ 3) - 24 * (j : ℝ)) * s + 0) * Real.cos ((j : ℝ) * s))
          / (j : ℝ) ^ 5)
        ((π ^ 2 - t ^ 2) ^ 2 * Real.cos ((j : ℝ) * t)) t := by
    intro t _
    refine HasDerivAt.congr_deriv
      (((hasDerivAt_mul_sin (hasDerivAt_quintic 0 ((j : ℝ) ^ 4) 0
            (-(2 * π ^ 2 * (j : ℝ) ^ 4) - 12 * (j : ℝ) ^ 2) 0
            (π ^ 4 * (j : ℝ) ^ 4 + 4 * π ^ 2 * (j : ℝ) ^ 2 + 24) t)).add
        (hasDerivAt_mul_cos (hasDerivAt_quintic 0 0 (4 * (j : ℝ) ^ 3) 0
            (-(4 * π ^ 2 * (j : ℝ) ^ 3) - 24 * (j : ℝ)) 0 t))).div_const ((j : ℝ) ^ 5)) ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ =>
      (π ^ 2 - t ^ 2) ^ 2 * Real.cos ((j : ℝ) * t)).intervalIntegrable _ _),
    show ((j : ℝ)) * -π = -((j : ℝ) * π) by ring, Real.sin_neg, Real.cos_neg,
    Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  field_simp
  ring

/-- The Fourier coefficients of $(\pi^2 - x^2)^2/\pi^4$ are $b_j = 0$, $a_0 = 16/15$ and
$a_j = 48(-1)^{j+1}/(\pi^4 j^4)$ for $j \ge 1$. -/
private theorem quartic_fourierCoeff {f : ℝ → ℝ}
    (hval : ∀ x ∈ Set.Icc (-π) π, f x = (π ^ 2 - x ^ 2) ^ 2 / π ^ 4) :
    (∀ j : ℕ, fourierCoeffSin f j = 0) ∧ fourierCoeffCos f 0 = 16 / 15 ∧
      ∀ j : ℕ, 0 < j → fourierCoeffCos f j = 48 * (-1 : ℝ) ^ (j + 1) / (π ^ 4 * j ^ 4) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  refine ⟨fun j => ?_, ?_, fun j hj => ?_⟩
  · rw [fourierCoeffSin, integral_congr_of_eqOn hval _,
      intervalIntegral_of_odd (g := fun t => (π ^ 2 - t ^ 2) ^ 2 / π ^ 4 * Real.sin ((j : ℝ) * t))
        (fun t => by rw [mul_neg, Real.sin_neg]; ring)
        ((by fun_prop : Continuous fun t : ℝ =>
          (π ^ 2 - t ^ 2) ^ 2 / π ^ 4 * Real.sin ((j : ℝ) * t)).intervalIntegrable _ _), mul_zero]
  · rw [fourierCoeffCos, integral_congr_of_eqOn hval _]
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one]
    rw [intervalIntegral.integral_div, integral_quartic]
    field_simp
  · have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
    rw [fourierCoeffCos, integral_congr_of_eqOn hval _]
    simp only [div_mul_eq_mul_div]
    rw [intervalIntegral.integral_div, integral_quartic_mul_cos hj]
    field_simp
    ring

/-- With the coefficients of $(\pi^2 - x^2)^2/\pi^4$, $S_n f(x) = 8/15 + (48/\pi^4) \sum_{i < n}
(-1)^i \cos((i + 1)x)/(i + 1)^4$. -/
private theorem quartic_fourierPartialSum {f : ℝ → ℝ} (hsin : ∀ j : ℕ, fourierCoeffSin f j = 0)
    (hcos0 : fourierCoeffCos f 0 = 16 / 15)
    (hcos : ∀ j : ℕ, 0 < j → fourierCoeffCos f j = 48 * (-1 : ℝ) ^ (j + 1) / (π ^ 4 * j ^ 4))
    (n : ℕ) (x : ℝ) :
    fourierPartialSum f n x
      = 8 / 15 + 48 / π ^ 4 * ∑ i ∈ Finset.range n,
          (-1 : ℝ) ^ i * (Real.cos ((i + 1) * x) / (i + 1) ^ 4) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  induction n with
  | zero => simp [fourierPartialSum, hcos0]; norm_num
  | succ n ih =>
      have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
      rw [fourierPartialSum_succ, ih, Finset.sum_range_succ, hcos (n + 1) (by omega),
        hsin (n + 1)]
      set S := ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * (Real.cos (((i : ℝ) + 1) * x) / ((i : ℝ) + 1) ^ 4) with hS
      simp only [zero_mul, add_zero]
      push_cast
      field_simp
      ring

/-- The Fourier series of the periodic extension of $(\pi^2 - x^2)^2/\pi^4$ converges to it at every
real point, by Theorem 4.1.1. -/
private theorem quartic_tendsto {f : ℝ → ℝ} (hper : Function.Periodic f (2 * π))
    (hval : ∀ x ∈ Set.Icc (-π) π, f x = (π ^ 2 - x ^ 2) ^ 2 / π ^ 4) (x : ℝ) :
    Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 (f x)) := by
  have hπ := Real.pi_pos
  have hπ' : π ≠ 0 := Real.pi_ne_zero
  have hfi := intervalIntegrable_of_eqOn (F := fun x : ℝ => (π ^ 2 - x ^ 2) ^ 2 / π ^ 4)
    (by fun_prop) hval
  have hq : Tendsto (fun t : ℝ => t * (2 * π - t) ^ 2 / π ^ 4) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => t * (2 * π - t) ^ 2 / π ^ 4 := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine tendsto_fourierPartialSum_of_Ico hper (fun y hy => ?_) x
  rcases eq_or_lt_of_le hy.1 with hyl | hyl
  · -- `y = -π`: the junction of the periodic extension
    subst hyl
    have hfy : f (-π) = 0 := by rw [hval _ ⟨le_rfl, by linarith⟩]; ring
    have hR : ∀ t ∈ Set.Ioo (0 : ℝ) π,
        (f (-π + t) - 0) / t = t * (2 * π - t) ^ 2 / π ^ 4 := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      rw [hval _ ⟨by linarith [ht.1], by linarith [ht.2]⟩]
      field_simp
      ring
    have hL : ∀ t ∈ Set.Ioo (0 : ℝ) π,
        (f (-π - t) - 0) / t = t * (2 * π - t) ^ 2 / π ^ 4 := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      rw [← hper.sub_int_mul_eq (x := -π - t) (-1),
        hval _ ⟨by push_cast; linarith [ht.2], by push_cast; linarith [ht.1]⟩]
      push_cast
      field_simp
      ring
    have hconv := theorem_4_1_1 hper hfi (tendsto_quotient_of_eventually_eq hR hq)
      (tendsto_quotient_of_eventually_eq hL hq)
    rw [hfy]
    rwa [show ((0 : ℝ) + 0) / 2 = 0 by norm_num] at hconv
  · -- `y ∈ (-π, π)`: the extension agrees with the polynomial near `y`
    have hnb : ∀ᶠ t in 𝓝 y, f t = (π ^ 2 - t ^ 2) ^ 2 / π ^ 4 := by
      filter_upwards [isOpen_Ioo.mem_nhds (⟨hyl, hy.2⟩ : y ∈ Set.Ioo (-π) π)] with t ht
      exact hval t ⟨ht.1.le, ht.2.le⟩
    exact theorem_4_1_1_continuous hper hfi
      ((hasDerivAt_quarticNorm y).congr_of_eventuallyEq hnb)

/-- **Example 4.1.5** of [han2009theoretical]. Let $p(x) = (\pi^2 - x^2)^2/\pi^4$, and let
$f : \mathbb{R} \to \mathbb{R}$ be $2\pi$-periodic with $f(x) = p(x)$ for $x \in [-\pi, \pi]$.
Then

* $p^{(l)}(-\pi) = p^{(l)}(\pi)$ for $l = 0, 1, 2$;
* $b_j = 0$ for all $j$, $a_0 = 16/15$, and $a_j = 48(-1)^{j+1}/(\pi^4 j^4)$ for $j \ge 1$;
* for all $n \ge 0$ and $x \in \mathbb{R}$, $S_n f(x) = \dfrac{8}{15} + \dfrac{48}{\pi^4}
  \sum_{j=1}^{n} \dfrac{(-1)^{j+1} \cos(jx)}{j^4}$;
* $S_n f(x) \to f(x)$ for every $x \in \mathbb{R}$;
* for every $x$, the series $\sum_{j \ge 1} \frac{48}{\pi^4} \frac{(-1)^{j+1} \cos(jx)}{j^4}$
  converges to $f(x) - 8/15$.

The endpoint conditions make the extension twice continuously differentiable. The convergence is
Theorem 4.1.1, and it is the book's statement that this function equals its Fourier series
pointwise. The last part states it with the series convergence of Definition 1.2.17.

The endpoint conditions are stated for the polynomial $p$, which is how the book checks them,
not for the extension $f$. The condition fails for $l = 3$, which matches the book's $k = 4$ for
this example. The sums are written over $i < n$ with $j = i + 1$, so that $(-1)^{j+1}$ is
$(-1)^i$. Note that `AtkinsonHan.Chapter04.equation_4_1_5` is the book's displayed equation
(4.1.5) on the complex Fourier coefficient, and is not about this example. -/
theorem example_4_1_5 {f : ℝ → ℝ} (hper : Function.Periodic f (2 * π))
    (hval : ∀ x ∈ Set.Icc (-π) π, f x = (π ^ 2 - x ^ 2) ^ 2 / π ^ 4) :
    (∀ l ≤ 2, iteratedDeriv l (fun x : ℝ => (π ^ 2 - x ^ 2) ^ 2 / π ^ 4) (-π)
        = iteratedDeriv l (fun x : ℝ => (π ^ 2 - x ^ 2) ^ 2 / π ^ 4) π) ∧
      (∀ j : ℕ, fourierCoeffSin f j = 0) ∧
      fourierCoeffCos f 0 = 16 / 15 ∧
      (∀ j : ℕ, 0 < j → fourierCoeffCos f j = 48 * (-1 : ℝ) ^ (j + 1) / (π ^ 4 * j ^ 4)) ∧
      (∀ (n : ℕ) (x : ℝ), fourierPartialSum f n x
        = 8 / 15 + 48 / π ^ 4 * ∑ i ∈ Finset.range n,
            (-1 : ℝ) ^ i * (Real.cos ((i + 1) * x) / (i + 1) ^ 4)) ∧
      (∀ x : ℝ, Tendsto (fun n : ℕ => fourierPartialSum f n x) atTop (𝓝 (f x))) ∧
      ∀ x : ℝ, Chapter01.definition_1_2_17
        (fun i : ℕ => 48 / π ^ 4 * ((-1 : ℝ) ^ i * (Real.cos ((i + 1) * x) / (i + 1) ^ 4)))
        (f x - 8 / 15) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  obtain ⟨hsin, hcos0, hcos⟩ := quartic_fourierCoeff hval
  have hpartial := quartic_fourierPartialSum hsin hcos0 hcos
  have hconv := quartic_tendsto hper hval
  have hderiv1 : deriv (fun x : ℝ => (π ^ 2 - x ^ 2) ^ 2 / π ^ 4)
      = fun t : ℝ => (4 * t ^ 3 - 4 * π ^ 2 * t) / π ^ 4 :=
    funext fun y => (hasDerivAt_quarticNorm y).deriv
  refine ⟨fun l hl => ?_, hsin, hcos0, hcos, hpartial, hconv, fun x => ?_⟩
  · interval_cases l
    · simp only [iteratedDeriv_zero]
      ring
    · rw [iteratedDeriv_one, hderiv1]
      ring
    · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hderiv1,
        (hasDerivAt_quarticNorm' (-π)).deriv, (hasDerivAt_quarticNorm' π).deriv]
      ring
  · have hclosed : Tendsto (fun n : ℕ => 8 / 15 + 48 / π ^ 4 * ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * (Real.cos ((i + 1) * x) / (i + 1) ^ 4)) atTop (𝓝 (f x)) :=
      (hconv x).congr fun n => hpartial n x
    refine (Chapter01.definition_1_2_17_iff _ _).mpr
      ((hclosed.sub_const (8 / 15)).congr fun n => ?_)
    rw [← Finset.mul_sum]
    ring

/-! ### The truncation error (4.1.14)–(4.1.15) -/

/-- **Equation (4.1.14)** of [han2009theoretical], the $L^2$ truncation error. Let
$f \in L^2(-\pi, \pi)$ with Fourier coefficients $a_j$ and $b_j$, and let $n \ge 0$. Then
$$\int_{-\pi}^{\pi} (f - S_n f)(x)^2\, dx = \pi \sum_{j > n} (a_j^2 + b_j^2).$$

This is the tail of Parseval's equality (4.1.13), and `AtkinsonHan.Chapter04.equation_4_1_13` is
the case $n = -1$. The sum is stated as an unordered sum (`HasSum`) over $j \in \mathbb{N}$
whose terms with $j \le n$ are $0$. Here $S_n f$ is the $L^2$ partial sum `trigPartialSum n f`,
the truncation of the Fourier series to the frequencies $|m| \le n$. By
`AtkinsonHan.Chapter04.equation_4_1_3_const`, `AtkinsonHan.Chapter04.equation_4_1_3_cos` and
`AtkinsonHan.Chapter04.equation_4_1_3_sin`, it is $a_0/2 + \sum_{j=1}^{n} (a_j \cos(jx) + b_j
\sin(jx))$. -/
theorem equation_4_1_14 (n : ℕ)
    (F : Lp ℝ 2 (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))) :
    HasSum (fun j : ℕ =>
        if j ≤ n then 0
        else π * (fourierCoeffCos (fun x : ℝ => (F : AddCircle (2 * π) → ℝ) ↑x) j ^ 2
          + fourierCoeffSin (fun x : ℝ => (F : AddCircle (2 * π) → ℝ) ↑x) j ^ 2))
      (∫ x in -π..π,
        ((F - trigPartialSum n F : Lp ℝ 2
          (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))) : AddCircle (2 * π) → ℝ)
            ↑x ^ 2) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  obtain ⟨G, hG⟩ : ∃ G : AddCircle (2 * π) → ℝ, (F : AddCircle (2 * π) → ℝ) = G := ⟨_, rfl⟩
  -- the tail of Parseval's identity, folded onto `ℕ` and rescaled to the book's normalisation
  have hB := (hasSum_int_fold (hasSum_sq_realFourierCoeff_compl n F)).mul_left (2 * π)
  rw [hG] at hB ⊢
  have hfun : (fun j : ℕ => 2 * π *
        if j = 0 then (if (0 : ℤ).natAbs ≤ n then 0 else realFourierCoeff G 0 ^ 2)
        else (if ((j : ℤ)).natAbs ≤ n then 0 else realFourierCoeff G (j : ℤ) ^ 2)
          + (if (-(j : ℤ)).natAbs ≤ n then 0 else realFourierCoeff G (-(j : ℤ)) ^ 2))
      = fun j : ℕ =>
        if j ≤ n then 0
        else π * (fourierCoeffCos (fun x : ℝ => G ↑x) j ^ 2
          + fourierCoeffSin (fun x : ℝ => G ↑x) j ^ 2) := by
    funext j
    rcases eq_or_ne j 0 with rfl | hj
    · rw [ite_eq_left rfl]
      simp
    · rw [ite_eq_right hj, Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_natCast]
      by_cases hjn : j ≤ n
      · rw [ite_eq_left hjn, ite_eq_left hjn, ite_eq_left hjn, add_zero, mul_zero]
      · rw [ite_eq_right hjn, ite_eq_right hjn, ite_eq_right hjn,
          sq_realFourierCoeff_cos G (Nat.pos_of_ne_zero hj),
          sq_realFourierCoeff_sin G (Nat.pos_of_ne_zero hj)]
        ring
  rw [hfun] at hB
  -- the squared norm of the error, as the book's integral over `(-π, π)`
  have hval : 2 * π * ‖F - trigPartialSum n F‖ ^ 2
      = ∫ x in -π..π, ((F - trigPartialSum n F :
          Lp ℝ 2 (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))) :
            AddCircle (2 * π) → ℝ) ↑x ^ 2 := by
    rw [norm_sq_eq_intervalIntegral]
    field_simp
  rwa [hval] at hB

/-- The $j$-th term of the real Fourier series of $f$ at $x$, with $a_0/2$ as the term $j = 0$, so
that the sum of the terms $j \le m$ is $S_m f(x)$. -/
private noncomputable def fourierTerm (f : ℝ → ℝ) (x : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then fourierCoeffCos f 0 / 2
  else fourierCoeffCos f j * Real.cos (j * x) + fourierCoeffSin f j * Real.sin (j * x)

private theorem sum_range_fourierTerm (f : ℝ → ℝ) (x : ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), fourierTerm f x j = fourierPartialSum f m x := by
  induction m with
  | zero =>
      rw [Finset.sum_range_one, fourierTerm, ite_eq_left rfl, fourierPartialSum]
      simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, fourierPartialSum_succ, fourierTerm,
        ite_eq_right (Nat.succ_ne_zero m)]

private theorem norm_fourierTerm_le (f : ℝ → ℝ) (x : ℝ) (j : ℕ) :
    ‖fourierTerm f x (j + 1)‖ ≤ |fourierCoeffCos f (j + 1)| + |fourierCoeffSin f (j + 1)| := by
  rw [fourierTerm, ite_eq_right (Nat.succ_ne_zero j), Real.norm_eq_abs]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
  · exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  · exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

private theorem summable_fourierTerm {f : ℝ → ℝ}
    (hs : Summable fun j : ℕ => |fourierCoeffCos f j| + |fourierCoeffSin f j|) (x : ℝ) :
    Summable (fourierTerm f x) :=
  (summable_nat_add_iff 1).mp
    (Summable.of_norm_bounded ((summable_nat_add_iff 1).mpr hs) (norm_fourierTerm_le f x))

/-- **Equation (4.1.15)** of [han2009theoretical], the uniform truncation error. Let
$f : \mathbb{R} \to \mathbb{R}$ have Fourier coefficients with
$\sum_j (|a_j| + |b_j|) < \infty$, and assume that $S_m f(y) \to f(y)$ as $m \to \infty$ for
every $y \in \mathbb{R}$. Then for all $n \ge 0$ and $x \in \mathbb{R}$,
$$|f(x) - S_n f(x)| \le \sum_{j > n} (|a_j| + |b_j|).$$
So the maximum of $|f - S_n f|$ over $[-\pi, \pi]$ has the same bound.

**Reading.** The summability hypothesis is the book's "the Fourier series is absolutely
convergent". The convergence hypothesis stands for the book's "$f$ is continuous after a change
on a set of measure zero", under which the book's identity $f(x) - S_n f(x) = \sum_{j > n} (a_j
\cos(jx) + b_j \sin(jx))$ holds.

The summability hypothesis cannot be dropped: without it the right side is the value $0$ that
Mathlib gives a sum that does not converge (`tsum`), and the inequality is false. -/
theorem equation_4_1_15 {f : ℝ → ℝ}
    (hs : Summable fun j : ℕ => |fourierCoeffCos f j| + |fourierCoeffSin f j|)
    (hconv : ∀ y : ℝ, Tendsto (fun m : ℕ => fourierPartialSum f m y) atTop (𝓝 (f y)))
    (n : ℕ) (x : ℝ) :
    |f x - fourierPartialSum f n x|
      ≤ ∑' j : ℕ, (|fourierCoeffCos f (j + (n + 1))| + |fourierCoeffSin f (j + (n + 1))|) := by
  have hsum := summable_fourierTerm hs x
  -- the series sums to `f x`
  have hfx : ∑' j : ℕ, fourierTerm f x j = f x :=
    tendsto_nhds_unique
      ((hsum.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)).congr
        (sum_range_fourierTerm f x))
      (hconv x)
  -- the truncation error is the tail of the series
  have htail : f x - fourierPartialSum f n x = ∑' j : ℕ, fourierTerm f x (j + (n + 1)) := by
    have h := hsum.sum_add_tsum_nat_add (n + 1)
    rw [sum_range_fourierTerm f x n, hfx] at h
    linarith
  have hcsum : Summable fun j : ℕ =>
      |fourierCoeffCos f (j + (n + 1))| + |fourierCoeffSin f (j + (n + 1))| :=
    (summable_nat_add_iff
      (f := fun j : ℕ => |fourierCoeffCos f j| + |fourierCoeffSin f j|) (n + 1)).mpr hs
  have hnormsum : Summable fun j : ℕ => ‖fourierTerm f x (j + (n + 1))‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => norm_fourierTerm_le f x (j + n))
      hcsum
  rw [htail, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hnormsum).trans
    (hnormsum.tsum_le_tsum (fun j => norm_fourierTerm_le f x (j + n)) hcsum)

end AtkinsonHan.Chapter04
