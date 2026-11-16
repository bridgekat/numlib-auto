/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Sums of cosines in arithmetic progression

This file proves Lagrange's trigonometric identity in a telescoped form that needs no division.
After multiplication by $2 \sin(d/2)$, each term of a sum of cosines in arithmetic progression
becomes a difference of two sines, $2 \sin(d/2) \cos x = \sin(x + d/2) - \sin(x - d/2)$, and the sum
telescopes:
$$2 \sin\frac{d}{2} \sum_{k=0}^{M-1} \cos(a + kd) = \sin\Bigl(a + Md - \frac{d}{2}\Bigr) -
  \sin\Bigl(a - \frac{d}{2}\Bigr).$$
Two special progressions are used elsewhere. The multiples $(k + 1)\varphi$ give the closed form of
the Dirichlet kernel and the orthogonality of the discrete cosine and sine transforms. The odd
multiples $(2k + 1)\psi$ give $2 \sin \psi \sum_{k<M} \cos((2k + 1)\psi) = \sin(2M\psi)$.

The file also gives the half-angle forms $2 - 2\cos \theta = 4 \sin^2(\theta/2)$ and
$2 + 2\cos \theta = 4 \cos^2(\theta/2)$, with their double-angle readings. These are the forms in
which the eigenvalues of the tridiagonal Toeplitz matrices $\operatorname{tridiag}(\mp 1, 2, \mp 1)$
are usually written.

## Main results

* `Real.two_mul_sin_half_mul_sum_range_cos_add_mul`: Lagrange's identity for the progression
  $a + kd$, displayed above.
* `Real.two_mul_sin_half_mul_sum_range_cos`: $2 \sin(\varphi/2) \sum_{k<M} \cos((k + 1)\varphi) =
  \sin((2M + 1)\varphi/2) - \sin(\varphi/2)$.
* `Real.two_mul_sin_mul_sum_range_cos_odd`: $2 \sin \psi \sum_{k<M} \cos((2k + 1)\psi) =
  \sin(2M\psi)$.
* `Real.two_sub_two_mul_cos`, `Real.two_add_two_mul_cos`: $2 \mp 2\cos \theta$ equals
  $4\sin^2(\theta/2)$ and $4\cos^2(\theta/2)$.
-/

open Finset

namespace Real

/-- **Lagrange's trigonometric identity** for an arithmetic progression, in telescoped form: for all
$a, d \in \mathbb{R}$ and every natural number $M$,
$$2 \sin\frac{d}{2} \sum_{k=0}^{M-1} \cos(a + kd) = \sin\Bigl(a + Md - \frac{d}{2}\Bigr) -
  \sin\Bigl(a - \frac{d}{2}\Bigr).$$
-/
theorem two_mul_sin_half_mul_sum_range_cos_add_mul (a d : ℝ) (M : ℕ) :
    2 * sin (d / 2) * ∑ k ∈ range M, cos (a + k * d) =
      sin (a + M * d - d / 2) - sin (a - d / 2) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, mul_add, ih]
    have h1 : a + ((M + 1 : ℕ) : ℝ) * d - d / 2 = (a + M * d) + d / 2 := by push_cast; ring
    have h2 : a + (M : ℝ) * d - d / 2 = (a + M * d) - d / 2 := by ring
    rw [h1, h2, sin_add, sin_sub]
    ring

/-- **Lagrange's trigonometric identity** for the multiples of $\varphi$, in telescoped form: for
every $\varphi \in \mathbb{R}$ and every natural number $M$,
$$2 \sin\frac{\varphi}{2} \sum_{k=0}^{M-1} \cos((k + 1)\varphi) = \sin\frac{(2M +
  1)\varphi}{2} - \sin\frac{\varphi}{2}.$$
-/
theorem two_mul_sin_half_mul_sum_range_cos (φ : ℝ) (M : ℕ) :
    2 * sin (φ / 2) * ∑ k ∈ range M, cos ((k + 1) * φ) =
      sin ((2 * M + 1) * (φ / 2)) - sin (φ / 2) := by
  have hs : ∑ k ∈ range M, cos ((k + 1) * φ) = ∑ k ∈ range M, cos (φ + k * φ) :=
    sum_congr rfl fun k _ => by congr 1; ring
  rw [hs, two_mul_sin_half_mul_sum_range_cos_add_mul,
    show φ + M * φ - φ / 2 = (2 * M + 1) * (φ / 2) by ring, show φ - φ / 2 = φ / 2 by ring]

/-- The **sum of cosines of the odd multiples** of $\psi$, in telescoped form: for every
$\psi \in \mathbb{R}$ and every natural number $M$,
$$2 \sin \psi \sum_{k=0}^{M-1} \cos((2k + 1)\psi) = \sin(2M\psi).$$
-/
theorem two_mul_sin_mul_sum_range_cos_odd (ψ : ℝ) (M : ℕ) :
    2 * sin ψ * ∑ k ∈ range M, cos ((2 * k + 1) * ψ) = sin (2 * M * ψ) := by
  have hs : ∑ k ∈ range M, cos ((2 * k + 1) * ψ) = ∑ k ∈ range M, cos (ψ + k * (2 * ψ)) :=
    sum_congr rfl fun k _ => by congr 1; ring
  have h := two_mul_sin_half_mul_sum_range_cos_add_mul ψ (2 * ψ) M
  rw [show 2 * ψ / 2 = ψ by ring, sub_self, sin_zero, sub_zero,
    show ψ + M * (2 * ψ) - ψ = 2 * M * ψ by ring] at h
  rw [hs, h]

/-- For every $\theta \in \mathbb{R}$, $2 - 2\cos \theta = 4 \sin^2(\theta/2)$. This is the
half-angle form in which the eigenvalues $2 - 2\cos \theta_k$ of
$\operatorname{tridiag}(-1, 2, -1)$ are usually written. -/
theorem two_sub_two_mul_cos (θ : ℝ) : 2 - 2 * cos θ = 4 * sin (θ / 2) ^ 2 := by
  have h2 : cos θ = cos (2 * (θ / 2)) := by ring_nf
  rw [h2, cos_two_mul]
  linear_combination (-4) * cos_sq_add_sin_sq (θ / 2)

/-- For every $x \in \mathbb{R}$, $2 - 2\cos(2x) = 4 \sin^2 x$. This is the double-angle reading of
`Real.two_sub_two_mul_cos`. -/
theorem two_sub_two_mul_cos_two_mul (x : ℝ) :
    2 - 2 * cos (2 * x) = 4 * sin x ^ 2 := by
  rw [Real.two_sub_two_mul_cos, mul_div_cancel_left₀ x two_ne_zero]

/-- For every $\theta \in \mathbb{R}$, $2 + 2\cos \theta = 4 \cos^2(\theta/2)$. This is the
half-angle form of the eigenvalues $2 + 2\cos \theta_k$ of $\operatorname{tridiag}(1, 2, 1)$,
the companion of `Real.two_sub_two_mul_cos`. -/
theorem two_add_two_mul_cos (θ : ℝ) : 2 + 2 * cos θ = 4 * cos (θ / 2) ^ 2 := by
  have h := cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  linarith

/-- For every $x \in \mathbb{R}$, $2 + 2\cos(2x) = 4 \cos^2 x$. This is the double-angle reading of
`Real.two_add_two_mul_cos`. -/
theorem two_add_two_mul_cos_two_mul (x : ℝ) :
    2 + 2 * cos (2 * x) = 4 * cos x ^ 2 := by
  rw [Real.two_add_two_mul_cos, mul_div_cancel_left₀ x two_ne_zero]

end Real
