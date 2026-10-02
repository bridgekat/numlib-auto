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

Lagrange's trigonometric identity, in the telescoped form that needs no division: multiplying a sum
of cosines in arithmetic progression by `2 sin (d / 2)` turns each term into a difference of two
sines, `2 sin (d / 2) cos x = sin (x + d / 2) - sin (x - d / 2)`, and the sum telescopes
(`Real.two_mul_sin_half_mul_sum_range_cos_add_mul`).

The two special progressions in use are the multiples `(k + 1) φ`, which give the closed form of
the Dirichlet kernel and the orthogonality of the discrete cosine and sine transforms
(`Real.two_mul_sin_half_mul_sum_range_cos`), and the odd multiples `(2 k + 1) ψ`
(`Real.two_mul_sin_mul_sum_range_cos_odd`).

The half-angle forms `2 ∓ 2 cos θ = 4 sin² (θ / 2)`, `4 cos² (θ / 2)` (`Real.two_sub_two_mul_cos`,
`Real.two_add_two_mul_cos`, and their double-angle readings) are the shapes in which the
eigenvalues of the tridiagonal Toeplitz matrices `tridiag(∓1, 2, ∓1)` are usually written.
-/

open Finset

namespace Real

/-- **Lagrange's trigonometric identity** for an arithmetic progression, telescoped:
`2 sin (d / 2) ∑_{k<M} cos (a + k d) = sin (a + M d - d / 2) - sin (a - d / 2)`. -/
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

/-- **Lagrange's trigonometric identity**, telescoped:
`2 sin (φ / 2) ∑_{k<M} cos ((k + 1) φ) = sin ((2 M + 1) φ / 2) - sin (φ / 2)`. -/
theorem two_mul_sin_half_mul_sum_range_cos (φ : ℝ) (M : ℕ) :
    2 * sin (φ / 2) * ∑ k ∈ range M, cos ((k + 1) * φ) =
      sin ((2 * M + 1) * (φ / 2)) - sin (φ / 2) := by
  have hs : ∑ k ∈ range M, cos ((k + 1) * φ) = ∑ k ∈ range M, cos (φ + k * φ) :=
    sum_congr rfl fun k _ => by congr 1; ring
  rw [hs, two_mul_sin_half_mul_sum_range_cos_add_mul,
    show φ + M * φ - φ / 2 = (2 * M + 1) * (φ / 2) by ring, show φ - φ / 2 = φ / 2 by ring]

/-- **The sum of the odd multiples**, telescoped:
`2 sin ψ ∑_{k<M} cos ((2 k + 1) ψ) = sin (2 M ψ)`. -/
theorem two_mul_sin_mul_sum_range_cos_odd (ψ : ℝ) (M : ℕ) :
    2 * sin ψ * ∑ k ∈ range M, cos ((2 * k + 1) * ψ) = sin (2 * M * ψ) := by
  have hs : ∑ k ∈ range M, cos ((2 * k + 1) * ψ) = ∑ k ∈ range M, cos (ψ + k * (2 * ψ)) :=
    sum_congr rfl fun k _ => by congr 1; ring
  have h := two_mul_sin_half_mul_sum_range_cos_add_mul ψ (2 * ψ) M
  rw [show 2 * ψ / 2 = ψ by ring, sub_self, sin_zero, sub_zero,
    show ψ + M * (2 * ψ) - ψ = 2 * M * ψ by ring] at h
  rw [hs, h]

/-- `2 − 2 cos θ = 4 sin² (θ / 2)`: the half-angle form in which the eigenvalues
`2 − 2 cos θ_k` of `tridiag(-1, 2, -1)` are usually written. -/
theorem two_sub_two_mul_cos (θ : ℝ) : 2 - 2 * cos θ = 4 * sin (θ / 2) ^ 2 := by
  have h2 : cos θ = cos (2 * (θ / 2)) := by ring_nf
  rw [h2, cos_two_mul]
  linear_combination (-4) * cos_sq_add_sin_sq (θ / 2)

/-- `2 − 2 cos (2 x) = 4 sin² x`, the double-angle reading of `Real.two_sub_two_mul_cos`. -/
theorem two_sub_two_mul_cos_two_mul (x : ℝ) :
    2 - 2 * cos (2 * x) = 4 * sin x ^ 2 := by
  rw [Real.two_sub_two_mul_cos, mul_div_cancel_left₀ x two_ne_zero]

/-- `2 + 2 cos θ = 4 cos² (θ / 2)`: the half-angle form of the eigenvalues `2 + 2 cos θ_k` of
`tridiag(1, 2, 1)`, the companion of `Real.two_sub_two_mul_cos`. -/
theorem two_add_two_mul_cos (θ : ℝ) : 2 + 2 * cos θ = 4 * cos (θ / 2) ^ 2 := by
  have h := cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  linarith

/-- `2 + 2 cos (2 x) = 4 cos² x`, the double-angle reading of `Real.two_add_two_mul_cos`. -/
theorem two_add_two_mul_cos_two_mul (x : ℝ) :
    2 + 2 * cos (2 * x) = 4 * cos x ^ 2 := by
  rw [Real.two_add_two_mul_cos, mul_div_cancel_left₀ x two_ne_zero]

end Real
