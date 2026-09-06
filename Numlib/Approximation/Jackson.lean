import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Numlib.Analysis.Fourier.TrigonometricBasis

/-!
# Jackson's theorem through the Fejér–Korovkin kernel

**Jackson's theorem** bounds the error of the best uniform approximation of a smooth `2 π`-periodic
function by trigonometric polynomials of degree at most `n`. This file builds the kernel that the
sharp form of the theorem rests on and proves the theorem for a Hölder continuous function:

`dist (g, 𝕋ₙ) ≤ M (π sin (π / (2 n + 4)))^α ≤ M (π² / 2)^α / n^α` when `|g u - g v| ≤ M |u - v|^α`.

The kernel is `K_n(r) = |∑_{k ≤ n} c_k e^{i k r}|²` with `c_k = √(2/(n+2)) sin ((k+1) π/(n+2))`. It
is nonnegative and has total mass `2 π` over a period, and its first cosine coefficient is
`cos (π / (n + 2))` — the largest such a kernel of degree `n` can have. That is what makes its
second moment as small as `2 π (π sin (π / (2 n + 4)))²`, hence its first absolute moment at most
`2 π · π sin (π / (2 n + 4))`, and that moment is exactly the error constant. The Fejér kernel and
its powers give a worse constant, which is why the extremal kernel is the one built here.

## Main definitions

* `Jackson.angle n` is `θ = π / (n + 2)`, and `Jackson.coeff n k` is `c_k`.
* `Jackson.kernel n` is `K_n`, written as the sum of the squares of the real and imaginary parts of
  `∑_k c_k e^{i k r}` so that `Jackson.kernel_nonneg` is immediate;
  `Jackson.kernel_eq_sum` expands it as `∑_{k, l} c_k c_l cos ((k - l) r)`, the form the moments
  and the degree are read off from.
* `Jackson.approx n g` is the convolution `x ↦ (2 π)⁻¹ ∫_{-π}^{π} K_n(r) g (x - r) dr`
  (`Jackson.approx_coe`), written out in the real trigonometric system so that
  `Jackson.approx_mem` — that it is a trigonometric polynomial of degree at most `n` — needs no
  argument.
* `Jackson.cosCM m`, `Jackson.sinCM m` are `x ↦ cos (m x)` and `x ↦ sin (m x)` as continuous
  functions on the circle of circumference `2 π`, again built from the trigonometric system.

## Main results

* `Jackson.integral_kernel` and `Jackson.integral_cos_mul_kernel`: the mass `2 π` and the first
  cosine coefficient `cos θ` of the kernel. Both come from the two sums `Jackson.sum_coeff_sq` and
  `Jackson.sum_coeff_mul_coeff_succ`, which are in turn the telescoping identities
  `Jackson.sum_cos_odd_angle` and `Jackson.sum_cos_even_angle` at `θ = π / (n + 2)`.
* `Jackson.integral_sq_mul_kernel_le` and `Jackson.integral_abs_mul_kernel_le`: the second and the
  first moments. The first follows from the second by `|r| ≤ r²/(2 s) + s/2`, which is the
  Cauchy–Schwarz step done by hand.
* `Jackson.abs_sub_approx_le_of_holder` and `Jackson.infDist_le_of_holder`: Jackson's theorem for
  a Hölder function, pointwise and as a bound on the distance to `trigPolyLE (2 π) n`. This is the
  case `k = 0`.
* `Jackson.hasDerivAt_approx`: **the operator commutes with differentiation**, by integration by
  parts on each Fourier coefficient of the kernel. It is what lets the `k = 0` estimate be iterated
  through the remainder `Jackson.rem n g = g - approx n g`, whose iterates are estimated by
  `Jackson.abs_iterate_rem_le`: each application removes a trigonometric polynomial of degree at
  most `n` (`Jackson.sub_iterate_rem_mem`) and costs one factor of the first moment.
* `Jackson.infDist_le_of_holder_deriv'` is **Jackson's theorem** in the classical form
  `ρₙ(g) ≤ (1 + π²/2)^{k+1} M / n^{k+α}` for a `2 π`-periodic `g` with `k` continuous derivatives
  whose `k`-th derivative is `α`-Hölder with constant `M`;
  `Jackson.infDist_le_of_holder_deriv` is the same bound before the constant is coarsened, and
  `Jackson.moment_pow_le` is that coarsening.

The derivatives are supplied as a tower `D 0 = g`, `D (j + 1) = (D j)'` rather than as
`iteratedDeriv`, so that a caller which already has the derivatives — or which produces them from
`ContDiff` — can use whichever form it holds.

Reference: [han2009theoretical], Theorem 3.7.1, which states this with the constant
`(1 + π²/2)^{k+1}` and refers to [meinardus1967approximation] for the proof.
-/

open Finset MeasureTheory Real

open scoped Real

namespace Jackson

/-! ### The angle `θ = π / (n + 2)` -/

/-- The angle `θₙ = π / (n + 2)` at which the Fejér–Korovkin kernel of degree `n` is built. -/
noncomputable def angle (n : ℕ) : ℝ := π / (n + 2)

theorem angle_pos (n : ℕ) : 0 < angle n := by
  rw [angle]
  positivity

theorem angle_lt_pi (n : ℕ) : angle n < π := by
  rw [angle, div_lt_iff₀ (by positivity)]
  nlinarith [pi_pos, Nat.cast_nonneg (α := ℝ) n]

theorem sin_angle_pos (n : ℕ) : 0 < Real.sin (angle n) :=
  Real.sin_pos_of_pos_of_lt_pi (angle_pos n) (angle_lt_pi n)

/-- `(n + 2) θₙ = π`, the defining property of the angle. -/
theorem cast_mul_angle (n : ℕ) : ((n : ℝ) + 2) * angle n = π := by
  rw [angle]
  field_simp

/-! ### Two trigonometric sums at that angle -/

/-- `∑_{j = 0}^{n} cos ((2 j + 1) θ) = -cos θ` at `θ = π / (n + 2)`: the sum telescopes against
`2 sin θ` to `sin ((2 n + 2) θ) = sin (2 π - 2 θ) = -sin (2 θ)`. -/
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

/-- `∑_{j = 1}^{n + 1} cos (2 j θ) = -1` at `θ = π / (n + 2)`: the sum telescopes against
`2 sin θ` to `sin ((2 n + 3) θ) - sin θ = -2 sin θ`. -/
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

/-- `∑_{k = 0}^{n} sin² ((k + 1) θ) = (n + 2) / 2` at `θ = π / (n + 2)`. -/
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

/-- `∑_{k = 0}^{n - 1} sin ((k + 1) θ) sin ((k + 2) θ) = (n + 2) cos θ / 2` at
`θ = π / (n + 2)`. -/
theorem sum_sin_mul_sin_angle (n : ℕ) :
    ∑ k ∈ range n, Real.sin (((k : ℝ) + 1) * angle n) * Real.sin (((k : ℝ) + 2) * angle n)
      = ((n : ℝ) + 2) * Real.cos (angle n) / 2 := by
  set θ := angle n with hθ
  have hprod : ∀ k : ℕ, Real.sin (((k : ℝ) + 1) * θ) * Real.sin (((k : ℝ) + 2) * θ)
      = (Real.cos θ - Real.cos ((2 * ((k : ℝ) + 1) + 1) * θ)) / 2 := by
    intro k
    have h1 : ((k : ℝ) + 1) * θ = ((2 * ((k : ℝ) + 1) + 1) * θ - θ) / 2 +
        ((2 * ((k : ℝ) + 1) + 1) * θ + θ) / 2 - ((k : ℝ) + 2) * θ := by ring
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

/-- The `k`-th coefficient `c_k = √(2 / (n + 2)) sin ((k + 1) π / (n + 2))` of the Fejér–Korovkin
kernel of degree `n`. The normalization makes `∑_{k ≤ n} c_k² = 1`, and the point of the choice is
that `∑_{k < n} c_k c_{k+1} = cos (π / (n + 2))`, which is as close to `1` as a nonnegative
trigonometric polynomial of degree `n` allows. -/
noncomputable def coeff (n k : ℕ) : ℝ :=
  Real.sqrt (2 / ((n : ℝ) + 2)) * Real.sin (((k : ℝ) + 1) * angle n)

private theorem sq_sqrt_two_div (n : ℕ) :
    Real.sqrt (2 / ((n : ℝ) + 2)) ^ 2 = 2 / ((n : ℝ) + 2) :=
  Real.sq_sqrt (by positivity)

/-- The coefficients are normalized: `∑_{k ≤ n} c_k² = 1`. -/
theorem sum_coeff_sq (n : ℕ) : ∑ k ∈ range (n + 1), coeff n k ^ 2 = 1 := by
  have hn : ((n : ℝ) + 2) ≠ 0 := by positivity
  simp only [coeff, mul_pow, sq_sqrt_two_div]
  rw [← Finset.mul_sum, sum_sin_sq_angle n]
  field_simp

/-- The consecutive products sum to `cos θ`: `∑_{k < n} c_k c_{k+1} = cos (π / (n + 2))`. -/
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

/-- The **Fejér–Korovkin kernel** `K_n(r) = |∑_{k ≤ n} c_k e^{i k r}|²`, written as the sum of the
squares of its real and imaginary parts so that its nonnegativity is visible. It is a nonnegative
trigonometric polynomial of degree at most `n` with `(2π)⁻¹ ∫ K_n = 1` whose first cosine
coefficient `cos (π / (n + 2))` is the largest such a kernel can have; that is what makes its
second moment small. -/
noncomputable def kernel (n : ℕ) (r : ℝ) : ℝ :=
  (∑ k ∈ range (n + 1), coeff n k * Real.cos ((k : ℝ) * r)) ^ 2
    + (∑ k ∈ range (n + 1), coeff n k * Real.sin ((k : ℝ) * r)) ^ 2

theorem kernel_nonneg (n : ℕ) (r : ℝ) : 0 ≤ kernel n r := by
  rw [kernel]
  positivity

theorem continuous_kernel (n : ℕ) : Continuous (kernel n) := by
  have h : kernel n = fun r : ℝ =>
      (∑ k ∈ range (n + 1), coeff n k * Real.cos ((k : ℝ) * r)) ^ 2
        + (∑ k ∈ range (n + 1), coeff n k * Real.sin ((k : ℝ) * r)) ^ 2 := rfl
  rw [h]
  exact ((continuous_finsetSum _ fun k _ => continuous_const.mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).pow 2).add
    ((continuous_finsetSum _ fun k _ => continuous_const.mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).pow 2)

/-- The kernel expanded as a double sum of cosines: `K_n(r) = ∑_{k, l ≤ n} c_k c_l cos ((k - l) r)`.
This is the form the moments are read off from, and the form that shows `K_n` is a trigonometric
polynomial of degree at most `n`. -/
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

private theorem integral_cos_intCast (m : ℤ) :
    (∫ r in -π..π, Real.cos ((m : ℝ) * r)) = if m = 0 then 2 * π else 0 := by
  by_cases hm : m = 0
  · rw [ite_eq_left hm, hm]
    simp only [Int.cast_zero, zero_mul, Real.cos_zero, intervalIntegral.integral_const,
      smul_eq_mul, mul_one]
    ring
  · have hm' : (m : ℝ) ≠ 0 := Int.cast_ne_zero.2 hm
    rw [ite_eq_right hm, intervalIntegral.integral_comp_mul_left Real.cos hm',
      integral_cos, smul_eq_mul]
    have h1 : Real.sin ((m : ℝ) * π) = 0 := Real.sin_int_mul_pi m
    have h2 : Real.sin ((m : ℝ) * -π) = 0 := by
      rw [show (m : ℝ) * -π = -((m : ℝ) * π) by ring, Real.sin_neg, h1, neg_zero]
    rw [h1, h2]
    ring

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
    integral_cos_intCast (m + 1), integral_cos_intCast (m - 1)]
  split_ifs <;> ring

/-- The inner sum `∑_{l ≤ n} c_k c_l [l = k + 1]` collapses, and summing over `k` gives
`∑_{k < n} c_k c_{k+1} = cos θ`. -/
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

/-- `(2π)⁻¹ ∫ K_n = 1`: the kernel is a probability density on a period. -/
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
      rw [intervalIntegral.integral_const_mul, ← hcast k l, integral_cos_intCast]
    rw [Finset.sum_congr rfl fun l _ => hterm l,
      Finset.sum_eq_single k (fun l _ hlk => by
        rw [ite_eq_right (by omega : (k : ℤ) - (l : ℤ) ≠ 0), mul_zero])
        fun h => absurd hk h]
    rw [ite_eq_left (by omega : (k : ℤ) - (k : ℤ) = 0)]
    ring
  rw [Finset.sum_congr rfl hk, ← Finset.sum_mul, sum_coeff_sq n, one_mul]

/-- `(2π)⁻¹ ∫ K_n(r) cos r dr = cos θ`: the first cosine coefficient of the kernel. -/
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

/-- **Jordan's inequality in the form the second moment needs**: `r² ≤ π² (1 - cos r) / 2` on a
period, because `|sin (r/2)| ≥ |r| / π` there. -/
private theorem sq_le_one_sub_cos {r : ℝ} (hr : |r| ≤ π) :
    r ^ 2 ≤ π ^ 2 * ((1 - Real.cos r) / 2) := by
  have hpi := Real.pi_pos
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

/-- The second moment of the Fejér–Korovkin kernel: `∫ r² K_n ≤ 2 π · π² (1 - cos θ) / 2`. Since
`π² (1 - cos θ) / 2 = (π sin (θ/2))²`, this says that the root mean square of `r` against the
kernel is at most `π sin (θ / 2)`. -/
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

/-- The half-angle `θ / 2 = π / (2 (n + 2))` has positive sine. -/
theorem sin_half_angle_pos (n : ℕ) : 0 < Real.sin (angle n / 2) := by
  have h1 := angle_pos n
  have h2 := angle_lt_pi n
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

/-- **The first absolute moment of the Fejér–Korovkin kernel**:
`(2 π)⁻¹ ∫ |r| K_n(r) dr ≤ π sin (θ / 2)`.

The kernel has total mass `2 π` and second moment at most `2 π s²` with `s = π sin (θ / 2)`, and
`|r| ≤ r² / (2 s) + s / 2` pointwise, so the first moment is at most `2 π (s/2 + s/2) = 2 π s`. -/
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

/-- `π sin (θ / 2) ≤ π² / (2 (n + 2))`, the bound behind the constant `1 + π² / 2` of Jackson's
theorem. -/
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

/-! ### Trigonometric monomials on the circle of circumference `2 π` -/

/-- `x ↦ cos (m x)` as a continuous function on the circle of circumference `2 π`, built from the
real trigonometric system so that its membership in `trigPolyLE (2 π) n` is immediate. -/
noncomputable def cosCM (m : ℤ) : C(AddCircle (2 * π), ℝ) :=
  if m = 0 then 1 else (√2 : ℝ)⁻¹ • trigFun (2 * π) |m|

/-- `x ↦ sin (m x)` as a continuous function on the circle of circumference `2 π`. -/
noncomputable def sinCM (m : ℤ) : C(AddCircle (2 * π), ℝ) :=
  if 0 < m then (√2 : ℝ)⁻¹ • trigFun (2 * π) (-m)
  else if m < 0 then -((√2 : ℝ)⁻¹ • trigFun (2 * π) m) else 0

@[simp]
theorem cosCM_coe (m : ℤ) (x : ℝ) :
    cosCM m ((x : ℝ) : AddCircle (2 * π)) = Real.cos ((m : ℝ) * x) := by
  have h2 : (√2 : ℝ) ≠ 0 := by positivity
  have h2' : (√2 : ℝ) * (√2 : ℝ) = 2 := Real.mul_self_sqrt (by norm_num)
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

theorem cosCM_mem {m : ℤ} {n : ℕ} (hm : m.natAbs ≤ n) : cosCM m ∈ trigPolyLE (2 * π) n := by
  rw [cosCM]
  split_ifs with h
  · rw [show (1 : C(AddCircle (2 * π), ℝ)) = trigFun (2 * π) 0 from trigFun_zero.symm]
    exact trigFun_mem_trigPolyLE (by simp)
  · exact Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE (by rwa [Int.natAbs_abs]))

theorem sinCM_mem {m : ℤ} {n : ℕ} (hm : m.natAbs ≤ n) : sinCM m ∈ trigPolyLE (2 * π) n := by
  rw [sinCM]
  split_ifs with h1 h2
  · exact Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE (by rwa [Int.natAbs_neg]))
  · exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE hm))
  · exact Submodule.zero_mem _

/-! ### The Fejér–Korovkin operator -/

/-- Translating the argument of a `2 π`-periodic function does not change its integral over a
period, and reflecting it does not either. -/
private theorem integral_comp_sub_of_periodic {φ : ℝ → ℝ} (hp : Function.Periodic φ (2 * π))
    (x : ℝ) : (∫ r in -π..π, φ (x - r)) = ∫ y in -π..π, φ y := by
  rw [intervalIntegral.integral_comp_sub_left φ x, show x - -π = x + π from by ring]
  have h := hp.intervalIntegral_add_eq (x - π) (-π)
  rw [show x - π + 2 * π = x + π by ring, show -π + 2 * π = π by ring] at h
  exact h

/-- Against a `2 π`-periodic `g`, the integral of `cos (m r) g (x - r)` over a period splits into
the `m`-th cosine and sine coefficients of `g` times `cos (m x)` and `sin (m x)`. -/
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

/-- The **Fejér–Korovkin approximation** of a `2 π`-periodic `g`: the trigonometric polynomial of
degree at most `n` whose value at `x` is the convolution
`(2 π)⁻¹ ∫_{-π}^{π} K_n(r) g(x - r) dr` (`Jackson.approx_coe`). It is written out in the real
trigonometric system, so that membership in `trigPolyLE (2 π) n` is immediate. -/
noncomputable def approx (n : ℕ) (g : ℝ → ℝ) : C(AddCircle (2 * π), ℝ) :=
  (2 * π)⁻¹ • ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1),
    (coeff n k * coeff n l) •
      ((∫ y in -π..π, Real.cos ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * y) * g y) •
          cosCM ((k : ℤ) - (l : ℤ))
        + (∫ y in -π..π, Real.sin ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * y) * g y) •
            sinCM ((k : ℤ) - (l : ℤ)))

/-- The Fejér–Korovkin approximation is a trigonometric polynomial of degree at most `n`. -/
theorem approx_mem (n : ℕ) (g : ℝ → ℝ) : approx n g ∈ trigPolyLE (2 * π) n := by
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k hk => Submodule.sum_mem _ fun l hl => ?_)
  have hkn := Finset.mem_range.1 hk
  have hln := Finset.mem_range.1 hl
  have hm : ((k : ℤ) - (l : ℤ)).natAbs ≤ n := by omega
  exact Submodule.smul_mem _ _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (cosCM_mem hm)) (Submodule.smul_mem _ _ (sinCM_mem hm)))

/-- **The Fejér–Korovkin approximation is the convolution of `g` with the kernel.** -/
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

/-- The **modulus of the Fejér–Korovkin error** is bounded by the kernel average of the increments
of `g`. -/
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

/-- The tangent line to the concave power `u ↦ u ^ α` at `u = s`: `u^α ≤ α s^{α-1} u +
(1 - α) s^α`. It is the weighted arithmetic–geometric mean inequality, and it is what replaces
Jensen's inequality in the Hölder estimate below. -/
private theorem rpow_le_tangent {u s α : ℝ} (hu : 0 ≤ u) (hs : 0 < s) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) : u ^ α ≤ α * s ^ (α - 1) * u + (1 - α) * s ^ α := by
  have h := Real.geom_mean_le_arith_mean2_weighted hα0 (by linarith : (0 : ℝ) ≤ 1 - α)
    (div_nonneg hu hs.le) zero_le_one (by ring)
  rw [Real.one_rpow, mul_one, mul_one, Real.div_rpow hu hs.le] at h
  have hsα : (0 : ℝ) < s ^ α := Real.rpow_pos_of_pos hs α
  have hmul := mul_le_mul_of_nonneg_right h hsα.le
  rw [div_mul_cancel₀ _ hsα.ne'] at hmul
  refine hmul.trans_eq ?_
  rw [Real.rpow_sub hs, Real.rpow_one]
  field_simp

/-- **The Fejér–Korovkin error for a Hölder function.** If `|g u - g v| ≤ M |u - v|^α` for some
`0 < α ≤ 1`, then the trigonometric polynomial `approx n g` of degree at most `n` approximates `g`
to within `M (π sin (π / (2 n + 4)))^α` uniformly. -/
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
    exact rpow_le_tangent (abs_nonneg r) hs hα0 hα1
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
    have : (0 : ℝ) < s ^ (α - 1) := Real.rpow_pos_of_pos hs _
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

/-- The real function underlying a continuous function on the circle of circumference `2 π`. -/
noncomputable abbrev lift (G : C(AddCircle (2 * π), ℝ)) : ℝ → ℝ := fun x => G ↑x

theorem continuous_lift (G : C(AddCircle (2 * π), ℝ)) : Continuous (lift G) :=
  G.continuous.comp (AddCircle.continuous_mk' (2 * π))

theorem periodic_lift (G : C(AddCircle (2 * π), ℝ)) :
    Function.Periodic (lift G) (2 * π) := fun t => by
  simp only [lift]
  rw [AddCircle.coe_add_period]

/-- **Jackson's theorem for a Hölder function**, the case `k = 0`: a continuous `2 π`-periodic
function whose increments satisfy `|g u - g v| ≤ M |u - v|^α` is approximated by trigonometric
polynomials of degree at most `n` to within `M (π sin (π / (2 n + 4)))^α`.

Since `π sin (π / (2 n + 4)) ≤ π² / (2 (n + 2))`, this is at most `M (π²/2)^α / n^α`, which is the
form the constant `1 + π²/2` of the classical statement comes from. -/
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

/-- The Fejér–Korovkin approximation written out as a trigonometric sum. -/
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

/-- Termwise differentiation of a trigonometric sum of the shape `approx` produces. -/
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

/-- **Integration by parts against the cosines.** For a `2 π`-periodic `g` the boundary terms
cancel, so `∫ cos (m y) g'(y) dy = m ∫ sin (m y) g(y) dy`. -/
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

/-- **Integration by parts against the sines.** For a `2 π`-periodic `g`,
`∫ sin (m y) g'(y) dy = -m ∫ cos (m y) g(y) dy`. -/
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

/-- **The Fejér–Korovkin operator commutes with differentiation.** -/
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

/-! ### The remainder operator and the `C^{k,α}` case -/

/-- The **Fejér–Korovkin remainder** `R_n g = g - L_n g`. Its iterates are what Jackson's theorem
for a `k` times differentiable function is estimated through: each application removes a
trigonometric polynomial of degree at most `n`, and each commutes with differentiation. -/
noncomputable def rem (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => g x - approx n g ((x : ℝ) : AddCircle (2 * π))

theorem continuous_rem (n : ℕ) {g : ℝ → ℝ} (hc : Continuous g) : Continuous (rem n g) :=
  hc.sub ((approx n g).continuous.comp (AddCircle.continuous_mk' (2 * π)))

theorem periodic_rem (n : ℕ) {g : ℝ → ℝ} (hp : Function.Periodic g (2 * π)) :
    Function.Periodic (rem n g) (2 * π) := by
  intro x
  simp only [rem]
  rw [hp x, AddCircle.coe_add_period]

/-- The remainder commutes with differentiation, because the operator does. -/
theorem hasDerivAt_rem {g g' : ℝ → ℝ} (hd : ∀ x, HasDerivAt g (g' x) x) (hc' : Continuous g')
    (hp : Function.Periodic g (2 * π)) (n : ℕ) (x : ℝ) :
    HasDerivAt (rem n g) (rem n g' x) x :=
  (hd x).sub (hasDerivAt_approx hd hc' hp n x)

/-- The derivative of a periodic function is periodic. -/
theorem periodic_deriv {f f' : ℝ → ℝ} {T : ℝ} (hp : Function.Periodic f T)
    (hd : ∀ x, HasDerivAt f (f' x) x) : Function.Periodic f' T := by
  intro x
  have h2 : HasDerivAt (fun y : ℝ => f (y + T)) (f' (x + T)) x :=
    HasDerivAt.comp_add_const x T (hd (x + T))
  rw [funext fun y => hp y] at h2
  exact h2.unique (hd x)

theorem continuous_iterate_rem (n : ℕ) : ∀ (j : ℕ) {g : ℝ → ℝ}, Continuous g →
    Continuous ((rem n)^[j] g)
  | 0, _, hc => hc
  | j + 1, g, hc => by
    rw [Function.iterate_succ_apply]
    exact continuous_iterate_rem n j (continuous_rem n hc)

theorem periodic_iterate_rem (n : ℕ) : ∀ (j : ℕ) {g : ℝ → ℝ}, Function.Periodic g (2 * π) →
    Function.Periodic ((rem n)^[j] g) (2 * π)
  | 0, _, hp => hp
  | j + 1, g, hp => by
    rw [Function.iterate_succ_apply]
    exact periodic_iterate_rem n j (periodic_rem n hp)

theorem hasDerivAt_iterate_rem (n : ℕ) : ∀ (j : ℕ) {g g' : ℝ → ℝ}, Continuous g →
    Continuous g' → Function.Periodic g (2 * π) → (∀ x, HasDerivAt g (g' x) x) →
    ∀ x, HasDerivAt ((rem n)^[j] g) ((rem n)^[j] g' x) x
  | 0, _, _, _, _, _, hd, x => hd x
  | j + 1, g, g', hc, hc', hp, hd, x => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact hasDerivAt_iterate_rem n j (continuous_rem n hc) (continuous_rem n hc')
      (periodic_rem n hp) (fun y => hasDerivAt_rem hd hc' hp n y) x

/-- Each application of the remainder subtracts a trigonometric polynomial of degree at most `n`,
so `g` and its iterated remainder differ by one. -/
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

/-- The remainder of a function with a bounded derivative is at most the first absolute moment of
the kernel times that bound. -/
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

/-- **The iterated remainder of a `k` times differentiable periodic function.** With `A` the first
absolute moment of the kernel, `k` applications of the remainder each cost a factor `A`, and the
last one is estimated by the modulus of continuity of the `k`-th derivative. -/
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

/-- **Jackson's theorem**, in terms of the first absolute moment `A = π sin (π / (2 n + 4))` of the
kernel: for a `2 π`-periodic `g` with `k` continuous derivatives whose `k`-th derivative satisfies
`|g⁽ᵏ⁾ u - g⁽ᵏ⁾ v| ≤ M |u - v|^α`, the best uniform approximation by trigonometric polynomials of
degree at most `n` is within `Aᵏ M Aᵅ`.

The derivatives are given as a tower `D 0 = g`, `D (j+1) = (D j)'`, which is what the iterated
remainder consumes; `Jackson.infDist_le_of_holder_deriv'` restates the bound with the classical
constant. -/
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

/-- The bound of `Jackson.infDist_le_of_holder_deriv` in the classical form: with `c = 1 + π²/2`
the moment satisfies `n A ≤ π²/2 < c`, so `Aᵏ M Aᵅ ≤ cᵏ⁺¹ M / n^{k+α}`. -/
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

/-- **Jackson's theorem** ([han2009theoretical], Theorem 3.7.1). Let `g` be a `2 π`-periodic
function with `k` continuous derivatives — given as a tower `D 0 = g`, `D (j+1) = (D j)'` — whose
`k`-th derivative satisfies the Hölder condition `|g⁽ᵏ⁾ u - g⁽ᵏ⁾ v| ≤ M |u - v|^α` for some
`0 < α ≤ 1`. Then for `n ≥ 1` the error of the best uniform approximation of `g` by trigonometric
polynomials of degree at most `n` satisfies

`ρₙ(g) ≤ c^{k+1} M / n^{k+α}`, with `c = 1 + π²/2`.

The proof is the Fejér–Korovkin kernel: its first absolute moment is `A ≤ π²/(2 n + 4)`, each of
the `k` applications of the remainder `Jackson.rem` costs a factor `A` because the operator
commutes with differentiation, and the last one costs `M Aᵅ`. -/
theorem infDist_le_of_holder_deriv' {G : C(AddCircle (2 * π), ℝ)} {k n : ℕ} {M α : ℝ}
    {D : ℕ → ℝ → ℝ} (hn : 1 ≤ n) (hD0 : D 0 = lift G) (hDc : ∀ j ≤ k, Continuous (D j))
    (hDd : ∀ j < k, ∀ x, HasDerivAt (D j) (D (j + 1) x) x)
    (hM : 0 ≤ M) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hhol : ∀ u v : ℝ, |D k u - D k v| ≤ M * |u - v| ^ α) :
    Metric.infDist G (trigPolyLE (2 * π) n : Set C(AddCircle (2 * π), ℝ))
      ≤ (1 + π ^ 2 / 2) ^ (k + 1) * M / (n : ℝ) ^ ((k : ℝ) + α) :=
  (infDist_le_of_holder_deriv hD0 hDc hDd hM hα0 hα1 hhol).trans
    (moment_pow_le n k hn hM hα0 hα1)

end Jackson
