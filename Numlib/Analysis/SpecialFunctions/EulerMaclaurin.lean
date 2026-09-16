import Mathlib.NumberTheory.ZetaValues
import Numlib.Approximation.NewtonCotes

/-!
# The Euler–Maclaurin formula

The Euler–Maclaurin summation formula in the form the composite trapezoidal rule uses: for `f`
of class `C^{2k+2}` on an open set containing `[a, b]`, `h = (b - a)/m` and `T_m(f)` the
composite trapezoidal sum,

`T_m(f) = ∫_a^b f + ∑_{i=1}^{k} B_{2i}/(2i)! h^{2i} (f^{(2i-1)}(b) - f^{(2i-1)}(a))
          + B_{2k+2}/(2k+2)! h^{2k+2} (b - a) f^{(2k+2)}(η)`

for some `η ∈ (a, b)` (`EulerMaclaurin.trapezoidSum_eq_integral_add_sum_add_mul`;
[quarteroni2000numerical] Property 9.3, (9.36)). The `B_j` are Mathlib's Bernoulli numbers
`bernoulli j : ℚ` (the `B₁ = -1/2` convention; only even indices occur), and
`bernoulli_eq_tsum_two_div_pow` identifies them with the book's zeta-series definition.

## Main results

* `EulerMaclaurin.integral_bernoulliFun_mul_eq` — one integration by parts against a Bernoulli
  polynomial: `∫_0^1 B_j F = [B_{j+1} F]_0^1/(j+1) - (1/(j+1)) ∫_0^1 B_{j+1} F'`.
* `EulerMaclaurin.integral_eq_sub_sum_sub_integral` — the one-panel identity on `[0, 1]` with the
  integral remainder `-(1/(2k+1)!) ∫_0^1 B_{2k+1} g^{(2k+1)}`, by induction on `k`: two
  integrations by parts per step, the odd boundary terms vanishing because the odd Bernoulli
  numbers beyond `B₁` are zero.
* `EulerMaclaurin.bernoulliFun_sub_bernoulli_sign`, `EulerMaclaurin.neg_one_pow_mul_bernoulli_pos`
  — `B_{2k}(t) - B_{2k}` has the constant sign `(-1)^k` on `[0, 1]`, and `B_{2k}` itself the sign
  `(-1)^{k+1}`: both read off Mathlib's Fourier expansion `hasSum_one_div_nat_pow_mul_cos` and
  `hasSum_zeta_nat`.
* `EulerMaclaurin.exists_integral_eq_mul` — the one-panel identity with the mean value remainder
  `-B_{2k+2}/(2k+2)! g^{(2k+2)}(η)`, `η ∈ (0, 1)`, from the sign of the weight
  `B_{2k+2} - B_{2k+2}(t)` and the weighted mean value theorem
  `intervalIntegral.exists_mem_Ioo_integral_mul_eq_mul_integral`.
* `EulerMaclaurin.trapezoidSum_eq_integral_add_sum_add_mul` — the composite formula: each panel is
  the reference panel scaled by `h`, the interior boundary terms telescope, and the `m` remainders
  are collected by the discrete mean value theorem on the open interval.

The one-panel statements take the integrand as a chain of derivatives `F 0, F 1, …` on `[0, 1]`,
as `Quadrature.error_eq_integral_peanoKernel` does, so that the composite theorem can instantiate
them with `F r s = h^r f^{(r)}(x_j + s h)` without a smoothness transport.

Relation to the rest of the library: `Quadrature.abs_sub_trapezoidSum_add_le` in
`Numlib/Approximation/CompositeQuadrature` is the case `k = 1` as a bound; the expansion here is
what Richardson extrapolation (`Numlib/Approximation/Extrapolation`, Romberg's method) consumes.
Mathlib has the Bernoulli polynomials and their Fourier expansion but no Euler–Maclaurin formula.

## References

[quarteroni2000numerical] §9.6, Property 9.3; [kress1998numerical] §9.4.
-/

open Filter Set Topology intervalIntegral
open MeasureTheory (volume)
open scoped Nat

namespace EulerMaclaurin

/-! ### Integration by parts against the Bernoulli polynomials -/

/-- **One integration by parts against a Bernoulli polynomial**: for `F` differentiable on
`[0, 1]` with continuous derivative `F'`,
`∫_0^1 B_j F = (B_{j+1}(1) F(1) - B_{j+1}(0) F(0))/(j + 1) - (1/(j + 1)) ∫_0^1 B_{j+1} F'`,
since `B_{j+1}/(j + 1)` is an antiderivative of `B_j`. -/
theorem integral_bernoulliFun_mul_eq (j : ℕ) {F F' : ℝ → ℝ}
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt F (F' t) t) (hF' : ContinuousOn F' (Icc 0 1)) :
    (∫ t in (0 : ℝ)..1, bernoulliFun j t * F t)
      = (bernoulliFun (j + 1) 1 * F 1 - bernoulliFun (j + 1) 0 * F 0) / (j + 1)
        - (1 / (j + 1)) * ∫ t in (0 : ℝ)..1, bernoulliFun (j + 1) t * F' t := by
  have hparts := integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1) (u := F) (u' := F')
    (v := fun t => bernoulliFun (j + 1) t / (j + 1)) (v' := bernoulliFun j)
    (fun t ht => hF t (by rwa [uIcc_of_le zero_le_one] at ht))
    (fun t _ => antideriv_bernoulliFun j t) (hF'.intervalIntegrable_of_Icc zero_le_one)
    (intervalIntegrable_bernoulliFun j 0 1)
  have e1 : (∫ t in (0 : ℝ)..1, bernoulliFun j t * F t)
      = ∫ t in (0 : ℝ)..1, F t * bernoulliFun j t :=
    integral_congr fun t _ => mul_comm _ _
  have e2 : (∫ t in (0 : ℝ)..1, F' t * (bernoulliFun (j + 1) t / (j + 1)))
      = (1 / (j + 1)) * ∫ t in (0 : ℝ)..1, bernoulliFun (j + 1) t * F' t := by
    rw [← integral_const_mul]
    exact integral_congr fun t _ => by ring
  rw [e1, hparts, e2]
  ring

/-- **The one-panel Euler–Maclaurin identity with integral remainder.** For a chain of
derivatives `F 0, F 1, …, F (2k+1)` on `[0, 1]` with `F (2k+1)` continuous,
`∫_0^1 F 0 = (F 0 0 + F 0 1)/2 - ∑_{i ∈ Icc 1 k} B_{2i}/(2i)! (F (2i-1) 1 - F (2i-1) 0)
  - (1/(2k+1)!) ∫_0^1 B_{2k+1}(t) F (2k+1) t dt`.

Induction on `k`: the base case is one integration by parts against `B₁(t) = t - 1/2`; the step
is two integrations by parts, the boundary term of the odd step vanishing because
`B_{2k+3}(0) = B_{2k+3}(1) = B_{2k+3} = 0`.

Reference: [quarteroni2000numerical], Property 9.3; [kress1998numerical], §9.4. -/
theorem integral_eq_sub_sum_sub_integral (k : ℕ) {F : ℕ → ℝ → ℝ}
    (hF : ∀ j < 2 * k + 1, ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (F j) (F (j + 1) t) t)
    (hc : ContinuousOn (F (2 * k + 1)) (Icc 0 1)) :
    ∫ t in (0 : ℝ)..1, F 0 t
      = (F 0 0 + F 0 1) / 2
        - ∑ i ∈ Finset.Icc 1 k, ((bernoulli (2 * i) : ℚ) : ℝ) / (2 * i)!
            * (F (2 * i - 1) 1 - F (2 * i - 1) 0)
        - (1 / ((2 * k + 1)! : ℝ)) * ∫ t in (0 : ℝ)..1,
            bernoulliFun (2 * k + 1) t * F (2 * k + 1) t := by
  induction k with
  | zero =>
    have hc1 : ContinuousOn (F 1) (Icc 0 1) := by simpa using hc
    have h := integral_bernoulliFun_mul_eq 0 (F := F 0) (F' := F 1)
      (fun t ht => hF 0 (by norm_num) t ht) hc1
    simp only [bernoulliFun_zero, one_mul, zero_add, bernoulliFun_one, Nat.cast_zero] at h
    rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty, h]
    simp only [Nat.mul_zero, zero_add, Nat.factorial_one, Nat.cast_one, bernoulliFun_one]
    ring
  | succ k ih =>
    have hchain : ∀ j < 2 * k + 1, ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (F j) (F (j + 1) t) t :=
      fun j hj t ht => hF j (by omega) t ht
    have hc' : ContinuousOn (F (2 * k + 1)) (Icc 0 1) := fun t ht =>
      (hF (2 * k + 1) (by omega) t ht).continuousAt.continuousWithinAt
    have hc'' : ContinuousOn (F (2 * k + 2)) (Icc 0 1) := fun t ht =>
      (hF (2 * k + 2) (by omega) t ht).continuousAt.continuousWithinAt
    have hc''' : ContinuousOn (F (2 * k + 3)) (Icc 0 1) := by
      simpa [show 2 * (k + 1) + 1 = 2 * k + 3 by ring] using hc
    -- two integrations by parts
    have h1 := integral_bernoulliFun_mul_eq (2 * k + 1) (F := F (2 * k + 1)) (F' := F (2 * k + 2))
      (fun t ht => hF (2 * k + 1) (by omega) t ht) hc''
    have h2 := integral_bernoulliFun_mul_eq (2 * k + 2) (F := F (2 * k + 2)) (F' := F (2 * k + 3))
      (fun t ht => hF (2 * k + 2) (by omega) t ht) hc'''
    have hB2 : bernoulliFun (2 * k + 1 + 1) 1 = bernoulliFun (2 * k + 1 + 1) 0 :=
      bernoulliFun_endpoints_eq_of_ne_one (by omega)
    have hB3 : bernoulliFun (2 * k + 2 + 1) 1 = 0 ∧ bernoulliFun (2 * k + 2 + 1) 0 = 0 := by
      have h0 : bernoulliFun (2 * k + 2 + 1) 0 = 0 := by
        rw [bernoulliFun_eval_zero, bernoulli_eq_zero_of_odd ⟨k + 1, by ring⟩ (by omega)]
        simp
      exact ⟨by rw [bernoulliFun_endpoints_eq_of_ne_one (by omega), h0], h0⟩
    rw [hB3.1, hB3.2] at h2
    simp only [zero_mul, sub_zero, zero_div, zero_sub] at h2
    rw [h2] at h1
    rw [ih hchain hc', Finset.sum_Icc_succ_top (by omega), h1, hB2, bernoulliFun_eval_zero]
    have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have e2 : 2 * (k + 1) + 1 = 2 * k + 2 + 1 := by ring
    have e3 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [e1, e2, e3]
    have hf1 : ((2 * k + 1 + 1)! : ℝ) = (2 * k + 1 + 1) * (2 * k + 1)! := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hf2 : ((2 * k + 2 + 1)! : ℝ) = (2 * k + 2 + 1) * ((2 * k + 1 + 1) * (2 * k + 1)!) := by
      rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
    rw [hf1, hf2]
    have hne : ((2 * k + 1)! : ℝ) ≠ 0 := by positivity
    push_cast at h1 ⊢
    field_simp
    ring

/-! ### The sign of `B_{2k}(t) - B_{2k}` -/

/-- `B_{2k}(t) - B_{2k}` has the constant sign `(-1)^k` on `[0, 1]` (`k = 1`: `t² - t ≤ 0`).
From the Fourier expansion `B_{2k}(t) = (-1)^{k+1} 2 (2k)!/(2π)^{2k} ∑ cos(2πnt)/n^{2k}`, so that
`B_{2k}(t) - B_{2k}` is that constant times `∑ (cos(2πnt) - 1)/n^{2k}`, a series with nonpositive
terms. -/
theorem bernoulliFun_sub_bernoulli_sign {k : ℕ} (hk : 0 < k) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ (-1) ^ k * (bernoulliFun (2 * k) t - ((bernoulli (2 * k) : ℚ) : ℝ)) := by
  set c : ℝ := (-1 : ℝ) ^ (k + 1) * (2 * Real.pi) ^ (2 * k) / 2 / (2 * k)! with hc
  have h1 := hasSum_one_div_nat_pow_mul_cos hk.ne' ht
  have h0 := hasSum_one_div_nat_pow_mul_cos hk.ne' (left_mem_Icc.2 (zero_le_one' ℝ))
  simp only [mul_zero, Real.cos_zero, mul_one] at h0
  have hsub := h1.sub h0
  have hterm : ∀ n : ℕ, 1 / (n : ℝ) ^ (2 * k) * Real.cos (2 * Real.pi * n * t)
      - 1 / (n : ℝ) ^ (2 * k) ≤ 0 := by
    intro n
    have hn : 0 ≤ 1 / (n : ℝ) ^ (2 * k) := by positivity
    nlinarith [Real.cos_le_one (2 * Real.pi * n * t)]
  have hle := hsub.nonpos hterm
  have hB0 : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * k))).eval (0 : ℝ)
      = ((bernoulli (2 * k) : ℚ) : ℝ) := bernoulliFun_eval_zero (2 * k)
  rw [hB0] at hle
  have hpos : 0 < (2 * Real.pi) ^ (2 * k) / 2 / (2 * k)! := by positivity
  have : (-1 : ℝ) ^ (k + 1) * (2 * Real.pi) ^ (2 * k) / 2 / (2 * k)! *
      (bernoulliFun (2 * k) t - ((bernoulli (2 * k) : ℚ) : ℝ)) ≤ 0 := by
    have e : (-1 : ℝ) ^ (k + 1) * (2 * Real.pi) ^ (2 * k) / 2 / (2 * k)!
        * (bernoulliFun (2 * k) t - ((bernoulli (2 * k) : ℚ) : ℝ))
        = (-1) ^ (k + 1) * (2 * Real.pi) ^ (2 * k) / 2 / (2 * k)! * bernoulliFun (2 * k) t
          - (-1) ^ (k + 1) * (2 * Real.pi) ^ (2 * k) / 2 / (2 * k)!
            * ((bernoulli (2 * k) : ℚ) : ℝ) := by ring
    rw [e]
    exact hle
  have e2 : (-1 : ℝ) ^ (k + 1) * (2 * Real.pi) ^ (2 * k) / 2 / (2 * k)!
      * (bernoulliFun (2 * k) t - ((bernoulli (2 * k) : ℚ) : ℝ))
      = -((2 * Real.pi) ^ (2 * k) / 2 / (2 * k)!)
        * ((-1) ^ k * (bernoulliFun (2 * k) t - ((bernoulli (2 * k) : ℚ) : ℝ))) := by
    rw [pow_succ]; ring
  rw [e2] at this
  nlinarith

/-- `∫_0^1 (B_{2k}(t) - B_{2k}) dt = -B_{2k}` for `0 < k`: the Bernoulli polynomial itself
integrates to zero. -/
theorem integral_bernoulliFun_sub_bernoulli {k : ℕ} (hk : 0 < k) :
    (∫ t in (0 : ℝ)..1, (bernoulliFun (2 * k) t - ((bernoulli (2 * k) : ℚ) : ℝ)))
      = -((bernoulli (2 * k) : ℚ) : ℝ) := by
  rw [integral_sub (intervalIntegrable_bernoulliFun _ _ _) intervalIntegrable_const,
    integral_bernoulliFun_eq_zero (by omega), integral_const]
  simp

/-- **The sign of the even Bernoulli numbers**: `(-1)^{k+1} B_{2k} > 0` for `0 < k`
(`B₂ = 1/6`, `B₄ = -1/30`, …), from the zeta series
`∑ 1/n^{2k} = (-1)^{k+1} 2^{2k-1} π^{2k} B_{2k}/(2k)!`, whose value is positive. -/
theorem neg_one_pow_mul_bernoulli_pos {k : ℕ} (hk : 0 < k) :
    0 < (-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℚ) : ℝ) := by
  have h := hasSum_zeta_nat hk.ne'
  have h1 : (1 : ℝ) ≤ (-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) *
      ((bernoulli (2 * k) : ℚ) : ℝ) / (2 * k)! := by
    have := le_hasSum h 1 fun j _ => by positivity
    simpa using this
  have hpos : 0 < (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) / (2 * k)! := by positivity
  have e : (-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) *
      ((bernoulli (2 * k) : ℚ) : ℝ) / (2 * k)!
      = ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) / (2 * k)!)
        * ((-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℚ) : ℝ)) := by ring
  rw [e] at h1
  by_contra hle
  push Not at hle
  nlinarith

/-! ### The mean value remainder -/

/-- **The one-panel Euler–Maclaurin identity with the mean value remainder.** For a chain of
derivatives `F 0, …, F (2k+2)` on `[0, 1]` with `F (2k+2)` continuous, there is `η ∈ (0, 1)` with
`∫_0^1 F 0 = (F 0 0 + F 0 1)/2 - ∑_{i ∈ Icc 1 k} B_{2i}/(2i)! (F (2i-1) 1 - F (2i-1) 0)
  - B_{2k+2}/(2k+2)! F (2k+2) η`.

One more integration by parts of the integral remainder of `integral_eq_sub_sum_sub_integral`,
together with `F (2k+1) 1 - F (2k+1) 0 = ∫_0^1 F (2k+2)`, writes it as
`-(1/(2k+2)!) ∫_0^1 (B_{2k+2} - B_{2k+2}(t)) F (2k+2) t dt`; the weight has the constant sign
`(-1)^k`, integrates to `B_{2k+2}`, and the weighted mean value theorem gives `η`, inside the
open interval because the weight's integral is nonzero. -/
theorem exists_integral_eq_mul (k : ℕ) {F : ℕ → ℝ → ℝ}
    (hF : ∀ j < 2 * k + 2, ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (F j) (F (j + 1) t) t)
    (hc : ContinuousOn (F (2 * k + 2)) (Icc 0 1)) :
    ∃ η ∈ Ioo (0 : ℝ) 1, ∫ t in (0 : ℝ)..1, F 0 t
      = (F 0 0 + F 0 1) / 2
        - ∑ i ∈ Finset.Icc 1 k, ((bernoulli (2 * i) : ℚ) : ℝ) / (2 * i)!
            * (F (2 * i - 1) 1 - F (2 * i - 1) 0)
        - ((bernoulli (2 * k + 2) : ℚ) : ℝ) / (2 * k + 2)! * F (2 * k + 2) η := by
  have hc' : ContinuousOn (F (2 * k + 1)) (Icc 0 1) := fun t ht =>
    (hF (2 * k + 1) (by omega) t ht).continuousAt.continuousWithinAt
  have hbase := integral_eq_sub_sum_sub_integral k (F := F) (fun j hj t ht => hF j (by omega) t ht)
    hc'
  -- one more integration by parts
  have h1 := integral_bernoulliFun_mul_eq (2 * k + 1) (F := F (2 * k + 1)) (F' := F (2 * k + 2))
    (fun t ht => hF (2 * k + 1) (by omega) t ht) hc
  have hB2 : bernoulliFun (2 * k + 1 + 1) 1 = bernoulliFun (2 * k + 1 + 1) 0 :=
    bernoulliFun_endpoints_eq_of_ne_one (by omega)
  have hftc : F (2 * k + 1) 1 - F (2 * k + 1) 0 = ∫ t in (0 : ℝ)..1, F (2 * k + 2) t :=
    (integral_eq_sub_of_hasDerivAt (fun t ht => hF (2 * k + 1) (by omega) t
      (by rwa [uIcc_of_le zero_le_one] at ht)) (hc.intervalIntegrable_of_Icc zero_le_one)).symm
  set B : ℝ := ((bernoulli (2 * k + 2) : ℚ) : ℝ) with hB
  have hB0 : bernoulliFun (2 * k + 1 + 1) 0 = B := by rw [bernoulliFun_eval_zero]
  -- the weight `(-1)^k (B - B(t))` is nonnegative with positive integral
  set K : ℝ → ℝ := fun t => (-1) ^ k * (B - bernoulliFun (2 * k + 2) t) with hK
  have hKnn : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ K t := by
    intro t ht
    have := bernoulliFun_sub_bernoulli_sign (k := k + 1) (Nat.succ_pos k) ht
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_succ] at this
    simp only [hK, hB]
    nlinarith
  have hKc : ContinuousOn K (Icc 0 1) := by
    simp only [hK]
    fun_prop
  have hKint : (∫ t in (0 : ℝ)..1, K t) = (-1) ^ k * B := by
    have := integral_bernoulliFun_sub_bernoulli (k := k + 1) (Nat.succ_pos k)
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, ← hB] at this
    have e : (∫ t in (0 : ℝ)..1, (B - bernoulliFun (2 * k + 2) t)) = B := by
      rw [show (fun t => B - bernoulliFun (2 * k + 2) t)
          = fun t => -(bernoulliFun (2 * k + 2) t - B) by funext t; ring, integral_neg, this,
        neg_neg]
    simp only [hK]
    rw [integral_const_mul, e]
  have hKpos : 0 < ∫ t in (0 : ℝ)..1, K t := by
    rw [hKint]
    have := neg_one_pow_mul_bernoulli_pos (k := k + 1) (Nat.succ_pos k)
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_succ, pow_succ, ← hB] at this
    nlinarith
  obtain ⟨η, hη, hηval⟩ :=
    intervalIntegral.exists_mem_Ioo_integral_mul_eq_mul_integral zero_lt_one hKc hc hKnn hKpos
  refine ⟨η, hη, ?_⟩
  have hsq : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by
    rw [← pow_add, ← two_mul]
    exact (even_two_mul k).neg_one_pow
  -- the remainder integral, through the weight `K`
  have hI : (∫ t in (0 : ℝ)..1, (-1) ^ k * (K t * F (2 * k + 2) t)) = B * F (2 * k + 2) η := by
    rw [integral_const_mul, hηval, hKint]
    linear_combination (F (2 * k + 2) η * B) * hsq
  have hint1 : IntervalIntegrable (fun t => B * F (2 * k + 2) t) volume 0 1 :=
    (hc.intervalIntegrable_of_Icc zero_le_one).const_mul B
  have hint2 : IntervalIntegrable (fun t => bernoulliFun (2 * k + 1 + 1) t * F (2 * k + 2) t)
      volume 0 1 :=
    (intervalIntegrable_bernoulliFun _ _ _).mul_continuousOn
      (by rw [uIcc_of_le zero_le_one]; exact hc)
  have hsplit : (∫ t in (0 : ℝ)..1, (-1) ^ k * (K t * F (2 * k + 2) t))
      = B * (∫ t in (0 : ℝ)..1, F (2 * k + 2) t)
        - ∫ t in (0 : ℝ)..1, bernoulliFun (2 * k + 1 + 1) t * F (2 * k + 2) t := by
    rw [← integral_const_mul, ← integral_sub hint1 hint2]
    refine integral_congr fun t _ => ?_
    simp only [hK]
    rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring]
    linear_combination ((B - bernoulliFun (2 * k + 2) t) * F (2 * k + 2) t) * hsq
  have hBF : B * (∫ t in (0 : ℝ)..1, F (2 * k + 2) t)
      - (∫ t in (0 : ℝ)..1, bernoulliFun (2 * k + 1 + 1) t * F (2 * k + 2) t)
      = B * F (2 * k + 2) η := hsplit.symm.trans hI
  have hrem : (∫ t in (0 : ℝ)..1, bernoulliFun (2 * k + 1) t * F (2 * k + 1) t)
      = B / (2 * k + 2) * F (2 * k + 2) η := by
    rw [h1, hB2, hB0, ← mul_sub, hftc]
    have key : ∀ c : ℝ, B * (∫ t in (0 : ℝ)..1, F (2 * k + 2) t) / c
        - 1 / c * ∫ t in (0 : ℝ)..1, bernoulliFun (2 * k + 1 + 1) t * F (2 * k + 2) t
        = B / c * F (2 * k + 2) η := by
      intro c
      rw [show B * (∫ t in (0 : ℝ)..1, F (2 * k + 2) t) / c
          - 1 / c * ∫ t in (0 : ℝ)..1, bernoulliFun (2 * k + 1 + 1) t * F (2 * k + 2) t
          = (B * (∫ t in (0 : ℝ)..1, F (2 * k + 2) t)
            - ∫ t in (0 : ℝ)..1, bernoulliFun (2 * k + 1 + 1) t * F (2 * k + 2) t) / c by ring,
        hBF]
      ring
    rw [key]
    push_cast
    ring
  rw [hbase, hrem]
  have hf : ((2 * k + 2)! : ℝ) = (2 * k + 2) * (2 * k + 1)! := by
    rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring, Nat.factorial_succ]
    push_cast
    ring
  rw [hf, div_mul_eq_div_div]
  ring

/-! ### The composite formula -/

/-- **One panel of the composite formula.** For `h > 0` and `f` of class `C^{2k+2}` on an open set
containing `[α, α + h]`, there is `ξ ∈ (α, α + h)` with
`∫_α^{α+h} f = h (f(α) + f(α + h))/2
  - ∑_{i ∈ Icc 1 k} B_{2i}/(2i)! h^{2i} (f^{(2i-1)}(α + h) - f^{(2i-1)}(α))
  - B_{2k+2}/(2k+2)! h^{2k+3} f^{(2k+2)}(ξ)`:
the reference identity `exists_integral_eq_mul` for `F r s = h^r f^{(r)}(α + s h)`, scaled by
`h`. -/
theorem exists_integral_eq_of_contDiffOn {α h : ℝ} (hh : 0 < h) {k : ℕ} {f : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hUα : Icc α (α + h) ⊆ U)
    (hf : ContDiffOn ℝ ((2 * k + 2 : ℕ) : WithTop ℕ∞) f U) :
    ∃ ξ ∈ Ioo α (α + h), ∫ t in α..(α + h), f t
      = h / 2 * (f α + f (α + h))
        - ∑ i ∈ Finset.Icc 1 k, ((bernoulli (2 * i) : ℚ) : ℝ) / (2 * i)! * h ^ (2 * i)
            * (iteratedDeriv (2 * i - 1) f (α + h) - iteratedDeriv (2 * i - 1) f α)
        - ((bernoulli (2 * k + 2) : ℚ) : ℝ) / (2 * k + 2)! * h ^ (2 * k + 3)
            * iteratedDeriv (2 * k + 2) f ξ := by
  set F : ℕ → ℝ → ℝ := fun r s => h ^ r * iteratedDeriv r f (α + s * h) with hF
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, α + s * h ∈ U := fun s hs =>
    hUα ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  have haff : ∀ s : ℝ, HasDerivAt (fun s : ℝ => α + s * h) h s := fun s => by
    simpa using ((hasDerivAt_id' s).mul_const h).const_add α
  have hchain : ∀ r < 2 * k + 2, ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (F r) (F (r + 1) s) s := by
    intro r hr s hs
    have hd := hf.hasDerivAt_iteratedDeriv_of_isOpen hU hr (hmem s hs)
    refine ((hd.comp s (haff s)).const_mul (h ^ r)).congr_deriv ?_
    simp only [hF]
    ring
  have hcont : ContinuousOn (F (2 * k + 2)) (Icc 0 1) := by
    have h1 : ContinuousOn (iteratedDeriv (2 * k + 2) f) U :=
      hf.continuousOn_iteratedDeriv_of_isOpen hU le_rfl
    have h2 : ContinuousOn (fun s : ℝ => α + s * h) (Icc 0 1) := by fun_prop
    exact continuousOn_const.mul (h1.comp h2 hmem)
  obtain ⟨η, hη, hid⟩ := exists_integral_eq_mul k hchain hcont
  refine ⟨α + η * h, ⟨by nlinarith [hη.1], by nlinarith [hη.2]⟩, ?_⟩
  have hint : (∫ t in α..(α + h), f t) = h * ∫ s in (0 : ℝ)..1, F 0 s := by
    have hcov := integral_comp_mul_add (fun t => f t) (a := 0) (b := 1) hh.ne' α
    simp only [mul_zero, zero_add, mul_one, smul_eq_mul] at hcov
    rw [show h + α = α + h by ring] at hcov
    have e : (∫ s in (0 : ℝ)..1, F 0 s) = ∫ s in (0 : ℝ)..1, f (h * s + α) :=
      integral_congr fun s _ => by
        simp only [hF, pow_zero, one_mul, iteratedDeriv_zero]
        ring_nf
    rw [e, hcov, ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
  rw [hint, hid]
  simp only [hF, pow_zero, one_mul, iteratedDeriv_zero, zero_mul, add_zero]
  have hS : ∑ i ∈ Finset.Icc 1 k, h * (((bernoulli (2 * i) : ℚ) : ℝ) / (2 * i)!
      * (h ^ (2 * i - 1) * iteratedDeriv (2 * i - 1) f (α + h)
        - h ^ (2 * i - 1) * iteratedDeriv (2 * i - 1) f α))
      = ∑ i ∈ Finset.Icc 1 k, ((bernoulli (2 * i) : ℚ) : ℝ) / (2 * i)! * h ^ (2 * i)
          * (iteratedDeriv (2 * i - 1) f (α + h) - iteratedDeriv (2 * i - 1) f α) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have h1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    have e : h ^ (2 * i) = h * h ^ (2 * i - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [e]
    ring
  rw [mul_sub, mul_sub, Finset.mul_sum, hS]
  ring

/-- **The Euler–Maclaurin expansion of the composite trapezoidal rule**
([quarteroni2000numerical] Property 9.3, (9.36)). For `a < b`, `f` of class `C^{2k+2}` on an open
set containing `[a, b]`, `0 < m` and `h = (b - a)/m`, there is `η ∈ (a, b)` with

`T_m(f) = ∫_a^b f + ∑_{i=1}^{k} B_{2i}/(2i)! h^{2i} (f^{(2i-1)}(b) - f^{(2i-1)}(a))
          + B_{2k+2}/(2k+2)! h^{2k+2} (b - a) f^{(2k+2)}(η)`.

Each panel is `exists_integral_eq_of_contDiffOn`; the interior boundary terms telescope, and the
`m` remainders, each at a point strictly inside its panel, are collected by the discrete mean value
theorem on the open interval `(a, b)`. -/
theorem trapezoidSum_eq_integral_add_sum_add_mul {a b : ℝ} (hab : a < b) {k : ℕ} {f : ℝ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((2 * k + 2 : ℕ) : WithTop ℕ∞) f U) {m : ℕ} (hm : 0 < m) :
    ∃ η ∈ Ioo a b,
      Quadrature.trapezoidSum f a ((b - a) / m) m
        = (∫ t in a..b, f t)
          + ∑ i ∈ Finset.Icc 1 k, ((bernoulli (2 * i) : ℚ) : ℝ) / (2 * i)!
              * ((b - a) / m) ^ (2 * i)
              * (iteratedDeriv (2 * i - 1) f b - iteratedDeriv (2 * i - 1) f a)
          + ((bernoulli (2 * k + 2) : ℚ) : ℝ) / (2 * k + 2)! * ((b - a) / m) ^ (2 * k + 2)
              * (b - a) * iteratedDeriv (2 * k + 2) f η := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  set h : ℝ := (b - a) / m with hh
  have hpos : 0 < h := by rw [hh]; positivity
  have hmh : (m : ℝ) * h = b - a := by rw [hh]; field_simp
  set x : ℕ → ℝ := fun j => a + j * h with hxdef
  have hx0 : x 0 = a := by simp [hxdef]
  have hxm : x m = b := by simp only [hxdef]; linarith
  have hxsucc : ∀ j : ℕ, x (j + 1) = x j + h := by
    intro j; simp only [hxdef]; push_cast; ring
  have hxmem : ∀ j ≤ m, x j ∈ Icc a b := by
    intro j hj
    have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
    have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    refine ⟨by simp only [hxdef]; nlinarith, ?_⟩
    simp only [hxdef]
    have : (j : ℝ) * h ≤ m * h := mul_le_mul_of_nonneg_right hj' hpos.le
    linarith
  have hxsub : ∀ j < m, Icc (x j) (x j + h) ⊆ Icc a b := fun j hj => by
    rw [← hxsucc]
    exact Icc_subset_Icc (hxmem j hj.le).1 (hxmem (j + 1) hj).2
  set B : ℝ := ((bernoulli (2 * k + 2) : ℚ) : ℝ) with hB
  set D : ℝ → ℝ := iteratedDeriv (2 * k + 2) f with hD
  have hDc : ContinuousOn D (Icc a b) :=
    (hf.continuousOn_iteratedDeriv_of_isOpen hU le_rfl).mono hUab
  -- the panels
  have hpanel : ∀ j < m, ∃ ξ ∈ Ioo (x j) (x j + h), ∫ t in (x j)..(x j + h), f t
      = h / 2 * (f (x j) + f (x j + h))
        - ∑ i ∈ Finset.Icc 1 k, ((bernoulli (2 * i) : ℚ) : ℝ) / (2 * i)! * h ^ (2 * i)
            * (iteratedDeriv (2 * i - 1) f (x j + h) - iteratedDeriv (2 * i - 1) f (x j))
        - B / (2 * k + 2)! * h ^ (2 * k + 3) * D ξ := fun j hj =>
    exists_integral_eq_of_contDiffOn hpos hU ((hxsub j hj).trans hUab) hf
  choose! ξ hξmem hξeq using hpanel
  have hint : ∀ j < m, IntervalIntegrable f volume (x j) (x (j + 1)) := fun j hj => by
    rw [hxsucc]
    exact ((hf.continuousOn.mono ((hxsub j hj).trans hUab)).mono
      (by rw [uIcc_of_le (by linarith)])).intervalIntegrable
  -- the integral as a sum of panel integrals
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [hx0, hxm] at hsum
  have htrap : Quadrature.trapezoidSum f a h m
      = ∑ j ∈ Finset.range m, h / 2 * (f (x j) + f (x j + h)) := by
    rw [Quadrature.trapezoidSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hxsucc]
    simp only [hxdef, Nat.cast_succ]
  -- the telescoping of the boundary terms
  have htel : ∀ i : ℕ, ∑ j ∈ Finset.range m,
      (iteratedDeriv i f (x j + h) - iteratedDeriv i f (x j))
      = iteratedDeriv i f b - iteratedDeriv i f a := by
    intro i
    have := Finset.sum_range_sub (fun j => iteratedDeriv i f (x j)) m
    simp only [hxsucc, hx0, hxm] at this
    exact this
  have hsplit : (∫ t in a..b, f t) = Quadrature.trapezoidSum f a h m
      - ∑ i ∈ Finset.Icc 1 k, ((bernoulli (2 * i) : ℚ) : ℝ) / (2 * i)! * h ^ (2 * i)
          * (iteratedDeriv (2 * i - 1) f b - iteratedDeriv (2 * i - 1) f a)
      - B / (2 * k + 2)! * h ^ (2 * k + 3) * ∑ j ∈ Finset.range m, D (ξ j) := by
    rw [← hsum, htrap, Finset.mul_sum]
    have e : ∀ j ∈ Finset.range m, (∫ t in (x j)..(x (j + 1)), f t)
        = h / 2 * (f (x j) + f (x j + h))
          - ∑ i ∈ Finset.Icc 1 k, ((bernoulli (2 * i) : ℚ) : ℝ) / (2 * i)! * h ^ (2 * i)
              * (iteratedDeriv (2 * i - 1) f (x j + h) - iteratedDeriv (2 * i - 1) f (x j))
          - B / (2 * k + 2)! * h ^ (2 * k + 3) * D (ξ j) := fun j hj => by
      rw [hxsucc]
      exact hξeq j (Finset.mem_range.1 hj)
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_comm]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, htel]
  -- the discrete mean value theorem on the open interval
  have hξIoo : ∀ j : Fin m, ξ j ∈ Ioo a b := fun j => by
    have := hξmem j j.2
    have hsub : Ioo (x j) (x j + h) ⊆ Ioo a b := by
      rw [← hxsucc]
      exact Ioo_subset_Ioo (hxmem j j.2.le).1 (hxmem (j + 1) j.2).2
    exact hsub this
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨η, hη, hηeq⟩ := (hDc.mono Ioo_subset_Icc_self).exists_sum_mul_eq_mul_sum_of_ordConnected
    ordConnected_Ioo (x := fun j : Fin m => ξ j) hξIoo (δ := fun _ => (1 : ℝ)) fun _ => zero_le_one
  simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hηeq
  rw [Finset.sum_range (fun j => D (ξ j))] at hsplit
  refine ⟨η, hη, ?_⟩
  rw [hsplit, hηeq]
  have e : h ^ (2 * k + 3) * ((m : ℝ) * D η) = h ^ (2 * k + 2) * (b - a) * D η := by
    rw [← hmh]; ring
  simp only [hD] at e ⊢
  linear_combination (B / (2 * k + 2)!) * e

/-! ### The zeta-series definition of the Bernoulli numbers -/

/-- **The book's definition of the Bernoulli numbers agrees with Mathlib's**: for `0 < j`,
`B_{2j} = (-1)^{j-1} (2j)! ∑_{n ≥ 1} 2/(2nπ)^{2j}` ([quarteroni2000numerical] Property 9.3), from
`hasSum_zeta_nat`. -/
theorem _root_.bernoulli_eq_tsum_two_div_pow {j : ℕ} (hj : 0 < j) :
    ((bernoulli (2 * j) : ℚ) : ℝ)
      = (-1) ^ (j - 1) * (2 * j)! * ∑' n : ℕ, 2 / (2 * ((n : ℝ) + 1) * Real.pi) ^ (2 * j) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h := hasSum_zeta_nat (Nat.succ_ne_zero i)
  set S : ℝ := (-1 : ℝ) ^ (i + 1 + 1) * (2 : ℝ) ^ (2 * (i + 1) - 1) * Real.pi ^ (2 * (i + 1)) *
    ((bernoulli (2 * (i + 1)) : ℚ) : ℝ) / (2 * (i + 1))! with hS
  -- drop the vanishing `n = 0` term
  have h1 : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 * (i + 1))) S := by
    have := (hasSum_nat_add_iff' (f := fun n : ℕ => 1 / (n : ℝ) ^ (2 * (i + 1))) 1).2 h
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_pow (by omega : 2 * (i + 1) ≠ 0),
      div_zero, sub_zero, Nat.cast_succ] at this
    exact this
  have h2 : HasSum (fun n : ℕ => 2 / (2 * ((n : ℝ) + 1) * Real.pi) ^ (2 * (i + 1)))
      (2 / (2 * Real.pi) ^ (2 * (i + 1)) * S) := by
    refine (h1.mul_left (2 / (2 * Real.pi) ^ (2 * (i + 1)))).congr_fun fun n => ?_
    rw [show 2 * ((n : ℝ) + 1) * Real.pi = (2 * Real.pi) * ((n : ℝ) + 1) by ring, mul_pow]
    field_simp
  rw [h2.tsum_eq, hS, Nat.add_sub_cancel, show 2 * (i + 1) - 1 = 2 * i + 1 by omega,
    show ((-1 : ℝ)) ^ (i + 1 + 1) = (-1) ^ i by rw [pow_succ, pow_succ]; ring, mul_pow]
  have hsq : ((-1 : ℝ) ^ i) * (-1) ^ i = 1 := by
    rw [← pow_add, ← two_mul]
    exact (even_two_mul i).neg_one_pow
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hfac : ((2 * (i + 1))! : ℝ) ≠ 0 := by positivity
  field_simp
  linear_combination (-(((bernoulli (2 * (i + 1)) : ℚ) : ℝ) * 2 ^ (2 * (i + 1)))) * hsq

end EulerMaclaurin
