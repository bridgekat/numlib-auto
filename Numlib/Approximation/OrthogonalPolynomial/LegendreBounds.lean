import Numlib.Approximation.OrthogonalPolynomial

/-!
# Bounds on the Legendre polynomials on `[-1, 1]`

The Legendre polynomials are bounded by `1` on `[-1, 1]`, and at the critical points of `L_n` in
that interval — the interior Gauss–Lobatto nodes — they are bounded *below*, by `1/√(4n)`. Both
bounds come from one auxiliary polynomial, the **Legendre energy**

`E_n = L_n² + (1 - x²) (L_n')² / (n(n + 1))`,

whose derivative the Legendre differential equation collapses to `2x (L_n')² / (n(n + 1))`. Hence
`E_n` decreases on `[-1, 0]` and increases on `[0, 1]`, so on `[-1, 1]` it is at most its value at
the endpoints, which is `L_n(±1)² = 1`, and at least its value at the origin. Since `L_n² ≤ E_n`
with equality wherever `(1 - x²) L_n'` vanishes, the first half gives `|L_n| ≤ 1` and the second
gives `L_n(x)² ≥ E_n(0)` at every Gauss–Lobatto node; `E_n(0)` is bounded below by `1/(4n)`
because the recurrence at the origin is `(k + 2) L_{k+2}(0) = -(k + 1) L_k(0)`, which makes
`4m L_{2m}(0)² ≥ 1` by induction.

Neither bound is in Mathlib — `Polynomial.legendre` itself is
`Numlib/Approximation/OrthogonalPolynomial` — and they are what the Legendre–Gauss–Lobatto weights
`ᾱⱼ = 2/(n(n+1) L_n(x̄ⱼ)²)` need: `|L_n| ≤ 1` gives `ᾱⱼ ≥ 2/(n(n+1))` and the lower bound gives
`ᾱⱼ ≤ 8/n`.

## Main results

* `Polynomial.abs_eval_legendre_le_one` — `|L_n(x)| ≤ 1` on `[-1, 1]`.
* `Polynomial.inv_le_eval_legendre_sq` — `1/(4n) ≤ L_n(x)²` at every `x ∈ [-1, 1]` with
  `(1 - x²) L_n'(x) = 0`.
* `Polynomial.legendre_eval_neg_one` — `L_n(-1) = (-1)^n`.

Reference: [quarteroni2000numerical] §10.4, the bounds quoted there from Bernardi and Maday.
-/

open Set

namespace Polynomial

variable {n : ℕ}

/-- **`L_n(-1) = (-1)^n`.** The three-term recurrence
`(k + 2) L_{k+2} = (2k + 3) x L_{k+1} - (k + 1) L_k` at `x = -1`, by two-step induction from
`L_0 = 1` and `L_1 = x`.

Reference: [quarteroni2000numerical] (10.12). -/
theorem legendre_eval_neg_one (n : ℕ) : (legendre n).eval (-1) = (-1) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [legendre_zero]
  | one => simp [legendre_one]
  | more k ih1 ih2 =>
    have h := congrArg (fun p : ℝ[X] => p.eval (-1)) (legendre_recurrence k)
    simp only [eval_mul, eval_add, eval_sub, eval_natCast, eval_X, eval_ofNat, eval_one] at h
    have hk : ((k : ℝ) + 2) ≠ 0 := by positivity
    have : ((k : ℝ) + 2) * (legendre (k + 2)).eval (-1) = ((k : ℝ) + 2) * (-1) ^ (k + 2) := by
      rw [h, ih1, ih2]
      ring
    exact mul_left_cancel₀ hk this

/-- **The Legendre energy** `E_n = L_n² + (1 - x²) (L_n')² / (n(n + 1))`, the polynomial whose
monotonicity on each half of `[-1, 1]` carries both bounds of this file. At `n = 0` the definition
divides by zero and is not used; every statement about it assumes `1 ≤ n`.

Reference: [quarteroni2000numerical] §10.4. -/
noncomputable def legendreEnergy (n : ℕ) : ℝ[X] :=
  legendre n ^ 2 + C (((n : ℝ) * ((n : ℝ) + 1))⁻¹) * ((1 - X ^ 2) * derivative (legendre n) ^ 2)

/-- **The derivative of the Legendre energy is `2x (L_n')² / (n(n + 1))`.** The Legendre
differential equation `(x² - 1) L_n'' + 2x L_n' = n(n + 1) L_n` (`Polynomial.legendre_ode`) turns
the two terms that involve `L_n L_n'` into each other's negatives. -/
theorem derivative_legendreEnergy (hn : 1 ≤ n) :
    derivative (legendreEnergy n)
      = C (((n : ℝ) * ((n : ℝ) + 1))⁻¹) * (2 * X * derivative (legendre n) ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : ((n : ℝ) * ((n : ℝ) + 1)) ≠ 0 := by positivity
  have hcast : ((n : ℝ[X]) * ((n : ℝ[X]) + 1)) = C ((n : ℝ) * ((n : ℝ) + 1)) := by
    rw [C_mul, C_add, C_1, C_eq_natCast]
  have hc : C (((n : ℝ) * ((n : ℝ) + 1))⁻¹) * ((n : ℝ[X]) * ((n : ℝ[X]) + 1)) = 1 := by
    rw [hcast, ← C_mul, inv_mul_cancel₀ hne, C_1]
  have hode := legendre_ode n
  rw [legendreEnergy]
  simp only [derivative_add, derivative_mul, derivative_pow, derivative_C, derivative_sub,
    derivative_one, derivative_X, Nat.cast_ofNat, map_ofNat, zero_mul,
    zero_add, mul_one]
  linear_combination (-2 * C (((n : ℝ) * ((n : ℝ) + 1))⁻¹) * derivative (legendre n)) * hode +
    (-2 * legendre n * derivative (legendre n)) * hc

/-- `E_n(1) = L_n(1)² = 1`: the second term of the energy carries the factor `1 - x²`. -/
theorem eval_legendreEnergy_one (n : ℕ) : (legendreEnergy n).eval 1 = 1 := by
  simp [legendreEnergy, legendre_eval_one]

/-- `E_n(-1) = L_n(-1)² = 1`. -/
theorem eval_legendreEnergy_neg_one (n : ℕ) : (legendreEnergy n).eval (-1) = 1 := by
  simp [legendreEnergy, legendre_eval_neg_one, ← pow_mul, mul_comm]

/-- The derivative of the Legendre energy as a function of a real variable. -/
theorem deriv_eval_legendreEnergy (hn : 1 ≤ n) (x : ℝ) :
    deriv (fun t => (legendreEnergy n).eval t) x
      = ((n : ℝ) * ((n : ℝ) + 1))⁻¹ * (2 * x * (derivative (legendre n)).eval x ^ 2) := by
  rw [Polynomial.deriv, derivative_legendreEnergy hn]
  simp

/-- **The Legendre energy is nondecreasing on `[0, 1]`**, its derivative `2x (L_n')²/(n(n+1))`
being nonnegative there. -/
theorem monotoneOn_eval_legendreEnergy (hn : 1 ≤ n) :
    MonotoneOn (fun t => (legendreEnergy n).eval t) (Icc 0 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (legendreEnergy n).continuous.continuousOn
    (legendreEnergy n).differentiableOn fun x hx => ?_
  rw [interior_Icc] at hx
  rw [deriv_eval_legendreEnergy hn]
  have : (0 : ℝ) ≤ x := hx.1.le
  positivity

/-- **The Legendre energy is nonincreasing on `[-1, 0]`.** -/
theorem antitoneOn_eval_legendreEnergy (hn : 1 ≤ n) :
    AntitoneOn (fun t => (legendreEnergy n).eval t) (Icc (-1) 0) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine antitoneOn_of_deriv_nonpos (convex_Icc (-1) 0) (legendreEnergy n).continuous.continuousOn
    (legendreEnergy n).differentiableOn fun x hx => ?_
  rw [interior_Icc] at hx
  rw [deriv_eval_legendreEnergy hn]
  have hx0 : x ≤ 0 := hx.2.le
  have hinv : (0 : ℝ) ≤ ((n : ℝ) * ((n : ℝ) + 1))⁻¹ := by positivity
  have : 2 * x * (derivative (legendre n)).eval x ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  exact mul_nonpos_of_nonneg_of_nonpos hinv this

/-- **The Legendre energy is at most `1` on `[-1, 1]`**: it is monotone towards each endpoint,
where it equals `L_n(±1)² = 1`. -/
theorem eval_legendreEnergy_le_one (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (legendreEnergy n).eval x ≤ 1 := by
  rcases le_total 0 x with h | h
  · have hm := monotoneOn_eval_legendreEnergy hn (⟨h, hx.2⟩ : x ∈ Icc (0:ℝ) 1)
      (right_mem_Icc.mpr zero_le_one) hx.2
    exact hm.trans (eval_legendreEnergy_one n).le
  · have hm := antitoneOn_eval_legendreEnergy hn (left_mem_Icc.mpr (by norm_num))
      (⟨hx.1, h⟩ : x ∈ Icc (-1:ℝ) 0) hx.1
    exact hm.trans (eval_legendreEnergy_neg_one n).le

/-- **The Legendre energy is at least its value at the origin**, on all of `[-1, 1]`. -/
theorem eval_legendreEnergy_zero_le (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (legendreEnergy n).eval 0 ≤ (legendreEnergy n).eval x := by
  rcases le_total 0 x with h | h
  · exact monotoneOn_eval_legendreEnergy hn (left_mem_Icc.mpr zero_le_one) ⟨h, hx.2⟩ h
  · exact antitoneOn_eval_legendreEnergy hn ⟨hx.1, h⟩ (right_mem_Icc.mpr (by norm_num)) h

/-- **`L_n(x)² ≤ 1` on `[-1, 1]`**: the energy dominates `L_n²` there and is at most `1`.

Reference: [quarteroni2000numerical] §10.4. -/
theorem eval_legendre_sq_le_one (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (legendre n).eval x ^ 2 ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [legendre_zero]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : (0 : ℝ) ≤ ((n : ℝ) * ((n : ℝ) + 1))⁻¹
      * ((1 - x ^ 2) * (derivative (legendre n)).eval x ^ 2) := by
    have h1 : (0 : ℝ) ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have h2 : (0 : ℝ) ≤ ((n : ℝ) * ((n : ℝ) + 1))⁻¹ := by positivity
    exact mul_nonneg h2 (mul_nonneg h1 (sq_nonneg _))
  have hE := eval_legendreEnergy_le_one hn hx
  rw [legendreEnergy] at hE
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_sub, eval_one, eval_X] at hE
  linarith

/-- **The Legendre polynomials are bounded by `1` on `[-1, 1]`**, `|L_n(x)| ≤ 1`.

Reference: [quarteroni2000numerical] §10.4. -/
theorem abs_eval_legendre_le_one (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(legendre n).eval x| ≤ 1 := by
  have h := eval_legendre_sq_le_one n hx
  nlinarith [abs_nonneg ((legendre n).eval x), sq_abs ((legendre n).eval x)]

/-- The three-term recurrence at the origin: `(k + 2) L_{k+2}(0) = -(k + 1) L_k(0)`. -/
private theorem eval_legendre_zero_succ_succ (k : ℕ) :
    ((k : ℝ) + 2) * (legendre (k + 2)).eval 0 = -(((k : ℝ) + 1) * (legendre k).eval 0) := by
  have h := congrArg (fun p : ℝ[X] => p.eval 0) (legendre_recurrence k)
  simp only [eval_mul, eval_add, eval_sub, eval_natCast, eval_X, eval_ofNat, eval_one, mul_zero,
    zero_mul] at h
  linarith

/-- `L_{k+1}'(0) = (k + 1) L_k(0)`, from `L_{k+1}' = x L_k' + (k + 1) L_k`. -/
private theorem eval_derivative_legendre_zero (k : ℕ) :
    (derivative (legendre (k + 1))).eval 0 = ((k : ℝ) + 1) * (legendre k).eval 0 := by
  have h := congrArg (fun p : ℝ[X] => p.eval 0) (derivative_legendre_succ k)
  simp only [eval_add, eval_mul, eval_X, eval_natCast, eval_one, zero_mul, zero_add] at h
  exact h

/-- **`4m L_{2m}(0)² ≥ 1` for `m ≥ 1`**, stated at `m + 1`. The recurrence at the origin gives
`L_{2m+2}(0) = -((2m+1)/(2m+2)) L_{2m}(0)`, and the induction step reduces to
`(2m+1)²(m+1) ≥ m(2m+2)²`, whose difference is `m + 1`. -/
theorem one_le_eval_legendre_zero_sq (m : ℕ) :
    1 ≤ 4 * ((m : ℝ) + 1) * (legendre (2 * (m + 1))).eval 0 ^ 2 := by
  induction m with
  | zero =>
    have h := eval_legendre_zero_succ_succ 0
    simp only [Nat.cast_zero, zero_add, legendre_zero, eval_one, mul_one] at h
    norm_num
    nlinarith [h]
  | succ k ih =>
    have hidx : 2 * (k + 1 + 1) = 2 * (k + 1) + 2 := by omega
    have h := eval_legendre_zero_succ_succ (2 * (k + 1))
    push_cast at h
    rw [hidx]
    push_cast
    set A := (legendre (2 * (k + 1))).eval 0 with hA
    set B := (legendre (2 * (k + 1) + 2)).eval 0 with hB
    have hsq : (2 * (k : ℝ) + 4) ^ 2 * B ^ 2 = (2 * (k : ℝ) + 3) ^ 2 * A ^ 2 := by
      linear_combination ((2 * (k : ℝ) + 4) * B - (2 * (k : ℝ) + 3) * A) * h
    have hpos : (0 : ℝ) < (2 * (k : ℝ) + 4) ^ 2 * (4 * ((k : ℝ) + 1)) := by positivity
    refine le_of_mul_le_mul_right ?_ hpos
    have hkey : 4 * ((k : ℝ) + 1 + 1) * B ^ 2 * ((2 * (k : ℝ) + 4) ^ 2 * (4 * ((k : ℝ) + 1)))
        = (4 * ((k : ℝ) + 1 + 1) * (2 * (k : ℝ) + 3) ^ 2) * (4 * ((k : ℝ) + 1) * A ^ 2) := by
      linear_combination (4 * ((k : ℝ) + 1 + 1) * (4 * ((k : ℝ) + 1))) * hsq
    rw [one_mul, hkey]
    have h1 : (4 * ((k : ℝ) + 1 + 1) * (2 * (k : ℝ) + 3) ^ 2) * 1
        ≤ (4 * ((k : ℝ) + 1 + 1) * (2 * (k : ℝ) + 3) ^ 2) * (4 * ((k : ℝ) + 1) * A ^ 2) :=
      mul_le_mul_of_nonneg_left ih (by positivity)
    nlinarith [h1]

/-- The arithmetic of the even case of `Polynomial.inv_le_eval_legendreEnergy_zero`. -/
private theorem even_energy_bound {M A : ℝ} (hM : 0 < M) (hb : 1 ≤ 4 * M * A ^ 2) :
    1 / (4 * (2 * M)) ≤ A ^ 2 := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hb, sq_nonneg A]

/-- The arithmetic of the odd case of `Polynomial.inv_le_eval_legendreEnergy_zero`. -/
private theorem odd_energy_bound {M A : ℝ} (hM : 0 < M) (hb : 1 ≤ 4 * M * A ^ 2) :
    1 / (4 * (2 * M + 1)) ≤ ((2 * M + 1) * (2 * M + 1 + 1))⁻¹ * ((2 * M + 1) * A) ^ 2 := by
  have hden : (0 : ℝ) < (2 * M + 1) * (2 * M + 1 + 1) := by positivity
  rw [inv_mul_eq_div, div_le_div_iff₀ (by positivity) hden]
  have h2 : (2 * M + 1) ^ 3 * 1 ≤ (2 * M + 1) ^ 3 * (4 * M * A ^ 2) :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  have h3 : M * ((2 * M + 1) * (2 * M + 1 + 1)) ≤ (2 * M + 1) ^ 3 := by nlinarith [hM.le]
  nlinarith [h2, h3, hM]

/-- **`E_n(0) ≥ 1/(4n)` for `n ≥ 1`.** For even `n = 2m` the energy at the origin is at least
`L_{2m}(0)² ≥ 1/(4m) = 1/(2n)`; for odd `n = 2m + 1` the polynomial vanishes at the origin and the
derivative term `(2m+1)² L_{2m}(0)²/((2m+1)(2m+2))` carries the bound instead. -/
theorem inv_le_eval_legendreEnergy_zero (hn : 1 ≤ n) :
    1 / (4 * (n : ℝ)) ≤ (legendreEnergy n).eval 0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hE : (legendreEnergy n).eval 0
      = (legendre n).eval 0 ^ 2
        + ((n : ℝ) * ((n : ℝ) + 1))⁻¹ * (derivative (legendre n)).eval 0 ^ 2 := by
    rw [legendreEnergy]
    simp
  rw [hE]
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨j, rfl⟩ : ∃ j, n = 2 * (j + 1) := ⟨m - 1, by omega⟩
    have hb := one_le_eval_legendre_zero_sq j
    have hterm : (0 : ℝ) ≤ ((((2 * (j + 1) : ℕ)) : ℝ) * ((((2 * (j + 1) : ℕ)) : ℝ) + 1))⁻¹
        * (derivative (legendre (2 * (j + 1)))).eval 0 ^ 2 := by positivity
    have hcast : (((2 * (j + 1) : ℕ)) : ℝ) = 2 * ((j : ℝ) + 1) := by push_cast; ring
    rw [hcast]
    have hd := even_energy_bound (M := (j : ℝ) + 1) (A := (legendre (2 * (j + 1))).eval 0)
      (by positivity) hb
    rw [hcast] at hterm
    linarith
  · obtain rfl : n = 2 * m + 1 := by omega
    have hder : (derivative (legendre (2 * m + 1))).eval 0
        = (2 * (m : ℝ) + 1) * (legendre (2 * m)).eval 0 := by
      have h := eval_derivative_legendre_zero (2 * m)
      push_cast at h
      exact h
    have hcast : (((2 * m + 1 : ℕ)) : ℝ) = 2 * (m : ℝ) + 1 := by push_cast; ring
    rw [hcast, hder]
    have hsq : (0 : ℝ) ≤ (legendre (2 * m + 1)).eval 0 ^ 2 := sq_nonneg _
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · norm_num [legendre_one, legendre_zero]
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      have hb := one_le_eval_legendre_zero_sq j
      have hjc : ((j : ℝ) + 1 : ℝ) = (((j + 1 : ℕ)) : ℝ) := by push_cast; ring
      have hd := odd_energy_bound (M := (j : ℝ) + 1) (A := (legendre (2 * (j + 1))).eval 0)
        (by positivity) hb
      rw [hjc] at hd
      linarith

/-- **At a Gauss–Lobatto node the Legendre polynomial is bounded below:** if `x ∈ [-1, 1]` and
`(1 - x²) L_n'(x) = 0` — that is, `x = ±1` or `x` is a zero of `L_n'` — then `L_n(x)² ≥ 1/(4n)`.
The energy equals `L_n²` at such a point and is at least `E_n(0) ≥ 1/(4n)`.

This is the quantitative half of the bounds [quarteroni2000numerical] quotes after (10.34) for the
Legendre–Gauss–Lobatto weights `ᾱⱼ = 2/(n(n + 1) L_n(x̄ⱼ)²)`; it gives `ᾱⱼ ≤ 8/n`. -/
theorem inv_le_eval_legendre_sq (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1)
    (hcrit : (1 - x ^ 2) * (derivative (legendre n)).eval x = 0) :
    1 / (4 * (n : ℝ)) ≤ (legendre n).eval x ^ 2 := by
  have hE : (legendreEnergy n).eval x = (legendre n).eval x ^ 2 := by
    rw [legendreEnergy]
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_sub, eval_one, eval_X]
    linear_combination (((n : ℝ) * ((n : ℝ) + 1))⁻¹ * (derivative (legendre n)).eval x) * hcrit
  calc 1 / (4 * (n : ℝ)) ≤ (legendreEnergy n).eval 0 := inv_le_eval_legendreEnergy_zero hn
    _ ≤ (legendreEnergy n).eval x := eval_legendreEnergy_zero_le hn hx
    _ = (legendre n).eval x ^ 2 := hE

end Polynomial
