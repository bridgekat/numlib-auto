import Numlib.Approximation.GaussLobatto
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

## The Legendre–Gauss–Lobatto discrete norm on `ℙ_n`

The second part of the file (which would sit in `Numlib/Approximation/GaussLobatto` and is kept
here only to leave that module untouched) is the norm equivalence

`‖p‖_{L²(-1,1)} ≤ ‖p‖_n ≤ √3 ‖p‖_{L²(-1,1)}` for `p ∈ ℙ_n`,

quoted by [quarteroni2000numerical] §12.3 from [CHQZ88] p. 286, where `‖p‖_n² = (p, p)_n` is the
Legendre–Gauss–Lobatto discrete inner product with `n + 1` nodes. Split `p = r + c L_n` with
`r ∈ ℙ_{n-1}`; the rule is exact on `r²` and `r L_n`, so `(p, p)_n = ‖r‖² + c² (L_n, L_n)_n` with
`(L_n, L_n)_n = 2/n` (`Quadrature.discreteInner_legendre_legendre`), while
`‖p‖² = ‖r‖² + c² · 2/(2n+1)`; the two constants are `1 ≤ (2n+1)/n ≤ 3`
(`Quadrature.integral_sq_le_discreteInner_self_legendre`,
`Quadrature.discreteInner_self_legendre_le_three_mul_integral_sq`). To reach the rule from the
hypotheses "distinct nodes containing `±1`, exact to degree `2n - 1`" alone,
`Quadrature.nodal_eq_lobattoNodal_of_isExactOnMeasure` identifies its nodal polynomial with the
Lobatto nodal polynomial: the Gauss–Lobatto rule of a weight is unique.

Reference: [quarteroni2000numerical] §10.4, the bounds quoted there from Bernardi and Maday;
§12.3 for the norm equivalence.
-/

open MeasureTheory Polynomial Set

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

/-! ### The Legendre–Gauss–Lobatto discrete norm on `ℙ_n` -/

namespace Quadrature

open OrthogonalPolynomial

variable {μ : Measure ℝ}

/-- **The nodal polynomial of a Gauss–Lobatto rule is the Lobatto nodal polynomial.** A rule with
`n + 1` distinct nodes among which `±1`, exact to degree `2n - 1` for a weight carried by
`[-1, 1]`, has nodal polynomial `∏ (X - x_j) = ω̄_n`: both are monic of degree `n + 1`, vanish at
`±1` and are `μ`-orthogonal to the polynomials of degree at most `n - 2` (Jacobi's theorem
`Quadrature.isExactOnMeasure_add_iff`), so their difference is `(X² - 1) s` with `s` of degree at
most `n - 2` orthogonal to itself for the modified weight, hence zero. It is the converse of
`Quadrature.isExactOnMeasure_of_nodal_eq_lobattoNodal`: the Gauss–Lobatto rule is unique. -/
theorem nodal_eq_lobattoNodal_of_isExactOnMeasure (hw : IsWeight μ)
    (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0) {n : ℕ} (hn : 1 ≤ n) {x w : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) (h1 : ∃ i, x i = 1) (h2 : ∃ i, x i = -1)
    (hexact : IsExactOnMeasure μ w x (2 * n - 1)) :
    Lagrange.nodal Finset.univ x = lobattoNodal μ n := by
  have hw' := isWeight_lobattoMeasure hw hsupp
  set g := Lagrange.nodal Finset.univ x with hg
  have hgdeg : g.degree = ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [hg, Lagrange.degree_nodal]; simp
  have hgmonic : g.Monic := Lagrange.nodal_monic
  have hg1 : g.eval 1 = 0 := by
    obtain ⟨i, hi⟩ := h1
    rw [← hi]; exact Lagrange.eval_nodal_at_node (Finset.mem_univ i)
  have hg2 : g.eval (-1) = 0 := by
    obtain ⟨i, hi⟩ := h2
    rw [← hi]; exact Lagrange.eval_nodal_at_node (Finset.mem_univ i)
  -- the difference `d = g - ω̄` is `(X² - 1) s`
  set d := g - lobattoNodal μ n with hd
  have hd1 : d.eval 1 = 0 := by rw [hd, eval_sub, hg1, lobattoNodal_eval_one, sub_zero]
  have hd2 : d.eval (-1) = 0 := by rw [hd, eval_sub, hg2, lobattoNodal_eval_neg_one, sub_zero]
  obtain ⟨r₁, hr₁⟩ : ∃ r₁ : ℝ[X], d = (X - C 1) * r₁ :=
    ⟨_, (mul_divByMonic_eq_iff_isRoot.mpr hd1).symm⟩
  have hr₁root : r₁.eval (-1) = 0 := by
    have h := hd2
    rw [hr₁, eval_mul, eval_sub, eval_X, eval_C] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  obtain ⟨s, hs⟩ : ∃ s : ℝ[X], r₁ = (X - C (-1)) * s :=
    ⟨_, (mul_divByMonic_eq_iff_isRoot.mpr hr₁root).symm⟩
  have hds : d = (X ^ 2 - 1) * s := by
    rw [hr₁, hs, C_neg, C_1]
    ring
  have hquad : (X ^ 2 - 1 : ℝ[X]).Monic := by
    have := monic_X_pow_sub_C (1 : ℝ) two_ne_zero
    rwa [C_1] at this
  have hquadnat : (X ^ 2 - 1 : ℝ[X]).natDegree = 2 := by
    have := natDegree_X_pow_sub_C (n := 2) (r := (1 : ℝ))
    rwa [C_1] at this
  have hddeg : d.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    have := degree_sub_lt_left (p := g) (q := lobattoNodal μ n)
      (by rw [hgdeg, degree_lobattoNodal μ hn]) hgmonic.ne_zero
      (by rw [hgmonic.leadingCoeff, (lobattoNodal_monic μ n).leadingCoeff])
    rwa [hgdeg] at this
  -- the degree of `s` is less than `n - 1`
  have hsnat : s ≠ 0 → 2 + s.natDegree < n + 1 := by
    intro hs0
    have hd0 : d ≠ 0 := by
      rw [hds]; exact mul_ne_zero hquad.ne_zero hs0
    rw [degree_eq_natDegree hd0, hds, natDegree_mul hquad.ne_zero hs0, hquadnat] at hddeg
    exact_mod_cast hddeg
  suffices hs0 : s = 0 by
    have hd0 : d = 0 := by rw [hds, hs0, mul_zero]
    exact sub_eq_zero.mp hd0
  by_contra hs0
  have hsnat' := hsnat hs0
  have hn2 : 2 ≤ n := by omega
  have hsdeg : s.degree ≤ ((n - 2 : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree hs0]
    exact_mod_cast (by omega : s.natDegree ≤ n - 2)
  -- `g` is orthogonal to the polynomials of degree at most `n - 2`
  have hgorth : ∫ t, g.eval t * s.eval t ∂μ = 0 := by
    have h := (isExactOnMeasure_add_iff hw (m := n - 1) (by omega) hx w).1
      (by rw [show n + (n - 1) = 2 * n - 1 by omega]; exact hexact)
    exact h.2 s (hsdeg.trans (by exact_mod_cast (by omega : n - 2 ≤ n - 1 - 1)))
  -- `d` is orthogonal to `s`, so `∫ s² d((1 - x²) μ) = 0`
  have horth : ∫ t, d.eval t * s.eval t ∂μ = 0 := by
    have e2 : ∫ t, (lobattoNodal μ n).eval t * s.eval t ∂μ = 0 :=
      integral_lobattoNodal_mul_of_degree_le hw hsupp hn2 hsdeg
    have hev : ∀ t, d.eval t * s.eval t =
        g.eval t * s.eval t - (lobattoNodal μ n).eval t * s.eval t := by
      intro t; rw [hd, eval_sub]; ring
    simp only [hev]
    rw [integral_sub (hw.integrable_eval_mul _ _) (hw.integrable_eval_mul _ _), hgorth, e2,
      sub_zero]
  have hsq : ∫ t, s.eval t ^ 2 ∂lobattoMeasure μ = 0 := by
    rw [integral_lobattoMeasure hsupp, ← neg_eq_zero, ← integral_neg, ← horth]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    rw [hds]
    simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one]
    ring
  exact (hw'.integral_eval_sq_pos hs0).ne' hsq

/-- A rule with `n + 1` distinct nodes exact to degree `2n - 1 ≥ n` is interpolatory. -/
theorem isInterpolatoryMeasure_of_isExactOnMeasure_two_mul_sub_one (hw : IsWeight μ) {n : ℕ}
    (hn : 1 ≤ n) {x w : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hexact : IsExactOnMeasure μ w x (2 * n - 1)) : IsInterpolatoryMeasure μ w x :=
  (isInterpolatoryMeasure_iff_isExactOnMeasure hw hx).mpr (hexact.mono (by omega))


/-- The discrete inner product of `f + c • g` with itself, expanded. -/
theorem discreteInner_add_smul_self {n : ℕ} (w x : Fin n → ℝ) (f g : ℝ → ℝ) (c : ℝ) :
    discreteInner w x (f + c • g) (f + c • g) =
      discreteInner w x f f + 2 * c * discreteInner w x f g + c ^ 2 * discreteInner w x g g := by
  simp only [discreteInner, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The `L²(μ)` inner product of `p + c L` with itself, expanded, for polynomials. -/
theorem integral_eval_add_C_mul_sq (hw : IsWeight μ) (p q : ℝ[X]) (c : ℝ) :
    ∫ t, (p + C c * q).eval t ^ 2 ∂μ =
      (∫ t, p.eval t ^ 2 ∂μ) + 2 * c * (∫ t, p.eval t * q.eval t ∂μ) +
        c ^ 2 * ∫ t, q.eval t ^ 2 ∂μ := by
  have hev : ∀ t, (p + C c * q).eval t ^ 2 =
      p.eval t ^ 2 + 2 * c * (p.eval t * q.eval t) + c ^ 2 * q.eval t ^ 2 := by
    intro t; simp only [eval_add, eval_mul, eval_C]; ring
  simp only [hev]
  rw [integral_add, integral_add, integral_const_mul, integral_const_mul]
  · exact hw.integrable_eval_sq p
  · exact (hw.integrable_eval_mul p q).const_mul _
  · exact (hw.integrable_eval_sq p).add ((hw.integrable_eval_mul p q).const_mul _)
  · exact (hw.integrable_eval_sq q).const_mul _

/-- The two norms of `p ∈ ℙ_n` for the Legendre–Gauss–Lobatto rule, through the split
`p = r + c L_n` with `r ∈ ℙ_{n-1}`: `(p, p)_n = ∫ r² + c² · 2/n` and
`∫ p² = ∫ r² + c² · 2/(2n+1)`. -/
theorem discreteInner_self_legendre_eq_and_integral_sq_eq {n : ℕ} (hn : 1 ≤ n)
    {x w : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hint : IsInterpolatoryMeasure legendreMeasure w x)
    (hnodal : Lagrange.nodal Finset.univ x = lobattoNodal legendreMeasure n)
    (hexact : IsExactOnMeasure legendreMeasure w x (2 * n - 1)) {p : ℝ[X]}
    (hp : p.natDegree ≤ n) :
    ∃ R c : ℝ, 0 ≤ R ∧
      discreteInner w x (fun t => p.eval t) (fun t => p.eval t) = R + c ^ 2 * (2 / n) ∧
      ∫ t, p.eval t ^ 2 ∂legendreMeasure = R + c ^ 2 * (2 / (2 * n + 1)) := by
  have hw := isWeight_legendreMeasure
  have hlc : (Polynomial.legendre n).coeff n ≠ 0 := by
    have h := leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero n)
    rwa [leadingCoeff, natDegree_legendre] at h
  set c : ℝ := p.coeff n / (Polynomial.legendre n).coeff n with hc
  set r : ℝ[X] := p - C c * Polynomial.legendre n with hr
  have hpr : p = r + C c * Polynomial.legendre n := by rw [hr]; ring
  -- `r` has degree less than `n`
  have hrdeg : r.degree < n := by
    rw [degree_lt_iff_coeff_zero]
    intro m hm
    rcases eq_or_lt_of_le hm with rfl | hlt
    · rw [hr, coeff_sub, coeff_C_mul, hc, div_mul_cancel₀ _ hlc, sub_self]
    · rw [hr, coeff_sub, coeff_C_mul, coeff_eq_zero_of_natDegree_lt (hp.trans_lt hlt),
        coeff_eq_zero_of_natDegree_lt (by rw [natDegree_legendre]; exact hlt), mul_zero,
        sub_self]
  have hrdeg' : r.degree ≤ ((n - 1 : ℕ) : WithBot ℕ) := by
    rcases eq_or_ne r 0 with hr0 | hr0
    · rw [hr0, degree_zero]; exact bot_le
    · rw [degree_eq_natDegree hr0] at hrdeg ⊢
      exact_mod_cast (by
        have : r.natDegree < n := by exact_mod_cast hrdeg
        omega)
  -- the function form of the split
  have hfun : (fun t => p.eval t) =
      (fun t => r.eval t) + c • fun t => (Polynomial.legendre n).eval t := by
    funext t
    rw [hpr]
    simp only [eval_add, eval_mul, eval_C, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  -- the discrete inner products of the pieces
  have hrr : discreteInner w x (fun t => r.eval t) (fun t => r.eval t) =
      ∫ t, r.eval t ^ 2 ∂legendreMeasure := by
    rw [discreteInner_eq_integral_of_degree_le hexact]
    · exact integral_congr_ae (Filter.Eventually.of_forall fun t => (sq _).symm)
    · calc r.degree + r.degree ≤ ((n - 1 : ℕ) : WithBot ℕ) + ((n - 1 : ℕ) : WithBot ℕ) := by
            gcongr
        _ ≤ ((2 * n - 1 : ℕ) : WithBot ℕ) := by
            norm_cast
            omega
  have hrL_int : ∫ t, r.eval t * (Polynomial.legendre n).eval t ∂legendreMeasure = 0 := by
    rw [← integral_legendre_mul_of_degree_lt hrdeg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => mul_comm _ _)
  have hrL : discreteInner w x (fun t => r.eval t) (fun t => (Polynomial.legendre n).eval t)
      = 0 := by
    rw [discreteInner_eq_integral_of_degree_le hexact, hrL_int]
    calc r.degree + (Polynomial.legendre n).degree
        ≤ ((n - 1 : ℕ) : WithBot ℕ) + (n : WithBot ℕ) := by
          rw [degree_legendre]; gcongr
      _ ≤ ((2 * n - 1 : ℕ) : WithBot ℕ) := by
          norm_cast
          omega
  have hLL : discreteInner w x (fun t => (Polynomial.legendre n).eval t)
      (fun t => (Polynomial.legendre n).eval t) = 2 / n := by
    have h := discreteInner_legendre_legendre hn hx hint hnodal hexact le_rfl le_rfl
    rwa [ite_eq_left rfl, ite_eq_left rfl] at h
  have hLL_int : ∫ t, (Polynomial.legendre n).eval t ^ 2 ∂legendreMeasure = 2 / (2 * n + 1) := by
    rw [integral_legendreMeasure, integral_legendre_sq]
  refine ⟨∫ t, r.eval t ^ 2 ∂legendreMeasure, c, integral_nonneg fun t => sq_nonneg _, ?_, ?_⟩
  · rw [hfun, discreteInner_add_smul_self, hrr, hrL, hLL]
    ring
  · rw [hpr, integral_eval_add_C_mul_sq hw, hrL_int, hLL_int]
    ring

/-- **The lower half of the norm equivalence on `ℙ_n`**: `‖p‖²_{L²(-1,1)} ≤ (p, p)_n` for the
Legendre–Gauss–Lobatto discrete inner product with `n + 1` nodes and every polynomial of degree
at most `n`. With `p = r + c L_n`, `r ∈ ℙ_{n-1}`, exactness gives `(p, p)_n = ‖r‖² + c² · 2/n`
while `‖p‖² = ‖r‖² + c² · 2/(2n + 1)`.

Reference: [quarteroni2000numerical] §12.3, the equivalence quoted there from [CHQZ88] p. 286. -/
theorem integral_sq_le_discreteInner_self_legendre {n : ℕ} (hn : 1 ≤ n)
    {x w : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hint : IsInterpolatoryMeasure legendreMeasure w x)
    (hnodal : Lagrange.nodal Finset.univ x = lobattoNodal legendreMeasure n)
    (hexact : IsExactOnMeasure legendreMeasure w x (2 * n - 1)) {p : ℝ[X]}
    (hp : p.natDegree ≤ n) :
    ∫ t, p.eval t ^ 2 ∂legendreMeasure ≤
      discreteInner w x (fun t => p.eval t) (fun t => p.eval t) := by
  obtain ⟨R, c, -, h1, h2⟩ :=
    discreteInner_self_legendre_eq_and_integral_sq_eq hn hx hint hnodal hexact hp
  rw [h1, h2]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : (2 : ℝ) / (2 * n + 1) ≤ 2 / n := by
    rw [div_le_div_iff₀ (by positivity) hnR]
    nlinarith
  nlinarith [sq_nonneg c]

/-- **The upper half of the norm equivalence on `ℙ_n`**: `(p, p)_n ≤ 3 ‖p‖²_{L²(-1,1)}` for the
Legendre–Gauss–Lobatto discrete inner product with `n + 1` nodes and every polynomial of degree
at most `n`, i.e. `‖p‖_n ≤ √3 ‖p‖_{L²(-1,1)}`; the ratio of the two coefficients of `c²` in
`Quadrature.discreteInner_self_legendre_eq_and_integral_sq_eq` is `(2n + 1)/n ≤ 3`.

Reference: [quarteroni2000numerical] §12.3, the equivalence quoted there from [CHQZ88] p. 286. -/
theorem discreteInner_self_legendre_le_three_mul_integral_sq {n : ℕ} (hn : 1 ≤ n)
    {x w : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hint : IsInterpolatoryMeasure legendreMeasure w x)
    (hnodal : Lagrange.nodal Finset.univ x = lobattoNodal legendreMeasure n)
    (hexact : IsExactOnMeasure legendreMeasure w x (2 * n - 1)) {p : ℝ[X]}
    (hp : p.natDegree ≤ n) :
    discreteInner w x (fun t => p.eval t) (fun t => p.eval t) ≤
      3 * ∫ t, p.eval t ^ 2 ∂legendreMeasure := by
  obtain ⟨R, c, hR, h1, h2⟩ :=
    discreteInner_self_legendre_eq_and_integral_sq_eq hn hx hint hnodal hexact hp
  rw [h1, h2]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hle : (2 : ℝ) / n ≤ 3 * (2 / (2 * n + 1)) := by
    rw [← mul_div_assoc, div_le_div_iff₀ hnR (by positivity)]
    nlinarith
  nlinarith [sq_nonneg c]

end Quadrature
