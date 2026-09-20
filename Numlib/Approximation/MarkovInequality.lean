import Numlib.Approximation.OrthogonalPolynomial.LegendreBounds

/-!
# The `L²` Markov inequality on `[-1, 1]`

For a polynomial `p` of degree at most `N`,

`‖p'‖_{L²(-1,1)} ≤ N (N + 1) ‖p‖_{L²(-1,1)}`

(`Polynomial.integral_derivative_sq_le`, `Polynomial.sqrt_integral_derivative_sq_le`): the `L²`
analogue of Markov's inequality `‖p'‖_∞ ≤ N² ‖p‖_∞`, which is what makes the largest eigenvalue
of a spectral (Legendre, Gauss–Lobatto) stiffness matrix grow like `N⁴`
([quarteroni2000numerical] §13.3.1, (13.24)). The constant `N (N + 1)` is not the sharp one, but the
order `N²` is: the test polynomial `L_N' ∈ ℙ_{N-1}` has `‖L_N''‖² ≥ ((N(N+1))²/36) ‖L_N'‖²`
(`Polynomial.integral_derivative_derivative_legendre_sq_ge`).

## The proof

Everything runs through the **Legendre coefficients** `p̂_k = ((2k + 1)/2) ∫_{-1}^1 p L_k`
(`Polynomial.legendreCoeff`): `p = ∑_{k ≤ N} p̂_k L_k` for `p ∈ ℙ_N`
(`Polynomial.eq_sum_legendreCoeff`) and Parseval's identity `∫ p² = ∑_k p̂_k² · 2/(2k + 1)`
(`Polynomial.integral_sq_eq_sum_legendreCoeff`), both from the orthogonality
`∫ L_j L_k = (2/(2k + 1)) δ_{jk}` of `Numlib/Approximation/OrthogonalPolynomial`. Integrating by
parts, `∫ L_k' L_j = 1 - (-1)^{k+j}` for `j < k` and `0` otherwise
(`Polynomial.integral_derivative_legendre_mul_legendre`) — the identity behind the classical
expansion `L_k' = ∑_{j < k, k - j odd} (2j + 1) L_j` — so the coefficients of `p'` obey
`|(p')^_j| ≤ (2j + 1) ∑_k |p̂_k|`, and Cauchy–Schwarz `(∑_k |p̂_k|)² ≤ ((N + 1)²/2) ∫ p²` together
with `∑_{j < N} (2j + 1) = N²` gives the bound. The sharpness statement pairs `L_N''` with `x L_N'`
by parts: `∫ x L_N' L_N'' = (N(N+1)/2)² - N(N+1)/2` while `‖L_N'‖² = N(N+1)`, from the endpoint
values `L_n'(±1) = (±1)^{n+1} n(n+1)/2` (`Polynomial.eval_one_derivative_legendre`,
`Polynomial.eval_neg_one_derivative_legendre`).

`intervalIntegral.sq_integral_mul_le_of_continuousOn` is Cauchy–Schwarz for interval integrals of
continuous functions (Mathlib has Hölder only for `lintegral` and `MemLp` data); it duplicates the
surface's `QuarteroniSaccoSaleri.Chapter12.sq_integral_mul_le`, which should be repointed here.

## References

[quarteroni2000numerical] §13.3.1; Canuto–Hussaini–Quarteroni–Zang, *Spectral Methods in Fluid
Dynamics*, Springer 1988, §9.4 (the inverse inequalities for Legendre expansions).
-/

open MeasureTheory Polynomial Set

namespace Polynomial

/-! ### The Legendre coefficients of a polynomial -/

/-- **The `k`-th Legendre coefficient** `p̂_k = ((2k + 1)/2) ∫_{-1}^1 p L_k` of a polynomial, so
that `p = ∑_{k ≤ N} p̂_k L_k` for `p ∈ ℙ_N` (`Polynomial.eq_sum_legendreCoeff`). -/
noncomputable def legendreCoeff (p : ℝ[X]) (k : ℕ) : ℝ :=
  (2 * k + 1) / 2 * ∫ t in (-1 : ℝ)..1, p.eval t * (legendre k).eval t

/-- The Legendre coefficients are linear in the polynomial. -/
theorem legendreCoeff_add (p q : ℝ[X]) (k : ℕ) :
    legendreCoeff (p + q) k = legendreCoeff p k + legendreCoeff q k := by
  simp only [legendreCoeff, eval_add, add_mul]
  rw [intervalIntegral.integral_add]
  · ring
  · exact ((Polynomial.continuous p).mul (Polynomial.continuous _)).intervalIntegrable _ _
  · exact ((Polynomial.continuous q).mul (Polynomial.continuous _)).intervalIntegrable _ _

/-- The Legendre coefficients are linear in the polynomial. -/
theorem legendreCoeff_C_mul (c : ℝ) (p : ℝ[X]) (k : ℕ) :
    legendreCoeff (C c * p) k = c * legendreCoeff p k := by
  simp only [legendreCoeff, eval_mul, eval_C, mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- The Legendre coefficients are linear in the polynomial. -/
theorem legendreCoeff_sum {ι : Type*} (s : Finset ι) (p : ι → ℝ[X]) (k : ℕ) :
    legendreCoeff (∑ i ∈ s, p i) k = ∑ i ∈ s, legendreCoeff (p i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [legendreCoeff]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, legendreCoeff_add, ih]

/-- `L_j` has Legendre coefficients `δ_{jk}`: the orthogonality `∫ L_j L_k = (2/(2k+1)) δ_{jk}`. -/
theorem legendreCoeff_legendre (j k : ℕ) :
    legendreCoeff (legendre j) k = if j = k then 1 else 0 := by
  rw [legendreCoeff, integral_legendre_mul_legendre]
  split_ifs with h
  · field_simp
  · simp

/-- A polynomial of degree less than `k` has vanishing `k`-th Legendre coefficient. -/
theorem legendreCoeff_eq_zero_of_natDegree_lt {p : ℝ[X]} {k : ℕ} (hp : p.natDegree < k) :
    legendreCoeff p k = 0 := by
  have h := OrthogonalPolynomial.integral_legendre_mul_of_degree_lt
    (n := k) (p := p) ((degree_lt_iff_coeff_zero p k).mpr fun m hm =>
      coeff_eq_zero_of_natDegree_lt (hp.trans_le hm))
  rw [OrthogonalPolynomial.integral_legendreMeasure] at h
  rw [legendreCoeff, intervalIntegral.integral_congr (fun t _ => mul_comm (p.eval t) _), h,
    mul_zero]

/-- **The Legendre expansion of a polynomial**: `p = ∑_{k ≤ N} p̂_k L_k` for `p ∈ ℙ_N`. The
Legendre polynomials `L_0, …, L_N` span `ℙ_N` (`OrthogonalPolynomial.exists_eq_sum_family`), and
the coefficients of any such expansion are read off by orthogonality. -/
theorem eq_sum_legendreCoeff {N : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ N) :
    p = ∑ k ∈ Finset.range (N + 1), C (legendreCoeff p k) * legendre k := by
  obtain ⟨c, hc⟩ := OrthogonalPolynomial.exists_eq_sum_family OrthogonalPolynomial.legendreMeasure
    (n := N + 1) (q := p)
    (degree_le_of_natDegree_le hp |>.trans_lt (by exact_mod_cast N.lt_succ_self))
  have hexp : p = ∑ k ∈ Finset.range (N + 1),
      C (c k * ((legendre k).leadingCoeff)⁻¹) * legendre k := by
    rw [hc]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [OrthogonalPolynomial.family_eq_legendre, smul_eq_C_mul, ← mul_assoc, ← C_mul]
  have hcoeff : ∀ k ∈ Finset.range (N + 1),
      legendreCoeff p k = c k * ((legendre k).leadingCoeff)⁻¹ := by
    intro k hk
    conv_lhs => rw [hexp]
    rw [legendreCoeff_sum, Finset.sum_eq_single k]
    · rw [legendreCoeff_C_mul, legendreCoeff_legendre, ite_eq_left rfl, mul_one]
    · intro j _ hjk
      rw [legendreCoeff_C_mul, legendreCoeff_legendre, ite_eq_right hjk, mul_zero]
    · intro h; exact absurd hk h
  conv_lhs => rw [hexp]
  exact Finset.sum_congr rfl fun k hk => by rw [hcoeff k hk]

/-- **Parseval's identity for the Legendre expansion**: for `p ∈ ℙ_N`,
`∫_{-1}^1 p² = ∑_{k ≤ N} p̂_k² · 2/(2k + 1)`. -/
theorem integral_sq_eq_sum_legendreCoeff {N : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ N) :
    ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 =
      ∑ k ∈ Finset.range (N + 1), legendreCoeff p k ^ 2 * (2 / (2 * k + 1)) := by
  have hint : ∀ q r : ℝ[X], IntervalIntegrable (fun t => q.eval t * r.eval t) volume (-1) 1 :=
    fun q r => ((Polynomial.continuous q).mul (Polynomial.continuous r)).intervalIntegrable _ _
  have hsq : ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 = ∫ t in (-1 : ℝ)..1, p.eval t * p.eval t :=
    intervalIntegral.integral_congr fun t _ => sq _
  rw [hsq]
  have hexp := eq_sum_legendreCoeff hp
  have hev : ∀ t, p.eval t * p.eval t = ∑ k ∈ Finset.range (N + 1),
        legendreCoeff p k * (p.eval t * (legendre k).eval t) := by
    intro t
    calc p.eval t * p.eval t
        = (∑ k ∈ Finset.range (N + 1), C (legendreCoeff p k) * legendre k).eval t * p.eval t := by
          rw [← hexp]
      _ = _ := by
          rw [eval_finsetSum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by rw [eval_mul, eval_C]; ring
  simp only [hev]
  rw [intervalIntegral.integral_finsetSum fun k _ => (hint p (legendre k)).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul]
  have h2k : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  have : ∫ t in (-1 : ℝ)..1, p.eval t * (legendre k).eval t =
      legendreCoeff p k * (2 / (2 * k + 1)) := by
    rw [legendreCoeff]
    field_simp
  rw [this]
  ring

/-! ### The derivatives of the Legendre polynomials at the endpoints -/

/-- **`L_n'(1) = n(n + 1)/2`**, from `L_{n+1}' = x L_n' + (n + 1) L_n` at `x = 1`. -/
theorem eval_one_derivative_legendre (n : ℕ) :
    (derivative (legendre n)).eval 1 = (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero => simp [legendre_zero]
  | succ k ih =>
    rw [derivative_legendre_succ, eval_add, eval_mul, eval_X, ih, eval_mul, eval_add,
      eval_natCast, eval_one, legendre_eval_one]
    push_cast
    ring

/-- **`L_n'(-1) = (-1)^{n+1} n(n + 1)/2`**, from `L_{n+1}' = x L_n' + (n + 1) L_n` at `x = -1`. -/
theorem eval_neg_one_derivative_legendre (n : ℕ) :
    (derivative (legendre n)).eval (-1) = (-1) ^ (n + 1) * ((n : ℝ) * (n + 1) / 2) := by
  induction n with
  | zero => simp [legendre_zero]
  | succ k ih =>
    rw [derivative_legendre_succ, eval_add, eval_mul, eval_X, ih, eval_mul, eval_add,
      eval_natCast, eval_one, legendre_eval_neg_one]
    push_cast
    ring

/-- **`∫_{-1}^1 L_k' L_j = 1 - (-1)^{k+j}` for `j < k`, and `0` for `k ≤ j`**: integrating by
parts, `∫ L_k' L_j = [L_k L_j]_{-1}^1 - ∫ L_k L_j'`, and the last integral vanishes for `j < k`
because `L_j'` has degree less than `k`; for `k ≤ j` it is `L_k'` that has degree less than `j`.
This is the identity behind the expansion `L_k' = ∑_{j < k, k - j odd} (2j + 1) L_j`. -/
theorem integral_derivative_legendre_mul_legendre (k j : ℕ) :
    ∫ t in (-1 : ℝ)..1, (derivative (legendre k)).eval t * (legendre j).eval t =
      if j < k then 1 - (-1) ^ (k + j) else 0 := by
  -- orthogonality of `L_m` to derivatives of lower index
  have horth : ∀ a b : ℕ, a ≤ b →
      ∫ t in (-1 : ℝ)..1, (derivative (legendre a)).eval t * (legendre b).eval t = 0 := by
    intro a b hab
    have hdeg : (derivative (legendre a)).degree < b := by
      refine (degree_derivative_lt (legendre_ne_zero a)).trans_le ?_
      rw [degree_legendre]
      exact_mod_cast hab
    have h := OrthogonalPolynomial.integral_legendre_mul_of_degree_lt hdeg
    rw [OrthogonalPolynomial.integral_legendreMeasure] at h
    rw [← h]
    exact intervalIntegral.integral_congr fun t _ => mul_comm _ _
  split_ifs with hjk
  · have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun t => (legendre j).eval t) (u' := fun t => (derivative (legendre j)).eval t)
      (v := fun t => (legendre k).eval t) (v' := fun t => (derivative (legendre k)).eval t)
      (a := (-1 : ℝ)) (b := 1) (fun t _ => (legendre j).hasDerivAt t)
      (fun t _ => (legendre k).hasDerivAt t)
      ((Polynomial.continuous _).intervalIntegrable _ _)
      ((Polynomial.continuous _).intervalIntegrable _ _)
    rw [horth j k hjk.le, sub_zero, legendre_eval_one, legendre_eval_one, legendre_eval_neg_one,
      legendre_eval_neg_one] at hibp
    rw [intervalIntegral.integral_congr (fun t _ => mul_comm ((derivative (legendre k)).eval t) _),
      hibp, pow_add]
    ring
  · exact horth k j (not_lt.mp hjk)

/-- The Legendre coefficients of `L_k'` are bounded by `2j + 1`. -/
theorem abs_legendreCoeff_derivative_legendre_le (k j : ℕ) :
    |legendreCoeff (derivative (legendre k)) j| ≤ 2 * j + 1 := by
  rw [legendreCoeff, integral_derivative_legendre_mul_legendre, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * j + 1) / 2)]
  have hb : |(if j < k then (1 : ℝ) - (-1) ^ (k + j) else 0)| ≤ 2 := by
    split_ifs
    · rcases neg_one_pow_eq_or ℝ (k + j) with h | h <;> rw [h] <;> norm_num
    · simp
  calc (2 * (j : ℝ) + 1) / 2 * |if j < k then (1 : ℝ) - (-1) ^ (k + j) else 0|
      ≤ (2 * (j : ℝ) + 1) / 2 * 2 := by gcongr
    _ = 2 * j + 1 := by ring

/-! ### The `L²` Markov inequality -/

/-- The Legendre coefficients of `p'` are controlled by those of `p`:
`|(p')^_j| ≤ (2j + 1) ∑_{k ≤ N} |p̂_k|` for `p ∈ ℙ_N`, since `p' = ∑_k p̂_k L_k'` and every
`|(L_k')^_j| ≤ 2j + 1`. -/
theorem abs_legendreCoeff_derivative_le {N : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ N) (j : ℕ) :
    |legendreCoeff (derivative p) j| ≤
      (2 * j + 1) * ∑ k ∈ Finset.range (N + 1), |legendreCoeff p k| := by
  have hder : derivative p = ∑ k ∈ Finset.range (N + 1),
      C (legendreCoeff p k) * derivative (legendre k) := by
    conv_lhs => rw [eq_sum_legendreCoeff hp]
    rw [derivative_sum]
    exact Finset.sum_congr rfl fun k _ => derivative_C_mul _ _
  rw [hder, legendreCoeff_sum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [legendreCoeff_C_mul, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_legendreCoeff_derivative_legendre_le k j) (abs_nonneg _)

/-- `∑_{k ≤ N} (2k + 1) = (N + 1)²`. -/
theorem sum_range_two_mul_add_one (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (2 * (k : ℝ) + 1) = ((N : ℝ) + 1) ^ 2 := by
  induction N with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- **Cauchy–Schwarz for the Legendre coefficients**: `(∑_{k ≤ N} |p̂_k|)² ≤ ((N + 1)²/2) ∫ p²`
for `p ∈ ℙ_N`, from `|p̂_k|² = ((2k + 1)/2) · (p̂_k² · 2/(2k + 1))` and Parseval. -/
theorem sq_sum_abs_legendreCoeff_le {N : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ N) :
    (∑ k ∈ Finset.range (N + 1), |legendreCoeff p k|) ^ 2 ≤
      ((N : ℝ) + 1) ^ 2 / 2 * ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range (N + 1))
    (r := fun k => |legendreCoeff p k|) (f := fun k => (2 * (k : ℝ) + 1) / 2)
    (g := fun k => legendreCoeff p k ^ 2 * (2 / (2 * k + 1)))
    (fun k _ => by positivity) (fun k _ => by positivity)
    (fun k _ => le_of_eq (by
      have h2k : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
      rw [sq_abs]
      field_simp))
  rw [integral_sq_eq_sum_legendreCoeff hp]
  refine hcs.trans (le_of_eq ?_)
  rw [← Finset.sum_div, sum_range_two_mul_add_one]

/-- **The `L²` Markov inequality on `[-1, 1]`**: for a polynomial `p` of degree at most `N`,
`∫_{-1}^1 (p')² ≤ (N (N + 1))² ∫_{-1}^1 p²`, i.e. `‖p'‖_{L²(-1,1)} ≤ N (N + 1) ‖p‖_{L²(-1,1)}`.
Expand `p = ∑_{k ≤ N} p̂_k L_k`; then `p' ∈ ℙ_{N-1}` has Legendre coefficients
`|(p')^_j| ≤ (2j + 1) ∑_k |p̂_k|` (`Polynomial.abs_legendreCoeff_derivative_le`), Parseval gives
`∫ (p')² = ∑_{j < N} (p')^_j² · 2/(2j + 1) ≤ 2 (∑_{j < N} (2j + 1)) (∑_k |p̂_k|)²`, and
Cauchy–Schwarz `(∑_k |p̂_k|)² ≤ ((N + 1)²/2) ∫ p²` with `∑_{j < N} (2j + 1) = N²` finish. The
constant is not the sharp one, which is of the same order `N²`
(`Polynomial.integral_derivative_derivative_legendre_sq_ge`).

Reference: [quarteroni2000numerical] §13.3.1, the `O(N⁴)` growth of the spectral stiffness
eigenvalues; Canuto–Hussaini–Quarteroni–Zang, *Spectral Methods in Fluid Dynamics*, §9.4. -/
theorem integral_derivative_sq_le {N : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ N) :
    ∫ t in (-1 : ℝ)..1, (derivative p).eval t ^ 2 ≤
      ((N : ℝ) * (N + 1)) ^ 2 * ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 := by
  have hpN : (0 : ℝ) ≤ ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · -- a constant has zero derivative
    have hc : derivative p = 0 := by
      rw [eq_C_of_natDegree_le_zero hp, derivative_C]
    rw [hc]
    simp only [eval_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      intervalIntegral.integral_zero]
    positivity
  have hderdeg : (derivative p).natDegree ≤ N - 1 :=
    (natDegree_derivative_le p).trans (Nat.sub_le_sub_right hp 1)
  set S := ∑ k ∈ Finset.range (N + 1), |legendreCoeff p k| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hSsq := sq_sum_abs_legendreCoeff_le hp
  rw [← hS] at hSsq
  -- Parseval for `p'`, term by term
  rw [integral_sq_eq_sum_legendreCoeff hderdeg]
  have hterm : ∀ j ∈ Finset.range (N - 1 + 1),
      legendreCoeff (derivative p) j ^ 2 * (2 / (2 * (j : ℝ) + 1)) ≤
        2 * (2 * (j : ℝ) + 1) * S ^ 2 := by
    intro j _
    have h := abs_legendreCoeff_derivative_le hp j
    rw [← hS] at h
    have h2 : legendreCoeff (derivative p) j ^ 2 ≤ ((2 * (j : ℝ) + 1) * S) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have h2j : (0 : ℝ) < 2 * (j : ℝ) + 1 := by positivity
    calc legendreCoeff (derivative p) j ^ 2 * (2 / (2 * (j : ℝ) + 1))
        ≤ ((2 * (j : ℝ) + 1) * S) ^ 2 * (2 / (2 * (j : ℝ) + 1)) := by gcongr
      _ = 2 * (2 * (j : ℝ) + 1) * S ^ 2 := by field_simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  -- `∑_{j < N} (2j + 1) = N²`
  have hsum : ∑ j ∈ Finset.range (N - 1 + 1), (2 * (j : ℝ) + 1) ≤ (N : ℝ) ^ 2 := by
    rw [sum_range_two_mul_add_one, Nat.cast_sub hNpos]
    push_cast
    ring_nf
    exact le_rfl
  calc 2 * (∑ j ∈ Finset.range (N - 1 + 1), (2 * (j : ℝ) + 1)) * S ^ 2
      ≤ 2 * (N : ℝ) ^ 2 * (((N : ℝ) + 1) ^ 2 / 2 * ∫ t in (-1 : ℝ)..1, p.eval t ^ 2) := by
        gcongr
    _ = ((N : ℝ) * (N + 1)) ^ 2 * ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 := by ring

/-- **The `L²` Markov inequality, norm form**: `‖p'‖_{L²(-1,1)} ≤ N (N + 1) ‖p‖_{L²(-1,1)}` for
`p ∈ ℙ_N`. -/
theorem sqrt_integral_derivative_sq_le {N : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ N) :
    Real.sqrt (∫ t in (-1 : ℝ)..1, (derivative p).eval t ^ 2) ≤
      (N : ℝ) * (N + 1) * Real.sqrt (∫ t in (-1 : ℝ)..1, p.eval t ^ 2) := by
  have h := integral_derivative_sq_le hp
  calc Real.sqrt (∫ t in (-1 : ℝ)..1, (derivative p).eval t ^ 2)
      ≤ Real.sqrt (((N : ℝ) * (N + 1)) ^ 2 * ∫ t in (-1 : ℝ)..1, p.eval t ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = (N : ℝ) * (N + 1) * Real.sqrt (∫ t in (-1 : ℝ)..1, p.eval t ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

end Polynomial

/-- **Cauchy–Schwarz for interval integrals** of continuous functions:
`(∫_a^b f g)² ≤ (∫_a^b f²)(∫_a^b g²)`, from the nonnegativity of `∫ (λ f + g)²` and the sign of
its discriminant. -/
theorem intervalIntegral.sq_integral_mul_le_of_continuousOn {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b)) :
    (∫ t in a..b, f t * g t) ^ 2 ≤ (∫ t in a..b, f t ^ 2) * ∫ t in a..b, g t ^ 2 := by
  have hff : IntervalIntegrable (fun t => f t ^ 2) volume a b :=
    (hf.pow 2).intervalIntegrable_of_Icc hab
  have hgg : IntervalIntegrable (fun t => g t ^ 2) volume a b :=
    (hg.pow 2).intervalIntegrable_of_Icc hab
  have hfg : IntervalIntegrable (fun t => f t * g t) volume a b :=
    (hf.mul hg).intervalIntegrable_of_Icc hab
  have hexp : ∀ l : ℝ, (∫ t in a..b, (l * f t + g t) ^ 2)
      = (∫ t in a..b, f t ^ 2) * (l * l) + 2 * (∫ t in a..b, f t * g t) * l
        + ∫ t in a..b, g t ^ 2 := by
    intro l
    have hcongr : ∀ t ∈ uIcc a b, (l * f t + g t) ^ 2
        = l ^ 2 * f t ^ 2 + (2 * l) * (f t * g t) + g t ^ 2 := fun t _ => by ring
    rw [integral_congr hcongr, integral_add ((hff.const_mul _).add (hfg.const_mul _)) hgg,
      integral_add (hff.const_mul _) (hfg.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  have hnn : ∀ l : ℝ, 0 ≤ (∫ t in a..b, f t ^ 2) * (l * l)
      + 2 * (∫ t in a..b, f t * g t) * l + ∫ t in a..b, g t ^ 2 := by
    intro l
    rw [← hexp l]
    exact integral_nonneg hab fun t _ => sq_nonneg _
  have hd := discrim_le_zero hnn
  rw [discrim] at hd
  nlinarith [hd]

namespace Polynomial

/-! ### Sharpness: the test polynomial `L_N'` -/

/-- `∫_{-1}^1 L_n L_n'' = 0`: the second derivative has lower degree. -/
theorem integral_legendre_mul_derivative_derivative (n : ℕ) :
    ∫ t in (-1 : ℝ)..1,
      (legendre n).eval t * (derivative (derivative (legendre n))).eval t = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [legendre_zero]
  have hdeg : (derivative (derivative (legendre n))).degree < n := by
    refine (degree_le_of_natDegree_le ((natDegree_derivative_le _).trans
      (Nat.sub_le_sub_right (natDegree_derivative_le _) 1))).trans_lt ?_
    rw [natDegree_legendre]
    exact_mod_cast (by omega : n - 1 - 1 < n)
  have h := OrthogonalPolynomial.integral_legendre_mul_of_degree_lt hdeg
  rwa [OrthogonalPolynomial.integral_legendreMeasure] at h

/-- **`‖L_n'‖²_{L²(-1,1)} = n(n + 1)`**: by parts, `∫ (L_n')² = [L_n' L_n]_{-1}^1 - ∫ L_n'' L_n`,
the last integral vanishing by orthogonality, and `L_n'(±1) L_n(±1) = ±n(n + 1)/2`. -/
theorem integral_derivative_legendre_sq (n : ℕ) :
    ∫ t in (-1 : ℝ)..1, (derivative (legendre n)).eval t ^ 2 = (n : ℝ) * (n + 1) := by
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t => (derivative (legendre n)).eval t)
    (u' := fun t => (derivative (derivative (legendre n))).eval t)
    (v := fun t => (legendre n).eval t) (v' := fun t => (derivative (legendre n)).eval t)
    (a := (-1 : ℝ)) (b := 1) (fun t _ => (derivative (legendre n)).hasDerivAt t)
    (fun t _ => (legendre n).hasDerivAt t)
    ((Polynomial.continuous _).intervalIntegrable _ _)
    ((Polynomial.continuous _).intervalIntegrable _ _)
  have horth : ∫ t in (-1 : ℝ)..1,
      (derivative (derivative (legendre n))).eval t * (legendre n).eval t = 0 := by
    rw [← integral_legendre_mul_derivative_derivative n]
    exact intervalIntegral.integral_congr fun t _ => mul_comm _ _
  rw [horth, sub_zero, eval_one_derivative_legendre, eval_neg_one_derivative_legendre,
    legendre_eval_one, legendre_eval_neg_one] at hibp
  rw [intervalIntegral.integral_congr (fun t _ => sq ((derivative (legendre n)).eval t)), hibp,
    pow_succ]
  have h1 : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  linear_combination ((n : ℝ) * (n + 1) / 2) * h1

/-- **`∫_{-1}^1 x L_n' L_n'' = (n(n + 1)/2)² - n(n + 1)/2`**:
`(x (L_n')²)' = (L_n')² + 2x L_n' L_n''`, so `2 ∫ x L_n' L_n'' = L_n'(1)² + L_n'(-1)² - ‖L_n'‖²`. -/
theorem integral_X_mul_derivative_legendre_mul_derivative_derivative (n : ℕ) :
    ∫ t in (-1 : ℝ)..1, t * (derivative (legendre n)).eval t *
        (derivative (derivative (legendre n))).eval t =
      ((n : ℝ) * (n + 1) / 2) ^ 2 - (n : ℝ) * (n + 1) / 2 := by
  set L' := fun t => (derivative (legendre n)).eval t with hL'
  set L'' := fun t => (derivative (derivative (legendre n))).eval t with hL''
  have hderiv : ∀ t, HasDerivAt (fun t => t * L' t ^ 2) (L' t ^ 2 + 2 * t * L' t * L'' t) t := by
    intro t
    have h1 : HasDerivAt (fun t => L' t ^ 2) (2 * L' t * L'' t) t := by
      have := ((derivative (legendre n)).hasDerivAt t).fun_pow 2
      simpa [hL', hL'', mul_comm, mul_assoc, mul_left_comm] using this
    have := (hasDerivAt_id t).fun_mul h1
    simpa [id, mul_comm, mul_assoc, mul_left_comm] using this
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (-1 : ℝ)) (b := 1)
    (fun t _ => hderiv t) (by
      have : Continuous fun t => L' t ^ 2 + 2 * t * L' t * L'' t := by
        simp only [hL', hL'']; fun_prop
      exact this.intervalIntegrable _ _)
  have hsq := integral_derivative_legendre_sq n
  have hsplit : ∫ t in (-1 : ℝ)..1, (L' t ^ 2 + 2 * t * L' t * L'' t) =
      (∫ t in (-1 : ℝ)..1, L' t ^ 2) + 2 * ∫ t in (-1 : ℝ)..1, t * L' t * L'' t := by
    rw [intervalIntegral.integral_add, ← intervalIntegral.integral_const_mul]
    · exact congrArg _ (intervalIntegral.integral_congr fun t _ => by ring)
    · exact ((Polynomial.continuous _).pow 2).intervalIntegrable _ _
    · have : Continuous fun t => 2 * t * L' t * L'' t := by simp only [hL', hL'']; fun_prop
      exact this.intervalIntegrable _ _
  simp only [hL', hL''] at hsplit hsq
  rw [hsplit, hsq] at hftc
  simp only [hL', eval_one_derivative_legendre, eval_neg_one_derivative_legendre] at hftc
  have hpow : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have : ∫ t in (-1 : ℝ)..1, t * (derivative (legendre n)).eval t *
      (derivative (derivative (legendre n))).eval t =
      (((n : ℝ) * (n + 1) / 2) ^ 2 + (-1 * ((-1) ^ (n + 1) * ((n : ℝ) * (n + 1) / 2)) ^ 2 * (-1))
        - (n : ℝ) * (n + 1)) / 2 := by
    linarith
  rw [this, mul_pow, hpow]
  ring

/-- **The `L²` Markov inequality is sharp up to a constant**: for `N ≥ 2` the test polynomial
`L_N' ∈ ℙ_{N-1}` has `‖L_N''‖² ≥ ((N(N + 1))²/36) ‖L_N'‖²`, so the growth `N²` of
`Polynomial.integral_derivative_sq_le` cannot be improved. Cauchy–Schwarz against `x L_N'` gives
`(∫ x L_N' L_N'')² ≤ ‖x L_N'‖² ‖L_N''‖² ≤ ‖L_N'‖² ‖L_N''‖²` with
`∫ x L_N' L_N'' = m(m - 2)/4 ≥ m²/6` for `m = N(N + 1) ≥ 6` and `‖L_N'‖² = m`. -/
theorem integral_derivative_derivative_legendre_sq_ge {N : ℕ} (hN : 2 ≤ N) :
    ((N : ℝ) * (N + 1)) ^ 2 / 36 * ∫ t in (-1 : ℝ)..1, (derivative (legendre N)).eval t ^ 2 ≤
      ∫ t in (-1 : ℝ)..1, (derivative (derivative (legendre N))).eval t ^ 2 := by
  set m : ℝ := (N : ℝ) * (N + 1) with hm
  have hm6 : 6 ≤ m := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    rw [hm]; nlinarith
  have hcs := intervalIntegral.sq_integral_mul_le_of_continuousOn (a := (-1 : ℝ)) (b := 1)
    (f := fun t => t * (derivative (legendre N)).eval t)
    (g := fun t => (derivative (derivative (legendre N))).eval t) (by norm_num)
    (continuous_id.mul (Polynomial.continuous _)).continuousOn
    (Polynomial.continuous _).continuousOn
  rw [integral_X_mul_derivative_legendre_mul_derivative_derivative, ← hm] at hcs
  -- `∫ (x L_N')² ≤ ∫ (L_N')²`
  have hxle : (∫ t in (-1 : ℝ)..1, (t * (derivative (legendre N)).eval t) ^ 2) ≤
      ∫ t in (-1 : ℝ)..1, (derivative (legendre N)).eval t ^ 2 := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((continuous_id.mul (Polynomial.continuous _)).pow 2 |>.intervalIntegrable _ _)
      (((Polynomial.continuous _).pow 2).intervalIntegrable _ _) fun t ht => ?_
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    rw [mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) ht2
  rw [integral_derivative_legendre_sq, ← hm] at hxle
  set E := ∫ t in (-1 : ℝ)..1, (derivative (derivative (legendre N))).eval t ^ 2 with hE
  have hE0 : 0 ≤ E := intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
  rw [integral_derivative_legendre_sq, ← hm]
  -- `(m²/4 - m/2)² ≤ m E`, and `m²/4 - m/2 ≥ m²/6`
  have hD : m ^ 2 / 6 ≤ (m / 2) ^ 2 - m / 2 := by nlinarith
  have hD2 : (m ^ 2 / 6) ^ 2 ≤ ((m / 2) ^ 2 - m / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hD 2
  have hkey : (m ^ 2 / 6) ^ 2 ≤ m * E :=
    hD2.trans (hcs.trans (mul_le_mul_of_nonneg_right hxle hE0))
  have hmpos : 0 < m := by linarith
  nlinarith [hkey, hmpos]

end Polynomial
