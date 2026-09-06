import Numlib.Analysis.Sobolev.Periodic

/-!
# Atkinson–Han §7.5: periodic Sobolev spaces

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §7.5.1–§7.5.3.

§7.5 is the one section of chapter 7 that needs no theory of Sobolev spaces on a domain.  The book
defines `H^s(2π)` by the decay of the Fourier coefficients: a formal series `φ = ∑_m a_m ψ_m` with
`ψ_m x = (2π)^{-1/2} e^{i m x}` belongs to it when

`‖φ‖²_{*,s} = |a₀|² + ∑_{|m| > 0} |m|^{2 s} |a_m|² < ∞`,

which is a weighted `ℓ²(ℤ, ℂ)` and nothing more.  That space is `PeriodicSobolev s` in the backbone,
and this module is the book's numbered statements about it.

## The normalization

The backbone reads a series against the *unnormalized* characters `periodicChar T m x =
exp (2 π i m x / T)`, whereas the book uses `ψ_m = (2π)^{-1/2} e^{i m x}`.  The two differ by the
constant `(2π)^{-1/2}`, which the norm `‖·‖_{*,s}` does not see — it is a norm on the coefficient
sequence — but which every statement about the *function* does.  `AtkinsonHan.Chapter07.eval`
carries that constant, so `eval φ` is the book's `φ(x)` on the nose, and the bounds below are the
book's with the book's constants.

## Main results

* `definition_7_5_1_norm`, `definition_7_5_1_inner` — (7.5.2) and the inner product that induces it.
* `theorem_7_5_2` — `H^s(2π)` is exactly the set of series (7.5.1) with `‖φ‖_{*,s} < ∞`.
* `theorem_7_5_2_norm_equiv` — for an integer `k ≥ 0` the norm `‖·‖_{*,k}` is equivalent to the
  classical `‖φ‖²_{H^k} = ∑_{j ≤ k} ‖φ^{(j)}‖²_{L²}`, with the constants `1` and `k + 1`.
* `proposition_7_5_4`, `proposition_7_5_4_bound` — the Sobolev embedding for `s > 1/2`: the series
  converges to a continuous `2π`-periodic function, with (7.5.10) and (7.5.11).
* `proposition_7_5_5` — for `s > t` the space `H^s(2π)` is dense in `H^t(2π)` and the inclusion is
  compact.  This is also Exercise 7.5.1, which asks for its proof.
* `proposition_7_5_6` — **the trapezoidal rule is exponentially accurate on smooth periodic
  integrands**: `|I(φ) − T_k(φ)| ≤ √(4 π ζ(2 s)) k^{-s} ‖φ‖_{*,s}`, the bound (7.5.13).
* `exercise_7_5_2` — the trigonometric polynomials `𝕋` of (7.5.4) are dense in `H^s(2π)` for every
  real `s`.
* `exercise_7_5_3` — Simpson's rule obeys the same bound, with the constant `(5/3) √(4 π ζ(2 s))`.
  The proof is that `S_{2k} = (4 T_{2k} − T_k)/3` on any function, so the two trapezoidal bounds
  combine.
* `exercise_7_5_4` — every element of `H^{-t}(2π)` is a bounded linear functional on `H^t(2π)`
  under the pairing (7.5.6), with `‖ℓ‖ ≤ ‖η‖_{*,-t}`.

## Not formalized here

* **(7.5.3)–(7.5.5), the distributional derivative `𝒟`.**  Its coefficient description `𝒟 φ =
  i ∑ m a_m ψ_m` is what `theorem_7_5_2_norm_equiv` uses, in the form of the classical norm written
  on the Fourier side; the operator itself, its norm `1` and its unique extension from `𝕋` are not
  built, because nothing else here consumes them.
* **Example 7.5.3**, the square wave and its Dirac comb: this needs distributions on the circle,
  and Mathlib's `TemperedDistribution` lives on `ℝ^d` only.
* **Theorem 7.5.7**, the trigonometric interpolation bound: the project has no trigonometric
  interpolation operator `𝓘_n` — `Numlib/Analysis/Fourier/TrigonometricBasis` builds the Fourier
  projection `𝓕_n` and the target subspace `trigPolyLE (2π) n`, but not the interpolant — and the
  book quotes the bound from Kress without proof.
* **§7.5.4**, the logarithmic-kernel operator `𝒜` of (7.5.16): the book obtains its symbol
  `a_m/|m|` from complex function theory that it does not reproduce.
* **§7.5.5**, spherical polynomials, spherical harmonics and the Laplace expansion (7.5.8)–(7.5.10)
  and (7.5.19)–(7.5.34): Mathlib has no spherical harmonics, and Theorem 7.5.10 is quoted from
  Ragozin without proof.

## References

[han2009theoretical] §7.5.
-/

open Filter Metric Set Topology
open scoped ComplexConjugate ENNReal InnerProductSpace Real

namespace AtkinsonHan.Chapter07

/-! ### The normalization constant -/

/-- `1 ≤ √(2 π)`, so the book's `ψ_m` are bounded by `1` and the bounds below can be read either
with or without the normalization. -/
theorem one_le_sqrt_two_pi : (1 : ℝ) ≤ √(2 * π) := by
  rw [show (1 : ℝ) = √1 by simp]
  exact Real.sqrt_le_sqrt (by nlinarith [Real.two_le_pi])

theorem sqrt_two_pi_pos : 0 < √(2 * π) := by linarith [one_le_sqrt_two_pi]

theorem inv_sqrt_two_pi_le_one : (√(2 * π))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ one_le_sqrt_two_pi

/-- The book's orthonormal system `ψ_m x = (2 π)^{-1/2} e^{i m x}`. -/
noncomputable def psi (m : ℤ) (x : ℝ) : ℂ := (√(2 * π))⁻¹ * periodicChar (2 * π) m x

@[simp]
theorem norm_psi (m : ℤ) (x : ℝ) : ‖psi m x‖ = (√(2 * π))⁻¹ := by
  rw [psi, norm_mul, norm_periodicChar, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

variable {s t : ℝ}

/-- The sum of the book's series (7.5.1), `φ(x) = ∑_m a_m ψ_m(x)`. -/
noncomputable def eval (φ : PeriodicSobolev s) (x : ℝ) : ℂ :=
  (√(2 * π))⁻¹ * PeriodicSobolev.eval (2 * π) φ x

/-- `eval` is the book's series (7.5.1) against the book's orthonormal system. -/
theorem eval_eq_tsum (φ : PeriodicSobolev s) (x : ℝ) :
    eval φ x = ∑' m : ℤ, φ.coeff m * psi m x := by
  rw [eval, PeriodicSobolev.eval, ← tsum_mul_left]
  exact tsum_congr fun m => by rw [psi]; ring

/-! ### Definition 7.5.1 and Theorem 7.5.2 -/

/-- **Definition 7.5.1, the norm (7.5.2)**: `‖φ‖²_{*,s} = |a₀|² + ∑_{|m| > 0} |m|^{2 s} |a_m|²`. -/
theorem definition_7_5_1_norm (s : ℝ) (φ : PeriodicSobolev s) :
    HasSum (fun m : ℤ => if m = 0 then ‖φ.coeff 0‖ ^ 2
      else |(m : ℝ)| ^ (2 * s) * ‖φ.coeff m‖ ^ 2) (‖φ‖ ^ 2) := by
  refine (PeriodicSobolev.hasSum_norm_sq φ).congr_fun fun m => ?_
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [ite_eq_right hm, mul_pow, periodicSobolevWeight_sq s hm]

/-- **Definition 7.5.1, the inner product**: `(φ, ρ)_{*,s} = a₀ conj b₀ +
∑_{|m| > 0} |m|^{2 s} a_m conj b_m`. Mathlib's inner product is conjugate-linear in its *first*
argument, the opposite of the book's convention, so the book's `(φ, ρ)_{*,s}` is `⟪ρ, φ⟫`. -/
theorem definition_7_5_1_inner (s : ℝ) (φ ρ : PeriodicSobolev s) :
    (inner ℂ ρ φ : ℂ) = ∑' m : ℤ, (if m = 0 then φ.coeff 0 * conj (ρ.coeff 0)
      else (|(m : ℝ)| ^ (2 * s) : ℝ) * (φ.coeff m * conj (ρ.coeff m))) := by
  rw [PeriodicSobolev.inner_eq_tsum]
  refine tsum_congr fun m => ?_
  rcases eq_or_ne m 0 with rfl | hm
  · simp [mul_comm]
  · rw [ite_eq_right hm, ← Complex.ofReal_pow, periodicSobolevWeight_sq s hm]
    ring

/-- **Theorem 7.5.2, the characterization**: `H^s(2π)` is exactly the set of formal series (7.5.1)
whose coefficients make (7.5.2) finite. -/
theorem theorem_7_5_2 (s : ℝ) (a : ℤ → ℂ) :
    (∃ φ : PeriodicSobolev s, φ.coeff = a) ↔
      Summable fun m : ℤ => (periodicSobolevWeight s m * ‖a m‖) ^ 2 := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact (PeriodicSobolev.hasSum_norm_sq φ).summable
  · intro ha
    refine ⟨PeriodicSobolev.ofCoeff s a (memℓp_two_iff.2 (ha.congr fun m => ?_)),
      PeriodicSobolev.coeff_ofCoeff _ _ _⟩
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (periodicSobolevWeight_pos s m).le]

/-- The classical Sobolev norm of Definition 7.5.1, `‖φ‖²_{H^k} = ∑_{j ≤ k} ‖φ^{(j)}‖²_{L²}`,
written on the Fourier side.  Differentiation multiplies the `m`-th coefficient by `i m`, by
(7.5.3), and Parseval turns each `‖φ^{(j)}‖²_{L²}` into `∑_m |m|^{2 j} |a_m|²`; summing over
`j ≤ k` gives the expression below. -/
noncomputable def classicalNormSq (k : ℕ) (φ : PeriodicSobolev (k : ℝ)) : ℝ :=
  ∑' m : ℤ, (∑ j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * j)) * ‖φ.coeff m‖ ^ 2

/-- The symbol inequality behind the equivalence: `w_k(m)² ≤ ∑_{j ≤ k} |m|^{2 j} ≤ (k+1) w_k(m)²`,
where `w_k` is the weight of (7.5.2). -/
theorem weight_sq_le_sum_le (k : ℕ) (m : ℤ) :
    periodicSobolevWeight (k : ℝ) m ^ 2 ≤ ∑ j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * j) ∧
      ∑ j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * j)
        ≤ ((k : ℝ) + 1) * periodicSobolevWeight (k : ℝ) m ^ 2 := by
  rcases eq_or_ne m 0 with rfl | hm
  · have hone : ∑ j ∈ Finset.range (k + 1), |((0 : ℤ) : ℝ)| ^ (2 * j) = 1 := by
      rw [Finset.sum_eq_single 0]
      · norm_num
      · intro b _ hb
        have h2b : 2 * b ≠ 0 := by omega
        simp [h2b]
      · intro h
        exact absurd (Finset.mem_range.2 (Nat.succ_pos k)) h
    rw [hone, periodicSobolevWeight_zero, one_pow]
    exact ⟨le_rfl, by linarith [Nat.cast_nonneg (α := ℝ) k]⟩
  · have habs : (1 : ℝ) ≤ |(m : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast h1
        _ = |(m : ℝ)| := by rw [Int.cast_abs]
    have hw : periodicSobolevWeight (k : ℝ) m ^ 2 = |(m : ℝ)| ^ (2 * k) := by
      rw [periodicSobolevWeight_sq _ hm,
        show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have hmono : ∀ j ∈ Finset.range (k + 1),
        |(m : ℝ)| ^ (2 * j) ≤ |(m : ℝ)| ^ (2 * k) := by
      intro j hj
      rw [Finset.mem_range] at hj
      exact pow_le_pow_right₀ habs (by omega)
    rw [hw]
    constructor
    · exact Finset.single_le_sum (f := fun j => |(m : ℝ)| ^ (2 * j))
        (fun j _ => by positivity) (Finset.self_mem_range_succ k)
    · calc ∑ j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * j)
          ≤ ∑ _j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * k) := Finset.sum_le_sum hmono
        _ = ((k : ℝ) + 1) * |(m : ℝ)| ^ (2 * k) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring

/-- **Theorem 7.5.2, the norm equivalence** for an integer `k ≥ 0`: `‖·‖_{*,k}` and the classical
`‖·‖_{H^k}` are equivalent, with the constants `1` and `k + 1`. -/
theorem theorem_7_5_2_norm_equiv (k : ℕ) (φ : PeriodicSobolev (k : ℝ)) :
    ‖φ‖ ^ 2 ≤ classicalNormSq k φ ∧ classicalNormSq k φ ≤ ((k : ℝ) + 1) * ‖φ‖ ^ 2 := by
  have hns := PeriodicSobolev.hasSum_norm_sq φ
  have hterm : ∀ m : ℤ, (periodicSobolevWeight (k : ℝ) m * ‖φ.coeff m‖) ^ 2
      = periodicSobolevWeight (k : ℝ) m ^ 2 * ‖φ.coeff m‖ ^ 2 := fun m => by ring
  have hns' : HasSum (fun m : ℤ => periodicSobolevWeight (k : ℝ) m ^ 2 * ‖φ.coeff m‖ ^ 2)
      (‖φ‖ ^ 2) := hns.congr_fun fun m => (hterm m).symm
  have hupper : HasSum (fun m : ℤ => (((k : ℝ) + 1) * periodicSobolevWeight (k : ℝ) m ^ 2)
      * ‖φ.coeff m‖ ^ 2) (((k : ℝ) + 1) * ‖φ‖ ^ 2) :=
    (hns'.mul_left ((k : ℝ) + 1)).congr_fun fun m => by ring
  have hnn : ∀ m : ℤ, (0 : ℝ) ≤ (∑ j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * j))
      * ‖φ.coeff m‖ ^ 2 := fun m =>
    mul_nonneg (Finset.sum_nonneg fun j _ => by positivity) (by positivity)
  have hmid : Summable fun m : ℤ =>
      (∑ j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * j)) * ‖φ.coeff m‖ ^ 2 := by
    refine Summable.of_nonneg_of_le hnn (fun m => ?_) hupper.summable
    exact mul_le_mul_of_nonneg_right (weight_sq_le_sum_le k m).2 (by positivity)
  refine ⟨?_, ?_⟩
  · rw [classicalNormSq, ← hns'.tsum_eq]
    refine hns'.summable.tsum_le_tsum (fun m => ?_) hmid
    exact mul_le_mul_of_nonneg_right (weight_sq_le_sum_le k m).1 (by positivity)
  · rw [classicalNormSq, ← hupper.tsum_eq]
    refine hmid.tsum_le_tsum (fun m => ?_) hupper.summable
    exact mul_le_mul_of_nonneg_right (weight_sq_le_sum_le k m).2 (by positivity)

/-! ### §7.5.2, the embedding results -/

/-- **The bound (7.5.10)**: `|φ(x)| ≤ |a₀| + √(2 ζ(2 s)) ‖φ‖_{*,s}` for `s > 1/2`. -/
theorem proposition_7_5_4_bound (hs : 1 / 2 < s) (φ : PeriodicSobolev s) (x : ℝ) :
    ‖eval φ x‖ ≤ ‖φ.coeff 0‖ + √(2 * zetaReal (2 * s)) * ‖φ‖ := by
  have hb := PeriodicSobolev.norm_eval_le_tsum_norm_coeff hs (2 * π) φ x
  have hle := PeriodicSobolev.tsum_norm_coeff_le hs φ
  rw [eval, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h1 : (√(2 * π))⁻¹ * ‖PeriodicSobolev.eval (2 * π) φ x‖
      ≤ 1 * ‖PeriodicSobolev.eval (2 * π) φ x‖ :=
    mul_le_mul_of_nonneg_right inv_sqrt_two_pi_le_one (norm_nonneg _)
  rw [one_mul] at h1
  linarith [hb.trans hle]

/-- **Proposition 7.5.4 at `k = 0`, with the bound (7.5.11)**: for `s > 1/2` the series (7.5.1)
converges to a continuous function of period `2 π`, and `‖φ‖_∞ ≤ [1 + √(2 ζ(2 s))] ‖φ‖_{*,s}`. -/
theorem proposition_7_5_4 (hs : 1 / 2 < s) (φ : PeriodicSobolev s) :
    Continuous (eval φ) ∧ Function.Periodic (eval φ) (2 * π) ∧
      ∀ x, ‖eval φ x‖ ≤ (1 + √(2 * zetaReal (2 * s))) * ‖φ‖ := by
  refine ⟨continuous_const.mul (PeriodicSobolev.continuous_eval hs (2 * π) φ),
    fun x => by rw [eval, eval, PeriodicSobolev.eval_periodic (by positivity) φ x], fun x => ?_⟩
  rw [eval, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h1 : (√(2 * π))⁻¹ * ‖PeriodicSobolev.eval (2 * π) φ x‖
      ≤ 1 * ‖PeriodicSobolev.eval (2 * π) φ x‖ :=
    mul_le_mul_of_nonneg_right inv_sqrt_two_pi_le_one (norm_nonneg _)
  rw [one_mul] at h1
  linarith [PeriodicSobolev.norm_eval_le hs (2 * π) φ x]

/-- **Proposition 7.5.5** (= Exercise 7.5.1): for `s > t` the identity map `H^s(2π) → H^t(2π)` has
dense range and is a compact operator. -/
theorem proposition_7_5_5 (h : t < s) :
    DenseRange (PeriodicSobolev.inclL h.le) ∧
      IsCompactOperator (PeriodicSobolev.inclL h.le) :=
  ⟨PeriodicSobolev.denseRange_inclL h.le, PeriodicSobolev.isCompactOperator_inclL h⟩

/-- **Exercise 7.5.1** asks for the proof of Proposition 7.5.5. -/
theorem exercise_7_5_1 (h : t < s) :
    DenseRange (PeriodicSobolev.inclL h.le) ∧
      IsCompactOperator (PeriodicSobolev.inclL h.le) :=
  proposition_7_5_5 h

/-- **Exercise 7.5.2**: the trigonometric polynomials `𝕋` of (7.5.4) — the finite linear
combinations of the `ψ_m`, equivalently the span of the coordinate series — are dense in
`H^s(2π)` for every real `s`. -/
theorem exercise_7_5_2 (s : ℝ) :
    Dense ((Submodule.span ℂ (Set.range (PeriodicSobolev.basisElt s)) :
      Submodule ℂ (PeriodicSobolev s)) : Set (PeriodicSobolev s)) :=
  PeriodicSobolev.dense_span_basisElt s

/-! ### §7.5.3, the approximation results -/

/-- `I(φ) = ∫_0^{2π} φ(x) dx`. -/
noncomputable def integral (φ : PeriodicSobolev s) : ℂ := ∫ x in (0 : ℝ)..(2 * π), eval φ x

/-- **(7.5.12)**, the trapezoidal rule `T_k(φ) = h ∑_{j=1}^{k} φ(j h)` with `h = 2π/k`. -/
noncomputable def trapezoid (k : ℕ) (φ : PeriodicSobolev s) : ℂ :=
  PeriodicSobolev.trapezoidSum (2 * π) k (eval φ)

private theorem trapezoidSum_const_mul (T : ℝ) (k : ℕ) (c : ℂ) (f : ℝ → ℂ) :
    PeriodicSobolev.trapezoidSum T k (fun x => c * f x)
      = c * PeriodicSobolev.trapezoidSum T k f := by
  rw [PeriodicSobolev.trapezoidSum, PeriodicSobolev.trapezoidSum, ← Finset.mul_sum]
  ring

/-- The quadrature error in the book's normalization is `(2 π)^{-1/2}` times the backbone's. -/
theorem integral_sub_trapezoid (φ : PeriodicSobolev s) (k : ℕ) :
    integral φ - trapezoid k φ = (√(2 * π))⁻¹ *
      ((∫ x in (0 : ℝ)..(2 * π), PeriodicSobolev.eval (2 * π) φ x)
        - PeriodicSobolev.trapezoidSum (2 * π) k (PeriodicSobolev.eval (2 * π) φ)) := by
  have h1 : integral φ = (√(2 * π))⁻¹ * ∫ x in (0 : ℝ)..(2 * π),
      PeriodicSobolev.eval (2 * π) φ x := by
    rw [integral]
    simp only [eval]
    rw [intervalIntegral.integral_const_mul]
  have h2 : trapezoid k φ = (√(2 * π))⁻¹ *
      PeriodicSobolev.trapezoidSum (2 * π) k (PeriodicSobolev.eval (2 * π) φ) := by
    rw [trapezoid, show eval φ = fun x => (√(2 * π))⁻¹ *
      PeriodicSobolev.eval (2 * π) φ x from rfl, trapezoidSum_const_mul]
  rw [h1, h2, mul_sub]

/-- **Proposition 7.5.6, the bound (7.5.13)**: the trapezoidal rule converges at the rate `k^{-s}`
on `H^s(2π)`, so for a smooth periodic integrand it is spectrally accurate.

`|I(φ) − T_k(φ)| ≤ √(4 π ζ(2 s)) k^{-s} ‖φ‖_{*,s}`.

This is the reason the trapezoidal rule is the method of choice for periodic integrands. -/
theorem proposition_7_5_6 (hs : 1 / 2 < s) {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) :
    ‖integral φ - trapezoid k φ‖ ≤ √(4 * π * zetaReal (2 * s)) * (k : ℝ) ^ (-s) * ‖φ‖ := by
  have hbb := PeriodicSobolev.norm_intervalIntegral_sub_trapezoidSum_le hs
    (by positivity : (0 : ℝ) < 2 * π) hk φ
  have hsq : √(2 * π) * √(2 * π) = 2 * π := Real.mul_self_sqrt (by positivity)
  have h4 : √(4 * π * zetaReal (2 * s)) = √(2 * π) * √(2 * zetaReal (2 * s)) := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * π)]
    congr 1
    ring
  rw [integral_sub_trapezoid, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  refine le_trans (mul_le_mul_of_nonneg_left hbb (by positivity)) (le_of_eq ?_)
  calc (√(2 * π))⁻¹ * (2 * π * ((k : ℝ) ^ (-s) * √(2 * zetaReal (2 * s)) * ‖φ‖))
      = ((√(2 * π))⁻¹ * (√(2 * π) * √(2 * π)))
        * ((k : ℝ) ^ (-s) * √(2 * zetaReal (2 * s)) * ‖φ‖) := by rw [hsq]; ring
    _ = √(2 * π) * ((k : ℝ) ^ (-s) * √(2 * zetaReal (2 * s)) * ‖φ‖) := by
        rw [inv_mul_cancel_left₀ (ne_of_gt sqrt_two_pi_pos)]
    _ = √(4 * π * zetaReal (2 * s)) * (k : ℝ) ^ (-s) * ‖φ‖ := by rw [h4]; ring

/-- **Simpson's rule** on one period at `2 k` equally spaced points, `h = π / k`:
`S_{2k}(φ) = (h/3) [4 ∑_{j=1}^{k} φ(x_{2j-1}) + 2 ∑_{j=1}^{k} φ(x_{2j})]` with `x_i = i h`. For a
periodic integrand the two endpoints coincide, so the end weights `1` merge into the weight `2` at
`x_{2k}` and the rule is the plain alternating pattern below. -/
noncomputable def simpson (k : ℕ) (φ : PeriodicSobolev s) : ℂ :=
  ((π / k : ℝ) / 3 : ℝ) *
    (4 * ∑ j ∈ Finset.range k, eval φ ((2 * (j : ℝ) + 1) * (π / k))
      + 2 * ∑ j ∈ Finset.range k, eval φ ((2 * (j : ℝ) + 2) * (π / k)))

private theorem sum_range_two_mul (f : ℕ → ℂ) (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k), f i = ∑ j ∈ Finset.range k, (f (2 * j) + f (2 * j + 1)) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

/-- Simpson's rule on a period is the Richardson combination `(4 T_{2k} − T_k)/3` of the two
trapezoidal rules it refines. This identity holds for any function whatever; it is what turns the
trapezoidal bound (7.5.13) into the Simpson bound. -/
theorem simpson_eq (k : ℕ) (hk : 0 < k) (φ : PeriodicSobolev s) :
    simpson k φ = (4 * trapezoid (2 * k) φ - trapezoid k φ) / 3 := by
  have hkR : ((k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hstep2 : 2 * π / ((2 * k : ℕ) : ℝ) = π / (k : ℝ) := by push_cast; field_simp
  have hstep1 : 2 * π / ((k : ℕ) : ℝ) = 2 * (π / (k : ℝ)) := by ring
  have hT2 : trapezoid (2 * k) φ
      = ((π / (k : ℝ) : ℝ) : ℂ)
        * ∑ i ∈ Finset.range (2 * k), eval φ (((i : ℝ) + 1) * (π / (k : ℝ))) := by
    rw [trapezoid, PeriodicSobolev.trapezoidSum, hstep2]
  have hT1 : trapezoid k φ
      = ((2 * (π / (k : ℝ)) : ℝ) : ℂ)
        * ∑ j ∈ Finset.range k, eval φ ((2 * (j : ℝ) + 2) * (π / (k : ℝ))) := by
    rw [trapezoid, PeriodicSobolev.trapezoidSum, hstep1]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => congrArg (eval φ) (by ring))
  have hsplit : ∑ i ∈ Finset.range (2 * k), eval φ (((i : ℝ) + 1) * (π / (k : ℝ)))
      = (∑ j ∈ Finset.range k, eval φ ((2 * (j : ℝ) + 1) * (π / (k : ℝ))))
        + ∑ j ∈ Finset.range k, eval φ ((2 * (j : ℝ) + 2) * (π / (k : ℝ))) := by
    rw [sum_range_two_mul (fun i => eval φ (((i : ℝ) + 1) * (π / (k : ℝ)))) k,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ((2 * j : ℕ) : ℝ) + 1 = 2 * (j : ℝ) + 1 by push_cast; ring,
      show ((2 * j + 1 : ℕ) : ℝ) + 1 = 2 * (j : ℝ) + 2 by push_cast; ring]
  rw [simpson, hT2, hT1, hsplit]
  push_cast
  ring

/-- **Exercise 7.5.3**: Simpson's rule obeys the same `k^{-s}` bound as the trapezoidal rule, with
the constant `(5/3) √(4 π ζ(2 s))`. Since `S_{2k} = (4 T_{2k} − T_k)/3`, the error is
`(4 (I − T_{2k}) − (I − T_k))/3`, and `(2k)^{-s} ≤ k^{-s}`. -/
theorem exercise_7_5_3 (hs : 1 / 2 < s) {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) :
    ‖integral φ - simpson k φ‖ ≤ 5 / 3 * √(4 * π * zetaReal (2 * s)) * (k : ℝ) ^ (-s) * ‖φ‖ := by
  have hspos : (0 : ℝ) < s := by linarith
  have h2k : (0 : ℕ) < 2 * k := by omega
  have hb1 := proposition_7_5_6 hs hk φ
  have hb2 := proposition_7_5_6 hs h2k φ
  have hrate : ((2 * k : ℕ) : ℝ) ^ (-s) ≤ (k : ℝ) ^ (-s) := by
    have hkp : (0 : ℝ) < (k : ℝ) ^ s :=
      Real.rpow_pos_of_pos (by exact_mod_cast hk) s
    have hle : (k : ℝ) ^ s ≤ ((2 * k : ℕ) : ℝ) ^ s :=
      Real.rpow_le_rpow (by positivity)
        (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]) hspos.le
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), inv_eq_one_div,
      inv_eq_one_div]
    exact one_div_le_one_div_of_le hkp hle
  have hb2' : ‖integral φ - trapezoid (2 * k) φ‖
      ≤ √(4 * π * zetaReal (2 * s)) * (k : ℝ) ^ (-s) * ‖φ‖ := by
    refine hb2.trans ?_
    have := mul_le_mul_of_nonneg_left hrate (Real.sqrt_nonneg (4 * π * zetaReal (2 * s)))
    exact mul_le_mul_of_nonneg_right this (norm_nonneg φ)
  have hsplit : integral φ - simpson k φ
      = (4 * (integral φ - trapezoid (2 * k) φ) - (integral φ - trapezoid k φ)) / 3 := by
    rw [simpson_eq k hk φ]
    ring
  rw [hsplit, norm_div, Complex.norm_ofNat]
  have hnum : ‖4 * (integral φ - trapezoid (2 * k) φ) - (integral φ - trapezoid k φ)‖
      ≤ 4 * ‖integral φ - trapezoid (2 * k) φ‖ + ‖integral φ - trapezoid k φ‖ := by
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_mul]
    norm_num
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
  linarith

/-- **Exercise 7.5.4**: for `t > 0` every element `η` of `H^{-t}(2π)` is a bounded linear functional
on `H^t(2π)` under the pairing (7.5.6), `ℓ[φ] = ∑_m a_m conj (b_m)`, with `‖ℓ‖ ≤ ‖η‖_{*,-t}`. -/
theorem exercise_7_5_4 (t : ℝ) (η : PeriodicSobolev (-t)) :
    (∀ φ : PeriodicSobolev t,
        PeriodicSobolev.dualPairing t η φ = ∑' m : ℤ, φ.coeff m * conj (η.coeff m)) ∧
      ‖PeriodicSobolev.dualPairing t η‖ ≤ ‖η‖ :=
  ⟨fun _ => rfl, PeriodicSobolev.norm_dualPairing_le t η⟩

end AtkinsonHan.Chapter07
