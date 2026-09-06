/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Fourier.AddCircle`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.RingTheory.RootsOfUnity.Complex
import Numlib.Analysis.Normed.Operator.Compact

/-!
# Periodic Sobolev spaces

A periodic Sobolev space is a space of formal Fourier series, graded by the decay of the
coefficients: for a real `s`, `PeriodicSobolev s` consists of the series `∑ a m ψ m` whose
coefficients satisfy

`‖a‖² = ‖a 0‖² + ∑_{m ≠ 0} |m|^{2 s} ‖a m‖² < ∞`.

No domain, no boundary and no weak derivative on an open set enter the definition — the space is a
weighted `ℓ²(ℤ, ℂ)`, and that is how it is built here: `PeriodicSobolev s` *is* `lp (fun _ : ℤ => ℂ)
2`, with the element `u` standing for the series whose `m`-th coefficient is `u m / weight s m`.
So the Hilbert structure, its completeness and Parseval's identity all come from `lp` unchanged, and
the grading lives entirely in `PeriodicSobolev.coeff`.

Two consequences of that choice are worth stating. For `s < 0` the elements are *not* functions —
the series need not converge in any usual sense — so the space is deliberately not a subtype of an
`L²` space. And for `s > 1/2` the coefficients are absolutely summable, so the series does converge
uniformly; `PeriodicSobolev.eval T φ` is the resulting continuous function of period `T` on the
line, for whatever period `T` one wants to read the series on. The period is therefore a parameter
of the *bridge to functions*, not of the space.

## Main definitions

* `zetaReal r`, the value `∑_{n ≥ 1} n ^ (-r)` of the Riemann zeta function at a real `r > 1`,
  identified with Mathlib's `riemannZeta` by `ofReal_zetaReal`;
* `periodicSobolevWeight s m`, the weight `1` at `m = 0` and `|m| ^ s` elsewhere;
* `PeriodicSobolev s`, the space itself, and `PeriodicSobolev.coeff` its coefficients;
* `PeriodicSobolev.inclL`, the inclusion `PeriodicSobolev s → PeriodicSobolev t` for `t ≤ s`, and
  `PeriodicSobolev.truncL` its finite-rank truncation to a finite set of frequencies;
* `periodicChar T m`, the character `x ↦ exp (2 π i m x / T)`;
* `PeriodicSobolev.eval T φ`, the sum of the series as a function on the line;
* `PeriodicSobolev.trapezoidSum T k f`, the trapezoidal rule `(T / k) ∑_{j = 1}^{k} f (j T / k)`
  for a function of period `T`.

## Main statements

* `PeriodicSobolev.hasSum_norm_sq` and `PeriodicSobolev.inner_eq_tsum`: the norm and the inner
  product in terms of the coefficients;
* `PeriodicSobolev.tsum_norm_coeff_le`: for `s > 1/2` the coefficients are absolutely summable,
  with `∑_{m ≠ 0} ‖a m‖ ≤ √(2 ζ(2 s)) ‖φ‖` — the Sobolev embedding into the continuous functions,
  in its coefficient form; `PeriodicSobolev.tsum_norm_coeff_mul_le` is the same Cauchy–Schwarz step
  read along the multiples of a `k`, which is what the quadrature bound needs;
* `PeriodicSobolev.norm_eval_le`, `PeriodicSobolev.continuous_eval` and
  `PeriodicSobolev.eval_periodic`: the embedding itself, `‖φ‖_∞ ≤ (1 + √(2 ζ(2 s))) ‖φ‖` into the
  continuous functions of period `T`;
* `PeriodicSobolev.denseRange_inclL` and `PeriodicSobolev.isCompactOperator_inclL`: the inclusion
  has dense range, and is compact when `t < s`;
* `PeriodicSobolev.norm_intervalIntegral_sub_trapezoidSum_le`: **the trapezoidal rule is spectrally
  accurate on smooth periodic integrands**, `|I(φ) − T_k(φ)| ≤ T k^{-s} √(2 ζ(2 s)) ‖φ‖`. The whole
  content is `sum_periodicChar`: the trapezoidal sum of `periodicChar T m` vanishes unless `k ∣ m`,
  so the quadrature error is the tail `∑_{j ≠ 0} a_{j k}` of the series along the multiples of `k`.

## References

The periodic Sobolev spaces and the three propositions above are [han2009theoretical] §7.5, where
they are stated for the period `2 π` with the orthonormal system `ψ m x = (2 π)^{-1/2} exp (i m x)`.
The coefficients here are those of the unnormalized system `exp (2 π i m x / T)`, so they are
`√T` times that book's; the definition of the norm is unaffected by the constant, but an
identification with the book's coefficients is not, and is made in the surface layer.
-/

open Filter Metric Set Topology
open scoped ComplexConjugate ENNReal InnerProductSpace Real

/-! ### The Riemann zeta function on the real axis -/

/-- `zetaReal r` is `∑_{n ≥ 1} n ^ (-r)`, the Riemann zeta function restricted to a real argument.
The sum is over all of `ℕ` and the term at `n = 0` is `(0 ^ r)⁻¹ = 0` whenever `r ≠ 0`, so no
shifting of the index is needed. It agrees with the analytic `riemannZeta` for `r > 1`, by
`ofReal_zetaReal`, and is junk (`0`, the value of a divergent sum) for `r ≤ 1`. -/
noncomputable def zetaReal (r : ℝ) : ℝ := ∑' n : ℕ, ((n : ℝ) ^ r)⁻¹

theorem summable_inv_nat_rpow {r : ℝ} (hr : 1 < r) : Summable fun n : ℕ => ((n : ℝ) ^ r)⁻¹ :=
  Real.summable_nat_rpow_inv.2 hr

theorem zetaReal_nonneg (r : ℝ) : 0 ≤ zetaReal r :=
  tsum_nonneg fun _ => by positivity

/-- The real zeta values are the values of Mathlib's `riemannZeta` on the real axis, above `1`. -/
theorem ofReal_zetaReal {r : ℝ} (hr : 1 < r) : (zetaReal r : ℂ) = riemannZeta (r : ℂ) := by
  have hre : 1 < (r : ℂ).re := by simpa using hr
  rw [zeta_eq_tsum_one_div_nat_cpow hre, zetaReal, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_inv, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, one_div]

/-- The two-sided zeta sum: `∑_{m ∈ ℤ} |m| ^ (-r) = 2 ζ(r)` for `r > 1`. The term at `m = 0` is
`(0 ^ r)⁻¹ = 0`, so the sum is really over `m ≠ 0`. -/
theorem hasSum_int_inv_abs_rpow {r : ℝ} (hr : 1 < r) :
    HasSum (fun m : ℤ => (|(m : ℝ)| ^ r)⁻¹) (2 * zetaReal r) := by
  have hr0 : r ≠ 0 := by linarith
  have hz : HasSum (fun n : ℕ => ((n : ℝ) ^ r)⁻¹) (zetaReal r) := (summable_inv_nat_rpow hr).hasSum
  set f : ℤ → ℝ := fun m => (|(m : ℝ)| ^ r)⁻¹ with hf
  have h₁ : HasSum (fun n : ℕ => f n) (zetaReal r) := hz.congr_fun fun n => by simp [hf]
  have h₂ : HasSum (fun n : ℕ => f (-n)) (zetaReal r) := hz.congr_fun fun n => by simp [hf]
  have hf0 : f 0 = 0 := by simp [hf, Real.zero_rpow hr0]
  have h := h₁.of_nat_of_neg h₂
  rw [hf0, sub_zero, ← two_mul] at h
  exact h

/-! ### Norms in `ℓ²` -/

namespace lp

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]

/-- Parseval's identity in `ℓ²`: the squared norms of the entries sum to the squared norm. -/
theorem hasSum_norm_sq (f : lp E 2) : HasSum (fun i => ‖f i‖ ^ 2) (‖f‖ ^ 2) := by
  have := lp.hasSum_norm (E := E) (p := 2) (by norm_num) f
  simpa using this

/-- The norm of an element of `lp E 2` is the square root of the sum of the squared norms of its
entries. -/
theorem norm_eq_sqrt_tsum_norm_sq (f : lp E 2) : ‖f‖ = √(∑' i, ‖f i‖ ^ 2) := by
  rw [(hasSum_norm_sq f).tsum_eq, Real.sqrt_sq (norm_nonneg f)]

end lp

/-! ### The weight -/

/-- The weight defining the `s`-th periodic Sobolev norm: `1` at `m = 0` and `|m| ^ s` elsewhere.
The exceptional value at `0` is what makes the weight positive for every `s`, and hence the norm a
norm; every other index carries the decay `|m| ^ s` that grades the scale. -/
noncomputable def periodicSobolevWeight (s : ℝ) (m : ℤ) : ℝ :=
  if m = 0 then 1 else |(m : ℝ)| ^ s

@[simp]
theorem periodicSobolevWeight_zero (s : ℝ) : periodicSobolevWeight s 0 = 1 := ite_eq_left rfl

theorem periodicSobolevWeight_of_ne_zero {m : ℤ} (s : ℝ) (hm : m ≠ 0) :
    periodicSobolevWeight s m = |(m : ℝ)| ^ s := ite_eq_right hm

theorem periodicSobolevWeight_pos (s : ℝ) (m : ℤ) : 0 < periodicSobolevWeight s m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [periodicSobolevWeight_of_ne_zero s hm]
    exact Real.rpow_pos_of_pos (abs_pos.2 (Int.cast_ne_zero.2 hm)) s

theorem periodicSobolevWeight_ne_zero (s : ℝ) (m : ℤ) : periodicSobolevWeight s m ≠ 0 :=
  (periodicSobolevWeight_pos s m).ne'

@[simp]
theorem periodicSobolevWeight_zero_exponent (m : ℤ) : periodicSobolevWeight 0 m = 1 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [periodicSobolevWeight_of_ne_zero 0 hm, Real.rpow_zero]

/-- The weight is monotone in the exponent, at every index: this is the inclusion of the scale. -/
theorem periodicSobolevWeight_le {s t : ℝ} (h : t ≤ s) (m : ℤ) :
    periodicSobolevWeight t m ≤ periodicSobolevWeight s m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [periodicSobolevWeight_of_ne_zero t hm, periodicSobolevWeight_of_ne_zero s hm]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Int.one_le_abs hm) h

/-! ### The space -/

/-- `PeriodicSobolev s` is the space of formal Fourier series `∑ a m ψ m` whose coefficients satisfy
`‖a 0‖² + ∑_{m ≠ 0} |m|^{2 s} ‖a m‖² < ∞`, an inner product space under

`⟪φ, ρ⟫ = conj (a 0) * b 0 + ∑_{m ≠ 0} |m|^{2 s} * conj (a m) * b m`.

It is implemented as `ℓ²(ℤ, ℂ)`, an element `u` of which stands for the series whose coefficients
are `a m = u m / periodicSobolevWeight s m`; the norm of the underlying `ℓ²` element is then exactly
the weighted norm above, and the whole Hilbert structure is inherited unchanged. Read the
coefficients off with `PeriodicSobolev.coeff` and build an element with `PeriodicSobolev.ofCoeff`.

For `s < 0` an element is genuinely only a formal series: its coefficients may grow, and it is not a
function. That is why the space is a sequence space and not a subtype of an `L²` space. -/
def PeriodicSobolev (_s : ℝ) : Type := lp (fun _ : ℤ => ℂ) 2

namespace PeriodicSobolev

variable {s t : ℝ}

noncomputable instance : NormedAddCommGroup (PeriodicSobolev s) :=
  inferInstanceAs (NormedAddCommGroup (lp (fun _ : ℤ => ℂ) 2))

noncomputable instance : InnerProductSpace ℂ (PeriodicSobolev s) :=
  inferInstanceAs (InnerProductSpace ℂ (lp (fun _ : ℤ => ℂ) 2))

instance : CompleteSpace (PeriodicSobolev s) :=
  inferInstanceAs (CompleteSpace (lp (fun _ : ℤ => ℂ) 2))

/-- The weighted coefficient sequence of an element, as an element of `ℓ²(ℤ, ℂ)`: its `m`-th entry
is `periodicSobolevWeight s m * coeff φ m`. On the underlying data this is the identity; it exists
to keep the two readings of the same sequence apart, and to carry `lp` lemmas across. -/
noncomputable def toLp (s : ℝ) : PeriodicSobolev s ≃ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  LinearIsometryEquiv.refl ℂ (lp (fun _ : ℤ => ℂ) 2)

@[simp]
theorem norm_toLp (φ : PeriodicSobolev s) : ‖toLp s φ‖ = ‖φ‖ := (toLp s).norm_map φ

/-- The `m`-th Fourier coefficient of `φ ∈ PeriodicSobolev s`. -/
noncomputable def coeff (φ : PeriodicSobolev s) (m : ℤ) : ℂ :=
  (periodicSobolevWeight s m : ℂ)⁻¹ * toLp s φ m

theorem toLp_apply (φ : PeriodicSobolev s) (m : ℤ) :
    toLp s φ m = periodicSobolevWeight s m * coeff φ m := by
  rw [coeff, ← mul_assoc, mul_inv_cancel₀ (by
    exact_mod_cast periodicSobolevWeight_ne_zero s m), one_mul]

theorem norm_toLp_apply (φ : PeriodicSobolev s) (m : ℤ) :
    ‖toLp s φ m‖ = periodicSobolevWeight s m * ‖coeff φ m‖ := by
  rw [toLp_apply, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (periodicSobolevWeight_pos s m).le]

theorem coeff_injective : Function.Injective (coeff (s := s)) := by
  intro φ ρ h
  refine (toLp s).injective (lp.ext (funext fun m => ?_))
  rw [toLp_apply, toLp_apply, h]

@[simp]
theorem coeff_zero (s : ℝ) : coeff (0 : PeriodicSobolev s) = 0 := by
  funext m; simp [coeff]

@[simp]
theorem coeff_add (φ ρ : PeriodicSobolev s) : coeff (φ + ρ) = coeff φ + coeff ρ := by
  funext m; simp [coeff, mul_add]

@[simp]
theorem coeff_smul (c : ℂ) (φ : PeriodicSobolev s) : coeff (c • φ) = c • coeff φ := by
  funext m; simp [coeff]; ring

@[simp]
theorem coeff_sub (φ ρ : PeriodicSobolev s) : coeff (φ - ρ) = coeff φ - coeff ρ := by
  funext m; simp [coeff, mul_sub]

/-- **Parseval's identity for the periodic Sobolev norm**: `‖φ‖² = ∑_m (|m|^s ‖a m‖)²`, with the
weight `1` at `m = 0`. This is the defining property of the space. -/
theorem hasSum_norm_sq (φ : PeriodicSobolev s) :
    HasSum (fun m : ℤ => (periodicSobolevWeight s m * ‖coeff φ m‖) ^ 2) (‖φ‖ ^ 2) := by
  have h := lp.hasSum_norm_sq (toLp s φ)
  simpa only [norm_toLp_apply, norm_toLp] using h

theorem norm_sq_eq_tsum (φ : PeriodicSobolev s) :
    ‖φ‖ ^ 2 = ∑' m : ℤ, (periodicSobolevWeight s m * ‖coeff φ m‖) ^ 2 :=
  (hasSum_norm_sq φ).tsum_eq.symm

/-- Every coefficient is controlled by the norm: `|m|^s ‖a m‖ ≤ ‖φ‖`. -/
theorem weight_mul_norm_coeff_le (φ : PeriodicSobolev s) (m : ℤ) :
    periodicSobolevWeight s m * ‖coeff φ m‖ ≤ ‖φ‖ := by
  rw [← norm_toLp_apply, ← norm_toLp φ]
  exact lp.norm_apply_le_norm (by norm_num) (toLp s φ) m

/-- The inner product in terms of the coefficients. Mathlib's inner product is conjugate-linear in
its *first* argument, the opposite of the convention usual in the numerical-analysis literature. -/
theorem inner_eq_tsum (φ ρ : PeriodicSobolev s) :
    (inner ℂ φ ρ : ℂ) =
      ∑' m : ℤ, (periodicSobolevWeight s m : ℂ) ^ 2 * (conj (coeff φ m) * coeff ρ m) := by
  rw [← (toLp s).inner_map_map φ ρ, lp.inner_eq_tsum]
  refine tsum_congr fun m => ?_
  rw [RCLike.inner_apply, toLp_apply, toLp_apply, map_mul, Complex.conj_ofReal]
  ring

/-- The element with prescribed coefficients. -/
noncomputable def ofCoeff (s : ℝ) (a : ℤ → ℂ)
    (ha : Memℓp (fun m => (periodicSobolevWeight s m : ℂ) * a m) 2) : PeriodicSobolev s :=
  (toLp s).symm ⟨_, ha⟩

@[simp]
theorem coeff_ofCoeff (s : ℝ) (a : ℤ → ℂ)
    (ha : Memℓp (fun m => (periodicSobolevWeight s m : ℂ) * a m) 2) :
    coeff (ofCoeff s a ha) = a := by
  funext m
  rw [coeff, ofCoeff, LinearIsometryEquiv.apply_symm_apply]
  change (periodicSobolevWeight s m : ℂ)⁻¹ * ((periodicSobolevWeight s m : ℂ) * a m) = a m
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast periodicSobolevWeight_ne_zero s m), one_mul]

end PeriodicSobolev

/-! ### Cauchy–Schwarz against the weights -/

/-- Away from `m = 0` the square of the weight is `|m| ^ (2 s)`. -/
theorem periodicSobolevWeight_sq (s : ℝ) {m : ℤ} (hm : m ≠ 0) :
    periodicSobolevWeight s m ^ 2 = |(m : ℝ)| ^ (2 * s) := by
  rw [periodicSobolevWeight_of_ne_zero s hm, ← Real.rpow_natCast (|(m : ℝ)| ^ s) 2,
    ← Real.rpow_mul (abs_nonneg _)]
  norm_num [mul_comm]

/-- `Memℓp` at the exponent `2`, with the square written as a natural power. `Memℓp` is phrased
with the *real* exponent `p.toReal`, so every use of it at `p = 2` has to cross this bridge. -/
theorem memℓp_two_iff {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] {f : ∀ i, E i} :
    Memℓp f 2 ↔ Summable fun i => ‖f i‖ ^ 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  refine summable_congr fun i => ?_
  rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

namespace PeriodicSobolev

variable {s t : ℝ}

/-- The `ℓ²` sequence `j ↦ |j k| ^ (-s)`, and `0` at `j = 0`. It is square summable exactly when
`s > 1/2`, and its norm is then `k^{-s} √(2 ζ(2 s))`; pairing it with the weighted coefficients
along the multiples of `k` is the Cauchy–Schwarz step behind both the embedding (`k = 1`) and the
quadrature error bound (general `k`). -/
private noncomputable def invWeightSeq (s : ℝ) (k : ℕ) (j : ℤ) : ℂ :=
  if j = 0 then 0 else ((periodicSobolevWeight s (j * k) : ℂ))⁻¹

private theorem norm_invWeightSeq_sq (s : ℝ) (hs : 0 < s) {k : ℕ} (hk : 0 < k) (j : ℤ) :
    ‖invWeightSeq s k j‖ ^ 2 = ((k : ℝ) ^ (2 * s))⁻¹ * (|(j : ℝ)| ^ (2 * s))⁻¹ := by
  have h2s : (2 : ℝ) * s ≠ 0 := by positivity
  rcases eq_or_ne j 0 with rfl | hj
  · rw [invWeightSeq, ite_eq_left rfl]
    simp [Real.zero_rpow h2s]
  · have hjk : j * (k : ℤ) ≠ 0 := mul_ne_zero hj (by exact_mod_cast hk.ne')
    have habs : |((j * (k : ℤ) : ℤ) : ℝ)| = |(j : ℝ)| * (k : ℝ) := by
      push_cast
      rw [abs_mul, Nat.abs_cast]
    rw [invWeightSeq, ite_eq_right hj, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (periodicSobolevWeight_pos s _).le, inv_pow,
      periodicSobolevWeight_sq s hjk, habs,
      Real.mul_rpow (abs_nonneg _) (Nat.cast_nonneg k), mul_inv, mul_comm]

private theorem hasSum_norm_invWeightSeq_sq (hs : 1 / 2 < s) {k : ℕ} (hk : 0 < k) :
    HasSum (fun j : ℤ => ‖invWeightSeq s k j‖ ^ 2)
      (((k : ℝ) ^ (2 * s))⁻¹ * (2 * zetaReal (2 * s))) :=
  ((hasSum_int_inv_abs_rpow (by linarith : (1 : ℝ) < 2 * s)).mul_left _).congr_fun fun j =>
    norm_invWeightSeq_sq s (by linarith) hk j

/-- The Cauchy–Schwarz partner as an element of `ℓ²(ℤ, ℂ)`. -/
private noncomputable def invWeightLp (hs : 1 / 2 < s) {k : ℕ} (hk : 0 < k) :
    lp (fun _ : ℤ => ℂ) 2 :=
  ⟨invWeightSeq s k, memℓp_two_iff.2 (hasSum_norm_invWeightSeq_sq hs hk).summable⟩

private theorem norm_invWeightLp (hs : 1 / 2 < s) {k : ℕ} (hk : 0 < k) :
    ‖invWeightLp hs hk‖ = (k : ℝ) ^ (-s) * √(2 * zetaReal (2 * s)) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have he : -(2 * s) * (1 / 2 : ℝ) = -s := by ring
  have hsqrt : √(((k : ℝ) ^ (2 * s))⁻¹) = (k : ℝ) ^ (-s) := by
    rw [← Real.rpow_neg hk0, Real.sqrt_eq_rpow, ← Real.rpow_mul hk0, he]
  have h : HasSum (fun j : ℤ => ‖(invWeightLp hs hk : ℤ → ℂ) j‖ ^ 2)
      (((k : ℝ) ^ (2 * s))⁻¹ * (2 * zetaReal (2 * s))) := hasSum_norm_invWeightSeq_sq hs hk
  rw [lp.norm_eq_sqrt_tsum_norm_sq, h.tsum_eq, Real.sqrt_mul (by positivity), hsqrt]

private theorem injective_mul_natCast {k : ℕ} (hk : 0 < k) :
    Function.Injective fun j : ℤ => j * (k : ℤ) :=
  fun _ _ hab => mul_right_cancel₀ (by exact_mod_cast hk.ne') hab

private theorem summable_norm_toLp_mul_sq {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) :
    Summable fun j : ℤ => ‖(toLp s φ : ℤ → ℂ) (j * k)‖ ^ 2 :=
  (lp.hasSum_norm_sq (toLp s φ)).summable.comp_injective (injective_mul_natCast hk)

/-- The weighted coefficients read along the multiples of `k`, as an element of `ℓ²(ℤ, ℂ)`: a
subfamily of a square-summable family, so square summable, with a norm no larger. -/
private noncomputable def subLp {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) :
    lp (fun _ : ℤ => ℂ) 2 :=
  ⟨fun j : ℤ => toLp s φ (j * k), memℓp_two_iff.2 (summable_norm_toLp_mul_sq hk φ)⟩

private theorem subLp_apply {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) (j : ℤ) :
    (subLp hk φ : ℤ → ℂ) j = toLp s φ (j * k) := rfl

private theorem norm_subLp_le {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) :
    ‖subLp hk φ‖ ≤ ‖φ‖ := by
  have h₁ := lp.hasSum_norm_sq (subLp hk φ)
  have h₂ := lp.hasSum_norm_sq (toLp s φ)
  have hle : ‖subLp hk φ‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
    rw [← h₁.tsum_eq, ← norm_toLp φ, ← h₂.tsum_eq]
    refine le_trans (le_of_eq (tsum_congr fun j => ?_))
      (tsum_comp_le_tsum_of_inj h₂.summable (fun _ => by positivity) (injective_mul_natCast hk))
    rw [subLp_apply]
    rfl
  nlinarith [norm_nonneg (subLp hk φ), norm_nonneg φ]

/-- **Cauchy–Schwarz along the multiples of `k`.** For `s > 1/2` the coefficients `a_{j k}` with
`j ≠ 0` are absolutely summable, with `∑_{j ≠ 0} ‖a_{j k}‖ ≤ k^{-s} √(2 ζ(2 s)) ‖φ‖`. At `k = 1`
this is the book's (7.5.10); for general `k` it is the tail that the trapezoidal rule leaves. -/
theorem summable_norm_coeff_mul (hs : 1 / 2 < s) {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) :
    Summable fun j : ℤ => if j = 0 then (0 : ℝ) else ‖coeff φ (j * k)‖ := by
  have hpq : ((2 : ℝ≥0∞).toReal).HolderConjugate ((2 : ℝ≥0∞).toReal) := by
    simpa using Real.HolderConjugate.two_two
  obtain ⟨hsum, -⟩ := lp.tsum_mul_le_mul_norm hpq (invWeightLp hs hk) (subLp hk φ)
  refine hsum.congr fun j => ?_
  rcases eq_or_ne j 0 with rfl | hj
  · simp [invWeightLp, invWeightSeq]
  · rw [ite_eq_right hj]
    change ‖invWeightSeq s k j‖ * ‖toLp s φ (j * k)‖ = _
    rw [invWeightSeq, ite_eq_right hj, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (periodicSobolevWeight_pos s _).le, norm_toLp_apply,
      inv_mul_cancel_left₀ (periodicSobolevWeight_ne_zero s _)]

/-- The bound of `summable_norm_coeff_mul`: the tail along the multiples of `k` is at most
`k^{-s} SQRT(2 zeta(2 s))` times the norm. -/
theorem tsum_norm_coeff_mul_le (hs : 1 / 2 < s) {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) :
    ∑' j : ℤ, (if j = 0 then (0 : ℝ) else ‖coeff φ (j * k)‖)
      ≤ (k : ℝ) ^ (-s) * √(2 * zetaReal (2 * s)) * ‖φ‖ := by
  have hpq : ((2 : ℝ≥0∞).toReal).HolderConjugate ((2 : ℝ≥0∞).toReal) := by
    simpa using Real.HolderConjugate.two_two
  obtain ⟨-, hle⟩ := lp.tsum_mul_le_mul_norm hpq (invWeightLp hs hk) (subLp hk φ)
  have hprod : ∀ j : ℤ, ‖(invWeightLp hs hk : ℤ → ℂ) j‖ * ‖(subLp hk φ : ℤ → ℂ) j‖
      = if j = 0 then (0 : ℝ) else ‖coeff φ (j * k)‖ := by
    intro j
    rcases eq_or_ne j 0 with rfl | hj
    · simp [invWeightLp, invWeightSeq]
    · rw [ite_eq_right hj]
      change ‖invWeightSeq s k j‖ * ‖toLp s φ (j * k)‖ = _
      rw [invWeightSeq, ite_eq_right hj, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (periodicSobolevWeight_pos s _).le, norm_toLp_apply,
        inv_mul_cancel_left₀ (periodicSobolevWeight_ne_zero s _)]
  rw [funext hprod, norm_invWeightLp hs hk] at hle
  exact hle.trans (mul_le_mul_of_nonneg_left (norm_subLp_le hk φ) (by positivity))

/-! ### The Sobolev embedding into the continuous functions -/

/-- **The Sobolev embedding in coefficient form**: for `s > 1/2` the Fourier coefficients of an
element of `PeriodicSobolev s` are absolutely summable away from `m = 0`, with the book's bound
`∑_{m ≠ 0} ‖a m‖ ≤ √(2 ζ(2 s)) ‖φ‖`. This is Cauchy–Schwarz against
`∑_{m ≠ 0} |m| ^ (-2 s) = 2 ζ(2 s)`, which converges exactly because `2 s > 1`. -/
theorem summable_norm_coeff_ne_zero (hs : 1 / 2 < s) (φ : PeriodicSobolev s) :
    Summable fun m : ℤ => if m = 0 then (0 : ℝ) else ‖coeff φ m‖ :=
  (summable_norm_coeff_mul hs one_pos φ).congr fun m => by simp

theorem tsum_norm_coeff_ne_zero_le (hs : 1 / 2 < s) (φ : PeriodicSobolev s) :
    ∑' m : ℤ, (if m = 0 then (0 : ℝ) else ‖coeff φ m‖) ≤ √(2 * zetaReal (2 * s)) * ‖φ‖ := by
  have h := tsum_norm_coeff_mul_le hs one_pos φ
  simp only [Nat.cast_one, Real.one_rpow, one_mul, mul_one] at h
  exact h

/-- For `s > 1/2` the full coefficient family is absolutely summable, the `m = 0` term included. -/
theorem summable_norm_coeff (hs : 1 / 2 < s) (φ : PeriodicSobolev s) :
    Summable fun m : ℤ => ‖coeff φ m‖ := by
  refine ((summable_norm_coeff_ne_zero hs φ).add
    (hasSum_ite_eq (0 : ℤ) ‖coeff φ 0‖).summable).congr fun m => ?_
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · simp [hm]

theorem summable_coeff (hs : 1 / 2 < s) (φ : PeriodicSobolev s) : Summable (coeff φ) :=
  (summable_norm_coeff hs φ).of_norm

/-- The book's (7.5.10): `∑_m ‖a m‖ ≤ ‖a 0‖ + √(2 ζ(2 s)) ‖φ‖`. -/
theorem tsum_norm_coeff_le (hs : 1 / 2 < s) (φ : PeriodicSobolev s) :
    ∑' m : ℤ, ‖coeff φ m‖ ≤ ‖coeff φ 0‖ + √(2 * zetaReal (2 * s)) * ‖φ‖ := by
  have hsplit : ∑' m : ℤ, ‖coeff φ m‖
      = (∑' m : ℤ, (if m = 0 then (0 : ℝ) else ‖coeff φ m‖)) + ‖coeff φ 0‖ := by
    rw [← (hasSum_ite_eq (0 : ℤ) ‖coeff φ 0‖).tsum_eq,
      ← (summable_norm_coeff_ne_zero hs φ).tsum_add (hasSum_ite_eq (0 : ℤ) ‖coeff φ 0‖).summable]
    refine tsum_congr fun m => ?_
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · simp [hm]
  rw [hsplit]
  have := tsum_norm_coeff_ne_zero_le hs φ
  linarith

/-- Since `‖a 0‖ ≤ ‖φ‖`, the bound (7.5.10) becomes `∑_m ‖a m‖ ≤ (1 + √(2 ζ(2 s))) ‖φ‖`. -/
theorem tsum_norm_coeff_le' (hs : 1 / 2 < s) (φ : PeriodicSobolev s) :
    ∑' m : ℤ, ‖coeff φ m‖ ≤ (1 + √(2 * zetaReal (2 * s))) * ‖φ‖ := by
  have h0 : ‖coeff φ 0‖ ≤ ‖φ‖ := by
    simpa using weight_mul_norm_coeff_le φ 0
  have := tsum_norm_coeff_le hs φ
  nlinarith [this, h0]

end PeriodicSobolev

/-! ### The scale: the inclusion `PeriodicSobolev s → PeriodicSobolev t` for `t ≤ s` -/

namespace PeriodicSobolev

variable {s t : ℝ}

/-- The coefficient map as a linear map into the sequence space. It exists to carry `map_sum`
across; the working interface is `PeriodicSobolev.coeff`. -/
noncomputable def coeffₗ (s : ℝ) : PeriodicSobolev s →ₗ[ℂ] (ℤ → ℂ) where
  toFun := coeff
  map_add' := coeff_add
  map_smul' := coeff_smul

theorem coeff_sum {ι : Type*} (F : Finset ι) (f : ι → PeriodicSobolev s) :
    coeff (∑ i ∈ F, f i) = ∑ i ∈ F, coeff (f i) :=
  map_sum (coeffₗ s) f F

/-- The `m`-th coordinate series: the element whose coefficients are `1` at `m` and `0` elsewhere.
Its coefficient family is finitely supported, so it lies in `PeriodicSobolev s` for every `s`. -/
noncomputable def basisElt (s : ℝ) (m : ℤ) : PeriodicSobolev s :=
  ofCoeff s (fun m' => if m' = m then 1 else 0)
    (memℓp_two_iff.2 (summable_of_ne_finset_zero (s := {m}) fun m' hm' => by
      rw [Finset.mem_singleton] at hm'
      simp [hm']))

@[simp]
theorem coeff_basisElt (s : ℝ) (m m' : ℤ) :
    coeff (basisElt s m) m' = if m' = m then 1 else 0 := by
  rw [basisElt, coeff_ofCoeff]

/-- The `m`-th coefficient as a continuous linear functional, of norm at most `|m| ^ (-s)`. -/
noncomputable def coeffL (s : ℝ) (m : ℤ) : PeriodicSobolev s →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun φ => coeff φ m
      map_add' := fun φ ρ => by simp
      map_smul' := fun c φ => by simp }
    (periodicSobolevWeight s m)⁻¹ fun φ => by
      rw [inv_mul_eq_div, le_div_iff₀ (periodicSobolevWeight_pos s m), mul_comm]
      exact weight_mul_norm_coeff_le φ m

@[simp]
theorem coeffL_apply (s : ℝ) (m : ℤ) (φ : PeriodicSobolev s) : coeffL s m φ = coeff φ m := rfl

/-- The inclusion of the scale: the same formal series, read in the weaker space. -/
noncomputable def incl (h : t ≤ s) (φ : PeriodicSobolev s) : PeriodicSobolev t :=
  ofCoeff t (coeff φ) (memℓp_two_iff.2 (by
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      (hasSum_norm_sq φ).summable
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (periodicSobolevWeight_pos t m).le]
    have h1 : periodicSobolevWeight t m * ‖coeff φ m‖ ≤ periodicSobolevWeight s m * ‖coeff φ m‖ :=
      mul_le_mul_of_nonneg_right (periodicSobolevWeight_le h m) (norm_nonneg _)
    have h2 : 0 ≤ periodicSobolevWeight t m * ‖coeff φ m‖ :=
      mul_nonneg (periodicSobolevWeight_pos t m).le (norm_nonneg _)
    nlinarith))

@[simp]
theorem coeff_incl (h : t ≤ s) (φ : PeriodicSobolev s) : coeff (incl h φ) = coeff φ :=
  coeff_ofCoeff _ _ _

/-- The inclusion does not increase the norm: the `t`-weights are smaller than the `s`-weights. -/
theorem norm_incl_le (h : t ≤ s) (φ : PeriodicSobolev s) : ‖incl h φ‖ ≤ ‖φ‖ := by
  have h₁ := hasSum_norm_sq (incl h φ)
  have h₂ := hasSum_norm_sq φ
  have hle : ‖incl h φ‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
    rw [← h₁.tsum_eq, ← h₂.tsum_eq]
    refine h₁.summable.tsum_le_tsum (fun m => ?_) h₂.summable
    rw [coeff_incl]
    have h1 : periodicSobolevWeight t m * ‖coeff φ m‖ ≤ periodicSobolevWeight s m * ‖coeff φ m‖ :=
      mul_le_mul_of_nonneg_right (periodicSobolevWeight_le h m) (norm_nonneg _)
    have h2 : 0 ≤ periodicSobolevWeight t m * ‖coeff φ m‖ :=
      mul_nonneg (periodicSobolevWeight_pos t m).le (norm_nonneg _)
    nlinarith
  nlinarith [norm_nonneg (incl h φ), norm_nonneg φ]

/-- **The inclusion of the scale**, as a continuous linear map of norm at most one. -/
noncomputable def inclL (h : t ≤ s) : PeriodicSobolev s →L[ℂ] PeriodicSobolev t :=
  LinearMap.mkContinuous
    { toFun := incl h
      map_add' := fun φ ρ => coeff_injective (by simp)
      map_smul' := fun c φ => coeff_injective (by simp) }
    1 fun φ => by simpa using norm_incl_le h φ

@[simp]
theorem inclL_apply (h : t ≤ s) (φ : PeriodicSobolev s) : inclL h φ = incl h φ := rfl

/-- The inclusion of the scale has norm at most one. -/
theorem norm_inclL_le (h : t ≤ s) : ‖inclL h‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Nothing but `0` is orthogonal to every coordinate series. This is the one computation behind
both `denseRange_inclL` and `dense_span_basisElt`. -/
theorem eq_zero_of_inner_basisElt_eq_zero {ρ : PeriodicSobolev s}
    (h : ∀ m : ℤ, (inner ℂ (basisElt s m) ρ : ℂ) = 0) : ρ = 0 := by
  refine coeff_injective (funext fun m => ?_)
  have hzero := h m
  rw [inner_eq_tsum, tsum_eq_single m fun m' hm' => by simp [hm']] at hzero
  have hw : ((periodicSobolevWeight s m : ℂ)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (by exact_mod_cast periodicSobolevWeight_ne_zero s m)
  have h0 : ((periodicSobolevWeight s m : ℂ)) ^ 2 * coeff ρ m = 0 := by simpa using hzero
  simpa using (mul_eq_zero.1 h0).resolve_left hw

/-- **The inclusion has dense range** (Atkinson–Han's Proposition 7.5.5, first half). In a Hilbert
space it is enough that nothing is orthogonal to the range, and the coordinate series
`basisElt t m` lie in it, so an orthogonal element has every coefficient zero. -/
theorem denseRange_inclL (h : t ≤ s) : DenseRange (inclL h) := by
  have hbot : (LinearMap.range (inclL h : PeriodicSobolev s →ₗ[ℂ] PeriodicSobolev t))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro ρ hρ
    refine eq_zero_of_inner_basisElt_eq_zero fun m => ?_
    have hmem : incl h (basisElt s m) ∈
        LinearMap.range (inclL h : PeriodicSobolev s →ₗ[ℂ] PeriodicSobolev t) :=
      ⟨basisElt s m, rfl⟩
    have hzero : (inner ℂ (incl h (basisElt s m)) ρ : ℂ) = 0 :=
      Submodule.mem_orthogonal _ _ |>.1 hρ _ hmem
    rwa [show incl h (basisElt s m) = basisElt t m from
      coeff_injective (by funext m'; simp)] at hzero
  have hdense : Dense
      ((LinearMap.range (inclL h : PeriodicSobolev s →ₗ[ℂ] PeriodicSobolev t)) :
        Set (PeriodicSobolev t)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2
      (Submodule.topologicalClosure_eq_top_iff.2 hbot)
  rw [LinearMap.coe_range] at hdense
  exact hdense

/-! ### Compactness of the inclusion -/

/-- The truncation of the scale to the frequencies in a finite set `F`: a finite sum of rank-one
operators, and the finite-rank approximation behind the compactness of the inclusion. -/
noncomputable def truncL (s t : ℝ) (F : Finset ℤ) : PeriodicSobolev s →L[ℂ] PeriodicSobolev t :=
  ∑ m ∈ F, (coeffL s m).smulRight (basisElt t m)

theorem coeff_truncL (s t : ℝ) (F : Finset ℤ) (φ : PeriodicSobolev s) (m : ℤ) :
    coeff (truncL s t F φ) m = if m ∈ F then coeff φ m else 0 := by
  classical
  simp only [truncL, sum_apply, ContinuousLinearMap.smulRight_apply,
    coeffL_apply, coeff_sum, Finset.sum_apply, coeff_smul, Pi.smul_apply, coeff_basisElt,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  exact Finset.sum_ite_eq F m fun m' => coeff φ m'

private theorem isCompactOperator_rankOne (f : PeriodicSobolev s →L[ℂ] ℂ)
    (y : PeriodicSobolev t) : IsCompactOperator (f.smulRight y) := by
  have h1 : IsCompactOperator (⇑f) := isCompactOperator_of_locallyCompactSpace_dom f
  have h2 := h1.continuous_comp (g := fun c : ℂ => c • y) (continuous_id.smul continuous_const)
  have heq : ⇑(f.smulRight y) = (fun c : ℂ => c • y) ∘ ⇑f := by
    funext x; simp
  rw [heq]
  exact h2

/-- A truncation is compact: it is a finite sum of rank-one operators. -/
theorem isCompactOperator_truncL (s t : ℝ) (F : Finset ℤ) :
    IsCompactOperator (truncL s t F) :=
  Finset.sum_induction _ (fun A : PeriodicSobolev s →L[ℂ] PeriodicSobolev t =>
      IsCompactOperator A)
    (fun _ _ ha hb => ha.add hb) isCompactOperator_zero
    fun _ _ => isCompactOperator_rankOne _ _

/-- The tail estimate behind the compactness: outside `[-n, n]` the `t`-weight is smaller than the
`s`-weight by the factor `(n + 1) ^ (t - s)`, which vanishes as `n → ∞` exactly when `t < s`. -/
theorem norm_incl_sub_truncL_le (h : t ≤ s) (n : ℕ) (φ : PeriodicSobolev s) :
    ‖incl h φ - truncL s t (Finset.Icc (-(n : ℤ)) (n : ℤ)) φ‖
      ≤ (((n : ℝ) + 1) ^ (s - t))⁻¹ * ‖φ‖ := by
  classical
  set F : Finset ℤ := Finset.Icc (-(n : ℤ)) (n : ℤ) with hFdef
  set c : ℝ := (((n : ℝ) + 1) ^ (s - t))⁻¹ with hcdef
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ (s - t) := Real.rpow_pos_of_pos (by positivity) _
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hcoeff : ∀ m : ℤ, coeff (incl h φ - truncL s t F φ) m
      = if m ∈ F then 0 else coeff φ m := by
    intro m
    rw [coeff_sub]
    simp only [Pi.sub_apply, coeff_incl, coeff_truncL]
    split <;> simp
  have hterm : ∀ m : ℤ, (periodicSobolevWeight t m * ‖coeff (incl h φ - truncL s t F φ) m‖) ^ 2
      ≤ c ^ 2 * (periodicSobolevWeight s m * ‖coeff φ m‖) ^ 2 := by
    intro m
    rw [hcoeff m]
    by_cases hmF : m ∈ F
    · rw [ite_eq_left hmF]
      have h0 : (periodicSobolevWeight t m * ‖(0 : ℂ)‖) ^ 2 = 0 := by simp
      rw [h0]
      positivity
    · rw [ite_eq_right hmF]
      have hn1 : ((n : ℤ) + 1) ≤ |m| := by
        rw [hFdef, Finset.mem_Icc, not_and_or, not_le, not_le] at hmF
        rcases hmF with hm | hm
        · rw [abs_of_nonpos (by omega)]; omega
        · rw [abs_of_nonneg (by omega)]; omega
      have habs : ((n : ℝ) + 1) ≤ |(m : ℝ)| := by
        calc ((n : ℝ) + 1) = (((n : ℤ) + 1 : ℤ) : ℝ) := by push_cast; ring
          _ ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast hn1
          _ = |(m : ℝ)| := by rw [Int.cast_abs]
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [abs_zero] at hn1
        omega
      have hmpos : (0 : ℝ) < |(m : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hm0)
      have hkey : periodicSobolevWeight t m ≤ c * periodicSobolevWeight s m := by
        rw [hcdef, inv_mul_eq_div, le_div_iff₀ hpos,
          periodicSobolevWeight_of_ne_zero t hm0, periodicSobolevWeight_of_ne_zero s hm0]
        calc |(m : ℝ)| ^ t * ((n : ℝ) + 1) ^ (s - t)
            ≤ |(m : ℝ)| ^ t * |(m : ℝ)| ^ (s - t) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow (by positivity) habs (by linarith : (0 : ℝ) ≤ s - t))
                (Real.rpow_nonneg (abs_nonneg _) t)
          _ = |(m : ℝ)| ^ s := by
              rw [← Real.rpow_add hmpos, show t + (s - t) = s by ring]
      have h1 : 0 ≤ periodicSobolevWeight t m * ‖coeff φ m‖ :=
        mul_nonneg (periodicSobolevWeight_pos t m).le (norm_nonneg _)
      have h2 : periodicSobolevWeight t m * ‖coeff φ m‖
          ≤ c * periodicSobolevWeight s m * ‖coeff φ m‖ :=
        mul_le_mul_of_nonneg_right hkey (norm_nonneg _)
      nlinarith
  have h₁ := hasSum_norm_sq (incl h φ - truncL s t F φ)
  have h₂ := hasSum_norm_sq φ
  have hsq : ‖incl h φ - truncL s t F φ‖ ^ 2 ≤ (c * ‖φ‖) ^ 2 := by
    rw [← h₁.tsum_eq, mul_pow]
    have hmul : HasSum (fun m : ℤ => c ^ 2 * (periodicSobolevWeight s m * ‖coeff φ m‖) ^ 2)
        (c ^ 2 * ‖φ‖ ^ 2) := h₂.mul_left _
    have hcmp := h₁.summable.tsum_le_tsum hterm hmul.summable
    rwa [hmul.tsum_eq] at hcmp
  have hnn : (0 : ℝ) ≤ c * ‖φ‖ := mul_nonneg hcpos.le (norm_nonneg φ)
  nlinarith [norm_nonneg (incl h φ - truncL s t F φ), hnn, hsq]

/-- **The inclusion is compact** when the drop in smoothness is strict (Atkinson–Han's
Proposition 7.5.5, second half). It is the operator-norm limit of its finite-rank truncations,
at the rate `(n + 1) ^ (t - s)`. -/
theorem isCompactOperator_inclL (h : t < s) : IsCompactOperator (inclL h.le) := by
  refine IsCompactOperator.of_tendsto
    (A := fun n : ℕ => truncL s t (Finset.Icc (-(n : ℤ)) (n : ℤ)))
    (fun n => isCompactOperator_truncL s t _) ?_
  have hbound : ∀ n : ℕ,
      ‖truncL s t (Finset.Icc (-(n : ℤ)) (n : ℤ)) - inclL h.le‖
        ≤ (((n : ℝ) + 1) ^ (s - t))⁻¹ := by
    intro n
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun φ => ?_
    rw [sub_apply, ← norm_neg, neg_sub, inclL_apply]
    exact norm_incl_sub_truncL_le h.le n φ
  have hnat : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hzero : Filter.Tendsto (fun n : ℕ => (((n : ℝ) + 1) ^ (s - t))⁻¹)
      Filter.atTop (𝓝 0) :=
    ((tendsto_rpow_atTop (by linarith : (0 : ℝ) < s - t)).comp hnat).inv_tendsto_atTop
  exact squeeze_zero (fun n => norm_nonneg _) hbound hzero

end PeriodicSobolev

/-! ### The characters of the circle, read on the line -/

/-- `periodicChar T m x = exp (2 π i m x / T)`, the `m`-th character of the circle of
circumference `T`, read as a function on the line. It is the `m`-th term of a Fourier series up to
the coefficient, and the only properties of it that the results below use are
`norm_periodicChar` and `sum_periodicChar`. -/
noncomputable def periodicChar (T : ℝ) (m : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (2 * (π : ℂ) * Complex.I * m * x / T)

theorem periodicChar_eq (T : ℝ) (m : ℤ) (x : ℝ) :
    periodicChar T m x = Complex.exp (((2 * π * m * x / T : ℝ) : ℂ) * Complex.I) := by
  rw [periodicChar]
  congr 1
  push_cast
  ring

/-- The characters have modulus one. -/
@[simp]
theorem norm_periodicChar (T : ℝ) (m : ℤ) (x : ℝ) : ‖periodicChar T m x‖ = 1 := by
  rw [periodicChar_eq, Complex.norm_exp_ofReal_mul_I]

@[simp]
theorem periodicChar_zero (T : ℝ) (x : ℝ) : periodicChar T 0 x = 1 := by
  simp [periodicChar]

theorem continuous_periodicChar (T : ℝ) (m : ℤ) : Continuous (periodicChar T m) :=
  Complex.continuous_exp.comp (by fun_prop)

/-- The characters have period `T`. -/
theorem periodicChar_periodic {T : ℝ} (hT : T ≠ 0) (m : ℤ) :
    Function.Periodic (periodicChar T m) T := by
  intro x
  have hT' : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hT
  rw [periodicChar, periodicChar, show 2 * (π : ℂ) * Complex.I * m * ((x + T : ℝ) : ℂ) / T
      = 2 * (π : ℂ) * Complex.I * m * x / T + (m : ℂ) * (2 * (π : ℂ) * Complex.I) by
    push_cast; field_simp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **(7.5.14)**: the trapezoidal sum of the `m`-th character over `k` equally spaced points of a
period is `k` when `k ∣ m` and `0` otherwise. This is the whole content of the quadrature bound: a
geometric sum of `k`-th roots of unity, degenerate exactly on the multiples of `k`. -/
theorem sum_periodicChar {T : ℝ} (hT : T ≠ 0) {k : ℕ} (hk : 0 < k) (m : ℤ) :
    ∑ j ∈ Finset.range k, periodicChar T m (((j : ℝ) + 1) * (T / (k : ℝ)))
      = if (k : ℤ) ∣ m then (k : ℂ) else 0 := by
  have hT' : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hT
  have hk' : ((k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  set ζ : ℂ := Complex.exp (2 * (π : ℂ) * Complex.I / (k : ℂ)) with hζdef
  have hprim : IsPrimitiveRoot ζ k := Complex.isPrimitiveRoot_exp k hk.ne'
  set z : ℂ := ζ ^ (m : ℤ) with hzdef
  have hterm : ∀ j : ℕ, periodicChar T m (((j : ℝ) + 1) * (T / (k : ℝ))) = z ^ (j + 1) := by
    intro j
    rw [hzdef, hζdef, ← Complex.exp_int_mul, periodicChar, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  have hzk : z ^ k = 1 := by
    rw [hzdef, hζdef, ← Complex.exp_int_mul, ← Complex.exp_nat_mul,
      show (k : ℂ) * ((m : ℂ) * (2 * (π : ℂ) * Complex.I / (k : ℂ)))
        = (m : ℂ) * (2 * (π : ℂ) * Complex.I) by field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I m
  by_cases hdvd : (k : ℤ) ∣ m
  · have hz1 : z = 1 := (hprim.zpow_eq_one_iff_dvd m).2 hdvd
    rw [ite_eq_left hdvd]
    simp [hz1]
  · have hz1 : z ≠ 1 := fun h => hdvd ((hprim.zpow_eq_one_iff_dvd m).1 h)
    rw [ite_eq_right hdvd]
    have hgeom : ∑ j ∈ Finset.range k, z ^ (j + 1) = z * ∑ j ∈ Finset.range k, z ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hgeom, geom_sum_eq hz1, hzk, sub_self, zero_div, mul_zero]

/-! ### The sum of the series, and the trapezoidal rule -/

namespace PeriodicSobolev

variable {s : ℝ}

/-- The sum of the Fourier series of `φ`, read with period `T`: `∑_m a_m exp (2 π i m x / T)`.
For `s > 1/2` the coefficients are absolutely summable, so the series converges uniformly and
`eval T φ` is a continuous function of period `T`; for smaller `s` the definition is junk. The
period is a parameter of this bridge to functions, not of the space. -/
noncomputable def eval (T : ℝ) (φ : PeriodicSobolev s) (x : ℝ) : ℂ :=
  ∑' m : ℤ, coeff φ m * periodicChar T m x

theorem summable_eval (hs : 1 / 2 < s) (T : ℝ) (φ : PeriodicSobolev s) (x : ℝ) :
    Summable fun m : ℤ => coeff φ m * periodicChar T m x :=
  Summable.of_norm ((summable_norm_coeff hs φ).congr fun m => by
    rw [norm_mul, norm_periodicChar, mul_one])

theorem hasSum_eval (hs : 1 / 2 < s) (T : ℝ) (φ : PeriodicSobolev s) (x : ℝ) :
    HasSum (fun m : ℤ => coeff φ m * periodicChar T m x) (eval T φ x) :=
  (summable_eval hs T φ x).hasSum

/-- The characters have modulus one, so the sum of the series is bounded by the sum of the moduli
of the coefficients. Every uniform bound on `eval` factors through this one. -/
theorem norm_eval_le_tsum_norm_coeff (hs : 1 / 2 < s) (T : ℝ) (φ : PeriodicSobolev s) (x : ℝ) :
    ‖eval T φ x‖ ≤ ∑' m : ℤ, ‖coeff φ m‖ := by
  refine le_trans (norm_tsum_le_tsum_norm ((summable_norm_coeff hs φ).congr fun m => by
    rw [norm_mul, norm_periodicChar, mul_one])) (le_of_eq (tsum_congr fun m => ?_))
  rw [norm_mul, norm_periodicChar, mul_one]

/-- **Atkinson–Han's Proposition 7.5.4 at `k = 0`, the bound (7.5.11)**: for `s > 1/2` the sum of
the series is bounded by `(1 + √(2 ζ(2 s))) ‖φ‖` uniformly in `x`, so the embedding of
`PeriodicSobolev s` into the bounded functions is continuous. -/
theorem norm_eval_le (hs : 1 / 2 < s) (T : ℝ) (φ : PeriodicSobolev s) (x : ℝ) :
    ‖eval T φ x‖ ≤ (1 + √(2 * zetaReal (2 * s))) * ‖φ‖ :=
  (norm_eval_le_tsum_norm_coeff hs T φ x).trans (tsum_norm_coeff_le' hs φ)

/-- The sum of the series is continuous: the convergence is uniform. Together with
`eval_periodic` this is the statement `φ ∈ C_p(T)` of Proposition 7.5.4. -/
theorem continuous_eval (hs : 1 / 2 < s) (T : ℝ) (φ : PeriodicSobolev s) :
    Continuous (eval T φ) :=
  continuous_tsum (fun m => continuous_const.mul (continuous_periodicChar T m))
    (summable_norm_coeff hs φ) fun m x => by rw [norm_mul, norm_periodicChar, mul_one]

/-- The sum of the series has period `T`. -/
theorem eval_periodic {T : ℝ} (hT : T ≠ 0) (φ : PeriodicSobolev s) :
    Function.Periodic (eval T φ) T := fun x =>
  tsum_congr fun m => by rw [periodicChar_periodic hT m x]

/-! #### The integral over a period -/

/-- The integral of the sum over one period picks out the constant term: `∫_0^T φ = T a₀`. -/
theorem intervalIntegral_eval (hs : 1 / 2 < s) {T : ℝ} (hT : 0 < T) (φ : PeriodicSobolev s) :
    (∫ x in (0 : ℝ)..T, eval T φ x) = T * coeff φ 0 := by
  have hvol : (MeasureTheory.volume.real (Set.Ioc (0 : ℝ) T)) = T := by
    rw [MeasureTheory.measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hT.le]
  have hint : ∀ m : ℤ, MeasureTheory.IntegrableOn
      (fun x : ℝ => coeff φ m * periodicChar T m x) (Set.Ioc 0 T) := fun m =>
    (continuous_const.mul (continuous_periodicChar T m)).integrableOn_Ioc
  have hnorm : ∀ m : ℤ, (∫ x in Set.Ioc (0 : ℝ) T, ‖coeff φ m * periodicChar T m x‖)
      = ‖coeff φ m‖ * T := by
    intro m
    simp only [norm_mul, norm_periodicChar, mul_one]
    rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul, mul_comm]
  have hsum := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (μ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) T))
    (F := fun (m : ℤ) (x : ℝ) => coeff φ m * periodicChar T m x) hint
    (((summable_norm_coeff hs φ).mul_right T).congr fun m => (hnorm m).symm)
  have hterm : ∀ m : ℤ, (∫ x in Set.Ioc (0 : ℝ) T, coeff φ m * periodicChar T m x)
      = if m = 0 then (T : ℂ) * coeff φ 0 else 0 := by
    intro m
    rw [← intervalIntegral.integral_of_le hT.le]
    rcases eq_or_ne m 0 with rfl | hm
    · rw [ite_eq_left rfl]
      simp only [periodicChar_zero, mul_one, intervalIntegral.integral_const, sub_zero]
      simp [Complex.real_smul]
    · rw [ite_eq_right hm]
      have hT' : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hT.ne'
      have hc : (2 * (π : ℂ) * Complex.I * m / T) ≠ 0 := by
        refine div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_)
          Complex.I_ne_zero) ?_) hT'
        · exact_mod_cast Real.pi_ne_zero
        · exact_mod_cast hm
      have hrw : ∀ x : ℝ, coeff φ m * periodicChar T m x
          = coeff φ m * Complex.exp ((2 * (π : ℂ) * Complex.I * m / T) * x) := by
        intro x
        rw [periodicChar]
        ring_nf
      rw [intervalIntegral.integral_congr (g := fun x : ℝ => coeff φ m *
          Complex.exp ((2 * (π : ℂ) * Complex.I * m / T) * x)) fun x _ => hrw x,
        intervalIntegral.integral_const_mul, integral_exp_mul_complex hc,
        show (2 * (π : ℂ) * Complex.I * m / T) * (T : ℂ)
          = (m : ℂ) * (2 * (π : ℂ) * Complex.I) by field_simp,
        Complex.exp_int_mul_two_pi_mul_I]
      simp
  rw [funext hterm] at hsum
  rw [intervalIntegral.integral_of_le hT.le]
  exact ((hasSum_ite_eq (0 : ℤ) ((T : ℂ) * coeff φ 0)).unique hsum).symm

/-! #### The trapezoidal rule -/

/-- **The trapezoidal rule for a `T`-periodic integrand**: `h ∑_{j = 1}^{k} f (j h)` with
`h = T / k`. For a periodic `f` the two endpoints of the interval carry the same value, so the
usual half weights at the ends merge into one full weight and the rule is a plain equally
weighted sum. -/
noncomputable def trapezoidSum (T : ℝ) (k : ℕ) (f : ℝ → ℂ) : ℂ :=
  ((T / (k : ℝ) : ℝ) : ℂ) * ∑ j ∈ Finset.range k, f (((j : ℝ) + 1) * (T / (k : ℝ)))

/-- The trapezoidal sum of a Fourier series is `T` times the sum of its coefficients along the
multiples of `k` — the aliasing formula behind Proposition 7.5.6. -/
theorem trapezoidSum_eval (hs : 1 / 2 < s) {T : ℝ} (hT : T ≠ 0) {k : ℕ} (hk : 0 < k)
    (φ : PeriodicSobolev s) :
    trapezoidSum T k (eval T φ) = T * ∑' j : ℤ, coeff φ (j * k) := by
  classical
  have hk' : ((k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  set g : ℤ → ℂ := fun m => if (k : ℤ) ∣ m then coeff φ m else 0 with hgdef
  have hsub : Function.support g ⊆ Set.range fun j : ℤ => j * (k : ℤ) := by
    intro m hm
    by_cases hd : (k : ℤ) ∣ m
    · obtain ⟨d, rfl⟩ := hd
      exact ⟨d, by ring⟩
    · exact absurd (show g m = 0 by simp [hgdef, hd]) (Function.mem_support.1 hm)
  have hstep : HasSum (fun m : ℤ => (k : ℂ) * g m)
      (∑ j ∈ Finset.range k, eval T φ (((j : ℝ) + 1) * (T / (k : ℝ)))) := by
    have h := hasSum_sum (s := Finset.range k)
      (f := fun (j : ℕ) (m : ℤ) => coeff φ m * periodicChar T m (((j : ℝ) + 1) * (T / (k : ℝ))))
      (a := fun j : ℕ => eval T φ (((j : ℝ) + 1) * (T / (k : ℝ))))
      fun j _ => hasSum_eval hs T φ _
    refine h.congr_fun fun m => ?_
    rw [← Finset.mul_sum, sum_periodicChar hT hk m, hgdef]
    by_cases hd : (k : ℤ) ∣ m <;> simp [hd, mul_comm]
  have hgsum : ∑' m : ℤ, g m = ∑' j : ℤ, coeff φ (j * k) := by
    refine ((injective_mul_natCast hk).tsum_eq hsub).symm.trans (tsum_congr fun j => ?_)
    simp only [hgdef]
    rw [ite_eq_left (dvd_mul_left (k : ℤ) j)]
  rw [trapezoidSum, ← hstep.tsum_eq, tsum_mul_left, hgsum]
  push_cast
  field_simp

/-- **Atkinson–Han's Proposition 7.5.6**: the trapezoidal rule is spectrally accurate on a smooth
periodic integrand. For `s > 1/2` and `φ ∈ PeriodicSobolev s`,

`|I(φ) − T_k(φ)| ≤ T k^{-s} √(2 ζ(2 s)) ‖φ‖`,

which for the book's period `T = 2 π` is `√(4 π ζ(2 s)) k^{-s} ‖φ‖`, the bound (7.5.13). The error
is exactly `−T` times the aliasing tail `∑_{j ≠ 0} a_{j k}`, by (7.5.14), and Cauchy–Schwarz along
the multiples of `k` bounds that tail. -/
theorem norm_intervalIntegral_sub_trapezoidSum_le (hs : 1 / 2 < s) {T : ℝ} (hT : 0 < T)
    {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) :
    ‖(∫ x in (0 : ℝ)..T, eval T φ x) - trapezoidSum T k (eval T φ)‖
      ≤ T * ((k : ℝ) ^ (-s) * √(2 * zetaReal (2 * s)) * ‖φ‖) := by
  have hnormtail : ∀ j : ℤ, ‖(if j = 0 then (0 : ℂ) else coeff φ (j * k))‖
      = if j = 0 then (0 : ℝ) else ‖coeff φ (j * k)‖ := by
    intro j
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · simp [hj]
  have htailnorm : Summable fun j : ℤ => ‖(if j = 0 then (0 : ℂ) else coeff φ (j * k))‖ :=
    (summable_norm_coeff_mul hs hk φ).congr fun j => (hnormtail j).symm
  have htailsum : Summable fun j : ℤ => (if j = 0 then (0 : ℂ) else coeff φ (j * k)) :=
    Summable.of_norm htailnorm
  have hS : Summable fun j : ℤ => coeff φ (j * k) :=
    (summable_coeff hs φ).comp_injective (injective_mul_natCast hk)
  have hsplit : ∑' j : ℤ, coeff φ (j * k)
      = coeff φ 0 + ∑' j : ℤ, (if j = 0 then (0 : ℂ) else coeff φ (j * k)) := by
    refine hS.hasSum.unique ?_
    refine ((hasSum_ite_eq (0 : ℤ) (coeff φ 0)).add htailsum.hasSum).congr_fun fun j => ?_
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · simp [hj]
  rw [intervalIntegral_eval hs hT φ, trapezoidSum_eval hs hT.ne' hk φ, hsplit,
    show (T : ℂ) * coeff φ 0 - (T : ℂ) * (coeff φ 0 +
        ∑' j : ℤ, (if j = 0 then (0 : ℂ) else coeff φ (j * k)))
      = -((T : ℂ) * ∑' j : ℤ, (if j = 0 then (0 : ℂ) else coeff φ (j * k))) by ring,
    norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hT.le]
  refine mul_le_mul_of_nonneg_left ?_ hT.le
  exact le_trans (norm_tsum_le_tsum_norm htailnorm)
    (le_trans (le_of_eq (tsum_congr hnormtail)) (tsum_norm_coeff_mul_le hs hk φ))

end PeriodicSobolev

/-! ### Density of the coordinate series, and the duality pairing -/

/-- The weights at opposite exponents are reciprocal. This is why `PeriodicSobolev (-t)` is the
dual of `PeriodicSobolev t`. -/
theorem periodicSobolevWeight_mul_neg (t : ℝ) (m : ℤ) :
    periodicSobolevWeight t m * periodicSobolevWeight (-t) m = 1 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [periodicSobolevWeight_of_ne_zero t hm, periodicSobolevWeight_of_ne_zero (-t) hm,
      ← Real.rpow_add (abs_pos.2 (Int.cast_ne_zero.2 hm)), add_neg_cancel, Real.rpow_zero]

namespace PeriodicSobolev

variable {s t : ℝ}

/-- **The trigonometric polynomials are dense in `PeriodicSobolev s` for every real `s`**: the
finite linear combinations of the coordinate series `basisElt s m`. In a Hilbert space it is
enough that nothing is orthogonal to them. -/
theorem dense_span_basisElt (s : ℝ) :
    Dense ((Submodule.span ℂ (Set.range (basisElt s)) : Submodule ℂ (PeriodicSobolev s)) :
      Set (PeriodicSobolev s)) := by
  refine Submodule.dense_iff_topologicalClosure_eq_top.2
    (Submodule.topologicalClosure_eq_top_iff.2 (Submodule.eq_bot_iff _ |>.2 fun ρ hρ => ?_))
  refine eq_zero_of_inner_basisElt_eq_zero fun m => ?_
  exact Submodule.mem_orthogonal _ _ |>.1 hρ _ (Submodule.subset_span ⟨m, rfl⟩)

/-! #### The duality pairing -/

theorem norm_toLp_mul_norm_toLp (t : ℝ) (φ : PeriodicSobolev t) (η : PeriodicSobolev (-t))
    (m : ℤ) : ‖toLp t φ m‖ * ‖toLp (-t) η m‖ = ‖coeff φ m * conj (coeff η m)‖ := by
  rw [norm_toLp_apply, norm_toLp_apply, norm_mul, RCLike.norm_conj]
  calc periodicSobolevWeight t m * ‖coeff φ m‖ * (periodicSobolevWeight (-t) m * ‖coeff η m‖)
      = (periodicSobolevWeight t m * periodicSobolevWeight (-t) m)
        * (‖coeff φ m‖ * ‖coeff η m‖) := by ring
    _ = ‖coeff φ m‖ * ‖coeff η m‖ := by rw [periodicSobolevWeight_mul_neg, one_mul]

/-- **(7.5.6)–(7.5.7), the duality pairing.** The coefficient sum `∑_m a_m conj (b_m)` converges
absolutely for `φ ∈ PeriodicSobolev t` and `η ∈ PeriodicSobolev (-t)`. -/
theorem summable_coeff_mul_conj (t : ℝ) (φ : PeriodicSobolev t) (η : PeriodicSobolev (-t)) :
    Summable fun m : ℤ => coeff φ m * conj (coeff η m) := by
  have hpq : ((2 : ℝ≥0∞).toReal).HolderConjugate ((2 : ℝ≥0∞).toReal) := by
    simpa using Real.HolderConjugate.two_two
  obtain ⟨hsum, -⟩ := lp.tsum_mul_le_mul_norm hpq (toLp t φ) (toLp (-t) η)
  exact Summable.of_norm (hsum.congr fun m => norm_toLp_mul_norm_toLp t φ η m)

/-- **(7.5.7)**: `|⟨φ, η⟩| ≤ ‖φ‖_{*,t} ‖η‖_{*,-t}`. -/
theorem norm_tsum_coeff_mul_conj_le (t : ℝ) (φ : PeriodicSobolev t) (η : PeriodicSobolev (-t)) :
    ‖∑' m : ℤ, coeff φ m * conj (coeff η m)‖ ≤ ‖φ‖ * ‖η‖ := by
  have hpq : ((2 : ℝ≥0∞).toReal).HolderConjugate ((2 : ℝ≥0∞).toReal) := by
    simpa using Real.HolderConjugate.two_two
  obtain ⟨hsum, hle⟩ := lp.tsum_mul_le_mul_norm hpq (toLp t φ) (toLp (-t) η)
  rw [funext fun m => norm_toLp_mul_norm_toLp t φ η m] at hsum hle
  rw [norm_toLp, norm_toLp] at hle
  exact (norm_tsum_le_tsum_norm hsum).trans hle

/-- **The dual pairing as a bounded linear functional**: every `η ∈ PeriodicSobolev (-t)` acts on
`PeriodicSobolev t` by `φ ↦ ∑_m a_m conj (b_m)`, with norm at most `‖η‖`. -/
noncomputable def dualPairing (t : ℝ) (η : PeriodicSobolev (-t)) : PeriodicSobolev t →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun φ => ∑' m : ℤ, coeff φ m * conj (coeff η m)
      map_add' := fun φ ρ => by
        rw [← (summable_coeff_mul_conj t φ η).tsum_add (summable_coeff_mul_conj t ρ η)]
        exact tsum_congr fun m => by simp [add_mul]
      map_smul' := fun c φ => by
        rw [RingHom.id_apply, smul_eq_mul, ← tsum_mul_left]
        exact tsum_congr fun m => by simp [mul_assoc] }
    ‖η‖ fun φ => by
      rw [mul_comm]
      exact norm_tsum_coeff_mul_conj_le t φ η

@[simp]
theorem dualPairing_apply (t : ℝ) (η : PeriodicSobolev (-t)) (φ : PeriodicSobolev t) :
    dualPairing t η φ = ∑' m : ℤ, coeff φ m * conj (coeff η m) := rfl

/-- The functional attached to `eta` has norm at most that of `eta`; with the Riesz representation
this makes `PeriodicSobolev (-t)` the dual of `PeriodicSobolev t`. -/
theorem norm_dualPairing_le (t : ℝ) (η : PeriodicSobolev (-t)) : ‖dualPairing t η‖ ≤ ‖η‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg η) _

end PeriodicSobolev
