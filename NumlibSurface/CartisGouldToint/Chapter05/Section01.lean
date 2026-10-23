import Numlib.Analysis.SpecialFunctions.Pow.Differences
import Numlib.Data.Nat.Factorization
import Numlib.Optimization.LeastSquares.Powers

/-!
# Cartis–Gould–Toint, Section 5.1: residual powers

The residual-power analysis uses increments of cascading dyadic powers and the unique
odd factorization of a positive integer. Lemma 5.1.3 retains the quotient form and all
integer exponents from the source, with the zero case interpreted by real division.
-/

namespace CartisGouldToint

/-- Cartis–Gould–Toint, Lemma 5.1.3: cascading differences of nonnegative
ordered numbers, with all dyadic and integer powers written explicitly.
When `a = b = 0`, the quotient is interpreted by real division. -/
theorem lemma_5_1_3 {a b : ℝ} (hba : b ≤ a) (hb : 0 ≤ b)
    (i ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (a ^ ℓ - b ^ ℓ) /
        ((2 : ℝ) ^ i * (ℓ : ℝ) *
          a ^ (((2 : ℝ) ^ i - 1) / (2 : ℝ) ^ i + (ℓ : ℝ) - 1)) ≤
      a ^ (1 / (2 : ℝ) ^ i) - b ^ (1 / (2 : ℝ) ^ i) := by
  have hpow : (0 : ℝ) < 2 ^ i := pow_pos (by norm_num) i
  have hpow1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  have hq : (0 : ℝ) < 1 / 2 ^ i := one_div_pos.mpr hpow
  have hqp : (1 : ℝ) / 2 ^ i ≤ (ℓ : ℝ) := by
    calc
      (1 : ℝ) / 2 ^ i ≤ 1 := (div_le_one hpow).mpr hpow1
      _ ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have h := Real.rpow_sub_div_le_rpow_sub hb hba hq hqp
  rw [Real.rpow_natCast, Real.rpow_natCast] at h
  have he : (ℓ : ℝ) - 1 / (2 : ℝ) ^ i =
      ((2 : ℝ) ^ i - 1) / (2 : ℝ) ^ i + (ℓ : ℝ) - 1 := by
    field_simp
    ring
  rw [he] at h
  simpa [div_div, mul_comm] using h

/-- **Lemma 5.1.5 (odd factorization).** Each positive natural number has a
unique representation as an odd positive integer times a power of two. The book's
`ℕ` excludes zero; the hypothesis `0 < p` makes that convention explicit. -/
theorem lemma_5_1_5 {p : ℕ} (hp : 0 < p) :
    ∃! z : ℕ × ℕ, Odd z.1 ∧ 0 < z.1 ∧ p = z.1 * 2 ^ z.2 :=
  Nat.existsUnique_odd_mul_two_pow hp

/-- The residual-power objective (5.1.3), with real exponent `ℓ`:
`Φ_ℓ(x) = ‖r(x)‖^ℓ / ℓ`. The optimization model uses positive exponents. -/
noncomputable def residualPowerObjective {E F : Type*} [NormedAddCommGroup F]
    (r : E → F) (ℓ : ℝ) (x : E) : ℝ := LeastSquares.powerObjective r ℓ x

/-- Evaluation of the residual-power objective. -/
@[simp]
theorem residualPowerObjective_apply {E F : Type*} [NormedAddCommGroup F]
    (r : E → F) (ℓ : ℝ) (x : E) :
    residualPowerObjective r ℓ x = ‖r x‖ ^ ℓ / ℓ := rfl

/-- The exponent-one residual objective is the residual norm. -/
@[simp]
theorem residualPowerObjective_one {E F : Type*} [NormedAddCommGroup F]
    (r : E → F) (x : E) : residualPowerObjective r 1 x = ‖r x‖ :=
  LeastSquares.powerObjective_one r x

/-- The exponent-two residual objective is the least-squares objective. -/
@[simp]
theorem residualPowerObjective_two {E F : Type*} [NormedAddCommGroup F]
    (r : E → F) (x : E) : residualPowerObjective r 2 x = ‖r x‖ ^ 2 / 2 :=
  LeastSquares.powerObjective_two r x

/-- **Lemma 5.1.1 (smoothness of residual powers).** A `C^p` residual has a `C^p`
residual-power objective whenever the positive exponent is an even integer or
is a real number strictly larger than `2p`. Both cases include residual zeros. -/
theorem lemma_5_1_1 {n m p : ℕ}
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {ℓ : ℝ}
    (hr : ContDiff ℝ p r) (_hℓ : 0 < ℓ)
    (hcase : (∃ q : ℕ, ℓ = 2 * (q : ℝ)) ∨ 2 * (p : ℝ) < ℓ) :
    ContDiff ℝ p (residualPowerObjective r ℓ) := by
  rcases hcase with ⟨q,rfl⟩ | hlarge
  · exact LeastSquares.contDiff_powerObjective_even hr q
  · exact LeastSquares.contDiff_powerObjective_of_two_mul_le hr hlarge.le

end CartisGouldToint
