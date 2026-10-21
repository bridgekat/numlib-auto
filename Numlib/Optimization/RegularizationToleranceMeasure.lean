import Numlib.Optimization.HigherOrderApproximateRegularizationBounds

/-!
# Common-tolerance bounds for regularization rates

The simultaneous tolerance scale controls every requested order. A common positive lower
tolerance gives a simpler single-power bound, using monotonicity of the two complexity
exponent families. These scalar facts do not require an objective or an algorithmic run.
-/

noncomputable section
namespace Optimization.HigherOrderApproximateRegularization

/-- The complexity exponent is nonnegative, including all natural boundary indices. -/
theorem complexityExponent_nonneg (p q j : ℕ) : 0 ≤ complexityExponent p q j := by
  unfold complexityExponent
  split_ifs <;> positivity

/-- Positive model degree and tested order give a strictly positive complexity exponent. -/
theorem complexityExponent_pos {p q j : ℕ} (hp : 0 < p) (hj : 0 < j) :
    0 < complexityExponent p q j := by
  unfold complexityExponent
  split_ifs
  · positivity
  · have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have hj' : (0 : ℝ) < j := by exact_mod_cast hj
    positivity

/-- Both regularization complexity exponent families are monotone in the tested order. -/
theorem complexityExponent_monotone (p q : ℕ) : Monotone (complexityExponent p q) := by
  intro i j hij
  unfold complexityExponent
  split_ifs
  · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact_mod_cast (show p - j + 1 ≤ p - i + 1 by omega)
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) (by positivity)

/-- A common tolerance in the unit interval bounds the full simultaneous scale from below
by the largest active complexity exponent. No relation between the natural orders is needed. -/
theorem common_rpow_le_toleranceMeasure (p q : ℕ) (hq : 1 ≤ q)
    {epsilon : ℕ → ℝ} {e : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (helower : ∀ j, 1 ≤ j → j ≤ q → e ≤ epsilon j) :
    e ^ complexityExponent p q q ≤ toleranceMeasure p q hq epsilon := by
  apply Finset.le_inf'
  intro j hj
  have hbounds := Finset.mem_Icc.mp hj
  exact (Real.rpow_le_rpow_of_exponent_ge he he1
    (complexityExponent_monotone p q hbounds.2)).trans
    (Real.rpow_le_rpow he.le (helower j hbounds.1 hbounds.2)
      (complexityExponent_nonneg p q j))

/-- A nonnegative objective gap divided by the simultaneous scale is bounded by the common
positive tolerance's largest active inverse power. -/
theorem div_toleranceMeasure_le_common_rpow (p q : ℕ) (hq : 1 ≤ q)
    {epsilon : ℕ → ℝ} {e gap : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (helower : ∀ j, 1 ≤ j → j ≤ q → e ≤ epsilon j) (hgap : 0 ≤ gap) :
    gap / toleranceMeasure p q hq epsilon ≤ gap / e ^ complexityExponent p q q :=
  div_le_div_of_nonneg_left hgap (Real.rpow_pos_of_pos he _)
    (common_rpow_le_toleranceMeasure p q hq he he1 helower)

/-- A polynomial-plus-logarithm evaluation budget on the unit tolerance interval obeys
a pure inverse-power bound with fixed positive-exponent coefficients. This reuses the
standard logarithm-times-power inequality, with no asymptotic assumption. -/
theorem logarithmic_budget_le_common_rpow {e alpha A B C gap : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (halpha : 0 < alpha)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hgap : 0 ≤ gap) :
    A * gap / e ^ alpha + B * |Real.log e| + C ≤
      (A + B / alpha + C) * (gap + 1) / e ^ alpha := by
  have hpow := Real.rpow_pos_of_pos he alpha
  have hpow1 := Real.rpow_le_one he.le he1 halpha.le
  have hlog : |Real.log e| ≤ (1 / alpha) / e ^ alpha := by
    apply (le_div_iff₀ hpow).mpr
    simpa only [abs_mul, abs_of_pos hpow] using
      (Real.abs_log_mul_self_rpow_lt e alpha he he1 halpha).le
  have hlogB : B * |Real.log e| ≤ (B / alpha) / e ^ alpha := by
    convert mul_le_mul_of_nonneg_left hlog hB using 1
    ring
  have hconstant : C ≤ C / e ^ alpha := by
    apply (le_div_iff₀ hpow).mpr
    nlinarith only [hC, hpow1]
  have hnum : A * gap + B / alpha + C ≤ (A + B / alpha + C) * (gap + 1) := by
    nlinarith only [hA, mul_nonneg (div_nonneg hB halpha.le) hgap, mul_nonneg hC hgap]
  calc
    _ ≤ A * gap / e ^ alpha + (B / alpha) / e ^ alpha + C / e ^ alpha :=
      add_le_add (add_le_add le_rfl hlogB) hconstant
    _ = (A * gap + B / alpha + C) / e ^ alpha := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hnum hpow.le

end Optimization.HigherOrderApproximateRegularization
