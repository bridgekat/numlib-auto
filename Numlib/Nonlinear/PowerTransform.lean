/-
Upstreaming candidate: real-power divided differences and Newton steps for power transforms.
Natural homes: Mathlib.Analysis.SpecialFunctions.Pow and numerical root-finding APIs.
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# Newton steps for real-power transforms

The quotient `(1 - μ^β)/β`, with value `-log μ` at zero, is antitone in `β` for every
positive `μ`. Convexity of the exponential supplies the secant-slope comparison, including
slopes across zero; differentiability supplies continuity at the removable singularity.
For a positive scalar function with negative derivative, the Newton step for its power
transform is a positive multiple of this quotient. The logarithmic equation is used at
exponent zero, and the denominator is proved nonzero at every exponent.
-/

open Set

namespace Real
/-- The normalized power difference, extended to its logarithmic value at exponent zero. -/
noncomputable def normalizedRpowDifference (μ β : ℝ) : ℝ :=
  if β = 0 then -log μ else (1 - μ ^ β) / β

/-- Convexity of the exponential makes the extended power quotient antitone. -/
theorem antitone_normalizedRpowDifference {μ : ℝ} (hμ : 0 < μ) :
    Antitone (normalizedRpowDifference μ) := by
  have hf : ConvexOn ℝ univ (fun β : ℝ => exp (β * log μ)) := by
    simpa only [Set.preimage_univ, Function.comp_def, LinearMap.coe_smulRight,
      LinearMap.id_coe, id_eq, smul_eq_mul] using
      convexOn_exp.comp_linearMap ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (log μ))
  intro a b hab
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b; exact le_rfl
    have hbpos : 0 < b := lt_of_le_of_ne hab (Ne.symm hb)
    rw [normalizedRpowDifference, normalizedRpowDifference, ite_eq_right hb, ite_eq_left rfl,
      div_le_iff₀ hbpos, rpow_def_of_pos hμ]
    have he := add_one_le_exp (log μ * b)
    nlinarith
  · by_cases hb : b = 0
    · subst b
      have haneg : a < 0 := lt_of_le_of_ne hab ha
      rw [normalizedRpowDifference, normalizedRpowDifference, ite_eq_left rfl, ite_eq_right ha,
        le_div_iff_of_neg haneg, rpow_def_of_pos hμ]
      have he := add_one_le_exp (log μ * a)
      nlinarith
    · have h := hf.secant_mono (a := 0) (by trivial) (by trivial) (by trivial) ha hb hab
      simp only [zero_mul, exp_zero, sub_zero] at h
      rw [normalizedRpowDifference, normalizedRpowDifference, ite_eq_right hb, ite_eq_right ha,
        rpow_def_of_pos hμ, rpow_def_of_pos hμ]
      have heq (z : ℝ) : (1 - exp (z * log μ)) / z = -((exp (z * log μ) - 1) / z) := by ring
      rw [mul_comm (log μ) b, mul_comm (log μ) a, heq, heq]
      exact neg_le_neg h
/-- The removable value at zero exponent. -/
@[simp] theorem normalizedRpowDifference_zero (μ : ℝ) : normalizedRpowDifference μ 0 = -log μ := by
  simp [normalizedRpowDifference]
/-- The logarithmic value is the continuous extension of the nonzero-exponent quotient. -/
theorem continuousAt_normalizedRpowDifference_zero {μ : ℝ} (hμ : 0 < μ) :
    ContinuousAt (normalizedRpowDifference μ) 0 := by
  have hd : HasDerivAt (fun β : ℝ => exp (log μ * β)) (log μ) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_mul (log μ)).exp) using 1 <;> simp
  have hc := hd.continuousAt_div.neg
  convert hc using 1
  funext β
  by_cases hβ : β = 0
  · subst β; simp [normalizedRpowDifference]
  · simp only [normalizedRpowDifference, ite_eq_right hβ, Pi.neg_apply, Function.update_of_ne hβ,
      mul_zero, exp_zero, sub_zero]
    rw [rpow_def_of_pos hμ]
    ring
/-- The power-transformed scalar equation, with its logarithmic version at exponent zero. -/
noncomputable def powerTransformDifference (f : ℝ → ℝ) (τ β z : ℝ) : ℝ :=
  if β = 0 then log (f z) - log τ else f z ^ β - τ ^ β

/-- Exact Newton step for a power-transformed equation, including the logarithmic exponent. -/
theorem newton_powerTransformDifference {f : ℝ → ℝ} {τ c d : ℝ}
    (hf : HasDerivAt f d c) (hτ : 0 < τ) (hx : 0 < f c) (hd : d ≠ 0) (β : ℝ) :
    -(powerTransformDifference f τ β c) / deriv (powerTransformDifference f τ β) c =
      (-f c / d) * normalizedRpowDifference (τ / f c) β := by
  by_cases hβ : β = 0
  · subst β
    have heq : powerTransformDifference f τ 0 = fun z => log (f z) - log τ := by
      funext z; simp [powerTransformDifference]
    rw [heq, (hf.log hx.ne').sub_const (log τ) |>.deriv,
      normalizedRpowDifference_zero, log_div hτ.ne' hx.ne']
    field_simp
    ring
  · have heq : powerTransformDifference f τ β = fun z => f z ^ β - τ ^ β := by
      funext z; simp [powerTransformDifference, hβ]
    rw [heq, (hf.rpow_const (Or.inl hx.ne')).sub_const (τ ^ β) |>.deriv,
      normalizedRpowDifference, ite_eq_right hβ,
      div_rpow hτ.le hx.le β, rpow_sub hx, rpow_one]
    have hp : f c ^ β ≠ 0 := (rpow_pos_of_pos hx β).ne'
    field_simp
end Real

namespace Real
/-- At a positive value and negative derivative, power-transformed Newton steps decrease
with the exponent. -/
theorem antitone_newton_powerTransformDifference {f : ℝ → ℝ} {τ c d : ℝ}
    (hf : HasDerivAt f d c) (hτ : 0 < τ) (hx : 0 < f c) (hd : d < 0) :
    Antitone (fun β : ℝ =>
      -(powerTransformDifference f τ β c) / deriv (powerTransformDifference f τ β) c) := by
  intro a b hab
  dsimp only
  rw [newton_powerTransformDifference hf hτ hx hd.ne a,
    newton_powerTransformDifference hf hτ hx hd.ne b]
  exact mul_le_mul_of_nonneg_left
    (antitone_normalizedRpowDifference (div_pos hτ hx) hab)
    (div_pos_of_neg_of_neg (neg_neg_of_pos hx) hd).le
end Real

namespace Real
/-- At nonzero exponents the extended quotient is the ordinary quotient. -/
@[simp] theorem normalizedRpowDifference_of_ne (μ : ℝ) {β : ℝ} (hβ : β ≠ 0) :
    normalizedRpowDifference μ β = (1 - μ ^ β) / β := by
  simp [normalizedRpowDifference, hβ]
/-- The zero-exponent equation is logarithmic. -/
@[simp] theorem powerTransformDifference_zero (f : ℝ → ℝ) (τ z : ℝ) :
    powerTransformDifference f τ 0 z = log (f z) - log τ := by
  simp [powerTransformDifference]
/-- At nonzero exponents the residual is the usual difference of real powers. -/
theorem powerTransformDifference_of_ne (f : ℝ → ℝ) (τ z : ℝ) {β : ℝ} (hβ : β ≠ 0) :
    powerTransformDifference f τ β z = f z ^ β - τ ^ β := by
  simp [powerTransformDifference, hβ]
/-- Every power-transformed Newton denominator is nonzero when the original value is
positive and its derivative is nonzero. -/
theorem deriv_powerTransformDifference_ne_zero {f : ℝ → ℝ} {τ c d : ℝ}
    (hf : HasDerivAt f d c) (hx : 0 < f c) (hd : d ≠ 0) (β : ℝ) :
    deriv (powerTransformDifference f τ β) c ≠ 0 := by
  by_cases hβ : β = 0
  · subst β
    have heq : powerTransformDifference f τ 0 = fun z => log (f z) - log τ := by
      funext z; simp [powerTransformDifference]
    rw [heq, (hf.log hx.ne').sub_const (log τ) |>.deriv]
    exact div_ne_zero hd hx.ne'
  · have heq : powerTransformDifference f τ β = fun z => f z ^ β - τ ^ β := by
      funext z; simp [powerTransformDifference, hβ]
    rw [heq, (hf.rpow_const (Or.inl hx.ne')).sub_const (τ ^ β) |>.deriv]
    exact mul_ne_zero (mul_ne_zero hd hβ) (rpow_pos_of_pos hx _).ne'
end Real
