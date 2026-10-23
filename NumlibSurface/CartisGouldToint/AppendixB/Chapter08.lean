import Numlib.Nonlinear.PowerTransform

/-!
# Cartis–Gould–Toint, Appendix B.8: transformed secular Newton steps

Lemma B.8.2 is stated for every differentiable scalar function with positive value and
negative derivative at the current point. These are the properties of the nondegenerate
secular function needed by its proof; a root or a position relative to that root is unnecessary.
For nonzero exponent the residual is exactly `π^β - (Δ²)^β = π^β - Δ^(2β)`.
At exponent zero that residual is identically zero, so the logarithmic residual is used
instead. Its Newton step is the continuous extension of the steps at nonzero exponents.
-/

namespace CartisGouldToint

/-- The transformed secular step (B.8.7), with its removable value `-A log μ` at `β = 0`. -/
noncomputable def transformedSecularStep (A μ β : ℝ) : ℝ :=
  A * Real.normalizedRpowDifference μ β

/-- The explicit nonzero-exponent expression in (B.8.7). -/
theorem transformedSecularStep_of_ne (A μ : ℝ) {β : ℝ} (hβ : β ≠ 0) :
    transformedSecularStep A μ β = A * (1 - μ ^ β) / β := by
  simp [transformedSecularStep, hβ, mul_div_assoc]

/-- The zero-exponent transformed step is logarithmic. -/
@[simp] theorem transformedSecularStep_zero (A μ : ℝ) :
    transformedSecularStep A μ 0 = -A * Real.log μ := by
  simp [transformedSecularStep, mul_neg, neg_mul]

/-- The transformed-step formula decreases with the exponent, including exponent zero. -/
theorem transformedSecularStep_antitone {A μ : ℝ} (hA : 0 ≤ A) (hμ : 0 < μ) :
    Antitone (transformedSecularStep A μ) := by
  intro a b hab
  exact mul_le_mul_of_nonneg_left (Real.antitone_normalizedRpowDifference hμ hab) hA

/-- The logarithmic step is the continuous extension at zero exponent. -/
theorem transformedSecularStep_continuousAt_zero (A : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    ContinuousAt (transformedSecularStep A μ) 0 :=
  continuousAt_const.mul (Real.continuousAt_normalizedRpowDifference_zero hμ)

/-- **Lemma B.8.2 (monotonicity of transformed secular Newton steps).**
The genuine Newton steps have nonzero denominators, satisfy (B.8.7), and are antitone
in the exponent. The scalar function need only be differentiable at the current point,
with positive value and negative derivative. The exponent-zero equation is logarithmic,
which corrects the removable singularity in the source's quotient. -/
theorem lemma_B_8_2 {φ : ℝ → ℝ} {Δ c d : ℝ} (hφ : HasDerivAt φ d c)
    (hΔ : 0 < Δ) (hv : 0 < φ c) (hd : d < 0) :
    (∀ β : ℝ, deriv (Real.powerTransformDifference φ (Δ ^ 2) β) c ≠ 0) ∧
    (∀ β : ℝ,
      -(Real.powerTransformDifference φ (Δ ^ 2) β c) /
          deriv (Real.powerTransformDifference φ (Δ ^ 2) β) c =
        transformedSecularStep (-φ c / d) (Δ ^ 2 / φ c) β) ∧
    Antitone (fun β : ℝ => -(Real.powerTransformDifference φ (Δ ^ 2) β c) /
      deriv (Real.powerTransformDifference φ (Δ ^ 2) β) c) :=
  ⟨Real.deriv_powerTransformDifference_ne_zero hφ hv hd.ne,
    fun β => Real.newton_powerTransformDifference hφ (sq_pos_of_pos hΔ) hv hd.ne β,
    Real.antitone_newton_powerTransformDifference hφ (sq_pos_of_pos hΔ) hv hd⟩

end CartisGouldToint
