import Numlib.Optimization.InexactRegularizationComplexity

/-!
# Tolerance independence of implicit-accuracy rate constants

Replacing the tolerance vector preserves every numerical coefficient in the proved
first-attainment and evaluation bounds. These identities expose the fixed-control
quantifier order without unfolding rate definitions in consumers.
-/

noncomputable section
namespace Optimization.InexactRegularization

/-- Tolerance replacement preserves `correctedSigmaBound`, which uses only fixed controls. -/
@[simp] theorem correctedSigmaBound_withTolerances (P : Parameters) (epsilon : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < epsilon j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → epsilon j < 1)
    (h0 : ℕ → ℝ) (sigma0 L K : ℝ) :
    correctedSigmaBound (P.withTolerances epsilon hpos hlt) h0 sigma0 L K =
      correctedSigmaBound P h0 sigma0 L K := rfl

/-- Tolerance replacement preserves `correctedTransferConstant`, using only fixed controls. -/
@[simp] theorem correctedTransferConstant_withTolerances (P : Parameters) (epsilon : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < epsilon j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → epsilon j < 1)
    (h0 : ℕ → ℝ) (sigma0 L K : ℝ) :
    correctedTransferConstant (P.withTolerances epsilon hpos hlt)
        h0 sigma0 L K =
      correctedTransferConstant P h0 sigma0 L K := rfl

/-- Tolerance replacement preserves the fixed accepted-decrease coefficient. -/
@[simp] theorem acceptedDecreaseCoefficient_withTolerances (P : Parameters) (epsilon : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < epsilon j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → epsilon j < 1)
    (h0 : ℕ → ℝ) (sigma0 L K M : ℝ) :
    acceptedDecreaseCoefficient (P.withTolerances epsilon hpos hlt) h0 sigma0 L K M =
      acceptedDecreaseCoefficient P h0 sigma0 L K M := rfl

/-- Tolerance replacement preserves `trialCountMultiplier`, which uses only fixed controls. -/
@[simp] theorem trialCountMultiplier_withTolerances (P : Parameters) (epsilon : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < epsilon j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → epsilon j < 1)
     :
    trialCountMultiplier (P.withTolerances epsilon hpos hlt)  =
      trialCountMultiplier P  := rfl

/-- Tolerance replacement preserves `trialLogBudget`, which uses only fixed controls. -/
@[simp] theorem trialLogBudget_withTolerances (P : Parameters) (epsilon : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < epsilon j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → epsilon j < 1)
    (h0 : ℕ → ℝ) (sigma0 L K : ℝ) :
    trialLogBudget (P.withTolerances epsilon hpos hlt) h0 sigma0 L K =
      trialLogBudget P h0 sigma0 L K := rfl

/-- Tolerance replacement preserves `refinementLogSlope`, which uses only fixed controls. -/
@[simp] theorem refinementLogSlope_withTolerances (P : Parameters) (epsilon : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < epsilon j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → epsilon j < 1)
     :
    refinementLogSlope (P.withTolerances epsilon hpos hlt)  =
      refinementLogSlope P  := rfl

/-- Tolerance replacement preserves `refinementCountConstant`, which uses only fixed controls. -/
@[simp] theorem refinementCountConstant_withTolerances (P : Parameters) (epsilon : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < epsilon j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → epsilon j < 1)
    (h0 : ℕ → ℝ) (sigma0 L K M : ℝ) :
    refinementCountConstant (P.withTolerances epsilon hpos hlt) h0 sigma0 L K M =
      refinementCountConstant P h0 sigma0 L K M := rfl

/-- The tolerance scale after replacement is the scale of precisely the new vector. -/
@[simp] theorem toleranceMeasure_withTolerances (P : Parameters) (epsilon : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < epsilon j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → epsilon j < 1) :
    HigherOrderApproximateRegularization.toleranceMeasure
        (P.withTolerances epsilon hpos hlt).p (P.withTolerances epsilon hpos hlt).q
        (P.withTolerances epsilon hpos hlt).order_pos
        (P.withTolerances epsilon hpos hlt).epsilon =
      HigherOrderApproximateRegularization.toleranceMeasure P.p P.q P.order_pos epsilon := rfl

end Optimization.InexactRegularization
