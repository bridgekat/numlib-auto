/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # Practical trust-region parameters -/

namespace ConnGouldToint.Chapter17

/-- The recommended acceptance thresholds in (17.1.1). -/
noncomputable def recommendedAcceptance : ℝ × ℝ := (0.05, 0.9)

/-- The recommended radius factors in (17.1.2). -/
noncomputable def recommendedRadiusFactors : ℝ × ℝ := (2.5, 0.25)

/-- The quadratic with value `a` and slope `l` at zero and value `b` at one. -/
def quadraticRayInterpolant (a l b t : ℝ) : ℝ :=
  a + l * t + (b - a - l) * t ^ 2

/-- Corrected (17.1.3). The common value and slope are scaled by `1 - η`. -/
noncomputable def interpolatedRadiusFactor (η a l f₁ m₁ : ℝ) : ℝ :=
  (1 - η) * l / ((1 - η) * (a + l) + η * m₁ - f₁)

/-- The corrected interpolation factor gives the target ratio for the two quadratic rays. -/
theorem interpolatedRadiusFactor_hits_ratio (η a l f₁ m₁ : ℝ)
    (hden : (1 - η) * (a + l) + η * m₁ - f₁ ≠ 0)
    (hpred : a - quadraticRayInterpolant a l m₁ (interpolatedRadiusFactor η a l f₁ m₁) ≠ 0) :
    let t := interpolatedRadiusFactor η a l f₁ m₁
    (a - quadraticRayInterpolant a l f₁ t) / (a - quadraticRayInterpolant a l m₁ t) = η := by
  let t := interpolatedRadiusFactor η a l f₁ m₁
  change (a - quadraticRayInterpolant a l f₁ t) /
    (a - quadraticRayInterpolant a l m₁ t) = η
  rw [div_eq_iff hpred]
  have ht : ((1 - η) * (a + l) + η * m₁ - f₁) * t = (1 - η) * l := by
    dsimp [t, interpolatedRadiusFactor]
    rw [mul_comm, div_mul_cancel₀ _ hden]
  unfold quadraticRayInterpolant
  linear_combination t * ht

/-- The factor in the printed (17.1.3) gives the wrong ratio for two quadratic rays. -/
theorem printedInterpolation_counterexample :
    let η : ℝ := 1 / 2
    let t : ℝ := ((1 - η) * (-1)) / ((1 - η) * (0 + (-1) + η * (-1) - 1))
    (0 - quadraticRayInterpolant 0 (-1) 1 t) / (0 - quadraticRayInterpolant 0 (-1) (-1) t) ≠ η := by
  norm_num [quadraticRayInterpolant]

/-- The four-branch practical update rule (17.1.4). -/
noncomputable def practicalRadiusUpdate (η₁ η₂ α₁ α₂ ρ Δ length γbad : ℝ) : ℝ :=
  if η₂ ≤ ρ then max (α₁ * length) Δ
  else if η₁ ≤ ρ then Δ
  else if 0 ≤ ρ then α₂ * length
  else min (α₂ * length) (max 0.0625 γbad * Δ)

end ConnGouldToint.Chapter17
