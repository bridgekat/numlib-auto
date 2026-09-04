import Numlib.Analysis.NormedRing.Inverse
import Numlib.Analysis.NormedRing.CondNumber
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Perturbation theory for linear systems

Normwise error bounds for `A x = b` in terms of the condition number (Saad §1.13.2 (1.76),
Atkinson–Han (2.4.1), Kress Thm 5.3, Higham Thm 7.2), the residual–error relation, and the
Rigal–Gaches formula for the normwise backward error (Higham Thm 7.1, Fong–Saunders (3.2)–(3.3)).
-/

open NormedRing

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Residual–error relation: `‖x - y‖ / ‖x‖ ≤ κ(A) ‖b - A y‖ / ‖b‖` (Atkinson–Han (2.4.1)). -/
theorem relative_error_le_condNumber_mul_relative_residual (A : E ≃L[𝕜] E) {b x y : E}
    (hx : A x = b) (hb : b ≠ 0) :
    ‖x - y‖ / ‖x‖ ≤ condNumber (A : E →L[𝕜] E) * (‖b - A y‖ / ‖b‖) := by
  sorry

/-- Normwise perturbation bound (Saad (1.76), Kress Thm 5.3, Higham Thm 7.2): if
`(A + ΔA) y = b + Δb` and `‖A⁻¹‖ ‖ΔA‖ < 1` then
`‖y - x‖/‖x‖ ≤ κ(A)/(1 - ‖A⁻¹‖‖ΔA‖) (‖ΔA‖/‖A‖ + ‖Δb‖/‖b‖)`. -/
theorem relative_error_le_condNumber [CompleteSpace E] (A : E ≃L[𝕜] E) (ΔA : E →L[𝕜] E)
    {b Δb x y : E} (hx : A x = b) (hy : ((A : E →L[𝕜] E) + ΔA) y = b + Δb)
    (hsmall : ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ < 1) (hx0 : x ≠ 0) (hb : b ≠ 0) :
    ‖y - x‖ / ‖x‖ ≤ condNumber (A : E →L[𝕜] E) / (1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖)
      * (‖ΔA‖ / ‖(A : E →L[𝕜] E)‖ + ‖Δb‖ / ‖b‖) := by
  sorry

/-- The perturbed operator is invertible and the perturbed solution exists (companion to
`relative_error_le_condNumber`). -/
theorem exists_perturbed_solution [CompleteSpace E] (A : E ≃L[𝕜] E) (ΔA : E →L[𝕜] E)
    (hsmall : ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ < 1) (b' : E) :
    ∃! y, ((A : E →L[𝕜] E) + ΔA) y = b' := by
  sorry

section BackwardError

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The normwise backward error of `y` for `A x = b` with tolerances `α` on `A` and `β` on `b`
(Rigal–Gaches; Fong–Saunders (3.2)): `‖b - A y‖ / (α ‖A‖ ‖y‖ + β ‖b‖)`. -/
noncomputable def backwardError (A : E →L[𝕜] E) (b y : E) (α β : ℝ) : ℝ :=
  ‖b - A y‖ / (α * ‖A‖ * ‖y‖ + β * ‖b‖)

/-- Rigal–Gaches (Higham Thm 7.1): `backwardError A b y α β` is the least `ξ` such that
`(A + ΔA) y = b + Δb` for some `‖ΔA‖ ≤ ξ α ‖A‖`, `‖Δb‖ ≤ ξ β ‖b‖`. -/
theorem isLeast_backwardError (A : E →L[𝕜] E) (b y : E) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hpos : 0 < α * ‖A‖ * ‖y‖ + β * ‖b‖) :
    IsLeast {ξ : ℝ | ∃ (ΔA : E →L[𝕜] E) (Δb : E), (A + ΔA) y = b + Δb ∧
        ‖ΔA‖ ≤ ξ * α * ‖A‖ ∧ ‖Δb‖ ≤ ξ * β * ‖b‖}
      (backwardError A b y α β) := by
  sorry

/-- The optimal perturbations (Fong–Saunders (3.3)): `ΔA = ((1 - ω) / ‖y‖²) r ⊗ y`,
`Δb = -ω r`, with `ω = β ‖b‖ / (α ‖A‖ ‖y‖ + β ‖b‖)`. -/
theorem exists_optimal_perturbation (A : E →L[𝕜] E) (b y : E) {α β : ℝ} (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hpos : 0 < α * ‖A‖ * ‖y‖ + β * ‖b‖) :
    ∃ (ΔA : E →L[𝕜] E) (Δb : E), (A + ΔA) y = b + Δb ∧
      ‖ΔA‖ = backwardError A b y α β * α * ‖A‖ ∧ ‖Δb‖ = backwardError A b y α β * β * ‖b‖ := by
  sorry

/-- Stopping rule (Fong–Saunders (3.4)): `backwardError ≤ ξ ↔ ‖r‖ ≤ ξ (α ‖A‖ ‖y‖ + β ‖b‖)`. -/
theorem backwardError_le_iff (A : E →L[𝕜] E) (b y : E) {α β ξ : ℝ}
    (hpos : 0 < α * ‖A‖ * ‖y‖ + β * ‖b‖) :
    backwardError A b y α β ≤ ξ ↔ ‖b - A y‖ ≤ ξ * (α * ‖A‖ * ‖y‖ + β * ‖b‖) := by
  sorry

end BackwardError
