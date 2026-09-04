/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Ring.Units`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Condition number in a normed ring

`NormedRing.condNumber a = ‖a‖ * ‖a⁻¹‖`, with the junk value `0` when `a` is not a unit
(via `Ring.inverse`). Specializes to operators (`E →L[𝕜] E`) and matrices under any of Mathlib's
scoped matrix norms (Saad §1.13, Atkinson–Han §2.4.3, Kress Def 5.2, Higham Ch. 6).
-/

namespace NormedRing

variable {R : Type*} [NormedRing R]

/-- Condition number `‖a‖ ‖a⁻¹‖`; `0` (junk) if `a` is not a unit. -/
noncomputable def condNumber (a : R) : ℝ := ‖a‖ * ‖Ring.inverse a‖

/-- Notation `κ a` for the condition number. -/
scoped notation "κ" => NormedRing.condNumber

theorem condNumber_of_not_isUnit {a : R} (ha : ¬ IsUnit a) : condNumber a = 0 := by
  sorry

theorem condNumber_nonneg (a : R) : 0 ≤ condNumber a := by
  sorry

theorem one_le_condNumber [NormOneClass R] {a : R} (ha : IsUnit a) : 1 ≤ condNumber a := by
  sorry

theorem condNumber_inverse (a : R) : condNumber (Ring.inverse a) = condNumber a := by
  sorry

theorem condNumber_smul {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra 𝕜 R] {c : 𝕜} (hc : c ≠ 0)
    (a : R) : condNumber (c • a) = condNumber a := by
  sorry

theorem condNumber_mul_le [NormOneClass R] {a b : R} (ha : IsUnit a) (hb : IsUnit b) :
    condNumber (a * b) ≤ condNumber a * condNumber b := by
  sorry

end NormedRing

namespace ContinuousLinearEquiv

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem condNumber_eq (e : E ≃L[𝕜] E) :
    NormedRing.condNumber (e : E →L[𝕜] E) = ‖(e : E →L[𝕜] E)‖ * ‖(e.symm : E →L[𝕜] E)‖ := by
  sorry

end ContinuousLinearEquiv
