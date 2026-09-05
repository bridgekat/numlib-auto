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

/-- A two-sided inverse computes `Ring.inverse`. -/
private theorem inverse_eq_of_mul_eq_one {M₀ : Type*} [MonoidWithZero M₀] {a b : M₀}
    (h₁ : a * b = 1) (h₂ : b * a = 1) : Ring.inverse a = b :=
  Ring.inverse_unit (⟨a, b, h₁, h₂⟩ : M₀ˣ)

section Smul

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra 𝕜 R]

private theorem isUnit_smul {c : 𝕜} (hc : c ≠ 0) {a : R} (ha : IsUnit a) : IsUnit (c • a) :=
  ⟨⟨c • a, c⁻¹ • Ring.inverse a,
    by rw [smul_mul_smul_comm, Ring.mul_inverse_cancel a ha, mul_inv_cancel₀ hc, one_smul],
    by rw [smul_mul_smul_comm, Ring.inverse_mul_cancel a ha, inv_mul_cancel₀ hc, one_smul]⟩, rfl⟩

private theorem isUnit_smul_iff {c : 𝕜} (hc : c ≠ 0) (a : R) : IsUnit (c • a) ↔ IsUnit a :=
  ⟨fun h ↦ by simpa [inv_smul_smul₀ hc] using isUnit_smul (inv_ne_zero hc) h, isUnit_smul hc⟩

private theorem inverse_smul {c : 𝕜} (hc : c ≠ 0) (a : R) :
    Ring.inverse (c • a) = c⁻¹ • Ring.inverse a := by
  by_cases ha : IsUnit a
  · exact inverse_eq_of_mul_eq_one
      (by rw [smul_mul_smul_comm, Ring.mul_inverse_cancel a ha, mul_inv_cancel₀ hc, one_smul])
      (by rw [smul_mul_smul_comm, Ring.inverse_mul_cancel a ha, inv_mul_cancel₀ hc, one_smul])
  · rw [Ring.inverse_non_unit _ ((isUnit_smul_iff hc a).not.mpr ha), Ring.inverse_non_unit _ ha,
      smul_zero]

end Smul

theorem condNumber_of_not_isUnit {a : R} (ha : ¬ IsUnit a) : condNumber a = 0 := by
  rw [condNumber, Ring.inverse_non_unit _ ha, norm_zero, mul_zero]

theorem condNumber_nonneg (a : R) : 0 ≤ condNumber a :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem one_le_condNumber [NormOneClass R] {a : R} (ha : IsUnit a) : 1 ≤ condNumber a :=
  calc (1 : ℝ) = ‖a * Ring.inverse a‖ := by rw [Ring.mul_inverse_cancel a ha, norm_one]
    _ ≤ condNumber a := norm_mul_le _ _

theorem condNumber_inverse (a : R) : condNumber (Ring.inverse a) = condNumber a := by
  by_cases ha : IsUnit a
  · rw [condNumber, condNumber, Ring.inverse_inverse ha, mul_comm]
  · rw [condNumber, condNumber, Ring.inverse_non_unit _ ha, norm_zero, zero_mul, mul_zero]

theorem condNumber_smul {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra 𝕜 R] {c : 𝕜} (hc : c ≠ 0)
    (a : R) : condNumber (c • a) = condNumber a := by
  have hc' : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [condNumber, condNumber, inverse_smul hc, norm_smul, norm_smul, norm_inv]
  field_simp

theorem condNumber_mul_le [NormOneClass R] {a b : R} (ha : IsUnit a) (hb : IsUnit b) :
    condNumber (a * b) ≤ condNumber a * condNumber b := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  rw [condNumber, condNumber, condNumber, ← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit,
    Ring.inverse_unit, mul_inv_rev, Units.val_mul, Units.val_mul]
  calc ‖(u : R) * v‖ * ‖(↑v⁻¹ : R) * ↑u⁻¹‖
      ≤ ‖(u : R)‖ * ‖(v : R)‖ * (‖(↑v⁻¹ : R)‖ * ‖(↑u⁻¹ : R)‖) := by
        gcongr <;> exact norm_mul_le _ _
    _ = ‖(u : R)‖ * ‖(↑u⁻¹ : R)‖ * (‖(v : R)‖ * ‖(↑v⁻¹ : R)‖) := by ring

end NormedRing

namespace ContinuousLinearEquiv

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- `Ring.inverse` of the underlying map of a continuous linear equivalence is the inverse map. -/
theorem ring_inverse_coe (e : E ≃L[𝕜] E) :
    Ring.inverse (e : E →L[𝕜] E) = (e.symm : E →L[𝕜] E) :=
  NormedRing.inverse_eq_of_mul_eq_one (by ext x; simp) (by ext x; simp)

theorem condNumber_eq (e : E ≃L[𝕜] E) :
    NormedRing.condNumber (e : E →L[𝕜] E) = ‖(e : E →L[𝕜] E)‖ * ‖(e.symm : E →L[𝕜] E)‖ := by
  rw [NormedRing.condNumber, ring_inverse_coe]

end ContinuousLinearEquiv
