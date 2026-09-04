/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Ring.Units`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Explicit Neumann-series and perturbation bounds

Quantitative versions of `Units.oneSub` / `Units.add` in a complete normed ring:
`‖(1 - t)⁻¹‖ ≤ 1 / (1 - ‖t‖)`, `‖(x + t)⁻¹‖ ≤ ‖x⁻¹‖ / (1 - ‖x⁻¹‖ ‖t‖)`, and the two-space
version for continuous linear equivalences (Atkinson–Han Thm 2.3.1, Cor 2.3.3, Thm 2.3.5;
Saad §1.13; Kress Thm 3.48; Higham Thm 7.2).
-/

namespace NormedRing

variable {R : Type*} [NormedRing R] [NormOneClass R] [CompleteSpace R]

/-- Geometric series theorem with the explicit bound `‖(1 - t)⁻¹‖ ≤ 1 / (1 - ‖t‖)`. -/
theorem norm_inverse_one_sub_le {t : R} (h : ‖t‖ < 1) :
    ‖Ring.inverse (1 - t)‖ ≤ 1 / (1 - ‖t‖) := by
  sorry

/-- `‖(1 - t)⁻¹ - 1‖ ≤ ‖t‖ / (1 - ‖t‖)`. -/
theorem norm_inverse_one_sub_sub_one_le {t : R} (h : ‖t‖ < 1) :
    ‖Ring.inverse (1 - t) - 1‖ ≤ ‖t‖ / (1 - ‖t‖) := by
  sorry

/-- Atkinson–Han Cor 2.3.3: `‖t ^ m‖ < 1` for some `m` suffices for `1 - t` to be a unit. -/
theorem isUnit_one_sub_of_norm_pow_lt_one {t : R} {m : ℕ} (h : ‖t ^ m‖ < 1) : IsUnit (1 - t) := by
  sorry

/-- The bound accompanying `isUnit_one_sub_of_norm_pow_lt_one` (Atkinson–Han (2.3.6)):
`‖(1 - t)⁻¹‖ ≤ (∑_{i < m} ‖t^i‖) / (1 - ‖t^m‖)`. -/
theorem norm_inverse_one_sub_le_of_norm_pow_lt_one {t : R} {m : ℕ} (h : ‖t ^ m‖ < 1) :
    ‖Ring.inverse (1 - t)‖ ≤ (∑ i ∈ Finset.range m, ‖t ^ i‖) / (1 - ‖t ^ m‖) := by
  sorry

end NormedRing

namespace Units

variable {R : Type*} [NormedRing R] [NormOneClass R] [CompleteSpace R]

/-- Perturbation of a unit: `x + t` is a unit when `‖t‖ < ‖x⁻¹‖⁻¹` (Mathlib's `Units.add`). -/
theorem isUnit_add_of_norm_lt (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) :
    IsUnit ((x : R) + t) := by
  sorry

/-- Atkinson–Han (2.3.13): `‖(x + t)⁻¹‖ ≤ ‖x⁻¹‖ / (1 - ‖x⁻¹‖ ‖t‖)`. -/
theorem norm_inverse_add_le (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) :
    ‖Ring.inverse ((x : R) + t)‖ ≤ ‖(↑x⁻¹ : R)‖ / (1 - ‖(↑x⁻¹ : R)‖ * ‖t‖) := by
  sorry

/-- Atkinson–Han (2.3.14): `‖(x + t)⁻¹ - x⁻¹‖ ≤ ‖x⁻¹‖² ‖t‖ / (1 - ‖x⁻¹‖ ‖t‖)`. -/
theorem norm_inverse_add_sub_le (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) :
    ‖Ring.inverse ((x : R) + t) - ↑x⁻¹‖ ≤
      ‖(↑x⁻¹ : R)‖ ^ 2 * ‖t‖ / (1 - ‖(↑x⁻¹ : R)‖ * ‖t‖) := by
  sorry

end Units

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace E]

/-- Atkinson–Han Thm 2.3.5 (two-space perturbation theorem): if `e : E ≃L F` and
`‖e⁻¹‖ ‖t‖ < 1` then `e + t` is invertible with `‖(e + t)⁻¹‖ ≤ ‖e⁻¹‖ / (1 - ‖e⁻¹‖ ‖t‖)`
(2.3.13) and `‖(e + t)⁻¹ - e⁻¹‖ ≤ ‖e⁻¹‖² ‖t‖ / (1 - ‖e⁻¹‖ ‖t‖)` (2.3.14). Completeness of `E`
suffices (the book assumes one of the two spaces complete). -/
theorem exists_symm_norm_le_of_add (e : E ≃L[𝕜] F) (t : E →L[𝕜] F)
    (h : ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖ < 1) :
    ∃ e' : E ≃L[𝕜] F, (e' : E →L[𝕜] F) = (e : E →L[𝕜] F) + t ∧
      ‖(e'.symm : F →L[𝕜] E)‖ ≤
        ‖(e.symm : F →L[𝕜] E)‖ / (1 - ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖) ∧
      ‖(e'.symm : F →L[𝕜] E) - (e.symm : F →L[𝕜] E)‖ ≤
        ‖(e.symm : F →L[𝕜] E)‖ ^ 2 * ‖t‖ / (1 - ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖) := by
  sorry

/-- Atkinson–Han (2.3.16): consistency plus stability gives convergence,
`‖v - vₙ‖ ≤ ‖Lₙ⁻¹‖ ‖(L - Lₙ) v‖` when `L v = Lₙ vₙ`. -/
theorem norm_sub_le_of_apply_eq (L : E →L[𝕜] F) (Ln : E ≃L[𝕜] F) {v vn : E}
    (h : L v = Ln vn) : ‖v - vn‖ ≤ ‖(Ln.symm : F →L[𝕜] E)‖ * ‖(L - Ln) v‖ := by
  sorry

end ContinuousLinearEquiv
