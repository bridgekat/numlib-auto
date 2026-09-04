/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Algebra.Spectrum`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Spectral radius and convergence of powers

In a complex unital Banach algebra, `ρ(a) < 1 ↔ aⁿ → 0` (Saad Thm 1.10, Kress Thm 4.1 /
Problem 4.3), the Neumann series converges iff `ρ(a) < 1` (Saad Thm 1.11), and powers decay
geometrically at any rate above the spectral radius (Gelfand's formula, which Mathlib provides as
`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`).
-/

open Filter Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- Geometric decay of powers at any rate `r > ρ(a)`. -/
theorem exists_norm_pow_le_of_spectralRadius_lt (a : A) {r : NNReal}
    (hr : spectralRadius ℂ a < r) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖a ^ n‖ ≤ C * (r : ℝ) ^ n := by
  sorry

/-- `ρ(a) < 1 ↔ aⁿ → 0`. -/
theorem spectralRadius_lt_one_iff_tendsto_pow (a : A) :
    spectralRadius ℂ a < 1 ↔ Tendsto (fun n => a ^ n) atTop (𝓝 0) := by
  sorry

theorem spectralRadius_lt_one_of_norm_lt_one {a : A} (h : ‖a‖ < 1) : spectralRadius ℂ a < 1 := by
  sorry

/-- `ρ(a) < 1 ↔ ‖aⁿ‖ < 1` for some `n`. -/
theorem spectralRadius_lt_one_iff_exists_norm_pow_lt_one (a : A) :
    spectralRadius ℂ a < 1 ↔ ∃ n, ‖a ^ n‖ < 1 := by
  sorry

/-- Saad Thm 1.11: the Neumann series converges iff `ρ(a) < 1`. -/
theorem summable_pow_iff_spectralRadius_lt_one (a : A) :
    Summable (fun n => a ^ n) ↔ spectralRadius ℂ a < 1 := by
  sorry

/-- When `ρ(a) < 1`, `1 - a` is a unit with inverse the Neumann series. -/
theorem isUnit_one_sub_of_spectralRadius_lt_one {a : A} (h : spectralRadius ℂ a < 1) :
    IsUnit (1 - a) := by
  sorry
