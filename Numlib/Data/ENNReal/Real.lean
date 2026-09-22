/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Basic.ENNReal.Real`, beside `ENNReal.toReal_mono`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Basic.ENNReal.Real

/-!
# `1 ≤ p.toReal` for a finite exponent

The exponent bookkeeping of the `L^p` theory: an exponent `p : ℝ≥0∞` with `1 ≤ p` (as a `Fact`,
the form the `Lp` API carries it in) and `p ≠ ∞` has `1 ≤ p.toReal`
(`ENNReal.one_le_toReal_of_ne_top`).
-/

open scoped ENNReal

/-- `1 ≤ p.toReal` for `1 ≤ p < ∞`. -/
theorem ENNReal.one_le_toReal_of_ne_top {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    1 ≤ p.toReal := by
  rw [← ENNReal.toReal_one]
  exact ENNReal.toReal_mono hp Fact.out
