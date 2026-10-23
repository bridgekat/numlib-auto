import Mathlib.Tactic

/-!
# High-order evaluation-complexity exponent profiles

The numerical profiles distinguish trust-region costs, unit-radius
regularization costs and the two nonunit-radius regularization estimates.
Every positive requested order at most the model degree has exponent above one.
-/

namespace EvaluationComplexity

/-- The four numerical exponent profiles appearing in high-order model methods. -/
inductive HighOrderProfile where
  | trustRegion
  | unitRadius
  | commonRadius
  | varyingRadius

/-- The numerical evaluation exponent at a specified positive derivative order. -/
noncomputable def HighOrderProfile.exponent (profile : HighOrderProfile) (p j : ℕ) : ℝ :=
  match profile with
  | .trustRegion => (j : ℝ) + 1
  | .unitRadius => (p + 1 : ℝ) / (p - j + 1 : ℕ)
  | .commonRadius => (j : ℝ) * (p + 1 : ℝ) / p
  | .varyingRadius => (j : ℝ) * (p + 1 : ℝ) / (p - j + 1 : ℕ)

/-- All admissible positive-order profiles have exponent strictly greater than one. -/
theorem HighOrderProfile.one_lt_exponent (profile : HighOrderProfile) {p j : ℕ}
    (hj : 1 ≤ j) (hjp : j ≤ p) : 1 < profile.exponent p j := by
  have hp : 0 < p := by omega
  have hd : 0 < p - j + 1 := by omega
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hdr : (0 : ℝ) < (p - j + 1 : ℕ) := by exact_mod_cast hd
  have hdle : (p - j + 1 : ℕ) ≤ p := by omega
  have hdler : ((p - j + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hdle
  cases profile <;> simp only [HighOrderProfile.exponent]
  · linarith
  · apply (one_lt_div hdr).mpr
    linarith
  · apply (one_lt_div hpr).mpr
    nlinarith
  · apply (one_lt_div hdr).mpr
    nlinarith

end EvaluationComplexity
