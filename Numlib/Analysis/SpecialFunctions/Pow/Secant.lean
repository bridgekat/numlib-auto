import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Monotonicity of power secants in the exponent

Convexity of the exponential makes its secants monotone, including pairs of exponents on
opposite sides of zero. This proves comparisons of transformed Newton corrections without
an exponent derivative calculation.
-/

namespace Real

/-- The power divided difference with its value at exponent zero removed is antitone.
The zero exponent is excluded because real division assigns it zero rather than the
continuous extension `-log μ`. -/
theorem antitoneOn_one_sub_rpow_div {μ : ℝ} (hμ : 0 < μ) :
    AntitoneOn (fun β : ℝ => (1 - μ ^ β) / β) ({0}ᶜ : Set ℝ) := by
  intro a ha b hb hab
  have hm := (convexOn_rpow_left hμ).slope_mono (Set.mem_univ 0)
  have hs := hm ⟨Set.mem_univ a, ha⟩ ⟨Set.mem_univ b, hb⟩ hab
  simp only [slope_def_field, sub_zero, rpow_zero] at hs
  have hna : (1 - μ ^ a) / a = -((μ ^ a - 1) / a) := by ring
  have hnb : (1 - μ ^ b) / b = -((μ ^ b - 1) / b) := by ring
  change (1 - μ ^ b) / b ≤ (1 - μ ^ a) / a
  rw [hna, hnb]
  exact neg_le_neg hs

end Real
