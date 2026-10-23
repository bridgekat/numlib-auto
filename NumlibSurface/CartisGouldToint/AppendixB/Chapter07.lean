import Numlib.Analysis.SpecialFunctions.Sqrt.Bounds

/-!
# Cartis–Gould–Toint, Appendix B to Chapter 7

The two-variable disk problem of Lemma B.7.1 is solved by a direct square-root inequality.
Feasibility, the attained value, and a global lower bound are all stated explicitly.
-/

namespace CartisGouldToint

/-- **Lemma B.7.1.** On `f²+c² ≤ ω²` with `0 < ω < ε`, the objective
`-f + sqrt (ε²-c²)` has minimum `ε-ω`, attained at the feasible point `(ω,0)`. -/
theorem lemma_B_7_1 {ω ε : ℝ} (hω : 0 < ω) (hε : ω < ε) :
    ω ^ 2 + (0 : ℝ) ^ 2 ≤ ω ^ 2 ∧
      -ω + Real.sqrt (ε ^ 2 - (0 : ℝ) ^ 2) = ε - ω ∧
      ∀ f c : ℝ, f ^ 2 + c ^ 2 ≤ ω ^ 2 →
        ε - ω ≤ -f + Real.sqrt (ε ^ 2 - c ^ 2) := by
  refine ⟨by simp, ?_, fun f c hfc =>
    Real.sub_le_neg_add_sqrt_of_sq_add_sq_le hω.le hε.le hfc⟩
  simp [Real.sqrt_sq_eq_abs, abs_of_pos (hω.trans hε)]
  ring

end CartisGouldToint
