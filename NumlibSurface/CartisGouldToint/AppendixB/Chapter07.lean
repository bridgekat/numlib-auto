import Numlib.Analysis.SpecialFunctions.SqrtDifference
import Mathlib.Order.Filter.Extr

/-!
# A disk minimization problem

The square-root bound proves the exact global minimizer in Lemma B.7.1 directly.
-/

namespace CartisGouldToint.AppendixB.Chapter07

/-- Lemma B.7.1: the disk problem attains its global minimum `ε - ω` at `(ω,0)`. -/
theorem lemma_B_7_1 {ε ω : ℝ} (hω : 0 < ω) (hεω : ω < ε) :
    (ω, (0 : ℝ)) ∈ {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 ≤ ω ^ 2} ∧
    IsMinOn (fun z : ℝ × ℝ => -z.1 + Real.sqrt (ε ^ 2 - z.2 ^ 2))
      {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 ≤ ω ^ 2} (ω, 0) ∧
    -ω + Real.sqrt (ε ^ 2 - (0 : ℝ) ^ 2) = ε - ω := by
  have hvalue : -ω + Real.sqrt (ε ^ 2 - (0 : ℝ) ^ 2) = ε - ω := by
    simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, Real.sqrt_sq (hω.le.trans hεω.le)]
    ring
  refine ⟨by simp, ?_, hvalue⟩
  intro z hz
  change -ω + Real.sqrt (ε ^ 2 - (0 : ℝ) ^ 2) ≤ _
  rw [hvalue]
  exact Real.sub_add_sqrt_sq_sub_sq_ge_sub hω.le hεω.le hz

end CartisGouldToint.AppendixB.Chapter07
