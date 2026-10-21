import Numlib.Analysis.SpecialFunctions.SqrtDifference

/-!
# Appendix B, Chapter 3: the square-root scaling inequality

The source's positive-parameter statement is a specialization of the nonnegative-parameter
inequality. The iteration-complexity proofs are in Chapter 3, Section 4.
-/

namespace CartisGouldToint.AppendixB.Chapter03

/-- Lemma B.3.1: the algebraic square-root bound used in Lemma 3.4.3. -/
theorem lemma_B_3_1 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) :
    (-b + Real.sqrt (b ^ 2 + a)) * min 1 c ≤ -b + Real.sqrt (b ^ 2 + a * c) := by
  simpa only [sub_eq_neg_add] using Real.sqrt_sq_add_mul_sub_ge_mul_min ha.le hb.le hc

end CartisGouldToint.AppendixB.Chapter03
