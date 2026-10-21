import Numlib.Optimization.ResidualDescentExponent

/-!
# Appendix B, Chapter 5: positivity of residual exponents

The repeated first-order exponent names in the OCR proof are read as second- and third-order
exponents in their respective clauses. The common algebra works at any positive derivative
order and real model degree.
-/

namespace CartisGouldToint.AppendixB.Chapter05

/-- Lemma B.5.1. A general derivative-order form proves all three source clauses, after
choosing orders one, two and three and their admissible natural model degrees. -/
theorem lemma_B_5_1 {p j : ℝ} (hj : 0 < j) (hp : j - 1 < p) {i : ℕ}
    (hi : Real.logb 2 (p - j + 1) < i) :
    0 < Optimization.residualDescentExponent p (p / j) i j :=
  Optimization.residualDescentExponent_pos_div_order_of_logb hj.ne' (by linarith) hi

end CartisGouldToint.AppendixB.Chapter05
