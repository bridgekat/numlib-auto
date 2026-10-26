import Numlib.Analysis.SpecialFunctions.SqrtBound

/-!
# Cartis–Gould–Toint, Appendix B: Appendix to Chapter 3

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], Appendix B, "Appendix to
Chapter 3": the algebraic Lemma B.3.1 used in the proof of Lemma 3.4.3, specialized from
`neg_add_sqrt_sq_add_mul_ge`. The proofs of Theorems 3.4.11, 3.4.12, Lemmas 3.5.1–3.5.3 and
Theorem 3.5.4 given in this appendix are the proofs of the corresponding Chapter 3 results.
-/

namespace CartisGouldToint.AppendixB

/-- **Lemma B.3.1** of [cartis2022evaluation]. For `a, b > 0` and `c ≥ 0`,
`-b + √(b² + a c) ≥ (-b + √(b² + a)) min(1, c)` (B.3.1). -/
theorem lemma_B_3_1 {a b c : ℝ} (ha : 0 < a) (_hb : 0 < b) (hc : 0 ≤ c) :
    -b + √(b ^ 2 + a * c) ≥ (-b + √(b ^ 2 + a)) * min 1 c :=
  neg_add_sqrt_sq_add_mul_ge ha.le hc

end CartisGouldToint.AppendixB
