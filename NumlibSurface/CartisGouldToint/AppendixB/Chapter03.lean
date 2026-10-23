import Numlib.Analysis.SpecialFunctions.Sqrt.Bounds

/-!
# Cartis–Gould–Toint, Appendix B to Chapter 3

Lemma B.3.1 is the algebraic square-root estimate used to bound the length of a strictly
feasible trust-region step in Lemma 3.4.3.
-/

namespace CartisGouldToint

/-- **Lemma B.3.1.** For `a,b > 0` and `c ≥ 0`, the square-root increment at scale `c`
is bounded below by its increment at scale one multiplied by `min 1 c`. -/
theorem lemma_B_3_1 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) :
    -b + Real.sqrt (b ^ 2 + a * c) ≥
      (-b + Real.sqrt (b ^ 2 + a)) * min 1 c :=
  Real.min_mul_sqrt_sub_le_sqrt_add_mul_sub ha.le hb.le hc

end CartisGouldToint
