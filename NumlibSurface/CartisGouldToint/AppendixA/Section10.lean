import Numlib.Analysis.SpecialFunctions.Exp.FiniteSum

/-!
# Cartis–Gould–Toint, Appendix A.10: simple series bounds

The two finite factorial-series inequalities of Lemma A.10.1, equation (A.33), including
zero step lengths and coincident lower and upper summation indices.
-/

open scoped BigOperators

namespace CartisGouldToint

/-- **Lemma A.10.1 (sum bounds).** For `0 ≤ δ ≤ 1` and `j ≤ p`, the shifted exponential
sum is at most `1 + 2δ`, and its higher-order tail is at most `2δ^(j+1)/j!`. -/
theorem lemma_A_10_1 {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {j p : ℕ} (hjp : j ≤ p) :
    (∑ ℓ ∈ Finset.Icc j p, δ ^ (ℓ - j) / (ℓ - j).factorial) ≤ 1 + 2 * δ ∧
      (∑ ℓ ∈ Finset.Icc (j + 1) (p + 1), δ ^ ℓ / ℓ.factorial) ≤
        2 * δ ^ (j + 1) / j.factorial :=
  ⟨Real.sum_Icc_shift_pow_div_factorial_le hδ0 hδ1 hjp,
    Real.sum_Icc_pow_div_factorial_le_tail hδ0 hδ1 j p⟩

end CartisGouldToint
