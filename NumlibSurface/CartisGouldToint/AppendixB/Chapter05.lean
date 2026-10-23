import Numlib.Analysis.SpecialFunctions.Pow.NormalizedGap

/-!
# Cartis–Gould–Toint, Appendix B.5: positive residual exponents

Lemma B.5.1 contains all three positivity claims for the explicit exponents of
(5.1.21), (5.1.23), and (5.1.25). The quotients `p/2` and `p/3` are natural-number
quotients with the stated divisibility assumptions; subtraction in the exponent formulas
is performed in the reals. The repeated `ι₁` labels in the last two parts of the source's
proof are transcription errors for `ι₂` and `ι₃`.
-/

namespace CartisGouldToint
/-- **Lemma B.5.1 (positive exponents).** The residual exponents `ι₁(p,p,i)`,
`ι₂(p,p/2,i)`, and `ι₃(p,p/3,i)` are positive under their respective logarithmic
thresholds and divisibility conditions. Every exponent is given by its actual formula. -/
theorem lemma_B_5_1 {p i : ℕ} (hp : 0 < p) :
    (Real.log (p : ℝ) / Real.log 2 < (i : ℝ) →
      0 < ((2 : ℝ) ^ i - 1) / (2 : ℝ) ^ i - ((p : ℝ) - 1) / (p : ℝ)) ∧
    (2 ∣ p → Real.log ((p : ℝ) - 1) / Real.log 2 < (i : ℝ) →
      0 < ((2 : ℝ) ^ i - 1) / (2 : ℝ) ^ i -
        2 * (((p / 2 : ℕ) : ℝ) - 1) / ((p : ℝ) - 1)) ∧
    (3 ∣ p → Real.log ((p : ℝ) - 2) / Real.log 2 < (i : ℝ) →
      0 < ((2 : ℝ) ^ i - 1) / (2 : ℝ) ^ i -
        3 * (((p / 3 : ℕ) : ℝ) - 1) / ((p : ℝ) - 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (Real.normalized_pow_gap_pos_iff (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast hp) i).mpr
  · intro hdiv hi
    have hp2 : 2 ≤ p := Nat.le_of_dvd hp hdiv
    have hx : 0 < (p : ℝ) - 1 := by
      have hh : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
      linarith
    have h := (Real.normalized_pow_gap_pos_iff (by norm_num : (1 : ℝ) < 2) hx i).mpr hi
    have heq : ((p / 2 : ℕ) : ℝ) = (p : ℝ) / 2 := Nat.cast_div_charZero hdiv
    convert h using 1
    rw [heq]
    ring
  · intro hdiv hi
    have hp3 : 3 ≤ p := Nat.le_of_dvd hp hdiv
    have hx : 0 < (p : ℝ) - 2 := by
      have hh : (2 : ℝ) < p := by exact_mod_cast (show 2 < p by omega)
      linarith
    have h := (Real.normalized_pow_gap_pos_iff (by norm_num : (1 : ℝ) < 2) hx i).mpr hi
    have heq : ((p / 3 : ℕ) : ℝ) = (p : ℝ) / 3 := Nat.cast_div_charZero hdiv
    convert h using 1
    rw [heq]
    ring
end CartisGouldToint
