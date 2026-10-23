import Numlib.Optimization.HighOrder.StepCoefficient

/-!
# Real-power stepsize bounds with an explicit safe radius coefficient

A normalized Taylor-criticality obstruction yields the two source accuracy
rates. The high-order branch uses a radius coefficient no larger than its
normalized obstruction coefficient; this condition is essential when the
step is shorter than the radius.
-/

namespace HighOrderStep

/-- The radius coefficient that validates both scalar comparison branches.
The first entry is the actual printed model-solver floor; the second is the
smallest normalized criticality obstruction coefficient. -/
noncomputable def regularizationRadiusCoefficient (ζ θ D L S : ℝ) (q : ℕ) : ℝ :=
  min (ζ * θ / (8 * (3 * D + S))) (criticalityCoefficient θ (L + S) q)

/-- Fixed normalized model bounds make the corrected radius coefficient
positive and at most one, before any accuracy is chosen. -/
theorem regularizationRadiusCoefficient_mem {ζ θ D L S : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hD : 1 ≤ D) (hL : 1 ≤ L) (hS : 0 ≤ S) (q : ℕ) :
    0 < regularizationRadiusCoefficient ζ θ D L S q ∧
      regularizationRadiusCoefficient ζ θ D L S q ≤ 1 := by
  have hden : 0 < 8 * (3 * D + S) := by linarith
  have hnum : ζ * θ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hζ1 hθ1.le hθ.le zero_le_one
  have hbase : ζ * θ / (8 * (3 * D + S)) ≤ 1 :=
    (div_le_one hden).mpr (by linarith)
  have hc := criticalityCoefficient_mem hθ hθ1 (by linarith : 1 ≤ L + S) q
  exact ⟨lt_min (div_pos (mul_pos hζ hθ) hden) hc.1,
    (min_le_left _ _).trans hbase⟩


/-- The weighted obstruction implies both source real-power rates with any
safe common radius coefficient. No function or model conclusion is assumed. -/
theorem lower_of_obstruction {p q j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ q) (hqp : q ≤ p)
    {θ C κ ε δ s : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hC : 1 ≤ C)
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hκa : κ ≤ criticalityCoefficient θ C q)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hs : 0 ≤ s)
    (hunit : q ≤ 2 → δ = 1) (hfloor : s ≤ 1 → κ * ε ≤ δ)
    (hbound : (1 - θ) * ε * δ ^ j / j.factorial ≤
      C * ∑ i ∈ Finset.range j, δ ^ (i + 1) * s ^ (p - (i + 1) + 1) /
        (i + 1).factorial) :
    (if q ≤ 2 then
      (criticalityCoefficient θ C j) ^ (1 / ((p - j + 1 : ℕ) : ℝ)) *
        ε ^ (1 / ((p - j + 1 : ℕ) : ℝ))
    else (criticalityCoefficient θ C j * κ ^ (j - 1)) ^ (1 / (p : ℝ)) *
      ε ^ ((j : ℝ) / p)) ≤ s := by
  have hjp := hjq.trans hqp
  have hc := criticalityCoefficient_mem hθ hθ1 hC j
  have hκj := hκa.trans
    (criticalityCoefficient_antitone hθ1.le (zero_lt_one.trans_le hC) hjq)
  have hh := two_mul_criticalityCoefficient_le_sum (zero_lt_one.trans_le hC) j hbound
  have hp : 0 < p := by omega
  split_ifs with hq2
  · have hpower : criticalityCoefficient θ C j * ε ≤ s ^ (p - j + 1) := by
      by_cases hs1 : s ≤ 1
      · exact pow_lower_of_step_le_radius hjp hs hδ (by rw [hunit hq2]; exact hs1) hh
      · exact (mul_le_of_le_one_left hε hc.2 |>.trans hε1).trans
          (one_le_pow₀ (not_le.mp hs1).le)
    have hb := rpow_mul_le_of_pow (p := p - j + 1) (j := 1) (by omega)
      hc.1.le hε hs (by simpa only [pow_one] using hpower)
    simpa only [Nat.cast_one] using hb
  · have hpower : criticalityCoefficient θ C j * κ ^ (j - 1) * ε ^ j ≤ s ^ p := by
      by_cases hs1 : s ≤ 1
      · exact pow_lower_of_mixed_sum hj hjp hs hs1 hδ hc.1.le hκ hκj hε (hfloor hs1) hh
      · have hcoef : criticalityCoefficient θ C j * κ ^ (j - 1) ≤ 1 := by
          simpa only [one_mul] using mul_le_mul hc.2 (pow_le_one₀ hκ hκ1)
            (pow_nonneg hκ _) zero_le_one
        have hh' := mul_le_mul hcoef (pow_le_one₀ hε hε1)
          (pow_nonneg hε j) zero_le_one
        exact (hh'.trans_eq (by ring)).trans (one_le_pow₀ (not_le.mp hs1).le)
    exact rpow_mul_le_of_pow hp (mul_nonneg hc.1.le (pow_nonneg hκ _)) hε hs hpower

end HighOrderStep
