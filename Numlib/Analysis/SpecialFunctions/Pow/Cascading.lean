import Numlib.Analysis.SpecialFunctions.Pow.Differences

/-!
# Weighted decrease under positive fractional powers

A secant-power estimate transfers weighted power decreases under a fixed
relative decrease condition. The complementary case gives a direct relative
decrease at every positive power.
-/

namespace Real
/-- A weighted large-power decrease transfers to a smaller power when the
endpoint is a fixed positive fraction of the starting value. -/
theorem cascading_decrease {a b β ℓ q κ u α e : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a) (hβ : 0 ≤ β)
    (hβa : β * a ≤ b) (hq : 0 < q) (hqℓ : q ≤ ℓ)
    (hκ : 0 ≤ κ) (hu : 0 ≤ u) (he : 0 ≤ e)
    (hd : κ * ℓ * u ^ α * b ^ e ≤ a ^ ℓ - b ^ ℓ) :
    κ * q * β ^ e * u ^ α / a ^ (ℓ - q - e) ≤ a ^ q - b ^ q := by
  have hℓ : 0 < ℓ := hq.trans_le hqℓ
  have hD : 0 < ℓ / q * a ^ (ℓ - q) :=
    mul_pos (div_pos hℓ hq) (rpow_pos_of_pos ha _)
  have hm : κ * ℓ * u ^ α * (β * a) ^ e ≤ κ * ℓ * u ^ α * b ^ e :=
    mul_le_mul_of_nonneg_left (rpow_le_rpow (mul_nonneg hβ ha.le) hβa he)
      (mul_nonneg (mul_nonneg hκ hℓ.le) (rpow_nonneg hu _))
  have hh := (div_le_div_of_nonneg_right (hm.trans hd) hD.le).trans
    (rpow_sub_div_le_rpow_sub hb hba hq hqℓ)
  convert hh using 1
  rw [mul_rpow hβ ha.le, rpow_sub ha]
  field_simp

/-- A fixed relative residual reduction gives both smaller-power decrease bounds. -/
theorem relative_cascading_decrease {a b β q : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hrel : b ≤ β * a) (hq : 0 < q) :
    0 < 1 - β ^ q ∧
    (1 - β ^ q) * a ^ q ≤ a ^ q - b ^ q ∧
    (1 - β ^ q) * b ^ q ≤ (1 - β ^ q) * a ^ q := by
  have hβq : β ^ q < 1 := rpow_lt_one hβ hβ1 hq
  have hh := rpow_le_rpow hb hrel hq.le
  rw [mul_rpow hβ (hb.trans hba)] at hh
  refine ⟨sub_pos.mpr hβq, ?_, ?_⟩
  · nlinarith
  · exact mul_le_mul_of_nonneg_left (rpow_le_rpow hb hba hq.le) (by linarith)
end Real
