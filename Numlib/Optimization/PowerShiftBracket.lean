import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Scalar brackets for power-regularization multipliers

The product `(t + a) t^p` is strictly increasing on its nonnegative branch.
Roots on those branches turn spectral inequalities into a certified multiplier interval.
-/

namespace Optimization

/-- A shifted power on the nonnegative multiplier half-line. -/
noncomputable def shiftPower (a p t : ℝ) : ℝ := (t + a) * t ^ p

/-- The shifted power strictly increases once both its factors are nonnegative. -/
theorem strictMonoOn_shiftPower {a p : ℝ} (hp : 0 < p) :
    StrictMonoOn (shiftPower a p) (Set.Ici (max 0 (-a))) := by
  intro x hx y _ hxy
  have hx0 : 0 ≤ x := (le_max_left _ _).trans hx
  have hxa : 0 ≤ x + a := by linarith [(le_max_right 0 (-a)).trans hx]
  have hy0 : 0 < y := hx0.trans_lt hxy
  exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0 hxy.le hp.le) hxa).trans_lt
    (mul_lt_mul_of_pos_right (by linarith : x + a < y + a) (Real.rpow_pos_of_pos hy0 p))

/-- Nonnegative-branch roots of two shifted powers enclose any multiplier satisfying
the corresponding inequalities. The lower spectral branch may begin above the multiplier. -/
theorem shiftPower_root_bracket {a b p C t L U : ℝ} (hp : 0 < p)
    (ht : 0 ≤ t) (htb : 0 ≤ t + b)
    (hlo : shiftPower a p t ≤ C) (hup : C ≤ shiftPower b p t)
    (hL : max 0 (-b) ≤ L) (hU : max 0 (-a) ≤ U)
    (hLeq : shiftPower b p L = C) (hUeq : shiftPower a p U = C) :
    L ≤ t ∧ t ≤ U := by
  constructor
  · apply (strictMonoOn_shiftPower hp).le_iff_le hL (max_le ht (by linarith)) |>.mp
    exact hLeq ▸ hup
  · by_cases hta : max 0 (-a) ≤ t
    · apply (strictMonoOn_shiftPower hp).le_iff_le hta hU |>.mp
      exact hUeq ▸ hlo
    · exact (le_of_not_ge hta).trans hU

end Optimization
