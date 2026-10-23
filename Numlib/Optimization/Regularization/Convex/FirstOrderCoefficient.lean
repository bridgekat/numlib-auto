import Numlib.Optimization.Regularization.Convex.FirstOrderComplexity

/-!
# A uniform upper bound for the actual first-order decrease coefficient

The legal source model tolerance exceeds one half. The regularization cap is
at least the parameter floor. These primitive facts imply that the exact
factorial successful-decrease coefficient is at most one, independently of
accuracies, objective data and execution length.
-/

namespace ConvexRegularization
open HighOrderRegularization

/-- The exact source first-order decrease coefficient never exceeds one. -/
theorem firstDecreaseCoefficient_le_one {p : ℕ} (P : Settings p) {L : ℝ} (hL : 0 < L) :
    firstDecreaseCoefficient P L ≤ 1 := by
  let d := L + parameterCap P L + P.theta * p.factorial
  let s := stepConstant p L (parameterCap P L) P.theta
  have hθ : (1 / 2 : ℝ) < P.theta := by
    have := P.theta_lower
    have := P.tau_pos
    linarith
  have hcap : P.sigmaMin ≤ parameterCap P L :=
    P.sigmaMin_le_initial.trans (le_max_left _ _)
  have hcap0 := P.sigmaMin_pos.trans_le hcap
  have hf : (0 : ℝ) < p.factorial := by positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hs : 0 < s := stepConstant_pos p hL hcap0.le (by linarith)
  have hs2 : s ≤ 2 := by
    change p.factorial / d ≤ 2
    apply (div_le_iff₀ hd).mpr
    dsimp [d]
    nlinarith
  have hden : P.sigmaMin ≤ d := by
    dsimp [d]
    nlinarith
  have hmin : P.sigmaMin * s ≤ p.factorial := by
    change P.sigmaMin * (p.factorial / d) ≤ p.factorial
    calc _ = p.factorial * (P.sigmaMin / d) := by ring
      _ ≤ p.factorial * 1 := mul_le_mul_of_nonneg_left ((div_le_one hd).mpr hden) hf.le
      _ = _ := mul_one _
  have hη : P.eta1 ≤ 1 := P.eta1_le_eta2.trans P.eta2_lt_one.le
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast P.order_pos
  have hpf : (0 : ℝ) < p + 1 := by positivity
  have hfac : ((p + 1).factorial : ℝ) = ((p : ℝ) + 1) * p.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hfront : P.eta1 * P.sigmaMin / (p + 1).factorial * s ≤ (1 / 2 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hmin P.eta1_pos.le
    have hh' : P.eta1 * P.sigmaMin / (p + 1).factorial * s ≤ P.eta1 / (p + 1) := by
      calc _ = (P.eta1 * (P.sigmaMin * s)) / (p + 1).factorial := by ring
        _ ≤ (P.eta1 * p.factorial) / (p + 1).factorial :=
          div_le_div_of_nonneg_right hh (by positivity)
        _ = P.eta1 / (p + 1) := by rw [hfac]; field_simp
    exact hh'.trans (by
      apply (div_le_iff₀ hpf).mpr
      linarith)
  have he : (((p + 1 : ℕ) : ℝ) / p) = 1 + 1 / p := by
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hroot : s ^ (1 / (p : ℝ)) ≤ 2 := by
    have hb := Real.rpow_le_rpow hs.le hs2 (show 0 ≤ 1 / (p : ℝ) by positivity)
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show 1 / (p : ℝ) ≤ 1 by exact (div_le_one (by positivity)).mpr hpR)
    exact hb.trans (by simpa only [Real.rpow_one] using hh)
  change P.eta1 * P.sigmaMin / (p + 1).factorial * s ^ (((p + 1 : ℕ) : ℝ) / p) ≤ 1
  rw [he, Real.rpow_add hs, Real.rpow_one, ←mul_assoc]
  exact (mul_le_mul hfront hroot (Real.rpow_nonneg hs.le _) (by norm_num)).trans_eq
    (by norm_num)

end ConvexRegularization
