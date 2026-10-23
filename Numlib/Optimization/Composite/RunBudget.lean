import Numlib.Optimization.Composite.ComplexityConstants
import Numlib.Optimization.EvaluationComplexity.Decrease

/-!
# Actual composite objective budgets

The accepted-step power bounds consume a fixed positive coefficient times the
true minimum accuracy power. The first target-reaching success contributes at
most one extra accepted step and does not need a pre-target decrease floor.
-/

namespace Composite
open InexactTrustRegion EvaluationComplexity
open HighOrderRegularization (parameterCap parameterCap_pos)
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- Each of `f` and `c` is evaluated initially and at every acceptance trial. -/
def functionEvaluations (N : ℕ) : ℕ := N + 1

/-- Each requested derivative order is evaluated initially and at accepted points. -/
noncomputable def derivativeEvaluations (ρ : ℕ → ℝ) (η : ℝ) (N : ℕ) : ℕ :=
  (successfulIterations {i | η ≤ ρ i} N).card + 1

namespace Run
variable {p q : ℕ} {f : E → ℝ} {c : E → F} {h : F → ℝ}
  {P : Settings p q} {ε : Fin q → ℝ} {D : ExecutionData E q} {N : ℕ}

/-- Before a true next-iterate certificate, an accepted composite trial consumes
the fixed general decrease coefficient times the actual minimum accuracy power. -/
theorem function_decrease_general (hr : Run f c h P ε D N)
    (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c) {Lf Lc : ℝ} {K : NNReal}
    (hLf : 1 ≤ Lf) (hLc : 0 ≤ Lc) (hh : LipschitzWith K h)
    (hlipf : ∀ u v,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ u v,
      ‖iteratedFDeriv ℝ p c u - iteratedFDeriv ℝ p c v‖ ≤ Lc * ‖u - v‖)
    {k : ℕ} (hk : k < N) (haccepted : P.eta1 ≤ D.ratio k)
    (hfloor : ‖D.step k‖ < 1 → ∀ a,
      radiusCoefficient P (Lf + (K : ℝ) * Lc)
        (parameterCap P (Lf + (K : ℝ) * Lc)) * ε a ≤ D.solvedRadius k a)
    (hn : ¬TargetAt f c h P ε D (k + 1)) :
    generalDecreaseCoefficient P (Lf + (K : ℝ) * Lc)
        (parameterCap P (Lf + (K : ℝ) * Lc)) * generalAccuracyFactor P ε ≤
      f (D.point k) + h (c (D.point k)) -
        (f (D.point (k + 1)) + h (c (D.point (k + 1)))) := by
  let L := Lf + (K : ℝ) * Lc
  let S := parameterCap P L
  have hL : 1 ≤ L := by dsimp [L]; nlinarith [mul_nonneg K.coe_nonneg hLc]
  have hS : 0 ≤ S := (parameterCap_pos P L).le
  have hcap := hr.parameter_le hf hc (zero_le_one.trans hLf) hLc hh hlipf hlipc hk.le
  obtain ⟨a, ha⟩ := hr.exists_power_lower hf hc hLf hLc hS hh hlipf hlipc
    hk haccepted hcap hfloor hn
  have hbase : 0 ≤ P.eta1 * P.sigmaMin / ((p + 1).factorial : ℝ) := by
    exact div_nonneg (mul_nonneg P.eta1_pos.le P.sigmaMin_pos.le) (Nat.cast_nonneg _)
  have hmin := mul_le_mul_of_nonneg_left (generalAccuracyFactor_le P ε a)
    (pow_nonneg (stepCoefficient_mem P hL hS).1.le (q + 1))
  have hb := mul_le_mul_of_nonneg_left (hmin.trans ha) hbase
  apply le_trans _ (hr.successful_decrease hk haccepted)
  convert hb using 1
  unfold generalDecreaseCoefficient
  ring

/-- Unit-radius first-order accepted trials consume the sharper first-order
accuracy power with a coefficient fixed before all accuracies. -/
theorem function_decrease_unit (hr : Run f c h P ε D N) (hq : q = 1)
    (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c) {Lf Lc : ℝ} {K : NNReal}
    (hLf : 1 ≤ Lf) (hLc : 0 ≤ Lc) (hh : LipschitzWith K h)
    (hlipf : ∀ u v,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ u v,
      ‖iteratedFDeriv ℝ p c u - iteratedFDeriv ℝ p c v‖ ≤ Lc * ‖u - v‖)
    {k : ℕ} (hk : k < N) (haccepted : P.eta1 ≤ D.ratio k)
    (hunit : ∀ a, D.solvedRadius k a = 1)
    (hn : ¬TargetAt f c h P ε D (k + 1)) :
    unitDecreaseCoefficient P (Lf + (K : ℝ) * Lc)
        (parameterCap P (Lf + (K : ℝ) * Lc)) * unitAccuracyFactor P ε ≤
      f (D.point k) + h (c (D.point k)) -
        (f (D.point (k + 1)) + h (c (D.point (k + 1)))) := by
  let L := Lf + (K : ℝ) * Lc
  let S := parameterCap P L
  have hL : 1 ≤ L := by dsimp [L]; nlinarith [mul_nonneg K.coe_nonneg hLc]
  have hS : 0 ≤ S := (parameterCap_pos P L).le
  have hcap := hr.parameter_le hf hc (zero_le_one.trans hLf) hLc hh hlipf hlipc hk.le
  obtain ⟨a, ha⟩ := hr.exists_unit_power_lower hq hf hc hLf hLc hS hh hlipf hlipc
    hk haccepted hcap hunit hn
  have hγ := CompositeStep.coefficient_mem P.theta_pos P.theta_lt_one
    (by linarith : 1 ≤ L + S) (by linarith : 0 ≤ 2 * L) 1
  have hp : 0 < p := P.order_pos.trans_le P.order_le
  have hroot := HighOrderStep.rpow_mul_le_of_pow (j := 1) hp hγ.1.le
    (hr.accuracy_pos a).le (norm_nonneg (D.step k)) (by simpa only [pow_one] using ha)
  have hpow := InexactRegularization.pow_lower_of_root_step (n := p + 1)
    (Real.rpow_nonneg hγ.1.le _) (hr.accuracy_pos a).le hroot
  have he : (1 / (p : ℝ)) * (p + 1 : ℕ) = unitExponent p := by
    unfold unitExponent
    ring
  simp only [Nat.cast_one, he] at hpow
  have hmin := mul_le_mul_of_nonneg_left (unitAccuracyFactor_le P ε a)
    (pow_nonneg (unitStepCoefficient_pos P hL hS).le (p + 1))
  have hpower : unitStepCoefficient P L S ^ (p + 1) * unitAccuracyFactor P ε ≤
      ‖D.step k‖ ^ (p + 1) := hmin.trans hpow
  have hbase : 0 ≤ P.eta1 * P.sigmaMin / ((p + 1).factorial : ℝ) := by
    exact div_nonneg (mul_nonneg P.eta1_pos.le P.sigmaMin_pos.le) (Nat.cast_nonneg _)
  have hb := mul_le_mul_of_nonneg_left hpower hbase
  apply le_trans _ (hr.successful_decrease hk haccepted)
  convert hb using 1
  unfold unitDecreaseCoefficient
  ring

omit [FiniteDimensional ℝ E] in
/-- An objective budget bounds every success in a prefix whose endpoint still
precedes the true target. The decrease premise is supplied by actual step bounds. -/
theorem successful_card_le_of_no_target_endpoint (hr : Run f c h P ε D N)
    {d wlow : ℝ} (hd : 0 < d)
    (hlow : wlow ≤ f (D.point N) + h (c (D.point N)))
    (hdecrease : ∀ k < N, P.eta1 ≤ D.ratio k → ¬TargetAt f c h P ε D (k + 1) →
      d ≤ f (D.point k) + h (c (D.point k)) -
        (f (D.point (k + 1)) + h (c (D.point (k + 1)))))
    (hn : ∀ k ≤ N, ¬TargetAt f c h P ε D k) :
    ((successfulIterations {i | P.eta1 ≤ D.ratio i} N).card : ℝ) ≤
      (f (D.point 0) + h (c (D.point 0)) - wlow) / d := by
  apply card_successful_le_gap_div (S := {i | P.eta1 ≤ D.ratio i})
    (f := fun i => f (D.point i) + h (c (D.point i))) hd hlow
  · intro k hk ha
    exact hdecrease k hk ha (hn (k + 1) (by omega))
  · intro k hk ha
    exact (hr.objective_eq_of_unsuccessful hk ha).le

omit [FiniteDimensional ℝ E] in
/-- The first success reaching a true target adds at most one to the objective
budget; its step need not satisfy a pre-target decrease floor. -/
theorem successful_card_le (hr : Run f c h P ε D N)
    {d wlow : ℝ} (hd : 0 < d) (hlow : ∀ x, wlow ≤ f x + h (c x))
    (hdecrease : ∀ k < N, P.eta1 ≤ D.ratio k → ¬TargetAt f c h P ε D (k + 1) →
      d ≤ f (D.point k) + h (c (D.point k)) -
        (f (D.point (k + 1)) + h (c (D.point (k + 1)))))
    (hn : ∀ k < N, ¬TargetAt f c h P ε D k) :
    ((successfulIterations {i | P.eta1 ≤ D.ratio i} N).card : ℝ) ≤
      (f (D.point 0) + h (c (D.point 0)) - wlow) / d + 1 := by
  cases N with
  | zero =>
    simp only [successfulIterations, Finset.range_zero, Finset.filter_empty,
      Finset.card_empty, Nat.cast_zero]
    exact le_add_of_le_of_nonneg (div_nonneg (sub_nonneg.mpr (hlow _)) hd.le) zero_le_one
  | succ n =>
    have hb := (hr.restrict (Nat.le_succ n)).successful_card_le_of_no_target_endpoint hd
      (hlow _) (fun k hk => hdecrease k (hk.trans_le (Nat.le_succ n)))
      (fun k hk => hn k (by omega))
    have hcard : (successfulIterations {i | P.eta1 ≤ D.ratio i} (n + 1)).card ≤
        (successfulIterations {i | P.eta1 ≤ D.ratio i} n).card + 1 := by
      rw [card_successful_succ]
      split_ifs <;> omega
    have hcast : ((successfulIterations {i | P.eta1 ≤ D.ratio i} (n + 1)).card : ℝ) ≤
        (successfulIterations {i | P.eta1 ≤ D.ratio i} n).card + 1 := by
      exact_mod_cast hcard
    linarith

omit [FiniteDimensional ℝ E] in
/-- The genuine objective budget and parameter update mechanism bound both
initialized evaluation schedules, allowing the first target-reaching success. -/
theorem evaluation_bounds (hr : Run f c h P ε D N) {d wlow S : ℝ}
    (hd : 0 < d) (hlow : ∀ x, wlow ≤ f x + h (c x))
    (hdecrease : ∀ k < N, P.eta1 ≤ D.ratio k → ¬TargetAt f c h P ε D (k + 1) →
      d ≤ f (D.point k) + h (c (D.point k)) -
        (f (D.point (k + 1)) + h (c (D.point (k + 1)))))
    (hn : ∀ k < N, ¬TargetAt f c h P ε D k) (hcap : D.parameter N ≤ S) :
    (functionEvaluations N : ℝ) ≤
        (f (D.point 0) + h (c (D.point 0)) - wlow) / d *
          (1 + |Real.log P.gamma1| / Real.log P.gamma2) +
        (1 + |Real.log P.gamma1| / Real.log P.gamma2 +
          Real.log (S / P.sigmaInitial) / Real.log P.gamma2 + 1) ∧
      (derivativeEvaluations D.ratio P.eta1 N : ℝ) ≤
        (f (D.point 0) + h (c (D.point 0)) - wlow) / d + 2 := by
  have hs := hr.successful_card_le hd hlow hdecrease hn
  have hu := hr.modelTrace.updates
  have ht := iteration_bound_of_parameter_upper
    (S := {i | P.eta1 ≤ D.ratio i}) (fun i hi => hu.pos hi)
    P.gamma1_pos P.gamma1_lt_one P.one_lt_gamma2 hcap
    (fun i hi ha => hu.successful_ge hi ha)
    (fun i hi ha => hu.unsuccessful_ge hi ha)
  rw [hr.initial_parameter] at ht
  have hfac : 0 ≤ 1 + |Real.log P.gamma1| / Real.log P.gamma2 :=
    add_nonneg zero_le_one (div_nonneg (abs_nonneg _) (Real.log_pos P.one_lt_gamma2).le)
  have hb := add_le_add_left (mul_le_mul_of_nonneg_right hs hfac)
    (Real.log (S / P.sigmaInitial) / Real.log P.gamma2)
  constructor
  · simp only [functionEvaluations, Nat.cast_add, Nat.cast_one]
    have hh := add_le_add_left (ht.trans hb) 1
    convert hh using 1
    ring
  · simp only [derivativeEvaluations, Nat.cast_add, Nat.cast_one]
    linarith

end Run
end Composite
