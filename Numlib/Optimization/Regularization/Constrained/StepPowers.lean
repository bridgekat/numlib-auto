import Numlib.Optimization.Regularization.Inexact.ComplexityConstants
import Numlib.Optimization.Regularization.Constrained.RunBounds
import Numlib.Optimization.HighOrder.StepCoefficient

/-!
# All-order constrained step and decrease powers

A safe common coefficient is fixed before every requested accuracy. Genuine
feasible criticality obstructions and actual solver radius floors give the
step power epsilon_j^(j/p) at every order, including q=1. Actual objective
ratios convert these into epsilon_j^(j(p+1)/p) function-decrease bounds.
-/

namespace ConstrainedRegularization
open InexactTrustRegion HighOrderStep
open HighOrderRegularization (parameterCap parameterCap_pos)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A safe coefficient below both the actual solver floor and every normalized
obstruction coefficient, chosen independently of all requested accuracies. -/
noncomputable def radiusCoefficient {p q : ℕ} (P : Settings p q) (L S : ℝ) : ℝ :=
  min (P.zeta * P.theta / (8 * (3 * L + S)))
    (criticalityCoefficient P.theta (L + S) q)

/-- The fixed safe radius coefficient is positive and at most one. -/
theorem radiusCoefficient_mem {p q : ℕ} (P : Settings p q) {L S : ℝ}
    (hL : 1 ≤ L) (hS : 0 ≤ S) :
    0 < radiusCoefficient P L S ∧ radiusCoefficient P L S ≤ 1 := by
  have hc := criticalityCoefficient_mem P.theta_pos P.theta_lt_one
    (by linarith : 1 ≤ L + S) q
  have hz := mul_pos P.zeta_pos P.theta_pos
  refine ⟨lt_min (div_pos hz (by linarith)) hc.1, (min_le_right _ _).trans hc.2⟩

/-- The corrected order-j root-step coefficient before all accuracies. -/
noncomputable def rootStepCoefficient {p q : ℕ} (P : Settings p q) (L S : ℝ) (j : ℕ) : ℝ :=
  (criticalityCoefficient P.theta (L + S) j * radiusCoefficient P L S ^ (j - 1)) ^
    (1 / (p : ℝ))

/-- Every fixed root-step coefficient is strictly positive. -/
theorem rootStepCoefficient_pos {p q : ℕ} (P : Settings p q) {L S : ℝ}
    (hL : 1 ≤ L) (hS : 0 ≤ S) (j : ℕ) : 0 < rootStepCoefficient P L S j := by
  have hc := (criticalityCoefficient_mem P.theta_pos P.theta_lt_one
    (by linarith : 1 ≤ L + S) j).1
  have hr := (radiusCoefficient_mem P hL hS).1
  exact Real.rpow_pos_of_pos (mul_pos hc (pow_pos hr _)) _

/-- The genuine finite minimum of all constrained objective-decrease accuracy powers. -/
noncomputable def accuracyFactor {p q : ℕ} (P : Settings p q) (ε : Fin q → ℝ) : ℝ :=
  minimumAccuracy P.order_pos
    (fun a => (ε a) ^ ((modelOrder a : ℝ) * (p + 1 : ℕ) / p))

/-- Positive accuracies give a positive actual minimum rate factor. -/
theorem accuracyFactor_pos {p q : ℕ} (P : Settings p q) {ε : Fin q → ℝ}
    (hε : ∀ a, 0 < ε a) : 0 < accuracyFactor P ε :=
  minimumAccuracy_pos P.order_pos (fun a => Real.rpow_pos_of_pos (hε a) _)

/-- The actual finite rate minimum lies below every order's accuracy power. -/
theorem accuracyFactor_le {p q : ℕ} (P : Settings p q) (ε : Fin q → ℝ) (a : Fin q) :
    accuracyFactor P ε ≤ (ε a) ^ ((modelOrder a : ℝ) * (p + 1 : ℕ) / p) :=
  minimumAccuracy_le P.order_pos _ a

/-- The fixed finite minimum of all positive actual objective-decrease coefficients. -/
noncomputable def commonDecreaseCoefficient {p q : ℕ} (P : Settings p q) (L S : ℝ) : ℝ :=
  minimumAccuracy P.order_pos (fun a =>
    P.eta1 * P.sigmaMin / ((p + 1).factorial : ℝ) *
      rootStepCoefficient P L S (modelOrder a) ^ (p + 1))

/-- The common objective-decrease coefficient is positive before all accuracies. -/
theorem commonDecreaseCoefficient_pos {p q : ℕ} (P : Settings p q) {L S : ℝ}
    (hL : 1 ≤ L) (hS : 0 ≤ S) : 0 < commonDecreaseCoefficient P L S := by
  apply minimumAccuracy_pos P.order_pos
  intro a
  have hr := rootStepCoefficient_pos P hL hS (modelOrder a)
  have hη := P.eta1_pos
  have hσ := P.sigmaMin_pos
  positivity

namespace Run
variable {p q : ℕ} {f : E → ℝ} {X : Set E} {P : Settings p q}
  {ε : Fin q → ℝ} {D : ExecutionData E q} {N : ℕ}

/-- Actual accepted trials before the next constrained certificate force one
of the all-order sharp root-step powers, using only derived solver floors. -/
theorem exists_root_step_lower (h : Run f X P ε D N) (hX : IsClosed X)
    (hf : ContDiff ℝ p f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ i f u - iteratedFDeriv ℝ i f v‖ ≤ L * ‖u - v‖)
    {k : ℕ} (hk : k < N) (ha : P.eta1 ≤ D.ratio k)
    (hnot : ¬TargetAt f X P ε D (k + 1)) :
    ∃ a, rootStepCoefficient P L (parameterCap P L) (modelOrder a) *
      (ε a) ^ ((modelOrder a : ℝ) / p) ≤ ‖D.step k‖ := by
  let S := parameterCap P L
  let κ := radiusCoefficient P L S
  have hS : 0 ≤ S := (parameterCap_pos P L).le
  have hκ := radiusCoefficient_mem P hL hS
  have hp : 0 < p := P.order_pos.trans_le P.order_le
  have hC : 1 ≤ L + S := by linarith
  have hbase : ∃ a, criticalityCoefficient P.theta (L + S) (modelOrder a) *
      κ ^ (modelOrder a - 1) * ε a ^ modelOrder a ≤ ‖D.step k‖ ^ p := by
    by_cases hs : ‖D.step k‖ ≤ 1
    · obtain ⟨a, hb⟩ := h.criticality_obstruction hX hf hL (hlip p hp le_rfl) hk ha hs hnot
      have hm := h.step_two k hk.le (h.continues k hk)
      have hlegal := hm.radius_mem a
      have haj : modelOrder a ≤ p := by have := P.order_le; unfold modelOrder; omega
      have hh := two_mul_criticalityCoefficient_le_sum (zero_lt_one.trans_le hC)
        (modelOrder a) hb
      have hcoef : κ ≤ criticalityCoefficient P.theta (L + S) (modelOrder a) :=
        (min_le_right _ _).trans (criticalityCoefficient_antitone P.theta_lt_one.le
          (zero_lt_one.trans_le hC) a.isLt)
      have hfloor : κ * ε a ≤ D.solvedRadius k a :=
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (h.accuracy_pos a).le).trans
          (h.solved_radius_floor hf hL hlip hk.le (h.continues k hk) hs a)
      exact ⟨a, pow_lower_of_mixed_sum (by unfold modelOrder; omega) haj (norm_nonneg _)
        hs hlegal.1 (criticalityCoefficient_mem P.theta_pos P.theta_lt_one hC _).1.le
        hκ.1.le hcoef (h.accuracy_pos a).le hfloor hh⟩
    · let a : Fin q := ⟨0, P.order_pos⟩
      have hc := (criticalityCoefficient_mem P.theta_pos P.theta_lt_one hC (modelOrder a)).2
      have hh : criticalityCoefficient P.theta (L + S) (modelOrder a) *
          κ ^ (modelOrder a - 1) * ε a ^ modelOrder a ≤ 1 := by
        have hm : criticalityCoefficient P.theta (L + S) (modelOrder a) *
            κ ^ (modelOrder a - 1) ≤ 1 := by
          simpa only [one_mul] using mul_le_mul hc
            (pow_le_one₀ (n := modelOrder a - 1) hκ.1.le hκ.2)
            (pow_nonneg hκ.1.le (modelOrder a - 1)) zero_le_one
        have hn := mul_le_mul hm
          (pow_le_one₀ (n := modelOrder a) (h.accuracy_pos a).le (h.accuracy_le_one a))
          (pow_nonneg (h.accuracy_pos a).le (modelOrder a)) zero_le_one
        simpa only [one_mul] using hn
      exact ⟨a, hh.trans (one_le_pow₀ (not_le.mp hs).le)⟩
  obtain ⟨a, ha⟩ := hbase
  have hc := (criticalityCoefficient_mem P.theta_pos P.theta_lt_one hC (modelOrder a)).1
  have hh := rpow_mul_le_of_pow hp (mul_nonneg hc.le (pow_nonneg hκ.1.le _))
    (h.accuracy_pos a).le (norm_nonneg _) ha
  exact ⟨a, hh⟩

/-- A genuine accepted objective ratio converts the constrained step powers
into a fixed all-order objective decrease before the next true certificate. -/
theorem function_decrease_uniform (h : Run f X P ε D N) (hX : IsClosed X)
    (hf : ContDiff ℝ p f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ i f u - iteratedFDeriv ℝ i f v‖ ≤ L * ‖u - v‖)
    {k : ℕ} (hk : k < N) (ha : P.eta1 ≤ D.ratio k)
    (hnot : ¬TargetAt f X P ε D (k + 1)) :
    commonDecreaseCoefficient P L (parameterCap P L) * accuracyFactor P ε ≤
      f (D.point k) - f (D.point (k + 1)) := by
  obtain ⟨a, hb⟩ := h.exists_root_step_lower hX hf hL hlip hk ha hnot
  have hr := rootStepCoefficient_pos P hL (parameterCap_pos P L).le (modelOrder a)
  have hp := InexactRegularization.pow_lower_of_root_step (n := p + 1) hr.le
    (h.accuracy_pos a).le hb
  have hη := P.eta1_pos
  have hσ := P.sigmaMin_pos
  have hc : commonDecreaseCoefficient P L (parameterCap P L) ≤
      P.eta1 * P.sigmaMin / ((p + 1).factorial : ℝ) *
        rootStepCoefficient P L (parameterCap P L) (modelOrder a) ^ (p + 1) :=
    minimumAccuracy_le P.order_pos _ a
  have hcommon := mul_le_mul hc (accuracyFactor_le P ε a)
    (accuracyFactor_pos P h.accuracy_pos).le (by positivity)
  have hscale := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ P.eta1 * P.sigmaMin / ((p + 1).factorial : ℝ) by positivity)
  apply hcommon.trans
  apply le_trans _ (h.modelTrace.successful_decrease hk ha).le
  have hexp : (modelOrder a : ℝ) / p * (p + 1 : ℕ) =
      (modelOrder a : ℝ) * (p + 1 : ℕ) / p := by ring
  rw [hexp] at hscale
  nlinarith only [hscale]

end Run
end ConstrainedRegularization
