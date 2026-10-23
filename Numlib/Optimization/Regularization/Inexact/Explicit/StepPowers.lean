import Numlib.Optimization.Regularization.Inexact.Explicit.Obstruction
import Numlib.Optimization.Regularization.Inexact.Explicit.Radius
import Numlib.Optimization.HighOrder.StepCoefficient

/-!
# Actual explicit-accuracy step powers before literal stopping

A common radius coefficient is the minimum of the proved radius floor and the
smallest normalized obstruction coefficient. This additional normalization
makes both branches of the mixed-sum argument valid. Its constants precede
all requested accuracies and preserve the low- and high-order source rates.
-/

namespace InexactRegularization.Explicit
open InexactTrustRegion HighOrderStep
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The common coefficient safely used in the high-order power argument.
It never exceeds either the actual radius floor or an obstruction coefficient. -/
noncomputable def safeRadiusCoefficient {p q : ℕ} (P : Settings p q) (L M S : ℝ) : ℝ :=
  min (stepRadiusCoefficient P.zeta P.theta M S)
    (criticalityCoefficient (1 - P.zeta / 2 + P.theta) (L + S + 4 * P.stepCoefficient) q)

namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Primitive successful trials that have not passed the literal stopping check force
one of the source step powers. A smaller common radius coefficient repairs the
high-order coefficient comparison, without changing the accuracy exponents.
All analytic caps and their coefficient precede the accuracies. -/
theorem step_powers_of_cap (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    (hmargin : P.theta < P.zeta / 2)
    {L M S : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    {k : ℕ} (hk : k < N) (ht : k ∈ D.trials) (haccepted : P.eta1 ≤ D.ratio k)
    (hnot : ¬StopsAt P ε D (k + 1)) :
    let C := L + S + 4 * P.stepCoefficient
    let κ := safeRadiusCoefficient P L M S
    0 < κ ∧ κ ≤ 1 ∧ ∃ a,
      (q ≤ 2 → criticalityCoefficient (1 - P.zeta / 2 + P.theta) C (modelOrder a) * ε a ≤
        ‖D.step k‖ ^ (p - modelOrder a + 1)) ∧
      (2 < q → criticalityCoefficient (1 - P.zeta / 2 + P.theta) C (modelOrder a) *
          κ ^ (modelOrder a - 1) *
        ε a ^ modelOrder a ≤ ‖D.step k‖ ^ p) := by
  classical
  let C := L + S + 4 * P.stepCoefficient
  let κ := safeRadiusCoefficient P L M S
  have hS : 0 ≤ S := (h.updates.pos (show 0 ≤ N by omega)).le.trans (hparam 0 (by omega))
  have hprod := P.stepCoefficient_pos.le
  have heff0 : 0 < 1 - P.zeta / 2 + P.theta := by
    have := P.zeta_le_one; have := P.theta_pos; linarith
  have heff1 : 1 - P.zeta / 2 + P.theta < 1 := by linarith
  have hC : 1 ≤ C := by dsimp [C]; nlinarith
  have hradius := stepRadiusCoefficient_mem (σ := S) P.zeta_pos P.zeta_le_one
    P.theta_pos P.theta_lt_one.le hM
  have hcoef := criticalityCoefficient_mem heff0 heff1 hC q
  have hκ : 0 < κ := lt_min hradius.1 hcoef.1
  have hκ1 : κ ≤ 1 := (min_le_left _ _).trans hradius.2
  have hκcoef : ∀ a : Fin q, κ ≤ criticalityCoefficient (1 - P.zeta / 2 + P.theta) C
      (modelOrder a) := by
    intro a
    exact (min_le_right _ _).trans
      (criticalityCoefficient_antitone heff1.le (zero_lt_one.trans_le hC) a.isLt)
  have hk1 : k + 1 ≤ N := by omega
  have hr := h.radius_floor_sharp hM hparam hjet
  have hfloor : ∀ a, κ * ε a ≤ D.startRadius (k + 1) a := fun a =>
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (h.accuracy_pos a).le).trans (hr.1 _ hk1 a)
  refine ⟨hκ, hκ1, ?_⟩
  by_cases hs : ‖D.step k‖ < 1
  · obtain ⟨a, ha⟩ := h.nonstopping_obstruction hf (zero_le_one.trans hL) hlip hk ht
      haccepted hs (hparam k hk.le) hnot
    have hq := P.order_le
    have horder : modelOrder a ≤ p := by unfold modelOrder; omega
    have ha' : (1 - (1 - P.zeta / 2 + P.theta)) * ε a *
        D.startRadius (k + 1) a ^ modelOrder a / (modelOrder a).factorial ≤ C *
          ∑ i ∈ Finset.range (modelOrder a), D.startRadius (k + 1) a ^ (i + 1) *
            ‖D.step k‖ ^ (p - (i + 1) + 1) / (i + 1).factorial := by
      convert ha using 1; ring
    have hbound := two_mul_criticalityCoefficient_le_sum (zero_lt_one.trans_le hC)
      (modelOrder a) ha'
    refine ⟨a, ?_, ?_⟩
    · intro hq2
      have hrad : D.startRadius (k + 1) a = 1 := by
        rw [h.radius_trial k hk ht, ite_eq_left ⟨haccepted, hs⟩]
        exact hr.2.2.2 k hk ((h.trial_rule k hk).mp ht).1 hs a (by
          unfold modelOrder
          omega)
      have hsδ : ‖D.step k‖ ≤ D.startRadius (k + 1) a := by rw [hrad]; exact hs.le
      exact pow_lower_of_step_le_radius horder (norm_nonneg _)
        (h.startRadius_mem hk1 a).1 hsδ hbound
    · intro _
      exact pow_lower_of_mixed_sum (by unfold modelOrder; omega) horder (norm_nonneg _)
        hs.le (h.startRadius_mem hk1 a).1
        (criticalityCoefficient_mem heff0 heff1 hC _).1.le hκ.le
        (hκcoef a) (h.accuracy_pos a).le (hfloor a) hbound
  · have hlarge : 1 ≤ ‖D.step k‖ := not_lt.mp hs
    let a : Fin q := ⟨0, P.order_pos⟩
    have hac := criticalityCoefficient_mem heff0 heff1 hC (modelOrder a)
    refine ⟨a, fun _ => ?_, fun _ => ?_⟩
    · apply le_trans _ (one_le_pow₀ hlarge)
      exact (mul_le_mul hac.2 (h.accuracy_le_one a) (h.accuracy_pos a).le zero_le_one).trans_eq
        (by ring)
    · have hh : criticalityCoefficient (1 - P.zeta / 2 + P.theta) C (modelOrder a) *
          κ ^ (modelOrder a - 1) ≤ 1 := by
        exact (mul_le_mul hac.2 (pow_le_one₀ hκ.le hκ1)
          (pow_nonneg hκ.le _) zero_le_one).trans_eq (by ring)
      exact ((mul_le_mul hh (pow_le_one₀ (h.accuracy_pos a).le (h.accuracy_le_one a))
        (pow_nonneg (h.accuracy_pos a).le _) zero_le_one).trans_eq (by ring)).trans
          (one_le_pow₀ hlarge)

/-- The actual successful-step power bounds give both source real-power
rates, with a common coefficient independent of all requested accuracies. -/
theorem step_lower_of_cap (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    (hmargin : P.theta < P.zeta / 2)
    {L M S : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    {k : ℕ} (hk : k < N) (ht : k ∈ D.trials) (haccepted : P.eta1 ≤ D.ratio k)
    (hnot : ¬StopsAt P ε D (k + 1)) :
    let C := L + S + 4 * P.stepCoefficient
    let κ := safeRadiusCoefficient P L M S
    0 < κ ∧ κ ≤ 1 ∧ ∃ a,
      (if q ≤ 2 then
        (criticalityCoefficient (1 - P.zeta / 2 + P.theta) C (modelOrder a)) ^
          (1 / ((p - modelOrder a + 1 : ℕ) : ℝ)) *
        (ε a) ^ (1 / ((p - modelOrder a + 1 : ℕ) : ℝ))
      else
        (criticalityCoefficient (1 - P.zeta / 2 + P.theta) C (modelOrder a) *
          κ ^ (modelOrder a - 1)) ^
          (1 / (p : ℝ)) * (ε a) ^ ((modelOrder a : ℝ) / p)) ≤ ‖D.step k‖ := by
  obtain ⟨hκ, hκ1, a, hlo, hhi⟩ := h.step_powers_of_cap hf hmargin hL hM hlip hparam hjet
    hk ht haccepted hnot
  have hS : 0 ≤ S := (h.updates.pos (show 0 ≤ N by omega)).le.trans (hparam 0 (by omega))
  have hC : 1 ≤ L + S + 4 * P.stepCoefficient := by
    have hp := P.stepCoefficient_pos.le
    nlinarith
  have heff0 : 0 < 1 - P.zeta / 2 + P.theta := by
    have := P.zeta_le_one; have := P.theta_pos; linarith
  have heff1 : 1 - P.zeta / 2 + P.theta < 1 := by linarith
  have hcoef := criticalityCoefficient_mem heff0 heff1 hC (modelOrder a)
  refine ⟨hκ, hκ1, a, ?_⟩
  split_ifs with hq
  · have hh := rpow_mul_le_of_pow (p := p - modelOrder a + 1) (j := 1) (by omega)
      hcoef.1.le (h.accuracy_pos a).le (norm_nonneg _) (by simpa only [pow_one] using hlo hq)
    simpa only [Nat.cast_one] using hh
  · exact rpow_mul_le_of_pow (P.order_pos.trans_le P.order_le)
      (mul_nonneg hcoef.1.le (pow_nonneg hκ.le _)) (h.accuracy_pos a).le (norm_nonneg _)
      (hhi (by omega))

end Run
end InexactRegularization.Explicit
