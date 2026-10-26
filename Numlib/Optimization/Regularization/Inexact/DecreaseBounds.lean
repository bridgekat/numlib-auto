import Numlib.Optimization.Regularization.Inexact.RunBudget

/-!
# Corrected model and function decreases for implicit accuracy

Actual candidate nonoptimality replaces mere nontermination in all-trial sharp
bounds. The guarded request rules derive every tensor error; the safe radius
coefficient and genuine parameter cap precede all requested accuracies.
-/

namespace InexactRegularization
open InexactTrustRegion HighOrderStep
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

omit [FiniteDimensional ℝ E] in
/-- Acceptance with the actual true-objective ratio transfers any computed
Taylor prediction floor to a true objective drop. -/
theorem function_decrease_ge_computed (h : Run f P ε D N) {k : ℕ} (hk : k < N)
    (ht : k ∈ D.trials) (ha : P.eta1 ≤ D.ratio k) :
    P.eta1 * TaylorModel.jetDecrement (D.jet k) p (D.step k) ≤
      f (D.point k) - f (D.point (k + 1)) := by
  have hr := ha
  rw [h.ratio k hk ht] at hr
  have hd := (le_div_iff₀ (h.toModelTrace.toOracleTrace.denominator_pos hk ht)).mp hr
  simpa only [h.point_trial k hk ht, ite_eq_left ha] using hd

/-- Failure of true approximate optimality at an actual short trial candidate
forces the source weighted step-power obstruction in some order. The
only parameter bound is a genuine current cap; no model-derivative identity,
criticality comparison or step-length conclusion is assumed. -/
theorem criticality_obstruction_candidate (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    {L S : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    {k : ℕ} (hk : k < N) (ht : k ∈ D.trials)
    (hs : ‖D.step k‖ < 1) (hS : D.parameter k ≤ S)
    (hnot : ¬OptimalityAt f ε ((D.point k + D.step k)) (D.solvedRadius k)) :
    ∃ a, (1 - P.theta) * ε a * D.solvedRadius k a ^ modelOrder a /
        (modelOrder a).factorial ≤
      (L + S + 3 * P.errorBound * P.stepCoefficient) *
        ∑ i ∈ Finset.range (modelOrder a), D.solvedRadius k a ^ (i + 1) *
          ‖D.step k‖ ^ (p - (i + 1) + 1) / (i + 1).factorial := by
  classical
  have hmstep := h.step_two k hk ((h.trial_rule k hk).mp ht).1
  have hlegal := hmstep.radius_mem (h.checkedRadius_mem hk.le)
  have hfail : ∃ a, ε a * D.solvedRadius k a ^ modelOrder a /
      (modelOrder a).factorial <
        TaylorModel.criticality f (modelOrder a) ((D.point k + D.step k))
          (D.solvedRadius k a) := by
    by_contra hn
    have hh : ∀ a, TaylorModel.criticality f (modelOrder a) ((D.point k + D.step k))
        (D.solvedRadius k a) ≤ ε a * D.solvedRadius k a ^ modelOrder a /
          (modelOrder a).factorial := fun a => not_lt.mp (fun ha => hn ⟨a, ha⟩)
    exact hnot ⟨hlegal, hh⟩
  obtain ⟨a, ha⟩ := hfail
  refine ⟨a, ?_⟩
  have hq := P.order_le
  have horder : modelOrder a ≤ p := by unfold modelOrder; omega
  have hδ : 0 ≤ D.solvedRadius k a := (hlegal a).1.le
  have hK := mul_nonneg P.errorBound_nonneg P.stepCoefficient_pos.le
  have herr := criticality_le_model_add_error f hf horder hL hK (h.updates.pos hk.le).le hδ
    hlip (D.jet k) (D.point k) (D.step k) (fun i hi hip => h.short_tensor_error hk ht hs hi hip)
  have hm := (h.step_two k hk ((h.trial_rule k hk).mp ht).1).criticality P.zeta_pos hs a
  change TaylorModel.criticality
    (ModelDecrease.penalized (TaylorModel.ofJet (D.jet k) p) p (D.parameter k))
    (modelOrder a) (D.step k) (D.solvedRadius k a) ≤
      P.theta * ε a * D.solvedRadius k a ^ modelOrder a / (modelOrder a).factorial at hm
  have hsum : 0 ≤ ∑ i ∈ Finset.range (modelOrder a), D.solvedRadius k a ^ (i + 1) *
      ‖D.step k‖ ^ (p - (i + 1) + 1) / (i + 1).factorial :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hcap := mul_le_mul_of_nonneg_right
    (show L + D.parameter k + 3 * (P.errorBound * P.stepCoefficient) ≤
      L + S + 3 * P.errorBound * P.stepCoefficient by nlinarith) hsum
  have he : (1 - P.theta) * ε a * D.solvedRadius k a ^ modelOrder a /
      (modelOrder a).factorial = ε a * D.solvedRadius k a ^ modelOrder a /
        (modelOrder a).factorial -
          P.theta * ε a * D.solvedRadius k a ^ modelOrder a / (modelOrder a).factorial := by ring
  rw [he]
  linarith


/-- Actual trial candidates that have not achieved true optimality force
one of the source step powers. A smaller common radius coefficient repairs the
high-order coefficient comparison, without changing the accuracy exponents.
All analytic caps and their coefficient precede the accuracies. -/
theorem step_powers_candidate (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    {L M S : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    {k : ℕ} (hk : k < N) (ht : k ∈ D.trials)
    (hnot : ¬OptimalityAt f ε ((D.point k + D.step k)) (D.solvedRadius k)) :
    let C := L + S + 3 * P.errorBound * P.stepCoefficient
    let κ := safeRadiusCoefficient P L M S
    0 < κ ∧ κ ≤ 1 ∧ ∃ a,
      (q ≤ 2 → criticalityCoefficient P.theta C (modelOrder a) * ε a ≤
        ‖D.step k‖ ^ (p - modelOrder a + 1)) ∧
      (2 < q → criticalityCoefficient P.theta C (modelOrder a) * κ ^ (modelOrder a - 1) *
        ε a ^ modelOrder a ≤ ‖D.step k‖ ^ p) := by
  classical
  let C := L + S + 3 * P.errorBound * P.stepCoefficient
  let κ := safeRadiusCoefficient P L M S
  have hS : 0 ≤ S := (h.updates.pos (show 0 ≤ N by omega)).le.trans (hparam 0 (by omega))
  have hprod := mul_nonneg P.errorBound_nonneg P.stepCoefficient_pos.le
  have hC : 1 ≤ C := by dsimp [C]; nlinarith
  have hradius := stepRadiusCoefficient_mem (σ := S) P.zeta_pos P.zeta_le_one
    P.theta_pos P.theta_lt_one.le hM
  have hcoef := criticalityCoefficient_mem P.theta_pos P.theta_lt_one hC q
  have hκ : 0 < κ := lt_min hradius.1 hcoef.1
  have hκ1 : κ ≤ 1 := (min_le_left _ _).trans hradius.2
  have hκcoef : ∀ a : Fin q, κ ≤ criticalityCoefficient P.theta C (modelOrder a) := by
    intro a
    exact (min_le_right _ _).trans
      (criticalityCoefficient_antitone P.theta_lt_one.le (zero_lt_one.trans_le hC) a.isLt)
  have hselected := ((h.trial_rule k hk).mp ht).1
  have hmstep := h.step_two k hk hselected
  have hlegal := hmstep.radius_mem (h.checkedRadius_mem hk.le)
  have hr := h.radius_floor_sharp hM hparam hjet
  have hfloor : ∀ a, κ * ε a ≤ D.solvedRadius k a := fun a =>
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (h.accuracy_pos a).le).trans
      (hr.2.2.1 k hk hselected a)
  refine ⟨hκ, hκ1, ?_⟩
  by_cases hs : ‖D.step k‖ < 1
  · obtain ⟨a, ha⟩ := h.criticality_obstruction_candidate hf (zero_le_one.trans hL) hlip hk ht
      hs (hparam k hk.le) hnot
    have hq := P.order_le
    have horder : modelOrder a ≤ p := by unfold modelOrder; omega
    have hbound := two_mul_criticalityCoefficient_le_sum (zero_lt_one.trans_le hC)
      (modelOrder a) ha
    refine ⟨a, ?_, ?_⟩
    · intro hq2
      have hrad : D.solvedRadius k a = 1 :=
        hr.2.2.2 k hk hselected hs a (by unfold modelOrder; omega)
      have hsδ : ‖D.step k‖ ≤ D.solvedRadius k a := by rw [hrad]; exact hs.le
      exact pow_lower_of_step_le_radius horder (norm_nonneg _)
        (hlegal a).1 hsδ hbound
    · intro _
      exact pow_lower_of_mixed_sum (by unfold modelOrder; omega) horder (norm_nonneg _)
        hs.le (hlegal a).1
        (criticalityCoefficient_mem P.theta_pos P.theta_lt_one hC _).1.le hκ.le
        (hκcoef a) (h.accuracy_pos a).le (hfloor a) hbound
  · have hlarge : 1 ≤ ‖D.step k‖ := not_lt.mp hs
    let a : Fin q := ⟨0, P.order_pos⟩
    have hac := criticalityCoefficient_mem P.theta_pos P.theta_lt_one hC (modelOrder a)
    refine ⟨a, fun _ => ?_, fun _ => ?_⟩
    · apply le_trans _ (one_le_pow₀ hlarge)
      exact (mul_le_mul hac.2 (h.accuracy_le_one a) (h.accuracy_pos a).le zero_le_one).trans_eq
        (by ring)
    · have hh : criticalityCoefficient P.theta C (modelOrder a) *
          κ ^ (modelOrder a - 1) ≤ 1 := by
        exact (mul_le_mul hac.2 (pow_le_one₀ hκ.le hκ1)
          (pow_nonneg hκ.le _) zero_le_one).trans_eq (by ring)
      exact ((mul_le_mul hh (pow_le_one₀ (h.accuracy_pos a).le (h.accuracy_le_one a))
        (pow_nonneg (h.accuracy_pos a).le _) zero_le_one).trans_eq (by ring)).trans
          (one_le_pow₀ hlarge)


/-- Actual candidate nonoptimality gives the sharp root-step rates for both
low and high orders, independently of whether the trial is accepted. -/
theorem exists_root_step_lower_candidate (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    {L M S : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    {k : ℕ} (hk : k < N) (ht : k ∈ D.trials)
    (hnot : ¬OptimalityAt f ε (D.point k + D.step k) (D.solvedRadius k)) :
    ∃ a, rootStepCoefficient P L M S (modelOrder a) *
      (ε a) ^ rootStepExponent p q (modelOrder a) ≤ ‖D.step k‖ := by
  obtain ⟨hκ, _, a, hlo, hhi⟩ := h.step_powers_candidate hf hL hM hlip hparam hjet hk ht hnot
  have hS : 0 ≤ S := (h.updates.pos (show 0 ≤ N by omega)).le.trans (hparam 0 (by omega))
  have hC : 1 ≤ L + S + 3 * P.errorBound * P.stepCoefficient := by
    have hp := mul_nonneg P.errorBound_nonneg P.stepCoefficient_pos.le
    nlinarith
  have hc := criticalityCoefficient_mem P.theta_pos P.theta_lt_one hC (modelOrder a)
  refine ⟨a, ?_⟩
  by_cases hq : q ≤ 2
  · have hh := rpow_mul_le_of_pow (p := p - modelOrder a + 1) (j := 1) (by omega)
      hc.1.le (h.accuracy_pos a).le (norm_nonneg _) (by simpa only [pow_one] using hlo hq)
    simpa only [rootStepCoefficient, rootStepExponent, ite_eq_left hq, Nat.cast_one] using hh
  · have hh := rpow_mul_le_of_pow (P.order_pos.trans_le P.order_le)
      (mul_nonneg hc.1.le (pow_nonneg hκ.le _)) (h.accuracy_pos a).le (norm_nonneg _)
      (hhi (by omega))
    simpa only [rootStepCoefficient, rootStepExponent, ite_eq_right hq] using hh

/-- Computed model decrease has the sharp source rates for any trial candidate
failing true criticality, with no acceptance hypothesis. -/
theorem model_decrease_uniform_candidate (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    {L M S : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    {k : ℕ} (hk : k < N) (ht : k ∈ D.trials)
    (hnot : ¬OptimalityAt f ε (D.point k + D.step k) (D.solvedRadius k)) :
    commonDecreaseCoefficient P L M S / P.eta1 * accuracyFactor P ε ≤
      TaylorModel.jetDecrement (D.jet k) p (D.step k) := by
  have hS : 0 ≤ S := (h.updates.pos (show 0 ≤ N by omega)).le.trans (hparam 0 (by omega))
  obtain ⟨a, ha⟩ := h.exists_root_step_lower_candidate hf hL hM hlip hparam hjet hk ht hnot
  have hr := rootStepCoefficient_pos P hL hM hS (modelOrder a)
  have hp := pow_lower_of_root_step (n := p + 1) hr.le (h.accuracy_pos a).le ha
  have hbase : 0 ≤ P.eta1 * P.sigmaMin / ((p + 1).factorial : ℝ) :=
    div_nonneg (mul_nonneg P.eta1_pos.le P.sigmaMin_pos.le) (Nat.cast_nonneg _)
  have hscale := mul_le_mul_of_nonneg_left hp hbase
  have hc := mul_le_mul (commonDecreaseCoefficient_le P L M S a)
    (accuracyFactor_le P ε a) (accuracyFactor_pos P h.accuracy_pos).le
    (show 0 ≤ orderDecreaseCoefficient P L M S a by
      unfold orderDecreaseCoefficient; positivity)
  have hm := (penalty_lt_decrement (h.toModelTrace.reference_improvement k hk ht)
    (h.step_two k hk ((h.trial_rule k hk).mp ht).1).comparison).le
  have hσ := h.updates.min_le hk.le
  have hpen := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hσ (Nat.cast_nonneg (p + 1).factorial))
    (pow_nonneg (norm_nonneg (D.step k)) (p + 1))
  have hb : commonDecreaseCoefficient P L M S * accuracyFactor P ε ≤
      P.eta1 * TaylorModel.jetDecrement (D.jet k) p (D.step k) := by
    apply hc.trans
    apply le_trans _ (mul_le_mul_of_nonneg_left (hpen.trans hm) P.eta1_pos.le)
    convert hscale using 1
    · unfold orderDecreaseCoefficient evaluationExponent
      ring
    · ring
  have hd : commonDecreaseCoefficient P L M S * accuracyFactor P ε / P.eta1 ≤
      TaylorModel.jetDecrement (D.jet k) p (D.step k) :=
    (div_le_iff₀ P.eta1_pos).2 (by convert hb using 1; ring)
  convert hd using 1
  ring

/-- Actual accepted trials before next true certificate attainment obey both
computed model and true objective floors with the same fixed coefficient. -/
theorem model_function_decrease_before_certificate (h : Run f P ε D N)
    (hf : ContDiff ℝ p f) {L M S : ℝ} (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    {k : ℕ} (hk : k < N) (ht : k ∈ D.trials) (ha : P.eta1 ≤ D.ratio k)
    (hnot : ¬OptimalityAt f ε (D.point (k + 1)) (D.startRadius (k + 1))) :
    let c := commonDecreaseCoefficient P L M S / P.eta1
    0 < c ∧ c * accuracyFactor P ε ≤ TaylorModel.jetDecrement (D.jet k) p (D.step k) ∧
      P.eta1 * c * accuracyFactor P ε ≤ f (D.point k) - f (D.point (k + 1)) := by
  have hS : 0 ≤ S := (h.updates.pos (show 0 ≤ N by omega)).le.trans (hparam 0 (by omega))
  obtain ⟨a, hb⟩ := h.exists_root_step_lower_of_cap hf hL hM hlip hparam hjet hk ht ha hnot
  have hr := rootStepCoefficient_pos P hL hM hS (modelOrder a)
  have hp := pow_lower_of_root_step (n := p + 1) hr.le (h.accuracy_pos a).le hb
  have hη := P.eta1_pos
  have hσ := P.sigmaMin_pos
  have hc := mul_le_mul (commonDecreaseCoefficient_le P L M S a)
    (accuracyFactor_le P ε a) (accuracyFactor_pos P h.accuracy_pos).le
    (show 0 ≤ orderDecreaseCoefficient P L M S a by
      unfold orderDecreaseCoefficient; positivity)
  have hm := (penalty_lt_decrement (h.toModelTrace.reference_improvement k hk ht)
    (h.step_two k hk ((h.trial_rule k hk).mp ht).1).comparison).le
  have hmin := h.updates.min_le hk.le
  have hpen := (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hmin (Nat.cast_nonneg (p + 1).factorial))
    (pow_nonneg (norm_nonneg (D.step k)) (p + 1))).trans hm
  have hscale := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ P.eta1 * P.sigmaMin / ((p + 1).factorial : ℝ) by positivity)
  have hd : commonDecreaseCoefficient P L M S / P.eta1 * accuracyFactor P ε ≤
      TaylorModel.jetDecrement (D.jet k) p (D.step k) := by
    have hh : commonDecreaseCoefficient P L M S * accuracyFactor P ε ≤
        P.eta1 * TaylorModel.jetDecrement (D.jet k) p (D.step k) := by
      apply hc.trans
      apply le_trans _ (mul_le_mul_of_nonneg_left hpen hη.le)
      convert hscale using 1
      · unfold orderDecreaseCoefficient evaluationExponent
        ring
      · ring
    have hh' : commonDecreaseCoefficient P L M S * accuracyFactor P ε / P.eta1 ≤
        TaylorModel.jetDecrement (D.jet k) p (D.step k) :=
      (div_le_iff₀ hη).2 (by convert hh using 1; ring)
    convert hh' using 1
    ring
  refine ⟨div_pos (commonDecreaseCoefficient_pos P hL hM hS) hη, hd, ?_⟩
  convert h.function_decrease_uniform hf hL hM hlip hparam hjet hk ht ha hnot using 1
  field_simp [hη.ne']

end Run
end InexactRegularization
