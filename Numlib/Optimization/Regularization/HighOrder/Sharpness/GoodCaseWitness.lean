import Numlib.Optimization.Regularization.HighOrder.Sharpness.GoodCaseExecution
import Numlib.Analysis.Calculus.IteratedDeriv.Bounded
import Numlib.Optimization.Regularization.HighOrder.Run

/-!
# Uniform all-order unit-radius evaluation lower bounds

Globally bounded Hermite objectives have all derivative Lipschitz constants fixed before
accuracy. Actual fresh-point check and model events give every requested derivative count.
-/

namespace HighOrderRegularization.Sharpness
open InexactTrustRegion

/-- All prescribed jets are realized by globally bounded actual smooth objectives with
constants fixed before accuracy. -/
theorem exists_uniform_good_objectives {p q : ℕ} (hq : 0 < q) (hqp : q ≤ p) :
    ∃ (L : ℝ) (hL : 0 < L), ∃ B > 0,
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧
        LipschitzWith ⟨L, hL.le⟩ (iteratedDeriv p f) ∧
        MatchesJets f p q (horizon p (root p q ε)) (goodAmplitude p q) (goodStep p q ε) ∧
        ∀ j ≤ p, ∀ x, |iteratedDeriv j f x| ≤ B := by
  obtain ⟨L, hL, B, hB, hex⟩ := exists_uniform_objectives hq hqp
    (goodAmplitude_pos hq).le le_rfl (C := 2 * goodScale p q ^ (p + 1))
  refine ⟨L, hL, B, hB, ?_⟩
  intro ε hε hε1
  apply hex (horizon p (root p q ε)) (horizon_pos p (root_pos p q hε))
    (goodStep p q ε) (goodStep_pos hq hε)
  · exact (goodStep_le_scale hq hε.le hε1).trans (goodScale_le_one hq)
  · have hh := horizon_mul_power_lt_two p (root_pos p q hε)
      (root_le_one p q hε.le hε1)
    have hm := mul_le_mul_of_nonneg_left hh.le
      (pow_nonneg (goodScale_pos (p := p) hq).le (p + 1))
    simpa only [goodStep, mul_pow, mul_left_comm, mul_comm, mul_assoc] using hm
/-- Uniform actual objectives and full unit-radius ARqp runs attain the source lower-bound
rate for every order. Every earlier iterate fails true criticality, the final check
passes, and derivative counts equal actual fresh-point event cardinalities. -/
theorem exists_good_criticality_witness {p q : ℕ} (hq : 0 < q) (hqp : q ≤ p) :
    ∃ L B : ℝ, 1 ≤ L ∧ 0 < B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ f : ℝ → ℝ,
        let N := horizon p (root p q ε)
        let t := goodStep p q ε
        let D := goodData p q N hq t
        ContDiff ℝ p f ∧ (∀ x, |f x| ≤ B) ∧
        (∀ j ≤ p, ∀ x y,
          ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤ L * ‖x - y‖) ∧
        HighOrderRegularization.Run f (goodSettings hq hqp) (fun _ => ε) D N ∧
        StrictMono D.point ∧
        (∀ k, ∀ a : Fin q, D.radius k a = 1 ∧ D.solvedRadius k a = 1) ∧
        D.selected N = none ∧
        (∀ a : Fin q, TaylorModel.criticality f (modelOrder a) (D.point N) 1 ≤
          ε / (modelOrder a).factorial) ∧
        (∀ k < N, ε / q.factorial < TaylorModel.criticality f q (D.point k) 1) ∧
        ε ^ (-((p + 1 : ℕ) : ℝ) / (p - q + 1 : ℕ)) ≤ (N : ℝ) ∧
        HighOrderRegularization.functionEvaluations N = N + 1 ∧
        ∀ j, 1 ≤ j → j ≤ p →
          criticalityDerivativeEvaluations q j N =
            (derivativeEvaluationNodes D.selected j N).card ∧
          criticalityDerivativeEvaluations q j N = N + (if j ≤ q then 1 else 0) ∧
          ε ^ (-((p + 1 : ℕ) : ℝ) / (p - q + 1 : ℕ)) ≤
            (criticalityDerivativeEvaluations q j N : ℝ) := by
  obtain ⟨L₀, hL₀, B, hB, hex⟩ := exists_uniform_good_objectives hq hqp
  let L := max 1 (max B L₀)
  refine ⟨L, B, le_max_left _ _, hB, ?_⟩
  intro ε hε hεhalf
  let N := horizon p (root p q ε)
  let t := goodStep p q ε
  have hε1 : ε ≤ 1 := by linarith
  obtain ⟨f, hf, hLip, hjet, hb⟩ := hex ε hε hε1
  have hrun := goodRun_of_matches hq hqp hε hε1 hjet
  have hN : ε ^ (-((p + 1 : ℕ) : ℝ) / (p - q + 1 : ℕ)) ≤ (N : ℝ) :=
    inverse_accuracy_le_horizon hε
  refine ⟨f, hf, (fun x => by simpa only [iteratedDeriv_zero] using hb 0 (Nat.zero_le _) x),
    ?_, hrun, point_strictMono (goodStep_pos hq hε), fun _ _ => ⟨rfl, rfl⟩,
    ?_, ?_, ?_, hN, rfl, ?_⟩
  · intro j hj x y
    have hall := norm_iteratedFDeriv_sub_le_of_bounded_jets hf hB.le
      (fun a ha z => by simpa only [Real.norm_eq_abs] using hb a ha z)
      hLip.norm_sub_le j hj x y
    exact hall.trans (mul_le_mul_of_nonneg_right (le_max_right 1 (max B L₀))
      (norm_nonneg _))
  · simp only [goodData, criticalityData, lt_self_iff_false, ite_false]
  · intro a
    change TaylorModel.criticality f (modelOrder a) (point t N) 1 ≤ _
    by_cases ha : modelOrder a = q
    · rw [ha, criticality_order_eq hq hqp hjet le_rfl (goodAmplitude_pos hq).le
        (goodStep_pos hq hε).le]
      simp only [lt_self_iff_false, ite_false]
      have hh := goodAmplitude_step_power (p := p) hq hε.le
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      change goodAmplitude p q / 2 * goodStep p q ε ^ balance p q ≤ ε
      nlinarith
    · rw [criticality_lower_eq_zero hq hjet le_rfl
        ((show modelOrder a ≤ q from a.isLt).trans hqp)
        (lt_of_le_of_ne a.isLt ha) zero_le_one]
      positivity
  · intro k hk
    change k < horizon p (root p q ε) at hk
    change ε / q.factorial < TaylorModel.criticality f q (point t k) 1
    rw [criticality_order_eq hq hqp hjet hk.le (goodAmplitude_pos hq).le
        (goodStep_pos hq hε).le, ite_eq_left hk]
    apply (div_lt_div_iff_of_pos_right (by positivity)).mpr
    have hh := goodAmplitude_step_power (p := p) hq hε.le
    change ε < goodAmplitude p q * goodStep p q ε ^ balance p q
    linarith
  · intro j _ _
    exact ⟨criticalityDerivativeEvaluations_eq_card (p := p) hq t j, rfl,
      hN.trans (by exact_mod_cast le_criticalityDerivativeEvaluations q j N)⟩

end HighOrderRegularization.Sharpness
