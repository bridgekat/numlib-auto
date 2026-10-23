import Numlib.Optimization.Regularization.HighOrder.Sharpness.CriticalityExecution
import Numlib.Optimization.Regularization.HighOrder.Sharpness.Execution
import Numlib.Analysis.Calculus.IteratedDeriv.Bounded

/-!
# Full low-order ARqp evaluation lower bounds

Uniform globally bounded C^p Hermite objectives have every derivative Lipschitz
with constants chosen before accuracy. Their actual ARqp executions use global
model minima, unit radii, exact ratios and a first literal stopping check. The
iteration and all evaluation counts attain the stated inverse-accuracy rate.
-/

namespace HighOrderRegularization.Sharpness
open InexactTrustRegion

/-- For q=1 or2, uniform actual objectives and literal ARqp runs attain the
source inverse-accuracy lower bound. All regularity and objective constants
precede accuracy; final stopping is strict and every earlier criticality fails. -/
theorem exists_low_order_criticality_witness {p q : ℕ}
    (hq : 0 < q) (hqp : q ≤ p) (hq2 : q ≤ 2) :
    ∃ L B : ℝ, 1 ≤ L ∧ 0 < B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ f : ℝ → ℝ,
        let u := (2 : ℝ) / 3 * ε
        let N := length p q u
        let t := step p q u
        let D := criticalityData p q N hq t
        ContDiff ℝ p f ∧ (∀ x, |f x| ≤ B) ∧
        (∀ j ≤ p, ∀ x y,
          ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤ L * ‖x - y‖) ∧
        HighOrderRegularization.Run f (criticalitySettings hq hqp) (fun _ => ε) D N ∧
        StrictMono D.point ∧
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
  obtain ⟨L₀, hL₀, B, hB, hex⟩ := exists_uniform_objectives_accuracy hq hqp
  let L := max 1 (max B L₀)
  refine ⟨L, B, le_max_left _ _, hB, ?_⟩
  intro ε hε hεhalf
  let u := (2 : ℝ) / 3 * ε
  let N := length p q u
  let t := step p q u
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; linarith
  have hε1 : ε ≤ 1 := by linarith
  obtain ⟨f, hf, hLip, hjet, hb⟩ := hex u hu hu1
  have hrun := criticalityRun_of_matches hq hqp hq2 hε hε1 hjet
  have hN : ε ^ (-((p + 1 : ℕ) : ℝ) / (p - q + 1 : ℕ)) ≤ (N : ℝ) := by
    have hrate := inverse_accuracy_le_horizon (p := p) (r := q) hu
    have hmono := Real.rpow_le_rpow_of_nonpos hu
      (show u ≤ ε by dsimp [u]; linarith)
      (show -((p + 1 : ℕ) : ℝ) / (balance p q : ℝ) ≤ 0 by
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _))
          (Nat.cast_nonneg _))
    exact hmono.trans hrate
  refine ⟨f, hf, (fun x => by simpa only [iteratedDeriv_zero] using hb 0 (Nat.zero_le _) x),
    ?_, hrun, point_strictMono (step_pos p q hu), ?_, ?_, ?_, ?_, rfl, ?_⟩
  · intro j hj x y
    have hall := norm_iteratedFDeriv_sub_le_of_bounded_jets hf hB.le
      (fun a ha z => by simpa only [Real.norm_eq_abs] using hb a ha z)
      hLip.norm_sub_le j hj x y
    exact hall.trans (mul_le_mul_of_nonneg_right (le_max_right 1 (max B L₀))
      (norm_nonneg _))
  · simp only [criticalityData, lt_self_iff_false, ite_false]
  · intro a
    change TaylorModel.criticality f (modelOrder a) (point t N) 1 ≤ _
    dsimp only [t, N, length]
    by_cases ha : modelOrder a = q
    · rw [ha, criticality_order_eq_accuracy hq hqp hu.le hjet le_rfl]
      simp only [lt_self_iff_false, ite_false]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      dsimp [u]
      linarith
    · rw [criticality_lower_eq_zero hq hjet le_rfl
        ((show modelOrder a ≤ q from a.isLt).trans hqp)
        (lt_of_le_of_ne a.isLt ha) zero_le_one]
      positivity
  · intro k hk
    change k < horizon p (root p q u) at hk
    change ε / q.factorial < TaylorModel.criticality f q (point t k) 1
    dsimp only [t]
    rw [criticality_order_eq_accuracy hq hqp hu.le hjet hk.le, ite_eq_left hk]
    apply (div_lt_div_iff_of_pos_right (by positivity)).mpr
    dsimp [u]
    linarith
  · exact hN
  · intro j _ _
    exact ⟨criticalityDerivativeEvaluations_eq_card hq t j, rfl,
      hN.trans (by exact_mod_cast le_criticalityDerivativeEvaluations q j N)⟩

end HighOrderRegularization.Sharpness
