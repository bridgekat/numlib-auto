import Numlib.Optimization.TrustRegion.HighOrder.Sharpness
import Numlib.Analysis.Calculus.IteratedDeriv.Bounded
import Numlib.Approximation.Hermite.Global

/-!
# Globally regular slow arbitrary-order trust-region objectives

Uniform Hermite interpolation realizes the prescribed actual jets. Its constants
precede the accuracy, and bounded jets imply common Lipschitz constants for all
lower derivatives. The resulting objective realizes the operational sharpness
execution for every admissible acceptance/update choice with unit optimality cap.
-/

namespace HighOrderTrustRegion.Sharpness

/-- Uniformly bounded, globally `C^q` objectives with uniformly Lipschitz derivative
families realize the inverse-accuracy sharpness rate. The same objective works for
every legal parameter choice with unit optimality cap and the specified accuracies.
All preterminal points fail the true optimality requirement at every positive radius.
Initialization uses radius `ε`, as in the source construction. -/
theorem exists_slow_objective {q : ℕ} (hq : 0 < q) :
    ∃ L ≥ 1, ∃ B > 0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (q.factorial : ℝ) →
      ∃ f : ℝ → ℝ, ContDiff ℝ q f ∧
        (∀ j ≤ q, ∀ y, |iteratedDeriv j f y| ≤ B) ∧
        (∀ j ≤ q, ∀ y z,
          ‖iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f z‖ ≤ L * ‖y - z‖) ∧
        (∀ y, -B ≤ f y) ∧ f 0 = 4 ∧ f 0 - (-B) = 4 + B ∧
        ∀ P : Parameters q, P.theta = 1 → ε ≤ P.radiusMax →
          (∀ a, P.accuracy a = ((modelOrder a).factorial : ℝ) * ε) →
          Run f P (point ε) (fun _ => ε) (fun _ _ => direction q ε P.zeta)
            (fun _ => topIndex hq) (fun _ => ε) (fun _ => 1) (length q ε) ∧
          (∀ k ≤ length q ε,
            CheckedOracle f P (point ε k) ε (fun _ => direction q ε P.zeta)) ∧
          (∀ k < length q ε,
            ¬TestsPass f P (point ε k) ε (fun _ => direction q ε P.zeta)) ∧
          TestsPass f P (point ε (length q ε)) ε (fun _ => direction q ε P.zeta) ∧
          (∀ k < length q ε, ∀ δ > 0,
            ¬∀ a, TaylorModel.criticality f (modelOrder a) (point ε k) δ ≤
              P.accuracy a * δ ^ modelOrder a / (modelOrder a).factorial) ∧
          (ε ∈ Set.Ioc (0 : ℝ) 1) ∧
          (∀ a, TaylorModel.criticality f (modelOrder a) (point ε (length q ε)) ε ≤
            P.accuracy a * ε ^ modelOrder a / (modelOrder a).factorial) ∧
          functionEvaluations (length q ε) = length q ε + 1 ∧
          derivativeEvaluations P (fun _ => 1) (length q ε) = length q ε + 1 ∧
          1 / ε ^ (q + 1) ≤ (length q ε : ℝ) ∧
          1 / ε ^ (q + 1) < (functionEvaluations (length q ε) : ℝ) ∧
          1 / ε ^ (q + 1) < (derivativeEvaluations P (fun _ => 1) (length q ε) : ℝ) := by
  let κ := max 4 (2 * (q.factorial : ℝ))
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  obtain ⟨L₀,hL₀,B,hB,H⟩ := Hermite.exists_uniform_interpolant q κ hκ
  refine ⟨max 1 (max B L₀), le_max_left _ _, B, hB, ?_⟩
  intro ε hε hεq
  have hε1 := accuracy_le_one hεq
  obtain ⟨_hκ,hN,hgrid,hstep,hjets,hres⟩ := uniform_data hq hε hε1
  obtain ⟨f,hf,hLip,hjet,hbound⟩ := H (length q ε) hN (point ε) (jet q ε (length q ε))
    (fun i j hij _ => hgrid hij)
    (fun k hk j hj => by simpa only [point_succ, add_sub_cancel_left] using hres k hk j hj)
  have hbounded : ∀ j ≤ q, ∀ y, |iteratedDeriv j f y| ≤ B := hbound
    ⟨fun k hk j hj => hjets k hk.le j hj,
      fun k _ => by simpa only [point_succ, add_sub_cancel_left] using hstep⟩
  have hmatch : MatchesJets f q ε (length q ε) := hjet
  have hvalue : f 0 = 4 := by
    simpa only [point_zero, value_zero] using hmatch.value_eq (Nat.zero_le _)
  have hglob := norm_iteratedFDeriv_sub_le_of_bounded_jets hf hB.le
    (fun j hj y => by simpa only [Real.norm_eq_abs] using hbounded j hj y)
    (fun y z => hLip.norm_sub_le y z)
  refine ⟨f,hf,hbounded,?_,?_,hvalue,by rw [hvalue]; ring,?_⟩
  · intro j hj y z
    exact (hglob j hj y z).trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 _) (norm_nonneg _))
  · intro y
    exact (abs_le.mp (by simpa only [iteratedDeriv_zero] using hbounded 0 (Nat.zero_le _) y)).1
  · intro P hθ hmax hacc
    obtain ⟨hF,hD⟩ := initialized_counts P (length q ε)
    obtain ⟨hFl,hDl⟩ := initialized_counts_lower P ε
    refine ⟨run_of_matches P hε hε1 hθ hmax hacc hmatch,
      fun k hk => checkedOracle_of_matches P hε hε1 hθ hmatch hk,
      fun k hk => not_testsPass_of_matches P hε hε1 hθ hacc hmatch hk,
      testsPass_last_of_matches P hε hε1 hθ hacc hmatch,
      fun k hk δ hδ => not_approximate_at_any_radius P hε hacc hmatch hk hδ,
      ⟨hε,hε1⟩, (true_first_stopping_index P hε hacc hmatch).2,
      hF,hD,inverse_pow_le_length q ε,hFl,hDl⟩


/-- Add the source's factorial-scaled accuracies to fixed settings with unit
optimality cap. -/
def settingsParameters {q : ℕ} (S : Settings q) (hθ : S.theta = 1)
    (ε : ℝ) (hε : 0 < ε) (hεq : ε ≤ 1 / (q.factorial : ℝ)) : Parameters q :=
  S.withAccuracy (fun a => ((modelOrder a).factorial : ℝ) * ε)
    (fun _ => by positivity) (factorial_accuracy_le_one hε.le hεq)
    ⟨⟨0,S.order_pos⟩, by simpa only [modelOrder, Fin.val_zero, zero_add,
      Nat.factorial_one, Nat.cast_one, one_mul, hθ] using accuracy_le_one hεq⟩

/-- Fixed legal settings have a uniformly regular sharpness family with an actual
execution, rather than conditional operational premises. The initialization radius
is `ε`; all settings and all regularity bounds precede the accuracy choice. -/
theorem exists_slow_objective_for_settings {q : ℕ} (hq : 0 < q)
    (S : Settings q) (hθ : S.theta = 1) (hmax : 1 ≤ S.radiusMax) :
    ∃ L ≥ 1, ∃ B > 0, ∀ (ε : ℝ) (hε : 0 < ε) (hεq : ε ≤ 1 / (q.factorial : ℝ)),
      let P := settingsParameters S hθ ε hε hεq
      ∃ f : ℝ → ℝ, ContDiff ℝ q f ∧
        (∀ j ≤ q, ∀ y, |iteratedDeriv j f y| ≤ B) ∧
        (∀ j ≤ q, ∀ y z,
          ‖iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f z‖ ≤ L * ‖y - z‖) ∧
        (∀ y, -B ≤ f y) ∧ f 0 = 4 ∧ f 0 - (-B) = 4 + B ∧
          Run f P (point ε) (fun _ => ε) (fun _ _ => direction q ε P.zeta)
            (fun _ => topIndex hq) (fun _ => ε) (fun _ => 1) (length q ε) ∧
          (∀ k ≤ length q ε,
            CheckedOracle f P (point ε k) ε (fun _ => direction q ε P.zeta)) ∧
          (∀ k < length q ε,
            ¬TestsPass f P (point ε k) ε (fun _ => direction q ε P.zeta)) ∧
          TestsPass f P (point ε (length q ε)) ε (fun _ => direction q ε P.zeta) ∧
          (∀ k < length q ε, ∀ δ > 0,
            ¬∀ a, TaylorModel.criticality f (modelOrder a) (point ε k) δ ≤
              P.accuracy a * δ ^ modelOrder a / (modelOrder a).factorial) ∧
          (ε ∈ Set.Ioc (0 : ℝ) 1) ∧
          (∀ a, TaylorModel.criticality f (modelOrder a) (point ε (length q ε)) ε ≤
            P.accuracy a * ε ^ modelOrder a / (modelOrder a).factorial) ∧
          functionEvaluations (length q ε) = length q ε + 1 ∧
          derivativeEvaluations P (fun _ => 1) (length q ε) = length q ε + 1 ∧
          1 / ε ^ (q + 1) ≤ (length q ε : ℝ) ∧
          1 / ε ^ (q + 1) < (functionEvaluations (length q ε) : ℝ) ∧
          1 / ε ^ (q + 1) < (derivativeEvaluations P (fun _ => 1) (length q ε) : ℝ) := by
  obtain ⟨L,hL,B,hB,H⟩ := exists_slow_objective hq
  refine ⟨L,hL,B,hB,?_⟩
  intro ε hε hεq
  let P := settingsParameters S hθ ε hε hεq
  obtain ⟨f,hf,hbound,hLip,hlow,hval,hgap,hslow⟩ := H ε hε hεq
  refine ⟨f,hf,hbound,hLip,hlow,hval,hgap,?_⟩
  exact hslow P hθ ((accuracy_le_one hεq).trans hmax) (fun _ => rfl)

end HighOrderTrustRegion.Sharpness
