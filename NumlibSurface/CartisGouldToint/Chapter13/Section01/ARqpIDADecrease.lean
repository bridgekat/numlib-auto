import NumlibSurface.CartisGouldToint.Chapter13.Section01.ARqpIDAUniformAccuracy
import Numlib.Optimization.InexactRegularizationDecrease

/-!
# Actual ARqpIDA trial decreases with corrected fixed-initialization constants

The genuine global smoothness and implicit oracle contracts determine analytic constants
before the tolerance vector or execution. The literal q-checked algorithm then pays both
source tolerance-power regimes at accepted trials whose actual successor fails the true
criterion. The actual detailed inner procedure supplies the short-return model radii from
globally derived tensor and parameter bounds; long steps retain their inherited radii.
This does not close the separate first-attainment or evaluation-count theorem, nor recover
the refuted printed local constants.
-/

noncomputable section
open scoped Nat
namespace CartisGouldToint.Chapter13.Section01
open Optimization InexactRegularization InexactTaylorModels

variable {n : ℕ}

/-- Full predicted and accepted objective decreases for literal Algorithm 13.1.2 at all
p>=q>=1, with corrected constants and the original two exponent regimes. Global analytic
constants are fixed before initialization data, tolerances or runs. The global tensor bound,
uniform sigma bound, all-order coefficient powers and prescribed short-return model radii
are all derived. Only true failure at the actual successor point and radii is required. -/
theorem arqpida_accepted_decrease_bounds {p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (O : ImplicitAccuracyOracle f p) (hf : ImplicitSmoothness f p) :
    ∃ L K : ℝ, 1 ≤ L ∧ 0 ≤ K ∧
      ∀ (h0 : ℕ → ℝ) (σ0 : ℝ) (P : ARqpIDAParameters), P.p = p →
        ∀ (N : ℕ) (r : InexactRegularization.Execution P P.q f O.derivative N),
          (r.state 0).request = h0 → (r.state 0).sigma = σ0 →
          ∀ (k : ℕ) (hk : k < N) (ht : r.trial k = true), r.accepted k = true →
            (¬HigherOrderApproximateRegularization.SatisfiesCriteria P.toParameters f
              (r.state (k + 1)).point (r.state (k + 1)).radii) →
            let M := L + K * P.kappaInitial
            let S := correctedSigmaBound P h0 σ0 L K
            let κ := prescribedRadiusCoefficient P M S
            let A := HigherOrderApproximateRegularization.modelDecreaseConstant
              P.p P.q P.order_pos P.theta (correctedTransferConstant P h0 σ0 L K) κ P.sigmaMin
            let τ := HigherOrderApproximateRegularization.toleranceMeasure
              P.p P.q P.order_pos P.epsilon
            A * τ ≤ decrement (O.derivative (r.state k).point (r.state k).request) P.p
              (r.executedTrial hk ht).inner.step ∧
            P.eta1 * (A * τ) ≤ f (r.state k).point - f (r.state (k + 1)).point := by
  obtain ⟨L, hL, hfL, hnorm⟩ := TRqIDA.exists_uniform_smoothness hf
  obtain ⟨K, hK, hO⟩ := (TRqIDA.oracle O).exists_uniformAccuracy
  refine ⟨L, K, hL, hK, ?_⟩
  intro h0 σ0 P hp N r hrequest hσ k hk ht ha hfail
  subst p
  have hf' := hfL P.p (P.order_pos.trans P.order_le) le_rfl
  let t := r.executedTrial hk ht
  let M := L + K * P.kappaInitial
  let S := correctedSigmaBound P (r.state 0).request (r.state 0).sigma L K
  let κ := prescribedRadiusCoefficient P M S
  have hM : 1 ≤ M := by dsimp only [M]; nlinarith [mul_nonneg hK P.kappaInitial_nonneg]
  have hκ := prescribedRadiusCoefficient_pos P (S := S) hM
  have hκ1 := prescribedRadiusCoefficient_le_one P (S := S) hM
  have hA : ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ M := by
    intro i hi
    exact r.supplied_coefficient_norm_le (TRqIDA.oracle O) hk.le hK hO hi
      (hnorm (r.state k).point i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2)
  have hradii : ‖t.inner.step‖ < 1 → PrescribedModelRadii P κ t.inner.radii := by
    intro hs
    exact r.prescribedModelRadii_of_bounds (TRqIDA.oracle O) P.order_pos hk.le
      t.inspection t.order_le t.inner hf' hK hO hM hA hs
  have hx := t.accepted_point ha
  have hδ := t.accepted_radii ha
  have hf'next : ¬HigherOrderApproximateRegularization.SatisfiesCriteria P.toParameters f
      ((r.state k).point + t.inner.step) t.inner.radii := by
    simpa only [hx, hδ] using hfail
  have hb := r.trial_predicted_decrease_of_true_gap_failure (TRqIDA.oracle O)
    P.order_pos hk ht hf' hL hK hO hκ hκ1 hradii hf'next
  have hd := r.accepted_decrease_of_true_gap_failure (TRqIDA.oracle O)
    P.order_pos hk ht ha hf' hL hK hO hκ hκ1 hradii hfail
  simpa only [κ, M, S, hrequest, hσ, TRqIDA.oracle] using And.intro hb hd

end CartisGouldToint.Chapter13.Section01
