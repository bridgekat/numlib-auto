import NumlibSurface.CartisGouldToint.Chapter13.Section01.ARqpIDA
import NumlibSurface.CartisGouldToint.Chapter13.Section01.TRqIDA
import Numlib.Optimization.InexactRegularizationTransfer

/-!
# Chapter 13, Section 1: actual ARqpIDA radius floors

The supplied coefficient bound (13.1.63) yields the source Step 2 radii, the entire inherited
radius history and the short-step accuracy threshold. A joint factorial-tail estimate proves
the printed `/24 max` floor directly; the intermediate scalar comparison printed in the
proof of Lemma 13.1.12 is not used. True-quality transfer is also available with an actual
encountered parameter bound, without asserting the false printed all-iteration bound.
-/

noncomputable section
open scoped Nat
namespace CartisGouldToint.Chapter13.Section01
open Optimization InexactRegularization InexactTaylorModels TaylorCriticality
variable {n : ℕ}

/-- Assumption f.D0pL and the global oracle contract supply the genuine coefficient bound
(13.1.63) on every state in a finite execution, including the final inspection. -/
theorem arqpida_exists_coefficient_bound {P : ARqpIDAParameters}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {O : ImplicitAccuracyOracle f P.p} {N : ℕ}
    (r : algorithm_13_1_2 P f O N) (hf : ImplicitSmoothness f P.p) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ k, k ≤ N → ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ L := by
  have hκ : 0 < P.kappaInitial := (r.initial_request 1
    (Finset.mem_Icc.mpr ⟨le_rfl, P.order_pos.trans P.order_le⟩)).trans_le
      (r.initial_request_le 1 (Finset.mem_Icc.mpr ⟨le_rfl, P.order_pos.trans P.order_le⟩))
  obtain ⟨L, K, M, hL, hK, hM, hO, hfL, hbound⟩ :=
    TRqIDA.exists_global_analysis_bounds O hf hκ
  refine ⟨max 1 M, le_max_left _ _, fun k hk i hi => ?_⟩
  exact (hbound _ _ (fun i hi => (r.request_bounds hk hi).1)
    (fun i hi => (r.request_bounds hk hi).2.trans (r.initial_request_le i hi)) i hi).trans
      (le_max_right _ _)

/-- Step 2, for the actual supplied model, always has a finite returned execution retaining
the inspected witness. Every such output is nonzero and has the exact source radius floor.
The same theorem gives all inherited and post-inspection radius bounds and the explicit
accuracy threshold (13.1.73). Its genuine coefficient premise is precisely (13.1.63), which
`arqpida_exists_coefficient_bound` obtains from the source assumptions. -/
theorem lemma_13_1_12 {P : ARqpIDAParameters}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {O : ImplicitAccuracyOracle f P.p} {N : ℕ}
    (r : algorithm_13_1_2 P f O N) {L : ℝ} (hL : 1 ≤ L)
    (hA : ∀ k, k ≤ N → ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ L)
    (I : Inspection P (f (r.state N).point) (O.derivative (r.state N).point (r.state N).request)
      (r.state N).sigma (r.state N).radii) :
    (∀ hq : I.order ≤ P.q,
      Nonempty (InnerResult P (f (r.state N).point)
        (O.derivative (r.state N).point (r.state N).request) (r.state N).sigma
        I.radii (I.direction hq))) ∧
    (∀ (hq : I.order ≤ P.q)
      (s : InnerResult P (f (r.state N).point)
        (O.derivative (r.state N).point (r.state N).request) (r.state N).sigma
        I.radii (I.direction hq)), s.step ≠ 0 ∧
      ((1 ≤ ‖s.step‖ ∧ s.radii = I.radii) ∨
        ((∀ j, 1 ≤ j → j ≤ P.q → ∃ d,
          HigherOrderApproximateRegularization.GapWitness
            (inexactRegularizedModel (f (r.state N).point)
              (O.derivative (r.state N).point (r.state N).request) P.p (r.state N).sigma)
            j s.step (s.radii j) P.fraction d ∧
          taylorDecrement (inexactRegularizedModel (f (r.state N).point)
            (O.derivative (r.state N).point (r.state N).request) P.p (r.state N).sigma)
            j s.step d ≤ P.fraction * P.theta * P.epsilon j * s.radii j ^ j / (j ! : ℝ)) ∧
          (∀ j, j ≤ 2 → s.radii j = 1) ∧
          ∀ j, 3 ≤ j → j ≤ P.q →
            P.fraction * P.theta / (24 * max L (r.state N).sigma) * P.epsilon j ≤ s.radii j))) ∧
    (∀ k, k ≤ N → ∀ j, 1 ≤ j → j ≤ P.q →
      P.fraction * P.theta / (24 * max L (r.runningSigma k)) * P.epsilon j ≤
        (r.state k).radii j) ∧
    (∀ j, 1 ≤ j → j ≤ P.q →
      (r.state N).radii j ≥ I.radii j ∧ I.radii j ≥
        P.fraction * P.theta / (24 * max L (r.runningSigma N)) * P.epsilon j) ∧
    (∀ (hq : I.order ≤ P.q)
      (s : InnerResult P (f (r.state N).point)
        (O.derivative (r.state N).point (r.state N).request) (r.state N).sigma
        I.radii (I.direction hq)),
      (∀ i ∈ Finset.Icc 1 P.p, (r.state N).request i ≤
        P.kappaStep * (P.fraction *
          (P.fraction * P.theta / (24 * max L (r.runningSigma N))) ^ P.q /
          (12 * (P.q ! : ℝ) * max L (r.runningSigma N))) ^ P.p *
          (Chapter12.Section02.TRq.epsilonMinimum P.q P.epsilon) ^ (P.p * (P.q + 1))) →
      StepAccurate P P.p (r.state N).request s.step) := by
  have hσ := P.sigmaMin_pos.trans_le (r.sigma_floor le_rfl)
  refine ⟨fun hq => exists_innerResult P _ _ hσ hL (hA N le_rfl) I.radii (I.direction hq),
    ?_, fun k hk j hj hjq => r.radii_lower_running hL (fun k hk => hA k hk.le) hk hj hjq,
    ?_, ?_⟩
  · intro hq s
    refine ⟨(s.decrement_pos I hq hσ.le (r.valid_radii le_rfl)).2.2, ?_⟩
    rcases s.quality with hl | hq'
    · exact Or.inl hl
    · by_cases hs : 1 ≤ ‖s.step‖
      · exact Or.inl ⟨hs, by simp only [InnerResult.radii, ite_eq_left hs]⟩
      · exact Or.inr ⟨hq', s.radii_bounds hL hσ.le (hA N le_rfl) (lt_of_not_ge hs)⟩
  · intro j hj hjq
    refine ⟨?_, r.inspection_radii_lower hL (fun k hk => r.sigma_le_running hk) hA I hj hjq⟩
    unfold Inspection.radii
    split_ifs
    · simpa only [halvedRadius_zero] using
        halvedRadius_antitone (r.valid_radii le_rfl j hj hjq).1.le (Nat.zero_le (I.halvings j))
    · exact le_rfl
  · intro hq s hh
    exact r.stepAccurate_of_uniform_request hL (fun k hk => r.sigma_le_running hk) hA I hq s
      (Chapter12.Section02.TRq.epsilonMinimum_pos P.order_pos P.epsilon_pos).le
      (fun j hj hjq => Chapter12.Section02.TRq.epsilonMinimum_le P.epsilon hj hjq) hh

/-- The Step 1→5 true-quality conclusion with the actual running parameter maximum.
The historical radius premise of the earlier local certificate is now proved from the run.
The running maximum is computed from the trace; no uniform parameter-bound premise is assumed. -/
theorem arqpida_true_quality_at_running_sigma {P : ARqpIDAParameters}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {O : ImplicitAccuracyOracle f P.p} {N : ℕ}
    (r : algorithm_13_1_2 P f O N) {L : ℝ} (hL : 1 ≤ L)
    (hA : ∀ k, k ≤ N → ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ L)
    (I : Inspection P (f (r.state N).point) (O.derivative (r.state N).point (r.state N).request)
      (r.state N).sigma (r.state N).radii) (hall : I.order = P.q + 1)
    {ε K H : ℝ} (hε : 0 ≤ ε)
    (hεj : ∀ j, 1 ≤ j → j ≤ P.q → ε ≤ P.epsilon j)
    (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hcoeff : ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state N).point (r.state N).request i -
        iteratedFDeriv ℝ i f (r.state N).point‖ ≤ K * H)
    (hsmall : 4 * (P.q ! : ℝ) * K * H ≤
      P.fraction * (P.fraction * P.theta / (24 * max L (r.runningSigma N))) ^ P.q * ε ^ (P.q + 1)) :
    HigherOrderApproximateRegularization.SatisfiesCriteria P.toParameters f
      (r.state N).point I.radii :=
  r.true_quality_of_uniform_accuracy hL (fun _ hk => r.sigma_le_running hk) hA I hall
    hε hεj hK hH hcoeff hsmall

/-- The useful transfer inequality for the all-order-checked short-step variant. The actual
returned inner witnesses supply the model criticality bound. Every coefficient through `p`
is checked here; the literal `q`-checked algorithm supplies this premise only when `p=q`.
The actual current parameter is used, so no global parameter-bound premise is needed. -/
theorem arqpida_allp_transfer_of_true_gap_failure {P : ARqpIDAParameters}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (O : ImplicitAccuracyOracle f P.p)
    (x : EuclideanSpace ℝ (Fin n)) (h δ : ℕ → ℝ) {σ L K : ℝ}
    (I : Inspection P (f x) (O.derivative x h) σ δ) (hq : I.order ≤ P.q)
    (s : InnerResult P (f x) (O.derivative x h) σ I.radii (I.direction hq))
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hK : 0 ≤ K) (hσ : 0 ≤ σ)
    (hδ : HigherOrderApproximateRegularization.ValidRadii P.toParameters δ)
    (hs : ‖s.step‖ < 1) (haccurate : StepAccurate P P.p h s.step)
    (hcoeff : ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative x h i - iteratedFDeriv ℝ i f x‖ ≤ K * h i)
    (hfail : ¬HigherOrderApproximateRegularization.SatisfiesCriteria
      P.toParameters f (x + s.step) s.radii) :
    ∃ j, 1 ≤ j ∧ j ≤ P.q ∧
      (1 - P.theta) * P.epsilon j * s.radii j ^ j / (j ! : ℝ) ≤
        (L + σ + 3 * K * P.kappaStep) * ∑ l ∈ Finset.Icc 1 j,
          s.radii j ^ l * ‖s.step‖ ^ (P.p - l + 1) / (l ! : ℝ) := by
  apply s.transfer_of_true_gap_failure I hq hf hK hσ le_rfl hδ hs ?_ hfail
  intro i hi
  exact (hcoeff i hi).trans (by
    have ha := (StepAccurate.short_iff hs).mp haccurate i hi
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ha hK)

end CartisGouldToint.Chapter13.Section01
