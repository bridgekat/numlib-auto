import Numlib.Optimization.Regularization.Universal.Complexity
import Numlib.Optimization.Regularization.Universal.FirstCounting
/-!
# First-order-only universal evaluation bounds

Actual objective decreases, update intervals and literal stopping checks give
the single accuracy power, logarithm and initialized evaluation schedules.
-/
namespace UniversalRegularization
open EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Consistent primitive execution prefixes must reach a first trial check.
The terminal step is itself computed by the genuine model conditions. -/
theorem exists_first_trial_stop_one {p : ℕ} {P : Settings p} {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β flow : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 1 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r) (hlow : ∀ x, flow ≤ f x)
    {ε1 : ℝ} {D : Data E}
    (hprefix : ∀ N, (∀ i < N, ¬Stops f ε1 none (D.point i + D.step i)) →
      Run f P ε1 none D N ∧
        Step f P none (D.point N) (D.step N) (D.parameter N)) :
    ∃ K, Stops f ε1 none (D.point K + D.step K) ∧
      Run f P ε1 none D K ∧
      Step f P none (D.point K) (D.step K) (D.parameter K) ∧
      ∀ i < K, ¬Stops f ε1 none (D.point i + D.step i) := by
  classical
  have hex : ∃ K, Stops f ε1 none (D.point K + D.step K) := by
    by_contra hn
    have hnon := not_exists.mp hn
    let b := (f (D.point 0) - flow) /
        (decreaseCoefficientOne P H β * (ε1 ^ (((p : ℝ) + β) / ((p : ℝ) + β - 1)))) *
          (1 + |Real.log P.gamma1| / Real.log P.gamma2) +
        (Real.log (uniformCapOne P H β / P.sigmaInitial) +
          (P.r - ((p : ℝ) + β)) / ((p : ℝ) + β - 1) * |Real.log ε1|) /
            Real.log P.gamma2
    obtain ⟨N,hN⟩ := exists_nat_gt b
    exact (not_le_of_gt hN)
      ((hprefix N (fun i _ => hnon i)).1.iterations_le_one hf hH hβ hβ1 hholder ha har hlow)
  have hfirst : ∀ i < Nat.find hex,
      ¬Stops f ε1 none (D.point i + D.step i) := fun i hi => Nat.find_min hex hi
  exact ⟨Nat.find hex,Nat.find_spec hex,(hprefix _ hfirst).1,(hprefix _ hfirst).2,hfirst⟩



/-- A logarithmic first-order tolerance is controlled by its source inverse power. -/
theorem log_le_inverse_power {a ε : ℝ} (ha : 1 < a) (he : 0 < ε) (he1 : ε ≤ 1) :
    |Real.log ε| ≤ 1 / ε ^ (a / (a - 1)) ∧ ε ^ (a / (a - 1)) ≤ 1 := by
  have hp := Real.rpow_pos_of_pos he (a / (a - 1))
  have hq : 1 ≤ a / (a - 1) := (le_div_iff₀ (by linarith : 0 < a - 1)).mpr (by linarith)
  have hd := Real.rpow_le_self_of_le_one he.le he1 hq
  have hi := one_div_le_one_div_of_le hp hd
  have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr he)
  rw [Real.log_inv] at hh
  constructor
  · rw [abs_of_nonpos (Real.log_nonpos he.le he1)]
    simp only [one_div] at hi ⊢
    linarith
  · exact hd.trans he1

/-- The detailed first-order source bound has a uniform inverse power envelope. -/
theorem detailed_bound_le_envelope_one {a ε A B1 C gap : ℝ} (ha : 1 < a)
    (he : 0 < ε) (he1 : ε ≤ 1)
    (hA : 0 ≤ A) (hB1 : 0 ≤ B1) (hC : 0 ≤ C) (hgap : 0 ≤ gap) :
    A * gap / ε ^ (a / (a - 1)) + B1*|Real.log ε| + C ≤
      (A + B1 + C) * (gap + 1) / ε ^ (a / (a - 1)) := by
  obtain ⟨hl1,hd1⟩ := log_le_inverse_power ha he he1
  have hd := Real.rpow_pos_of_pos he (a / (a - 1))
  have hb1 := mul_le_mul_of_nonneg_left hl1 hB1
  have hcc : C ≤ C / ε ^ (a / (a - 1)) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith
  apply (le_div_iff₀ hd).mpr
  have hm1 := (le_div_iff₀ hd).mp (show B1*|Real.log ε| ≤ B1 / ε ^ (a / (a - 1)) by
    simpa only [mul_one_div] using hb1)
  have hmc := (le_div_iff₀ hd).mp hcc
  have hdiv : (A * gap / ε ^ (a / (a - 1))) * ε ^ (a / (a - 1)) = A * gap := by field_simp
  have hb : (A * gap / ε ^ (a / (a - 1)) + B1*|Real.log ε|+C) * ε ^ (a / (a - 1)) ≤ A *
    gap + B1 + C := by
    rw [add_mul,add_mul,hdiv]
    linarith
  exact hb.trans (by nlinarith)

/-- Fixed positive source constants precede all first-order accuracy requests.
The literal first check at initialization or a trial and every actual evaluation schedule
satisfy the displayed objective, bounds for low and remaining derivative orders. -/
theorem exists_uniform_complexity_one {p : ℕ} (P : Settings p) {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β flow : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 1 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r) (hlow : ∀ x, flow ≤ f x) :
    ∃ κS > 0, ∃ κA > 0, ∃ κB1 > 0, ∃ κC > 0, ∃ κO > 0,
      ∀ ε1 : ℝ, 0 < ε1 → ε1 ≤ 1 → ∀ D : Data E,
      (∀ N, (¬Stops f ε1 none (D.point 0) ∧
        ∀ i < N, ¬Stops f ε1 none (D.point i + D.step i)) →
          Run f P ε1 none D N ∧
            Step f P none (D.point N) (D.step N) (D.parameter N)) →
      ∃ K, checkAt f ε1 none D K ∧
        (∀ i < K, ¬checkAt f ε1 none D i) ∧
        (K ≠ 0 → Run f P ε1 none D (K - 1) ∧
          Step f P none (D.point (K - 1)) (D.step (K - 1)) (D.parameter (K - 1))) ∧
        (functionEvaluations K : ℝ) ≤
          κA * (f (D.point 0) - flow) / (ε1 ^ (((p : ℝ) + β) / ((p : ℝ) + β - 1))) +
            κB1 * |Real.log ε1| + κC ∧
        (lowDerivativeEvaluations K : ℝ) ≤
          κA * (f (D.point 0) - flow) / (ε1 ^ (((p : ℝ) + β) / ((p : ℝ) + β - 1))) +
            κB1 * |Real.log ε1| + κC ∧
        (highDerivativeEvaluations f P none D K : ℝ) ≤
          κS * (f (D.point 0) - flow) / (ε1 ^ (((p : ℝ) + β) / ((p : ℝ) + β - 1))) + 1 ∧
        max (max (functionEvaluations K : ℝ) (lowDerivativeEvaluations K : ℝ))
          (highDerivativeEvaluations f P none D K : ℝ) ≤
            κO * (f (D.point 0) - flow + 1) / (ε1 ^ (((p : ℝ) + β) / ((p : ℝ) + β - 1))) := by
  let c := decreaseCoefficientOne P H β
  let S := 1 / c
  let A := 1 + |Real.log P.gamma1| / Real.log P.gamma2
  let b0 := Real.log (uniformCapOne P H β / P.sigmaInitial)
  let b1 := (P.r - ((p : ℝ) + β)) / ((p : ℝ) + β - 1) / Real.log P.gamma2
  let C := |b0| / Real.log P.gamma2 + 2
  let O := S * A + (b1 + 1) + C + S + 1
  have hc : 0 < c := decreaseCoefficientOne_pos P H β
  have hS : 0 < S := one_div_pos.mpr hc
  have hlog : 0 < Real.log P.gamma2 := Real.log_pos P.gamma2_gt
  have hA : 0 < A := by dsimp [A]; positivity
  have hb1 : 0 ≤ b1 := div_nonneg
    (div_nonneg (sub_nonneg.mpr har) (by linarith)) hlog.le
  have hC : 2 ≤ C := by
    dsimp [C]
    linarith [div_nonneg (abs_nonneg b0) hlog.le]
  refine ⟨S,hS,S * A,mul_pos hS hA,b1 + 1,by linarith,
    C,by linarith,O,by dsimp [O];positivity,?_⟩
  intro ε1 he1 he11 D hprefix
  let δ := (ε1 ^ (((p : ℝ) + β) / ((p : ℝ) + β - 1)))
  have hδ : 0 < δ := Real.rpow_pos_of_pos he1 _
  have hgap : 0 ≤ f (D.point 0) - flow := sub_nonneg.mpr (hlow _)
  have hG : 0 ≤ S * A * (f (D.point 0) - flow) / δ := by positivity
  have htotal : 2 ≤ S * A * (f (D.point 0) - flow) / δ +
      (b1 + 1)*|Real.log ε1| + C := by
    have h1 := mul_nonneg (show 0 ≤ b1 + 1 by linarith) (abs_nonneg (Real.log ε1))
    linarith
  have hlowEnvelope : S * A * (f (D.point 0) - flow) / δ +
      (b1 + 1)*|Real.log ε1| + C ≤
        O * (f (D.point 0) - flow + 1) / δ := by
    apply (detailed_bound_le_envelope_one ha he1 he11
      (mul_pos hS hA).le (by linarith) (by linarith) hgap).trans
    apply (div_le_div_iff_of_pos_right hδ).mpr
    apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ f (D.point 0) - flow + 1)
    dsimp [O]
    linarith
  have hhighEnvelope : S * (f (D.point 0) - flow) / δ + 1 ≤
      O * (f (D.point 0) - flow + 1) / δ := by
    have hh := detailed_bound_le_envelope_one (A := S) (B1 := 0) (C := 1)
      ha he1 he11 hS.le le_rfl zero_le_one hgap
    simp only [zero_mul,add_zero] at hh
    apply hh.trans
    apply (div_le_div_iff_of_pos_right hδ).mpr
    apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ f (D.point 0) - flow + 1)
    dsimp [O]
    nlinarith
  by_cases hi : Stops f ε1 none (D.point 0)
  · refine ⟨0,by simpa only [checkAt,ite_true] using hi,by simp,by simp,?_,?_,?_,?_⟩
    · simpa only [functionEvaluations,Nat.cast_one, max_eq_left (by omega : 0 ≤ 1)] using
        (show (1 : ℝ) ≤ _ by linarith [htotal])
    · simpa only [lowDerivativeEvaluations,zero_add,Nat.cast_one] using
        (show (1 : ℝ) ≤ _ by linarith [htotal])
    · simp only [highDerivativeEvaluations,ite_true,Nat.cast_one]
      have hh : 0 ≤ S * (f (D.point 0) - flow) / δ := by positivity
      linarith
    · simp only [functionEvaluations,lowDerivativeEvaluations,highDerivativeEvaluations,
        ite_true,max_eq_left (by omega : 0 ≤ 1),zero_add,Nat.cast_one,max_self]
      exact (show (1 : ℝ) ≤ _ by linarith [htotal]).trans hlowEnvelope
  obtain ⟨N,hstop,hrun,hstep,hfirst⟩ := exists_first_trial_stop_one
    hf hH hβ hβ1 hholder ha har hlow (fun N hn => hprefix N ⟨hi,hn⟩)
  have hD : ((successfulIterations (successful f P none D) N).card : ℝ) ≤
      S * (f (D.point 0) - flow) / δ := by
    convert hrun.successful_card_le_one hf hH hβ hβ1 hholder ha har hlow using 1
    dsimp [S,c,δ,accuracyFactor]
    field_simp
  have hN : (N : ℝ) ≤ S * A * (f (D.point 0) - flow) / δ +
      b0 / Real.log P.gamma2 + b1*|Real.log ε1| := by
    convert hrun.iterations_le_one hf hH hβ hβ1 hholder ha har hlow using 1
    dsimp [S,c,δ,A,b0,b1,accuracyFactor]
    field_simp
    ring
  have hN2 : (N : ℝ) + 2 ≤ S * A * (f (D.point 0) - flow) / δ +
      (b1 + 1)*|Real.log ε1| + C := by
    have hb0 := div_le_div_of_nonneg_right (le_abs_self b0) hlog.le
    dsimp [C]
    nlinarith [abs_nonneg (Real.log ε1)]
  refine ⟨N + 1,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [checkAt,Nat.add_eq_zero_iff, Nat.one_ne_zero,and_false,ite_false,
      Nat.add_sub_cancel] using hstop
  · intro i hiN
    cases i with
    | zero => simpa only [checkAt,ite_true] using hi
    | succ i =>
      simpa only [checkAt,Nat.succ_ne_zero,ite_false,Nat.succ_sub_one] using
        hfirst i (by omega)
  · intro _
    simpa only [Nat.add_sub_cancel] using And.intro hrun hstep
  · simp only [functionEvaluations,max_eq_right (by omega : 1 ≤ N + 1),
      Nat.cast_add,Nat.cast_one]
    linarith [hN2]
  · simp only [lowDerivativeEvaluations,Nat.cast_add,Nat.cast_one]
    linarith [hN2]
  · simpa only [highDerivativeEvaluations,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,
      ite_false,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using
        add_le_add hD (le_refl (1 : ℝ))
  · simp only [functionEvaluations,lowDerivativeEvaluations,highDerivativeEvaluations,
      max_eq_right (by omega : 1 ≤ N + 1),Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,
      ite_false,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    apply max_le
    · apply max_le
      · exact (show (N : ℝ) + 1 ≤ _ by linarith [hN2]).trans hlowEnvelope
      · exact (show (N : ℝ) + 1 + 1 ≤ _ by linarith [hN2]).trans hlowEnvelope
    · exact (add_le_add hD (le_refl (1 : ℝ))).trans hhighEnvelope

end UniversalRegularization
