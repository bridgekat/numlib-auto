import Numlib.Optimization.Regularization.Universal.Counting

/-!
# First literal stopping checks and universal evaluation counts

A genuine execution provides actual primitive steps and update prefixes until
its first true check. Finite budgets force that first check, including the
initial check before any model computation.
-/
namespace UniversalRegularization
open EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
attribute [local instance] Classical.propDecidable

/-- The positive source minimum of the two stopping accuracy powers. -/
noncomputable def accuracyFactor (a ε1 ε2 : ℝ) : ℝ :=
  min (ε1 ^ (a / (a - 1))) (ε2 ^ (a / (a - 2)))

/-- Both positive accuracies give a positive source accuracy factor. -/
theorem accuracyFactor_pos {a ε1 ε2 : ℝ} (hε1 : 0 < ε1) (hε2 : 0 < ε2) :
    0 < accuracyFactor a ε1 ε2 :=
  lt_min (Real.rpow_pos_of_pos hε1 _) (Real.rpow_pos_of_pos hε2 _)

/-- The actual algorithm checks the initial point and then each model trial before acceptance. -/
def checkAt (f : E → ℝ) (ε1 : ℝ) (ε2 : Option ℝ) (D : Data E) (k : ℕ) : Prop :=
  if k = 0 then Stops f ε1 ε2 (D.point 0)
  else Stops f ε1 ε2 (D.point (k - 1) + D.step (k - 1))

/-- The point returned by a true check, including an immediate initial return. -/
def returnedPoint (D : Data E) (k : ℕ) : E :=
  if k = 0 then D.point 0 else D.point (k - 1) + D.step (k - 1)

/-- Function initialization and nonterminal trials; the terminal check needs no value. -/
def functionEvaluations (K : ℕ) : ℕ := max 1 K

/-- First and second derivatives are evaluated initially and at every computed trial. -/
def lowDerivativeEvaluations (K : ℕ) : ℕ := K + 1

/-- Remaining derivatives are evaluated at the initial point and new accepted iterates. -/
noncomputable def highDerivativeEvaluations {p : ℕ} (f : E → ℝ) (P : Settings p)
    (ε2 : Option ℝ) (D : Data E) (K : ℕ) : ℕ :=
  if K = 0 then 1 else (successfulIterations (successful f P ε2 D) (K - 1)).card + 1

/-- True stopping at a check gives the source output guarantees at its returned point. -/
theorem checkAt_guarantee {f : E → ℝ} {ε1 : ℝ} {ε2 : Option ℝ} {D : Data E} {K : ℕ}
    (h : checkAt f ε1 ε2 D K) : Stops f ε1 ε2 (returnedPoint D K) := by
  simpa only [checkAt,returnedPoint,apply_ite] using h

/-- Consistent primitive execution prefixes must reach a first trial check.
The terminal step is itself computed by the genuine model conditions. -/
theorem exists_first_trial_stop_two {p : ℕ} {P : Settings p} {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β flow : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 2 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r) (hlow : ∀ x, flow ≤ f x)
    {ε1 ε2 : ℝ} {D : Data E}
    (hprefix : ∀ N, (∀ i < N, ¬Stops f ε1 (some ε2) (D.point i + D.step i)) →
      Run f P ε1 (some ε2) D N ∧
        Step f P (some ε2) (D.point N) (D.step N) (D.parameter N)) :
    ∃ K, Stops f ε1 (some ε2) (D.point K + D.step K) ∧
      Run f P ε1 (some ε2) D K ∧
      Step f P (some ε2) (D.point K) (D.step K) (D.parameter K) ∧
      ∀ i < K, ¬Stops f ε1 (some ε2) (D.point i + D.step i) := by
  classical
  have hex : ∃ K, Stops f ε1 (some ε2) (D.point K + D.step K) := by
    by_contra hn
    have hnon := not_exists.mp hn
    let b := (f (D.point 0) - flow) /
        (decreaseCoefficientTwo P H β * accuracyFactor ((p : ℝ) + β) ε1 ε2) *
          (1 + |Real.log P.gamma1| / Real.log P.gamma2) +
        (Real.log (uniformCapTwo P H β / P.sigmaInitial) +
          (P.r - ((p : ℝ) + β)) / ((p : ℝ) + β - 1) * |Real.log ε1| +
          (P.r - ((p : ℝ) + β)) / ((p : ℝ) + β - 2) * |Real.log ε2|) /
            Real.log P.gamma2
    obtain ⟨N,hN⟩ := exists_nat_gt b
    exact (not_le_of_gt hN)
      ((hprefix N (fun i _ => hnon i)).1.iterations_le_two hf hH hβ hβ1 hholder ha har hlow)
  have hfirst : ∀ i < Nat.find hex,
      ¬Stops f ε1 (some ε2) (D.point i + D.step i) := fun i hi => Nat.find_min hex hi
  exact ⟨Nat.find hex,Nat.find_spec hex,(hprefix _ hfirst).1,(hprefix _ hfirst).2,hfirst⟩


/-- Logarithmic accuracy terms are bounded by the reciprocal source accuracy factor. -/
theorem logs_le_inverse_accuracy {a ε1 ε2 : ℝ} (ha : 2 < a)
    (he1 : 0 < ε1) (he11 : ε1 ≤ 1) (he2 : 0 < ε2) (he21 : ε2 ≤ 1) :
    |Real.log ε1| ≤ 1 / accuracyFactor a ε1 ε2 ∧
      |Real.log ε2| ≤ 1 / accuracyFactor a ε1 ε2 ∧ accuracyFactor a ε1 ε2 ≤ 1 := by
  have hδ := accuracyFactor_pos (a := a) he1 he2
  have hq1 : 1 ≤ a / (a-1) := (le_div_iff₀ (by linarith : 0 < a-1)).mpr (by linarith)
  have hq2 : 1 ≤ a / (a-2) := (le_div_iff₀ (by linarith : 0 < a-2)).mpr (by linarith)
  have hd1 : accuracyFactor a ε1 ε2 ≤ ε1 := (min_le_left _ _).trans
    (Real.rpow_le_self_of_le_one he1.le he11 hq1)
  have hd2 : accuracyFactor a ε1 ε2 ≤ ε2 := (min_le_right _ _).trans
    (Real.rpow_le_self_of_le_one he2.le he21 hq2)
  have hlog (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδε : accuracyFactor a ε1 ε2 ≤ ε) :
      |Real.log ε| ≤ 1 / accuracyFactor a ε1 ε2 := by
    have hi : (1 : ℝ)/ε ≤ 1 / accuracyFactor a ε1 ε2 :=
      (div_le_div_iff₀ hε hδ).mpr (by simpa only [one_mul] using hδε)
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hε)
    rw [Real.log_inv] at hh
    simp only [one_div] at hi
    rw [abs_of_nonpos (Real.log_nonpos hε.le hε1)]
    simp only [one_div]
    linarith
  exact ⟨hlog ε1 he1 he11 hd1,hlog ε2 he2 he21 hd2,hd1.trans he11⟩

/-- The detailed source bound has a uniform reciprocal-accuracy envelope. -/
theorem detailed_bound_le_envelope {a ε1 ε2 A B1 B2 C gap : ℝ} (ha : 2 < a)
    (he1 : 0 < ε1) (he11 : ε1 ≤ 1) (he2 : 0 < ε2) (he21 : ε2 ≤ 1)
    (hA : 0 ≤ A) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (hC : 0 ≤ C) (hgap : 0 ≤ gap) :
    A * gap / accuracyFactor a ε1 ε2 + B1*|Real.log ε1| + B2*|Real.log ε2| + C ≤
      (A+B1+B2+C) * (gap+1) / accuracyFactor a ε1 ε2 := by
  obtain ⟨hl1,hl2,hd1⟩ := logs_le_inverse_accuracy ha he1 he11 he2 he21
  have hd := accuracyFactor_pos (a := a) he1 he2
  have hb1 := mul_le_mul_of_nonneg_left hl1 hB1
  have hb2 := mul_le_mul_of_nonneg_left hl2 hB2
  have hcc : C ≤ C / accuracyFactor a ε1 ε2 := by
    apply (le_div_iff₀ hd).mpr
    nlinarith
  apply (le_div_iff₀ hd).mpr
  have hm1 := (le_div_iff₀ hd).mp (show B1*|Real.log ε1| ≤ B1/accuracyFactor a ε1 ε2 by
    simpa only [mul_one_div] using hb1)
  have hm2 := (le_div_iff₀ hd).mp (show B2*|Real.log ε2| ≤ B2/accuracyFactor a ε1 ε2 by
    simpa only [mul_one_div] using hb2)
  have hmc := (le_div_iff₀ hd).mp hcc
  have hdiv : (A*gap/accuracyFactor a ε1 ε2)*accuracyFactor a ε1 ε2=A*gap := by
    field_simp
  have hb : (A*gap/accuracyFactor a ε1 ε2+B1*|Real.log ε1|+B2*|Real.log ε2|+C)*
      accuracyFactor a ε1 ε2 ≤ A*gap+B1+B2+C := by
    rw [add_mul,add_mul,add_mul,hdiv]
    linarith
  exact hb.trans (by nlinarith)

/-- The reciprocal source minimum is exactly the displayed worst accuracy rate. -/
theorem reciprocal_accuracy_eq_rate {a ε1 ε2 : ℝ} (he1 : 0 < ε1) (he2 : 0 < ε2) :
    1 / accuracyFactor a ε1 ε2 =
      max (ε1 ^ (-a / (a - 1))) (ε2 ^ (-a / (a - 2))) := by
  rw [neg_div,Real.rpow_neg he1.le,neg_div,Real.rpow_neg he2.le]
  simp only [one_div,accuracyFactor]
  have hp1 := Real.rpow_pos_of_pos he1 (a/(a-1))
  have hp2 := Real.rpow_pos_of_pos he2 (a/(a-2))
  by_cases h : ε1 ^ (a/(a-1)) ≤ ε2 ^ (a/(a-2))
  · rw [min_eq_left h,max_eq_left ((inv_le_inv₀ hp2 hp1).mpr h)]
  · rw [min_eq_right (le_of_not_ge h),max_eq_right
      ((inv_le_inv₀ hp1 hp2).mpr (le_of_not_ge h))]

/-- Fixed positive source constants precede all two-test accuracy requests.
The literal first initial-or-trial check and every actual evaluation schedule
satisfy the displayed objective, low-derivative and remaining-derivative bounds. -/
theorem exists_uniform_complexity_two {p : ℕ} (P : Settings p) {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β flow : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 2 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r) (hlow : ∀ x, flow ≤ f x) :
    ∃ κS > 0, ∃ κA > 0, ∃ κB1 > 0, ∃ κB2 > 0, ∃ κC > 0, ∃ κO > 0,
      ∀ ε1 ε2 : ℝ, 0 < ε1 → ε1 ≤ 1 → 0 < ε2 → ε2 ≤ 1 → ∀ D : Data E,
      (∀ N, (¬Stops f ε1 (some ε2) (D.point 0) ∧
        ∀ i < N, ¬Stops f ε1 (some ε2) (D.point i + D.step i)) →
          Run f P ε1 (some ε2) D N ∧
            Step f P (some ε2) (D.point N) (D.step N) (D.parameter N)) →
      ∃ K, checkAt f ε1 (some ε2) D K ∧
        (∀ i < K, ¬checkAt f ε1 (some ε2) D i) ∧
        (K ≠ 0 → Run f P ε1 (some ε2) D (K - 1) ∧
          Step f P (some ε2) (D.point (K - 1)) (D.step (K - 1)) (D.parameter (K - 1))) ∧
        (functionEvaluations K : ℝ) ≤
          κA * (f (D.point 0) - flow) / accuracyFactor ((p : ℝ) + β) ε1 ε2 +
            κB1 * |Real.log ε1| + κB2 * |Real.log ε2| + κC ∧
        (lowDerivativeEvaluations K : ℝ) ≤
          κA * (f (D.point 0) - flow) / accuracyFactor ((p : ℝ) + β) ε1 ε2 +
            κB1 * |Real.log ε1| + κB2 * |Real.log ε2| + κC ∧
        (highDerivativeEvaluations f P (some ε2) D K : ℝ) ≤
          κS * (f (D.point 0) - flow) / accuracyFactor ((p : ℝ) + β) ε1 ε2 + 1 ∧
        max (max (functionEvaluations K : ℝ) (lowDerivativeEvaluations K : ℝ))
          (highDerivativeEvaluations f P (some ε2) D K : ℝ) ≤
            κO * (f (D.point 0) - flow + 1) / accuracyFactor ((p : ℝ) + β) ε1 ε2 := by
  let c := decreaseCoefficientTwo P H β
  let S := 1 / c
  let A := 1 + |Real.log P.gamma1| / Real.log P.gamma2
  let b0 := Real.log (uniformCapTwo P H β / P.sigmaInitial)
  let b1 := (P.r - ((p : ℝ) + β)) / ((p : ℝ) + β - 1) / Real.log P.gamma2
  let b2 := (P.r - ((p : ℝ) + β)) / ((p : ℝ) + β - 2) / Real.log P.gamma2
  let C := |b0| / Real.log P.gamma2 + 2
  let O := S*A+(b1+1)+(b2+1)+C+S+1
  have hc : 0 < c := decreaseCoefficientTwo_pos P H β
  have hS : 0 < S := one_div_pos.mpr hc
  have hlog : 0 < Real.log P.gamma2 := Real.log_pos P.gamma2_gt
  have hA : 0 < A := by dsimp [A]; positivity
  have hb1 : 0 ≤ b1 := div_nonneg
    (div_nonneg (sub_nonneg.mpr har) (by linarith)) hlog.le
  have hb2 : 0 ≤ b2 := by dsimp [b2]; positivity [sub_nonneg.mpr har,sub_pos.mpr ha]
  have hC : 2 ≤ C := by
    dsimp [C]
    linarith [div_nonneg (abs_nonneg b0) hlog.le]
  refine ⟨S,hS,S*A,mul_pos hS hA,b1+1,by linarith,b2+1,by linarith,
    C,by linarith,O,by dsimp [O];positivity,?_⟩
  intro ε1 ε2 he1 he11 he2 he21 D hprefix
  let δ := accuracyFactor ((p : ℝ) + β) ε1 ε2
  have hδ : 0 < δ := accuracyFactor_pos he1 he2
  have hgap : 0 ≤ f (D.point 0) - flow := sub_nonneg.mpr (hlow _)
  have hG : 0 ≤ S*A*(f (D.point 0) - flow)/δ := by positivity
  have htotal : 2 ≤ S*A*(f (D.point 0) - flow)/δ +
      (b1+1)*|Real.log ε1| + (b2+1)*|Real.log ε2| + C := by
    have h1 := mul_nonneg (show 0 ≤ b1+1 by linarith) (abs_nonneg (Real.log ε1))
    have h2 := mul_nonneg (show 0 ≤ b2+1 by linarith) (abs_nonneg (Real.log ε2))
    linarith
  have hlowEnvelope : S*A*(f (D.point 0) - flow)/δ +
      (b1+1)*|Real.log ε1| + (b2+1)*|Real.log ε2| + C ≤
        O*(f (D.point 0) - flow+1)/δ := by
    apply (detailed_bound_le_envelope ha he1 he11 he2 he21
      (mul_pos hS hA).le (by linarith) (by linarith) (by linarith) hgap).trans
    apply (div_le_div_iff_of_pos_right hδ).mpr
    apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ f (D.point 0) - flow+1)
    dsimp [O]
    linarith
  have hhighEnvelope : S*(f (D.point 0) - flow)/δ+1 ≤
      O*(f (D.point 0) - flow+1)/δ := by
    have hh := detailed_bound_le_envelope (A := S) (B1 := 0) (B2 := 0) (C := 1)
      ha he1 he11 he2 he21 hS.le le_rfl le_rfl zero_le_one hgap
    simp only [zero_mul,add_zero] at hh
    apply hh.trans
    apply (div_le_div_iff_of_pos_right hδ).mpr
    apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ f (D.point 0) - flow+1)
    dsimp [O]
    nlinarith
  by_cases hi : Stops f ε1 (some ε2) (D.point 0)
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
  obtain ⟨N,hstop,hrun,hstep,hfirst⟩ := exists_first_trial_stop_two
    hf hH hβ hβ1 hholder ha har hlow (fun N hn => hprefix N ⟨hi,hn⟩)
  have hD : ((successfulIterations (successful f P (some ε2) D) N).card : ℝ) ≤
      S * (f (D.point 0) - flow) / δ := by
    convert hrun.successful_card_le_two hf hH hβ hβ1 hholder ha har hlow using 1
    dsimp [S,c,δ,accuracyFactor]
    field_simp
  have hN : (N : ℝ) ≤ S*A*(f (D.point 0) - flow)/δ +
      b0/Real.log P.gamma2 + b1*|Real.log ε1| + b2*|Real.log ε2| := by
    convert hrun.iterations_le_two hf hH hβ hβ1 hholder ha har hlow using 1
    dsimp [S,c,δ,A,b0,b1,b2,accuracyFactor]
    field_simp
    ring
  have hN2 : (N : ℝ)+2 ≤ S*A*(f (D.point 0) - flow)/δ +
      (b1+1)*|Real.log ε1| + (b2+1)*|Real.log ε2| + C := by
    have hb0 := div_le_div_of_nonneg_right (le_abs_self b0) hlog.le
    dsimp [C]
    nlinarith [abs_nonneg (Real.log ε1),abs_nonneg (Real.log ε2)]
  refine ⟨N+1,?_,?_,?_,?_,?_,?_,?_⟩
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
  · simp only [functionEvaluations,max_eq_right (by omega : 1 ≤ N+1),
      Nat.cast_add,Nat.cast_one]
    linarith [hN2]
  · simp only [lowDerivativeEvaluations,Nat.cast_add,Nat.cast_one]
    linarith [hN2]
  · simpa only [highDerivativeEvaluations,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,
      ite_false,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using
        add_le_add hD (le_refl (1 : ℝ))
  · simp only [functionEvaluations,lowDerivativeEvaluations,highDerivativeEvaluations,
      max_eq_right (by omega : 1 ≤ N+1),Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,
      ite_false,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    apply max_le
    · apply max_le
      · exact (show (N : ℝ)+1 ≤ _ by linarith [hN2]).trans hlowEnvelope
      · exact (show (N : ℝ)+1+1 ≤ _ by linarith [hN2]).trans hlowEnvelope
    · exact (add_le_add hD (le_refl (1 : ℝ))).trans hhighEnvelope
end UniversalRegularization
