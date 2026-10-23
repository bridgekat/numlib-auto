import Numlib.Optimization.Regularization.HighOrder.Sharpness.GoodCaseData

/-!
# Actual all-order unit-radius regularization executions

Actual ordered Taylor checks, exact objective ratios and unchanged regularization parameters
define the full execution. Every model computation satisfies the primitive positive-fraction
and unit-radius tests.
-/

namespace HighOrderRegularization.Sharpness
open InexactTrustRegion
/-- The actual ordered objective Taylor checks select the highest order before the last
node and pass strictly at the endpoint. -/
theorem good_optimalityCheck_of_matches {f : ℝ → ℝ} {p q N k : ℕ} {ε : ℝ}
    (hq : 0 < q) (hqp : q ≤ p) (hε : 0 < ε)
    (h : MatchesJets f p q N (goodAmplitude p q) (goodStep p q ε)) (hk : k ≤ N) :
    let t := goodStep p q ε
    OptimalityCheck f 1 (fun _ : Fin q => ε) (fun _ => 1) (point t k)
      (fun _ => 1) ((criticalityData p q N hq t).selected k) := by
  dsimp only
  let t := goodStep p q ε
  have ht := (goodStep_pos (p := p) hq hε).le
  have hdec : ∀ a : Fin q, TaylorModel.decrement f (modelOrder a) (point t k) 1 =
      TaylorModel.criticality f (modelOrder a) (point t k) 1 :=
    fun a => decrement_one_eq_criticality hq hqp h hk a.isLt (goodAmplitude_pos (p := p) hq).le ht
  have hqcrit : TaylorModel.criticality f q (point t k) 1 =
      (if k < N then (4 / 3 : ℝ) * ε else (2 / 3 : ℝ) * ε) / q.factorial := by
    rw [criticality_order_eq hq hqp h hk (goodAmplitude_pos (p := p) hq).le ht]
    have hp := goodAmplitude_step_power (p := p) hq hε.le
    change goodAmplitude p q * goodStep p q ε ^ balance p q = _ at hp
    split_ifs
    · rw [hp]
    · congr 1
      nlinarith
  have hcrit : ∀ a : Fin q, TaylorModel.criticality f (modelOrder a) (point t k) 1 =
      if modelOrder a = q then (if k < N then (4 / 3 : ℝ) * ε else (2 / 3 : ℝ) * ε) /
        (modelOrder a).factorial else 0 := by
    intro a
    by_cases ha : modelOrder a = q
    · simpa only [ha, ite_true] using hqcrit
    · rw [ite_eq_right ha]
      exact criticality_lower_eq_zero hq h hk ((show modelOrder a ≤ q from a.isLt).trans hqp)
        (lt_of_le_of_ne a.isLt ha) zero_le_one
  refine ⟨fun _ _ => by norm_num,
    fun a _ => by rw [hdec]; simp only [one_mul]; exact le_rfl, ?_, ?_, ?_⟩
  · intro hnone a
    have hkn : ¬k < N := by
      by_contra hb
      simp [criticalityData, hb] at hnone
    rw [hdec, hcrit, ite_eq_right hkn]
    simp only [one_mul, one_pow, mul_one]
    split_ifs
    · apply (div_lt_div_iff_of_pos_right (by positivity)).mpr
      linarith
    · positivity
  · intro a hsome
    have hkn : k < N := by
      by_contra hn
      simp [criticalityData, hn] at hsome
    have ha : a = ⟨q - 1, by omega⟩ := by
      simpa only [criticalityData, hkn, ite_true, Option.some.injEq] using hsome.symm
    have haorder : modelOrder a = q := by rw [ha]; unfold modelOrder; dsimp; omega
    rw [hdec, hcrit, ite_eq_left haorder, ite_eq_left hkn]
    simp only [one_mul, one_pow, mul_one]
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr
    linarith
  · intro a hsome b hba
    have hkn : k < N := by
      by_contra hn
      simp [criticalityData, hn] at hsome
    have ha : a = ⟨q - 1, by omega⟩ := by
      simpa only [criticalityData, hkn, ite_true, Option.some.injEq] using hsome.symm
    have hb : modelOrder b < q := by
      rw [ha] at hba
      unfold modelOrder
      exact_mod_cast (show b.val + 1 < q by have := hba; simp only [Fin.lt_def] at this; omega)
    rw [hdec, hcrit, ite_eq_right (ne_of_lt hb)]
    simp only [one_mul, one_pow, mul_one]
    positivity


/-- The matched actual jets give strict model improvement, exact ratio one and legal
constant-parameter updates. -/
theorem good_modelTrace_of_matches {f : ℝ → ℝ} {p q N : ℕ} {t : ℝ}
    (hq : 0 < q) (hqp : q ≤ p) (h : MatchesJets f p q N (goodAmplitude p q) t)
    (ht : 0 < t) :
    HighOrderRegularization.ModelTrace f p (point t) (fun _ => t)
      (fun _ => goodParameter p q) (fun _ => 1)
      (1 / 4) (3 / 4) (1 / 2) 2 3 (goodParameter p q) N := by
  have hσ := goodParameter_pos (p := p) hq
  have hjet : MatchesJets f p q N (cancellationAmplitude p q (goodParameter p q)) t :=
    cancellationAmplitude_goodParameter ▸ h
  have himproves := fun (k : ℕ) (hk : k < N) =>
    cancellation_model_improves (k := k) hq hqp hσ hjet hk ht
  refine ⟨by omega, ?_, himproves, ?_, ?_⟩
  · refine ⟨hσ, le_rfl, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    intro k hk
    norm_num only
    exact ⟨max_le le_rfl (by linarith), le_rfl⟩
  · intro k hk
    have hd := HighOrderRegularization.decrement_pos hσ.le (himproves k hk)
    symm
    rw [HighOrderRegularization.ratio, TaylorModel.decrement_eq,
      eval_step_of_matches hq hqp h hk, ← point_succ]
    apply div_self
    rw [TaylorModel.decrement_eq, eval_step_of_matches hq hqp h hk] at hd
    exact hd.ne'
  · intro k hk
    norm_num only
    exact point_succ t k
/-- Fixed legal ARqp settings for the all-order unit-radius construction. -/
noncomputable def goodSettings {p q : ℕ} (hq : 0 < q) (hqp : q ≤ p) :
    HighOrderRegularization.Settings p q :=
  { criticalitySettings hq hqp with
    sigmaMin := goodParameter p q
    sigmaInitial := goodParameter p q
    sigmaMin_pos := goodParameter_pos hq
    sigmaMin_le_initial := le_rfl }
/-- Actual constant-spacing arrays with unit inherited and model radii and the last failing
order selected. -/
noncomputable def goodData (p q N : ℕ) (hq : 0 < q) (t : ℝ) :
    HighOrderRegularization.ExecutionData ℝ q :=
  { criticalityData p q N hq t with parameter := fun _ => goodParameter p q }
/-- Matched actual jets generate a full primitive ARqp execution for every criticality
order, with no radius reductions. -/
theorem goodRun_of_matches {f : ℝ → ℝ} {p q N : ℕ} {ε : ℝ}
    (hq : 0 < q) (hqp : q ≤ p) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h : MatchesJets f p q N (goodAmplitude p q) (goodStep p q ε)) :
    let P := goodSettings hq hqp
    let t := goodStep p q ε
    let D := goodData p q N hq t
    HighOrderRegularization.Run f P (fun _ => ε) D N := by
  let t := goodStep p q ε
  have ht : 0 < t := goodStep_pos hq hε
  have ht1 : t ≤ 1 := (goodStep_le_scale hq hε.le hε1).trans (goodScale_le_one hq)
  refine {
    accuracy_pos := fun _ => hε
    accuracy_le_one := fun _ => hε1
    initial_parameter := rfl
    initial_radii := fun _ => ⟨zero_lt_one, le_rfl⟩
    modelTrace := good_modelTrace_of_matches hq hqp h ht
    check := fun k hk => good_optimalityCheck_of_matches hq hqp hε h hk
    continues := ?_
    radius_update := fun _ _ => by
      funext a
      norm_num [goodData, goodSettings, criticalityData, criticalitySettings]
    step_two := ?_ }
  · intro k hk hselected
    have hkn : k < N := by
      by_contra hn
      exact hselected (by simp only [goodData, criticalityData, hn, ite_false])
    change ModelSolve.StepComputation
      (model f p (point t k) (goodParameter p q)) modelOrder (1 / 2) 1
        (fun _ => ε) t (fun _ => 1)
    exact cancellation_stepComputation hq hqp (goodParameter_pos hq)
      (cancellationAmplitude_goodParameter ▸ h) hkn ht ht1 hε.le
      (good_model_test_bound hq hε.le hε1)
  · intro k hk
    simp [goodData, criticalityData, hk]

end HighOrderRegularization.Sharpness
