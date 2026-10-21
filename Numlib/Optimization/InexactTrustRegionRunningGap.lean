import Numlib.Optimization.InexactTrustRegionBounds

/-!
# Historical gaps for implicit trust-region iterations

Only actual trial indices enter the historical minimum. Accuracy-only transitions leave the
radius fixed. The common success threshold yields the running-gap radius bound without assuming
any gap or decrease result as an execution field.
-/

noncomputable section
open scoped Nat
namespace Optimization.InexactTrustRegion
open HigherOrderTrustRegion HigherOrderRegularization
attribute [local instance] Classical.propDecidable
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {q N : ℕ} {p : Parameters} {a : AccuracyParameters}
  {epsilon : ℕ → ℝ} {O : Oracle f q} {t : Trace E}

/-- The minimum scaled computed gap at actual trials through the specified index.
The value at an empty trial history is zero, and empty histories are treated separately. -/
def runningGap (p : Parameters) (O : Oracle f q) (t : Trace E) (k : ℕ) : ℝ :=
  if hs : (trials t (k + 1)).Nonempty then
    (trials t (k + 1)).inf' hs (InexactTrustRegion.scaledGap p O t) else 0

/-- Every historical actual trial bounds the running minimum from above. -/
theorem runningGap_le {k i : ℕ} (hi : i ∈ trials t (k + 1)) :
    runningGap p O t k ≤ InexactTrustRegion.scaledGap p O t i := by
  rw [runningGap, dite_eq_left ⟨i, hi⟩]
  exact Finset.inf'_le _ hi

/-- Half-threshold computed failures give the full historical scaled-gap lower bound. -/
theorem LegalPrefix.runningGap_lower (h : LegalPrefix p a epsilon O t N)
    {emin : ℝ} (he : ∀ j, 1 ≤ j → j ≤ q → emin ≤ epsilon j)
    {k : ℕ} (hk : k < N) (hs : (trials t (k + 1)).Nonempty) :
    p.fraction * emin / 2 ≤ runningGap p O t k := by
  rw [runningGap, dite_eq_left hs]
  apply Finset.le_inf'
  intro i hi
  have hm := Finset.mem_filter.mp hi
  exact (h.scaledGap_lower he (by have := Finset.mem_range.mp hm.1; omega)
    (by simp [hm.2])).le

/-- Without any executed trial the trust-region radius remains its initial value. -/
theorem LegalPrefix.radius_eq_initial_of_no_trials (h : LegalPrefix p a epsilon O t N)
    (hs : trials t N = ∅) : t.radius N = t.radius 0 := by
  have hall : ∀ k ≤ N, t.radius k = t.radius 0 := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have ht : t.branch k ≠ .trial := by
        intro ht
        have hm : k ∈ trials t N := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ht⟩
        rw [hs] at hm
        exact Finset.notMem_empty k hm
      exact (h.accuracy_radius k (by omega) ht).trans (ih (by omega))
  exact hall N le_rfl

/-- The radius lower bound expressed in the historical trial gap, valid for any analysis
coefficient below the actual sufficient-success coefficient. -/
theorem LegalPrefix.radius_lower_runningGap (h : LegalPrefix p a epsilon O t N)
    (he : ∀ j, 1 ≤ j → j ≤ q → 0 < epsilon j)
    {K L c : ℝ} (hK : 0 ≤ K) (hL : 0 < L) (hO : UniformAccuracy O K)
    (hf : ∀ j, 1 ≤ j → j ≤ q → DiagonalLipschitz f j L)
    (hi : p.theta ≤ t.radius 0)
    (hc : c ≤ p.gamma1 * (1 - p.eta2) / errorCoefficient q L K a.stepConstant)
    {k : ℕ} (hk : k < N) (hgap : 0 ≤ runningGap p O t k) :
    min (p.gamma1 * p.theta) (c * runningGap p O t k) ≤ t.radius k := by
  let α := runningGap p O t k
  let C := errorCoefficient q L K a.stepConstant
  have hks := a.stepConstant_pos
  have hC : 0 < C := by dsimp [C, errorCoefficient]; positivity
  let T := min p.theta ((1 - p.eta2) * α / C)
  have hp : LegalPrefix p a epsilon O t (k + 1) := by
    exact ⟨h.initial_pos, h.initial_cap, h.request_pos,
      fun i hi => h.witness_feasible i (by omega),
      fun i hi => h.witness_fraction i (by omega),
      fun i hi => h.test_branch i (by omega),
      fun i hi => h.order_pos i (by omega), fun i hi => h.order_le i (by omega),
      fun i hi => h.first_failure i (by omega), fun i hi => h.failure i (by omega),
      fun i hi => h.step_feasible i (by omega), fun i hi => h.prediction i (by omega),
      fun i hi => h.step_branch i (by omega), fun i hi => h.iterate i (by omega),
      fun i hi => h.request_update i (by omega), fun i hi => h.accuracy_radius i (by omega),
      fun i hi => h.trial_radius i (by omega), fun i hi => h.reuse i (by omega)⟩
  have hsmall : ∀ i < k + 1, t.branch i = .trial → t.radius i ≤ T →
      p.eta2 ≤ InexactTrustRegion.ratio O t i := by
    intro i hiN ht hr
    apply hp.ratio_ge_of_radius he hK hL.le hO hf hiN ht (hr.trans (min_le_left _ _))
    have hm : i ∈ trials t (k + 1) := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hiN, ht⟩
    have hg := runningGap_le (p := p) (O := O) hm
    have hb := (le_div_iff₀ hC).mp (hr.trans (min_le_right _ _))
    nlinarith [mul_le_mul_of_nonneg_left hg (sub_nonneg.mpr p.eta2_lt_one.le)]
  apply le_trans _ (hp.radius_lower_of_threshold hsmall (k := k) (by omega))
  apply le_min
  · exact (min_le_left _ _).trans ((mul_le_of_le_one_left p.theta_pos.le
      (p.gamma_le.trans p.gamma2_lt_one.le)).trans hi)
  · dsimp [T]
    rw [mul_min_of_nonneg _ _ p.gamma1_pos.le]
    apply le_min (min_le_left _ _)
    apply (min_le_right _ _).trans
    have hh := mul_le_mul_of_nonneg_right hc hgap
    convert hh using 1
    ring

end Optimization.InexactTrustRegion
