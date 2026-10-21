import Numlib.Optimization.InexactTrustRegion

/-!
# Accuracy estimates for implicit trust-region steps

All estimates concern actual returned derivative tensors. Unknown error multipliers enter
only the analysis, never the refinement rule. Passing computed witnesses becomes a true
optimality statement only after bounding the absolute tensor errors.
-/

noncomputable section
open scoped Nat
namespace Optimization.InexactTrustRegion
open InexactTaylorModels TaylorCriticality HigherOrderTrustRegion
open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {q N : ℕ} {p : Parameters} {a : AccuracyParameters}
  {epsilon : ℕ → ℝ} {O : Oracle f q} {t : Trace E}

/-- A common analysis-only multiplier for the genuine errors of an oracle's returned tensors. -/
def UniformAccuracy (O : Oracle f q) (K : ℝ) : Prop :=
  ∀ x h, (∀ i ∈ Finset.Icc 1 q, 0 < h i) → ∀ i ∈ Finset.Icc 1 q,
    ‖O.derivative x h i - iteratedFDeriv ℝ i f x‖ ≤ K * h i

/-- Every implicit accuracy oracle has a finite common error multiplier, even at order zero. -/
theorem Oracle.exists_uniformAccuracy (O : Oracle f q) :
    ∃ K : ℝ, 0 ≤ K ∧ UniformAccuracy O K := by
  obtain ⟨κ, hκ, hO⟩ := O.accuracy
  refine ⟨∑ i ∈ Finset.Icc 1 q, κ i, Finset.sum_nonneg hκ, ?_⟩
  intro x h hh i hi
  exact (hO x h hh i hi).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum hκ hi) (hh i hi).le)

/-- Step-dependent request control gives the actual polynomial error of order `q+1`. -/
theorem LegalPrefix.step_decrement_error (h : LegalPrefix p a epsilon O t N)
    {K : ℝ} (hK : 0 ≤ K) (hO : UniformAccuracy O K)
    {k : ℕ} (hk : k < N) (ht : t.branch k = .trial) :
    |InexactTrustRegion.prediction O t k (t.order k) (t.step k) -
      taylorDecrement f (t.order k) (t.point k) (t.step k)| ≤
        2 * K * a.stepConstant * ‖t.step k‖ ^ (q + 1) := by
  have hn : t.branch k ≠ .testRefinement := by simp [ht]
  rw [InexactTrustRegion.prediction, ← decrement_iteratedFDeriv]
  apply decrement_error_le_step_power _ _ _ (h.order_le k hk hn) hK a.stepConstant_pos.le
  intro i hi
  have hiq : i ∈ Finset.Icc 1 q := Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans (h.order_le k hk hn)⟩
  have he := hO (t.point k) (t.request k) (fun i hi => h.requests_pos (by omega) hi) i hiq
  have hs := (h.step_branch k hk hn).mp ht i hiq
  exact he.trans (by
    nlinarith [mul_le_mul_of_nonneg_left hs hK])

/-- Uniform requested accuracies bound the discrepancy between true and computed Taylor gaps. -/
theorem LegalPrefix.true_gap_le [ProperSpace E] (h : LegalPrefix p a epsilon O t N)
    {K H : ℝ} (hK : 0 ≤ K) (hH : 0 ≤ H) (hO : UniformAccuracy O K)
    {k : ℕ} (hk : k ≤ N) {j : ℕ} (hjq : j ≤ q)
    (hhH : ∀ i ∈ Finset.Icc 1 q, t.request k i ≤ H) :
    gapOn (taylorDecrement f j (t.point k)) (closedBall 0 (testRadius p t k)) ≤
      approximateGap O t k j (testRadius p t k) + 2 * K * H := by
  have hδ := h.testRadius_bounds hk
  have herr := gap_error_le (coefficients O t k)
    (fun i => iteratedFDeriv ℝ i f (t.point k)) (fun _ => K * H) (q := j)
    (isCompact_closedBall (0 : E) (testRadius p t k))
    (show (closedBall (0 : E) (testRadius p t k)).Nonempty from
      ⟨0, by simpa using hδ.1.le⟩) hδ.1.le (Set.Subset.refl _)
    (fun i hi => by
      have hiq : i ∈ Finset.Icc 1 q := Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans hjq⟩
      exact (hO _ _ (fun i hi => h.requests_pos hk hi) i hiq).trans
        (mul_le_mul_of_nonneg_left (hhH i hiq) hK))
  have hsum := error_sum_le (q := j) ⟨hδ.1.le, hδ.2⟩ (mul_nonneg hK hH)
    (fun _ _ => le_rfl)
  have heq : decrement (fun i => iteratedFDeriv ℝ i f (t.point k)) j =
      taylorDecrement f j (t.point k) := funext (decrement_iteratedFDeriv f (t.point k) j)
  rw [heq] at herr
  have hb := (abs_le.mp herr).1
  change gapOn _ _ ≤ gapOn (decrement (coefficients O t k) j) _ + _
  linarith

/-- Computed all-orders passes bound the actual approximate-polynomial gaps by half tolerances. -/
theorem LegalPrefix.approximate_gaps_at_pass (h : LegalPrefix p a epsilon O t N)
    {k : ℕ} (hk : k ≤ N) (hs : AllPass p epsilon O t k) :
    ∀ j, 1 ≤ j → j ≤ q → approximateGap O t k j (testRadius p t k) ≤
      epsilon j * testRadius p t k ^ j / (2 * (j ! : ℝ)) := by
  intro j hj hjq
  have hw := h.witness_fraction k hk j hj hjq
  have ht := hs j hj hjq
  have heq : p.fraction * epsilon j * testRadius p t k ^ j / (2 * (j ! : ℝ)) =
      p.fraction * (epsilon j * testRadius p t k ^ j / (2 * (j ! : ℝ))) := by ring
  rw [heq] at ht
  exact (mul_le_mul_iff_right₀ p.fraction_pos).mp (hw.trans ht)

/-- A true all-orders optimality property, independent of the algorithm's computed tests. -/
def Quality (p : Parameters) (epsilon : ℕ → ℝ) (f : E → ℝ) (t : Trace E) (k : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ q →
    gapOn (taylorDecrement f j (t.point k)) (closedBall 0 (testRadius p t k)) ≤
      epsilon j * testRadius p t k ^ j / (j ! : ℝ)

/-- A small absolute error budget converts an actual computed all-orders pass into true quality.
The multiplicative condition includes zero oracle multipliers without division by them. -/
theorem LegalPrefix.quality_at_pass [ProperSpace E] (h : LegalPrefix p a epsilon O t N)
    {K H : ℝ} (hK : 0 ≤ K) (hH : 0 ≤ H) (hO : UniformAccuracy O K)
    {k : ℕ} (hk : k ≤ N) (hhH : ∀ i ∈ Finset.Icc 1 q, t.request k i ≤ H)
    (hs : AllPass p epsilon O t k)
    (hsmall : ∀ j, 1 ≤ j → j ≤ q → 4 * K * H ≤
      epsilon j * testRadius p t k ^ j / (j ! : ℝ)) :
    Quality (q := q) p epsilon f t k := by
  intro j hj hjq
  have hb := h.true_gap_le hK hH hO hk hjq hhH
  have ha := h.approximate_gaps_at_pass hk hs j hj hjq
  have hc := hsmall j hj hjq
  have heq : epsilon j * testRadius p t k ^ j / (2 * (j ! : ℝ)) =
      (epsilon j * testRadius p t k ^ j / (j ! : ℝ)) / 2 := by ring
  rw [heq] at ha
  linarith

end Optimization.InexactTrustRegion
