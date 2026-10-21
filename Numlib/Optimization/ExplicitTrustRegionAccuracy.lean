import Numlib.Optimization.ExplicitTrustRegion
import Numlib.Optimization.InexactTrustRegionAccuracy

/-!
# Accuracy estimates for certified trust-region steps

All estimates concern actual returned derivative tensors with known absolute error bounds.
The observable full-order error check controls every shorter Taylor-gap perturbation.
Termination still requires all computed half-threshold witnesses to pass.
-/

noncomputable section
open scoped Nat
namespace Optimization.ExplicitTrustRegion
open InexactTaylorModels TaylorCriticality HigherOrderTrustRegion
open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {q N : ℕ} {p : Parameters} {a : AccuracyParameters}
  {epsilon : ℕ → ℝ} {minimumTolerance : ℝ} {O : Oracle f q} {t : Trace E}

/-- The inherited implicit accuracy predicate applied to actual returned explicit tensors. -/
abbrev UniformAccuracy (O : Oracle f q) (K : ℝ) : Prop :=
  InexactTrustRegion.UniformAccuracy O.toImplicit K

/-- Every request-valid explicit oracle has known uniform derivative-error multiplier one. -/
theorem Oracle.uniformAccuracy (O : Oracle f q) : UniformAccuracy O 1 := by
  simpa [UniformAccuracy, InexactTrustRegion.UniformAccuracy, Oracle.toImplicit] using
    O.derivative_accuracy

/-- Step-dependent request control gives the actual polynomial error of order `q+1`. -/
theorem LegalPrefix.step_decrement_error (h : LegalPrefix p a epsilon minimumTolerance O t N)
    {K : ℝ} (hK : 0 ≤ K) (hO : UniformAccuracy O K)
    {k : ℕ} (hk : k < N) (ht : t.branch k = .trial) :
    |ExplicitTrustRegion.prediction O t k (t.order k) (t.step k) -
      taylorDecrement f (t.order k) (t.point k) (t.step k)| ≤
        2 * K * a.stepConstant * ‖t.step k‖ ^ (q + 1) := by
  have hn : t.branch k ≠ .testRefinement := by simp [ht]
  rw [ExplicitTrustRegion.prediction, ← decrement_iteratedFDeriv]
  apply decrement_error_le_step_power _ _ _ (h.order_le k hk hn) hK a.stepConstant_pos.le
  intro i hi
  have hiq : i ∈ Finset.Icc 1 q := Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans (h.order_le k hk hn)⟩
  have he := hO (t.point k) (t.request k) (fun i hi => h.requests_pos (by omega) hi) i hiq
  have hs := (h.step_branch k hk hn).mp ht i hiq
  exact he.trans (by
    nlinarith [mul_le_mul_of_nonneg_left hs hK])

/-- Computed all-orders passes bound the actual approximate-polynomial gaps by half tolerances. -/
theorem LegalPrefix.approximate_gaps_at_pass (h : LegalPrefix p a epsilon minimumTolerance O t N)
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

/-- The full-order error check bounds every shorter Taylor error sum by its half tolerance. -/
theorem LegalPrefix.errorCheck_each
    (h : LegalPrefix p a epsilon minimumTolerance O t N)
    (he : 0 ≤ minimumTolerance)
    (heps : ∀ j, 1 ≤ j → j ≤ q → minimumTolerance ≤ epsilon j)
    {k : ℕ} (hk : k ≤ N) (hc : ErrorCheck p q minimumTolerance t k)
    {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ q) :
    ∑ i ∈ Finset.Icc 1 j, t.request k i * testRadius p t k ^ i / (i ! : ℝ) ≤
      epsilon j * testRadius p t k ^ j / (2 * (j ! : ℝ)) := by
  have hr := h.testRadius_bounds hk
  have hsum : (∑ i ∈ Finset.Icc 1 j,
      t.request k i * testRadius p t k ^ i / (i ! : ℝ)) ≤
      ∑ i ∈ Finset.Icc 1 q,
        t.request k i * testRadius p t k ^ i / (i ! : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      have hi' := Finset.mem_Icc.mp hi
      exact Finset.mem_Icc.mpr ⟨hi'.1, hi'.2.trans hjq⟩
    · intro i hi _
      exact div_nonneg (mul_nonneg (h.requests_pos hk hi).le
        (pow_nonneg hr.1.le i)) (by positivity)
  have hpower : testRadius p t k ^ q ≤ testRadius p t k ^ j :=
    pow_le_pow_of_le_one hr.1.le hr.2 hjq
  have hmono : minimumTolerance * testRadius p t k ^ q / (q ! : ℝ) ≤
      epsilon j * testRadius p t k ^ j / (j ! : ℝ) := by
    have hep : 0 ≤ epsilon j := he.trans (heps j hj hjq)
    exact (div_le_div_of_nonneg_right
      (mul_le_mul (heps j hj hjq) hpower (pow_nonneg hr.1.le q)
        (he.trans (heps j hj hjq))) (by positivity)).trans
      (div_le_div_of_nonneg_left (mul_nonneg hep (pow_nonneg hr.1.le _))
        (by positivity) (Nat.cast_le.mpr (Nat.factorial_le hjq)))
  have hfrac : p.fraction * minimumTolerance * testRadius p t k ^ q /
      (2 * (q ! : ℝ)) ≤
      minimumTolerance * testRadius p t k ^ q / (2 * (q ! : ℝ)) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right p.fraction_le_one
      (mul_nonneg he (pow_nonneg hr.1.le q))]
  exact ((hsum.trans hc).trans hfrac).trans (by
    convert div_le_div_of_nonneg_right hmono (by norm_num : (0 : ℝ) ≤ 2) using 1 <;>
      ring)

/-- The actual observable stopping test certifies all true Taylor-gap criteria. -/
theorem LegalPrefix.certified_quality [ProperSpace E]
    (h : LegalPrefix p a epsilon minimumTolerance O t N)
    (he : 0 ≤ minimumTolerance)
    (heps : ∀ j, 1 ≤ j → j ≤ q → minimumTolerance ≤ epsilon j)
    {k : ℕ} (hk : k ≤ N) (hc : Certified p epsilon minimumTolerance O t k) :
    Quality (q := q) p epsilon f t k := by
  intro j hj hjq
  have hr := h.testRadius_bounds hk
  have hgap := h.approximate_gaps_at_pass hk hc.1 j hj hjq
  have herr := h.errorCheck_each he heps hk hc.2 hj hjq
  have hp := approximate_gap_certifies (coefficients O t k)
    (fun i => iteratedFDeriv ℝ i f (t.point k)) (t.request k)
    (isCompact_closedBall (0 : E) (testRadius p t k))
    (show (closedBall (0 : E) (testRadius p t k)).Nonempty from
      ⟨0, by simpa using hr.1.le⟩) hr.1.le (Set.Subset.refl _)
    (fun i hi => O.derivative_accuracy _ _ (fun i hi => h.requests_pos hk hi) i
      (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans hjq⟩))
    hgap herr
  have heq : decrement (fun i => iteratedFDeriv ℝ i f (t.point k)) j =
      taylorDecrement f j (t.point k) := funext (decrement_iteratedFDeriv f (t.point k) j)
  rwa [heq] at hp

/-- A small common request bound forces the explicit error certificate at a reachable state.
A computed pass is still separately required for termination. -/
theorem LegalPrefix.errorCheck_of_requests (h : LegalPrefix p a epsilon minimumTolerance O t N)
    {H : ℝ} (hH : 0 ≤ H) {k : ℕ} (hk : k ≤ N)
    (hh : ∀ i ∈ Finset.Icc 1 q, t.request k i ≤ H)
    (hsmall : 4 * H ≤ p.fraction * minimumTolerance * testRadius p t k ^ q / (q ! : ℝ)) :
    ErrorCheck p q minimumTolerance t k := by
  have hr := h.testRadius_bounds hk
  have hs := error_sum_le (q := q) ⟨hr.1.le, hr.2⟩ hH hh
  unfold ErrorCheck
  have heq : p.fraction * minimumTolerance * testRadius p t k ^ q / (2 * (q ! : ℝ)) =
      (p.fraction * minimumTolerance * testRadius p t k ^ q / (q ! : ℝ)) / 2 := by ring
  rw [heq]
  linarith

end Optimization.ExplicitTrustRegion
