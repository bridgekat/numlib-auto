import NumlibSurface.CartisGouldToint.Chapter05.Section04
import Numlib.Optimization.CubicLocalConvergence

/-!
# Corrected global and local cubic phase complexity

The printed local constants use a constant shift in place of the actual step-dependent
cubic shift. We use a smaller explicitly derived local threshold, pay for entry using the
global complexity theorem, and retain the original exclusion hypothesis and original
threshold parameter. The numbered theorem first gives an unconditional first-zeta-stop global
bound, then the conditional first-epsilon-stop local bound, with one common constant fixed
before either tolerance. Both counts concern actual first-attainment prefixes; no arbitrary
all-run reentry count is asserted. The local iteration bound uses integer ceiling logarithms.
The supplied strict final inequality is replaced by the actual AR2 stopping convention
`‖gradient‖ ≤ epsilon`;
no claim is made that the printed local constants or strict terminal inequality are valid.
-/

noncomputable section
namespace CartisGouldToint.Chapter05.Section04
open Optimization Optimization.CubicRegularization Optimization.ParameterUpdates
open Chapter03.Section03

variable {n : ℕ}

/-- The strengthened residual test (5.4.3) on actual cubic models. -/
def strengthenedResidual (p : RegularizationParameters) (theta : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n))
    (sigma : ℕ → ℝ) : Prop :=
  firstOrderRun p theta f x s sigma ∧ ∀ k,
    ‖fderiv ℝ (Chapter03.Section03.cubicModel f (x k) (sigma k)) (s k)‖ ≤
      theta * min ‖gradient f (x k)‖ (‖s k‖ ^ 2 / 2)

/-- A strengthened-residual run satisfies all original AR2 update and model laws. -/
theorem strengthenedResidual.toFirstOrderRun {p : RegularizationParameters} {theta : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)}
    {sigma : ℕ → ℝ} (h : strengthenedResidual p theta f x s sigma) :
    firstOrderRun p theta f x s sigma := h.1

/-- The actual source model residual bound extracted from the bundled strengthened run. -/
theorem strengthenedResidual.model_bound {p : RegularizationParameters} {theta : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)}
    {sigma : ℕ → ℝ} (h : strengthenedResidual p theta f x s sigma) (k : ℕ) :
    ‖fderiv ℝ (Chapter03.Section03.cubicModel f (x k) (sigma k)) (s k)‖ ≤
      theta * min ‖gradient f (x k)‖ (‖s k‖ ^ 2 / 2) := h.2 k

/-- The strengthened source test includes the relative-gradient residual bound. -/
theorem strengthenedResidual.relative {p : RegularizationParameters} {theta : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)}
    {sigma : ℕ → ℝ} (h : strengthenedResidual p theta f x s sigma)
    (htheta : 0 ≤ theta) (k : ℕ) :
    ‖fderiv ℝ (CubicRegularization.cubicModel f (x k) (sigma k)) (s k)‖ ≤
      theta * ‖gradient f (x k)‖ := by
  rw [← Chapter03.Section03.cubicModel_eq]
  exact (h.model_bound k).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) htheta)

/-- The exact exclusion condition (5.4.18), with the original source ball and threshold.
Points whose gradient already meets the non-strict termination test need not lie in the ball. -/
def phaseExclusion (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n)) (L zeta epsilon : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ k, epsilon < ‖gradient f (x k)‖ → ‖gradient f (x k)‖ ≤ zeta →
    x k ∈ localConvexityRegion f xstar L

/-- The corrected global and local phase bound for the actual strengthened-residual AR2
algorithm. The source threshold and exclusion (5.4.18) are retained. Entry into a smaller
valid quadratic region is paid for by a fixed inflation of the global constant; the local
term is a nonnegative integer double logarithm of `2*zeta/epsilon`. Termination uses the
usual non-strict first-order test, and its first occurrence is a conclusion. -/
theorem corrected_phase_complexity [NeZero n] {p : RegularizationParameters} {theta L low : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)}
    {sigma : ℕ → ℝ} (h : strengthenedResidual p theta f x s sigma)
    (hf : Chapter03.Section01.hessianLipschitz f L) (htheta : 0 < theta)
    (hlow : ∀ y, low ≤ f y) {xstar : EuclideanSpace ℝ (Fin n)}
    (hmin : IsLocalMin f xstar)
    (hcurv : 0 < leastCurvature (fderiv ℝ (fderiv ℝ f) xstar)) :
    ∃ C : ℝ, 0 < C ∧ ∀ zeta : ℝ, 0 < zeta →
      zeta ≤ phaseGradientThreshold (leastCurvature (fderiv ℝ (fderiv ℝ f) xstar))
        L theta p.sigmaMin (sigmaMax p L (sigma 0)) p.eta2 / 2 →
      ∀ epsilon : ℝ, 0 < epsilon → phaseExclusion f xstar L zeta epsilon x →
        ∃ K : ℕ, ‖gradient f (x K)‖ ≤ epsilon ∧
          (∀ j < K, epsilon < ‖gradient f (x j)‖) ∧
          (successCount (fun k => p.eta1 ≤ ratio f (x k) (s k) (sigma k) ∧
            zeta < ‖gradient f (x k)‖) K : ℝ) ≤
              C * ((f (x 0) - low) / zeta ^ (3 / 2 : ℝ)) + 1 ∧
          (successCount (fun k => p.eta1 ≤ ratio f (x k) (s k) (sigma k)) K : ℝ) ≤
              C * ((f (x 0) - low) / zeta ^ (3 / 2 : ℝ)) +
                quadraticIterationBound (2 * zeta) epsilon + 1 := by
  classical
  let lambda := leastCurvature (fderiv ℝ (fderiv ℝ f) xstar)
  let M := sigmaMax p L (sigma 0)
  let Z := phaseGradientThreshold lambda L theta p.sigmaMin M p.eta2
  let R := localQuadraticThreshold lambda L theta M p.eta2
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hf.one_le
  have hM : ∀ k, sigma k ≤ M := fun k => lemma_3_3_2 h.toFirstOrderRun hf k
  have hM0 : 0 ≤ M := (h.toFirstOrderRun.toRegularizationUpdates.pos 0).le.trans (hM 0)
  have hR : 0 < R := localQuadraticThreshold_pos hcurv hL htheta hM0 p.eta2_lt_one
  have hZ : 0 < Z := phaseGradientThreshold_pos hcurv hL htheta.le
    p.sigmaMin_pos.le hM0 p.eta2_lt_one
  obtain ⟨S, A, F, hS, _, _, hglobal⟩ := theorem_3_3_5 h.toFirstOrderRun hf htheta hlow
  let C := S * max 1 (Z / R) ^ (3 / 2 : ℝ)
  have hC : 0 < C := mul_pos hS (Real.rpow_pos_of_pos
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _)
  refine ⟨C, hC, ?_⟩
  intro zeta hz hzupper epsilon he hexclusion
  let t := min zeta (R / 2)
  let N := quadraticIterationBound (2 * zeta) epsilon
  let accepted := fun k => p.eta1 ≤ ratio f (x k) (s k) (sigma k)
  have ht : 0 < t := lt_min hz (by positivity)
  have htz : t ≤ zeta := min_le_left _ _
  have htR2 : t ≤ R / 2 := min_le_right _ _
  have htR : t ≤ R := htR2.trans (by linarith)
  obtain ⟨k0, hk0, _, _, hcost⟩ := hglobal t ht
  change ‖gradient f (x k0)‖ ≤ t at hk0
  have hentry : (successCount accepted k0 : ℝ) ≤
      C * ((f (x 0) - low) / zeta ^ (3 / 2 : ℝ)) + 1 := by
    have hb := mul_le_mul_of_nonneg_left
      (phase_entry_budget hz hR hzupper (sub_nonneg.mpr (hlow (x 0)))) hS.le
    rw [← mul_assoc] at hb
    change S * ((f (x 0) - low) / t ^ (3 / 2 : ℝ)) ≤
      C * ((f (x 0) - low) / zeta ^ (3 / 2 : ℝ)) at hb
    change (successCount accepted k0 : ℝ) + 1 ≤
      S * ((f (x 0) - low) / t ^ (3 / 2 : ℝ)) + 2 at hcost
    linarith only [hcost, hb]
  obtain ⟨J, hJ, hJbound, htail⟩ : ∃ J, ‖gradient f (x J)‖ ≤ epsilon ∧
      J ≤ k0 + N ∧ ∀ k, k0 ≤ k → k < J → ‖gradient f (x k)‖ ≤ zeta := by
    by_cases hquality : ‖gradient f (x k0)‖ ≤ epsilon
    · exact ⟨k0, hquality, Nat.le_add_right _ _, fun k hle hlt => by omega⟩
    have hx := hexclusion k0 (lt_of_not_ge hquality) (hk0.trans htz)
    have hinv := h.toFirstOrderRun.local_invariant hf.toHessianLipschitz hL htheta hcurv
      (xstar := xstar) le_rfl hmin.fderiv_eq_zero hM (fun k => h.relative htheta.le k)
      k0 (mem_localConvexityRegion.mp hx) (hk0.trans htR)
    have hrec : ∀ j, ‖gradient f (x (k0 + (j + 1)))‖ ≤
        ‖gradient f (x (k0 + j))‖ ^ 2 / (2 * t) := by
      intro j
      have hh := (hinv j).2.2.2
      have hd : 2 * t ≤ R := by linarith only [htR2]
      have hh' : ‖gradient f (x (k0 + (j + 1)))‖ ≤
          ‖gradient f (x (k0 + j))‖ ^ 2 / R := by
        simpa only [Nat.add_assoc] using hh
      exact hh'.trans (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hd)
    have henv := le_double_exponential_of_quadratic_recurrence
      (g := fun j => ‖gradient f (x (k0 + j))‖)
      (by positivity : 0 < 2 * t) (fun _ => norm_nonneg _)
      (by simpa only [Nat.add_zero, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
        using hk0) hrec
    have hlocal : ‖gradient f (x (k0 + N))‖ ≤ epsilon := by
      calc
        _ ≤ 2 * t / (2 : ℝ) ^ (2 ^ N) := henv N
        _ ≤ 2 * zeta / (2 : ℝ) ^ (2 ^ N) :=
          div_le_div_of_nonneg_right (by linarith only [htz]) (by positivity)
        _ ≤ epsilon := quadraticIterationBound_spec he
    refine ⟨k0 + N, hlocal, le_rfl, ?_⟩
    intro k hle _
    have hp : (2 : ℝ) ≤ (2 : ℝ) ^ (2 ^ (k - k0)) := by
      have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (show 1 ≤ (2 : ℕ) ^ (k - k0) from Nat.one_le_pow _ _ (by norm_num))
      simpa only [pow_one] using hh
    have hh := henv (k - k0)
    rw [Nat.add_sub_of_le hle] at hh
    apply hh.trans
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ (2 ^ (k - k0)))).mpr
    nlinarith only [htz, mul_le_mul_of_nonneg_left hp hz.le]
  have hexists : ∃ K, ‖gradient f (x K)‖ ≤ epsilon := ⟨J, hJ⟩
  let K := Nat.find hexists
  have hK : K ≤ J := Nat.find_min' hexists hJ
  refine ⟨K, Nat.find_spec hexists, ?_, ?_, ?_⟩
  · intro j hj
    exact lt_of_not_ge (Nat.find_min hexists hj)
  · have hc : successCount (fun k => accepted k ∧ zeta < ‖gradient f (x k)‖) K ≤
        successCount accepted k0 := by
      apply Finset.card_le_card
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      have hpre : k < k0 := by
        by_contra hn
        exact (not_le.mpr hk.2.2) (htail k (by omega) (by omega))
      exact ⟨hpre, hk.2.1⟩
    have hc' : (successCount (fun k => accepted k ∧ zeta < ‖gradient f (x k)‖) K : ℝ) ≤
        (successCount accepted k0 : ℝ) := by exact_mod_cast hc
    exact hc'.trans hentry
  · have hc := (successCount_mono accepted (hK.trans hJbound)).trans
      (successCount_add_le accepted k0 N)
    have hc' : (successCount accepted K : ℝ) ≤ (successCount accepted k0 : ℝ) + N := by
      exact_mod_cast hc
    change (successCount accepted K : ℝ) ≤ _
    change _ ≤ _ + (N : ℝ) + 1
    linarith only [hc', hentry]

/-- The unconditional global phase ends at the first actual zeta stop. No local exclusion
or final epsilon tolerance is needed for this first-attainment successful-prefix bound. -/
theorem global_phase_complexity {p : RegularizationParameters} {theta L low : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)}
    {sigma : ℕ → ℝ} (h : firstOrderRun p theta f x s sigma)
    (hf : Chapter03.Section01.hessianLipschitz f L) (htheta : 0 < theta)
    (hlow : ∀ y, low ≤ f y) :
    ∃ C : ℝ, 0 < C ∧ ∀ zeta : ℝ, 0 < zeta →
      ∃ K : ℕ, ‖gradient f (x K)‖ ≤ zeta ∧
        (∀ j < K, zeta < ‖gradient f (x j)‖) ∧
        (successCount (fun k => p.eta1 ≤ ratio f (x k) (s k) (sigma k)) K : ℝ) ≤
          C * ((f (x 0) - low) / zeta ^ (3 / 2 : ℝ)) + 1 := by
  obtain ⟨S, _, _, hS, _, _, hglobal⟩ := theorem_3_3_5 h hf htheta hlow
  refine ⟨S, hS, ?_⟩
  intro zeta hz
  obtain ⟨K, hK, hfirst, _, hcost⟩ := hglobal zeta hz
  exact ⟨K, hK, hfirst, by linarith only [hcost]⟩

/-- Theorem 5.4.4 with the corrections required by its planned phase-count formulation.
The unconditional global branch counts actual successful trials through the first zeta stop;
it precedes and is independent of epsilon and the exclusion condition. The second branch
bounds the first epsilon stop under the unchanged original exclusion (5.4.18). One constant
is chosen before both tolerances. Stopping uses the actual AR2 convention
`‖gradient‖ ≤ tolerance`,
replacing the supplied strict final inequality. A valid local threshold is derived from the
actual cubic shift, its entry cost is absorbed into a parameter-dependent global inflation,
and the local count uses nonnegative integer ceiling logarithms. No arbitrary all-run
reentry count, printed local constants, or strict epsilon termination is asserted. -/
theorem theorem_5_4_4 [NeZero n] {p : RegularizationParameters} {theta L low : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)}
    {sigma : ℕ → ℝ} (h : strengthenedResidual p theta f x s sigma)
    (hf : Chapter03.Section01.hessianLipschitz f L) (htheta : 0 < theta)
    (hlow : ∀ y, low ≤ f y) {xstar : EuclideanSpace ℝ (Fin n)}
    (hmin : IsLocalMin f xstar)
    (hcurv : 0 < leastCurvature (fderiv ℝ (fderiv ℝ f) xstar)) :
    ∃ C : ℝ, 0 < C ∧ ∀ zeta : ℝ, 0 < zeta →
      zeta ≤ phaseGradientThreshold (leastCurvature (fderiv ℝ (fderiv ℝ f) xstar))
        L theta p.sigmaMin (sigmaMax p L (sigma 0)) p.eta2 / 2 →
      (∃ K : ℕ, ‖gradient f (x K)‖ ≤ zeta ∧
        (∀ j < K, zeta < ‖gradient f (x j)‖) ∧
        (successCount (fun k => p.eta1 ≤ ratio f (x k) (s k) (sigma k)) K : ℝ) ≤
          C * ((f (x 0) - low) / zeta ^ (3 / 2 : ℝ)) + 1) ∧
      (∀ epsilon : ℝ, 0 < epsilon → phaseExclusion f xstar L zeta epsilon x →
        ∃ K : ℕ, ‖gradient f (x K)‖ ≤ epsilon ∧
          (∀ j < K, epsilon < ‖gradient f (x j)‖) ∧
          (successCount (fun k => p.eta1 ≤ ratio f (x k) (s k) (sigma k) ∧
            zeta < ‖gradient f (x k)‖) K : ℝ) ≤
              C * ((f (x 0) - low) / zeta ^ (3 / 2 : ℝ)) + 1 ∧
          (successCount (fun k => p.eta1 ≤ ratio f (x k) (s k) (sigma k)) K : ℝ) ≤
              C * ((f (x 0) - low) / zeta ^ (3 / 2 : ℝ)) +
                quadraticIterationBound (2 * zeta) epsilon + 1) := by
  obtain ⟨G, hG, hglobal⟩ := global_phase_complexity h.toFirstOrderRun hf htheta hlow
  obtain ⟨C, hC, hlocal⟩ := corrected_phase_complexity h hf htheta hlow hmin hcurv
  refine ⟨max G C, lt_of_lt_of_le hG (le_max_left _ _), ?_⟩
  intro zeta hz hzupper
  have hgap : 0 ≤ (f (x 0) - low) / zeta ^ (3 / 2 : ℝ) :=
    div_nonneg (sub_nonneg.mpr (hlow (x 0))) (Real.rpow_pos_of_pos hz _).le
  constructor
  · obtain ⟨K, hK, hfirst, hcount⟩ := hglobal zeta hz
    refine ⟨K, hK, hfirst, ?_⟩
    have hb := mul_le_mul_of_nonneg_right (le_max_left G C) hgap
    linarith only [hcount, hb]
  · intro epsilon he hexclusion
    obtain ⟨K, hK, hfirst, hhigh, hcount⟩ := hlocal zeta hz hzupper epsilon he hexclusion
    refine ⟨K, hK, hfirst, ?_, ?_⟩
    all_goals
      have hb := mul_le_mul_of_nonneg_right (le_max_right G C) hgap
      linarith only [hhigh, hcount, hb]

end CartisGouldToint.Chapter05.Section04
