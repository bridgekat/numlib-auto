import Numlib.Optimization.SmoothDescent
import Numlib.Optimization.ParameterUpdates

/-!
# Adaptive first-order regularization

Lawful runs retain the three update intervals and the actual trial objective. The ratio at a
zero gradient is extended by one; this only specifies an unused continuation after termination.
Evaluation counts concern the prefix preceding the first successful gradient test.
-/

noncomputable section
namespace Optimization.FirstOrderRegularization

/-- Ordered adaptive-regularization parameters, shared across model orders. -/
abbrev Parameters := ParameterUpdates.RegularizationParameters

variable {E : Type*} [NormedAddCommGroup E]

section Normed
variable [NormedSpace ℝ E]

/-- Exact first-order regularized trial point. -/
def trial (g : E → E) (x : E) (sigma : ℝ) : E := x - sigma⁻¹ • g x

open Classical in
/-- Actual reduction divided by the linear-model reduction. -/
def ratio (f : E → ℝ) (g : E → E) (x : E) (sigma : ℝ) : ℝ :=
  if g x = 0 then 1 else (f x - f (trial g x sigma)) / (‖g x‖ ^ 2 / sigma)

/-- A run makes precisely the accepted moves and obeys all three parameter-update intervals.
It can be truncated at any positive gradient tolerance. -/
structure IsRun (p : Parameters) (f : E → ℝ) (g : E → E)
    (x : ℕ → E) (sigma : ℕ → ℝ) : Prop extends
    ParameterUpdates.RegularizationUpdates p (fun k => ratio f g (x k) (sigma k)) sigma where
  iterate : ∀ k, x (k + 1) = if p.eta1 ≤ ratio f g (x k) (sigma k)
    then trial g (x k) (sigma k) else x k

variable {p : Parameters} {f : E → ℝ} {g : E → E} {x : ℕ → E} {sigma : ℕ → ℝ}

/-- The floor in every update interval is preserved. -/
theorem IsRun.sigma_lower (h : IsRun p f g x sigma) (k : ℕ) : p.sigmaMin ≤ sigma k :=
  h.toRegularizationUpdates.lower k

/-- Every regularization parameter is positive. -/
theorem IsRun.sigma_pos (h : IsRun p f g x sigma) (k : ℕ) : 0 < sigma k :=
  p.sigmaMin_pos.trans_le (h.sigma_lower k)

/-- Successful and unsuccessful updates have the multiplicative bounds used for counting. -/
theorem IsRun.updateBounds (h : IsRun p f g x sigma) :
    ParameterUpdates.UpdateBounds sigma (fun k => p.eta1 ≤ ratio f g (x k) (sigma k))
      p.gamma1 p.gamma2 :=
  h.toRegularizationUpdates.updateBounds

/-- The model-independent logarithmic bound on total iterations. -/
theorem IsRun.total_count_le (h : IsRun p f g x sigma) (n : ℕ) {M : ℝ}
    (hM : sigma n ≤ M) :
    (n : ℝ) ≤ (ParameterUpdates.successCount
      (fun k => p.eta1 ≤ ratio f g (x k) (sigma k)) n : ℝ) *
      (1 + |Real.log p.gamma1| / Real.log p.gamma2) +
      Real.log (M / sigma 0) / Real.log p.gamma2 :=
  h.toRegularizationUpdates.total_count_le n hM

/-- An accepted step realizes its guaranteed fraction of the predicted reduction. -/
theorem IsRun.accepted_decrease (h : IsRun p f g x sigma) (k : ℕ)
    (hk : p.eta1 ≤ ratio f g (x k) (sigma k)) :
    p.eta1 * (‖g (x k)‖ ^ 2 / sigma k) ≤ f (x k) - f (x (k + 1)) := by
  classical
  rw [h.iterate k, ite_eq_left hk]
  by_cases hg : g (x k) = 0
  · simp [trial, hg]
  · rw [ratio, ite_eq_right hg] at hk
    exact (le_div_iff₀ (div_pos (sq_pos_of_pos (norm_pos_iff.mpr hg))
      (h.sigma_pos k))).mp hk

/-- Rejected trials leave the objective unchanged, and accepted trials never increase it. -/
theorem IsRun.objective_nonincrease (h : IsRun p f g x sigma) (k : ℕ) :
    f (x (k + 1)) ≤ f (x k) := by
  classical
  by_cases hk : p.eta1 ≤ ratio f g (x k) (sigma k)
  · have hd := h.accepted_decrease k hk
    have hn : 0 ≤ p.eta1 * (‖g (x k)‖ ^ 2 / sigma k) :=
      mul_nonneg p.eta1_pos.le (div_nonneg (sq_nonneg _) (h.sigma_pos k).le)
    linarith
  · rw [h.iterate k, ite_eq_right hk]

/-- A finite prefix that has not passed the gradient test has a bounded successful count. -/
theorem IsRun.success_count_le (h : IsRun p f g x sigma) {n : ℕ} {low M epsilon : ℝ}
    (he : 0 < epsilon) (hlow : low ≤ f (x n)) (hM : ∀ k < n, sigma k ≤ M)
    (hMp : 0 < M) (htest : ∀ k < n, epsilon < ‖g (x k)‖) :
    (ParameterUpdates.successCount (fun k => p.eta1 ≤ ratio f g (x k) (sigma k)) n : ℝ) ≤
      (f (x 0) - low) / (p.eta1 * (epsilon ^ 2 / M)) := by
  classical
  have hd : 0 < p.eta1 * (epsilon ^ 2 / M) :=
    mul_pos p.eta1_pos (div_pos (sq_pos_of_pos he) hMp)
  apply (le_div_iff₀ hd).mpr
  unfold ParameterUpdates.successCount
  apply EvaluationComplexity.card_mul_le_gap (u := fun k => f (x k))
    (Finset.filter_subset _ _) hlow (fun k _ => h.objective_nonincrease k)
  intro k hk
  obtain ⟨hkn, hks⟩ := Finset.mem_filter.mp hk
  have hkn' := Finset.mem_range.mp hkn
  have hsq : epsilon ^ 2 ≤ ‖g (x k)‖ ^ 2 := by nlinarith [htest k hkn']
  exact (mul_le_mul_of_nonneg_left
    (div_le_div₀ (sq_nonneg _) hsq (h.sigma_pos k) (hM k hkn')) p.eta1_pos.le).trans
    (h.accepted_decrease k hks)

/-- Combining successful decrease and update counting bounds every unterminated prefix. -/
theorem IsRun.prefix_count_le (h : IsRun p f g x sigma) {n : ℕ} {low M epsilon : ℝ}
    (he : 0 < epsilon) (hlow : low ≤ f (x n)) (hM : ∀ k ≤ n, sigma k ≤ M)
    (htest : ∀ k < n, epsilon < ‖g (x k)‖) :
    (n : ℝ) ≤ (f (x 0) - low) / (p.eta1 * (epsilon ^ 2 / M)) *
      (1 + |Real.log p.gamma1| / Real.log p.gamma2) +
      Real.log (M / sigma 0) / Real.log p.gamma2 := by
  have hMp : 0 < M := (h.sigma_pos 0).trans_le (hM 0 (Nat.zero_le _))
  have hlog : 0 < Real.log p.gamma2 := Real.log_pos p.one_lt_gamma2
  have hC : 0 ≤ 1 + |Real.log p.gamma1| / Real.log p.gamma2 :=
    add_nonneg zero_le_one (div_nonneg (abs_nonneg _) hlog.le)
  have hc := mul_le_mul_of_nonneg_right
    (h.success_count_le he hlow (fun k hk => hM k hk.le) hMp htest) hC
  linarith [h.total_count_le n (hM n le_rfl)]

/-- The first successful gradient test occurs within the total iteration budget. Function
values cost one initialization plus one trial per iteration; gradients cost one initialization
plus one computation per accepted trial. -/
theorem IsRun.exists_stationary_with_cost (h : IsRun p f g x sigma)
    {low M epsilon : ℝ} (he : 0 < epsilon) (hlow : ∀ y, low ≤ f y)
    (hM : ∀ k, sigma k ≤ M) :
    ∃ K : ℕ, ‖g (x K)‖ ≤ epsilon ∧ (∀ j < K, epsilon < ‖g (x j)‖) ∧
      (K : ℝ) + 1 ≤ (f (x 0) - low) / (p.eta1 * (epsilon ^ 2 / M)) *
        (1 + |Real.log p.gamma1| / Real.log p.gamma2) +
        Real.log (M / sigma 0) / Real.log p.gamma2 + 1 ∧
      (ParameterUpdates.successCount
        (fun k => p.eta1 ≤ ratio f g (x k) (sigma k)) K : ℝ) + 1 ≤
        (f (x 0) - low) / (p.eta1 * (epsilon ^ 2 / M)) + 1 := by
  classical
  obtain ⟨K, _, hk, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound
    (P := fun k => ‖g (x k)‖ ≤ epsilon)
    (fun n hn => h.prefix_count_le he (hlow _) (fun k _ => hM k)
      (fun j hj => lt_of_not_ge (hn j hj)))
  have htest : ∀ j < K, epsilon < ‖g (x j)‖ := fun j hj => lt_of_not_ge (hfirst j hj)
  refine ⟨K, hk, htest, ?_, ?_⟩
  · linarith [h.prefix_count_le he (hlow (x K)) (fun k _ => hM k) htest]
  · have hMp := (h.sigma_pos 0).trans_le (hM 0)
    linarith [h.success_count_le he (hlow (x K)) (fun k _ => hM k) hMp htest]

/-- A deterministic legal choice from the update intervals. -/
def nextSigma (p : Parameters) (rho sigma : ℝ) : ℝ :=
  if p.eta2 ≤ rho then max p.sigmaMin (p.gamma1 * sigma)
  else if p.eta1 ≤ rho then sigma else p.gamma2 * sigma

/-- The deterministic choice preserves the positive parameter floor. -/
theorem nextSigma_lower (p : Parameters) (rho : ℝ) {sigma : ℝ}
    (hs : p.sigmaMin ≤ sigma) : p.sigmaMin ≤ nextSigma p rho sigma := by
  unfold nextSigma
  split_ifs
  · exact le_max_left _ _
  · exact hs
  · exact hs.trans (le_mul_of_one_le_left (p.sigmaMin_pos.le.trans hs)
      p.one_lt_gamma2.le)

/-- The deterministic choice belongs to the prescribed update interval. -/
theorem nextSigma_mem (p : Parameters) (rho : ℝ) {sigma : ℝ}
    (hs : p.sigmaMin ≤ sigma) :
    if p.eta2 ≤ rho then
      nextSigma p rho sigma ∈ Set.Icc (max p.sigmaMin (p.gamma1 * sigma)) sigma
    else if p.eta1 ≤ rho then
      nextSigma p rho sigma ∈ Set.Icc sigma (p.gamma2 * sigma)
    else nextSigma p rho sigma ∈ Set.Icc (p.gamma2 * sigma) (p.gamma3 * sigma) := by
  have hp := p.sigmaMin_pos.le.trans hs
  unfold nextSigma
  split_ifs
  · exact ⟨le_rfl, max_le hs (mul_le_of_le_one_left hp p.gamma1_lt_one.le)⟩
  · exact ⟨le_rfl, le_mul_of_one_le_left hp p.one_lt_gamma2.le⟩
  · exact ⟨le_rfl, mul_le_mul_of_nonneg_right p.gamma2_lt_gamma3.le hp⟩

/-- An explicit infinite continuation, truncated by the desired gradient test. -/
def states (p : Parameters) (f : E → ℝ) (g : E → E) (x0 : E) (sigma0 : ℝ) :
    ℕ → E × ℝ
  | 0 => (x0, sigma0)
  | k + 1 =>
    let z := states p f g x0 sigma0 k
    let r := ratio f g z.1 z.2
    (if p.eta1 ≤ r then trial g z.1 z.2 else z.1, nextSigma p r z.2)

/-- Explicit initialization. -/
@[simp] theorem states_zero (p : Parameters) (f : E → ℝ) (g : E → E) (x0 : E)
    (sigma0 : ℝ) : states p f g x0 sigma0 0 = (x0, sigma0) := rfl

/-- The explicit construction has the required parameter floor. -/
theorem states_sigma_lower (p : Parameters) (f : E → ℝ) (g : E → E) (x0 : E)
    {sigma0 : ℝ} (hs : p.sigmaMin ≤ sigma0) (k : ℕ) :
    p.sigmaMin ≤ (states p f g x0 sigma0 k).2 := by
  induction k with
  | zero => exact hs
  | succ k ih => exact nextSigma_lower p _ ih

/-- In particular lawful-run hypotheses are inhabited by a concrete algorithm. -/
theorem states_isRun (p : Parameters) (f : E → ℝ) (g : E → E) (x0 : E)
    {sigma0 : ℝ} (hs : p.sigmaMin ≤ sigma0) :
    IsRun p f g (fun k => (states p f g x0 sigma0 k).1)
      (fun k => (states p f g x0 sigma0 k).2) where
  initial_lower := hs
  iterate _ := rfl
  update k := nextSigma_mem p _ (states_sigma_lower p f g x0 hs k)

end Normed

section InnerProduct
variable [InnerProductSpace ℝ E]
variable {p : Parameters} {f : E → ℝ} {g : E → E} {x : ℕ → E} {sigma : ℕ → ℝ}

/-- A large regularization parameter guarantees a very successful trial. -/
theorem ratio_ge_of_sigma_ge {L sigma : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLp : 0 < L)
    (hs : 0 < sigma) (x : E) (hb : L / (2 * (1 - p.eta2)) ≤ sigma) :
    p.eta2 ≤ ratio f g x sigma := by
  classical
  by_cases hg : g x = 0
  · simp [ratio, hg, p.eta2_lt_one.le]
  have hden : 0 < 2 * (1 - p.eta2) := by linarith [p.eta2_lt_one]
  have hb' := (div_le_iff₀ hden).mp hb
  have ht : sigma⁻¹ ≤ 2 * (1 - p.eta2) / L := by
    apply (le_div_iff₀ hLp).mpr
    apply (inv_mul_le_iff₀ hs).mpr
    nlinarith
  have ha := SmoothDescent.armijo_of_step_le hf hL hLp x (inv_pos.mpr hs).le ht
  have hsq : 0 < ‖g x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hg)
  rw [ratio, ite_eq_right hg, le_div_iff₀ (div_pos hsq hs)]
  simp only [LineSearch.Armijo, map_neg, innerSL_apply_apply,
    real_inner_self_eq_norm_sq, smul_neg, ← sub_eq_add_neg] at ha
  change p.eta2 * (‖g x‖ ^ 2 / sigma) ≤ f x - f (x - sigma⁻¹ • g x)
  rw [div_eq_mul_inv]
  nlinarith [ha]

/-- Lipschitz gradients impose a uniform upper bound on all regularization parameters. -/
theorem IsRun.sigma_upper (h : IsRun p f g x sigma) {L : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLp : 0 < L) (n : ℕ) :
    sigma n ≤ max (sigma 0) (p.gamma3 * (L / (2 * (1 - p.eta2)))) := by
  apply h.toRegularizationUpdates.upper
  intro k hk
  exact ratio_ge_of_sigma_ge hf hL hLp (h.sigma_pos k) (x k) hk

end InnerProduct

end Optimization.FirstOrderRegularization
