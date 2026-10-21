import Numlib.Optimization.HigherOrderRegularizationRun
import Numlib.Optimization.HigherOrderRegularizationBounds
import Numlib.Optimization.AdaptiveRegularizationComplexity

/-!
# Evaluation complexity on finite higher-order regularization prefixes

Successful trials whose successors fail a criticality test pay a fixed positive objective
decrease. Legal finite prefixes therefore yield evaluation budgets, first stops at orders
one and two, and restricted third-order iterate quality.
-/

noncomputable section
namespace Optimization.HigherOrderRegularization
open ParameterUpdates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {params : RegularizationParameters} {degree N : ℕ} {f : E → ℝ}
    {x s : ℕ → E} {sigma : ℕ → ℝ} {P : ℕ → Prop} {delta low : ℝ}

/-- Failed successor tests bound all successful trials except possibly the last one. -/
theorem TrialPrefix.success_count_le (h : TrialPrefix params degree f x s sigma N)
    (hd : 0 < delta) (hlow : ∀ k ≤ N, low ≤ f (x k))
    (hdec : ∀ k < N, params.eta1 ≤ ratio f degree (x k) (s k) →
      ¬P (k + 1) → delta ≤ f (x k) - f (x (k + 1)))
    (hfirst : ∀ k < N, ¬P k) :
    (successCount (fun k => params.eta1 ≤ ratio f degree (x k) (s k)) N : ℝ) ≤
      (f (x 0) - low) / delta + 1 := by
  classical
  cases N with
  | zero =>
    simp only [successCount, Finset.range_zero, Finset.filter_empty, Finset.card_empty,
      Nat.cast_zero]
    have := div_nonneg (sub_nonneg.mpr (hlow 0 le_rfl)) hd.le
    linarith
  | succ n =>
    have hb : (successCount (fun k => params.eta1 ≤ ratio f degree (x k) (s k)) n : ℝ) ≤
        (f (x 0) - low) / delta := by
      apply (le_div_iff₀ hd).mpr
      unfold successCount
      apply EvaluationComplexity.card_mul_le_gap (u := fun k => f (x k))
        (n := n)
        (Finset.filter_subset _ (Finset.range n)) (hlow n (by omega))
        (fun k hk => h.objective_nonincrease (by omega))
      intro k hk
      have hkn := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      exact hdec k (by omega) (Finset.mem_filter.mp hk).2 (hfirst (k + 1) (by omega))
    have hc : (successCount (fun k => params.eta1 ≤ ratio f degree (x k) (s k))
        (n + 1) : ℝ) ≤
        (successCount (fun k => params.eta1 ≤ ratio f degree (x k) (s k)) n : ℝ) + 1 := by
      exact_mod_cast successCount_succ_le
        (fun k => params.eta1 ≤ ratio f degree (x k) (s k)) n
    linarith

/-- Actual finite trials have one initial objective call and cached derivative calls. -/
theorem TrialPrefix.evaluation_bounds (h : TrialPrefix params degree f x s sigma N)
    {L : ℝ} (hf : DiagonalLipschitz f degree L) (hp : 1 ≤ degree)
    (hd : 0 < delta) (hlow : ∀ k ≤ N, low ≤ f (x k))
    (hdec : ∀ k < N, params.eta1 ≤ ratio f degree (x k) (s k) →
      ¬P (k + 1) → delta ≤ f (x k) - f (x (k + 1)))
    (hfirst : ∀ k < N, ¬P k) :
    let M := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (M / sigma 0) / Real.log params.gamma2
    (functionEvaluations N : ℝ) ≤ C * ((f (x 0) - low) / delta) + C + D + 1 ∧
      (derivativeEvaluations params degree f x s N : ℝ) ≤ (f (x 0) - low) / delta + 2 := by
  dsimp only
  have hC : 0 ≤ 1 + |Real.log params.gamma1| / Real.log params.gamma2 :=
    add_nonneg zero_le_one
      (div_nonneg (abs_nonneg _) (Real.log_pos params.one_lt_gamma2).le)
  have hs := h.success_count_le hd hlow hdec hfirst
  have ht := h.toRegularizationPrefix.total_count_le le_rfl (h.sigma_upper hf hp le_rfl)
  have hm := mul_le_mul_of_nonneg_right hs hC
  simp only [functionEvaluations, derivativeEvaluations, Nat.cast_add, Nat.cast_one]
  constructor <;> linarith

/-- A finite prefix can always reach its first stopping test within the decrease budget,
provided legal trials are available whenever all preceding tests fail. -/
theorem exists_first_with_evaluation_bounds {L : ℝ}
    (hf : DiagonalLipschitz f degree L) (hp : 1 ≤ degree) (hd : 0 < delta)
    (hlow : ∀ y, low ≤ f y)
    (hprefix : ∀ N, (∀ k < N, ¬P k) → TrialPrefix params degree f x s sigma N)
    (hdec : ∀ N (_hfirst : ∀ k < N, ¬P k),
      ∀ k < N, params.eta1 ≤ ratio f degree (x k) (s k) →
        ¬P (k + 1) → delta ≤ f (x k) - f (x (k + 1))) :
    let M := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (M / sigma 0) / Real.log params.gamma2
    ∃ K : ℕ, P K ∧ (∀ k < K, ¬P k) ∧
      (functionEvaluations K : ℝ) ≤ C * ((f (x 0) - low) / delta) + C + D + 1 ∧
      (derivativeEvaluations params degree f x s K : ℝ) ≤ (f (x 0) - low) / delta + 2 := by
  dsimp only
  have hb : ∀ N, (∀ k < N, ¬P k) →
      (N : ℝ) ≤ (1 + |Real.log params.gamma1| / Real.log params.gamma2) *
        ((f (x 0) - low) / delta) +
        (1 + |Real.log params.gamma1| / Real.log params.gamma2) +
        Real.log (max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))) / sigma 0) /
          Real.log params.gamma2 + 1 := by
    intro N hn
    have h := hprefix N hn
    have hc := (h.evaluation_bounds hf hp hd (fun k _ => hlow (x k)) (hdec N hn) hn).1
    simp only [functionEvaluations, Nat.cast_add, Nat.cast_one] at hc
    linarith
  obtain ⟨K, _, hK, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound hb
  exact ⟨K, hK, hfirst,
    (hprefix K hfirst).evaluation_bounds hf hp hd (fun k _ => hlow (x k))
      (hdec K hfirst) hfirst⟩

section Inner
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Second-order termination is exactly simultaneous gradient and negative-curvature control. -/
theorem stationary_two_iff (epsilon : Fin 3 → ℝ) (he : 0 ≤ epsilon 1)
    (f : F → ℝ) (z : F) (D : Set F) :
    Stationary 2 epsilon f z D ↔ ‖fderiv ℝ f z‖ ≤ epsilon 0 ∧
      max 0 (-leastCurvature (fderiv ℝ (fderiv ℝ f) z)) ≤ epsilon 1 := by
  constructor
  · intro h
    exact ⟨h.first, max_le he (by linarith [h.second (by decide) he])⟩
  · rintro ⟨hg, hH⟩
    have hc := (le_max_right 0 (-leastCurvature (fderiv ℝ (fderiv ℝ f) z))).trans hH
    exact ⟨hg, fun _ => Or.inr ⟨by linarith, by simp⟩⟩

/-- With no current model directions the third-order test can terminate only through the
strict positive-curvature branch. -/
theorem stationary_three_empty_iff (epsilon : Fin 3 → ℝ) (f : F → ℝ) (z : F) :
    Stationary 3 epsilon f z ∅ ↔ ‖fderiv ℝ f z‖ ≤ epsilon 0 ∧
      epsilon 1 < leastCurvature (fderiv ℝ (fderiv ℝ f) z) := by
  simp [Stationary]

/-- A nonempty objective flat-direction set need not repair an empty model-direction stop:
any objective curvature at or below its positive threshold still fails the exact test. -/
theorem not_stationary_three_empty {epsilon : Fin 3 → ℝ} {f : F → ℝ} {z : F}
    (hcurv : leastCurvature (fderiv ℝ (fderiv ℝ f) z) ≤ epsilon 1) :
    ¬Stationary 3 epsilon f z ∅ := by
  rw [stationary_three_empty_iff]
  exact fun h => (not_lt_of_ge hcurv) h.2

end Inner

section FiniteDimensional
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
variable {params : RegularizationParameters} {p N : ℕ} {theta epsilon : Fin 3 → ℝ}
    {f : F → ℝ} {x s : ℕ → F} {sigma : ℕ → ℝ} {L low : ℝ}

/-- Third-order iterate quality on the current model directions, allowing an empty set.
This certifies an iterate's derivatives; it does not assert the algorithm's stopping test. -/
def ThirdOrderQualityTest (epsilon : Fin 3 → ℝ) (f : F → ℝ) (z : F) (D : Set F) : Prop :=
  ‖fderiv ℝ f z‖ ≤ epsilon 0 ∧
    (epsilon 1 < leastCurvature (fderiv ℝ (fderiv ℝ f) z) ∨
      (-epsilon 1 ≤ leastCurvature (fderiv ℝ (fderiv ℝ f) z) ∧ ∀ d ∈ D,
        |iteratedFDeriv ℝ 3 f z (fun _ => d)| ≤ epsilon 2 ∧
        |iteratedFDeriv ℝ 2 f z (fun _ => d)| ≤ epsilon 1))

omit [FiniteDimensional ℝ F] in
/-- Exact third-order stopping implies the weaker derivative-quality test. -/
theorem Stationary.toThirdOrderQualityTest {epsilon : Fin 3 → ℝ} {f : F → ℝ}
    {z : F} {D : Set F} (h : Stationary 3 epsilon f z D) :
    ThirdOrderQualityTest epsilon f z D := by
  refine ⟨h.first, ?_⟩
  rcases h.2 (by decide) with hs | hs
  · exact Or.inl hs
  · exact Or.inr ⟨hs.1, ((hs.2 (by decide)).2)⟩

omit [FiniteDimensional ℝ F] in
/-- At strict positive curvature choose the empty certified set; otherwise certify exactly
the current model directions, including the possibility that they are empty. -/
theorem ThirdOrderQualityTest.certificate {epsilon : Fin 3 → ℝ} {f : F → ℝ}
    {z : F} {D : Set F} (h : ThirdOrderQualityTest epsilon f z D)
    (he : 0 ≤ epsilon 1) (hunit : ∀ d ∈ D, ‖d‖ = 1) :
    ∃ M : Set F,
      M = (if epsilon 1 < leastCurvature (fderiv ℝ (fderiv ℝ f) z) then ∅ else D) ∧
      ‖fderiv ℝ f z‖ ≤ epsilon 0 ∧
      -epsilon 1 ≤ leastCurvature (fderiv ℝ (fderiv ℝ f) z) ∧
      (∀ d ∈ M, |iteratedFDeriv ℝ 3 f z (fun _ => d)| ≤ epsilon 2) ∧
      M ⊆ smallCurvatureDirections f z (epsilon 1) := by
  by_cases hs : epsilon 1 < leastCurvature (fderiv ℝ (fderiv ℝ f) z)
  · exact ⟨∅, by simp [hs], h.1, by linarith, by simp, Set.empty_subset _⟩
  · have hD := h.2.resolve_left hs
    exact ⟨D, by simp [hs], h.1, hD.1, fun d hd => (hD.2 d hd).1,
      fun d hd => ⟨hunit d hd, (hD.2 d hd).2⟩⟩

omit [FiniteDimensional ℝ F] in
/-- Every current direction of a run has unit norm, at initialization and after trials. -/
theorem directionSequence_unit (p : ℕ) (theta2 epsilon2 : ℝ) (f : F → ℝ)
    (x s : ℕ → F) (sigma : ℕ → ℝ) (k : ℕ) {d : F}
    (hd : d ∈ directionSequence p theta2 epsilon2 f x s sigma k) : ‖d‖ = 1 := by
  cases k <;> exact hd.1

/-- The first-order inverse decrease coefficient depends only on model and algorithm data. -/
def firstOrderComplexityConstant (params : RegularizationParameters) (p : ℕ)
    (L S theta1 : ℝ) : ℝ := (decreaseConstant params p 1 L S theta1)⁻¹

/-- The joint inverse decrease coefficient is independent of the requested tolerances. -/
def secondOrderComplexityConstant (params : RegularizationParameters) (p : ℕ)
    (L S theta1 theta2 : ℝ) : ℝ :=
  (min (decreaseConstant params p 1 L S theta1)
    (decreaseConstant params p 2 L S theta2))⁻¹

/-- The third-order quality coefficient is fixed independently of all three tolerances. -/
def thirdOrderComplexityConstant (params : RegularizationParameters) (p : ℕ)
    (L S : ℝ) (theta : Fin 3 → ℝ) : ℝ :=
  (min (decreaseConstant params p 1 L S (theta 0))
    (min (decreaseConstant params p 2 L S (theta 1))
      (decreaseConstant params p 3 L S (theta 2))))⁻¹

/-- The first-order complexity coefficient is positive under the model data bounds. -/
theorem firstOrderComplexityConstant_pos (params : RegularizationParameters) (p : ℕ)
    {L S theta1 : ℝ} (hL : 0 ≤ L) (hS : 0 ≤ S) (htheta1 : 0 < theta1) :
    0 < firstOrderComplexityConstant params p L S theta1 :=
  inv_pos.mpr (decreaseConstant_pos params p 1 hL hS htheta1)

/-- The second-order complexity coefficient is positive independently of the tolerances. -/
theorem secondOrderComplexityConstant_pos (params : RegularizationParameters) (p : ℕ)
    {L S theta1 theta2 : ℝ} (hL : 0 ≤ L) (hS : 0 ≤ S)
    (htheta1 : 0 < theta1) (htheta2 : 0 < theta2) :
    0 < secondOrderComplexityConstant params p L S theta1 theta2 :=
  inv_pos.mpr (lt_min (decreaseConstant_pos params p 1 hL hS htheta1)
    (decreaseConstant_pos params p 2 hL hS htheta2))

/-- The three-order complexity coefficient is positive independently of the tolerances. -/
theorem thirdOrderComplexityConstant_pos (params : RegularizationParameters) (p : ℕ)
    {L S : ℝ} {theta : Fin 3 → ℝ} (hL : 0 ≤ L) (hS : 0 ≤ S)
    (htheta : ∀ i, 0 < theta i) :
    0 < thirdOrderComplexityConstant params p L S theta :=
  inv_pos.mpr (lt_min (decreaseConstant_pos params p 1 hL hS (htheta 0))
    (lt_min (decreaseConstant_pos params p 2 hL hS (htheta 1))
      (decreaseConstant_pos params p 3 hL hS (htheta 2))))

/-- First-order failed tests give the natural real-power decrease budget on finite prefixes. -/
theorem RunPrefix.first_order_evaluation_bounds
    (h : RunPrefix params 1 p theta epsilon f x s sigma N)
    (hf : DiagonalLipschitz f p L) (hlow : ∀ k ≤ N, low ≤ f (x k))
    (hfirst : ∀ k < N, ¬Stationary 1 epsilon f (x k)
      (directionSequence p (theta 1) (epsilon 1) f x s sigma k)) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := firstOrderComplexityConstant params p L S (theta 0) *
      ((f (x 0) - low) / (epsilon 0) ^ (((p + 1 : ℕ) : ℝ) / p))
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (S / sigma 0) / Real.log params.gamma2
    (functionEvaluations N : ℝ) ≤ C * Q + C + D + 1 ∧
      (derivativeEvaluations params p f x s N : ℝ) ≤ Q + 2 := by
  dsimp only
  let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
  let K := decreaseConstant params p 1 L S (theta 0)
  have hp : 1 ≤ p := h.degree_ge_order
  have he : 0 < epsilon 0 := h.epsilon_pos 0 (by decide)
  have hS : 0 ≤ S :=
    (h.toTrialPrefix.toRegularizationPrefix.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  have hK : 0 < K := decreaseConstant_pos params p 1 hf.nonneg hS (h.theta_pos 0)
  have hdelta : 0 < K * (epsilon 0) ^ (((p + 1 : ℕ) : ℝ) / p) :=
    mul_pos hK (Real.rpow_pos_of_pos he _)
  have hdec : ∀ k < N, params.eta1 ≤ ratio f p (x k) (s k) →
      ¬Stationary 1 epsilon f (x (k + 1))
        (directionSequence p (theta 1) (epsilon 1) f x s sigma (k + 1)) →
      K * (epsilon 0) ^ (((p + 1 : ℕ) : ℝ) / p) ≤ f (x k) - f (x (k + 1)) := by
    intro k hk hs hnot
    have hg : epsilon 0 ≤ ‖fderiv ℝ f (x (k + 1))‖ :=
      (lt_of_not_ge (by simpa only [stationary_one_iff] using hnot)).le
    have hd := h.gradient_decrease hf hk hs (h.toTrialPrefix.sigma_upper hf hp (by omega))
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow he.le hg (by positivity)) hK.le).trans hd
  have hb := h.toTrialPrefix.evaluation_bounds hf hp hdelta hlow hdec hfirst
  have hid : (f (x 0) - low) / (K * (epsilon 0) ^ (((p + 1 : ℕ) : ℝ) / p)) =
      firstOrderComplexityConstant params p L S (theta 0) *
        ((f (x 0) - low) / (epsilon 0) ^ (((p + 1 : ℕ) : ℝ) / p)) := by
    simp only [firstOrderComplexityConstant, K, div_eq_mul_inv, mul_inv_rev]
    ring
  simpa only [hid] using hb

/-- Joint first- and second-order failed tests give the minimum of their natural powers. -/
theorem RunPrefix.second_order_evaluation_bounds [Nontrivial F]
    (h : RunPrefix params 2 p theta epsilon f x s sigma N)
    (hf : DiagonalLipschitz f p L) (hlow : ∀ k ≤ N, low ≤ f (x k))
    (hfirst : ∀ k < N, ¬Stationary 2 epsilon f (x k)
      (directionSequence p (theta 1) (epsilon 1) f x s sigma k)) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := secondOrderComplexityConstant params p L S (theta 0) (theta 1) *
      ((f (x 0) - low) / min ((epsilon 0) ^ (((p + 1 : ℕ) : ℝ) / p))
        ((epsilon 1) ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ))))
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (S / sigma 0) / Real.log params.gamma2
    (functionEvaluations N : ℝ) ≤ C * Q + C + D + 1 ∧
      (derivativeEvaluations params p f x s N : ℝ) ≤ Q + 2 := by
  dsimp only
  let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
  let K1 := decreaseConstant params p 1 L S (theta 0)
  let K2 := decreaseConstant params p 2 L S (theta 1)
  let A := (epsilon 0) ^ (((p + 1 : ℕ) : ℝ) / p)
  let B := (epsilon 1) ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ))
  have hp : 1 ≤ p := by have := h.degree_ge_order; omega
  have he1 : 0 < epsilon 0 := h.epsilon_pos 0 (by decide)
  have he2 : 0 < epsilon 1 := h.epsilon_pos 1 (by decide)
  have hS : 0 ≤ S :=
    (h.toTrialPrefix.toRegularizationPrefix.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  have hK1 : 0 < K1 := decreaseConstant_pos params p 1 hf.nonneg hS (h.theta_pos 0)
  have hK2 : 0 < K2 := decreaseConstant_pos params p 2 hf.nonneg hS (h.theta_pos 1)
  have hA : 0 < A := Real.rpow_pos_of_pos he1 _
  have hB : 0 < B := Real.rpow_pos_of_pos he2 _
  have hK : 0 < min K1 K2 := lt_min hK1 hK2
  have hdelta : 0 < min K1 K2 * min A B := mul_pos hK (lt_min hA hB)
  have hdec : ∀ k < N, params.eta1 ≤ ratio f p (x k) (s k) →
      ¬Stationary 2 epsilon f (x (k + 1))
        (directionSequence p (theta 1) (epsilon 1) f x s sigma (k + 1)) →
      min K1 K2 * min A B ≤ f (x k) - f (x (k + 1)) := by
    intro k hk hs hnot
    have hsigma := h.toTrialPrefix.sigma_upper hf hp (by omega : k ≤ N)
    by_cases hg : ‖fderiv ℝ f (x (k + 1))‖ ≤ epsilon 0
    · have hc : epsilon 1 ≤ max 0 (-leastCurvature
          (fderiv ℝ (fderiv ℝ f) (x (k + 1)))) := by
        by_contra! hc
        exact hnot ((stationary_two_iff epsilon he2.le _ _ _).mpr ⟨hg, hc.le⟩)
      calc
        _ ≤ K2 * B := mul_le_mul (min_le_right _ _) (min_le_right _ _)
          (le_of_lt (lt_min hA hB)) hK2.le
        _ ≤ K2 * (max 0 (-leastCurvature (fderiv ℝ (fderiv ℝ f) (x (k + 1))))) ^
            (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow he2.le hc (by positivity)) hK2.le
        _ ≤ _ := h.curvature_decrease hf (by decide) hk hs hsigma
    · calc
        _ ≤ K1 * A := mul_le_mul (min_le_left _ _) (min_le_left _ _)
          (le_of_lt (lt_min hA hB)) hK1.le
        _ ≤ K1 * ‖fderiv ℝ f (x (k + 1))‖ ^ (((p + 1 : ℕ) : ℝ) / p) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow he1.le (lt_of_not_ge hg).le (by positivity)) hK1.le
        _ ≤ _ := h.gradient_decrease hf hk hs hsigma
  have hb := h.toTrialPrefix.evaluation_bounds hf hp hdelta hlow hdec hfirst
  have hid : (f (x 0) - low) / (min K1 K2 * min A B) =
      secondOrderComplexityConstant params p L S (theta 0) (theta 1) *
        ((f (x 0) - low) / min A B) := by
    simp only [secondOrderComplexityConstant, K1, K2, div_eq_mul_inv, mul_inv_rev]
    ring
  simpa only [hid] using hb

/-- Third-order iterate quality has the full three-power evaluation budget on actual finite
prefixes. Empty current model directions satisfy the restricted tests vacuously. -/
theorem RunPrefix.third_order_quality_evaluation_bounds [Nontrivial F]
    (h : RunPrefix params 3 p theta epsilon f x s sigma N)
    (hf : DiagonalLipschitz f p L) (hlow : ∀ k ≤ N, low ≤ f (x k))
    (hfirst : ∀ k < N, ¬ThirdOrderQualityTest epsilon f (x k)
      (directionSequence p (theta 1) (epsilon 1) f x s sigma k)) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := thirdOrderComplexityConstant params p L S theta *
      ((f (x 0) - low) / min ((epsilon 0) ^ (((p + 1 : ℕ) : ℝ) / p))
        (min ((epsilon 1) ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)))
          ((epsilon 2) ^ (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)))))
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (S / sigma 0) / Real.log params.gamma2
    (functionEvaluations N : ℝ) ≤ C * Q + C + D + 1 ∧
      (derivativeEvaluations params p f x s N : ℝ) ≤ Q + 2 := by
  dsimp only
  let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
  let K1 := decreaseConstant params p 1 L S (theta 0)
  let K2 := decreaseConstant params p 2 L S (theta 1)
  let K3 := decreaseConstant params p 3 L S (theta 2)
  let A := (epsilon 0) ^ (((p + 1 : ℕ) : ℝ) / p)
  let B := (epsilon 1) ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ))
  let C := (epsilon 2) ^ (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ))
  let K := min K1 (min K2 K3)
  let T := min A (min B C)
  have hp : 1 ≤ p := by have := h.degree_ge_order; omega
  have he1 : 0 < epsilon 0 := h.epsilon_pos 0 (by decide)
  have he2 : 0 < epsilon 1 := h.epsilon_pos 1 (by decide)
  have he3 : 0 < epsilon 2 := h.epsilon_pos 2 (by decide)
  have hS : 0 ≤ S :=
    (h.toTrialPrefix.toRegularizationPrefix.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  have hK1 : 0 < K1 := decreaseConstant_pos params p 1 hf.nonneg hS (h.theta_pos 0)
  have hK2 : 0 < K2 := decreaseConstant_pos params p 2 hf.nonneg hS (h.theta_pos 1)
  have hK3 : 0 < K3 := decreaseConstant_pos params p 3 hf.nonneg hS (h.theta_pos 2)
  have hA : 0 < A := Real.rpow_pos_of_pos he1 _
  have hB : 0 < B := Real.rpow_pos_of_pos he2 _
  have hC : 0 < C := Real.rpow_pos_of_pos he3 _
  have hK : 0 < K := lt_min hK1 (lt_min hK2 hK3)
  have hT : 0 < T := lt_min hA (lt_min hB hC)
  have hb1 : K * T ≤ K1 * A :=
    mul_le_mul (min_le_left _ _) (min_le_left _ _) hT.le hK1.le
  have hb2 : K * T ≤ K2 * B :=
    mul_le_mul ((min_le_right _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_left _ _)) hT.le hK2.le
  have hb3 : K * T ≤ K3 * C :=
    mul_le_mul ((min_le_right _ _).trans (min_le_right _ _))
      ((min_le_right _ _).trans (min_le_right _ _)) hT.le hK3.le
  have hdec : ∀ k < N, params.eta1 ≤ ratio f p (x k) (s k) →
      ¬ThirdOrderQualityTest epsilon f (x (k + 1))
        (directionSequence p (theta 1) (epsilon 1) f x s sigma (k + 1)) →
      K * T ≤ f (x k) - f (x (k + 1)) := by
    intro k hk hs hnot
    have hsigma := h.toTrialPrefix.sigma_upper hf hp (by omega : k ≤ N)
    by_cases hg : ‖fderiv ℝ f (x (k + 1))‖ ≤ epsilon 0
    · by_cases hc : -epsilon 1 ≤ leastCurvature (fderiv ℝ (fderiv ℝ f) (x (k + 1)))
      · have hdirs : ¬∀ d ∈ directionSequence p (theta 1) (epsilon 1) f x s sigma (k + 1),
            |iteratedFDeriv ℝ 3 f (x (k + 1)) (fun _ => d)| ≤ epsilon 2 ∧
            |iteratedFDeriv ℝ 2 f (x (k + 1)) (fun _ => d)| ≤ epsilon 1 :=
          fun hd => hnot ⟨hg, Or.inr ⟨hc, hd⟩⟩
        push Not at hdirs
        obtain ⟨d, hd, hbad⟩ := hdirs
        by_cases hthird : |iteratedFDeriv ℝ 3 f (x (k + 1)) (fun _ => d)| ≤ epsilon 2
        · have hh : epsilon 1 ≤ |iteratedFDeriv ℝ 2 f (x (k + 1)) (fun _ => d)| :=
            (hbad hthird).le
          exact hb2.trans ((mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow he2.le hh (by positivity)) hK2.le).trans
              (h.flat_hessian_decrease hf (by decide) hk hs hsigma hd))
        · exact hb3.trans ((mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow he3.le (lt_of_not_ge hthird).le (by positivity)) hK3.le).trans
              (h.cubic_decrease hf (by decide) hk hs hsigma hd))
      · have hn : epsilon 1 ≤ max 0 (-leastCurvature
            (fderiv ℝ (fderiv ℝ f) (x (k + 1)))) := by
          have hm := le_max_right 0 (-leastCurvature (fderiv ℝ (fderiv ℝ f) (x (k + 1))))
          linarith
        exact hb2.trans ((mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow he2.le hn (by positivity)) hK2.le).trans
            (h.curvature_decrease hf (by decide) hk hs hsigma))
    · exact hb1.trans ((mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow he1.le (lt_of_not_ge hg).le (by positivity)) hK1.le).trans
          (h.gradient_decrease hf hk hs hsigma))
  have hb := h.toTrialPrefix.evaluation_bounds hf hp (mul_pos hK hT) hlow hdec hfirst
  have hid : (f (x 0) - low) / (K * T) =
      thirdOrderComplexityConstant params p L S theta * ((f (x 0) - low) / T) := by
    simp only [thirdOrderComplexityConstant, K, K1, K2, K3, div_eq_mul_inv, mul_inv_rev]
    ring
  simpa only [hid] using hb

/-- Legal first-order trials, supplied only while tests fail, force a first stopping index
with the natural higher-order evaluation budget. -/
theorem exists_first_order_run_with_cost
    (hf : DiagonalLipschitz f p L) (hlow : ∀ y, low ≤ f y)
    (hprefix : ∀ N, (∀ k < N, ¬Stationary 1 epsilon f (x k)
      (directionSequence p (theta 1) (epsilon 1) f x s sigma k)) →
      RunPrefix params 1 p theta epsilon f x s sigma N) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := firstOrderComplexityConstant params p L S (theta 0) *
      ((f (x 0) - low) / (epsilon 0) ^ (((p + 1 : ℕ) : ℝ) / p))
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (S / sigma 0) / Real.log params.gamma2
    ∃ K, IsRun params 1 p theta epsilon f x s sigma K ∧
      (functionEvaluations K : ℝ) ≤ C * Q + C + D + 1 ∧
      (derivativeEvaluations params p f x s K : ℝ) ≤ Q + 2 := by
  dsimp only
  let P := fun k => Stationary 1 epsilon f (x k)
    (directionSequence p (theta 1) (epsilon 1) f x s sigma k)
  have hb : ∀ N, (∀ k < N, ¬P k) → (N : ℝ) ≤
      (1 + |Real.log params.gamma1| / Real.log params.gamma2) *
        (firstOrderComplexityConstant params p L
          (max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))) (theta 0) *
          ((f (x 0) - low) / (epsilon 0) ^ (((p + 1 : ℕ) : ℝ) / p))) +
        (1 + |Real.log params.gamma1| / Real.log params.gamma2) +
        Real.log (max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))) / sigma 0) /
          Real.log params.gamma2 + 1 := by
    intro N hn
    have hc := ((hprefix N hn).first_order_evaluation_bounds hf
      (fun k _ => hlow (x k)) hn).1
    exact (by simp [functionEvaluations] : (N : ℝ) ≤ (functionEvaluations N : ℝ)).trans hc
  obtain ⟨K, _, hK, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound hb
  exact ⟨K, ⟨hprefix K hfirst, hK, hfirst⟩,
    (hprefix K hfirst).first_order_evaluation_bounds hf (fun k _ => hlow (x k)) hfirst⟩

/-- Legal second-order trials force first termination with simultaneous gradient and
curvature tolerances and cached derivative cost at most the decrease budget plus two. -/
theorem exists_second_order_run_with_cost [Nontrivial F]
    (hf : DiagonalLipschitz f p L) (hlow : ∀ y, low ≤ f y)
    (hprefix : ∀ N, (∀ k < N, ¬Stationary 2 epsilon f (x k)
      (directionSequence p (theta 1) (epsilon 1) f x s sigma k)) →
      RunPrefix params 2 p theta epsilon f x s sigma N) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := secondOrderComplexityConstant params p L S (theta 0) (theta 1) *
      ((f (x 0) - low) / min ((epsilon 0) ^ (((p + 1 : ℕ) : ℝ) / p))
        ((epsilon 1) ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ))))
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (S / sigma 0) / Real.log params.gamma2
    ∃ K, IsRun params 2 p theta epsilon f x s sigma K ∧
      (functionEvaluations K : ℝ) ≤ C * Q + C + D + 1 ∧
      (derivativeEvaluations params p f x s K : ℝ) ≤ Q + 2 := by
  dsimp only
  let P := fun k => Stationary 2 epsilon f (x k)
    (directionSequence p (theta 1) (epsilon 1) f x s sigma k)
  have hb : ∀ N, (∀ k < N, ¬P k) → (N : ℝ) ≤
      (1 + |Real.log params.gamma1| / Real.log params.gamma2) *
        (secondOrderComplexityConstant params p L
          (max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))) (theta 0) (theta 1) *
          ((f (x 0) - low) / min ((epsilon 0) ^ (((p + 1 : ℕ) : ℝ) / p))
            ((epsilon 1) ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ))))) +
        (1 + |Real.log params.gamma1| / Real.log params.gamma2) +
        Real.log (max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))) / sigma 0) /
          Real.log params.gamma2 + 1 := by
    intro N hn
    have hc := ((hprefix N hn).second_order_evaluation_bounds hf
      (fun k _ => hlow (x k)) hn).1
    exact (by simp [functionEvaluations] : (N : ℝ) ≤ (functionEvaluations N : ℝ)).trans hc
  obtain ⟨K, _, hK, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound hb
  exact ⟨K, ⟨hprefix K hfirst, hK, hfirst⟩,
    (hprefix K hfirst).second_order_evaluation_bounds hf (fun k _ => hlow (x k)) hfirst⟩

/-- Legal trials force an iterate meeting the restricted third-order quality tests with the
full three-power bound. This conclusion deliberately contains no third-order stopping claim. -/
theorem exists_third_order_quality_with_cost [Nontrivial F]
    (hf : DiagonalLipschitz f p L) (hlow : ∀ y, low ≤ f y)
    (hprefix : ∀ N, (∀ k < N, ¬ThirdOrderQualityTest epsilon f (x k)
      (directionSequence p (theta 1) (epsilon 1) f x s sigma k)) →
      RunPrefix params 3 p theta epsilon f x s sigma N) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := thirdOrderComplexityConstant params p L S theta *
      ((f (x 0) - low) / min ((epsilon 0) ^ (((p + 1 : ℕ) : ℝ) / p))
        (min ((epsilon 1) ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)))
          ((epsilon 2) ^ (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)))))
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (S / sigma 0) / Real.log params.gamma2
    ∃ K, RunPrefix params 3 p theta epsilon f x s sigma K ∧
      ThirdOrderQualityTest epsilon f (x K)
        (directionSequence p (theta 1) (epsilon 1) f x s sigma K) ∧
      (∀ k < K, ¬ThirdOrderQualityTest epsilon f (x k)
        (directionSequence p (theta 1) (epsilon 1) f x s sigma k)) ∧
      (functionEvaluations K : ℝ) ≤ C * Q + C + D + 1 ∧
      (derivativeEvaluations params p f x s K : ℝ) ≤ Q + 2 := by
  dsimp only
  let P := fun k => ThirdOrderQualityTest epsilon f (x k)
    (directionSequence p (theta 1) (epsilon 1) f x s sigma k)
  have hb : ∀ N, (∀ k < N, ¬P k) → (N : ℝ) ≤
      (1 + |Real.log params.gamma1| / Real.log params.gamma2) *
        (thirdOrderComplexityConstant params p L
          (max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))) theta *
          ((f (x 0) - low) / min ((epsilon 0) ^ (((p + 1 : ℕ) : ℝ) / p))
            (min ((epsilon 1) ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)))
              ((epsilon 2) ^ (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)))))) +
        (1 + |Real.log params.gamma1| / Real.log params.gamma2) +
        Real.log (max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))) / sigma 0) /
          Real.log params.gamma2 + 1 := by
    intro N hn
    have hc := ((hprefix N hn).third_order_quality_evaluation_bounds hf
      (fun k _ => hlow (x k)) hn).1
    exact (by simp [functionEvaluations] : (N : ℝ) ≤ (functionEvaluations N : ℝ)).trans hc
  obtain ⟨K, _, hK, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound hb
  exact ⟨K, hprefix K hfirst, hK, hfirst,
    (hprefix K hfirst).third_order_quality_evaluation_bounds hf (fun k _ => hlow (x k)) hfirst⟩

end FiniteDimensional

end Optimization.HigherOrderRegularization
