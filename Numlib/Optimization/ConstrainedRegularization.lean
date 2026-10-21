import Numlib.Optimization.HigherOrderRegularizationComplexity
import Numlib.Optimization.FeasibleCriticality
import Mathlib.Analysis.Convex.Basic

/-!
# Regularized Taylor steps under convex constraints

Local smoothness on an open neighborhood and Lipschitz control on the constraint set suffice
for actual Taylor trials. Feasibility is preserved by the acceptance rule. First-order model
criticality is tested on displacements feasible at the trial point, with a step-scaled tolerance.
Finite prefixes record only executed algorithm laws; existence of legal steps is separate.
-/

noncomputable section
open scoped Nat
namespace Optimization.ConstrainedRegularization
open HigherOrderRegularization RegularizedTaylorModel ParameterUpdates FeasibleCriticality

variable {E : Type} [NormedAddCommGroup E]

section Normed
variable [NormedSpace ℝ E]

/-- Smoothness on an open neighborhood, with the highest derivative Lipschitz on `C` only. -/
structure SmoothOn (f : E → ℝ) (C : Set E) (p : ℕ) (L : ℝ) : Prop where
  degree_pos : 1 ≤ p
  nonneg : 0 ≤ L
  neighborhood : ∃ U : Set E, IsOpen U ∧ C ⊆ U ∧ ContDiffOn ℝ p f U
  lipschitz : ∀ x ∈ C, ∀ y ∈ C,
    ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ L * ‖x - y‖

/-- The open extension gives unambiguous ambient derivatives at every feasible point. -/
theorem SmoothOn.contDiffAt {f : E → ℝ} {C : Set E} {p : ℕ} {L : ℝ}
    (h : SmoothOn f C p L) {x : E} (hx : x ∈ C) : ContDiffAt ℝ p f x := by
  obtain ⟨U, hU, hCU, hf⟩ := h.neighborhood
  exact (hf x (hCU hx)).contDiffAt (hU.mem_nhds (hCU hx))

/-- A convex feasible segment remains inside the domain of the local derivative estimates. -/
theorem SmoothOn.derivative_remainder {f : E → ℝ} {C : Set E} {p j : ℕ} {L : ℝ}
    (h : SmoothOn f C p L) (hC : Convex ℝ C) {x s : E}
    (hx : x ∈ C) (hs : x + s ∈ C) (hj : j ≤ p) :
    ‖iteratedFDeriv ℝ j f (x + s) - iteratedFDeriv ℝ j (taylorModel f p x) s‖ ≤
      L / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) := by
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • s ∈ C := by
    intro t ht
    have hh := hC hx hs (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
    convert hh using 1
    module
  have hb := norm_iteratedFDeriv_sub_taylorModel_le_holder (f := f) (p := p)
    (j := j) (x := x) (s := s) (H := L) (β := 1) hj (by norm_num)
    (fun t ht => h.contDiffAt (hseg t ht))
    (by
      intro t ht
      simpa only [add_sub_cancel_left, Real.rpow_one] using
        h.lipschitz (x + t • s) (hseg t ht) x hx)
  have hprod : ∀ k : ℕ, (∏ i ∈ Finset.range k, (((i + 1 : ℕ) : ℝ) + 1)) =
      ((k + 1)! : ℝ) := by
    intro k
    have hh := congrArg (fun n : ℕ => (n : ℝ)) (Nat.factorial_mul_ascFactorial 1 k)
    norm_num [Nat.ascFactorial_eq_prod_range, Nat.cast_prod, Nat.cast_add, Nat.cast_one,
      add_comm, add_left_comm, add_assoc] at hh ⊢
    exact hh
  rw [hprod, ← Nat.cast_add_one, Real.rpow_natCast] at hb
  exact hb

/-- Feasible executed trials and the exact objective acceptance and parameter update laws. -/
structure TrialPrefix (params : RegularizationParameters) (p : ℕ) (f : E → ℝ) (C : Set E)
    (x s : ℕ → E) (sigma : ℕ → ℝ) (N : ℕ) : Prop extends
    HigherOrderRegularization.TrialPrefix params p f x s sigma N where
  initial_feasible : x 0 ∈ C
  trial_feasible : ∀ k < N, x k + s k ∈ C

variable {params : RegularizationParameters} {p N : ℕ} {f : E → ℝ} {C : Set E}
  {x s : ℕ → E} {sigma : ℕ → ℝ} {L S : ℝ}

/-- Every accepted or retained iterate of an executed prefix is feasible. -/
theorem TrialPrefix.feasible (h : TrialPrefix params p f C x s sigma N)
    {k : ℕ} (hk : k ≤ N) : x k ∈ C := by
  induction k with
  | zero => exact h.initial_feasible
  | succ k ih =>
    rw [h.iterate k (by omega)]
    split_ifs
    · exact h.trial_feasible k (by omega)
    · exact ih (by omega)

/-- Objective query locations: the initial point, then each actual trial point. -/
def functionQueryPoints (x s : ℕ → E) (N : ℕ) : List E :=
  x 0 :: (List.range N).map (fun k => x k + s k)

omit [NormedSpace ℝ E] in
/-- The objective counter is the length of the actual query schedule. -/
@[simp] theorem length_functionQueryPoints (x s : ℕ → E) (N : ℕ) :
    (functionQueryPoints x s N).length = functionEvaluations N := by
  simp [functionQueryPoints, functionEvaluations]

open Classical in
/-- Each derivative order is queried initially and at accepted successors only. -/
def derivativeQueryPoints (params : RegularizationParameters) (p : ℕ) (f : E → ℝ)
    (x s : ℕ → E) (N : ℕ) : List E :=
  let accepted := (Finset.range N).filter (fun k => params.eta1 ≤ ratio f p (x k) (s k))
  x 0 :: (accepted.sort (· ≤ ·)).map (fun k => x (k + 1))

/-- The cached derivative counter is the length of its actual query schedule. -/
@[simp] theorem length_derivativeQueryPoints (params : RegularizationParameters) (p : ℕ)
    (f : E → ℝ) (x s : ℕ → E) (N : ℕ) :
    (derivativeQueryPoints params p f x s N).length = derivativeEvaluations params p f x s N := by
  classical
  simp [derivativeQueryPoints, derivativeEvaluations, successCount, Nat.add_comm]

/-- Tensor perturbations control every diagonal evaluation on the closed unit ball. -/
theorem abs_diagonal_sub_le_norm {j : ℕ}
    (A B : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ) {d : E} (hd : ‖d‖ ≤ 1) :
    |A (fun _ => d) - B (fun _ => d)| ≤ ‖A - B‖ := by
  have hb : ‖(A - B) (fun _ => d)‖ ≤ ‖A - B‖ * ‖d‖ ^ j := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (A - B).le_opNorm (fun _ => d)
  have hh := hb.trans (mul_le_of_le_one_right (norm_nonneg (A - B))
    (pow_le_one₀ (norm_nonneg d) hd))
  simpa only [sub_apply, Real.norm_eq_abs] using hh

/-- A tensor error transfers an absolute directional bound, on directions of norm at most one. -/
theorem abs_diagonal_le_add_error {j : ℕ}
    (A B : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ) {d : E} {R T : ℝ}
    (hd : ‖d‖ ≤ 1) (hR : ‖A - B‖ ≤ R) (hT : |A (fun _ => d)| ≤ T) :
    |B (fun _ => d)| ≤ R + T := by
  have he := (abs_diagonal_sub_le_norm A B hd).trans hR
  have ht := abs_add_le (B (fun _ => d) - A (fun _ => d)) (A (fun _ => d))
  have he' : |B (fun _ => d) - A (fun _ => d)| ≤ R := by
    rwa [abs_sub_comm] at he
  simpa only [sub_add_cancel] using ht.trans (add_le_add he' hT)

/-- An unchanged iterate after rejection reuses every actual objective derivative tensor. -/
theorem TrialPrefix.derivative_cache_rejected
    (h : TrialPrefix params p f C x s sigma N) {k : ℕ} (hk : k < N)
    (hs : ¬params.eta1 ≤ ratio f p (x k) (s k)) (j : ℕ) :
    iteratedFDeriv ℝ j f (x (k + 1)) = iteratedFDeriv ℝ j f (x k) := by
  rw [h.iterate k hk, ite_eq_right hs]

end Normed

section Inner
variable [InnerProductSpace ℝ E]
variable {params : RegularizationParameters} {p N : ℕ} {f : E → ℝ} {C : Set E}
  {x s : ℕ → E} {sigma : ℕ → ℝ} {L S : ℝ}

/-- Objective and model tensors differ by the sharp factorial bound on a feasible trial. -/
theorem TrialPrefix.derivative_difference (h : TrialPrefix params p f C x s sigma N)
    (hf : SmoothOn f C p L) (hC : Convex ℝ C) {j k : ℕ}
    (hj : 1 ≤ j) (hj3 : j ≤ 3) (hjp : j ≤ p) (hk : k < N) (hS : sigma k ≤ S) :
    ‖iteratedFDeriv ℝ j f (x k + s k) -
      iteratedFDeriv ℝ j (model f p (x k) (sigma k)) (s k)‖ ≤
      (L + S) / ((p - j + 1)! : ℝ) * ‖s k‖ ^ (p - j + 1) :=
  norm_derivative_sub_model_le (h.toTrialPrefix.step_ne_zero hk)
    (h.toRegularizationPrefix.pos (by omega)).le hS
    (hf.derivative_remainder hC (h.feasible (by omega)) (h.trial_feasible k hk) hjp)
    (norm_iteratedFDeriv_norm_pow_le hj hj3 hjp (h.toTrialPrefix.step_ne_zero hk))

/-- A local Taylor value remainder makes sufficiently regularized trials very successful. -/
theorem TrialPrefix.ratio_ge_of_sigma_ge (h : TrialPrefix params p f C x s sigma N)
    (hf : SmoothOn f C p L) (hC : Convex ℝ C) {k : ℕ} (hk : k < N)
    (hb : L / (1 - params.eta2) ≤ sigma k) : params.eta2 ≤ ratio f p (x k) (s k) := by
  have hrem := hf.derivative_remainder hC (h.feasible (by omega))
    (h.trial_feasible k hk) (Nat.zero_le p)
  rw [norm_iteratedFDeriv_zero_sub] at hrem
  have he := (abs_le.mp (show |f (x k + s k) - taylorModel f p (x k) (s k)| ≤
    L / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) by simpa using hrem)).2
  rw [ratio, ite_eq_right (h.toTrialPrefix.step_ne_zero hk),
    le_div_iff₀ (h.toTrialPrefix.predicted_pos hk)]
  have hden : 0 < 1 - params.eta2 := sub_pos.mpr params.eta2_lt_one
  have hb' := (div_le_iff₀ hden).mp hb
  have hh := mul_le_mul_of_nonneg_right hb' (pow_nonneg (norm_nonneg (s k)) (p + 1))
  have hd' := mul_le_mul_of_nonneg_left (h.toTrialPrefix.predicted_decrease hk) hden.le
  have hc : L / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) ≤
      (1 - params.eta2) * (sigma k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1)) := by
    calc
      _ = (L * ‖s k‖ ^ (p + 1)) / ((p + 1)! : ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hh (by positivity)
      _ = _ := by ring
  have herr := he.trans (hc.trans hd')
  simp only [taylorModel_zero] at herr ⊢
  nlinarith

/-- The source parameter bound uses Lipschitz control only on the convex constraint set. -/
theorem TrialPrefix.sigma_upper (h : TrialPrefix params p f C x s sigma N)
    (hf : SmoothOn f C p L) (hC : Convex ℝ C) {k : ℕ} (hk : k ≤ N) :
    sigma k ≤ max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))) :=
  h.toRegularizationPrefix.upper (fun _ hj hb => h.ratio_ge_of_sigma_ge hf hC hj hb) hk

/-- First-order trials use a feasible derivative gap with the actual step-scaled tolerance. -/
structure FirstOrderPrefix (params : RegularizationParameters) (p : ℕ) (theta epsilon : ℝ)
    (f : E → ℝ) (C : Set E) (x s : ℕ → E) (sigma : ℕ → ℝ) (N : ℕ) : Prop extends
    toFeasibleTrial : TrialPrefix params p f C x s sigma N where
  degree_pos : 1 ≤ p
  theta_mem : theta ∈ Set.Ioo 0 1
  epsilon_pos : 0 < epsilon
  residual : ∀ k < N, feasibleCriticality C (x k + s k)
    (fderiv ℝ (model f p (x k) (sigma k)) (s k)) ≤ theta * ‖s k‖ ^ p

variable [FiniteDimensional ℝ E] {theta epsilon : ℝ}

/-- The objective gap at an accepted successor is bounded by a multiple of step power. -/
theorem FirstOrderPrefix.criticality_bound
    (h : FirstOrderPrefix params p theta epsilon f C x s sigma N)
    (hf : SmoothOn f C p L) (hC : IsClosed C) (hconv : Convex ℝ C)
    {k : ℕ} (hk : k < N) (hs : params.eta1 ≤ ratio f p (x k) (s k)) (hS : sigma k ≤ S) :
    feasibleCriticality C (x (k + 1)) (fderiv ℝ f (x (k + 1))) ≤
      criticalityConstant p 1 L S theta * ‖s k‖ ^ p := by
  have he : p - 1 + 1 = p := by have := h.degree_pos; omega
  have hd := h.toFeasibleTrial.derivative_difference hf hconv (j := 1)
    (by omega) (by omega) h.degree_pos hk hS
  rw [he, norm_iteratedFDeriv_sub_eq_fderiv_sub, norm_iteratedFDeriv_zero_sub] at hd
  have hg := (le_abs_self _).trans (feasibleCriticality_lipschitz_derivative hC
    (h.trial_feasible k hk) (fderiv ℝ f (x k + s k))
    (fderiv ℝ (model f p (x k) (sigma k)) (s k)))
  rw [h.iterate k hk, ite_eq_left hs]
  have hr := h.residual k hk
  dsimp [criticalityConstant]
  rw [he]
  nlinarith

/-- A successful feasible trial gives real-power objective decrease from its true criticality. -/
theorem FirstOrderPrefix.criticality_decrease
    (h : FirstOrderPrefix params p theta epsilon f C x s sigma N)
    (hf : SmoothOn f C p L) (hC : IsClosed C) (hconv : Convex ℝ C)
    {k : ℕ} (hk : k < N) (hs : params.eta1 ≤ ratio f p (x k) (s k)) (hS : sigma k ≤ S) :
    decreaseConstant params p 1 L S theta *
      feasibleCriticality C (x (k + 1)) (fderiv ℝ f (x (k + 1))) ^
        (((p + 1 : ℕ) : ℝ) / p) ≤ f (x k) - f (x (k + 1)) := by
  have he : p - 1 + 1 = p := by have := h.degree_pos; omega
  have hS0 : 0 ≤ S := (h.toRegularizationPrefix.pos (by omega)).le.trans hS
  simpa only [he] using h.toTrialPrefix.accepted_decrease_of_criticality hk hs
    (j := 1) (L := L) (S := S) (theta := theta)
    (feasibleCriticality_nonneg hC (h.toFeasibleTrial.feasible (by omega)) _)
    (criticalityConstant_pos hf.nonneg hS0 h.theta_mem.1)
    (by simpa only [he] using h.criticality_bound hf hC hconv hk hs hS)

/-- A complete first-order execution stops at its first feasible criticality test. -/
structure FirstOrderRun (params : RegularizationParameters) (p : ℕ) (theta epsilon : ℝ)
    (f : E → ℝ) (C : Set E) (x s : ℕ → E) (sigma : ℕ → ℝ) (N : ℕ) : Prop extends
    toFirstOrderPrefix : FirstOrderPrefix params p theta epsilon f C x s sigma N where
  terminal : feasibleCriticality C (x N) (fderiv ℝ f (x N)) ≤ epsilon
  first : ∀ k < N, ¬feasibleCriticality C (x k) (fderiv ℝ f (x k)) ≤ epsilon

/-- Counts refer to one objective query per trial and one derivative query per accepted point.
No derivative queries occur after rejected trials. Each derivative order has this same budget. -/
theorem FirstOrderPrefix.evaluation_bounds
    (h : FirstOrderPrefix params p theta epsilon f C x s sigma N)
    (hf : SmoothOn f C p L) (hC : IsClosed C) (hconv : Convex ℝ C) {low : ℝ}
    (hlow : ∀ y ∈ C, low ≤ f y)
    (hfirst : ∀ k < N, ¬feasibleCriticality C (x k) (fderiv ℝ f (x k)) ≤ epsilon) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := firstOrderComplexityConstant params p L S theta *
      ((f (x 0) - low) / epsilon ^ (((p + 1 : ℕ) : ℝ) / p))
    let A := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let B := Real.log (S / sigma 0) / Real.log params.gamma2
    (functionEvaluations N : ℝ) ≤ A * Q + A + B + 1 ∧
      (derivativeEvaluations params p f x s N : ℝ) ≤ Q + 2 := by
  dsimp only
  let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
  let K := decreaseConstant params p 1 L S theta
  have hS : 0 ≤ S :=
    (h.toRegularizationPrefix.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  have hK : 0 < K := decreaseConstant_pos params p 1 hf.nonneg hS h.theta_mem.1
  have hd : 0 < K * epsilon ^ (((p + 1 : ℕ) : ℝ) / p) :=
    mul_pos hK (Real.rpow_pos_of_pos h.epsilon_pos _)
  have hdec : ∀ k < N, params.eta1 ≤ ratio f p (x k) (s k) →
      ¬feasibleCriticality C (x (k + 1)) (fderiv ℝ f (x (k + 1))) ≤ epsilon →
      K * epsilon ^ (((p + 1 : ℕ) : ℝ) / p) ≤ f (x k) - f (x (k + 1)) := by
    intro k hk hs hnot
    have hg : epsilon ≤ feasibleCriticality C (x (k + 1))
        (fderiv ℝ f (x (k + 1))) := (lt_of_not_ge hnot).le
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow h.epsilon_pos.le hg (by positivity)) hK.le).trans
      (h.criticality_decrease hf hC hconv hk hs
        (h.toFeasibleTrial.sigma_upper hf hconv (by omega)))
  have hs := h.toTrialPrefix.success_count_le hd
    (fun k hk => hlow (x k) (h.toFeasibleTrial.feasible hk)) hdec hfirst
  have ht := h.toRegularizationPrefix.total_count_le le_rfl
    (h.toFeasibleTrial.sigma_upper hf hconv le_rfl)
  have hA : 0 ≤ 1 + |Real.log params.gamma1| / Real.log params.gamma2 :=
    add_nonneg zero_le_one (div_nonneg (abs_nonneg _) (Real.log_pos params.one_lt_gamma2).le)
  have hm := mul_le_mul_of_nonneg_right hs hA
  have hid : (f (x 0) - low) / (K * epsilon ^ (((p + 1 : ℕ) : ℝ) / p)) =
      firstOrderComplexityConstant params p L S theta *
        ((f (x 0) - low) / epsilon ^ (((p + 1 : ℕ) : ℝ) / p)) := by
    simp only [firstOrderComplexityConstant, K, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hid] at hs hm
  dsimp only [S] at hs hm
  simp only [functionEvaluations, derivativeEvaluations, Nat.cast_add, Nat.cast_one] at hs hm ⊢
  constructor <;> linarith

/-- Availability of actual legal prefixes forces a first stop with the source cached budgets.
The availability hypothesis is an explicit solver contract, separate from the execution laws. -/
theorem exists_first_order_run_with_cost
    (hf : SmoothOn f C p L) (hC : IsClosed C) (hconv : Convex ℝ C) {low : ℝ}
    (hlow : ∀ y ∈ C, low ≤ f y)
    (hprefix : ∀ N, (∀ k < N,
      ¬feasibleCriticality C (x k) (fderiv ℝ f (x k)) ≤ epsilon) →
      FirstOrderPrefix params p theta epsilon f C x s sigma N) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := firstOrderComplexityConstant params p L S theta *
      ((f (x 0) - low) / epsilon ^ (((p + 1 : ℕ) : ℝ) / p))
    let A := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let B := Real.log (S / sigma 0) / Real.log params.gamma2
    ∃ K, FirstOrderRun params p theta epsilon f C x s sigma K ∧
      (functionEvaluations K : ℝ) ≤ A * Q + A + B + 1 ∧
      (derivativeEvaluations params p f x s K : ℝ) ≤ Q + 2 := by
  dsimp only
  have hb : ∀ N, (∀ k < N,
      ¬feasibleCriticality C (x k) (fderiv ℝ f (x k)) ≤ epsilon) →
      (N : ℝ) ≤ (1 + |Real.log params.gamma1| / Real.log params.gamma2) *
        (firstOrderComplexityConstant params p L
          (max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))) theta *
          ((f (x 0) - low) / epsilon ^ (((p + 1 : ℕ) : ℝ) / p))) +
        (1 + |Real.log params.gamma1| / Real.log params.gamma2) +
        Real.log (max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))) / sigma 0) /
          Real.log params.gamma2 + 1 := by
    intro N hn
    have hc := ((hprefix N hn).evaluation_bounds hf hC hconv hlow hn).1
    exact (by simp [functionEvaluations] : (N : ℝ) ≤ (functionEvaluations N : ℝ)).trans hc
  obtain ⟨K, _, hK, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound hb
  exact ⟨K, ⟨hprefix K hfirst, hK, hfirst⟩,
    (hprefix K hfirst).evaluation_bounds hf hC hconv hlow hfirst⟩

end Inner

end Optimization.ConstrainedRegularization
