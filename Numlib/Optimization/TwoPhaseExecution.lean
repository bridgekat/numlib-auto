import Numlib.Optimization.TwoPhaseCertificates

/-!
# Finite executions of two-phase target methods

Inner histories record actual feasible Taylor trials, acceptances and parameter updates.
The literal variant uses a fixed model tolerance and a weak small-residual stopping test.
The corrected variant uses step-scaled ARp1 trials and the same strict boundary in its
inner stop and target reset. Neither execution interface assumes convergence or a budget.
-/

noncomputable section
namespace Optimization.TwoPhaseTargets
open FeasibleCriticality ConstrainedRegularization HigherOrderRegularization ParameterUpdates

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : Type} [NormedAddCommGroup F]

/-- The actual squared-residual feasible criticality test at the current target. -/
def TargetStationary (f : E → ℝ) (c : E → F) (C : Set E)
    (epsilon1 t : ℝ) (x : E) : Prop :=
  feasibleCriticality C x (fderiv ℝ (TargetLeastSquares.objective f c t) x) ≤
    epsilon1 * residualNorm f c t x

/-- Introduction and elimination of the actual target stationarity test. -/
@[simp] theorem targetStationary_iff (f : E → ℝ) (c : E → F) (C : Set E)
    (epsilon1 t : ℝ) (x : E) : TargetStationary f c C epsilon1 t x ↔
    feasibleCriticality C x (fderiv ℝ (TargetLeastSquares.objective f c t) x) ≤
      epsilon1 * residualNorm f c t x := Iff.rfl

/-- Ordered inner stopping tests. The Boolean selects strict consistent boundaries. -/
def InnerStop (corrected : Bool) (f : E → ℝ) (c : E → F) (C : Set E)
    (theta epsilon0 epsilon1 t : ℝ) (x : E) : Prop :=
  (if corrected then residualNorm f c t x < theta * epsilon0
    else residualNorm f c t x ≤ theta * epsilon0) ∨
    f x < t ∨ TargetStationary f c C epsilon1 t x

/-- A complete finite inner history includes endpoints, every trial and every parameter. -/
structure InnerHistory (E : Type) where
  point : ℕ → E
  step : ℕ → E
  sigma : ℕ → ℝ
  length : ℕ

/-- Genuine feasible Taylor trials, with either fixed ARp model criticality or the corrected
step-scaled ARp1 criterion. The first stopping test is checked at every iterate. -/
structure InnerHistory.IsRun (h : InnerHistory E) (corrected : Bool)
    (params : RegularizationParameters) (p : ℕ) (modelTheta theta epsilon0 epsilon1 : ℝ)
    (f : E → ℝ) (c : E → F) (C : Set E) (t : ℝ) : Prop extends
    toFeasibleTrial : ConstrainedRegularization.TrialPrefix params p
      (TargetLeastSquares.objective f c t) C h.point h.step
      h.sigma h.length where
  degree_pos : 1 ≤ p
  modelTheta_mem : modelTheta ∈ Set.Ioo 0 1
  epsilon1_pos : 0 < epsilon1
  model_test : ∀ i < h.length, feasibleCriticality C (h.point i + h.step i)
    (fderiv ℝ (model (TargetLeastSquares.objective f c t) p (h.point i) (h.sigma i))
      (h.step i)) ≤ modelTheta * (if corrected then ‖h.step i‖ ^ p else epsilon1)
  terminal : InnerStop corrected f c C theta epsilon0 epsilon1 t (h.point h.length)
  first : ∀ i < h.length, ¬InnerStop corrected f c C theta epsilon0 epsilon1 t (h.point i)

/-- Corrected inner trials are genuine ARp1-CC prefixes with the actual objective. -/
theorem InnerHistory.IsRun.toFirstOrderPrefix {h : InnerHistory E}
    {params : RegularizationParameters} {p : ℕ} {modelTheta theta epsilon0 epsilon1 : ℝ}
    {f : E → ℝ} {c : E → F} {C : Set E} {t : ℝ}
    (hr : h.IsRun true params p modelTheta theta epsilon0 epsilon1 f c C t) :
    FirstOrderPrefix params p modelTheta epsilon1 (TargetLeastSquares.objective f c t)
      C h.point h.step h.sigma h.length :=
  { hr.toFeasibleTrial with
    degree_pos := hr.degree_pos
    theta_mem := hr.modelTheta_mem
    epsilon_pos := hr.epsilon1_pos
    residual := by simpa using hr.model_test }

/-- The target update is the literal reset/reflection/final branch, without any oracle. -/
def nextTarget (f : E → ℝ) (c : E → F) (theta epsilon0 t : ℝ) (x : E) : ℝ :=
  if residualNorm f c t x < theta * epsilon0 then resetTarget f c epsilon0 x
  else if f x < t then reflectTarget f t x else t

/-- The outer loop terminates at the final branch, or after an updated-target test succeeds. -/
def OuterStop (f : E → ℝ) (c : E → F) (C : Set E)
    (theta epsilon0 epsilon1 t : ℝ) (x : E) : Prop :=
  (theta * epsilon0 ≤ residualNorm f c t x ∧ t ≤ f x) ∨
    TargetStationary f c C epsilon1 (nextTarget f c theta epsilon0 t x) x

/-- Finite actual outer histories identify the last inner point with the next outer point.
Every earlier outer iteration fails the actual termination test; the terminal one is retained. -/
structure OuterPrefix (corrected : Bool) (params : RegularizationParameters) (p : ℕ)
    (modelTheta theta epsilon0 epsilon1 : ℝ) (f : E → ℝ) (c : E → F) (C : Set E)
    (x : ℕ → E) (t : ℕ → ℝ) (history : ℕ → InnerHistory E) (N : ℕ) : Prop where
  theta_mem : theta ∈ Set.Ioo 0 1
  epsilon0_pos : 0 < epsilon0
  initial_feasible : x 0 ∈ C
  initial_small : ‖c (x 0)‖ ≤ theta * epsilon0
  initial_target : t 0 = resetTarget f c epsilon0 (x 0)
  inner : ∀ k < N, (history k).IsRun corrected params p modelTheta theta epsilon0
    epsilon1 f c C (t k)
  initial_link : ∀ k < N, (history k).point 0 = x k
  terminal_link : ∀ k < N, (history k).point (history k).length = x (k + 1)
  target_update : ∀ k < N, t (k + 1) = nextTarget f c theta epsilon0 (t k) (x (k + 1))
  first : ∀ k, k + 1 < N → ¬OuterStop f c C theta epsilon0 epsilon1 (t k) (x (k + 1))

/-- A complete Phase-2 run ends at its first actual outer termination test. -/
structure OuterRun (corrected : Bool) (params : RegularizationParameters) (p : ℕ)
    (modelTheta theta epsilon0 epsilon1 : ℝ) (f : E → ℝ) (c : E → F) (C : Set E)
    (x : ℕ → E) (t : ℕ → ℝ) (history : ℕ → InnerHistory E) (N : ℕ) : Prop extends
    OuterPrefix corrected params p modelTheta theta epsilon0 epsilon1 f c C x t history N where
  nonempty : 0 < N
  terminal : OuterStop f c C theta epsilon0 epsilon1 (t (N - 1)) (x N)

variable {corrected : Bool} {params : RegularizationParameters} {p N : ℕ}
  {modelTheta theta epsilon0 epsilon1 : ℝ} {f : E → ℝ} {c : E → F} {C : Set E}
  {x : ℕ → E} {t : ℕ → ℝ} {history : ℕ → InnerHistory E}

/-- Actual inner objective monotonicity implies augmented-residual monotonicity. -/
theorem OuterPrefix.inner_residual_le
    (h : OuterPrefix corrected params p modelTheta theta epsilon0 epsilon1 f c C x t history N)
    {k i : ℕ} (hk : k < N) (hi : i ≤ (history k).length) :
    residualNorm f c (t k) ((history k).point i) ≤ residualNorm f c (t k) (x k) := by
  have hm : TargetLeastSquares.objective f c (t k) ((history k).point i) ≤
      TargetLeastSquares.objective f c (t k) ((history k).point 0) := by
    induction i with
    | zero => exact le_rfl
    | succ i ih => exact ((h.inner k hk).toTrialPrefix.objective_nonincrease
        (by omega)).trans (ih (by omega))
  rw [objective_eq_half_sq, objective_eq_half_sq, h.initial_link k hk] at hm
  nlinarith [residualNorm_nonneg f c (t k) ((history k).point i),
    residualNorm_nonneg f c (t k) (x k)]

/-- Every outer point remains feasible, including the endpoint of a finite prefix. -/
theorem OuterPrefix.feasible
    (h : OuterPrefix corrected params p modelTheta theta epsilon0 epsilon1 f c C x t history N)
    {k : ℕ} (hk : k ≤ N) : x k ∈ C := by
  cases k with
  | zero => exact h.initial_feasible
  | succ k =>
    rw [← h.terminal_link k (by omega)]
    exact (h.inner k (by omega)).toFeasibleTrial.feasible le_rfl

/-- Both boundary conventions preserve nonnegative scalar gaps and the radius invariant. -/
theorem OuterPrefix.gap_and_radius
    (h : OuterPrefix corrected params p modelTheta theta epsilon0 epsilon1 f c C x t history N)
    {k : ℕ} (hk : k ≤ N) :
    0 ≤ f (x k) - t k ∧ residualNorm f c (t k) (x k) ≤ epsilon0 := by
  induction k with
  | zero =>
    rw [h.initial_target]
    refine ⟨reset_gap_nonneg _ _ _ _, ?_⟩
    rw [residualNorm_reset h.epsilon0_pos.le (h.initial_small.trans ?_)]
    nlinarith [h.theta_mem.2, h.epsilon0_pos]
  | succ k ih =>
    have hk' : k < N := by omega
    have hr : residualNorm f c (t k) (x (k + 1)) ≤ epsilon0 := by
      rw [← h.terminal_link k hk']
      exact (h.inner_residual_le hk' le_rfl).trans (ih (by omega)).2
    rw [h.target_update k hk']
    unfold nextTarget
    split_ifs with hs hf
    · refine ⟨reset_gap_nonneg _ _ _ _, ?_⟩
      rw [residualNorm_reset h.epsilon0_pos.le ((norm_constraint_le _ _ _ _).trans hr)]
    · exact ⟨(reflect_gap_pos hf).le, by simpa using hr⟩
    · exact ⟨by linarith, hr⟩

/-- Every executed target update is nonincreasing, with the reset paying its full radius gap. -/
theorem OuterPrefix.target_decrease
    (h : OuterPrefix corrected params p modelTheta theta epsilon0 epsilon1 f c C x t history N)
    {k : ℕ} (hk : k < N) :
    (if residualNorm f c (t k) (x (k + 1)) < theta * epsilon0
      then (1 - theta) * epsilon0 else 0) ≤ t k - t (k + 1) := by
  rw [h.target_update k hk]
  unfold nextTarget
  split_ifs with hs hf
  · exact reset_decrease h.epsilon0_pos.le h.theta_mem.1.le h.theta_mem.2.le hs.le
  · linarith [reflectTarget_lt hf]
  · simp

/-- A corrected terminating iteration necessarily satisfies the actual updated-target test.
The literal weak boundary does not support this implication. -/
theorem OuterRun.stationary
    (h : OuterRun true params p modelTheta theta epsilon0 epsilon1 f c C x t history N) :
    TargetStationary f c C epsilon1 (t N) (x N) := by
  have hn := h.nonempty
  have hN : N - 1 < N := by omega
  have hlink : N - 1 + 1 = N := by omega
  have ht : t N = nextTarget f c theta epsilon0 (t (N - 1)) (x N) := by
    simpa only [hlink] using h.target_update (N - 1) hN
  rw [ht]
  rcases h.terminal with hfinal | hs
  · have hstop := (h.inner (N - 1) hN).terminal
    rw [h.terminal_link (N - 1) hN, hlink] at hstop
    simp only [InnerStop, ite_true] at hstop
    have hs : ¬residualNorm f c (t (N - 1)) (x N) < theta * epsilon0 :=
      not_lt.mpr hfinal.1
    have hf : ¬ f (x N) < t (N - 1) := not_lt.mpr hfinal.2
    simpa [nextTarget, hs, hf] using hstop.resolve_left hs |>.resolve_left hf
  · exact hs

end Optimization.TwoPhaseTargets

namespace Optimization.TwoPhaseTargets
open FeasibleCriticality ConstrainedRegularization HigherOrderRegularization ParameterUpdates

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : Type} [NormedAddCommGroup F]
variable {corrected : Bool} {params : RegularizationParameters} {p N : ℕ}
  {modelTheta theta epsilon0 epsilon1 : ℝ} {f : E → ℝ} {c : E → F} {C : Set E}
  {x : ℕ → E} {t : ℕ → ℝ} {history : ℕ → InnerHistory E}

/-- A corrected run terminates in the closed residual annulus, including its inner boundary. -/
theorem OuterRun.residual_lower
    (h : OuterRun true params p modelTheta theta epsilon0 epsilon1 f c C x t history N) :
    theta * epsilon0 ≤ residualNorm f c (t N) (x N) := by
  have hn := h.nonempty
  have hk : N - 1 < N := by omega
  have hlink : N - 1 + 1 = N := by omega
  have ht : t N = nextTarget f c theta epsilon0 (t (N - 1)) (x N) := by
    simpa only [hlink] using h.target_update (N - 1) hk
  have hr : residualNorm f c (t (N - 1)) (x N) ≤ epsilon0 := by
    rw [← hlink, ← h.terminal_link (N - 1) hk]
    exact (h.inner_residual_le hk le_rfl).trans (h.gap_and_radius (by omega)).2
  rw [ht]
  unfold nextTarget
  split_ifs with hs hf
  · rw [residualNorm_reset h.epsilon0_pos.le ((norm_constraint_le _ _ _ _).trans hr)]
    nlinarith [h.theta_mem.2, h.epsilon0_pos]
  · simpa using le_of_not_gt hs
  · exact le_of_not_gt hs

open Classical in
/-- The actual reset indices among the first `N` complete outer histories. -/
def resetIndices (f : E → ℝ) (c : E → F) (theta epsilon0 : ℝ)
    (x : ℕ → E) (t : ℕ → ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun k => residualNorm f c (t k) (x (k + 1)) < theta * epsilon0)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Membership characterizes precisely an executed reset branch. -/
@[simp] theorem mem_resetIndices {k : ℕ} :
    k ∈ resetIndices f c theta epsilon0 x t N ↔
      k < N ∧ residualNorm f c (t k) (x (k + 1)) < theta * epsilon0 := by
  classical
  simp [resetIndices]

open Classical in
/-- The actual reflection indices among the first complete outer histories. -/
def reflectionIndices (f : E → ℝ) (c : E → F) (theta epsilon0 : ℝ)
    (x : ℕ → E) (t : ℕ → ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun k => theta * epsilon0 ≤ residualNorm f c (t k) (x (k + 1)) ∧
    f (x (k + 1)) < t k

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Membership exposes exactly the reflection branch and its executed index. -/
@[simp] theorem mem_reflectionIndices {k : ℕ} :
    k ∈ reflectionIndices f c theta epsilon0 x t N ↔
      k < N ∧ theta * epsilon0 ≤ residualNorm f c (t k) (x (k + 1)) ∧
        f (x (k + 1)) < t k := by
  classical
  simp [reflectionIndices]

/-- Target decreases telescope across every finite actual outer prefix. -/
theorem OuterPrefix.reset_budget
    (h : OuterPrefix corrected params p modelTheta theta epsilon0 epsilon1 f c C x t history N) :
    ((resetIndices f c theta epsilon0 x t N).card : ℝ) * ((1 - theta) * epsilon0) ≤
      t 0 - t N := by
  classical
  have hh := Finset.sum_le_sum (s := Finset.range N) (fun k hk =>
    h.target_decrease (Finset.mem_range.mp hk))
  have he : (∑ k ∈ Finset.range N,
      if residualNorm f c (t k) (x (k + 1)) < theta * epsilon0
      then (1 - theta) * epsilon0 else 0) =
      ((resetIndices f c theta epsilon0 x t N).card : ℝ) * ((1 - theta) * epsilon0) := by
    simp [← Finset.sum_filter, resetIndices]
  rw [he, Finset.sum_range_sub' (fun k => t k) N] at hh
  linarith

/-- Bounds on the objective near feasibility give the finite-prefix reset count. -/
theorem OuterPrefix.reset_count_le
    (h : OuterPrefix corrected params p modelTheta theta epsilon0 epsilon1 f c C x t history N)
    {low up : ℝ} (he : epsilon0 ≤ 1)
    (hb : ∀ k ≤ N, low ≤ f (x k) ∧ f (x k) ≤ up) :
    ((resetIndices f c theta epsilon0 x t N).card : ℝ) ≤
      (up - low + 1) / ((1 - theta) * epsilon0) := by
  have h0 := target_mem_interval he (hb 0 (Nat.zero_le N)).1
    (hb 0 (Nat.zero_le N)).2 (h.gap_and_radius (Nat.zero_le N)).1
    (h.gap_and_radius (Nat.zero_le N)).2
  have hN := target_mem_interval he (hb N le_rfl).1 (hb N le_rfl).2
    (h.gap_and_radius le_rfl).1 (h.gap_and_radius le_rfl).2
  apply (le_div_iff₀ (mul_pos (sub_pos.mpr h.theta_mem.2) h.epsilon0_pos)).mpr
  linarith [h.reset_budget, h0.2, hN.1]

/-- Rejection in an actual inner history reuses all tensors of each original oracle. -/
theorem InnerHistory.IsRun.oracle_cache_rejected {h : InnerHistory E}
    {corrected : Bool} {params : RegularizationParameters} {p : ℕ}
    {modelTheta theta epsilon0 epsilon1 : ℝ} {f : E → ℝ} {c : E → F} {C : Set E} {t : ℝ}
    (hr : h.IsRun corrected params p modelTheta theta epsilon0 epsilon1 f c C t)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (oracle : E → G)
    {i : ℕ} (hi : i < h.length)
    (hs : ¬params.eta1 ≤ ratio (TargetLeastSquares.objective f c t) p (h.point i) (h.step i))
    (j : ℕ) : iteratedFDeriv ℝ j oracle (h.point (i + 1)) =
      iteratedFDeriv ℝ j oracle (h.point i) := by
  rw [hr.iterate i hi, ite_eq_right hs]

/-- The shared terminal point reuses all original-oracle tensors when the target changes. -/
theorem OuterPrefix.oracle_cache_link
    (h : OuterPrefix corrected params p modelTheta theta epsilon0 epsilon1 f c C x t history N)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (oracle : E → G)
    {k : ℕ} (hk : k + 1 < N) (j : ℕ) :
    iteratedFDeriv ℝ j oracle ((history (k + 1)).point 0) =
      iteratedFDeriv ℝ j oracle ((history k).point (history k).length) := by
  rw [h.initial_link (k + 1) hk, h.terminal_link k (by omega)]

end Optimization.TwoPhaseTargets
