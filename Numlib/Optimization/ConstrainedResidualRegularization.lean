import Numlib.Optimization.ConstrainedRegularization
import Numlib.Optimization.ResidualRegularizationComplexity

/-!
# Convexly constrained residual regularization

Actual feasible Taylor trials minimize the residual-power objective. Stopping first checks
whether the residual is small, and otherwise tests its normalized feasible derivative gap.
The execution laws contain neither decrease certificates nor stopping-time bounds.
-/

noncomputable section
namespace Optimization.ConstrainedResidualRegularization
open HigherOrderRegularization ParameterUpdates FeasibleCriticality
open ConstrainedRegularization

variable {E : Type} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F]

/-- Feasible approximate residual minimization, with the small-residual branch before division. -/
def Stationary (C : Set E) (epsilon0 epsilon1 : ℝ) (r : E → F) (ell : ℝ) (x : E) : Prop :=
  x ∈ C ∧ (‖r x‖ ≤ epsilon0 ∨ epsilon0 < ‖r x‖ ∧
    feasibleCriticality C x (fderiv ℝ (residualPowerObjective r ell) x) /
      ‖r x‖ ^ (ell - 1) ≤ epsilon1)

/-- The feasible stopping test is exactly the ordered pair of residual alternatives. -/
@[simp] theorem stationary_iff (C : Set E) (epsilon0 epsilon1 : ℝ) (r : E → F)
    (ell : ℝ) (x : E) : Stationary C epsilon0 epsilon1 r ell x ↔
    x ∈ C ∧ (‖r x‖ ≤ epsilon0 ∨ epsilon0 < ‖r x‖ ∧
      feasibleCriticality C x (fderiv ℝ (residualPowerObjective r ell) x) /
        ‖r x‖ ^ (ell - 1) ≤ epsilon1) := Iff.rfl

/-- Small feasible residuals terminate without any derivative normalization. -/
theorem stationary_of_residual_le {C : Set E} {epsilon0 epsilon1 ell : ℝ}
    {r : E → F} {x : E} (hx : x ∈ C) (hr : ‖r x‖ ≤ epsilon0) :
    Stationary C epsilon0 epsilon1 r ell x := ⟨hx, Or.inl hr⟩

/-- A failed test at a feasible point gives both a positive residual and a genuine
normalized feasible-criticality violation. -/
theorem not_stationary_iff {C : Set E} {epsilon0 epsilon1 ell : ℝ}
    {r : E → F} {x : E} (hx : x ∈ C) :
    ¬Stationary C epsilon0 epsilon1 r ell x ↔ epsilon0 < ‖r x‖ ∧
      epsilon1 < feasibleCriticality C x (fderiv ℝ (residualPowerObjective r ell) x) /
        ‖r x‖ ^ (ell - 1) := by
  simp only [Stationary, hx, true_and, not_or, not_and, not_le]
  constructor
  · rintro ⟨hr, hg⟩
    exact ⟨hr, hg hr⟩
  · rintro ⟨hr, hg⟩
    exact ⟨hr, fun _ => hg⟩

/-- Local ARp1-CC laws for the actual residual objective, with positive requested tolerances. -/
structure RunPrefix (params : RegularizationParameters) (p : ℕ)
    (theta epsilon0 epsilon1 : ℝ) (r : E → F) (ell : ℝ) (C : Set E)
    (x s : ℕ → E) (sigma : ℕ → ℝ) (N : ℕ) : Prop extends
    toFirstOrderPrefix : FirstOrderPrefix params p theta epsilon1
      (residualPowerObjective r ell) C x s sigma N where
  exponent_ge_two : 2 ≤ ell
  residual_tolerance_pos : 0 < epsilon0

/-- A complete constrained residual run stops at its first actual normalized feasible test. -/
structure IsRun (params : RegularizationParameters) (p : ℕ)
    (theta epsilon0 epsilon1 : ℝ) (r : E → F) (ell : ℝ) (C : Set E)
    (x s : ℕ → E) (sigma : ℕ → ℝ) (N : ℕ) : Prop extends
    toResidualPrefix : RunPrefix params p theta epsilon0 epsilon1 r ell C x s sigma N where
  terminal : Stationary C epsilon0 epsilon1 r ell (x N)
  first : ∀ k < N, ¬Stationary C epsilon0 epsilon1 r ell (x k)

variable {params : RegularizationParameters} {p N : ℕ} {theta epsilon0 epsilon1 ell : ℝ}
  {r : E → F} {C : Set E} {x s : ℕ → E} {sigma : ℕ → ℝ}

/-- Actual objective monotonicity implies monotonic residual norms. -/
theorem RunPrefix.residual_norm_nonincrease
    (h : RunPrefix params p theta epsilon0 epsilon1 r ell C x s sigma N)
    {k : ℕ} (hk : k < N) : ‖r (x (k + 1))‖ ≤ ‖r (x k)‖ := by
  have hell : 0 < ell := by linarith [h.exponent_ge_two]
  have hm := h.toTrialPrefix.objective_nonincrease hk
  change ‖r (x (k + 1))‖ ^ ell / ell ≤ ‖r (x k)‖ ^ ell / ell at hm
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hell).mp
    ((div_le_div_iff_of_pos_right hell).mp hm)

/-- Every residual in an executed prefix is bounded by its initial residual. -/
theorem RunPrefix.residual_norm_le_initial
    (h : RunPrefix params p theta epsilon0 epsilon1 r ell C x s sigma N)
    {k : ℕ} (hk : k ≤ N) : ‖r (x k)‖ ≤ ‖r (x 0)‖ := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (h.residual_norm_nonincrease (by omega)).trans (ih (by omega))

/-- Rejection retains the point and reuses every residual derivative tensor, not merely
its norm-power objective derivative. -/
theorem RunPrefix.residual_derivative_cache_rejected [NormedSpace ℝ F]
    (h : RunPrefix params p theta epsilon0 epsilon1 r ell C x s sigma N)
    {k : ℕ} (hk : k < N)
    (hs : ¬params.eta1 ≤ ratio (residualPowerObjective r ell) p (x k) (s k)) (j : ℕ) :
    iteratedFDeriv ℝ j r (x (k + 1)) = iteratedFDeriv ℝ j r (x k) := by
  rw [h.iterate k hk, ite_eq_right hs]

variable [FiniteDimensional ℝ E]

set_option maxHeartbeats 1200000 in
-- The scalar root transfer elaborates the full feasible derivative estimate.
/-- Accepted objective decrease yields the normalized dyadic root estimate, using the
actual feasible criticality rather than the unrestricted gradient norm. -/
theorem RunPrefix.root_decrease_from_criticality
    (h : RunPrefix params p theta epsilon0 epsilon1 r ell C x s sigma N)
    {L beta : ℝ} {i k : ℕ} (hf : SmoothOn (residualPowerObjective r ell) C p L)
    (hC : IsClosed C) (hconv : Convex ℝ C) (hk : k < N)
    (hs : params.eta1 ≤ ratio (residualPowerObjective r ell) p (x k) (s k))
    (hb0 : 0 < beta) (hrel : beta * ‖r (x k)‖ ≤ ‖r (x (k + 1))‖)
    (hb : 0 < ‖r (x (k + 1))‖) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    ResidualRegularization.rootDecreaseCoefficient params p i ell beta L S (fun _ => theta) 0 *
      (feasibleCriticality C (x (k + 1))
        (fderiv ℝ (residualPowerObjective r ell) (x (k + 1))) /
        ‖r (x (k + 1))‖ ^ (ell - 1)) ^ (((p + 1 : ℕ) : ℝ) / p) /
      ‖r (x k)‖ ^ residualDescentExponent p ell i 1 ≤
        ‖r (x k)‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i) -
          ‖r (x (k + 1))‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i) := by
  dsimp only
  let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
  have hS : 0 ≤ S :=
    (h.toRegularizationPrefix.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  have hc := feasibleCriticality_nonneg hC (h.toFeasibleTrial.feasible (k := k + 1) (by omega))
    (fderiv ℝ (residualPowerObjective r ell) (x (k + 1)))
  have hd := h.toFirstOrderPrefix.criticality_decrease hf hC hconv hk hs
    (h.toFeasibleTrial.sigma_upper hf hconv (by omega))
  have hell : 0 < ell := by linarith [h.exponent_ge_two]
  have hnorm := normalized_power_decrease hell hb hc hd
  have hp : (0 : ℝ) < p := by exact_mod_cast h.degree_pos
  simpa only [ResidualRegularization.rootDecreaseCoefficient,
    ResidualRegularization.derivativeExponent, Fin.val_zero, Nat.sub_zero, zero_add,
    sub_self, add_zero, sub_add_cancel, Nat.cast_add, Nat.cast_one] using
    residual_root_decrease (p := (p : ℝ)) (j := 1) (i := i) (ell := ell)
      (c := feasibleCriticality C (x (k + 1))
        (fderiv ℝ (residualPowerObjective r ell) (x (k + 1))) /
        ‖r (x (k + 1))‖ ^ (ell - 1))
      (by linarith) (by linarith [h.exponent_ge_two])
      (hb.trans_le (h.residual_norm_nonincrease hk)) hb.le
      (h.residual_norm_nonincrease hk) hb0 hrel
      (div_nonneg hc (Real.rpow_nonneg hb.le _))
      (decreaseConstant_pos params p 1 hf.nonneg hS h.theta_mem.1).le (by positivity)
      (by simpa only [Nat.cast_add, Nat.cast_one, sub_add_cancel] using hnorm)

end Optimization.ConstrainedResidualRegularization
