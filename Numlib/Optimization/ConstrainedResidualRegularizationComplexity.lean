import Numlib.Optimization.ConstrainedResidualRegularization
import Numlib.Optimization.ParameterUpdatesPotential

/-!
# Evaluation bounds for constrained residual regularization

The feasible accepted-step estimate transfers to the scalar residual-root potential. The
large-contraction split and uniformization use the same arithmetic as unconstrained residual
regularization. A finite root telescope and actual parameter updates bound cached oracle calls.
-/

noncomputable section
namespace Optimization.ConstrainedResidualRegularization
open HigherOrderRegularization ParameterUpdates FeasibleCriticality ConstrainedRegularization
open ResidualRegularization

variable {E : Type} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  {params : RegularizationParameters} {p N : ℕ} {theta epsilon0 epsilon1 ell : ℝ}
  {r : E → F} {C : Set E} {x s : ℕ → E} {sigma : ℕ → ℝ}

omit [FiniteDimensional ℝ E] in
/-- The first-order residual-root decrease coefficient is positive for actual legal trials. -/
theorem RunPrefix.rootDecrease_pos
    (h : RunPrefix params p theta epsilon0 epsilon1 r ell C x s sigma N)
    {L S beta : ℝ} {i : ℕ} (hb0 : 0 < beta) (hb1 : beta < 1)
    (hL : 0 ≤ L) (hS : 0 ≤ S) (a0 : ℝ) :
    0 < rootDecrease params 1 p i ell beta L S epsilon0 a0
      (fun _ => theta) (fun _ => epsilon1) := by
  unfold rootDecrease
  apply div_pos
  · apply mul_pos
    · apply enabledMin_pos (by omega)
      · exact sub_pos.mpr (Real.rpow_lt_one hb0.le hb1 (by positivity))
      · intro j _
        exact div_pos (mul_pos (decreaseConstant_pos params p (j.val + 1) hL hS
          h.theta_mem.1) (Real.rpow_pos_of_pos hb0 _)) (by positivity)
    · exact enabledMin_pos (by omega) (Real.rpow_pos_of_pos h.residual_tolerance_pos _)
        (fun _ _ => Real.rpow_pos_of_pos h.epsilon_pos _)
  · exact zero_lt_one.trans_le (residual_le_enabledMax _ _ _)

/-- Failure of the normalized feasible stopping test pays a uniform root decrease at
accepted trials, including the separate large-residual-contraction branch. -/
theorem RunPrefix.root_decrease_of_not_stationary
    (h : RunPrefix params p theta epsilon0 epsilon1 r ell C x s sigma N)
    {L beta : ℝ} {i k : ℕ} (hf : SmoothOn (residualPowerObjective r ell) C p L)
    (hC : IsClosed C) (hconv : Convex ℝ C) (hb0 : 0 < beta) (hb1 : beta < 1)
    (hi : 0 ≤ residualDescentExponent p ell i 1) (hk : k < N)
    (hs : params.eta1 ≤ ratio (residualPowerObjective r ell) p (x k) (s k))
    (hn : ¬Stationary C epsilon0 epsilon1 r ell (x (k + 1))) :
    rootDecrease params 1 p i ell beta L
      (max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))) epsilon0 ‖r (x 0)‖
      (fun _ => theta) (fun _ => epsilon1) ≤
        ‖r (x k)‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i) -
          ‖r (x (k + 1))‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i) := by
  let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
  let t := (1 : ℝ) / (2 : ℝ) ^ i
  let K0 := 1 - beta ^ t
  let KR := rootDecreaseCoefficient params p i ell beta L S (fun _ => theta)
  let K := enabledMin 1 K0 KR
  let T := enabledMin 1 (epsilon0 ^ t) (fun j : Fin 3 => epsilon1 ^ derivativeExponent p j)
  let D := enabledMax 1 1 (fun j : Fin 3 => ‖r (x 0)‖ ^
    residualDescentExponent p ell i (j.val + 1))
  change K * T / D ≤ _
  have hS : 0 ≤ S :=
    (h.toRegularizationPrefix.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  have hKr : ∀ j : Fin 3, 0 < KR j := fun j =>
    div_pos (mul_pos (decreaseConstant_pos params p (j.val + 1) hf.nonneg hS h.theta_mem.1)
      (Real.rpow_pos_of_pos hb0 _)) (by positivity)
  have hK0 : 0 < K0 := sub_pos.mpr (Real.rpow_lt_one hb0.le hb1 (by positivity))
  have hK : 0 < K := enabledMin_pos (by omega) hK0 (fun j _ => hKr j)
  have hT : 0 < T := enabledMin_pos (by omega)
    (Real.rpow_pos_of_pos h.residual_tolerance_pos _)
    (fun _ _ => Real.rpow_pos_of_pos h.epsilon_pos _)
  have hD1 : 1 ≤ D := residual_le_enabledMax _ _ _
  have hD : 0 < D := zero_lt_one.trans_le hD1
  obtain ⟨hbtest, hfail⟩ := (not_stationary_iff
    (h.toFeasibleTrial.feasible (k := k + 1) (by omega))).mp hn
  have hb : 0 < ‖r (x (k + 1))‖ := h.residual_tolerance_pos.trans hbtest
  have hba := h.residual_norm_nonincrease hk
  have ha := hb.trans_le hba
  by_cases hrel : beta * ‖r (x k)‖ < ‖r (x (k + 1))‖
  · have hraw := h.root_decrease_from_criticality (i := i) hf hC hconv hk hs hb0 hrel.le hb
    have hpower : 0 ≤ derivativeExponent p 0 := by unfold derivativeExponent; positivity
    have hd := uniform_root_decrease hK.le hT.le hD
      (enabledMin_le (q := 1) 0 (by decide))
      (enabledMin_le (q := 1) 0 (by decide)) h.epsilon_pos.le hfail.le hpower ha
      (h.residual_norm_le_initial (by omega)) hi
      (by simpa only [Fin.val_zero, Nat.cast_zero, zero_add] using
        (le_enabledMax (q := 1) (b := 1) (a := fun j => ‖r (x 0)‖ ^
          residualDescentExponent p ell i (j.val + 1)) 0 (by decide)))
    exact hd.trans (by simpa [KR, derivativeExponent, S] using hraw)
  · have hsmall := Real.root_sub_root_ge_of_le_mul (norm_nonneg (r (x k)))
      (norm_nonneg (r (x (k + 1)))) hb0.le (le_of_not_gt hrel) (by positivity : 0 ≤ t)
    have hbt : epsilon0 ^ t ≤ ‖r (x k)‖ ^ t :=
      Real.rpow_le_rpow h.residual_tolerance_pos.le (hbtest.le.trans hba) (by positivity)
    have hKT : K * T ≤ K0 * ‖r (x k)‖ ^ t :=
      mul_le_mul (enabledMin_le_residual _ _ _)
        ((enabledMin_le_residual _ _ _).trans hbt) hT.le hK0.le
    exact (div_le_self (mul_nonneg hK.le hT.le) hD1).trans (hKT.trans hsmall)

/-- The actual root telescope gives cached residual and derivative budgets with the exact
maximum of initial powers and minimum of the two distinct tolerance powers. -/
theorem RunPrefix.evaluation_bounds
    (h : RunPrefix params p theta epsilon0 epsilon1 r ell C x s sigma N)
    {L beta : ℝ} {i : ℕ} (hf : SmoothOn (residualPowerObjective r ell) C p L)
    (hC : IsClosed C) (hconv : Convex ℝ C) (hb0 : 0 < beta) (hb1 : beta < 1)
    (hi : 0 ≤ residualDescentExponent p ell i 1)
    (hfirst : ∀ k < N, ¬Stationary C epsilon0 epsilon1 r ell (x k)) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := complexityConstant params 1 p i ell beta L S (fun _ => theta) *
      (max (‖r (x 0)‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i))
        (‖r (x 0)‖ ^ (1 - (ell - 1) / p)) /
        min (epsilon0 ^ ((1 : ℝ) / (2 : ℝ) ^ i))
          (epsilon1 ^ (((p + 1 : ℕ) : ℝ) / p)))
    let A := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let B := Real.log (S / sigma 0) / Real.log params.gamma2
    (residualFunctionEvaluations N : ℝ) ≤ A * Q + A + B + 1 ∧
      (residualDerivativeEvaluations params p r ell x s N : ℝ) ≤ Q + 2 := by
  dsimp only
  classical
  let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
  let delta := rootDecrease params 1 p i ell beta L S epsilon0 ‖r (x 0)‖
    (fun _ => theta) (fun _ => epsilon1)
  let u := fun k => ‖r (x k)‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i)
  let accepted := fun k => params.eta1 ≤ ratio (residualPowerObjective r ell) p (x k) (s k)
  have hS : 0 ≤ S :=
    (h.toRegularizationPrefix.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  have hd : 0 < delta := h.rootDecrease_pos hb0 hb1 hf.nonneg hS _
  have hcount := successCount_le_of_potential (N := N) (u := u) (accepted := accepted)
    (P := fun k => Stationary C epsilon0 epsilon1 r ell (x k)) hd
    (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
    (fun k hk => Real.rpow_le_rpow (norm_nonneg _) (h.residual_norm_nonincrease hk)
      (by positivity : 0 ≤ (1 : ℝ) / (2 : ℝ) ^ i))
    (fun k hk hs hn => h.root_decrease_of_not_stationary hf hC hconv hb0 hb1 hi hk hs hn)
    hfirst
  have hid := root_budget_eq (params := params) (q := 1) (p := p) (i := i)
    (ell := ell) (beta := beta) (L := L) (S := S) (epsilon0 := epsilon0)
    (theta := fun _ => theta) (epsilon := fun _ => epsilon1)
    (by omega) (norm_nonneg (r (x 0)))
    (by
      intro j hj
      have hz : j = 0 := Fin.ext (by omega)
      subst j
      simpa only [Fin.val_zero, Nat.cast_zero, zero_add] using hi)
  simp only [initialResidualFactor, enabledMax, show ¬2 ≤ (1 : ℕ) by omega,
    ite_false, max_self, Fin.val_zero, zero_add, Nat.cast_one, one_mul,
    Nat.cast_zero, sub_zero, toleranceFactor_one] at hid
  change u 0 / delta = _ at hid
  rw [hid] at hcount
  have ht := h.toRegularizationPrefix.total_count_le le_rfl
    (h.toFeasibleTrial.sigma_upper hf hconv le_rfl)
  have hA : 0 ≤ 1 + |Real.log params.gamma1| / Real.log params.gamma2 :=
    add_nonneg zero_le_one
      (div_nonneg (abs_nonneg _) (Real.log_pos params.one_lt_gamma2).le)
  have hm := mul_le_mul_of_nonneg_right hcount hA
  simp only [residualFunctionEvaluations, residualDerivativeEvaluations,
    functionEvaluations, derivativeEvaluations, Nat.cast_add, Nat.cast_one]
  dsimp only [accepted, S] at hcount hm
  push_cast at hcount hm
  constructor <;> linarith

/-- Availability of genuine feasible Taylor trials before first stop forces termination
with exact residual budgets; the contract assumes no decrease, count or terminal certificate. -/
theorem exists_first_run_with_cost {L beta : ℝ} {i : ℕ}
    (hf : SmoothOn (residualPowerObjective r ell) C p L)
    (hC : IsClosed C) (hconv : Convex ℝ C) (hb0 : 0 < beta) (hb1 : beta < 1)
    (hi : 0 ≤ residualDescentExponent p ell i 1)
    (hprefix : ∀ N, (∀ k < N, ¬Stationary C epsilon0 epsilon1 r ell (x k)) →
      RunPrefix params p theta epsilon0 epsilon1 r ell C x s sigma N) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := complexityConstant params 1 p i ell beta L S (fun _ => theta) *
      (max (‖r (x 0)‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i))
        (‖r (x 0)‖ ^ (1 - (ell - 1) / p)) /
        min (epsilon0 ^ ((1 : ℝ) / (2 : ℝ) ^ i))
          (epsilon1 ^ (((p + 1 : ℕ) : ℝ) / p)))
    let A := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let B := Real.log (S / sigma 0) / Real.log params.gamma2
    ∃ K, IsRun params p theta epsilon0 epsilon1 r ell C x s sigma K ∧
      (residualFunctionEvaluations K : ℝ) ≤ A * Q + A + B + 1 ∧
      (residualDerivativeEvaluations params p r ell x s K : ℝ) ≤ Q + 2 := by
  dsimp only
  have hb := fun N hn => (hprefix N hn).evaluation_bounds hf hC hconv hb0 hb1 hi hn
  let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
  let Q := complexityConstant params 1 p i ell beta L S (fun _ => theta) *
    (max (‖r (x 0)‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i))
      (‖r (x 0)‖ ^ (1 - (ell - 1) / p)) /
      min (epsilon0 ^ ((1 : ℝ) / (2 : ℝ) ^ i))
        (epsilon1 ^ (((p + 1 : ℕ) : ℝ) / p)))
  let A := 1 + |Real.log params.gamma1| / Real.log params.gamma2
  let B := Real.log (S / sigma 0) / Real.log params.gamma2
  obtain ⟨K, _, hK, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound
    (B := A * Q + A + B + 1)
    (fun N hn => (by
      have hc := (hb N hn).1
      simp only [residualFunctionEvaluations, functionEvaluations, Nat.cast_add,
        Nat.cast_one] at hc
      change (N : ℝ) ≤ A * Q + A + B + 1
      have hc' : (N : ℝ) + 1 ≤ A * Q + A + B + 1 := by
        simpa only [Q, A, B, S, Nat.cast_add, Nat.cast_one] using hc
      linarith))
  exact ⟨K, ⟨hprefix K hfirst, hK, hfirst⟩, hb K hfirst⟩

end Optimization.ConstrainedResidualRegularization
