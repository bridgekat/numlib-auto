import NumlibSurface.CartisGouldToint.Chapter07.Section02.Targets
import NumlibSurface.CartisGouldToint.Chapter06.Section03
import Numlib.Optimization.TwoPhaseBlocks
import Numlib.Optimization.TwoPhaseBoundaryCounterexample

/-!
# Chapter 7, Section 2: actual target-method executions

The literal transcription and a corrected variant have separate names. The latter uses
ARp1-CC inner trials and a strict small-residual stopping test consistent with Step 2(a).
The existing wrong source records remain unresolved. Algebraic invariants hold for both
variants; corrected certificates use the weak residual boundary proved in the source text.
-/

noncomputable section
namespace CartisGouldToint.Chapter07.Section02
open Optimization ConstrainedRegularization TwoPhaseTargets
variable {n m : ℕ}

/-- The surface's actual augmented Euclidean norm agrees with the canonical scalar formula. -/
theorem norm_targetResidual_eq_residualNorm (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖targetResidual f c t x‖ = residualNorm f c t x := by
  rw [norm_targetResidual_eq_sqrt, residualNorm]
  congr 1
  unfold targetObjective TargetLeastSquares.objective
  ring

/-- The complete two-phase execution records Phase-1 ARpLE trials and, when feasibility
succeeds, all Phase-2 inner histories and shared endpoints. The Boolean selects only the
explicit boundary/model correction; no outcome certificate or budget is assumed. -/
structure twoPhaseExecution (corrected : Bool)
    (params : Chapter02.Section04.regularizationParameters) (p : ℕ)
    (tau modelTheta theta ell beta epsilon0 epsilon1 : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (C : Set (EuclideanSpace ℝ (Fin n)))
    (phaseOnePoint phaseOneStep : ℕ → EuclideanSpace ℝ (Fin n))
    (phaseOneSigma : ℕ → ℝ) (K : ℕ)
    (phaseTwoPoint : ℕ → EuclideanSpace ℝ (Fin n)) (target : ℕ → ℝ)
    (history : ℕ → InnerHistory (EuclideanSpace ℝ (Fin n))) (N : ℕ) : Prop where
  theta_mem : theta ∈ Set.Ioo 0 1
  tolerance0 : epsilon0 ∈ Set.Ioc 0 (min 1 beta)
  tolerance1 : epsilon1 ∈ Set.Ioc 0 1
  exponent_choice : ∃ i : ℕ, (ell = p ∧ Real.logb 2 p < i) ∨
    ∃ o : ℕ, Odd o ∧ p = o * 2 ^ i ∧ ell = 1 + (o : ℝ) * ((2 : ℝ) ^ i - 1)
  phase_one : Chapter06.Section03.algorithm_6_3_1 params p tau modelTheta
    (theta * epsilon0) epsilon1 c ell C phaseOnePoint phaseOneStep phaseOneSigma K
  phase_link : phaseTwoPoint 0 = phaseOnePoint K
  phase_two : if theta * epsilon0 < ‖c (phaseOnePoint K)‖ then N = 0 else
    OuterRun corrected params p modelTheta theta epsilon0 epsilon1 f c C
      phaseTwoPoint target history N

/-- Literal Algorithm 7.2.1 execution, preserving the weak inner boundary and the fixed
ARp-CC model-gradient tolerance. Its source correctness record is deliberately retained. -/
abbrev algorithm_7_2_1_literal := @twoPhaseExecution n m false

/-- Corrected TPp-GC execution: strict inner/reset small-residual boundaries and ARp1-CC
model-gradient trials. It is separate from the original wrong Algorithm 7.2.1 identifier. -/
abbrev algorithm_7_2_1_corrected := @twoPhaseExecution n m true

/-- Actual Phase-1 termination above the feasibility threshold gives the infeasibility
stationarity inequality (7.2.14), with strictly positive normalization denominator. -/
theorem twoPhaseExecution.phase_one_infeasibility {corrected : Bool}
    {params : Chapter02.Section04.regularizationParameters} {p K N : ℕ}
    {tau modelTheta theta ell beta epsilon0 epsilon1 : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {x1 s1 : ℕ → EuclideanSpace ℝ (Fin n)} {sigma1 : ℕ → ℝ}
    {x2 : ℕ → EuclideanSpace ℝ (Fin n)} {t : ℕ → ℝ}
    {history : ℕ → InnerHistory (EuclideanSpace ℝ (Fin n))}
    (h : twoPhaseExecution corrected params p tau modelTheta theta ell beta epsilon0 epsilon1
      f c C x1 s1 sigma1 K x2 t history N)
    (hr : theta * epsilon0 < ‖c (x1 K)‖) :
    x1 K ∈ C ∧ theta * epsilon0 < ‖c (x1 K)‖ ∧
      FeasibleCriticality.feasibleCriticality C (x1 K)
        (fderiv ℝ (Chapter05.Section01.residualPowerObjective c ell) (x1 K)) ≤
          epsilon1 * ‖c (x1 K)‖ ^ (ell - 1) := by
  have hstop := h.phase_one.terminal
  refine ⟨hstop.1, hr, ?_⟩
  rcases hstop.2 with hs | ⟨_, hw⟩
  · exact (not_le.mpr hr hs).elim
  · have hp : 0 < ‖c (x1 K)‖ :=
      (mul_pos h.theta_mem.1 h.tolerance0.1).trans hr
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hp (ell - 1))).mp hw

/-- Precise execution-level boundary defect: with identity objective and zero constraints,
one actual fixed-tolerance regularization step exits at equality without stationarity. -/
theorem literal_boundary_counterexample :
    let x : ℕ → ℝ := fun i => if i = 0 then 1 else 1 / 2
    let t : ℕ → ℝ := fun _ => 0
    OuterRun false boundaryParameters 2 (3 / 4) (1 / 2) 1 (1 / 4)
      (fun x : ℝ => x) (fun _ => (0 : ℝ)) Set.univ x t (fun _ => boundaryHistory) 1 ∧
    ¬TargetStationary (fun x : ℝ => x) (fun _ => (0 : ℝ)) Set.univ (1 / 4) (t 1) (x 1) :=
  TwoPhaseTargets.literal_boundary_counterexample

/-- Complete blocks of actual inner trials, with the initial and terminal partial blocks. -/
abbrev outerIterationBlocks (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (theta epsilon0 : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ)
    (history : ℕ → InnerHistory (EuclideanSpace ℝ (Fin n))) (N b : ℕ) :=
  iterationBlock f c theta epsilon0 x t history N b

/-- The original target invariants are independent of the two known source defects.
Both literal and corrected executions preserve the radius and nonnegative scalar gap. -/
theorem phase_two_invariants {corrected : Bool}
    {params : Chapter02.Section04.regularizationParameters} {p N : ℕ}
    {modelTheta theta epsilon0 epsilon1 : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C : Set (EuclideanSpace ℝ (Fin n))} {x : ℕ → EuclideanSpace ℝ (Fin n)}
    {t : ℕ → ℝ} {history : ℕ → InnerHistory (EuclideanSpace ℝ (Fin n))}
    (h : OuterPrefix corrected params p modelTheta theta epsilon0 epsilon1 f c C x t history N)
    {k : ℕ} (hk : k ≤ N) :
    x k ∈ C ∧ 0 ≤ f (x k) - t k ∧ ‖targetResidual f c (t k) (x k)‖ ≤ epsilon0 ∧
      ‖c (x k)‖ ≤ epsilon0 ∧ f (x k) - t k ≤ epsilon0 := by
  have hh := h.gap_and_radius hk
  refine ⟨h.feasible hk, hh.1, ?_, (norm_constraint_le _ _ _ _).trans hh.2, ?_⟩
  · simpa only [norm_targetResidual_eq_residualNorm] using hh.2
  · exact (le_abs_self _).trans ((abs_gap_le _ _ _ _).trans hh.2)

/-- Lemma 7.2.3: the actual target-update invariants, independent of whether the inner
model uses ARp or ARp1 and independent of the weak/strict inner stopping convention.
A final Step 2(c) retains its target; reset and reflection branches strictly decrease it. -/
theorem lemma_7_2_3 {corrected : Bool}
    {params : Chapter02.Section04.regularizationParameters} {p N : ℕ}
    {modelTheta theta epsilon0 epsilon1 beta low up : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C : Set (EuclideanSpace ℝ (Fin n))} {x : ℕ → EuclideanSpace ℝ (Fin n)}
    {t : ℕ → ℝ} {history : ℕ → InnerHistory (EuclideanSpace ℝ (Fin n))}
    (h : OuterPrefix corrected params p modelTheta theta epsilon0 epsilon1 f c C x t history N)
    (he : epsilon0 ≤ min 1 beta)
    (hb : ∀ z ∈ nearFeasibleSet C c beta, low ≤ f z ∧ f z ≤ up) :
    (∀ k ≤ N, 0 ≤ f (x k) - t k ∧ ‖c (x k)‖ ≤ epsilon0 ∧
      f (x k) - t k ≤ epsilon0 ∧ t k ∈ Set.Icc (low - 1) up) ∧
    (∀ k < N, t (k + 1) ≤ t k ∧
      (‖targetResidual f c (t k) (x (k + 1))‖ < theta * epsilon0 →
        ‖targetResidual f c (t (k + 1)) (x (k + 1))‖ = epsilon0 ∧
        (1 - theta) * epsilon0 ≤ t k - t (k + 1) ∧ t (k + 1) < t k) ∧
      (theta * epsilon0 ≤ ‖targetResidual f c (t k) (x (k + 1))‖ ∧
        f (x (k + 1)) < t k →
        ‖targetResidual f c (t (k + 1)) (x (k + 1))‖ =
          ‖targetResidual f c (t k) (x (k + 1))‖ ∧
        ‖targetResidual f c (t (k + 1)) (x (k + 1))‖ ≤ epsilon0 ∧ t (k + 1) < t k)) := by
  constructor
  · intro k hk
    obtain ⟨hx, hg, hr, hc, hgap⟩ := phase_two_invariants h hk
    have hf := hb _ ⟨hx, hc.trans (he.trans (min_le_right _ _))⟩
    exact ⟨hg, hc, hgap, target_mem_interval (he.trans (min_le_left _ _)) hf.1 hf.2 hg
      (by simpa only [norm_targetResidual_eq_residualNorm] using hr)⟩
  · intro k hk
    have hd := h.target_decrease hk
    have hnonneg : 0 ≤ t k - t (k + 1) := by
      split_ifs at hd with hs
      · exact (mul_nonneg (sub_pos.mpr h.theta_mem.2).le h.epsilon0_pos.le).trans hd
      · exact hd
    refine ⟨by linarith, ?_, ?_⟩
    · intro hs
      rw [norm_targetResidual_eq_residualNorm] at hs
      have ht : t (k + 1) = resetTarget f c epsilon0 (x (k + 1)) := by
        rw [h.target_update k hk, nextTarget, ite_eq_left hs]
      refine ⟨?_, ?_, ?_⟩
      · rw [norm_targetResidual_eq_residualNorm, ht]
        exact residualNorm_reset h.epsilon0_pos.le
          ((phase_two_invariants h (by omega)).2.2.2.1)
      · simpa only [ite_eq_left hs] using hd
      · have hpos : 0 < (1 - theta) * epsilon0 :=
          mul_pos (sub_pos.mpr h.theta_mem.2) h.epsilon0_pos
        rw [ite_eq_left hs] at hd
        linarith
    · rintro ⟨hs, hf⟩
      rw [norm_targetResidual_eq_residualNorm] at hs
      have ht : t (k + 1) = reflectTarget f (t k) (x (k + 1)) := by
        rw [h.target_update k hk, nextTarget, ite_eq_right (not_lt.mpr hs), ite_eq_left hf]
      refine ⟨?_, (phase_two_invariants h (by omega)).2.2.1, ?_⟩
      · rw [norm_targetResidual_eq_residualNorm, norm_targetResidual_eq_residualNorm, ht,
          residualNorm_reflect]
      · rw [ht]
        exact reflectTarget_lt hf

/-- The reset bound of Lemma 7.2.4 holds on every finite actual execution prefix under
f.B.Fb, for either boundary convention. This does not assert that the outer loop terminates. -/
theorem lemma_7_2_4 {corrected : Bool}
    {params : Chapter02.Section04.regularizationParameters} {p N : ℕ}
    {modelTheta theta epsilon0 epsilon1 beta low up : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C : Set (EuclideanSpace ℝ (Fin n))} {x : ℕ → EuclideanSpace ℝ (Fin n)}
    {t : ℕ → ℝ} {history : ℕ → InnerHistory (EuclideanSpace ℝ (Fin n))}
    (h : OuterPrefix corrected params p modelTheta theta epsilon0 epsilon1 f c C x t history N)
    (he : epsilon0 ≤ min 1 beta)
    (hb : ∀ z ∈ nearFeasibleSet C c beta, low ≤ f z ∧ f z ≤ up) :
    ((resetIndices f c theta epsilon0 x t N).card : ℝ) ≤
      (up - low + 1) / ((1 - theta) * epsilon0) := by
  apply h.reset_count_le (he.trans (min_le_left _ _))
  intro k hk
  apply hb _
  exact ⟨h.feasible hk, ((norm_constraint_le _ _ _ _).trans
    (h.gap_and_radius hk).2).trans (he.trans (min_le_right _ _))⟩

/-- Corrected Phase-2 termination yields either the source infeasibility certificate with
its justified weak boundary, or the actual scaled approximate KKT certificate (7.2.16). -/
theorem corrected_phase_two_certificate
    {params : Chapter02.Section04.regularizationParameters} {p N : ℕ}
    {modelTheta theta epsilon0 epsilon1 : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C : Set (EuclideanSpace ℝ (Fin n))} {x : ℕ → EuclideanSpace ℝ (Fin n)}
    {t : ℕ → ℝ} {history : ℕ → InnerHistory (EuclideanSpace ℝ (Fin n))}
    (h : OuterRun true params p modelTheta theta epsilon0 epsilon1 f c C x t history N)
    (hC : IsClosed C) (hf : DifferentiableAt ℝ f (x N)) (hc : DifferentiableAt ℝ c (x N)) :
    (f (x N) = t N ∧ theta * epsilon0 ≤ ‖c (x N)‖ ∧ ‖c (x N)‖ ≤ epsilon0 ∧
      FeasibleCriticality.feasibleCriticality C (x N)
        (fderiv ℝ (Chapter05.Section01.residualPowerObjective c 2) (x N)) /
          ‖c (x N)‖ ≤ epsilon1) ∨
    (t N < f (x N) ∧ Section01.IsScaledApproximateKKTPoint f c C epsilon0 epsilon1
      (x N) (targetMultiplier f c (t N) (x N))) := by
  have hx := h.feasible le_rfl
  have hh := h.gap_and_radius le_rfl
  have hw := h.stationary
  by_cases ha : f (x N) = t N
  · left
    have hr := residualNorm_of_gap_zero (c := c) ha
    have hlo : theta * epsilon0 ≤ ‖c (x N)‖ := by simpa only [hr] using h.residual_lower
    have hp : 0 < ‖c (x N)‖ := (mul_pos h.theta_mem.1 h.epsilon0_pos).trans_le hlo
    refine ⟨ha, hlo, (norm_constraint_le _ _ _ _).trans hh.2, ?_⟩
    have he : Chapter05.Section01.residualPowerObjective c 2 = fun z => ‖c z‖ ^ 2 / 2 := by
      funext z
      simp [Chapter05.Section01.residualPowerObjective, Optimization.residualPowerObjective]
    rw [he, div_le_iff₀ hp]
    rw [targetStationary_iff] at hw
    rw [fderiv_objective_eq_constraint hf hc ha, hr] at hw
    exact hw
  · right
    have hpos : 0 < f (x N) - t N := lt_of_le_of_ne hh.1 (Ne.symm (sub_ne_zero.mpr ha))
    refine ⟨by linarith, hx, (norm_constraint_le _ _ _ _).trans hh.2, ?_⟩
    rw [Section01.lagrangianCriticality_eq_feasibleCriticality]
    have he : (fun z => Section01.lagrangian f c z (targetMultiplier f c (t N) (x N))) =
        TwoPhaseTargets.lagrangian f c (targetMultiplier f c (t N) (x N)) := by
      funext z
      exact Section01.lagrangian_eq_sub_inner _ _ _ _
    rw [he]
    exact scaled_lagrangian_criticality hC hx hf hc hpos hw

/-- Lemma 7.2.2, with the exact Chapter 6.3 cached budgets: scaling the feasibility
threshold by theta scales its root by theta to the same exponent. The derivative schedule
retains the two terminal/initial overhead calls from Theorem 6.3.1. Constants precede both
tolerances; availability requests only genuine legal prefixes before the first test. -/
theorem lemma_7_2_2
    {params : Chapter02.Section04.regularizationParameters} {p i : ℕ}
    {tau modelTheta theta ell beta L sigmaInitial : ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    (htau : tau ∈ Set.Ioo 0 1) (hmodel : modelTheta ∈ Set.Ioo 0 1)
    (hcompat : (1 + tau) / 2 ≤ modelTheta) (htheta : theta ∈ Set.Ioo 0 1)
    (hsigma : 0 < sigmaInitial)
    (hf : SmoothOn (Chapter05.Section01.residualPowerObjective c ell) C p L)
    (hC : Chapter06.Section01.ConvexConstraintAssumptions C) (hell : 1 < ell)
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (hchoice : (ell = p ∧ Real.logb 2 p < i) ∨
      ∃ o : ℕ, Odd o ∧ p = o * 2 ^ i ∧ ell = 1 + (o : ℝ) * ((2 : ℝ) ^ i - 1)) :
    ∃ kD kF kC : ℝ, 0 < kD ∧ 0 < kF ∧ 0 < kC ∧
      ∀ epsilon0 ∈ Set.Ioc (0 : ℝ) 1, ∀ epsilon1 ∈ Set.Ioc (0 : ℝ) 1,
      ∀ (x s : ℕ → EuclideanSpace ℝ (Fin n)) (sigma : ℕ → ℝ),
      sigma 0 = sigmaInitial →
      (∀ N, (∀ k < N,
        ¬Chapter06.Section03.IsApproximateConstrainedResidualMinimizer c C ell
          (theta * epsilon0) epsilon1 (x k)) →
        ConstrainedResidualRegularization.RunPrefix params p modelTheta (theta * epsilon0)
          epsilon1 c ell C x s sigma N) →
      ∃ K, Chapter06.Section03.algorithm_6_3_1 params p tau modelTheta
          (theta * epsilon0) epsilon1 c ell C x s sigma K ∧
        let Q := max (‖c (x 0)‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i))
          (‖c (x 0)‖ ^ (1 - (ell - 1) / p)) /
          min (theta ^ ((1 : ℝ) / (2 : ℝ) ^ i) *
            epsilon0 ^ ((1 : ℝ) / (2 : ℝ) ^ i))
            (epsilon1 ^ (((p + 1 : ℕ) : ℝ) / p))
        (ResidualRegularization.residualFunctionEvaluations K : ℝ) ≤ kF * Q + kC ∧
        (ResidualRegularization.residualDerivativeEvaluations params p c ell x s K : ℝ) ≤
          kD * Q + 2 := by
  obtain ⟨hD, hF, hC', hbound⟩ := Chapter06.Section03.theorem_6_3_1
    (params := params) (i := i) htau hmodel hcompat hsigma hf hC hell hb0 hb1 hchoice
  refine ⟨_, _, _, hD, hF, hC', ?_⟩
  intro epsilon0 he0 epsilon1 he1 x s sigma hs hprefix
  have hscaled : theta * epsilon0 ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨mul_pos htheta.1 he0.1,
      (mul_le_mul_of_nonneg_right htheta.2.le he0.1.le).trans (by simpa using he0.2)⟩
  obtain ⟨K, hrun, hfunc, hderiv⟩ :=
    hbound (theta * epsilon0) hscaled epsilon1 he1 x s sigma hs hprefix
  refine ⟨K, hrun, ?_, ?_⟩
  · simpa only [Real.mul_rpow htheta.1.le he0.1.le] using hfunc
  · simpa only [Real.mul_rpow htheta.1.le he0.1.le] using hderiv

end CartisGouldToint.Chapter07.Section02
