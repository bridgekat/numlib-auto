import Numlib.Optimization.ConstrainedResidualRegularizationComplexity
import NumlibSurface.CartisGouldToint.Chapter06.Section02
import NumlibSurface.CartisGouldToint.Chapter05.Section01

/-!
# Chapter 6, Section 3: convexly constrained least residual norms

The residual-power objective and constrained first derivative test are the actual source
quantities. The small-residual alternative precedes division. Legal ARp1-CC trials and the
same residual-root arithmetic as Section 5.1 yield the two exact evaluation budgets.
-/

noncomputable section
namespace CartisGouldToint.Chapter06.Section03
open Optimization HigherOrderRegularization ParameterUpdates
open ConstrainedRegularization ConstrainedResidualRegularization

variable {n m : ℕ}

/-- The alternatives (6.3.1)–(6.3.2), including feasibility and the early residual-small test. -/
abbrev IsApproximateConstrainedResidualMinimizer
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (C : Set (EuclideanSpace ℝ (Fin n))) (ell epsilon0 epsilon1 : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ConstrainedResidualRegularization.Stationary C epsilon0 epsilon1 r ell x

/-- Algorithm 6.3.1 applies the actual ARp1-CC model and feasible model-gradient test to
Phi_ell, replacing only termination by (6.3.1)–(6.3.2). The source tau/theta compatibility
is inherited from Algorithm 6.2.2. Smoothness Phi_ell.DpL.C is a theorem hypothesis. -/
structure algorithm_6_3_1 (params : Chapter02.Section04.regularizationParameters)
    (p : ℕ) (tau theta epsilon0 epsilon1 : ℝ)
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (ell : ℝ)
    (C : Set (EuclideanSpace ℝ (Fin n)))
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (sigma : ℕ → ℝ) (N : ℕ) : Prop extends
    IsRun params p theta epsilon0 epsilon1 r ell C x s sigma N where
  tau_mem : tau ∈ Set.Ioo 0 1
  compatibility : (1 + tau) / 2 ≤ theta

/-- Theorem 6.3.1: fixed beta and the admissible choices (5.1.38) or (5.1.39) give
positive constants before either tolerance is chosen. Actual legal-prefix availability is
the model-solver contract. Residual calls have the exact maximum/minimum quotient, and each
cached residual derivative order has the same quotient plus two. Formula (6.3.3) uses the
normalized feasible criticality, as required by (6.3.2) and the Section 5.1 derivation. -/
theorem theorem_6_3_1
    {params : Chapter02.Section04.regularizationParameters} {p i : ℕ}
    {tau theta ell beta L sigmaInitial : ℝ}
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    (htau : tau ∈ Set.Ioo 0 1) (htheta : theta ∈ Set.Ioo 0 1)
    (hcompat : (1 + tau) / 2 ≤ theta) (hsigma : 0 < sigmaInitial)
    (hf : SmoothOn (Chapter05.Section01.residualPowerObjective r ell) C p L)
    (hC : Section01.ConvexConstraintAssumptions C) (hell : 1 < ell)
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (hchoice : (ell = p ∧ Real.logb 2 p < i) ∨
      ∃ o : ℕ, Odd o ∧ p = o * 2 ^ i ∧ ell = 1 + (o : ℝ) * ((2 : ℝ) ^ i - 1)) :
    let S := max sigmaInitial (params.gamma3 * (L / (1 - params.eta2)))
    let kS := ResidualRegularization.complexityConstant params 1 p i ell beta L S
      (fun _ => theta)
    let A := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let B := Real.log (S / sigmaInitial) / Real.log params.gamma2
    0 < kS ∧ 0 < A * kS ∧ 0 < A + B + 1 ∧
    ∀ epsilon0 ∈ Set.Ioc (0 : ℝ) 1, ∀ epsilon1 ∈ Set.Ioc (0 : ℝ) 1,
      ∀ (x s : ℕ → EuclideanSpace ℝ (Fin n)) (sigma : ℕ → ℝ),
      sigma 0 = sigmaInitial →
      (∀ N, (∀ k < N,
        ¬IsApproximateConstrainedResidualMinimizer r C ell epsilon0 epsilon1 (x k)) →
        ConstrainedResidualRegularization.RunPrefix params p theta epsilon0 epsilon1
          r ell C x s sigma N) →
      ∃ K, algorithm_6_3_1 params p tau theta epsilon0 epsilon1 r ell C x s sigma K ∧
        let Q := max (‖r (x 0)‖ ^ ((1 : ℝ) / (2 : ℝ) ^ i))
          (‖r (x 0)‖ ^ (1 - (ell - 1) / p)) /
          min (epsilon0 ^ ((1 : ℝ) / (2 : ℝ) ^ i))
            (epsilon1 ^ (((p + 1 : ℕ) : ℝ) / p))
        (ResidualRegularization.residualFunctionEvaluations K : ℝ) ≤ A * kS * Q +
          (A + B + 1) ∧
        (ResidualRegularization.residualDerivativeEvaluations params p r ell x s K : ℝ) ≤
          kS * Q + 2 := by
  dsimp only
  let S := max sigmaInitial (params.gamma3 * (L / (1 - params.eta2)))
  have hS : 0 ≤ S := hsigma.le.trans (le_max_left _ _)
  have hKS := ResidualRegularization.complexityConstant_pos
    (params := params) (q := 1) (p := p) (i := i) (ell := ell) (beta := beta)
    (L := L) (S := S) (theta := fun _ => theta) (by omega) hb0 hb1 hf.nonneg hS
    (fun _ => htheta.1)
  have hA : 0 < 1 + |Real.log params.gamma1| / Real.log params.gamma2 :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (div_nonneg (abs_nonneg _) (Real.log_pos params.one_lt_gamma2).le)
  have hB : 0 ≤ Real.log (S / sigmaInitial) / Real.log params.gamma2 :=
    div_nonneg (Real.log_nonneg ((one_le_div₀ hsigma).mpr (le_max_left _ _)))
      (Real.log_pos params.one_lt_gamma2).le
  refine ⟨hKS, mul_pos hA hKS, by linarith, ?_⟩
  intro epsilon0 _ epsilon1 _ x s sigma hinit hprefix
  have hi : 0 ≤ Optimization.residualDescentExponent p ell i 1 := by
    obtain ⟨hsimple, hdyadic, _⟩ := Chapter05.Section01.lemma_5_1_6 hf.degree_pos hell
    rcases hchoice with ⟨he, hi⟩ | hchoice
    · simpa only [Chapter05.Section01.residualDescentExponent, Nat.cast_one] using
        (hsimple he hi).le
    · simpa only [Chapter05.Section01.residualDescentExponent, Nat.cast_one] using
        (hdyadic hchoice).1.ge
  obtain ⟨K, hrun, hF, hD⟩ :=
    ConstrainedResidualRegularization.exists_first_run_with_cost hf hC.isClosed hC.convex
      hb0 hb1 hi hprefix
  refine ⟨K, { toIsRun := hrun, tau_mem := htau, compatibility := hcompat }, ?_, ?_⟩
  · rw [hinit] at hF
    dsimp only [S] at *
    nlinarith [hF]
  · simpa only [hinit] using hD

end CartisGouldToint.Chapter06.Section03
