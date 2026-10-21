import NumlibSurface.CartisGouldToint.Chapter06.Section01
import NumlibSurface.CartisGouldToint.Chapter04.Section01
import Numlib.Optimization.ConstrainedRegularization

/-!
# Chapter 6, Section 2: regularization with convex constraints

The two algorithms have different model residual tests. ARp-CC uses tolerance-scaled
restricted model measures; ARp1-CC uses step-scaled first-order feasible criticality.
Smoothness is required on an open neighborhood, while derivative Lipschitz control and the
objective lower bound are required only on the constraint set. First stopping results use
an explicit availability contract for actual legal finite prefixes.
-/

noncomputable section
open Optimization.ParameterUpdates Optimization.HigherOrderRegularization
open Optimization.ConstrainedRegularization Optimization.FeasibleCriticality
open Optimization.TaylorCriticality
namespace CartisGouldToint.Chapter06.Section02
open Section01
variable {n : ℕ}

/-- The assumptions f.DpL.C and f.bB.C, with the actual open extension and lower bound. -/
structure ConstrainedSmoothnessAssumptions (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Set (EuclideanSpace ℝ (Fin n))) (p : ℕ) (L low : ℝ) : Prop extends
    SmoothOn f C p L where
  lower : ∀ x ∈ C, low ≤ f x

/-- The unbounded model restricted sets (6.2.1)–(6.2.2). Translation retains the actual
constraint set, and restrictions use actual derivatives of the regularized model at `s`. -/
def modelRestrictedSteps (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Set (EuclideanSpace ℝ (Fin n))) (p : ℕ) (x s : EuclideanSpace ℝ (Fin n))
    (sigma : ℝ) (theta epsilon : Fin 3 → ℝ) (j : Fin 3) : Set (EuclideanSpace ℝ (Fin n)) :=
  restrictedFeasibleSteps (model f p x sigma) ((fun z => x + z) ⁻¹' C) s
    (fun i => theta i.castSucc) (fun i => epsilon i.castSucc) j

/-- Membership in the unbounded model restricted sets exposes exactly the two tests. -/
@[simp] theorem mem_modelRestrictedSteps (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Set (EuclideanSpace ℝ (Fin n))) (p : ℕ) (x s d : EuclideanSpace ℝ (Fin n))
    (sigma : ℝ) (theta epsilon : Fin 3 → ℝ) (j : Fin 3) :
    d ∈ modelRestrictedSteps f C p x s sigma theta epsilon j ↔
      x + s + d ∈ C ∧
      (1 ≤ j.val → |directionalDerivative (model f p x sigma) s 0 d| ≤
        theta 0 * epsilon 0) ∧
      (2 ≤ j.val → |directionalDerivative (model f p x sigma) s 1 d| ≤
        theta 1 * epsilon 1) := by
  simp [modelRestrictedSteps, add_assoc]

/-- The model measures (6.2.3)–(6.2.5) maximize negative actual directional derivatives
on the restricted feasible displacements intersected with the closed unit ball. -/
def modelRestrictedCriticality (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Set (EuclideanSpace ℝ (Fin n))) (p : ℕ) (x s : EuclideanSpace ℝ (Fin n))
    (sigma : ℝ) (theta epsilon : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  gapOn (fun d => -directionalDerivative (model f p x sigma) s j d)
    (modelRestrictedSteps f C p x s sigma theta epsilon j ∩ unitBall)

/-- Translation identifies the model measures with the preceding section's compact gap. -/
theorem modelRestrictedCriticality_eq_constrainedCriticality
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (C : Set (EuclideanSpace ℝ (Fin n)))
    (p : ℕ) (x s : EuclideanSpace ℝ (Fin n)) (sigma : ℝ)
    (theta epsilon : Fin 3 → ℝ) (j : Fin 3) :
    modelRestrictedCriticality f C p x s sigma theta epsilon j =
      constrainedCriticality (model f p x sigma) ((fun z => x + z) ⁻¹' C) s
        (fun i => theta i.castSucc) (fun i => epsilon i.castSucc) j := rfl

/-- The first model domain contains precisely the feasible displacements from the trial point. -/
@[simp] theorem modelRestrictedSteps_first (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Set (EuclideanSpace ℝ (Fin n))) (p : ℕ) (x s : EuclideanSpace ℝ (Fin n))
    (sigma : ℝ) (theta epsilon : Fin 3 → ℝ) :
    modelRestrictedSteps f C p x s sigma theta epsilon 0 = feasibleSteps C (x + s) := by
  ext d
  simp [modelRestrictedSteps, feasibleSteps, add_assoc]

/-- The first model measure is the canonical feasible criticality of the actual model gradient. -/
@[simp] theorem modelRestrictedCriticality_first (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Set (EuclideanSpace ℝ (Fin n))) (p : ℕ) (x s : EuclideanSpace ℝ (Fin n))
    (sigma : ℝ) (theta epsilon : Fin 3 → ℝ) :
    modelRestrictedCriticality f C p x s sigma theta epsilon 0 =
      feasibleCriticality C (x + s) (fderiv ℝ (model f p x sigma) s) := by
  simp [modelRestrictedCriticality, feasibleCriticality, feasibleSteps_inter_unitBall]

/-- Executed ARp-CC laws, before imposing a terminal test. Index `q` activates orders
one through `q.val+1`; inactive infinite tolerances are represented by omitting their tests. -/
structure arpCCPrefix (params : Chapter02.Section04.regularizationParameters)
    (p : ℕ) (q : Fin 3) (tau : Fin 2 → ℝ) (theta epsilon : Fin 3 → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (C : Set (EuclideanSpace ℝ (Fin n)))
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (sigma : ℕ → ℝ) (N : ℕ) : Prop extends
    toFeasibleTrial :
      Optimization.ConstrainedRegularization.TrialPrefix params p f C x s sigma N where
  degree_ge : q.val + 1 ≤ p
  tau_mem : ∀ i, tau i ∈ Set.Ioo 0 1
  theta_mem : ∀ j, theta j ∈ Set.Ioo 0 1
  epsilon_pos : ∀ j ≤ q, 0 < epsilon j
  compatibility : ∀ i, (1 + tau i) / 2 ≤ theta i.castSucc
  residuals : ∀ k < N, ∀ j ≤ q,
    modelRestrictedCriticality f C p (x k) (s k) (sigma k) theta epsilon j ≤ theta j * epsilon j

/-- Algorithm 6.2.1, with actual feasible trials, strict model decrease, exact acceptance
and parameter intervals, and the first source constrained stopping test. -/
structure algorithm_6_2_1 (params : Chapter02.Section04.regularizationParameters)
    (p : ℕ) (q : Fin 3) (tau : Fin 2 → ℝ) (theta epsilon : Fin 3 → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (C : Set (EuclideanSpace ℝ (Fin n)))
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (sigma : ℕ → ℝ) (N : ℕ) : Prop extends
    arpCCPrefix params p q tau theta epsilon f C x s sigma N where
  terminal : IsApproximateConstrainedMinimizer f C (x N) tau epsilon q
  first : ∀ k < N, ¬IsApproximateConstrainedMinimizer f C (x k) tau epsilon q

/-- Algorithm 6.2.2 uses (6.2.29), the step-scaled feasible first derivative residual.
It retains the fixed source `tau1` and compatibility `(1+tau1)/2 ≤ theta1` from Algorithm
6.2.1, together with actual model decrease, trials, ratios and parameter intervals. -/
structure algorithm_6_2_2 (params : Chapter02.Section04.regularizationParameters)
    (p : ℕ) (tau theta epsilon : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Set (EuclideanSpace ℝ (Fin n))) (x s : ℕ → EuclideanSpace ℝ (Fin n))
    (sigma : ℕ → ℝ) (N : ℕ) : Prop extends
    FirstOrderRun params p theta epsilon f C x s sigma N where
  tau_mem : tau ∈ Set.Ioo 0 1
  compatibility : (1 + tau) / 2 ≤ theta

variable {params : Chapter02.Section04.regularizationParameters} {p N : ℕ}
  {theta epsilon L low : ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
  {C : Set (EuclideanSpace ℝ (Fin n))} {x s : ℕ → EuclideanSpace ℝ (Fin n)}
  {sigma : ℕ → ℝ}

/-- Lemma 6.2.4: an accepted actual ARp1-CC step pays the factorial-normalized constant
multiplying the true constrained criticality at its successor. Only f.DpL.C is needed. -/
theorem lemma_6_2_4 (h : FirstOrderPrefix params p theta epsilon f C x s sigma N)
    (hf : SmoothOn f C p L) (hC : ConvexConstraintAssumptions C)
    {k : ℕ} (hk : k < N) (hs : params.eta1 ≤ ratio f p (x k) (s k)) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    decreaseConstant params p 1 L S theta *
      feasibleCriticality C (x (k + 1)) (fderiv ℝ f (x (k + 1))) ^
        (((p + 1 : ℕ) : ℝ) / p) ≤ f (x k) - f (x (k + 1)) :=
  h.criticality_decrease hf hC.isClosed hC.convex hk hs
    (h.toFeasibleTrial.sigma_upper hf hC.convex (by omega))

/-- The source constant (4.1.32), with normalization `(p+1)!` forced by the actual model. -/
theorem lemma_6_2_4_constant (hp : 1 ≤ p) (S : ℝ) :
    decreaseConstant params p 1 L S theta =
      params.eta1 * params.sigmaMin / ((p + 1).factorial : ℝ) *
        ((p.factorial : ℝ) / (L + S + theta * (p.factorial : ℝ))) ^
          (((p + 1 : ℕ) : ℝ) / p) := by
  have he : p - 1 + 1 = p := by omega
  rw [decreaseConstant_eq_factorial, he]

/-- Theorem 6.2.5: legal available ARp1-CC prefixes force the first stop with actual objective
and cached derivative budgets. Availability is explicit, as in the finite-prefix form of 4.1.5;
it supplies legal executions without postulating a decrease, count, or termination oracle. -/
theorem theorem_6_2_5 {tau : ℝ} (htau : tau ∈ Set.Ioo 0 1)
    (hcompat : (1 + tau) / 2 ≤ theta) (hf : ConstrainedSmoothnessAssumptions f C p L low)
    (hC : ConvexConstraintAssumptions C)
    (hprefix : ∀ N, (∀ k < N,
      ¬feasibleCriticality C (x k) (fderiv ℝ f (x k)) ≤ epsilon) →
      FirstOrderPrefix params p theta epsilon f C x s sigma N) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := firstOrderComplexityConstant params p L S theta *
      ((f (x 0) - low) / epsilon ^ (((p + 1 : ℕ) : ℝ) / p))
    let A := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let B := Real.log (S / sigma 0) / Real.log params.gamma2
    ∃ K, algorithm_6_2_2 params p tau theta epsilon f C x s sigma K ∧
      (functionEvaluations K : ℝ) ≤ A * Q + A + B + 1 ∧
      (derivativeEvaluations params p f x s K : ℝ) ≤ Q + 2 := by
  obtain ⟨K, hrun, hF, hD⟩ :=
    Optimization.ConstrainedRegularization.exists_first_order_run_with_cost hf.toSmoothOn
      hC.isClosed hC.convex hf.lower hprefix
  exact ⟨K, { toFirstOrderRun := hrun, tau_mem := htau, compatibility := hcompat }, hF, hD⟩

/-- Corrected bounded-direction version of (6.2.18). The original unrestricted-length
claim remains marked wrong in the plan; the unit-ball restriction is essential. -/
theorem lemma_6_2_1_first_bounded_directions
    {q : Fin 3} {tau : Fin 2 → ℝ} {th ep : Fin 3 → ℝ}
    (h : arpCCPrefix params p q tau th ep f C x s sigma N)
    (hf : SmoothOn f C p L) (hC : ConvexConstraintAssumptions C)
    {k : ℕ} (hk : k < N) (hs : params.eta1 ≤ ratio f p (x k) (s k))
    {d : EuclideanSpace ℝ (Fin n)}
    (hd : d ∈ restrictedFeasibleSteps f C (x (k + 1)) tau
      (fun i => ep i.castSucc) 1 ∩ unitBall) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    |directionalDerivative (model f p (x k) (sigma k)) (s k) 0 d| ≤
      (L + S) / (p.factorial : ℝ) * ‖s k‖ ^ p + tau 0 * ep 0 := by
  have hp : 1 ≤ p := by have := h.degree_ge; omega
  have he : p - 1 + 1 = p := by omega
  have hdif := h.toFeasibleTrial.derivative_difference hf hC.convex (j := 1)
    (by omega) (by omega) hp hk (h.toFeasibleTrial.sigma_upper hf hC.convex (by omega))
  have ht : |iteratedFDeriv ℝ 1 f (x k + s k) (fun _ => d)| ≤ tau 0 * ep 0 := by
    have hb := hd.1.2.1 (by decide)
    rw [h.iterate k hk, ite_eq_left hs] at hb
    exact hb
  have hb := abs_diagonal_le_add_error (iteratedFDeriv ℝ 1 f (x k + s k))
    (iteratedFDeriv ℝ 1 (model f p (x k) (sigma k)) (s k))
    (mem_unitBall.mp hd.2) hdif ht
  simpa only [directionalDerivative, Fin.val_zero, zero_add, he] using hb

/-- Corrected bounded-direction version of (6.2.19), at every activated second order.
The bound concerns the actual model Hessian on the objective restricted unit displacements. -/
theorem lemma_6_2_1_second_bounded_directions
    {q : Fin 3} {tau : Fin 2 → ℝ} {th ep : Fin 3 → ℝ}
    (h : arpCCPrefix params p q tau th ep f C x s sigma N) (hq : 1 ≤ q.val)
    (hf : SmoothOn f C p L) (hC : ConvexConstraintAssumptions C)
    {k : ℕ} (hk : k < N) (hs : params.eta1 ≤ ratio f p (x k) (s k))
    {d : EuclideanSpace ℝ (Fin n)}
    (hd : d ∈ restrictedFeasibleSteps f C (x (k + 1)) tau
      (fun i => ep i.castSucc) 2 ∩ unitBall) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    |directionalDerivative (model f p (x k) (sigma k)) (s k) 1 d| ≤
      (L + S) / ((p - 1).factorial : ℝ) * ‖s k‖ ^ (p - 1) + tau 1 * ep 1 := by
  have hp : 2 ≤ p := by have := h.degree_ge; omega
  have he : p - 2 + 1 = p - 1 := by omega
  have hdif := h.toFeasibleTrial.derivative_difference hf hC.convex (j := 2)
    (by omega) (by omega) hp hk (h.toFeasibleTrial.sigma_upper hf hC.convex (by omega))
  have ht : |iteratedFDeriv ℝ 2 f (x k + s k) (fun _ => d)| ≤ tau 1 * ep 1 := by
    have hb := hd.1.2.2 (by decide)
    rw [h.iterate k hk, ite_eq_left hs] at hb
    exact hb
  have hb := abs_diagonal_le_add_error (iteratedFDeriv ℝ 2 f (x k + s k))
    (iteratedFDeriv ℝ 2 (model f p (x k) (sigma k)) (s k))
    (mem_unitBall.mp hd.2) hdif ht
  simpa only [directionalDerivative, Fin.val_one, Nat.reduceAdd, he] using hb

end CartisGouldToint.Chapter06.Section02
