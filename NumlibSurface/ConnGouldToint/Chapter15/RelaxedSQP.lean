import NumlibSurface.ConnGouldToint.Chapter08.Section03
import NumlibSurface.ConnGouldToint.Chapter15.Section04
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Relaxed linearization SQP algorithms -/

open scoped RealInnerProductSpace Topology
open ConnGouldToint.Chapter06 Optimization Filter

namespace ConnGouldToint.Chapter15

variable {E F W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The parameters for relaxed linearization SQP, including the
normal scaling and the sufficient model-decrease coefficients. -/
structure RelaxedSQPParams extends BTRParams where
  ξN : ℝ
  ξT : ℝ
  θ : ℝ
  ν : ℝ
  τ₁ : ℝ
  τ₂ : ℝ
  κN : ℝ
  κT : ℝ
  normal_fraction : ξN ∈ Set.Ioc 0 1
  tangential_fraction : ξT ∈ Set.Ioc 0 1
  scale_fraction : θ ∈ Set.Ioc 0 1
  penalty_fraction : ν ∈ Set.Ioo 0 1
  penalty_growth : 1 < τ₁
  penalty_increment : 0 < τ₂
  normal_bound : 0 < κN
  tangential_decrease : κT ∈ Set.Ioo 0 1

/-- The common trial and penalty construction of Algorithms 15.4.1–15.4.4.
The supplied null-space coordinates may be nonorthogonal. The trace
represents iterations with strictly positive predicted reduction. -/
structure RelaxedSQPTrials [CompleteSpace E] [CompleteSpace F]
    (f : E → ℝ) (c : E → F) (P : RelaxedSQPParams) (W : Type*)
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] where
  x : ℕ → E
  radius : ℕ → ℝ
  H : ℕ → E →L[ℝ] E
  N : ℕ → W →L[ℝ] E
  normalTrial : ℕ → E
  scale : ℕ → ℝ
  tangential : ℕ → E
  penaltyBase : ℕ → ℝ
  previousPenalty : ℕ → ℝ
  initial_penalty_pos : 0 < previousPenalty 0
  radius_pos : ∀ k, 0 < radius k
  symmetric : ∀ k, (H k).toLinearMap.IsSymmetric
  nullspace : ∀ k, LinearMap.range (N k).toLinearMap = LinearMap.ker (fderiv ℝ c (x k)).toLinearMap
  coordinates_injective : ∀ k, Function.Injective (N k)
  normal_equation : ∀ k, fderiv ℝ c (x k) (normalTrial k) + c (x k) = 0
  normal_bound : ∀ k, ‖normalTrial k‖ ≤ P.κN * ‖c (x k)‖
  normal_scaling : ∀ k, IsSQPNormalScaling (normalTrial k) P.θ P.ξN (radius k) (scale k)
  normal_radius : ∀ k, ‖scale k • normalTrial k‖ ≤ P.ξN * radius k
  tangential_kernel : ∀ k, fderiv ℝ c (x k) (tangential k) = 0
  tangential_radius : ∀ k, ‖tangential k‖ ≤ P.ξT * radius k
  tangential_decrease : ∀ k,
    let n := scale k • normalTrial k
    let g := gradient f (x k)
    let gN := (N k).adjoint (g + H k n)
    let HN := (N k).adjoint.comp ((H k).comp (N k))
    P.κT * ‖gN‖ * min (P.ξT * radius k / ‖N k‖) (‖gN‖ / (1 + ‖HN‖)) ≤
      sqpTangentialModel g (H k) n 0 - sqpTangentialModel g (H k) n (tangential k)

namespace RelaxedSQPTrials

variable [CompleteSpace E] [CompleteSpace F] [CompleteSpace W]
  {f : E → ℝ} {c : E → F} {P : RelaxedSQPParams}

/-- The scaled normal step (15.4.9). -/
noncomputable def normal (tr : RelaxedSQPTrials f c P W) (k : ℕ) : E :=
  tr.scale k • tr.normalTrial k

/-- The sum of the normal and tangential displacements. -/
noncomputable def step (tr : RelaxedSQPTrials f c P W) (k : ℕ) : E :=
  tr.normal k + tr.tangential k

/-- The penalty choice in Step 2. At zero normal decrease only the
baseline penalty is used. -/
noncomputable def penalty (tr : RelaxedSQPTrials f c P W) (k : ℕ) : ℝ :=
  let x := tr.x k
  let A := fderiv ℝ c x
  let g := gradient f x
  let H := tr.H k
  let n := tr.normal k
  let dN := sqpNormalModel (c x) A 0 - sqpNormalModel (c x) A n
  let dT := sqpTangentialModel g H n 0 - sqpTangentialModel g H n (tr.tangential k)
  let dq := quadraticModel (f x) g H.toLinearMap 0 - quadraticModel (f x) g H.toLinearMap n
  let required := if 0 < dN then
    max (tr.penaltyBase k) (sqpPenaltyThreshold P.ν dN dT dq)
    else tr.penaltyBase k
  sqpPenaltyUpdate P.τ₁ P.τ₂ required (tr.previousPenalty k)

/-- The overall model decrease predicted for the original trial. -/
noncomputable def prediction (tr : RelaxedSQPTrials f c P W) (k : ℕ) : ℝ :=
  let x := tr.x k
  let model := sqpOverallModel (f x) (gradient f x) (tr.H k) (c x) (fderiv ℝ c x)
    (tr.penalty k)
  model 0 - model (tr.step k)

/-- The merit ratio for a trial, using the original predicted decrease. -/
noncomputable def ratio (tr : RelaxedSQPTrials f c P W) (k : ℕ) (s : E) : ℝ :=
  reductionRatio (sqpMerit f c (tr.penalty k)) (tr.x k) s (tr.prediction k)

end RelaxedSQPTrials

variable [CompleteSpace E] [CompleteSpace F] [CompleteSpace W]

/-- The relaxed linearization run of Algorithm 15.4.1. -/
structure RelaxedSQPRun (f : E → ℝ) (c : E → F) (P : RelaxedSQPParams)
    (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] where
  trials : RelaxedSQPTrials f c P W
  penalty_update : ∀ k, trials.previousPenalty (k + 1) = trials.penalty k
  prediction_pos : ∀ k, 0 < trials.prediction k
  iterate_update : ∀ k, trials.x (k + 1) =
    acceptStep P.η₁ (sqpMerit f c (trials.penalty k)) (trials.x k) (trials.step k)
      (trials.prediction k)
  radius_update : ∀ k, BTRRadiusUpdate P.toBTRParams (trials.ratio k (trials.step k))
    (trials.radius k) (trials.radius (k + 1))

/-- The trial passed to the acceptance test. The optional norm cap
is (15.4.94). Rejecting an oversized correction keeps the original ratio. -/
noncomputable def relaxedSQPProbe (η ρ : ℝ) (smallNormal : Prop)
    (cap : Option ℝ) (s correction : E) : E :=
  open Classical in
  if ρ < η ∧ smallNormal ∧ ∀ r, cap = some r → ‖correction‖ ≤ r then
    s + correction
  else s

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- A successful uncorrected trial is always used. -/
theorem relaxedSQPProbe_of_successful_original {η ρ : ℝ} (h : η ≤ ρ)
    (smallNormal : Prop) (cap : Option ℝ) (s correction : E) :
    relaxedSQPProbe η ρ smallNormal cap s correction = s := by
  simp [relaxedSQPProbe, not_lt_of_ge h]

/-- Algorithm 15.4.2, optionally imposing the correction norm cap.
Both trials use the predicted reduction of the original step. -/
structure RelaxedSQPCorrectedRun (f : E → ℝ) (c : E → F) (P : RelaxedSQPParams)
    (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (cap : ℝ → Option ℝ := fun _ ↦ none) where
  trials : RelaxedSQPTrials f c P W
  χ : ℝ
  normal_test : χ ∈ Set.Ioo 0 P.θ
  correction : ℕ → E
  penalty_update : ∀ k, trials.previousPenalty (k + 1) = trials.penalty k
  prediction_pos : ∀ k, 0 < trials.prediction k
  iterate_update : ∀ k,
    let s := relaxedSQPProbe P.η₁ (trials.ratio k (trials.step k))
      (‖trials.normal k‖ ≤ χ * P.ξN * trials.radius k) (cap (trials.radius k))
      (trials.step k) (correction k)
    trials.x (k + 1) = acceptStep P.η₁ (sqpMerit f c (trials.penalty k))
      (trials.x k) s (trials.prediction k)
  radius_update : ∀ k,
    let s := relaxedSQPProbe P.η₁ (trials.ratio k (trials.step k))
      (‖trials.normal k‖ ≤ χ * P.ξN * trials.radius k) (cap (trials.radius k))
      (trials.step k) (correction k)
    BTRRadiusUpdate P.toBTRParams (trials.ratio k s) (trials.radius k) (trials.radius (k + 1))

namespace RelaxedSQPCorrectedRun

variable {f : E → ℝ} {c : E → F} {P : RelaxedSQPParams} {cap : ℝ → Option ℝ}

/-- The original or corrected displacement passed to the merit-ratio test. -/
noncomputable def probe (run : RelaxedSQPCorrectedRun f c P W cap) (k : ℕ) : E :=
  let tr := run.trials
  relaxedSQPProbe P.η₁ (tr.ratio k (tr.step k)) (‖tr.normal k‖ ≤ run.χ * P.ξN * tr.radius k)
    (cap (tr.radius k)) (tr.step k) (run.correction k)

/-- Either accepted trial achieves a decrease measured against the
prediction for the original step. -/
theorem merit_drop_of_successful (run : RelaxedSQPCorrectedRun f c P W cap) (k : ℕ)
    (h : P.η₁ ≤ run.trials.ratio k (run.probe k)) :
    P.η₁ * run.trials.prediction k ≤
      sqpMerit f c (run.trials.penalty k) (run.trials.x k) -
        sqpMerit f c (run.trials.penalty k) (run.trials.x (k + 1)) := by
  have hs : run.trials.x (k + 1) = run.trials.x k + run.probe k :=
    (run.iterate_update k).trans (acceptStep_of_le h)
  rw [hs]
  exact sub_le_of_le_reductionRatio (run.prediction_pos k) h

end RelaxedSQPCorrectedRun

/-- Algorithm 15.4.3. Full corrections use the supplied correction gradient
when the trial solves the standard SQP equations. Partial corrections use
zero. The KKT inverse is required to be uniformly bounded, as in the
derivation of the correction estimates. -/
structure RelaxedSQPStructuredRun (f : E → ℝ) (c : E → F) (P : RelaxedSQPParams)
    (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] where
  correctionFactor : ℝ
  correctionFactor_pos : 0 < correctionFactor
  corrected : RelaxedSQPCorrectedRun f c P W (fun Δ ↦ some (correctionFactor * Δ))
  multiplier : ℕ → F
  correctionShift : ℕ → E
  correctionHessian : ℕ → E →L[ℝ] E
  correctionGradient : ℕ → E
  shift_bound : ∃ C ≥ 0, ∀ k, ‖correctionShift k‖ ≤ C * ‖corrected.trials.step k‖
  correction_gradient_bound : ∀ xstar ystar,
    MapClusterPt (xstar, ystar) atTop (fun k ↦ (corrected.trials.x k, multiplier k)) →
    ∃ C ≥ 0, ∀ᶠ k in atTop,
      ‖correctionGradient k‖ ≤ C *
        max ‖corrected.trials.x k - xstar‖ ‖multiplier k - ystar‖ *
        ‖corrected.trials.step k‖
  correction_system : ∃ K > 0, ∀ k,
    let trials := corrected.trials
    trials.ratio k (trials.step k) < P.η₁ →
    ‖trials.normal k‖ ≤ corrected.χ * P.ξN * trials.radius k →
    let x := trials.x k
    let s := trials.step k
    let A := fderiv ℝ c x
    let Ac := fderiv ℝ c (x + correctionShift k)
    let Hc := correctionHessian k
    let u := corrected.correction k
    let standard := ∃ y : F, trials.H k s + gradient f x = A.adjoint y ∧ A s + c x = 0
    let gc := open Classical in if standard then correctionGradient k else 0
    (∃ y : F, Hc u - Ac.adjoint y = -gc ∧ Ac u = -c (x + s)) ∧
      ∀ b : E × F, ∃ z : E × F,
        Hc z.1 - Ac.adjoint z.2 = b.1 ∧ Ac z.1 = b.2 ∧ ‖z‖ ≤ K * ‖b‖ ∧
          ∀ z' : E × F, Hc z'.1 - Ac.adjoint z'.2 = b.1 → Ac z'.1 = b.2 → z' = z
  keep_radius : ∀ k,
    let trials := corrected.trials
    let s := relaxedSQPProbe P.η₁ (trials.ratio k (trials.step k))
      (‖trials.normal k‖ ≤ corrected.χ * P.ξN * trials.radius k)
      (some (correctionFactor * trials.radius k)) (trials.step k) (corrected.correction k)
    P.η₁ ≤ trials.ratio k s → trials.ratio k s < P.η₂ →
    trials.x (k + 1) = trials.x k + trials.step k →
    ‖trials.normal k‖ ≤ corrected.χ * P.ξN * trials.radius k →
    trials.radius (k + 1) = trials.radius k

/-- The radius is held when an original trial is accepted with a
moderate ratio and a small normal component. -/
theorem RelaxedSQPStructuredRun.radius_eq_of_original_moderate
    {f : E → ℝ} {c : E → F} {P : RelaxedSQPParams} (run : RelaxedSQPStructuredRun f c P W)
    (k : ℕ) (h₁ : P.η₁ ≤ run.corrected.trials.ratio k (run.corrected.trials.step k))
    (h₂ : run.corrected.trials.ratio k (run.corrected.trials.step k) < P.η₂)
    (hsmall : ‖run.corrected.trials.normal k‖ ≤ run.corrected.χ * P.ξN *
      run.corrected.trials.radius k) :
    run.corrected.trials.radius (k + 1) = run.corrected.trials.radius k := by
  let tr := run.corrected.trials
  have hp : run.corrected.probe k = tr.step k :=
    relaxedSQPProbe_of_successful_original h₁ _ _ _ _
  have h₁' : P.η₁ ≤ tr.ratio k (run.corrected.probe k) := by rw [hp]; exact h₁
  have h₂' : tr.ratio k (run.corrected.probe k) < P.η₂ := by rw [hp]; exact h₂
  have ha : tr.x (k + 1) = tr.x k + run.corrected.probe k :=
    (run.corrected.iterate_update k).trans (acceptStep_of_le h₁')
  have hs : tr.x (k + 1) = tr.x k + tr.step k := by rwa [hp] at ha
  exact run.keep_radius k h₁' h₂' hs hsmall

/-- Algorithm 15.4.4 follows the boxed rule and adds AA.2d to the
tangential step of Algorithm 15.4.3. -/
structure RelaxedSQPSecondOrderRun (f : E → ℝ) (c : E → F) (P : RelaxedSQPParams)
    (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] where
  run : RelaxedSQPStructuredRun f c P W
  κ : ℝ
  curvature_fraction : κ ∈ Set.Ioo 0 (1 / 2)
  curvature_decrease : ∀ k,
    let tr := run.corrected.trials
    let N := tr.N k
    let τ := Chapter08.hilbertRayleighFloor (N.adjoint.comp ((tr.H k).comp N))
    let m := sqpTangentialModel (gradient f (tr.x k)) (tr.H k) (tr.normal k)
    τ < 0 → -κ * τ * (tr.radius k) ^ 2 ≤ m 0 - m (tr.tangential k)

end ConnGouldToint.Chapter15
