/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter15.Section04

/-! # Composite-step and infeasibility-reducing SQP variants

The Byrd–Omojokun variants replace individual step conditions in the inherited
iteration. The infeasibility-reducing variant uses an augmented merit on the
primal and multiplier variables and a corrected penalty threshold.
-/

open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter15

open Chapter06

/-- Parameters common to the SQP variants. -/
structure SQPVariantParams extends BTRParams where
  ν : ℝ
  τ₁ : ℝ
  τ₂ : ℝ
  nu_pos : 0 < ν
  nu_lt_one : ν < 1
  tau₁_gt_one : 1 < τ₁
  tau₂_pos : 0 < τ₂

section CompositeSteps

variable {E F U V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The replacement normal step in Algorithm 15.4.5. The coordinate maps R
and N give its row-space and null-space components. -/
structure ByrdOmojokunNormalStep (c : F) (A : E →L[ℝ] F) (p : Seminorm ℝ E)
    (ξN Δ κ β κdrs : ℝ) (R : U →ₗ[ℝ] E) (N : V →ₗ[ℝ] E)
    (n : E) (nR : U) (nN : V) : Prop where
  radius : p n ≤ ξN * Δ
  decrease : κ * (‖A.adjoint c‖ / ‖c‖) *
    min (ξN * Δ) (‖A.adjoint c‖ / β) ≤ ‖c‖ - sqpNormalModel c A n
  row_range : LinearMap.range R = LinearMap.range A.adjoint.toLinearMap
  null_range : LinearMap.range N = LinearMap.ker A.toLinearMap
  row_injective : Function.Injective R
  null_injective : Function.Injective N
  decomposition : n = R nR + N nN
  null_bound : ‖nN‖ ≤ κdrs * ‖nR‖
  stationary_row : A.adjoint c = 0 → nR = 0

omit [CompleteSpace V] in
/-- A normal-stationary point has zero normal step under AA.1k. -/
theorem ByrdOmojokunNormalStep.eq_zero_of_normal_stationary
    {c : F} {A : E →L[ℝ] F} {p : Seminorm ℝ E} {ξN Δ κ β κdrs : ℝ}
    {R : U →ₗ[ℝ] E} {N : V →ₗ[ℝ] E} {n : E} {nR : U} {nN : V}
    (h : ByrdOmojokunNormalStep c A p ξN Δ κ β κdrs R N n nR nN)
    (hz : A.adjoint c = 0) : n = 0 := by
  have hr := h.stationary_row hz
  have hn : nN = 0 := norm_le_zero_iff.mp (by simpa [hr] using h.null_bound)
  simp [h.decomposition, hr, hn]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The replacement tangential step in Algorithm 15.4.7 has both
Cauchy decrease and the extra negative-curvature decrease. -/
structure SQPSecondOrderTangentialStep (A : E →L[ℝ] F) (g n t : E) (H : E →L[ℝ] E)
    (p : Seminorm ℝ E) (ξT Δ reducedGradient basisNorm κT β κ₂ τ : ℝ) : Prop where
  tangent : A t = 0
  radius : p t ≤ ξT * Δ
  cauchy : κT * reducedGradient * min (ξT * Δ / basisNorm) (reducedGradient / β) ≤
    sqpTangentialModel g H n 0 - sqpTangentialModel g H n t
  negative_curvature : τ < 0 → -(κ₂ * τ * Δ ^ 2) ≤
    sqpTangentialModel g H n 0 - sqpTangentialModel g H n t

omit [CompleteSpace E] [CompleteSpace F] in
/-- The normal and tangential steps and the local model data for the
Byrd–Omojokun variants. The ratio uses the sum of the two steps. -/
structure SQPCompositeTrial (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] where
  x : E
  n : E
  t : E
  g : E
  A : E →L[ℝ] F
  H : E →L[ℝ] E
  p : Seminorm ℝ E
  radius : ℝ
  previousPenalty : ℝ
  penaltyBase : ℝ
  norm_separates : ∀ v, p v = 0 → v = 0

omit [CompleteSpace E] [CompleteSpace F] in
/-- The inherited penalty update at a composite trial. -/
noncomputable def SQPCompositeTrial.penalty (tr : SQPCompositeTrial E F) (P : SQPVariantParams)
    (f : E → ℝ) (c : E → F) : ℝ :=
  let normal := ‖c tr.x‖ - sqpNormalModel (c tr.x) tr.A tr.n
  let tangential := sqpTangentialModel tr.g tr.H tr.n 0 - sqpTangentialModel tr.g tr.H tr.n tr.t
  let dq := f tr.x - quadraticModel (f tr.x) tr.g tr.H.toLinearMap tr.n
  let required := if 0 < normal then max tr.penaltyBase (sqpPenaltyThreshold P.ν normal tangential dq)
    else tr.penaltyBase
  sqpPenaltyUpdate P.τ₁ P.τ₂ required tr.previousPenalty

omit [CompleteSpace E] [CompleteSpace F] in
/-- The original trial determines the predicted decrease, including when the
subsequent acceptance test uses a second-order correction. -/
noncomputable def SQPCompositeTrial.prediction (tr : SQPCompositeTrial E F) (f : E → ℝ)
    (c : E → F) (σ : ℝ) : ℝ :=
  let m := sqpOverallModel (f tr.x) tr.g tr.H (c tr.x) tr.A σ
  m 0 - m (tr.n + tr.t)

omit [CompleteSpace E] [CompleteSpace F] in
/-- First-order tangential selection in the composite variants. -/
def SQPCompositeTrial.cauchy (tr : SQPCompositeTrial E F)
    (ξT reducedGradient basisNorm κT β : ℝ) : Prop :=
  tr.A tr.t = 0 ∧ tr.p tr.t ≤ ξT * tr.radius ∧
    κT * reducedGradient * min (ξT * tr.radius / basisNorm) (reducedGradient / β) ≤
      sqpTangentialModel tr.g tr.H tr.n 0 - sqpTangentialModel tr.g tr.H tr.n tr.t

/-- One iteration of Algorithm 15.4.5, with the Byrd–Omojokun normal step
and the uncorrected composite trial used in the acceptance test. -/
def algorithm_15_4_5 (P : SQPVariantParams) (f : E → ℝ) (c : E → F)
    (tr : SQPCompositeTrial E F) (ξN ξT κN βN κdrs κT : ℝ)
    (R : U →ₗ[ℝ] E) (N : V →L[ℝ] E) (nR : U) (nN : V) (x' : E) (Δ' σ : ℝ) : Prop :=
  let pred := tr.prediction f c σ
  let merit := sqpMerit f c σ
  let s := tr.n + tr.t
  let gN := ‖N.adjoint (tr.g + tr.H tr.n)‖
  let HN := N.adjoint.comp (tr.H.comp N)
  0 < tr.radius ∧ 0 < tr.previousPenalty ∧
    ξN ∈ Set.Ioc 0 1 ∧ ξT ∈ Set.Ioc 0 1 ∧ 0 < κN ∧ 0 < βN ∧ 0 ≤ κdrs ∧ 0 < κT ∧
    tr.A = fderiv ℝ c tr.x ∧ tr.g = gradient f tr.x ∧
    ByrdOmojokunNormalStep (c tr.x) tr.A tr.p ξN tr.radius κN βN κdrs R N.toLinearMap tr.n nR nN ∧
    tr.cauchy ξT gN ‖N‖ κT (quadraticCurvatureBound HN) ∧
    σ = tr.penalty P f c ∧ 0 < pred ∧
    x' = Optimization.acceptStep P.η₁ merit tr.x s pred ∧
    BTRRadiusUpdate P.toBTRParams (Optimization.reductionRatio merit tr.x s pred) tr.radius Δ'

/-- One iteration of Algorithm 15.4.6. The correction selector supplies a
full or partial correction as appropriate for the original SQP step. The
linearized-feasibility test and norm cap determine whether it is tried. -/
def algorithm_15_4_6 (P : SQPVariantParams) (f : E → ℝ) (c : E → F)
    (tr : SQPCompositeTrial E F) (ξN ξT κN βN κdrs κT ηCS : ℝ)
    (R : U →ₗ[ℝ] E) (N : V →L[ℝ] E) (nR : U) (nN : V)
    (correctionOK : E → Prop) (correction x' : E) (Δ' σ : ℝ) : Prop :=
  open Classical in
  let pred := tr.prediction f c σ
  let merit := sqpMerit f c σ
  let s := tr.n + tr.t
  let exactNormal := c tr.x + tr.A tr.n = 0
  let original := Optimization.reductionRatio merit tr.x s pred
  let tested := if original < P.η₁ ∧ exactNormal ∧ tr.p correction ≤ ηCS * tr.radius
    then s + correction else s
  let ρ := Optimization.reductionRatio merit tr.x tested pred
  let gN := ‖N.adjoint (tr.g + tr.H tr.n)‖
  let HN := N.adjoint.comp (tr.H.comp N)
  0 < tr.radius ∧ 0 < tr.previousPenalty ∧
    ξN ∈ Set.Ioc 0 1 ∧ ξT ∈ Set.Ioc 0 1 ∧ 0 < κN ∧ 0 < βN ∧ 0 ≤ κdrs ∧ 0 < κT ∧
    0 < ηCS ∧ tr.A = fderiv ℝ c tr.x ∧ tr.g = gradient f tr.x ∧
    ByrdOmojokunNormalStep (c tr.x) tr.A tr.p ξN tr.radius κN βN κdrs R N.toLinearMap tr.n nR nN ∧
    (tr.p tr.n = ξN * tr.radius ∨ exactNormal) ∧
    tr.cauchy ξT gN ‖N‖ κT (quadraticCurvatureBound HN) ∧
    (original < P.η₁ → exactNormal → correctionOK correction) ∧
    σ = tr.penalty P f c ∧ 0 < pred ∧
    x' = Optimization.acceptStep P.η₁ merit tr.x tested pred ∧
    BTRRadiusUpdate P.toBTRParams ρ tr.radius Δ' ∧
    (P.η₁ ≤ ρ → ρ < P.η₂ → x' = tr.x + s → exactNormal → Δ' = tr.radius)

/-- Algorithm 15.4.7 adds AA.2d to the corrected Byrd–Omojokun iteration. -/
def algorithm_15_4_7 (P : SQPVariantParams) (f : E → ℝ) (c : E → F)
    (tr : SQPCompositeTrial E F) (ξN ξT κN βN κdrs κT κ₂ τ ηCS : ℝ)
    (R : U →ₗ[ℝ] E) (N : V →L[ℝ] E) (nR : U) (nN : V)
    (correctionOK : E → Prop) (correction x' : E) (Δ' σ : ℝ) : Prop :=
  let HN := N.adjoint.comp (tr.H.comp N)
  algorithm_15_4_6 P f c tr ξN ξT κN βN κdrs κT ηCS R N nR nN correctionOK correction x' Δ' σ ∧
    0 < κ₂ ∧ τ = sInf ((fun v : V ↦ ⟪v, HN v⟫) '' Metric.sphere 0 1) ∧
    (τ < 0 → -(κ₂ * τ * tr.radius ^ 2) ≤
      sqpTangentialModel tr.g tr.H tr.n 0 - sqpTangentialModel tr.g tr.H tr.n tr.t)

end CompositeSteps

section Infeasibility

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The augmented merit in the convention where the Lagrangian subtracts
the constraint pairing. -/
noncomputable def infeasibilitySQPMerit (f : E → ℝ) (c : E → F)
    (σ : ℝ) (z : E × F) : ℝ :=
  f z.1 - ⟪c z.1, z.2⟫ + (σ / 2) * ‖c z.1‖ ^ 2

/-- The augmented model counts the squared residual penalty once.
Its constant is the unaugmented Lagrangian value at the center. -/
noncomputable def infeasibilitySQPModel (f₀ : ℝ) (c y : F) (g : E) (H : E →L[ℝ] E)
    (A : E →L[ℝ] F) (σ : ℝ) (step : E × F) : ℝ :=
  quadraticModel (f₀ - ⟪c, y⟫) g H.toLinearMap step.1 -
    ⟪c + A step.1, step.2⟫ + (σ / 2) * ‖c + A step.1‖ ^ 2

/-- The augmented model and merit agree at the center. -/
theorem infeasibilitySQPModel_zero (f : E → ℝ) (c : E → F) (z : E × F)
    (g : E) (H : E →L[ℝ] E) (A : E →L[ℝ] F) (σ : ℝ) :
    infeasibilitySQPModel (f z.1) (c z.1) z.2 g H A σ 0 =
      infeasibilitySQPMerit f c σ z := by
  simp [infeasibilitySQPModel, infeasibilitySQPMerit, quadraticModel]

/-- The total predicted decrease is the penalty-weighted squared residual
decrease minus the change in the other model terms. -/
theorem infeasibilitySQPModel_drop (f₀ : ℝ) (c y : F) (g : E) (H : E →L[ℝ] E)
    (A : E →L[ℝ] F) (σ : ℝ) (step : E × F) :
    infeasibilitySQPModel f₀ c y g H A σ 0 - infeasibilitySQPModel f₀ c y g H A σ step =
      (σ / 2) * (‖c‖ ^ 2 - ‖c + A step.1‖ ^ 2) -
        (quadraticModel 0 g H.toLinearMap step.1 - ⟪c + A step.1, step.2⟫) := by
  simp [infeasibilitySQPModel, quadraticModel]
  ring

/-- With the objective term δF written as a change, its sign in the penalty
threshold is positive. A zero normal reduction leaves the penalty alone. -/
noncomputable def infeasibilitySQPPenaltyRequired (ν δN δF base : ℝ) : ℝ :=
  max base (2 * δF / ((1 - ν) * δN))

/-- For positive normal decrease, the penalty threshold is equivalent to
the base bound and (15.4.171). -/
theorem infeasibilitySQPPenaltyRequired_le_iff {ν δN δF base σ : ℝ}
    (hν : ν < 1) (hN : 0 < δN) :
    infeasibilitySQPPenaltyRequired ν δN δF base ≤ σ ↔
      base ≤ σ ∧ (ν * σ / 2) * δN ≤ (σ / 2) * δN - δF := by
  rw [infeasibilitySQPPenaltyRequired, max_le_iff,
    div_le_iff₀ (mul_pos (sub_pos.mpr hν) hN)]
  constructor <;> rintro ⟨hbase, h⟩ <;> exact ⟨hbase, by linarith only [h]⟩

/-- The printed negative sign can leave the penalty too small for (15.4.171). -/
theorem infeasibilitySQPPenalty_printed_sign_counterexample :
    max (1 : ℝ) (-2 / ((1 - 1 / 2) * 1)) ≤ 1 ∧
      ¬ ((1 / 2 : ℝ) * 1 / 2) * 1 ≤ (1 / 2 : ℝ) * 1 - 1 := by
  norm_num [max_def]

/-- One iteration of Algorithm 15.4.8. Step selection is supplied by an
approximate solver for the stated feasible set, and the multiplier step is
free. The state contains the primal and dual variables, the trust-region
radius, and the carried penalty. A zero predicted decrease ends this
ratio-based transition. -/
def algorithm_15_4_8 (P : SQPVariantParams) (f : E → ℝ) (c : E → F)
    (approximate : (E → ℝ) → Set E → E → Prop)
    (A : E →L[ℝ] F) (g : E) (H : E →L[ℝ] E) (p : Seminorm ℝ E) (base : ℝ)
    (z z' : E × F) (Δ Δ' previous σ : ℝ) (n : E) (step : E × F) : Prop :=
  let residual := c z.1
  let θ := ‖residual + A n‖
  let q := quadraticModel 0 g H.toLinearMap
  let δN := ‖residual‖ ^ 2 - ‖residual + A step.1‖ ^ 2
  let δF := q step.1 - ⟪residual + A step.1, step.2⟫
  let required := infeasibilitySQPPenaltyRequired P.ν δN δF base
  let m := infeasibilitySQPModel (f z.1) residual z.2 g H A σ
  let predicted := m 0 - m step
  let ρ := Optimization.reductionRatio (infeasibilitySQPMerit f c σ) z step predicted
  0 < Δ ∧ 0 < previous ∧
    A = fderiv ℝ c z.1 ∧
    (∀ v, ⟪g, v⟫ = fderiv ℝ (fun x ↦ f x - ⟪c x, z.2⟫) z.1 v) ∧
    (∀ v, p v = 0 → v = 0) ∧
    (residual = 0 → n = 0) ∧ p n ≤ Δ ∧ θ ≤ ‖residual‖ ∧
    ((∃ u, p u ≤ Δ ∧ ‖residual + A u‖ < ‖residual‖) → θ < ‖residual‖) ∧
    ‖residual + A step.1‖ ≤ θ ∧ p step.1 ≤ Δ ∧
    approximate q {s | ‖residual + A s‖ ≤ θ ∧ p s ≤ Δ} step.1 ∧
    σ = (if δN = 0 then previous else sqpPenaltyUpdate P.τ₁ P.τ₂ required previous) ∧
    0 < predicted ∧
    z' = Optimization.acceptStep P.η₁ (infeasibilitySQPMerit f c σ) z step predicted ∧
    BTRRadiusUpdate P.toBTRParams ρ Δ Δ'

/-- The accepted update preserves positive radius and penalty. The penalty
choice also enforces the predicted decrease (15.4.171). -/
theorem algorithm_15_4_8_invariants {P : SQPVariantParams}
    {f : E → ℝ} {c : E → F} {approximate : (E → ℝ) → Set E → E → Prop}
    {A : E →L[ℝ] F} {g : E} {H : E →L[ℝ] E} {p : Seminorm ℝ E} {base : ℝ}
    {z z' : E × F} {Δ Δ' previous σ : ℝ} {n : E} {step : E × F}
    (h : algorithm_15_4_8 P f c approximate A g H p base z z' Δ Δ' previous σ n step) :
    0 < Δ' ∧ previous ≤ σ ∧
      (P.ν * σ / 2) * (‖c z.1‖ ^ 2 - ‖c z.1 + A step.1‖ ^ 2) ≤
        infeasibilitySQPModel (f z.1) (c z.1) z.2 g H A σ 0 -
          infeasibilitySQPModel (f z.1) (c z.1) z.2 g H A σ step := by
  obtain ⟨hΔ, -, -, -, -, -, -, hθ, -, hres, -, -, hσ, hd, -, hΔ'⟩ := h
  refine ⟨BTRRadiusUpdate.pos hΔ' hΔ, ?_, ?_⟩
  · rw [hσ]
    unfold sqpPenaltyUpdate
    split_ifs
    · exact le_rfl
    · exact le_rfl
    · exact (le_add_of_nonneg_right P.tau₂_pos.le).trans
        ((le_max_right _ _).trans (le_max_right _ _))
  · let δN := ‖c z.1‖ ^ 2 - ‖c z.1 + A step.1‖ ^ 2
    let δF := quadraticModel 0 g H.toLinearMap step.1 - ⟪c z.1 + A step.1, step.2⟫
    let required := infeasibilitySQPPenaltyRequired P.ν δN δF base
    change σ = (if δN = 0 then previous else sqpPenaltyUpdate P.τ₁ P.τ₂ required previous) at hσ
    change (P.ν * σ / 2) * δN ≤ _
    rw [infeasibilitySQPModel_drop]
    change (P.ν * σ / 2) * δN ≤ (σ / 2) * δN - δF
    have hN : 0 ≤ δN := sub_nonneg.mpr
      (pow_le_pow_left₀ (norm_nonneg _) (hres.trans hθ) 2)
    rcases hN.eq_or_lt with hN | hN
    · have hdrop := hd
      rw [infeasibilitySQPModel_drop] at hdrop
      change 0 < (σ / 2) * δN - δF at hdrop
      rw [← hN, mul_zero]
      simpa only [← hN, mul_zero] using hdrop.le
    · have hbound : required ≤ σ := by
        rw [hσ, ite_eq_right hN.ne', sqpPenaltyUpdate]
        split_ifs with hb
        · exact hb
        · exact le_max_left _ _
      exact ((infeasibilitySQPPenaltyRequired_le_iff P.nu_lt_one hN).mp hbound).2

end Infeasibility

end ConnGouldToint.Chapter15
