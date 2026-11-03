import NumlibSurface.ConnGouldToint.Chapter13.Section06

/-! # Log barriers for general inequalities -/

open Filter Set
open scoped Topology

namespace ConnGouldToint.Chapter13

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- The primal-dual model (13.9.4) of the barrier contribution. -/
noncomputable def generalPrimalDualBarrierModel
    (c : ι → E → ℝ) (x s : E) (y : ι → ℝ) (μ : ℝ) : ℝ :=
  primalDualBarrierModel (fun i ↦ c i x) y (fun i ↦ fderiv ℝ (c i) x s) μ -
    (1 / 2 : ℝ) * ∑ i, y i * fderiv ℝ (fderiv ℝ (c i)) x s s

/-- The stationarity residual in (13.9.6), represented as a covector. -/
noncomputable def generalBarrierDualResidual
    (f : E → ℝ) (c : ι → E → ℝ) (x : E) (y : ι → ℝ) : E →L[ℝ] ℝ :=
  fderiv ℝ f x - ∑ i, y i • fderiv ℝ (c i) x

/-- The Lagrangian Hessian quadratic form used in (13.9.8). -/
noncomputable def generalBarrierLagrangianCurvature
    (f : E → ℝ) (c : ι → E → ℝ) (x : E) (y : ι → ℝ) (d : E) : ℝ :=
  fderiv ℝ (fderiv ℝ f) x d d - ∑ i, y i * fderiv ℝ (fderiv ℝ (c i)) x d d

/-- The outer stopping tests of Algorithm 13.9.2. In (13.9.7) the right
side of the residual is the vector `μ e`, since the left side is a vector. -/
def GeneralPrimalDualBarrierStop (f : E → ℝ) (c : ι → E → ℝ) (x : E)
    (y : ι → ℝ) (μ εD εC εE : ℝ) : Prop :=
  (∀ i, 0 < c i x ∧ 0 < y i) ∧ ‖generalBarrierDualResidual f c x y‖ ≤ εD ∧
  (∀ i, |c i x * y i - μ| ≤ εC) ∧
  ∀ d : E, -εE * ‖d‖ ^ 2 ≤ generalBarrierLagrangianCurvature f c x y d +
    ∑ i, (y i / c i x) * (fderiv ℝ (c i) x d) ^ 2

/-- The ratio in Step 3 of Algorithm 13.9.1. Zero represents rejection
when any fractional slack test fails, since both thresholds are positive. -/
noncomputable def generalBarrierAcceptanceRatio (c : ι → E → ℝ)
    (σ : ℝ) (φ m : E → ℝ) (x s : E) : ℝ :=
  open Classical in
  if ∀ i, σ * c i x ≤ c i (x + s) then Chapter06.btrRatio φ m x s else 0

/-- The state and update rules of Algorithm 13.9.1 with a fixed barrier
parameter. Step 2 uses the ordinary, uncapped sufficient decrease test. -/
structure GeneralPrimalDualBarrierInnerRun [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : Chapter06.BTRParams) (f : E → ℝ) (c : ι → E → ℝ) (σ μ : ℝ) where
  x : ℕ → E
  y : ℕ → ι → ℝ
  s : ℕ → E
  Δ : ℕ → ℝ
  objectiveModel : ℕ → E → ℝ
  model : ℕ → E → ℝ
  β : ℕ → ℝ
  τ : ℕ → ℝ
  κ : ℝ
  fraction : σ ∈ Ioo (0 : ℝ) 1
  barrier_parameter_pos : 0 < μ
  initial_slack_pos : ∀ i, 0 < c i (x 0)
  initial_radius_pos : 0 < Δ 0
  dual_pos : ∀ j i, 0 < y j i
  model_formula : ∀ j v, model j (x j + v) =
    objectiveModel j (x j + v) + generalPrimalDualBarrierModel c (x j) v (y j) μ
  model_center : ∀ j, objectiveModel j (x j) = f (x j) ∧
    fderiv ℝ (objectiveModel j) (x j) = fderiv ℝ f (x j)
  model_twice_differentiable : ∀ j,
    DifferentiableOn ℝ (objectiveModel j) (Metric.closedBall (x j) (Δ j)) ∧
    DifferentiableOn ℝ (fderiv ℝ (objectiveModel j)) (Metric.closedBall (x j) (Δ j))
  model_hessian_bound : ∃ K : ℝ, ∀ j v, v ∈ Metric.closedBall (x j) (Δ j) →
    (∀ i, 0 < c i v) → ‖fderiv ℝ (fderiv ℝ (objectiveModel j)) v‖ ≤ K
  curvature_model : ∀ j, β j = 1 + sSup
    ((fun v ↦ ‖fderiv ℝ (fderiv ℝ (model j)) v‖) '' Metric.closedBall (x j) (Δ j))
  nonpositive_least_curvature : ∀ j, τ j = min 0
    (sInf ((fun v ↦ fderiv ℝ (fderiv ℝ (model j)) (x j) v v) '' Metric.sphere 0 1))
  feasible_step : ∀ j, ‖s j‖ ≤ Δ j
  decrease_constant : 0 < κ
  sufficient_decrease : ∀ j,
    let g := ‖gradient (model j) (x j)‖
    κ * max (g * min (g / β j) (Δ j)) (-τ j * min (τ j ^ 2) (Δ j ^ 2)) ≤
      model j (x j) - model j (x j + s j)
  predicted_pos : ∀ j, 0 < model j (x j) - model j (x j + s j)
  iterate_update : ∀ j,
    let φ := fun v ↦ f v + logBarrier (fun i ↦ c i v) μ
    x (j + 1) = if P.η₁ ≤ generalBarrierAcceptanceRatio c σ φ (model j) (x j) (s j)
      then x j + s j else x j
  radius_update : ∀ j,
    let φ := fun v ↦ f v + logBarrier (fun i ↦ c i v) μ
    Chapter06.BTRRadiusUpdate P (generalBarrierAcceptanceRatio c σ φ (model j) (x j) (s j))
      (Δ j) (Δ (j + 1))

/-- Algorithm 13.9.2 joins fixed-parameter runs at the first qualifying
stopping index and drives the positive barrier parameter to zero. -/
structure GeneralPrimalDualBarrierOuterRun [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : Chapter06.BTRParams) (f : E → ℝ) (c : ι → E → ℝ) where
  x : ℕ → E
  y : ℕ → ι → ℝ
  μ : ℕ → ℝ
  σ : ℕ → ℝ
  εD : ℝ → ℝ
  εC : ℝ → ℝ
  εE : ℝ → ℝ
  initial_slack_pos : ∀ i, 0 < c i (x 0)
  initial_dual_pos : ∀ i, 0 < y 0 i
  forcing_pos : ∀ μ > 0, 0 < εD μ ∧ 0 < εC μ ∧ 0 < εE μ
  forcing_limit : Tendsto εD (𝓝[>] 0) (𝓝 0) ∧ Tendsto εC (𝓝[>] 0) (𝓝 0) ∧
    Tendsto εE (𝓝[>] 0) (𝓝 0)
  parameter_limit : Tendsto μ atTop (𝓝 0)
  inner : ∀ k, GeneralPrimalDualBarrierInnerRun P f c (σ k) (μ k)
  stopIndex : ℕ → ℕ
  start_inner : ∀ k, (inner k).x 0 = x k ∧ (inner k).y 0 = y k
  finish_inner : ∀ k, (inner k).x (stopIndex k) = x (k + 1) ∧
    (inner k).y (stopIndex k) = y (k + 1)
  stopping_test : ∀ k, GeneralPrimalDualBarrierStop f c (x (k + 1)) (y (k + 1)) (μ k)
    (εD (μ k)) (εC (μ k)) (εE (μ k))
  first_stop : ∀ k j, j < stopIndex k →
    ¬ GeneralPrimalDualBarrierStop f c ((inner k).x j) ((inner k).y j) (μ k)
      (εD (μ k)) (εC (μ k)) (εE (μ k))

/-- Theorem 13.9.1. The first-order limits follow directly from the outer
stopping tests. On a consistently active subsequence, the same
complementarity test controls the correction on the free rows, so the
additional multiplier-error assumption (13.9.10) is unnecessary.
The infimum in (13.9.11) is taken over unit directions, as in its proof. -/
theorem theorem_13_9_1 {α : Type*} {l : Filter α} {f : E → ℝ} {c : ι → E → ℝ}
    {x : α → E} {y : α → ι → ℝ} {μ εD εC εE : α → ℝ} {K : ℝ}
    (hμ : Tendsto μ l (𝓝 0)) (hD : Tendsto εD l (𝓝 0))
    (hC : Tendsto εC l (𝓝 0)) (hE : Tendsto εE l (𝓝 0)) (hEpos : ∀ k, 0 ≤ εE k)
    (hK : 0 ≤ K) (hA : ∀ k i, ‖fderiv ℝ (c i) (x k)‖ ≤ K)
    (hs : ∀ k, GeneralPrimalDualBarrierStop f c (x k) (y k) (μ k) (εD k) (εC k) (εE k)) :
    Tendsto (fun k ↦ ‖generalBarrierDualResidual f c (x k) (y k)‖) l (𝓝 0) ∧
    Tendsto (fun k i ↦ c i (x k) * y k i) l (𝓝 0) ∧
    ∀ active : Set ι, (∀ i ∉ active, ∃ δ > 0, ∀ᶠ k in l, δ ≤ c i (x k)) →
      ∀ η, 0 < η → ∀ᶠ k in l, ∀ d : E, ‖d‖ ≤ 1 →
        (∀ i ∈ active, fderiv ℝ (c i) (x k) d = 0) →
        -η ≤ generalBarrierLagrangianCurvature f c (x k) (y k) d := by
  classical
  have hp (i : ι) : Tendsto (fun k ↦ c i (x k) * y k i) l (𝓝 0) := by
    have he : Tendsto (fun k ↦ c i (x k) * y k i - μ k) l (𝓝 0) :=
      squeeze_zero_norm' (Eventually.of_forall fun k ↦ by
        simpa only [Real.norm_eq_abs] using (hs k).2.2.1 i) hC
    simpa only [sub_add_cancel, add_zero] using he.add hμ
  refine ⟨squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ (hs k).2.1) hD,
    tendsto_pi_nhds.mpr hp, ?_⟩
  intro active hfree η hη
  let b (k : α) (i : ι) := if i ∈ active then 0 else (y k i / c i (x k)) * K ^ 2
  have hb : Tendsto (fun k ↦ ∑ i, b k i) l (𝓝 0) := by
    rw [← Finset.sum_const_zero (s := (Finset.univ : Finset ι))]
    apply tendsto_finsetSum Finset.univ
    intro i _
    by_cases ha : i ∈ active
    · simpa [b, ha] using (tendsto_const_nhds : Tendsto (fun _ : α ↦ (0 : ℝ)) l (𝓝 0))
    obtain ⟨δ, hδ, hxi⟩ := hfree i ha
    have hr : Tendsto (fun k ↦ y k i / c i (x k)) l (𝓝 0) := by
      apply squeeze_zero' (g := fun k ↦ (c i (x k) * y k i) / δ ^ 2)
      · exact Eventually.of_forall fun k ↦ div_nonneg ((hs k).1 i).2.le ((hs k).1 i).1.le
      · filter_upwards [hxi] with k hk
        have hpos := ((hs k).1 i).1
        have he : y k i / c i (x k) = (c i (x k) * y k i) / (c i (x k)) ^ 2 := by
          field_simp [hpos.ne']
        rw [he]
        exact div_le_div_of_nonneg_left (mul_nonneg hpos.le ((hs k).1 i).2.le)
          (sq_pos_of_pos hδ) ((sq_le_sq₀ hδ.le hpos.le).mpr hk)
      · simpa using (hp i).div_const (δ ^ 2)
    simpa [b, ha] using hr.mul_const (K ^ 2)
  have hlim : Tendsto (fun k ↦ εE k + ∑ i, b k i) l (𝓝 0) := by simpa using hE.add hb
  filter_upwards [hlim.eventually (gt_mem_nhds hη)] with k hk
  intro d hd hactive
  have hcorr : (∑ i, (y k i / c i (x k)) * (fderiv ℝ (c i) (x k) d) ^ 2) ≤ ∑ i, b k i := by
    apply Finset.sum_le_sum
    intro i _
    by_cases ha : i ∈ active
    · simp [b, ha, hactive i ha]
    · simp only [b, ite_eq_right ha]
      apply mul_le_mul_of_nonneg_left _ (div_nonneg ((hs k).1 i).2.le ((hs k).1 i).1.le)
      rw [← sq_abs (fderiv ℝ (c i) (x k) d)]
      apply (sq_le_sq₀ (abs_nonneg _) hK).mpr
      rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ (c i) (x k)).le_opNorm d).trans <|
        (mul_le_mul_of_nonneg_left hd (norm_nonneg _)).trans (by simpa using hA k i)
  have hmul := mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg d) zero_le_one).mpr hd) (hEpos k)
  norm_num at hmul
  linarith [(hs k).2.2.2 d]

end ConnGouldToint.Chapter13
