import Mathlib.Analysis.InnerProductSpace.PiL2
import NumlibSurface.ConnGouldToint.Chapter13.Section03
import NumlibSurface.ConnGouldToint.Chapter13.Section04

/-! # Primal-dual barrier methods -/

open Filter Set
open scoped Topology

namespace ConnGouldToint.Chapter13

variable {ι : Type*} [Fintype ι]

/-- The corrected barrier contribution in (13.6.3). The quadratic term has a
positive sign, as in Section 13.6.2 and the elimination of the dual Newton step. -/
noncomputable def primalDualBarrierModel (x z s : ι → ℝ) (μ : ℝ) : ℝ :=
  logBarrier x μ - μ * (∑ i, (x i)⁻¹ * s i) +
    (1 / 2 : ℝ) * ∑ i, (z i / x i) * (s i) ^ 2

/-- With exact dual values the corrected model is the primal Taylor model. -/
theorem primalDualBarrierModel_eq_primal (x s : ι → ℝ) (μ : ℝ) :
    primalDualBarrierModel x (fun i ↦ μ / x i) s μ = logBarrierModel x s μ := by
  unfold primalDualBarrierModel logBarrierModel
  simp only [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by
    simp only [div_eq_mul_inv, ← inv_pow]
    ring

/-- In one dimension at `x = z = μ = 1`, the printed negative quadratic
term differs from the primal Taylor model, even for the exact dual value. -/
theorem primalDualBarrierModel_printed_sign_counterexample :
    logBarrierModel (ι := Unit) (fun _ ↦ 1) (fun _ ↦ 1) 1 ≠
      logBarrier (ι := Unit) (fun _ ↦ 1) 1 - 1 - 1 / 2 := by
  norm_num [logBarrierModel]
  linarith

private noncomputable def barrierCoordinateBilinear (i : ι) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj i)

/-- The continuous bilinear form represented by a real diagonal. -/
noncomputable def primalDualBarrierDiagonal (a : ι → ℝ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, a i • barrierCoordinateBilinear i

/-- Evaluation of the bilinear form represented by a real diagonal. -/
theorem primalDualBarrierDiagonal_apply (a d e : ι → ℝ) :
    primalDualBarrierDiagonal a d e = ∑ i, a i * d i * e i := by
  simp [primalDualBarrierDiagonal, barrierCoordinateBilinear, mul_assoc]

private theorem norm_primalDualBarrierDiagonal_le (a : ι → ℝ) :
    ‖primalDualBarrierDiagonal a‖ ≤ ∑ i, |a i| *
      ‖barrierCoordinateBilinear i‖ := by
  unfold primalDualBarrierDiagonal
  refine (norm_sum_le Finset.univ (fun i ↦ a i • barrierCoordinateBilinear i)).trans ?_
  apply Finset.sum_le_sum
  intro i _
  simpa only [Real.norm_eq_abs] using ContinuousLinearMap.opNorm_smul_le (a i) (barrierCoordinateBilinear i)

private theorem primalDualBarrierModel_eq_quadratic {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    (z : ι → ℝ) (μ : ℝ) (s : ι → ℝ) :
    primalDualBarrierModel x z s μ =
      logBarrier x μ + fderiv ℝ (Optimization.logBarrier μ) x s +
        (1 / 2 : ℝ) * primalDualBarrierDiagonal (fun i ↦ z i / x i) s s := by
  rw [Optimization.fderiv_logBarrier_apply μ hx, primalDualBarrierDiagonal_apply]
  simp only [primalDualBarrierModel, pow_two, mul_assoc]
  ring

private theorem primalDualBarrierModel_fderiv {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    (z : ι → ℝ) (μ : ℝ) (s : ι → ℝ) :
    fderiv ℝ (fun d ↦ primalDualBarrierModel x z d μ) s =
      fderiv ℝ (Optimization.logBarrier μ) x + primalDualBarrierDiagonal (fun i ↦ z i / x i) s := by
  simp only [primalDualBarrierModel_eq_quadratic hx]
  apply (barrierQuadratic_hasFDerivAt ?_ s).fderiv
  intro d e
  simp only [primalDualBarrierDiagonal_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- AM.1–AM.3 in Lemma 13.6.1. The model is smooth and matches the value and
derivative of the barrier at the current point. -/
theorem primalDualBarrierModel_center {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    (z : ι → ℝ) (μ : ℝ) :
    ContDiff ℝ 2 (fun s ↦ primalDualBarrierModel x z s μ) ∧
    primalDualBarrierModel x z 0 μ = logBarrier x μ ∧
    fderiv ℝ (fun s ↦ primalDualBarrierModel x z s μ) 0 = fderiv ℝ (Optimization.logBarrier μ) x := by
  refine ⟨?_, by simp [primalDualBarrierModel], ?_⟩
  · simp only [primalDualBarrierModel_eq_quadratic hx]
    fun_prop
  · rw [primalDualBarrierModel_fderiv hx, map_zero, add_zero]

/-- The Hessian in Lemma 13.6.1 is independent of the displacement, which
gives AC.6b with zero variation. -/
theorem primalDualBarrierModel_hessian {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    (z : ι → ℝ) (μ : ℝ) (s : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (fun d ↦ primalDualBarrierModel x z d μ)) s =
      primalDualBarrierDiagonal (fun i ↦ z i / x i) := by
  rw [funext (primalDualBarrierModel_fderiv hx z μ)]
  exact ((primalDualBarrierDiagonal _).hasFDerivAt.const_add _).fderiv

/-- AM.4h in Lemma 13.6.1 on a layer bounded away from the boundary.
The dual bound is AA.7. -/
theorem primalDualBarrierModel_hessian_bounded {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (μ : ℝ) :
    ∃ C ≥ (1 : ℝ), ∀ x z s : ι → ℝ, (∀ i, ε ≤ x i) →
      (∀ i, 0 ≤ z i ∧ z i ≤ K * max (x i)⁻¹ 1) →
      ‖fderiv ℝ (fderiv ℝ (fun d ↦ primalDualBarrierModel x z d μ)) s‖ ≤ C := by
  let B := K * max ε⁻¹ 1 / ε
  let C := ∑ i : ι, B * ‖barrierCoordinateBilinear i‖
  refine ⟨max 1 C, le_max_left _ _, fun x z s hx hz ↦ ?_⟩
  rw [primalDualBarrierModel_hessian (fun i ↦ hε.trans_le (hx i))]
  refine (norm_primalDualBarrierDiagonal_le _).trans (le_trans ?_ (le_max_right 1 C))
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg (barrierCoordinateBilinear i))
  rw [abs_of_nonneg (div_nonneg (hz i).1 (hε.le.trans (hx i)))]
  calc
    z i / x i ≤ z i / ε := div_le_div_of_nonneg_left (hz i).1 hε (hx i)
    _ ≤ B := by
      apply div_le_div_of_nonneg_right _ hε.le
      exact (hz i).2.trans (mul_le_mul_of_nonneg_left
        (max_le_max (inv_anti₀ hε (hx i)) le_rfl) hK.le)

/-- AM.5c in Lemma 13.6.1. When AA.8 makes the dual error vanish, a uniformly
positive primal layer makes the barrier model Hessian asymptotically exact. -/
theorem primalDualBarrierModel_hessian_consistent {α : Type*} {l : Filter α}
    {x z s : α → ι → ℝ} {ε μ : ℝ} (hε : 0 < ε) (hx : ∀ j i, ε ≤ x j i)
    (hdual : ∀ i, Tendsto (fun j ↦ z j i - μ / x j i) l (𝓝 0)) :
    Tendsto (fun j ↦
      ‖fderiv ℝ (fderiv ℝ (fun d ↦ primalDualBarrierModel (x j) (z j) d μ)) (s j) -
      fderiv ℝ (fderiv ℝ (Optimization.logBarrier μ)) (x j)‖) l (𝓝 0) := by
  have heq (j : α) :
      fderiv ℝ (fderiv ℝ (fun d ↦ primalDualBarrierModel (x j) (z j) d μ)) (s j) -
        fderiv ℝ (fderiv ℝ (Optimization.logBarrier μ)) (x j) =
      primalDualBarrierDiagonal (fun i ↦ (z j i - μ / x j i) / x j i) := by
    rw [primalDualBarrierModel_hessian (fun i ↦ hε.trans_le (hx j i))]
    ext d e
    simp only [sub_apply, primalDualBarrierDiagonal_apply,
      Optimization.fderiv_fderiv_logBarrier_apply μ (fun i ↦ hε.trans_le (hx j i)),
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by
      simp only [div_eq_mul_inv, ← inv_pow]
      ring
  simp only [heq]
  refine squeeze_zero
    (fun j ↦ norm_nonneg (primalDualBarrierDiagonal (fun i ↦ (z j i - μ / x j i) / x j i)))
    (fun j ↦ norm_primalDualBarrierDiagonal_le (fun i ↦ (z j i - μ / x j i) / x j i)) ?_
  rw [← Finset.sum_const_zero (s := (Finset.univ : Finset ι))]
  apply tendsto_finsetSum Finset.univ
  intro i _
  have ht : Tendsto (fun j ↦ |(z j i - μ / x j i) / x j i|) l (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ abs_nonneg _)
      (g := fun j ↦ |z j i - μ / x j i| / ε)
    · intro j
      rw [abs_div, abs_of_pos (hε.trans_le (hx j i))]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hε (hx j i)
    · simpa using (continuous_abs.continuousAt.tendsto.comp (hdual i)).div_const ε
  simpa only [zero_mul] using ht.mul_const
    ‖barrierCoordinateBilinear i‖

variable [DecidableEq ι]

/-- The stopping tests (13.6.5)–(13.6.8). The complementarity matrix is
diagonal, so its operator norm is the maximum coordinate residual. The
minimum-eigenvalue test is expressed as a bound on all quadratic forms. -/
def PrimalDualBarrierStop (f : (ι → ℝ) → ℝ) (x z : ι → ℝ) (μ εD εC εE : ℝ) : Prop :=
  (∀ i, 0 < x i) ∧ (∀ i, 0 < z i) ∧
  (∑ i, (barrierCoordinateGradient f x i - z i) ^ 2) ≤ εD ^ 2 ∧
  (∀ i, |x i * z i - μ| ≤ εC) ∧
  ∀ d : ι → ℝ, -εE * (∑ i, (d i) ^ 2) ≤
    fderiv ℝ (fderiv ℝ f) x d d + ∑ i, (z i / x i) * d i * d i

/-- The distance test in Step 2 of Algorithm 13.6.1 also admits exterior
points. From `1`, the point `-1` satisfies the printed distance test in a
radius-two ball around the current iterate, although it is infeasible. -/
theorem primalDual_distance_test_infeasible_counterexample :
    ∃ x y : ℝ, x ∈ interior (Ici (0 : ℝ)) ∧ y ∈ Metric.closedBall x 2 ∧
      (1 / 2 : ℝ) * Metric.infDist x (frontier (Ici (0 : ℝ))) ≤
        Metric.infDist y (frontier (Ici (0 : ℝ))) ∧ y ∉ Ici (0 : ℝ) := by
  refine ⟨1, -1, ?_⟩
  norm_num [interior_Ici, Metric.mem_closedBall, frontier_Ici, Metric.infDist_singleton,
    Real.dist_eq]

private def euclideanOrthant : Set (EuclideanSpace ℝ ι) :=
  WithLp.ofLp ⁻¹' Optimization.nonnegativeOrthant ι

/-- Algorithm 13.6.1 in Euclidean coordinates. Step 2 explicitly keeps the
trial feasible, and Step 1 uses the corrected positive quadratic sign. -/
structure PrimalDualBarrierInnerRun (P : Chapter06.BTRParams) (f : (ι → ℝ) → ℝ) (σ μ : ℝ)
    extends SecondPrimalBarrierInnerRun P (euclideanOrthant (ι := ι)) σ
      (fun x ↦ logBarrierObjective f x.ofLp μ) where
  barrier_parameter_pos : 0 < μ
  z : ℕ → ι → ℝ
  dual_pos : ∀ j i, 0 < z j i
  barrier_model : ∀ j y, barrierModel j y =
    primalDualBarrierModel (x j).ofLp (z j) (y - x j).ofLp μ
  objective_model_twice_diff : ∀ j,
    DifferentiableOn ℝ (objectiveModel j) (Metric.closedBall (x j) (Δ j)) ∧
    DifferentiableOn ℝ (fderiv ℝ (objectiveModel j)) (Metric.closedBall (x j) (Δ j))
  objective_model_value : ∀ j, objectiveModel j (x j) = f (x j).ofLp
  objective_model_derivative : ∀ j, fderiv ℝ (objectiveModel j) (x j) =
    fderiv ℝ (fun y : EuclideanSpace ℝ ι ↦ f y.ofLp) (x j)
  objective_model_hessian_bound : ∃ K : ℝ, ∀ j y,
    y ∈ Metric.closedBall (x j) (Δ j) → y ∈ interior (euclideanOrthant (ι := ι)) →
      ‖fderiv ℝ (fderiv ℝ (objectiveModel j)) y‖ ≤ K

/-- Algorithm 13.6.2 joins fixed-parameter inner runs at the first
qualifying stopping index and drives the positive barrier parameter to zero.
The positive forcing tolerances tend to zero at positive arguments. -/
structure PrimalDualBarrierOuterRun (P : Chapter06.BTRParams) (f : (ι → ℝ) → ℝ) where
  x : ℕ → ι → ℝ
  z : ℕ → ι → ℝ
  μ : ℕ → ℝ
  σ : ℕ → ℝ
  εD : ℝ → ℝ
  εC : ℝ → ℝ
  εE : ℝ → ℝ
  initial_primal_pos : ∀ i, 0 < x 0 i
  initial_dual_pos : ∀ i, 0 < z 0 i
  forcing_pos : ∀ μ > 0, 0 < εD μ ∧ 0 < εC μ ∧ 0 < εE μ
  forcing_limit : Tendsto εD (𝓝[>] 0) (𝓝 0) ∧ Tendsto εC (𝓝[>] 0) (𝓝 0) ∧
    Tendsto εE (𝓝[>] 0) (𝓝 0)
  parameter_limit : Tendsto μ atTop (𝓝 0)
  inner : ∀ k, PrimalDualBarrierInnerRun P f (σ k) (μ k)
  stopIndex : ℕ → ℕ
  start_inner : ∀ k, ((inner k).x 0).ofLp = x k ∧ (inner k).z 0 = z k
  finish_inner : ∀ k, ((inner k).x (stopIndex k)).ofLp = x (k + 1) ∧
    (inner k).z (stopIndex k) = z (k + 1)
  stopping_test : ∀ k, PrimalDualBarrierStop f (x (k + 1)) (z (k + 1)) (μ k)
    (εD (μ k)) (εC (μ k)) (εE (μ k))
  first_stop : ∀ k j, j < stopIndex k →
    ¬ PrimalDualBarrierStop f ((inner k).x j).ofLp ((inner k).z j) (μ k)
      (εD (μ k)) (εC (μ k)) (εE (μ k))

/-- Finite stopping in Theorem 13.6.2 from the inner limits. An upper
bound on the primal coordinates is needed to pass from AA.8 to the unscaled
complementarity test. The curvature lower bound is that of the primal-dual
model used in the stopping test. -/
theorem theorem_13_6_2_of_inner_limits {f : (ι → ℝ) → ℝ} {x z : ℕ → ι → ℝ}
    {μ εD εC εE M : ℝ} (hD : 0 < εD) (hC : 0 < εC) (hE : 0 < εE) (hM : 0 < M)
    (hx : ∀ j i, 0 < x j i) (hz : ∀ j i, 0 < z j i) (hxM : ∀ j i, x j i ≤ M)
    (hgrad : ∀ i, Tendsto (fun j ↦ barrierCoordinateGradient f (x j) i - μ / x j i)
      atTop (𝓝 0))
    (hdual : ∀ i, Tendsto (fun j ↦ z j i - μ / x j i) atTop (𝓝 0))
    {lamMin : ℕ → ℝ} (hbelow : atTop.IsCoboundedUnder (· ≤ ·) lamMin)
    (hlimsup : 0 ≤ limsup lamMin atTop)
    (hmin : ∀ j (d : ι → ℝ), lamMin j * (∑ i, (d i) ^ 2) ≤
      fderiv ℝ (fderiv ℝ f) (x j) d d + ∑ i, (z j i / x j i) * d i * d i) :
    ∃ᶠ j in atTop, PrimalDualBarrierStop f (x j) (z j) μ εD εC εE := by
  have hgs : Tendsto (fun j ↦ ∑ i, (barrierCoordinateGradient f (x j) i - z j i) ^ 2)
      atTop (𝓝 0) := by
    rw [← Finset.sum_const_zero (s := (Finset.univ : Finset ι))]
    apply tendsto_finsetSum Finset.univ
    intro i _
    simpa only [sub_sub_sub_cancel_right, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      ((hgrad i).sub (hdual i)).pow 2
  have hcomp : ∀ᶠ j in atTop, ∀ i, |x j i * z j i - μ| ≤ εC := by
    apply eventually_all.mpr
    intro i
    have hsmall := (continuous_abs.continuousAt.tendsto.comp (hdual i)).eventually
      (gt_mem_nhds (show |(0 : ℝ)| < εC / M by simpa using div_pos hC hM))
    filter_upwards [hsmall] with j hj
    change |z j i - μ / x j i| < εC / M at hj
    have heq : x j i * z j i - μ = x j i * (z j i - μ / x j i) := by
      field_simp [(hx j i).ne']
    rw [heq, abs_mul, abs_of_pos (hx j i)]
    exact (mul_le_mul (hxM j i) hj.le (abs_nonneg _) hM.le).trans_eq
      (mul_div_cancel₀ _ hM.ne')
  have hfreq := frequently_lt_of_lt_limsup hbelow ((neg_lt_zero.mpr hE).trans_le hlimsup)
  refine (hfreq.and_eventually
    ((hgs.eventually (gt_mem_nhds (sq_pos_of_pos hD))).and hcomp)).mono ?_
  intro j hj
  exact ⟨hx j, hz j, hj.2.1.le, hj.2.2, fun d ↦
    (mul_le_mul_of_nonneg_right hj.1.le (Finset.sum_nonneg fun i _ ↦ sq_nonneg (d i))).trans
      (hmin j d)⟩

/-- Under AA.8 and two-sided primal bounds, arbitrarily late tighter
primal stopping tests give arbitrarily late primal-dual stopping tests.
The lower primal bound transfers the true barrier Hessian test to the
primal-dual Hessian, while the upper bound transfers dual consistency
to unscaled complementarity. -/
theorem theorem_13_6_2_of_primal_stopping {f : (ι → ℝ) → ℝ} {x z : ℕ → ι → ℝ}
    {μ εD εC εE δ M : ℝ} (hD : 0 < εD) (hC : 0 < εC) (hE : 0 < εE)
    (hδ : 0 < δ) (hM : 0 < M) (hxδ : ∀ j i, δ ≤ x j i) (hxM : ∀ j i, x j i ≤ M)
    (hz : ∀ j i, 0 < z j i)
    (hdual : ∀ i, Tendsto (fun j ↦ z j i - μ / x j i) atTop (𝓝 0))
    (hfreq : ∃ᶠ j in atTop, BarrierSecondOrderStop f (x j) μ (εD / 2) (εE / 2)) :
    ∃ᶠ j in atTop, PrimalDualBarrierStop f (x j) (z j) μ εD εC εE := by
  let e (j : ℕ) (i : ι) := z j i - μ / x j i
  have hsum : Tendsto (fun j ↦ ∑ i, (e j i) ^ 2) atTop (𝓝 0) := by
    rw [← Finset.sum_const_zero (s := (Finset.univ : Finset ι))]
    apply tendsto_finsetSum Finset.univ
    intro i _
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using (hdual i).pow 2
  have hsmall {a : ℝ} (ha : 0 < a) : ∀ᶠ j in atTop, ∀ i, |e j i| ≤ a := by
    apply eventually_all.mpr
    intro i
    have h := (continuous_abs.continuousAt.tendsto.comp (hdual i)).eventually
      (gt_mem_nhds (show |(0 : ℝ)| < a by simpa using ha))
    exact h.mono fun j hj ↦ hj.le
  have hδE : 0 < δ * (εE / 2) := mul_pos hδ (half_pos hE)
  refine (hfreq.and_eventually
    ((hsum.eventually (gt_mem_nhds (sq_pos_of_pos (half_pos hD)))).and
      ((hsmall (div_pos hC hM)).and (hsmall hδE)))).mono ?_
  intro j hj
  obtain ⟨hp, hsumj, hCj, hEj⟩ := hj
  refine ⟨hp.1, hz j, ?_, ?_, ?_⟩
  · let a (i : ι) := barrierCoordinateGradient f (x j) i - μ / x j i
    have hsumle : (∑ i, (barrierCoordinateGradient f (x j) i - z j i) ^ 2) ≤
        ∑ i, (2 * (a i) ^ 2 + 2 * (e j i) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      dsimp [a, e]
      nlinarith [sq_nonneg (barrierCoordinateGradient f (x j) i - μ / x j i + (z j i - μ / x j i))]
    refine hsumle.trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    linarith [hp.2.1]
  · intro i
    have heq : x j i * z j i - μ = x j i * e j i := by
      unfold e
      field_simp [(hp.1 i).ne']
    rw [heq, abs_mul, abs_of_pos (hp.1 i)]
    exact (mul_le_mul (hxM j i) (hCj i) (abs_nonneg _) hM.le).trans_eq
      (mul_div_cancel₀ _ hM.ne')
  · intro d
    have hd (i : ι) : -(εE / 2) ≤ z j i / x j i - μ * ((x j i) ^ 2)⁻¹ := by
      have heq : z j i / x j i - μ * ((x j i) ^ 2)⁻¹ = e j i / x j i := by
        unfold e
        field_simp [(hp.1 i).ne']
      rw [heq]
      apply (le_div_iff₀ (hp.1 i)).mpr
      have hh := (abs_le.mp (hEj i)).1
      have hmul := mul_le_mul_of_nonpos_left (hxδ j i) (show -(εE / 2) ≤ 0 by linarith)
      linarith
    have hcorr := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
      mul_le_mul_of_nonneg_right (hd i) (sq_nonneg (d i)))
    rw [← Finset.mul_sum] at hcorr
    simp_rw [sub_mul, Finset.sum_sub_distrib] at hcorr
    have hh := hp.2.2 d
    rw [Finset.mul_sum (s := Finset.univ) (a := μ)] at hh
    simp only [pow_two, ← mul_assoc] at hcorr hh ⊢
    linarith only [hcorr, hh]

/-- Without bounded primal iterates AA.8 alone does not imply convergence
of the unscaled complementarity residual, even with positive primal and
dual coordinates and a uniform lower bound on the primal coordinates. -/
theorem primalDual_complementarity_unbounded_counterexample :
    ∃ x z : ℕ → ℝ, (∀ j, 1 ≤ x j ∧ 0 < z j) ∧
      Tendsto (fun j ↦ z j - 1 / x j) atTop (𝓝 0) ∧
      (∀ j, x j * z j - 1 = 1) := by
  let x (j : ℕ) := (j : ℝ) + 1
  refine ⟨x, fun j ↦ 2 / x j, fun j ↦ ⟨by simp [x], by dsimp [x]; positivity⟩, ?_, ?_⟩
  · have h (j : ℕ) : 2 / x j - 1 / x j = 1 / x j := by rw [← sub_div]; norm_num
    simpa only [h, x] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · intro j
    change x j * (2 / x j) - 1 = 1
    rw [mul_div_cancel₀ _ (show x j ≠ 0 by dsimp [x]; positivity)]
    norm_num

private theorem dual_coordinate_tendsto_zero {α : Type*} {l : Filter α}
    {x z : α → ℝ} (hz : ∀ k, 0 ≤ z k)
    (hp : Tendsto (fun k ↦ x k * z k) l (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) (hx : ∀ᶠ k in l, δ ≤ x k) :
    Tendsto z l (𝓝 0) := by
  apply squeeze_zero' (g := fun k ↦ (x k * z k) / δ) (Eventually.of_forall hz)
  · filter_upwards [hx] with k hk
    exact (le_div_iff₀ hδ).mpr (by
      rw [mul_comm (z k) δ]
      exact mul_le_mul_of_nonneg_right hk (hz k))
  · simpa using hp.div_const δ

/-- Theorem 13.6.3. Positive primal-dual iterates satisfying the outer
stopping tests have nonnegative gradient lower limits, zero gradient on
coordinates separated from zero, and nonnegative Hessian lower limits on
directions supported on those coordinates. Lower limits are written as
eventual inequalities for every positive tolerance. -/
theorem theorem_13_6_3 {α : Type*} {l : Filter α} {f : (ι → ℝ) → ℝ}
    {x z : α → ι → ℝ} {μ εD εC εE : α → ℝ}
    (hμ : Tendsto μ l (𝓝 0)) (hD : Tendsto εD l (𝓝 0)) (hDpos : ∀ k, 0 ≤ εD k)
    (hC : Tendsto εC l (𝓝 0)) (hE : Tendsto εE l (𝓝 0))
    (hstop : ∀ k, PrimalDualBarrierStop f (x k) (z k) (μ k) (εD k) (εC k) (εE k)) :
    (∀ i η, 0 < η → ∀ᶠ k in l, -η ≤ barrierCoordinateGradient f (x k) i) ∧
    (∀ i, (∃ δ > 0, ∀ᶠ k in l, δ ≤ x k i) →
      Tendsto (fun k ↦ barrierCoordinateGradient f (x k) i) l (𝓝 0)) ∧
    ∀ d : ι → ℝ, (∀ i, d i ≠ 0 → ∃ δ > 0, ∀ᶠ k in l, δ ≤ x k i) →
      ∀ η, 0 < η → ∀ᶠ k in l, -η ≤ fderiv ℝ (fderiv ℝ f) (x k) d d := by
  have hres (k : α) (i : ι) : |barrierCoordinateGradient f (x k) i - z k i| ≤ εD k := by
    apply (sq_le_sq₀ (abs_nonneg _) (hDpos k)).mp
    rw [sq_abs]
    exact (Finset.single_le_sum (fun j _ ↦ sq_nonneg
      (barrierCoordinateGradient f (x k) j - z k j)) (Finset.mem_univ i)).trans (hstop k).2.2.1
  have hprod (i : ι) : Tendsto (fun k ↦ x k i * z k i) l (𝓝 0) := by
    have he : Tendsto (fun k ↦ x k i * z k i - μ k) l (𝓝 0) :=
      squeeze_zero_norm' (Eventually.of_forall fun k ↦ by
        simpa [Real.norm_eq_abs] using (hstop k).2.2.2.1 i) hC
    simpa only [sub_add_cancel, add_zero] using he.add hμ
  have hdual (i : ι) {δ : ℝ} (hδ : 0 < δ) (hxi : ∀ᶠ k in l, δ ≤ x k i) :
      Tendsto (fun k ↦ z k i) l (𝓝 0) :=
    dual_coordinate_tendsto_zero (fun k ↦ ((hstop k).2.1 i).le) (hprod i) hδ hxi
  refine ⟨?_, ?_, ?_⟩
  · intro i η hη
    filter_upwards [hD.eventually (gt_mem_nhds hη)] with k hk
    linarith [(abs_le.mp (hres k i)).1, (hstop k).2.1 i]
  · intro i ⟨δ, hδ, hxi⟩
    have he : Tendsto (fun k ↦ barrierCoordinateGradient f (x k) i - z k i) l (𝓝 0) :=
      squeeze_zero_norm' (Eventually.of_forall fun k ↦ by simpa [Real.norm_eq_abs] using hres k i) hD
    simpa only [sub_add_cancel, add_zero] using he.add (hdual i hδ hxi)
  · intro d hd η hη
    have hc : Tendsto (fun k ↦ ∑ i, (z k i / x k i) * d i * d i) l (𝓝 0) := by
      rw [← Finset.sum_const_zero (s := (Finset.univ : Finset ι))]
      apply tendsto_finsetSum Finset.univ
      intro i _
      by_cases hi : d i = 0
      · simpa [hi] using (tendsto_const_nhds : Tendsto (fun _ : α ↦ (0 : ℝ)) l (𝓝 0))
      obtain ⟨δ, hδ, hxi⟩ := hd i hi
      have hr : Tendsto (fun k ↦ z k i / x k i) l (𝓝 0) := by
        apply squeeze_zero' (g := fun k ↦ z k i / δ)
        · exact Eventually.of_forall fun k ↦ div_nonneg ((hstop k).2.1 i).le ((hstop k).1 i).le
        · filter_upwards [hxi] with k hk
          exact div_le_div_of_nonneg_left ((hstop k).2.1 i).le hδ hk
        · simpa using (hdual i hδ hxi).div_const δ
      simpa only [zero_mul] using (hr.mul_const (d i)).mul_const (d i)
    have he := hE.mul_const (∑ i, (d i) ^ 2)
    have hec : Tendsto
        (fun k ↦ εE k * (∑ i, (d i) ^ 2) + ∑ i, (z k i / x k i) * d i * d i) l (𝓝 0) := by
      simpa only [zero_mul, zero_add] using he.add hc
    filter_upwards [hec.eventually (gt_mem_nhds hη)] with k hk
    linarith [(hstop k).2.2.2.2 d]

/-- On a consistently active subsequence, the free coordinates are exactly
the ones to which the vanishing-gradient and second-order conclusions apply. -/
theorem theorem_13_6_3_consistentlyActive {α : Type*} {l : Filter α} {f : (ι → ℝ) → ℝ}
    {x z : α → ι → ℝ} (ha : ConsistentlyActive l x) {μ εD εC εE : α → ℝ}
    (hμ : Tendsto μ l (𝓝 0)) (hD : Tendsto εD l (𝓝 0)) (hDpos : ∀ k, 0 ≤ εD k)
    (hC : Tendsto εC l (𝓝 0)) (hE : Tendsto εE l (𝓝 0))
    (hstop : ∀ k, PrimalDualBarrierStop f (x k) (z k) (μ k) (εD k) (εC k) (εE k)) :
    (∀ i, ¬ AsymptoticallyActive l x i →
      Tendsto (fun k ↦ barrierCoordinateGradient f (x k) i) l (𝓝 0)) ∧
    ∀ d : ι → ℝ, (∀ i, AsymptoticallyActive l x i → d i = 0) →
      ∀ η, 0 < η → ∀ᶠ k in l, -η ≤ fderiv ℝ (fderiv ℝ f) (x k) d d := by
  obtain ⟨_, hg, hH⟩ := theorem_13_6_3 hμ hD hDpos hC hE hstop
  refine ⟨fun i hi ↦ hg i ((ha i).resolve_left hi), ?_⟩
  exact fun d hd ↦ hH d fun i hi ↦ (ha i).resolve_left fun h ↦ hi (hd i h)

/-- Theorem 13.6.3 for the completed outer iterations of Algorithm 13.6.2. -/
theorem PrimalDualBarrierOuterRun.convergence {P : Chapter06.BTRParams} {f : (ι → ℝ) → ℝ}
    (r : PrimalDualBarrierOuterRun P f) :
    (∀ i η, 0 < η → ∀ᶠ k in atTop, -η ≤ barrierCoordinateGradient f (r.x (k + 1)) i) ∧
    (∀ i, (∃ δ > 0, ∀ᶠ k in atTop, δ ≤ r.x (k + 1) i) →
      Tendsto (fun k ↦ barrierCoordinateGradient f (r.x (k + 1)) i) atTop (𝓝 0)) ∧
    ∀ d : ι → ℝ, (∀ i, d i ≠ 0 → ∃ δ > 0, ∀ᶠ k in atTop, δ ≤ r.x (k + 1) i) →
      ∀ η, 0 < η → ∀ᶠ k in atTop, -η ≤ fderiv ℝ (fderiv ℝ f) (r.x (k + 1)) d d := by
  have hμpos (k : ℕ) := (r.inner k).barrier_parameter_pos
  have hμ : Tendsto r.μ atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨r.parameter_limit, Eventually.of_forall hμpos⟩
  exact theorem_13_6_3 r.parameter_limit (r.forcing_limit.1.comp hμ)
    (fun k ↦ (r.forcing_pos _ (hμpos k)).1.le) (r.forcing_limit.2.1.comp hμ)
    (r.forcing_limit.2.2.comp hμ) r.stopping_test

/-- One coordinate of the predicted multiplier (13.6.16). -/
noncomputable def primalDualPredictedMultiplier (μ x z s : ℝ) : ℝ := μ / x - z / x * s

private noncomputable def dualSafeguardLower (l μ y z : ℝ) : ℝ := l * min 1 (min z (μ / y))

private noncomputable def dualSafeguardUpper (u μ y z : ℝ) : ℝ := max u (max z (max (u / μ) (u * (μ / y))))

/-- The componentwise projection in (13.6.17)–(13.6.19) on a successful
iteration. An unsuccessful iteration retains the old multiplier. -/
noncomputable def primalDualSafeguard (l u μ x y z s : ℝ) : ℝ :=
  max (dualSafeguardLower l μ y z)
    (min (dualSafeguardUpper u μ y z) (primalDualPredictedMultiplier μ x z s))

private theorem safeguard_bounds {l u μ y z : ℝ} (hl : 0 < l) (hl' : l < 1) (hu : 1 < u)
    (hμ : 0 < μ) (hy : 0 < y) (hz : 0 < z) :
    0 < dualSafeguardLower l μ y z ∧
      dualSafeguardLower l μ y z ≤ μ / y ∧ μ / y ≤ dualSafeguardUpper u μ y z := by
  have h : 0 < μ / y := div_pos hμ hy
  have hmin : min 1 (min z (μ / y)) ≤ μ / y :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨mul_pos hl (lt_min zero_lt_one (lt_min hz h)), ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hmin hl.le).trans
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hl'.le) h.le])
  · exact (show μ / y ≤ u * (μ / y) by nlinarith [mul_nonneg (sub_nonneg.mpr hu.le) h.le]).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

/-- Positivity and AA.7 in Theorem 13.6.4, on the layer (13.6.21).
The theorem gives the explicit uniform bound from its proof. -/
theorem theorem_13_6_4 {x z s : ℕ → ℝ} {success : ℕ → Prop} [DecidablePred success]
    {l u μ ε : ℝ} (hl : 0 < l) (hl' : l < 1) (hu : 1 < u) (hμ : 0 < μ)
    (hε : 0 < ε) (hx : ∀ j, ε ≤ x j) (hz : 0 < z 0)
    (hupdate : ∀ j, z (j + 1) = if success j then
      primalDualSafeguard l u μ (x j) (x (j + 1)) (z j) (s j) else z j) :
    ∀ j, 0 < z j ∧ z j ≤ max u (max (z 0) (max (u / μ) (u * (μ / ε)))) := by
  let B := max u (max (z 0) (max (u / μ) (u * (μ / ε))))
  have hzB : z 0 ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  intro j
  induction j with
  | zero => exact ⟨hz, hzB⟩
  | succ j ih =>
    by_cases hs : success j
    · rw [hupdate, ite_eq_left hs]
      obtain ⟨hlo, hle, hhi⟩ :=
        safeguard_bounds hl hl' hu hμ (hε.trans_le (hx (j + 1))) ih.1
      refine ⟨hlo.trans_le (le_max_left _ _), max_le (hle.trans (hhi.trans ?_))
        ((min_le_left _ _).trans ?_)⟩ <;>
        exact max_le (le_max_left _ _) (max_le ih.2 (max_le
          ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
          ((mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left hμ.le hε (hx (j + 1))) (zero_lt_one.trans hu).le).trans
              ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))))
    · rwa [hupdate, ite_eq_right hs]

private theorem dualSafeguard_error_le {l u μ ε B x y z s : ℝ}
    (hl : 0 < l) (hl' : l < 1) (hu : 1 < u) (hμ : 0 < μ) (hε : 0 < ε)
    (hx : ε ≤ x) (hy : ε ≤ y) (hz : 0 < z) (hzB : z ≤ B) (hyx : y = x + s) :
    |primalDualSafeguard l u μ x y z s - μ / y| ≤ (μ / (ε * ε) + B / ε) * |s| := by
  obtain ⟨_, hlow, hhigh⟩ := safeguard_bounds hl hl' hu hμ (hε.trans_le hy) hz
  have hx' := hε.trans_le hx
  have hy' := hε.trans_le hy
  let p := primalDualPredictedMultiplier μ x z s
  have hclip : |primalDualSafeguard l u μ x y z s - μ / y| ≤ |p - μ / y| := by
    apply abs_le.mpr
    have hab := abs_le.mp (le_refl |p - μ / y|)
    unfold primalDualSafeguard
    change -|p - μ / y| ≤ max _ (min _ p) - μ / y ∧
      max _ (min _ p) - μ / y ≤ |p - μ / y|
    constructor
    · apply le_sub_iff_add_le.mpr
      exact (le_min (by linarith [abs_nonneg (p - μ / y)]) (by linarith [hab.1])).trans
        (le_max_right _ _)
    · apply sub_le_iff_le_add.mpr
      exact max_le (by linarith [abs_nonneg (p - μ / y)])
        ((min_le_right _ _).trans (by linarith [hab.2]))
  refine hclip.trans ?_
  have heq : p - μ / y = (μ / (x * y) - z / x) * s := by
    unfold p primalDualPredictedMultiplier
    field_simp [hx'.ne', hy'.ne']
    rw [hyx]
    ring
  rw [heq, abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg s)
  exact (abs_sub _ _).trans (add_le_add
    (by rw [abs_of_pos (div_pos hμ (mul_pos hx' hy'))]
        exact div_le_div_of_nonneg_left hμ.le (mul_pos hε hε) (mul_le_mul hx hy hε.le hx'.le))
    (by rw [abs_of_pos (div_pos hz hx')]
        exact (div_le_div_of_nonneg_right hzB hx'.le).trans
          (div_le_div_of_nonneg_left (hz.le.trans hzB) hε hx)))

/-- AA.8 in Theorem 13.6.4, with arbitrarily late successful steps. The
projection cannot increase error relative to the exact multiplier because
the projection interval contains that multiplier. This avoids requiring
the predictor eventually to lie strictly inside the interval. -/
theorem theorem_13_6_4_aa8_of_frequently_successful
    {x z s : ℕ → ℝ} {success : ℕ → Prop} [DecidablePred success]
    {l u μ ε : ℝ} (hl : 0 < l) (hl' : l < 1) (hu : 1 < u) (hμ : 0 < μ)
    (hε : 0 < ε) (hx : ∀ j, ε ≤ x j) (hz : 0 < z 0)
    (hprimal : ∀ j, x (j + 1) = if success j then x j + s j else x j)
    (hupdate : ∀ j, z (j + 1) = if success j then
      primalDualSafeguard l u μ (x j) (x (j + 1)) (z j) (s j) else z j)
    (hs : Tendsto s atTop (𝓝 0)) (hfreq : ∃ᶠ j in atTop, success j) :
    Tendsto (fun j ↦ z j - μ / x j) atTop (𝓝 0) := by
  let B := max u (max (z 0) (max (u / μ) (u * (μ / ε))))
  have hb := theorem_13_6_4 hl hl' hu hμ hε hx hz hupdate
  have hs0 : Tendsto (fun j ↦ (μ / (ε * ε) + B / ε) * |s j|) atTop (𝓝 0) := by
    simpa using ((continuous_abs.continuousAt.tendsto.comp hs).const_mul
      (μ / (ε * ε) + B / ε))
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hs0.eventually (gt_mem_nhds hδ))
  obtain ⟨J, hJ, hsucc⟩ := (frequently_atTop.mp hfreq) N
  have hlate (j : ℕ) (hj : N ≤ j) (ha : success j) :
      dist (z (j + 1) - μ / x (j + 1)) 0 < δ := by
    rw [Real.dist_eq, sub_zero, hupdate, ite_eq_left ha]
    exact (dualSafeguard_error_le hl hl' hu hμ hε (hx j) (hx (j + 1))
      (hb j).1 (hb j).2 (by rw [hprimal, ite_eq_left ha])).trans_lt (hN j hj)
  refine ⟨J + 1, fun n hn ↦ ?_⟩
  induction n, hn using Nat.le_induction with
  | base => exact hlate J hJ hsucc
  | succ j hj ih =>
    by_cases ha : success j
    · exact hlate j (hJ.trans (Nat.le_succ J |>.trans hj)) ha
    · rwa [hprimal, hupdate, ite_eq_right ha, ite_eq_right ha]

/-- Corrected safeguard update. After rejection, reset the dual coordinate
to the exact barrier multiplier. This is the ordinary projection with
zero effective step, so positivity, the AA.7 bound, and AA.8 hold
without requiring arbitrarily late successful trials. -/
theorem theorem_13_6_4_aa8_of_reset_rejected
    {x z s : ℕ → ℝ} {success : ℕ → Prop} [DecidablePred success]
    {l u μ ε : ℝ} (hl : 0 < l) (hl' : l < 1) (hu : 1 < u) (hμ : 0 < μ)
    (hε : 0 < ε) (hx : ∀ j, ε ≤ x j) (hz : 0 < z 0)
    (hprimal : ∀ j, x (j + 1) = if success j then x j + s j else x j)
    (hupdate : ∀ j, z (j + 1) = if success j then
      primalDualSafeguard l u μ (x j) (x (j + 1)) (z j) (s j) else μ / x (j + 1))
    (hs : Tendsto (fun j ↦ x (j + 1) - x j) atTop (𝓝 0)) :
    (∀ j, 0 < z j ∧ z j ≤ max u (max (z 0) (max (u / μ) (u * (μ / ε))))) ∧
    Tendsto (fun j ↦ z j - μ / x j) atTop (𝓝 0) := by
  have hp (j : ℕ) : 0 < x j := hε.trans_le (hx j)
  have hzpos (j : ℕ) : 0 < z j := by
    induction j with
    | zero => exact hz
    | succ j ih =>
      rw [hupdate]
      split_ifs
      · exact (safeguard_bounds hl hl' hu hμ (hp (j + 1)) ih).1.trans_le (le_max_left _ _)
      · exact div_pos hμ (hp (j + 1))
  let t (j : ℕ) := if success j then s j else 0
  have ht : Tendsto t atTop (𝓝 0) := by
    have he (j : ℕ) : x (j + 1) - x j = t j := by
      rw [hprimal]
      unfold t
      split_ifs <;> ring
    simpa only [he] using hs
  have hpr (j : ℕ) : x (j + 1) = if True then x j + t j else x j := by
    simp only [ite_true]
    rw [hprimal]
    unfold t
    split_ifs <;> simp
  have hdu (j : ℕ) : z (j + 1) =
      if True then primalDualSafeguard l u μ (x j) (x (j + 1)) (z j) (t j) else z j := by
    simp only [ite_true]
    by_cases hj : success j
    · simp [hupdate j, t, hj]
    · have hxe : x (j + 1) = x j := by rw [hprimal, ite_eq_right hj]
      rw [hupdate, ite_eq_right hj]
      obtain ⟨_, hlo, hhi⟩ := safeguard_bounds hl hl' hu hμ (hp j) (hzpos j)
      simp only [t, ite_eq_right hj, hxe, primalDualSafeguard, primalDualPredictedMultiplier,
        mul_zero, sub_zero, min_eq_right hhi, max_eq_right hlo]
  exact ⟨theorem_13_6_4 (success := fun _ ↦ True) hl hl' hu hμ hε hx hz hdu,
    theorem_13_6_4_aa8_of_frequently_successful (success := fun _ ↦ True)
      hl hl' hu hμ hε hx hz hpr hdu ht (frequently_atTop.mpr fun N ↦ ⟨N, le_rfl, trivial⟩)⟩

/-- A successful inner iteration, using the actual primal-dual model and
the guarded barrier ratio of the inner run. -/
def PrimalDualBarrierInnerRun.Successful {P : Chapter06.BTRParams} {f : (ι → ℝ) → ℝ} {σ μ : ℝ}
    (r : PrimalDualBarrierInnerRun P f σ μ) (j : ℕ) : Prop :=
  P.η₁ ≤ primalBarrierRatio (euclideanOrthant (ι := ι)) σ
    (fun x ↦ logBarrierObjective f x.ofLp μ) (r.model j) (r.x j) (r.s j)

omit [DecidableEq ι] in
/-- The corrected rejection safeguard gives coordinate AA.8 on the
actual inner run when its accepted displacements tend to zero. -/
theorem PrimalDualBarrierInnerRun.dual_consistent_of_reset_rejected
    {P : Chapter06.BTRParams} {f : (ι → ℝ) → ℝ} {σ μ : ℝ}
    (r : PrimalDualBarrierInnerRun P f σ μ) {l u δ : ℝ}
    (hl : 0 < l) (hl' : l < 1) (hu : 1 < u)
    (hδ : 0 < δ) (hx : ∀ j i, δ ≤ (r.x j).ofLp i)
    (hstep : Tendsto (fun j ↦ r.x (j + 1) - r.x j) atTop (𝓝 0))
    (haccept : ∀ j i, r.Successful j → r.z (j + 1) i =
      primalDualSafeguard l u μ ((r.x j).ofLp i) ((r.x (j + 1)).ofLp i) (r.z j i) ((r.s j).ofLp i))
    (hreject : ∀ j i, ¬r.Successful j → r.z (j + 1) i = μ / (r.x (j + 1)).ofLp i) :
    ∀ i, Tendsto (fun j ↦ r.z j i - μ / (r.x j).ofLp i) atTop (𝓝 0) := by
  classical
  intro i
  have hpr (j : ℕ) : (r.x (j + 1)).ofLp i =
      if r.Successful j then (r.x j).ofLp i + (r.s j).ofLp i else (r.x j).ofLp i := by
    rw [r.iterate_update]
    unfold PrimalDualBarrierInnerRun.Successful
    split_ifs <;> rfl
  let T := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)
  have hc : Continuous (fun x : EuclideanSpace ℝ ι ↦ x.ofLp i) :=
    (continuous_apply i).comp T.continuous
  have hs : Tendsto (fun j ↦ (r.x (j + 1)).ofLp i - (r.x j).ofLp i) atTop (𝓝 0) := by
    have hh := hc.continuousAt.tendsto.comp hstep
    change Tendsto (fun j ↦ (r.x (j + 1) - r.x j).ofLp i) atTop
      (𝓝 ((0 : EuclideanSpace ℝ ι).ofLp i)) at hh
    simpa only [WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_zero, Pi.zero_apply] using hh
  exact (theorem_13_6_4_aa8_of_reset_rejected (success := r.Successful) hl hl' hu
    r.barrier_parameter_pos hδ (fun j ↦ hx j i) (r.dual_pos 0 i) hpr
    (fun j ↦ by
      by_cases h : r.Successful j
      · rw [ite_eq_left h]
        exact haccept j i h
      · rw [ite_eq_right h]
        exact hreject j i h) hs).2

/-- Corrected Theorem 13.6.2 for a bounded primal-dual inner run. The
derivative and curvature limits can be obtained on the run's own
acceptance ratios by applying the inner extension theorem to its second
primal run. AA.8 then transfers both limits to the dual stopping tests. -/
theorem PrimalDualBarrierInnerRun.frequently_stop_of_extension_limits [Nonempty ι]
    {P : Chapter06.BTRParams} {f : (ι → ℝ) → ℝ} {σ μ : ℝ}
    (r : PrimalDualBarrierInnerRun P f σ μ) {F : EuclideanSpace ℝ ι → ℝ}
    {εD εC εE δ M : ℝ} (hD : 0 < εD) (hC : 0 < εC) (hE : 0 < εE)
    (hf : ContDiff ℝ 2 f) (hF : ContDiff ℝ 2 F)
    (hδ : 0 < δ) (hM : 0 < M)
    (hxδ : ∀ j i, δ ≤ (r.x j).ofLp i) (hxM : ∀ j i, (r.x j).ofLp i ≤ M)
    (hlocal : ∀ j, (F ∘ barrierEuclideanCoordinates) =ᶠ[𝓝 (r.x j).ofLp]
      fun y ↦ logBarrierObjective f y μ)
    (hgrad : Tendsto (fun j ↦ ‖fderiv ℝ F (r.x j)‖) atTop (𝓝 0))
    (hcurv : ∀ ε > (0 : ℝ), ∃ᶠ j in atTop, -ε <
      Chapter06.leastUnitCurvature (fderiv ℝ (fderiv ℝ F) (r.x j)))
    (hAA8 : Tendsto (fun j ↦ ‖fderiv ℝ F (r.x j)‖) atTop (𝓝 0) →
      ∀ i, Tendsto (fun j ↦ r.z j i - μ / (r.x j).ofLp i) atTop (𝓝 0)) :
    ∃ᶠ j in atTop, PrimalDualBarrierStop f (r.x j).ofLp (r.z j) μ εD εC εE := by
  have hprimal := theorem_13_4_2_of_local_extension (half_pos hD) (half_pos hE)
    hf hF (fun j i ↦ hδ.trans_le (hxδ j i)) hlocal hgrad hcurv
  exact theorem_13_6_2_of_primal_stopping hD hC hE hδ hM hxδ hxM r.dual_pos
    (hAA8 hgrad) hprimal

/-- The corrected inner convergence theorem for Algorithm 13.6.1.
A smooth extension preserving all iterate and trial values lets the
capped trust-region convergence proof use the actual primal-dual ratios.
The bounded primal layer and AA.8 transfer its two limits to all three
primal-dual stopping inequalities. -/
theorem PrimalDualBarrierInnerRun.frequently_stop_of_extension [Nonempty ι]
    {P : Chapter06.BTRParams} {f : (ι → ℝ) → ℝ} {σ μ : ℝ}
    (r : PrimalDualBarrierInnerRun P f σ μ) {F : EuclideanSpace ℝ ι → ℝ}
    {εD εC εE δ M K L D G T : ℝ}
    (hD : 0 < εD) (hC : 0 < εC) (hE : 0 < εE)
    (hf : ContDiff ℝ 2 f) (hF : ContDiff ℝ 2 F) (hlower : BddBelow (range F))
    (hδ : 0 < δ) (hM : 0 < M)
    (hxδ : ∀ j i, δ ≤ (r.x j).ofLp i) (hxM : ∀ j i, (r.x j).ofLp i ≤ M)
    (hlocal : ∀ j, (F ∘ barrierEuclideanCoordinates) =ᶠ[𝓝 (r.x j).ofLp]
      fun y ↦ logBarrierObjective f y μ)
    (htrial : ∀ j, F (r.x j + r.s j) = logBarrierObjective f (r.x j + r.s j).ofLp μ)
    (hDp : 0 < D) (hG : 0 < G) (hT : 0 < T)
    (hclear : ∀ j, D ≤ (1 - σ) * Metric.infDist (r.x j) (frontier (euclideanOrthant (ι := ι))))
    (hH : ∀ y, ‖fderiv ℝ (fderiv ℝ F) y‖ ≤ L)
    (hβ₁ : ∀ j, 1 ≤ r.β j) (hβK : ∀ j, r.β j ≤ K)
    (hGbd : ∀ j, ‖r.g j‖ ≤ G) (hτbd : ∀ j, |r.τ j| ≤ T)
    (hτ : ∀ j, r.τ j = min 0
      (Chapter06.leastUnitCurvature (fderiv ℝ (fderiv ℝ (r.model j)) (r.x j))))
    (hval : ∀ j, F (r.x j) = r.model j (r.x j))
    (hgrad : ∀ j, fderiv ℝ F (r.x j) = fderiv ℝ (r.model j) (r.x j))
    (herr : ∀ j, |F (r.x j + r.s j) - r.model j (r.x j + r.s j)| ≤ K * (r.Δ j) ^ 2)
    (hm : ∀ j y, y ∈ segment ℝ (r.x j) (r.x j + r.s j) →
      DifferentiableAt ℝ (r.model j) y)
    (hDm : ∀ j y, y ∈ segment ℝ (r.x j) (r.x j + r.s j) →
      DifferentiableAt ℝ (fderiv ℝ (r.model j)) y)
    (hvar : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ j, r.Δ j ≤ δ →
      ∀ y ∈ segment ℝ (r.x j) (r.x j + r.s j),
        ‖fderiv ℝ (fderiv ℝ F) y - fderiv ℝ (fderiv ℝ F) (r.x j)‖ +
        ‖fderiv ℝ (fderiv ℝ (r.model j)) y -
          fderiv ℝ (fderiv ℝ (r.model j)) (r.x j)‖ ≤ ε)
    (hagree : Chapter06.ModelHessianAgreement F r.model r.x)
    (hAA8 : Tendsto (fun j ↦ ‖r.g j‖) atTop (𝓝 0) →
      ∀ i, Tendsto (fun j ↦ r.z j i - μ / (r.x j).ofLp i) atTop (𝓝 0)) :
    ∃ᶠ j in atTop, PrimalDualBarrierStop f (r.x j).ofLp (r.z j) μ εD εC εE := by
  have hx (j : ℕ) : F (r.x j) = logBarrierObjective f (r.x j).ofLp μ := by
    have hh := (hlocal j).eq_of_nhds
    change F (WithLp.toLp 2 (r.x j).ofLp) = _ at hh
    rwa [WithLp.toLp_ofLp] at hh
  obtain ⟨hg, hc⟩ := theorem_13_4_2_inner_of_extension r.toSecondPrimalBarrierInnerRun hx htrial
    hF hlower hDp hG hT hclear hH hβ₁ hβK hGbd hτbd hτ hval hgrad herr hm hDm hvar hagree
  apply r.frequently_stop_of_extension_limits hD hC hE hf hF hδ hM hxδ hxM hlocal hg hc
  intro h
  apply hAA8
  have he (j : ℕ) : ‖r.g j‖ = ‖fderiv ℝ F (r.x j)‖ := by
    rw [r.gradient_model]
    unfold gradient
    rw [LinearIsometryEquiv.norm_map, hgrad]
  simpa only [he] using h

/-- Holding both iterates on a rejected step cannot transfer a limit over
successful indices to the full sequence when all later steps are rejected. -/
theorem primalDual_safeguard_stalled_counterexample :
    ∃ x z s : ℕ → ℝ, (∀ j, 1 ≤ x j ∧ 0 < z j) ∧ Tendsto s atTop (𝓝 0) ∧
      (∀ j, x (j + 1) = x j ∧ z (j + 1) = z j) ∧
      ¬ Tendsto (fun j ↦ z j - 1 / x j) atTop (𝓝 0) := by
  refine ⟨fun _ ↦ 1, fun _ ↦ 2, fun _ ↦ 0, by norm_num, tendsto_const_nhds, by simp, ?_⟩
  intro h
  have h' : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 0) := by
    convert h using 1
    norm_num
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h')

section EscapeExample

open Metric

private def escapeBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

private noncomputable def escapeTail (x : ℝ) : ℝ := Real.log x + x⁻¹

/-- A globally smooth extension of `log x + 1 / x` outside the radius-two ball. -/
noncomputable def primalDualEscapeObjective (x : ℝ) : ℝ := (1 - escapeBump x) * escapeTail x

private theorem escape_eq_zero {x : ℝ} (hx : |x| < 1) :
    primalDualEscapeObjective =ᶠ[𝓝 x] fun _ ↦ 0 := by
  have hx' : x ∈ ball (0 : ℝ) 1 := by simpa [Real.dist_eq] using hx
  filter_upwards [isOpen_ball.mem_nhds hx'] with y hy
  simp [primalDualEscapeObjective, escapeBump.one_of_mem_closedBall (ball_subset_closedBall hy)]

private theorem escape_eq_tail {x : ℝ} (hx : 2 < |x|) :
    primalDualEscapeObjective =ᶠ[𝓝 x] escapeTail := by
  have hx' : x ∈ (closedBall (0 : ℝ) 2)ᶜ := by simpa [Real.dist_eq] using hx.not_ge
  filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hx'] with y hy
  have hby : escapeBump y = 0 :=
    escapeBump.zero_of_le_dist (le_of_not_ge (show y ∉ closedBall (0 : ℝ) 2 from hy))
  simp [primalDualEscapeObjective, hby]

private theorem escape_contDiff : ContDiff ℝ 2 primalDualEscapeObjective := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    exact contDiffAt_const.congr_of_eventuallyEq (escape_eq_zero (x := 0) (by norm_num))
  have ht : ContDiffAt ℝ 2 escapeTail x :=
    (contDiffAt_id.log hx).add (contDiffAt_id.inv hx)
  exact (contDiffAt_const.sub (escapeBump.contDiff (n := 2)).contDiffAt).mul ht

private theorem escapeTail_deriv {x : ℝ} (hx : x ≠ 0) :
    deriv escapeTail x = x⁻¹ - (x ^ 2)⁻¹ := by
  have h := (Real.hasDerivAt_log hx).add ((hasDerivAt_id x).inv hx)
  have he := h.deriv
  change deriv escapeTail x = _ at he
  simpa [div_eq_mul_inv, sub_eq_add_neg] using he

private theorem escapeTail_deriv_deriv {x : ℝ} (hx : x ≠ 0) :
    deriv (deriv escapeTail) x = -(x ^ 2)⁻¹ + 2 * (x ^ 3)⁻¹ := by
  have he : deriv escapeTail =ᶠ[𝓝 x] fun y ↦ y⁻¹ - (y ^ 2)⁻¹ := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact escapeTail_deriv hy
  rw [he.deriv_eq]
  have h := ((hasDerivAt_id x).inv hx).sub (((hasDerivAt_id x).pow 2).inv (pow_ne_zero _ hx))
  have hh := h.deriv
  change deriv (fun y : ℝ ↦ y⁻¹ - (y ^ 2)⁻¹) x = _ at hh
  rw [hh]
  simp only [id_eq, Pi.pow_apply]
  field_simp [hx]
  ring

private theorem escape_deriv {x : ℝ} (hx : 2 < |x|) :
    deriv primalDualEscapeObjective x = x⁻¹ - (x ^ 2)⁻¹ := by
  rw [(escape_eq_tail hx).deriv_eq, escapeTail_deriv]
  exact abs_pos.mp (zero_lt_two.trans hx)

private theorem escape_deriv_deriv {x : ℝ} (hx : 2 < |x|) :
    deriv (deriv primalDualEscapeObjective) x = -(x ^ 2)⁻¹ + 2 * (x ^ 3)⁻¹ := by
  have he : deriv primalDualEscapeObjective =ᶠ[𝓝 x] deriv escapeTail := by
    filter_upwards [continuous_abs.continuousAt.eventually (lt_mem_nhds hx)] with y hy
    exact (escape_eq_tail hy).deriv_eq
  rw [he.deriv_eq]
  exact escapeTail_deriv_deriv (abs_pos.mp (zero_lt_two.trans hx))

private theorem escape_hessian_bounded :
    ∃ B : ℝ, ∀ x, |deriv (deriv primalDualEscapeObjective) x| ≤ B := by
  have hcont : Continuous (deriv (deriv primalDualEscapeObjective)) :=
    ((escape_contDiff.deriv' (n := 1)).deriv' (n := 0)).continuous
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℝ) 2).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B 3, fun x ↦ ?_⟩
  by_cases hx : |x| ≤ 2
  · exact (by simpa [Real.norm_eq_abs] using hB x (show x ∈ closedBall (0 : ℝ) 2 by
        simpa [Real.dist_eq] using hx) : _ ≤ B).trans (le_max_left _ _)
  · have hp : 2 < |x| := lt_of_not_ge hx
    rw [escape_deriv_deriv hp]
    have habs : |-(x ^ 2)⁻¹ + 2 * (x ^ 3)⁻¹| ≤ |-(x ^ 2)⁻¹| + |2 * (x ^ 3)⁻¹| := by
      simpa only [Real.norm_eq_abs] using norm_add_le (-(x ^ 2)⁻¹) (2 * (x ^ 3)⁻¹)
    have hsum : |-(x ^ 2)⁻¹| + |2 * (x ^ 3)⁻¹| ≤ 3 := by
      simp only [abs_neg, abs_inv, abs_pow, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      have h1 : (|x| ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
      have h2 : (|x| ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
      linarith
    exact habs.trans (hsum.trans (le_max_right B 3))

private theorem escape_barrier_bounded :
    BddBelow ((fun x : ℝ ↦ primalDualEscapeObjective x - Real.log x) '' Ioi 0) := by
  let φ := fun x : ℝ ↦ primalDualEscapeObjective x - Real.log x
  have hc : ContinuousOn φ (Icc (1 / 2 : ℝ) 3) :=
    escape_contDiff.continuous.continuousOn.sub (fun x hx ↦
      (Real.continuousAt_log (show x ≠ 0 from ne_of_gt (by linarith [hx.1]))).continuousWithinAt)
  obtain ⟨B, hB⟩ := isCompact_Icc.bddBelow_image hc
  refine ⟨min B 0, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx0 : 0 < x := hx
  by_cases h1 : x < 1 / 2
  · have he := (escape_eq_zero (x := x) (by rw [abs_of_pos hx0]; linarith)).eq_of_nhds
    change min B 0 ≤ primalDualEscapeObjective x - Real.log x
    rw [he]
    exact (min_le_right _ _).trans (by linarith [Real.log_nonpos hx0.le (by linarith : x ≤ 1)])
  by_cases h3 : x ≤ 3
  · exact (min_le_left _ _).trans (hB ⟨x, ⟨le_of_not_gt h1, h3⟩, rfl⟩)
  · have he := (escape_eq_tail (x := x) (by rw [abs_of_pos hx0]; linarith)).eq_of_nhds
    change min B 0 ≤ primalDualEscapeObjective x - Real.log x
    rw [he, escapeTail, add_sub_cancel_left]
    exact (min_le_right _ _).trans (inv_nonneg.mpr hx0.le)

private theorem escape_barrier_uniform_lower_bound :
    ∃ B : ℝ, ∀ μ ∈ Ioc (0 : ℝ) 1, ∀ x > 0,
      B ≤ primalDualEscapeObjective x - μ * Real.log x := by
  obtain ⟨B, hB⟩ := escape_barrier_bounded
  obtain ⟨A, hA⟩ := (isCompact_Icc (α := ℝ) (a := 0) (b := 1)).bddBelow_image
    escape_contDiff.continuous.continuousOn
  refine ⟨min A B, fun μ hμ x hx ↦ ?_⟩
  by_cases hx1 : 1 ≤ x
  · have hh := hB ⟨x, hx, rfl⟩
    change B ≤ primalDualEscapeObjective x - Real.log x at hh
    exact (min_le_right _ _).trans (hh.trans (by
      have hm := mul_le_of_le_one_left (Real.log_nonneg hx1) hμ.2
      linarith))
  · have hh := hA ⟨x, ⟨hx.le, le_of_not_ge hx1⟩, rfl⟩
    exact (min_le_left _ _).trans (hh.trans (by
      have hm := mul_nonpos_of_nonneg_of_nonpos hμ.1.le (Real.log_nonpos hx.le (le_of_not_ge hx1))
      linarith))

/-- One-dimensional all-successful specialization of Algorithm 13.6.1
with fixed unit radius, unit steps, fraction one half, and `μ = 1`.
The objective model is its exact quadratic Taylor model at each iterate.
The curvature in the model includes the corrected positive dual term. -/
structure ScalarPrimalDualEscapeRun (f : ℝ → ℝ) (x z : ℕ → ℝ) : Prop where
  primal_pos : ∀ j, 0 < x j
  dual_pos : ∀ j, 0 < z j
  update : ∀ j, x (j + 1) = x j + 1
  fractional_clearance : ∀ j, (1 / 2 : ℝ) * x j ≤ x (j + 1)
  positive_curvature : ∀ j, 0 ≤ deriv (deriv f) (x j) + z j / x j
  decrease : ∀ j,
    let g := deriv f (x j) - (x j)⁻¹
    let h := deriv (deriv f) (x j) + z j / x j
    (1 / 8 : ℝ) * (|g| * min (|g| / (1 + |h|)) 1) ≤ -g - h / 2
  very_successful : ∀ j,
    let g := deriv f (x j) - (x j)⁻¹
    let h := deriv (deriv f) (x j) + z j / x j
    0 < -g - h / 2 ∧ -g - h / 2 ≤
      (f (x j) - Real.log (x j)) - (f (x (j + 1)) - Real.log (x (j + 1)))

/-- In the unbounded run the exact Taylor objective models satisfy the
center matching and curvature conditions, AA.7 and AA.8 hold, and every
ratio is at least one. The unit complementarity error nevertheless
prevents finite stopping at tolerance one half. -/
theorem theorem_13_6_2_unbounded_run_counterexample :
    ∃ x z : ℕ → ℝ,
      ContDiff ℝ 2 primalDualEscapeObjective ∧
      (∃ B : ℝ, ∀ x, |deriv (deriv primalDualEscapeObjective) x| ≤ B) ∧
      (∃ B : ℝ, ∀ μ ∈ Ioc (0 : ℝ) 1, ∀ x > 0,
        B ≤ primalDualEscapeObjective x - μ * Real.log x) ∧
      ScalarPrimalDualEscapeRun primalDualEscapeObjective x z ∧
      Tendsto x atTop atTop ∧
      (∀ j, z j ≤ 2 * max (x j)⁻¹ 1) ∧
      Tendsto (fun j ↦ deriv primalDualEscapeObjective (x j) - (x j)⁻¹) atTop (𝓝 0) ∧
      Tendsto (fun j ↦ z j - (x j)⁻¹) atTop (𝓝 0) ∧
      (∀ j, ¬ |x j * z j - 1| ≤ (1 / 2 : ℝ)) := by
  let x (j : ℕ) := (j : ℝ) + 3
  let z (j : ℕ) := 2 / x j
  have hx (j : ℕ) : 3 ≤ x j := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) j]
  have hxp (j : ℕ) : 0 < x j := by linarith [hx j]
  have hx2 (j : ℕ) : 2 < |x j| := by rw [abs_of_pos (hxp j)]; linarith [hx j]
  have hxadd (j : ℕ) : x (j + 1) = x j + 1 := by simp [x, Nat.cast_add]; ring
  have hz (j : ℕ) : 0 < z j := div_pos zero_lt_two (hxp j)
  have hg (j : ℕ) : deriv primalDualEscapeObjective (x j) - (x j)⁻¹ = -((x j) ^ 2)⁻¹ := by
    rw [escape_deriv (hx2 j)]
    ring
  have hh (j : ℕ) : deriv (deriv primalDualEscapeObjective) (x j) + z j / x j =
      ((x j) ^ 2)⁻¹ + 2 * ((x j) ^ 3)⁻¹ := by
    rw [escape_deriv_deriv (hx2 j)]
    unfold z
    field_simp [(hxp j).ne']
    ring
  have hphi (j : ℕ) : primalDualEscapeObjective (x j) - Real.log (x j) = (x j)⁻¹ := by
    rw [(escape_eq_tail (hx2 j)).eq_of_nhds, escapeTail, add_sub_cancel_left]
  refine ⟨x, z, escape_contDiff, escape_hessian_bounded, escape_barrier_uniform_lower_bound,
    ⟨hxp, hz, hxadd, ?_, ?_, ?_, ?_⟩,
    tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hxadd]
    linarith [hx j]
  · intro j
    rw [hh]
    positivity
  · intro j
    dsimp only
    rw [hg, hh, abs_neg, abs_of_nonneg (by positivity : 0 ≤ ((x j) ^ 2)⁻¹)]
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (min_le_right _ _)
      (by positivity)) (by norm_num)).trans
    have hp := hxp j
    field_simp [hp.ne']
    nlinarith [hx j]
  · intro j
    dsimp only
    rw [hg, hh, hphi j, hphi (j + 1), hxadd]
    have hp := hxp j
    have hpa : 0 < x j + 1 := by positivity
    constructor
    · field_simp [hp.ne']
      nlinarith [hx j]
    · field_simp [hp.ne', hpa.ne']
      nlinarith [hx j, sq_nonneg (x j)]
  · intro j
    unfold z
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) zero_lt_two.le
  · have ht : Tendsto (fun j ↦ (x j)⁻¹) atTop (𝓝 0) := by
      have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 2)
      simpa [x, Function.comp_def, Nat.cast_add, add_assoc, one_div, show (2 : ℝ) + 1 = 3 by norm_num] using ht
    simpa only [hg, ← inv_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), neg_zero] using (ht.pow 2).neg
  · have ht : Tendsto (fun j ↦ (x j)⁻¹) atTop (𝓝 0) := by
      have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 2)
      simpa [x, Function.comp_def, Nat.cast_add, add_assoc, one_div, show (2 : ℝ) + 1 = 3 by norm_num] using ht
    have he (j : ℕ) : z j - (x j)⁻¹ = (x j)⁻¹ := by unfold z; rw [div_eq_mul_inv]; ring
    simpa only [he] using ht
  · intro j
    unfold z
    rw [mul_div_cancel₀ _ (hxp j).ne']
    norm_num

end EscapeExample

section RejectionExample

open Metric Chapter06

private noncomputable def stalledBump : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

private noncomputable def stalledLocal (x : ℝ) : ℝ := Real.log x + (x - 1) ^ 2 / 4

/-- A smooth objective with barrier value `(x - 1)^2 / 4` near one
and with a positive quadratic tail. -/
noncomputable def primalDualStalledObjective (x : ℝ) : ℝ :=
  stalledBump x * stalledLocal x + (1 - stalledBump x) * x ^ 2

private theorem stalled_eq_local {x : ℝ} (hx : x ∈ ball (1 : ℝ) (1 / 4)) :
    primalDualStalledObjective =ᶠ[𝓝 x] stalledLocal := by
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  simp [primalDualStalledObjective, stalledBump.one_of_mem_closedBall (ball_subset_closedBall hy)]

private theorem stalled_eq_outer {x : ℝ} (hx : x ∉ closedBall (1 : ℝ) (1 / 2)) :
    primalDualStalledObjective =ᶠ[𝓝 x] (fun y : ℝ ↦ y ^ 2) := by
  filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hx] with y hy
  have hb : stalledBump y = 0 :=
    stalledBump.zero_of_le_dist (le_of_not_ge (show y ∉ closedBall (1 : ℝ) (1 / 2) from hy))
  simp [primalDualStalledObjective, hb]

private theorem stalled_contDiff : ContDiff ℝ 2 primalDualStalledObjective := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have h := (contDiffAt_id (𝕜 := ℝ) (n := 2) (x := (0 : ℝ))).pow 2
    exact h.congr_of_eventuallyEq (stalled_eq_outer (by norm_num [mem_closedBall, Real.dist_eq]))
  have hlocal : ContDiffAt ℝ 2 stalledLocal x := by
    unfold stalledLocal
    exact (contDiffAt_id.log hx).add (((contDiffAt_id.sub contDiffAt_const).pow 2).div_const 4)
  have hb : ContDiffAt ℝ 2 stalledBump x := stalledBump.contDiff.contDiffAt
  exact (hb.mul hlocal).add ((contDiffAt_const.sub hb).mul (contDiffAt_id.pow 2))

private theorem stalledLocal_deriv {x : ℝ} (hx : x ≠ 0) :
    deriv stalledLocal x = x⁻¹ + (x - 1) / 2 := by
  have h := (Real.hasDerivAt_log hx).add ((((hasDerivAt_id x).sub_const 1).pow 2).div_const 4)
  have he := h.deriv
  change deriv stalledLocal x = _ at he
  rw [he]
  simp only [id_eq, Nat.cast_ofNat, show (2 - 1 : ℕ) = 1 by decide, pow_one, mul_one]
  ring

private theorem stalled_center_derivatives :
    deriv primalDualStalledObjective 1 = 1 ∧
    deriv (deriv primalDualStalledObjective) 1 = -(1 / 2 : ℝ) := by
  have h1 : (1 : ℝ) ∈ ball 1 (1 / 4) := mem_ball_self (by norm_num)
  constructor
  · rw [(stalled_eq_local h1).deriv_eq, stalledLocal_deriv (by norm_num)]
    norm_num
  have he : deriv primalDualStalledObjective =ᶠ[𝓝 (1 : ℝ)] fun x ↦ x⁻¹ + (x - 1) / 2 := by
    filter_upwards [isOpen_ball.mem_nhds h1, isOpen_ne.mem_nhds (one_ne_zero : (1 : ℝ) ≠ 0)]
      with y hy hy0
    rw [(stalled_eq_local hy).deriv_eq, stalledLocal_deriv hy0]
  rw [he.deriv_eq]
  have hd := ((hasDerivAt_id (1 : ℝ)).inv (by norm_num : (1 : ℝ) ≠ 0)).add
    (((hasDerivAt_id (1 : ℝ)).sub_const 1).div_const 2)
  have hh := hd.deriv
  change deriv (fun x : ℝ ↦ x⁻¹ + (x - 1) / 2) 1 = _ at hh
  rw [hh]
  norm_num

private theorem stalled_hessian_bounded :
    ∃ B : ℝ, ∀ x, |deriv (deriv primalDualStalledObjective) x| ≤ B := by
  have hc : Continuous (deriv (deriv primalDualStalledObjective)) :=
    ((stalled_contDiff.deriv' (n := 1)).deriv' (n := 0)).continuous
  obtain ⟨B, hB⟩ := (isCompact_closedBall (1 : ℝ) (1 / 2)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B 2, fun x ↦ ?_⟩
  by_cases hx : x ∈ closedBall (1 : ℝ) (1 / 2)
  · exact (by simpa only [Real.norm_eq_abs] using hB x hx : _ ≤ B).trans (le_max_left _ _)
  · have he : deriv primalDualStalledObjective =ᶠ[𝓝 x] deriv (fun y : ℝ ↦ y ^ 2) := by
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hx] with y hy
      exact (stalled_eq_outer hy).deriv_eq
    rw [he.deriv_eq]
    have hd (y : ℝ) : deriv (fun y : ℝ ↦ y ^ 2) y = 2 * y := by simp
    have h := (hasDerivAt_id x |>.const_mul (2 : ℝ)).deriv
    change deriv (fun y : ℝ ↦ 2 * y) x = _ at h
    rw [funext hd, h]
    simp

private theorem stalled_barrier_bounded (μ : ℝ) (hμ : 0 < μ) :
    BddBelow ((fun x : ℝ ↦ primalDualStalledObjective x - μ * Real.log x) '' Ioi 0) := by
  obtain ⟨A, hA⟩ := (isCompact_closedBall (1 : ℝ) (1 / 2)).bddBelow_image
    stalled_contDiff.continuous.continuousOn
  refine ⟨min (A - 2 * μ) (-(μ ^ 2 / 4)), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hp : 0 < x := hx
  have hl := Real.log_le_self hp.le
  by_cases hb : x ∈ closedBall (1 : ℝ) (1 / 2)
  · have hxb : x ≤ 2 := by
      have h := abs_le.mp (show |x - 1| ≤ (1 / 2 : ℝ) by simpa [mem_closedBall, Real.dist_eq] using hb)
      linarith [h.2]
    have ha : A ≤ primalDualStalledObjective x := hA ⟨x, hb, rfl⟩
    exact (min_le_left _ _).trans (by linarith [mul_le_mul_of_nonneg_left (hl.trans hxb) hμ.le])
  · change min (A - 2 * μ) (-(μ ^ 2 / 4)) ≤ primalDualStalledObjective x - μ * Real.log x
    rw [(stalled_eq_outer hb).eq_of_nhds]
    exact (min_le_right _ _).trans (by
      nlinarith [mul_le_mul_of_nonneg_left hl hμ.le, sq_nonneg (x - μ / 2)])

/-- A scalar rejected trial of Algorithm 13.6.1 with unit barrier
parameter, half fraction-to-boundary, and the exact Taylor objective
model. The safeguarded dual branch (13.6.19) retains the old multiplier. -/
structure ScalarPrimalDualRejectedTrial (P : BTRParams) (f : ℝ → ℝ)
    (x z s Δ x' z' Δ' : ℝ) : Prop where
  primal_pos : 0 < x
  dual_pos : 0 < z
  trial_pos : 0 < x + s
  step_bound : |s| ≤ Δ
  fractional_clearance : (1 / 2 : ℝ) * x ≤ x + s
  model_decrease :
    let g := deriv f x - x⁻¹
    let h := deriv (deriv f) x + z / x
    let τ := min 0 h
    (1 / 4 : ℝ) * max (|g| * min (|g| / (1 + |h|)) (min Δ ((1 / 2 : ℝ) * x)))
      (-τ * min (τ ^ 2) ((min Δ ((1 / 2 : ℝ) * x)) ^ 2)) ≤ -(g * s + h * s ^ 2 / 2)
  predicted_pos :
    let g := deriv f x - x⁻¹
    let h := deriv (deriv f) x + z / x
    0 < -(g * s + h * s ^ 2 / 2)
  ratio_reject :
    let g := deriv f x - x⁻¹
    let h := deriv (deriv f) x + z / x
    ((f x - Real.log x) - (f (x + s) - Real.log (x + s))) /
      (-(g * s + h * s ^ 2 / 2)) < P.η₁
  retain : x' = x ∧ z' = z
  radius_update : P.γ₁ * Δ ≤ Δ' ∧ Δ' ≤ P.γ₂ * Δ

/-- In a bounded primal-dual run with exact Taylor objective models,
all trials can be rejected while the model gradients are zero and the
steps tend to zero. The safeguard retains the dual coordinate at one
quarter, so the AA.8 conclusion of Theorem 13.6.4 fails. -/
theorem theorem_13_6_4_all_rejected_counterexample :
    ∃ Δ : ℕ → ℝ,
      ContDiff ℝ 2 primalDualStalledObjective ∧
      (∃ B : ℝ, ∀ x, |deriv (deriv primalDualStalledObjective) x| ≤ B) ∧
      (∀ μ > 0, BddBelow ((fun x ↦ primalDualStalledObjective x - μ * Real.log x) '' Ioi 0)) ∧
      (∀ j, 0 < Δ j ∧
        ScalarPrimalDualRejectedTrial defaultBTRParams primalDualStalledObjective
          1 (1 / 4) (Δ j) (Δ j) 1 (1 / 4) (Δ (j + 1))) ∧
      deriv primalDualStalledObjective 1 - (1 : ℝ)⁻¹ = 0 ∧ Tendsto Δ atTop (𝓝 0) ∧
      ¬ Tendsto (fun _ : ℕ ↦ (1 / 4 : ℝ) - 1 / 1) atTop (𝓝 0) := by
  let Δ (j : ℕ) := (1 / 2 : ℝ) ^ j * (1 / 8)
  have hΔ (j : ℕ) : 0 < Δ j := by dsimp [Δ]; positivity
  have hbound (j : ℕ) : Δ j ≤ 1 / 8 := by
    dsimp only [Δ]
    exact mul_le_of_le_one_left (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))
  have hφ (s : ℝ) (hs : |s| < 1 / 4) :
      primalDualStalledObjective (1 + s) - Real.log (1 + s) = s ^ 2 / 4 := by
    have hh : 1 + s ∈ ball (1 : ℝ) (1 / 4) := by
      simpa [mem_ball, Real.dist_eq, add_comm] using hs
    rw [(stalled_eq_local hh).eq_of_nhds, stalledLocal]
    ring
  have hg : deriv primalDualStalledObjective 1 - (1 : ℝ)⁻¹ = 0 := by
    rw [stalled_center_derivatives.1]
    norm_num
  have hh : deriv (deriv primalDualStalledObjective) 1 + (1 / 4 : ℝ) / 1 = -(1 / 4 : ℝ) := by
    rw [stalled_center_derivatives.2]
    norm_num
  refine ⟨Δ, stalled_contDiff, stalled_hessian_bounded, stalled_barrier_bounded, ?_, hg, ?_, ?_⟩
  · intro j
    have hp := hΔ j
    have hb := hbound j
    refine ⟨hp, ⟨by norm_num, by norm_num, by linarith, ?_, by linarith, ?_, ?_, ?_,
      ⟨rfl, rfl⟩, ?_⟩⟩
    · rw [abs_of_pos hp]
    · dsimp only
      rw [hg, hh]
      norm_num
      have hmin : min (Δ j) (1 / 2) = Δ j := min_eq_left (by linarith)
      have hs : (Δ j) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
        (sq_le_sq₀ hp.le (by norm_num)).mpr (by linarith)
      rw [hmin]
      simp only [min_eq_right (show (Δ j) ^ 2 ≤ (1 / 16 : ℝ) by nlinarith)] at *
      simp only [max_eq_right (by positivity : (0 : ℝ) ≤ (1 / 4) * (Δ j) ^ 2)]
      nlinarith [sq_nonneg (Δ j)]
    · dsimp only
      rw [hg, hh]
      nlinarith [sq_pos_of_pos hp]
    · dsimp only
      rw [hg, hh, hφ (Δ j) (by rw [abs_of_pos hp]; linarith)]
      have hzero := hφ 0 (by norm_num)
      simp only [add_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div] at hzero
      rw [hzero]
      have hη : 0 < defaultBTRParams.η₁ := defaultBTRParams.eta₁_pos
      apply lt_of_le_of_lt (div_nonpos_of_nonpos_of_nonneg ?_ ?_) hη
      · nlinarith [sq_nonneg (Δ j)]
      · nlinarith [sq_nonneg (Δ j)]
    · have he : Δ (j + 1) = (1 / 2 : ℝ) * Δ j := by
        simp only [Δ, pow_succ]
        ring
      rw [he]
      exact ⟨le_rfl, le_rfl⟩
  · simpa only [Δ, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 8 : ℝ)
  · intro h
    have he := tendsto_nhds_unique
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 / 4 : ℝ) - 1 / 1) atTop (𝓝 ((1 / 4 : ℝ) - 1 / 1))) h
    norm_num at he

end RejectionExample

end ConnGouldToint.Chapter13
