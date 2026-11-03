import Mathlib.Analysis.InnerProductSpace.PiL2
import NumlibSurface.ConnGouldToint.Chapter13.Section03
import NumlibSurface.ConnGouldToint.Chapter13.Section01
import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # The logarithmic barrier model -/

open Filter Metric
open scoped Topology
open scoped BigOperators

namespace ConnGouldToint.Chapter13

variable {ι : Type*} [Fintype ι]

/-- The quadratic model (13.4.2), evaluated at the displacement `s`. -/
noncomputable def logBarrierModel (x s : ι → ℝ) (μ : ℝ) : ℝ :=
  logBarrier x μ - μ * (∑ i, (x i)⁻¹ * s i) +
    μ / 2 * (∑ i, ((x i) ^ 2)⁻¹ * (s i) ^ 2)

/-- The diagonal Hessian formula (13.4.8). -/
theorem logBarrier_hessian (μ : ℝ) {x : ι → ℝ} (hx : ∀ i, 0 < x i) (d e : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (fun y ↦ logBarrier y μ)) x d e =
      μ * ∑ i, ((x i) ^ 2)⁻¹ * d i * e i :=
  Optimization.fderiv_fderiv_logBarrier_apply μ hx d e

/-- The smoothness part AC.1c of Lemma 13.4.1. -/
theorem logBarrier_contDiffOn (μ : ℝ) :
    ContDiffOn ℝ 2 (fun x : ι → ℝ ↦ logBarrier x μ)
      (interior (Optimization.nonnegativeOrthant ι)) := by
  intro x hx
  have hpos : ∀ i, 0 < x i := by
    rw [Optimization.nonnegativeOrthant, interior_pi_set Set.finite_univ] at hx
    simpa only [Set.mem_pi, Set.mem_univ, true_implies, interior_Ici, Set.mem_Ioi] using hx
  exact (Optimization.contDiffAt_logBarrier μ hpos).contDiffWithinAt

/-- The Hessian-bound part AC.4c of Lemma 13.4.1. -/
theorem logBarrier_hessian_bounded (μ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ (1 : ℝ), ∀ x : ι → ℝ, (∀ i, 0 < x i) →
      ε ≤ infDist x (frontier (Optimization.nonnegativeOrthant ι)) →
      ‖fderiv ℝ (fderiv ℝ (fun y ↦ logBarrier y μ)) x‖ ≤ C := by
  refine ⟨max 1 (|μ| * Fintype.card ι * (ε ^ 2)⁻¹), le_max_left _ _, fun x hx hdist ↦ ?_⟩
  exact (Optimization.norm_fderiv_fderiv_logBarrier_le μ hε
    (fun i ↦ hdist.trans (Optimization.infDist_frontier_le_coordinate hx i))).trans
      (le_max_right _ _)

/-- The model (13.4.2) is the second-order Taylor model of the barrier. -/
theorem logBarrierModel_eq_taylor {x : ι → ℝ} (hx : ∀ i, 0 < x i) (s : ι → ℝ) (μ : ℝ) :
    logBarrierModel x s μ = logBarrier x μ + fderiv ℝ (fun y ↦ logBarrier y μ) x s +
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ (fun y ↦ logBarrier y μ)) x s s := by
  change _ = logBarrier x μ + fderiv ℝ (Optimization.logBarrier μ) x s + _
  rw [Optimization.fderiv_logBarrier_apply μ hx, logBarrier_hessian μ hx]
  simp only [logBarrierModel, pow_two, mul_assoc]
  ring


/-- A quadratic model with symmetric bilinear term has affine derivative. -/
theorem barrierQuadratic_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ}
    {g : E →L[ℝ] ℝ} {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hs : ∀ d e, H d e = H e d) (s : E) :
    HasFDerivAt (fun d ↦ a + g d + (1 / 2 : ℝ) * H d d) (g + H s) s := by
  have hquad₀ := H.hasFDerivAt.clm_apply (hasFDerivAt_id s)
  have heq : (H s).comp (ContinuousLinearMap.id ℝ E) + H.flip s = (2 : ℝ) • H s := by
    ext d
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply,
      smul_apply, smul_eq_mul, hs d s]
    ring
  simp only [id_eq] at hquad₀
  rw [heq] at hquad₀
  have hquad : HasFDerivAt (fun d : E ↦ H d d) ((2 : ℝ) • H s) s := by
    exact hquad₀
  have hmodel₀ := (g.hasFDerivAt.const_add a).add
    (hquad.const_smul (1 / 2 : ℝ))
  have heq' : (g + (1 / 2 : ℝ) • ((2 : ℝ) • H s)) = g + H s := by
    rw [smul_smul]
    norm_num
  rw [heq'] at hmodel₀
  exact hmodel₀

private theorem logBarrierModel_fderiv {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    (μ : ℝ) (s : ι → ℝ) :
    fderiv ℝ (logBarrierModel x · μ) s =
      fderiv ℝ (Optimization.logBarrier μ) x +
        fderiv ℝ (fderiv ℝ (Optimization.logBarrier μ)) x s := by
  let g := fderiv ℝ (Optimization.logBarrier μ) x
  let H := fderiv ℝ (fderiv ℝ (Optimization.logBarrier μ)) x
  have hs : ∀ d e, H d e = H e d := by
    intro d e
    rw [show H d e = μ * ∑ i, ((x i) ^ 2)⁻¹ * d i * e i from logBarrier_hessian μ hx d e,
      show H e d = μ * ∑ i, ((x i) ^ 2)⁻¹ * e i * d i from logBarrier_hessian μ hx e d]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hm : (logBarrierModel x · μ) = fun d ↦ logBarrier x μ + g d + (1 / 2 : ℝ) * H d d := by
    funext d
    exact logBarrierModel_eq_taylor hx d μ
  rw [hm]
  exact (barrierQuadratic_hasFDerivAt hs s).fderiv

/-- The log-barrier model agrees with the barrier gradient at its center. -/
theorem logBarrierModel_fderiv_center {x : ι → ℝ} (hx : ∀ i, 0 < x i) (μ : ℝ) :
    fderiv ℝ (logBarrierModel x · μ) 0 = fderiv ℝ (Optimization.logBarrier μ) x := by
  rw [logBarrierModel_fderiv hx, map_zero, add_zero]

/-- The model Hessian is constant and equals the barrier Hessian at the
center. Thus the barrier part of AM.5c is exact, and AC.6b holds with zero
Hessian variation. -/
theorem logBarrierModel_fderiv_fderiv {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    (μ : ℝ) (s : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (logBarrierModel x · μ)) s =
      fderiv ℝ (fderiv ℝ (Optimization.logBarrier μ)) x := by
  rw [show fderiv ℝ (logBarrierModel x · μ) = fun t ↦
      fderiv ℝ (Optimization.logBarrier μ) x +
        fderiv ℝ (fderiv ℝ (Optimization.logBarrier μ)) x t from
      funext (logBarrierModel_fderiv hx μ)]
  exact ((fderiv ℝ (fderiv ℝ (Optimization.logBarrier μ)) x).hasFDerivAt.const_add _).fderiv

/-- The log-barrier model is smooth as a function of the displacement. -/
theorem logBarrierModel_contDiff {x : ι → ℝ} (hx : ∀ i, 0 < x i) (μ : ℝ) :
    ContDiff ℝ 2 (logBarrierModel x · μ) := by
  simp only [logBarrierModel_eq_taylor hx]
  fun_prop

/-- The model interpolates the barrier value at its center. -/
@[simp] theorem logBarrierModel_zero (x : ι → ℝ) (μ : ℝ) :
    logBarrierModel x 0 μ = logBarrier x μ := by
  simp [logBarrierModel]

/-- The AM.4h bound holds for the model Hessian on a layer separated from the boundary. -/
theorem logBarrierModel_hessian_bounded (μ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ (1 : ℝ), ∀ x : ι → ℝ, (∀ i, 0 < x i) →
      ε ≤ infDist x (frontier (Optimization.nonnegativeOrthant ι)) →
      ∀ s : ι → ℝ, ‖fderiv ℝ (fderiv ℝ (logBarrierModel x · μ)) s‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := logBarrier_hessian_bounded (ι := ι) μ hε
  exact ⟨C, hC, fun x hx hdist s ↦ by
    rw [logBarrierModel_fderiv_fderiv hx]
    exact hb x hx hdist⟩

section Outer

variable [DecidableEq ι]

/-- The coordinate gradient of the objective. -/
noncomputable def barrierCoordinateGradient (f : (ι → ℝ) → ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- The stopping tests (13.4.3)–(13.4.5). The Hessian test is written as
a quadratic-form inequality in the Euclidean norm. -/
def BarrierSecondOrderStop (f : (ι → ℝ) → ℝ) (x : ι → ℝ) (μ εD εE : ℝ) : Prop :=
  (∀ i, 0 < x i) ∧
  (∑ i, (barrierCoordinateGradient f x i - μ / x i) ^ 2) ≤ εD ^ 2 ∧
  ∀ d : ι → ℝ, -εE * (∑ i, (d i) ^ 2) ≤
    fderiv ℝ (fderiv ℝ f) x d d + μ * ∑ i, ((x i) ^ 2)⁻¹ * d i * d i

/-- The coordinate residual in (13.4.3) is the gradient of the barrier objective. -/
theorem barrierCoordinateGradient_logBarrierObjective {f : (ι → ℝ) → ℝ} {x : ι → ℝ}
    (hf : DifferentiableAt ℝ f x) (hx : ∀ i, 0 < x i) (μ : ℝ) (i : ι) :
    barrierCoordinateGradient (fun y ↦ logBarrierObjective f y μ) x i =
      barrierCoordinateGradient f x i - μ / x i := by
  have hb := (Optimization.contDiffAt_logBarrier (n := 1) μ hx).differentiableAt (by simp)
  have hd := (hf.hasFDerivAt.add hb.hasFDerivAt).fderiv
  change fderiv ℝ (f + Optimization.logBarrier μ) x (Pi.single i 1) =
    barrierCoordinateGradient f x i - μ / x i
  rw [hd, add_apply, Optimization.fderiv_logBarrier_apply μ hx, barrierCoordinateGradient]
  have hsum : (∑ j, (x j)⁻¹ * (Pi.single i (1 : ℝ) : ι → ℝ) j) = (x i)⁻¹ := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  rw [hsum, div_eq_mul_inv]
  ring

omit [DecidableEq ι] in
/-- The quadratic form in (13.4.4) is that of the barrier objective Hessian. -/
theorem logBarrierObjective_hessian_apply {f : (ι → ℝ) → ℝ} {x : ι → ℝ}
    (hf : ContDiff ℝ 2 f) (hx : ∀ i, 0 < x i) (μ : ℝ) (d : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (fun y ↦ logBarrierObjective f y μ)) x d d =
      fderiv ℝ (fderiv ℝ f) x d d + μ * ∑ i, ((x i) ^ 2)⁻¹ * d i * d i := by
  let b := Optimization.logBarrier (ι := ι) μ
  have hpos : ∀ᶠ y in 𝓝 x, ∀ i, 0 < y i :=
    eventually_all.mpr fun i ↦ (continuous_apply i).continuousAt.eventually (lt_mem_nhds (hx i))
  have he : fderiv ℝ (fun y ↦ logBarrierObjective f y μ) =ᶠ[𝓝 x]
      fun y ↦ fderiv ℝ f y + fderiv ℝ b y := by
    filter_upwards [hpos] with y hy
    have hb := (Optimization.contDiffAt_logBarrier (n := 1) μ hy).differentiableAt (by simp)
    exact ((hf.differentiable (by norm_num) y).hasFDerivAt.add hb.hasFDerivAt).fderiv
  have hf' := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by simp) x
  have hb' := ((Optimization.contDiffAt_logBarrier (n := 2) μ hx).fderiv_right (m := 1)
    (by norm_num)).differentiableAt (by simp)
  rw [he.fderiv_eq]
  change (fderiv ℝ ((fderiv ℝ f + fderiv ℝ (Optimization.logBarrier μ)) :
    (ι → ℝ) → ((ι → ℝ) →L[ℝ] ℝ)) x) d d = _
  rw [(hf'.hasFDerivAt.add hb'.hasFDerivAt).fderiv, add_apply, add_apply]
  change _ + fderiv ℝ (fderiv ℝ (fun y ↦ logBarrier y μ)) x d d = _
  rw [logBarrier_hessian μ hx]

/-- The finite stopping implication in Theorem 13.4.2. The inner analysis
supplies convergence of the squared residual and a nonnegative curvature
limsup. The latter yields arbitrarily late qualifying indices. -/
theorem theorem_13_4_2_of_inner_limits {f : (ι → ℝ) → ℝ} {x : ℕ → ι → ℝ}
    {μ εD εE : ℝ} (hD : 0 < εD) (hE : 0 < εE)
    (hx : ∀ j i, 0 < x j i)
    (hgrad : Tendsto (fun j ↦ ∑ i, (barrierCoordinateGradient f (x j) i - μ / x j i) ^ 2)
      atTop (𝓝 0))
    {lamMin : ℕ → ℝ} (hbelow : atTop.IsCoboundedUnder (· ≤ ·) lamMin)
    (hlimsup : 0 ≤ limsup lamMin atTop)
    (hmin : ∀ j (d : ι → ℝ), lamMin j * (∑ i, (d i) ^ 2) ≤
      fderiv ℝ (fderiv ℝ f) (x j) d d + μ * ∑ i, ((x j i) ^ 2)⁻¹ * d i * d i) :
    ∃ᶠ j in atTop, BarrierSecondOrderStop f (x j) μ εD εE := by
  have hfreq := frequently_lt_of_lt_limsup hbelow ((neg_lt_zero.mpr hE).trans_le hlimsup)
  refine (hfreq.and_eventually (hgrad.eventually (gt_mem_nhds (sq_pos_of_pos hD)))).mono ?_
  intro j hj
  exact ⟨hx j, hj.2.le, fun d ↦
    (mul_le_mul_of_nonneg_right hj.1.le (Finset.sum_nonneg fun i _ ↦ sq_nonneg (d i))).trans
      (hmin j d)⟩

section InnerConvergence

open Chapter06 Set
open Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Algorithm 13.3.1 is a BTR run for any objective extension that matches
all iterates and trials. Its step already passes the fraction-to-boundary
test before the ratio is evaluated. -/
noncomputable def SecondPrimalBarrierInnerRun.toBTRRun
    {P : BTRParams} {C : Set E} {σ : ℝ} {φ F : E → ℝ}
    (r : SecondPrimalBarrierInnerRun P C σ φ)
    (hx : ∀ j, F (r.x j) = φ (r.x j))
    (hs : ∀ j, F (r.x j + r.s j) = φ (r.x j + r.s j)) :
    BTRRun F P (fun _ _ _ _ ↦ True) where
  x := r.x
  s := r.s
  Δ := r.Δ
  p := fun _ ↦ normSeminorm ℝ E
  norm_separates := fun _ _ h ↦ norm_eq_zero.mp h
  model := r.model
  delta_initial_pos := r.initial_radius_pos
  feasible := fun j ↦ by simpa [trustRegion] using r.step_feasible j
  sufficient_decrease := fun _ ↦ trivial
  predicted_pos := r.predicted_pos
  iterate_update := by
    intro j
    classical
    rw [r.iterate_update, primalBarrierRatio, ite_eq_left (r.trial_admissible j)]
    simp only [Optimization.acceptStep, btrRatio, Optimization.reductionRatio, hx, hs]
    split_ifs with h
    · exact ite_eq_left h
    · exact ite_eq_right h
  radius_update := by
    intro j
    have h := r.radius_update j
    rw [primalBarrierRatio, ite_eq_left (r.trial_admissible j)] at h
    simpa only [btrRatio, Optimization.reductionRatio, hx, hs] using h

private theorem barrier_fraction_mul_min_le {q a b c : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : q * a ≤ c) :
    q * min a b ≤ min a (min b c) :=
  le_min ((mul_le_mul_of_nonneg_left (min_le_left _ _) hq).trans
    (mul_le_of_le_one_left ha hq1))
    (le_min ((mul_le_mul_of_nonneg_left (min_le_right _ _) hq).trans
      (mul_le_of_le_one_left hb hq1)) ((mul_le_mul_of_nonneg_left (min_le_left _ _) hq).trans hc))

private theorem sq_min_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (min a b) ^ 2 = min (a ^ 2) (b ^ 2) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left ((sq_le_sq₀ ha hb).mpr h)]
  · rw [min_eq_right h, min_eq_right ((sq_le_sq₀ hb ha).mpr h)]

private theorem abs_sub_min_zero_le (a b : ℝ) : |min 0 a - min 0 b| ≤ |a - b| := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [min_eq_right ha, min_eq_right hb]
  · rw [min_eq_right ha, min_eq_left hb, sub_zero, abs_of_nonpos ha,
      abs_of_nonpos (sub_nonpos.mpr (ha.trans hb))]
    linarith
  · rw [min_eq_left ha, min_eq_right hb, abs_of_nonneg (sub_nonneg.mpr hb),
      abs_of_nonneg (sub_nonneg.mpr (hb.trans ha))]
    linarith
  · simp [min_eq_left ha, min_eq_left hb]

/-- The first-order limit and the frequently nonnegative curvature bound
used by Theorem 13.4.2 for Algorithm 13.3.1. The extension has the same
values at the iterates and trials and agrees with the model derivatives
at the centers. A fixed positive clearance and uniform bounds on the
first- and second-order measures remove the caps in (13.3.2) at the
cost of fixed factors. -/
theorem theorem_13_4_2_inner_of_extension [Nontrivial E]
    {P : BTRParams} {C : Set E} {σ : ℝ} {φ F : E → ℝ}
    (r : SecondPrimalBarrierInnerRun P C σ φ)
    (hx : ∀ j, F (r.x j) = φ (r.x j))
    (hs : ∀ j, F (r.x j + r.s j) = φ (r.x j + r.s j))
    (hf : ContDiff ℝ 2 F) (hlower : BddBelow (range F))
    {K L D G T : ℝ} (hD : 0 < D) (hG : 0 < G) (hT : 0 < T)
    (hclear : ∀ j, D ≤ (1 - σ) * infDist (r.x j) (frontier C))
    (hH : ∀ y, ‖fderiv ℝ (fderiv ℝ F) y‖ ≤ L)
    (hβ₁ : ∀ j, 1 ≤ r.β j) (hβK : ∀ j, r.β j ≤ K)
    (hGbd : ∀ j, ‖r.g j‖ ≤ G)
    (hτbd : ∀ j, |r.τ j| ≤ T)
    (hτ : ∀ j, r.τ j = min 0
      (leastUnitCurvature (fderiv ℝ (fderiv ℝ (r.model j)) (r.x j))))
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
    (hagree : ModelHessianAgreement F r.model r.x) :
    Tendsto (fun j ↦ ‖fderiv ℝ F (r.x j)‖) atTop (𝓝 0) ∧
    ∀ ε > (0 : ℝ), ∃ᶠ j in atTop,
      -ε < leastUnitCurvature (fderiv ℝ (fderiv ℝ F) (r.x j)) := by
  let run := r.toBTRRun hx hs
  have hΔ (j : ℕ) : 0 < r.Δ j := run.delta_pos j
  have hβ (j : ℕ) := zero_lt_one.trans_le (hβ₁ j)
  have hg (j : ℕ) : r.g j = gradient F (r.x j) := by
    rw [r.gradient_model]
    unfold gradient
    rw [hgrad]
  let q := min 1 (D / G)
  have hq : 0 < q := lt_min zero_lt_one (div_pos hD hG)
  have hq1 : q ≤ 1 := min_le_left _ _
  let κ := min (1 / 2) (r.κ * q)
  have hκ : κ ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_min (by norm_num) (mul_pos r.decrease_constant hq),
      (min_le_left _ _).trans_lt (by norm_num)⟩
  have hdec (j : ℕ) : HasSufficientModelDecrease (r.model j) (r.x j) (r.s j)
      (gradient F (r.x j)) (r.β j) (r.Δ j) κ := by
    rw [← hg]
    refine ⟨hκ, ?_⟩
    have hGq : q * (‖r.g j‖ / r.β j) ≤ (1 - σ) * infDist (r.x j) (frontier C) := calc
      _ ≤ q * ‖r.g j‖ := mul_le_mul_of_nonneg_left (div_le_self (norm_nonneg _) (hβ₁ j)) hq.le
      _ ≤ q * G := mul_le_mul_of_nonneg_left (hGbd j) hq.le
      _ ≤ D := (le_div_iff₀ hG).mp (min_le_right _ _)
      _ ≤ _ := hclear j
    have hcap := barrier_fraction_mul_min_le hq.le hq1
      (div_nonneg (norm_nonneg _) (hβ j).le) (hΔ j).le hGq
    have hmain := mul_le_mul_of_nonneg_left hcap (mul_nonneg r.decrease_constant.le (norm_nonneg (r.g j)))
    have hm : r.κ * (‖r.g j‖ * min (‖r.g j‖ / r.β j)
        (constrainedBarrierRadius (r.Δ j) σ (infDist (r.x j) (frontier C)))) ≤
        r.model j (r.x j) - r.model j (r.x j + r.s j) :=
      (mul_le_mul_of_nonneg_left (le_max_left _ _) r.decrease_constant.le).trans
        (r.sufficient_decrease j)
    calc
      _ ≤ (r.κ * q) * ‖r.g j‖ * min (‖r.g j‖ / r.β j) (r.Δ j) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _))
          (le_min (div_nonneg (norm_nonneg _) (hβ j).le) (hΔ j).le)
      _ = (r.κ * ‖r.g j‖) * (q * min (‖r.g j‖ / r.β j) (r.Δ j)) := by ring
      _ ≤ _ := by
        exact hmain.trans (by simpa only [constrainedBarrierRadius, mul_assoc] using hm)
  have hgradlim := theorem_6_4_6 run r.β hβ hβK hval hdec herr hlower hf hH
    (show (0 : ℝ) ≤ 1 by norm_num) (fun _ _ ↦ by simp [run, SecondPrimalBarrierInnerRun.toBTRRun])
  have hcrit : Tendsto (fun j ↦ ‖fderiv ℝ F (r.x j)‖) atTop (𝓝 0) := by
    simpa only [run, SecondPrimalBarrierInnerRun.toBTRRun, gradient, LinearIsometryEquiv.norm_map]
      using hgradlim
  have hsmall : smallRadiusModelAgreement run :=
    smallRadiusModelAgreement_of_hessians run hf hm hDm hval hgrad hcrit hagree
      zero_lt_one (fun j ↦ by
        change ‖r.s j‖ ≤ 1 * r.Δ j
        rw [one_mul]
        exact r.step_feasible j) hvar
  refine ⟨hcrit, ?_⟩
  let curv (j : ℕ) := min 0 (leastUnitCurvature (fderiv ℝ (fderiv ℝ F) (r.x j)))
  have ha : Tendsto (fun j ↦ |curv j - r.τ j|) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ ↦ abs_nonneg _) (fun j ↦ ?_) (hagree hcrit)
    rw [hτ]
    exact (abs_sub_min_zero_le _ _).trans
      (abs_sub_leastUnitCurvature_le _ _)
  let q₂ := min 1 (D ^ 2 / T ^ 2)
  have hq₂ : 0 < q₂ := lt_min zero_lt_one (div_pos (sq_pos_of_pos hD) (sq_pos_of_pos hT))
  have hsecond (j : ℕ) : HasNegativeCurvatureDecrease (r.model j) (r.x j) (r.s j)
      (r.τ j) (r.Δ j) (r.κ * q₂) := by
    refine ⟨mul_pos r.decrease_constant hq₂, fun hneg ↦ ?_⟩
    let b := (1 - σ) * infDist (r.x j) (frontier C)
    have hb : 0 < b := hD.trans_le (hclear j)
    have hTq : q₂ * (r.τ j) ^ 2 ≤ b ^ 2 := calc
      _ ≤ q₂ * T ^ 2 := mul_le_mul_of_nonneg_left
        (by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hT.le).mpr (hτbd j)) hq₂.le
      _ ≤ D ^ 2 := (le_div_iff₀ (sq_pos_of_pos hT)).mp (min_le_right _ _)
      _ ≤ _ := (sq_le_sq₀ hD.le hb.le).mpr (hclear j)
    have hcap := barrier_fraction_mul_min_le hq₂.le (min_le_left _ _)
      (sq_nonneg (r.τ j)) (sq_nonneg (r.Δ j)) hTq
    rw [← sq_min_of_nonneg (a := r.Δ j) (hΔ j).le hb.le] at hcap
    have hh := mul_le_mul_of_nonneg_left hcap
      (mul_nonneg r.decrease_constant.le (neg_nonneg.mpr hneg.le))
    have hm : r.κ * (-r.τ j * min ((r.τ j) ^ 2)
        (constrainedBarrierRadius (r.Δ j) σ (infDist (r.x j) (frontier C)) ^ 2)) ≤
        r.model j (r.x j) - r.model j (r.x j + r.s j) :=
      (mul_le_mul_of_nonneg_left (le_max_right _ _) r.decrease_constant.le).trans
        (r.sufficient_decrease j)
    rw [abs_of_neg hneg]
    calc
      _ = (r.κ * -r.τ j) * (q₂ * min ((r.τ j) ^ 2) ((r.Δ j) ^ 2)) := by ring
      _ ≤ _ := hh.trans (by simpa only [constrainedBarrierRadius, mul_assoc, b] using hm)
  intro ε hε
  exact (theorem_6_6_4 run (mul_pos r.decrease_constant hq₂) hval hlower hsmall ha hsecond ε hε).mono
    (fun j hj ↦ hj.trans_le (min_le_right _ _))

omit [CompleteSpace E] in
private theorem leastUnitCurvature_mul_norm_sq_le [Nontrivial E]
    (H : E →L[ℝ] E →L[ℝ] ℝ) (v : E) :
    leastUnitCurvature H * ‖v‖ ^ 2 ≤ H v v := by
  by_cases hv : v = 0
  · simp [hv]
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u : sphere (0 : E) 1 :=
    ⟨‖v‖⁻¹ • v, mem_sphere_zero_iff_norm.mpr (by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hvn.le), inv_mul_cancel₀ hvn.ne'])⟩
  have hlower : BddBelow (range (fun u : sphere (0 : E) 1 ↦ H u u)) := by
    refine ⟨-‖H‖, ?_⟩
    rintro _ ⟨w, rfl⟩
    have hw : ‖(w : E)‖ = 1 := norm_eq_of_mem_sphere w
    have h₁ := (H w).le_opNorm (w : E)
    have h₂ := H.le_opNorm (w : E)
    simp only [hw, mul_one, Real.norm_eq_abs] at h₁ h₂
    linarith [(abs_le.mp (h₁.trans h₂)).1]
  have hq := ciInf_le hlower u
  have hh := mul_le_mul_of_nonneg_right hq (sq_nonneg ‖v‖)
  change leastUnitCurvature H * ‖v‖ ^ 2 ≤ H (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) * ‖v‖ ^ 2 at hh
  simp only [map_smul, smul_apply, smul_eq_mul] at hh
  have heq : (‖v‖⁻¹ * (‖v‖⁻¹ * H v v)) * ‖v‖ ^ 2 = H v v := by field_simp
  simpa only [heq] using hh

end InnerConvergence

section EuclideanStopping

open Chapter06 Set

variable [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
private theorem barrier_euclidean_norm_sq (d : ι → ℝ) :
    ‖(WithLp.toLp 2 d : EuclideanSpace ℝ ι)‖ ^ 2 = ∑ i, (d i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
  · simp only [Real.norm_eq_abs, sq_abs]
  · exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The continuous linear coordinate map into the Euclidean product. -/
noncomputable def barrierEuclideanCoordinates : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.toContinuousLinearMap

omit [DecidableEq ι] [Nonempty ι] in
private theorem barrier_composed_hessian {F : EuclideanSpace ℝ ι → ℝ}
    (hf : ContDiff ℝ 2 F) (x d : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (F ∘ barrierEuclideanCoordinates)) x d d =
      fderiv ℝ (fderiv ℝ F) (barrierEuclideanCoordinates x)
        (barrierEuclideanCoordinates d) (barrierEuclideanCoordinates d) := by
  let T : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι := barrierEuclideanCoordinates
  let A : (EuclideanSpace ℝ ι →L[ℝ] ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (ι → ℝ) (EuclideanSpace ℝ ι) ℝ).flip T
  have he : fderiv ℝ (F ∘ T) = fun y ↦ A (fderiv ℝ F (T y)) := by
    funext y
    exact (((hf.differentiable (by norm_num) (T y)).hasFDerivAt).comp y T.hasFDerivAt).fderiv
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) (T x)
  have hd := A.hasFDerivAt.comp x (hdf.hasFDerivAt.comp x T.hasFDerivAt)
  change HasFDerivAt (fun y ↦ A (fderiv ℝ F (T y))) _ x at hd
  change fderiv ℝ (fderiv ℝ (F ∘ T)) x d d = _
  rw [he, hd.fderiv]
  rfl

/-- The inner limits give the coordinate stopping tests of Theorem 13.4.2.
The two derivative identities are the gradient and Hessian transformation
under the Euclidean coordinate map at the positive iterates. -/
theorem theorem_13_4_2_of_extension {f : (ι → ℝ) → ℝ} {F : EuclideanSpace ℝ ι → ℝ}
    {x : ℕ → EuclideanSpace ℝ ι} {μ εD εE : ℝ} (hD : 0 < εD) (hE : 0 < εE)
    (hx : ∀ j i, 0 < (x j).ofLp i)
    (hDmap : ∀ j i,
      barrierCoordinateGradient f (x j).ofLp i - μ / (x j).ofLp i =
        fderiv ℝ F (x j) (WithLp.toLp 2 (Pi.single i 1)))
    (hHmap : ∀ j (d : ι → ℝ),
      fderiv ℝ (fderiv ℝ f) (x j).ofLp d d + μ * ∑ i, (((x j).ofLp i) ^ 2)⁻¹ * d i * d i =
        fderiv ℝ (fderiv ℝ F) (x j) (WithLp.toLp 2 d) (WithLp.toLp 2 d))
    (hgrad : Tendsto (fun j ↦ ‖fderiv ℝ F (x j)‖) atTop (𝓝 0))
    (hcurv : ∀ ε > (0 : ℝ), ∃ᶠ j in atTop,
      -ε < leastUnitCurvature (fderiv ℝ (fderiv ℝ F) (x j))) :
    ∃ᶠ j in atTop, BarrierSecondOrderStop f (x j).ofLp μ εD εE := by
  have hDlim : Tendsto (fun j ↦
      ∑ i, (barrierCoordinateGradient f (x j).ofLp i - μ / (x j).ofLp i) ^ 2) atTop (𝓝 0) := by
    rw [← Finset.sum_const_zero (s := (Finset.univ : Finset ι))]
    apply tendsto_finsetSum Finset.univ
    intro i _
    let v : EuclideanSpace ℝ ι := WithLp.toLp 2 (Pi.single i 1)
    have hterm : Tendsto (fun j ↦
        barrierCoordinateGradient f (x j).ofLp i - μ / (x j).ofLp i) atTop (𝓝 0) :=
      squeeze_zero_norm' (a := fun j ↦ ‖fderiv ℝ F (x j)‖ * ‖v‖)
        (Eventually.of_forall fun j ↦ by rw [hDmap]; exact (fderiv ℝ F (x j)).le_opNorm v)
        (by simpa using hgrad.mul_const ‖v‖)
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using hterm.pow 2
  refine ((hcurv εE hE).and_eventually
    (hDlim.eventually (gt_mem_nhds (sq_pos_of_pos hD)))).mono ?_
  intro j hj
  refine ⟨hx j, hj.2.le, fun d ↦ ?_⟩
  rw [hHmap, ← barrier_euclidean_norm_sq]
  exact (mul_le_mul_of_nonneg_right hj.1.le (sq_nonneg _)).trans
    (leastUnitCurvature_mul_norm_sq_le _ _)

/-- A smooth extension that agrees with the barrier objective in a
neighborhood of each iterate satisfies the coordinate derivative identities
in the stopping transfer. -/
theorem theorem_13_4_2_of_local_extension {f : (ι → ℝ) → ℝ} {F : EuclideanSpace ℝ ι → ℝ}
    {x : ℕ → EuclideanSpace ℝ ι} {μ εD εE : ℝ} (hD : 0 < εD) (hE : 0 < εE)
    (hf : ContDiff ℝ 2 f) (hF : ContDiff ℝ 2 F) (hx : ∀ j i, 0 < (x j).ofLp i)
    (hlocal : ∀ j, (F ∘ barrierEuclideanCoordinates) =ᶠ[𝓝 (x j).ofLp]
      fun y ↦ logBarrierObjective f y μ)
    (hgrad : Tendsto (fun j ↦ ‖fderiv ℝ F (x j)‖) atTop (𝓝 0))
    (hcurv : ∀ ε > (0 : ℝ), ∃ᶠ j in atTop,
      -ε < leastUnitCurvature (fderiv ℝ (fderiv ℝ F) (x j))) :
    ∃ᶠ j in atTop, BarrierSecondOrderStop f (x j).ofLp μ εD εE := by
  have hTx (j : ℕ) : barrierEuclideanCoordinates (x j).ofLp = x j :=
    WithLp.toLp_ofLp 2 (x j)
  refine theorem_13_4_2_of_extension hD hE hx ?_ ?_ hgrad hcurv
  · intro j i
    rw [← barrierCoordinateGradient_logBarrierObjective
      (hf.differentiable (by norm_num) _) (hx j)]
    unfold barrierCoordinateGradient
    rw [← (hlocal j).fderiv_eq]
    have hh := ((hF.differentiable (by norm_num) _).hasFDerivAt.comp
      (x j).ofLp barrierEuclideanCoordinates.hasFDerivAt).fderiv
    rw [hh, ContinuousLinearMap.comp_apply, hTx]
    rfl
  · intro j d
    rw [← logBarrierObjective_hessian_apply hf (hx j), ← (hlocal j).fderiv.fderiv_eq,
      barrier_composed_hessian hF, hTx]
    rfl

omit [DecidableEq ι] in
/-- A globally lower-bounded objective with bounded Hessian and AW.2 at a
larger parameter gives uniform Euclidean clearance for the actual accepted
iterates of a primal barrier inner run. -/
theorem PrimalBarrierInnerRun.euclidean_clearance_of_global_lower
    {P : BTRParams} {f : (ι → ℝ) → ℝ} {σ μ ν L A H : ℝ}
    (r : PrimalBarrierInnerRun P
      ((WithLp.ofLp : EuclideanSpace ℝ ι → (ι → ℝ)) ⁻¹' Optimization.nonnegativeOrthant ι)
      σ (fun x ↦ logBarrierObjective f x.ofLp μ))
    (hμ : 0 < μ) (hν : μ < ν) (hf : ContDiff ℝ 2 f)
    (hlower : ∀ y, L ≤ f y) (hH : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (hbar : ∀ y : ι → ℝ, (∀ i, 0 < y i) → A ≤ logBarrierObjective f y ν) :
    ∃ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ j,
      ε ≤ infDist (r.x j) (frontier
        ((WithLp.ofLp : EuclideanSpace ℝ ι → (ι → ℝ)) ⁻¹' Optimization.nonnegativeOrthant ι)) := by
  let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).toHomeomorph
  let O := Optimization.nonnegativeOrthant ι
  let C := T ⁻¹' O
  have hCfront : T ⁻¹' frontier O = frontier C := T.preimage_frontier O
  have hxp (j : ℕ) (i : ι) : 0 < (r.x j).ofLp i := by
    have hh : r.x j ∈ interior C := r.interior_iterate j
    rw [← T.preimage_interior O] at hh
    have hh' : (r.x j).ofLp ∈ interior O := hh
    change (r.x j).ofLp ∈ interior (Set.univ.pi (fun _ : ι ↦ Ici (0 : ℝ))) at hh'
    rw [interior_pi_set Set.finite_univ] at hh'
    exact (by simpa only [Set.mem_pi, Set.mem_univ, true_implies, interior_Ici, Set.mem_Ioi] using hh' :
      ∀ i, 0 < (r.x j).ofLp i) i
  obtain ⟨ε, hε, hbound⟩ := logBarrier_sublevel_separation_of_global_lower
    hμ hν hf hlower hH hbar hxp (fun j ↦ r.objective_antitone (Nat.zero_le j))
  have hzero : (0 : EuclideanSpace ℝ ι) ∈ frontier C := by
    rw [← hCfront]
    apply Optimization.mem_frontier_nonnegativeOrthant.mpr
    exact ⟨fun _ ↦ le_rfl, Classical.arbitrary ι, rfl⟩
  refine ⟨ε, hε, fun j ↦ (le_infDist ⟨0, hzero⟩).mpr ?_⟩
  intro y hy
  have hy' : y.ofLp ∈ frontier O := by
    rw [← hCfront] at hy
    exact hy
  obtain ⟨_, i, hi⟩ := Optimization.mem_frontier_nonnegativeOrthant.mp hy'
  have hxi := (hbound j).trans (Optimization.infDist_frontier_le_coordinate (hxp j) i)
  have hnorm : |(r.x j - y).ofLp i| ≤ ‖r.x j - y‖ := by
    rw [EuclideanSpace.norm_eq]
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
    exact Finset.single_le_sum (fun k _ ↦ sq_nonneg ‖(r.x j - y).ofLp k‖) (Finset.mem_univ i)
  rw [WithLp.ofLp_sub, Pi.sub_apply, hi, sub_zero, abs_of_pos (hxp j i)] at hnorm
  exact hxi.trans (by simpa only [dist_eq_norm] using hnorm)

end EuclideanStopping


/-- The asymptotically active constraints of a sequence. -/
def AsymptoticallyActive {α : Type*} (l : Filter α) (x : α → ι → ℝ) (i : ι) : Prop :=
  Tendsto (fun k ↦ x k i) l (𝓝 0)

/-- Each coordinate either tends to zero or is eventually bounded away from zero. -/
def ConsistentlyActive {α : Type*} (l : Filter α) (x : α → ι → ℝ) : Prop :=
  ∀ i, AsymptoticallyActive l x i ∨ ∃ δ > 0, ∀ᶠ k in l, δ ≤ x k i

private theorem barrier_coordinate_residual_le {f : (ι → ℝ) → ℝ}
    {x : ι → ℝ} {μ εD εE : ℝ} (hs : BarrierSecondOrderStop f x μ εD εE)
    (hε : 0 ≤ εD) (i : ι) :
    |barrierCoordinateGradient f x i - μ / x i| ≤ εD := by
  apply (sq_le_sq₀ (abs_nonneg _) hε).mp
  rw [sq_abs]
  exact (Finset.single_le_sum (fun j _ ↦ sq_nonneg
    (barrierCoordinateGradient f x j - μ / x j)) (Finset.mem_univ i)).trans hs.2.1

private theorem barrier_ratio_tendsto_zero {α : Type*} {l : Filter α} {μ v : α → ℝ}
    (hμ : Tendsto μ l (𝓝 0)) (hμpos : ∀ k, 0 ≤ μ k)
    {δ : ℝ} (hδ : 0 < δ) (hv : ∀ᶠ k in l, δ ≤ v k) :
    Tendsto (fun k ↦ μ k / v k) l (𝓝 0) := by
  apply squeeze_zero' (g := fun k ↦ μ k / δ)
  · filter_upwards [hv] with k hk
    exact div_nonneg (hμpos k) (hδ.le.trans hk)
  · filter_upwards [hv] with k hk
    exact div_le_div_of_nonneg_left (hμpos k) hδ hk
  · simpa using hμ.div_const δ

omit [DecidableEq ι] in
private theorem barrier_hessian_correction_tendsto_zero {α : Type*} {l : Filter α}
    {x : α → ι → ℝ} {μ : α → ℝ} (hμ : Tendsto μ l (𝓝 0)) (hμpos : ∀ k, 0 ≤ μ k)
    (d : ι → ℝ) (hfree : ∀ i, d i ≠ 0 → ∃ δ > 0, ∀ᶠ k in l, δ ≤ x k i) :
    Tendsto (fun k ↦ μ k * ∑ i, ((x k i) ^ 2)⁻¹ * d i * d i) l (𝓝 0) := by
  simp only [Finset.mul_sum]
  rw [← Finset.sum_const_zero (s := (Finset.univ : Finset ι))]
  apply tendsto_finsetSum Finset.univ
  intro i _
  by_cases hi : d i = 0
  · simpa [hi] using (tendsto_const_nhds : Tendsto (fun _ : α ↦ (0 : ℝ)) l (𝓝 0))
  obtain ⟨δ, hδ, hxi⟩ := hfree i hi
  have hr : Tendsto (fun k ↦ μ k / (x k i) ^ 2) l (𝓝 0) :=
    barrier_ratio_tendsto_zero hμ hμpos (sq_pos_of_pos hδ)
      (hxi.mono fun k hk ↦ (sq_le_sq₀ hδ.le (hδ.le.trans hk)).mpr hk)
  simpa only [div_eq_mul_inv, mul_assoc, zero_mul] using (hr.mul_const (d i)).mul_const (d i)

/-- Theorem 13.4.3. Lower-limit inequalities are written in eventual form:
each negative tolerance is eventually a lower bound. This also covers
sequences whose real-valued lower limit diverges to positive infinity. -/
theorem theorem_13_4_3 {α : Type*} {l : Filter α} {f : (ι → ℝ) → ℝ}
    {x : α → ι → ℝ} {μ εD εE : α → ℝ}
    (hμ : Tendsto μ l (𝓝 0)) (hμpos : ∀ k, 0 ≤ μ k)
    (hD : Tendsto εD l (𝓝 0)) (hDpos : ∀ k, 0 ≤ εD k)
    (hE : Tendsto εE l (𝓝 0))
    (hstop : ∀ k, BarrierSecondOrderStop f (x k) (μ k) (εD k) (εE k)) :
    (∀ i η, 0 < η → ∀ᶠ k in l, -η ≤ barrierCoordinateGradient f (x k) i) ∧
    (∀ i, (∃ δ > 0, ∀ᶠ k in l, δ ≤ x k i) →
      Tendsto (fun k ↦ barrierCoordinateGradient f (x k) i) l (𝓝 0)) ∧
    ∀ d : ι → ℝ, (∀ i, d i ≠ 0 → ∃ δ > 0, ∀ᶠ k in l, δ ≤ x k i) →
      ∀ η, 0 < η → ∀ᶠ k in l, -η ≤ fderiv ℝ (fderiv ℝ f) (x k) d d := by
  have herr (k : α) (i : ι) :=
    barrier_coordinate_residual_le (hstop k) (hDpos k) i
  refine ⟨?_, ?_, ?_⟩
  · intro i η hη
    filter_upwards [hD.eventually (gt_mem_nhds hη)] with k hk
    have hh := (abs_le.mp (herr k i)).1
    have hp := div_nonneg (hμpos k) ((hstop k).1 i).le
    linarith
  · intro i ⟨δ, hδ, hxi⟩
    have hr := barrier_ratio_tendsto_zero hμ hμpos hδ hxi
    have he : Tendsto (fun k ↦ barrierCoordinateGradient f (x k) i - μ k / x k i) l (𝓝 0) :=
      squeeze_zero_norm' (Eventually.of_forall fun k ↦ by simpa [Real.norm_eq_abs] using herr k i)
        hD
    simpa only [sub_add_cancel, zero_add] using he.add hr
  · intro d hd η hη
    have hc := barrier_hessian_correction_tendsto_zero hμ hμpos d hd
    have he := hE.mul_const (∑ i, (d i) ^ 2)
    have hec : Tendsto
        (fun k ↦ εE k * (∑ i, (d i) ^ 2) + μ k * ∑ i, ((x k i) ^ 2)⁻¹ * d i * d i)
        l (𝓝 0) := by
      simpa only [zero_mul, zero_add] using he.add hc
    filter_upwards [hec.eventually (gt_mem_nhds hη)] with k hk
    linarith [(hstop k).2.2 d]

/-- Along a consistently active subsequence, all coordinates outside the
asymptotically active set are eventually separated from the boundary. -/
theorem theorem_13_4_3_consistentlyActive {α : Type*} {l : Filter α}
    {f : (ι → ℝ) → ℝ} {x : α → ι → ℝ} (ha : ConsistentlyActive l x)
    {μ εD εE : α → ℝ} (hμ : Tendsto μ l (𝓝 0)) (hμpos : ∀ k, 0 ≤ μ k)
    (hD : Tendsto εD l (𝓝 0)) (hDpos : ∀ k, 0 ≤ εD k)
    (hE : Tendsto εE l (𝓝 0))
    (hstop : ∀ k, BarrierSecondOrderStop f (x k) (μ k) (εD k) (εE k)) :
    (∀ i, ¬ AsymptoticallyActive l x i →
      Tendsto (fun k ↦ barrierCoordinateGradient f (x k) i) l (𝓝 0)) ∧
    ∀ d : ι → ℝ, (∀ i, AsymptoticallyActive l x i → d i = 0) →
      ∀ η, 0 < η → ∀ᶠ k in l, -η ≤ fderiv ℝ (fderiv ℝ f) (x k) d d := by
  obtain ⟨_, hg, hH⟩ := theorem_13_4_3 hμ hμpos hD hDpos hE hstop
  refine ⟨fun i hi ↦ hg i ((ha i).resolve_left hi), ?_⟩
  exact fun d hd ↦ hH d fun i hi ↦ (ha i).resolve_left fun h ↦ hi (hd i h)

/-- Weak second-order criticality of a limit point, in derivative form.
The Hessian is tested on the nullspace of all active bounds. -/
theorem corollary_13_4_4 {α : Type*} {l : Filter α} [l.NeBot]
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    {x : α → ι → ℝ} {xstar : ι → ℝ} (hx : Tendsto x l (𝓝 xstar))
    {μ εD εE : α → ℝ} (hμ : Tendsto μ l (𝓝 0)) (hμpos : ∀ k, 0 ≤ μ k)
    (hD : Tendsto εD l (𝓝 0)) (hDpos : ∀ k, 0 ≤ εD k) (hE : Tendsto εE l (𝓝 0))
    (hstop : ∀ k, BarrierSecondOrderStop f (x k) (μ k) (εD k) (εE k)) :
    (∀ i, 0 ≤ xstar i) ∧
    (∀ i, 0 ≤ barrierCoordinateGradient f xstar i ∧
      (0 < xstar i → barrierCoordinateGradient f xstar i = 0)) ∧
    ∀ d : ι → ℝ, (∀ i, xstar i = 0 → d i = 0) → 0 ≤ fderiv ℝ (fderiv ℝ f) xstar d d := by
  have hxi (i : ι) : Tendsto (fun k ↦ x k i) l (𝓝 (xstar i)) :=
    ((continuous_apply i).tendsto xstar).comp hx
  have hfeas (i : ι) : 0 ≤ xstar i :=
    ge_of_tendsto (hxi i) (Eventually.of_forall fun k ↦ ((hstop k).1 i).le)
  have haway (i : ι) (hi : 0 < xstar i) : ∃ δ > 0, ∀ᶠ k in l, δ ≤ x k i :=
    ⟨xstar i / 2, half_pos hi, ((hxi i).eventually (lt_mem_nhds (half_lt_self hi))).mono
      fun _ h ↦ h.le⟩
  obtain ⟨hg₀, hg, hH⟩ := theorem_13_4_3 hμ hμpos hD hDpos hE hstop
  have hlimit_nonneg {u : α → ℝ} {a : ℝ} (hu : Tendsto u l (𝓝 a))
      (hb : ∀ η > 0, ∀ᶠ k in l, -η ≤ u k) : 0 ≤ a := by
    by_contra! hn
    have := ge_of_tendsto hu (hb (-a / 2) (by linarith))
    linarith
  refine ⟨hfeas, ?_, ?_⟩
  · intro i
    have hc : Continuous (fun y ↦ barrierCoordinateGradient f y i) :=
      (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have ht := (hc.tendsto xstar).comp hx
    exact ⟨hlimit_nonneg ht (hg₀ i), fun hi ↦ tendsto_nhds_unique ht (hg i (haway i hi))⟩
  · intro d hd
    have hf' := hf.fderiv_right (m := 1) (by norm_num)
    have hc : Continuous (fun y ↦ fderiv ℝ (fderiv ℝ f) y d d) :=
      ((hf'.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
    exact hlimit_nonneg ((hc.tendsto xstar).comp hx)
      (hH d fun i hi ↦ haway i (lt_of_le_of_ne (hfeas i) (fun hz ↦ hi (hd i hz.symm))))

end Outer


section PrimalOuterRun

open Chapter06 Set

/-- The closed nonnegative orthant with the Euclidean metric. Its interior
is the domain of the logarithmic barrier. -/
def logBarrierEuclideanDomain (ι : Type*) [Fintype ι] : Set (EuclideanSpace ℝ ι) :=
  WithLp.ofLp ⁻¹' Optimization.nonnegativeOrthant ι

private theorem mem_interior_logBarrierEuclideanDomain (x : EuclideanSpace ℝ ι) :
    x ∈ interior (logBarrierEuclideanDomain ι) ↔ ∀ i, 0 < x.ofLp i := by
  let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).toHomeomorph
  change x ∈ interior (T ⁻¹' Optimization.nonnegativeOrthant ι) ↔ _
  rw [← T.preimage_interior]
  change x.ofLp ∈ interior (Set.univ.pi (fun _ : ι ↦ Ici (0 : ℝ))) ↔ _
  rw [interior_pi_set Set.finite_univ]
  simp only [Set.mem_pi, Set.mem_univ, true_implies, interior_Ici, Set.mem_Ioi]

/-- Algorithm 13.4.1 can either reject an exterior trial after computing
it, or impose the fraction-to-boundary condition in the step calculation. -/
inductive PrimalBarrierStepRule
  | rejectOutside
  | constrainTrial

/-- A finite primal log-barrier inner minimization. The exact quadratic
barrier term is (13.4.2). The selected step rule distinguishes the
uncapped decrease and guarded ratio of Algorithm 13.2.1 from the
feasible capped decrease of Algorithm 13.3.1. -/
structure PrimalLogBarrierInnerPrefix (P : BTRParams) (f : (ι → ℝ) → ℝ)
    (σ μ : ℝ) (x : ℕ → EuclideanSpace ℝ ι) (J : ℕ)
    extends PrimalBarrierInnerPrefix P (logBarrierEuclideanDomain ι) σ
      (fun v ↦ logBarrierObjective f v.ofLp μ) x J where
  rule : PrimalBarrierStepRule
  fraction : σ ∈ Ioo (0 : ℝ) 1
  objectiveModel : ℕ → EuclideanSpace ℝ ι → ℝ
  model_split : ∀ j < J, ∀ v ∈ closedBall (x j) (Δ j),
    model j v = objectiveModel j v + logBarrierModel (x j).ofLp (v - x j).ofLp μ
  objective_model_twice_diff : ∀ j < J,
    DifferentiableOn ℝ (objectiveModel j) (closedBall (x j) (Δ j)) ∧
    DifferentiableOn ℝ (fderiv ℝ (objectiveModel j)) (closedBall (x j) (Δ j))
  objective_model_value : ∀ j < J, objectiveModel j (x j) = f (x j).ofLp
  objective_model_derivative : ∀ j < J, fderiv ℝ (objectiveModel j) (x j) =
    fderiv ℝ (fun v : EuclideanSpace ℝ ι ↦ f v.ofLp) (x j)
  objective_model_hessian_bound : ∃ K : ℝ, ∀ j < J, ∀ v ∈ closedBall (x j) (Δ j),
    v ∈ interior (logBarrierEuclideanDomain ι) → ‖fderiv ℝ (fderiv ℝ (objectiveModel j)) v‖ ≤ K
  κ : ℝ
  decrease_constant : κ ∈ Ioo (0 : ℝ) 1
  step_rule : ∀ j < J,
    let g := gradient (model j) (x j)
    let β := 1 + sSup ((fun v ↦ ‖fderiv ℝ (fderiv ℝ (model j)) v‖) '' closedBall (x j) (Δ j))
    let τ := min 0 (leastUnitCurvature (fderiv ℝ (fderiv ℝ (model j)) (x j)))
    match rule with
    | .rejectOutside =>
      HasSufficientModelDecrease (model j) (x j) (s j) g β (Δ j) κ ∧
      HasNegativeCurvatureDecrease (model j) (x j) (s j) τ (Δ j) κ
    | .constrainTrial =>
      BarrierAdmissibleTrial (logBarrierEuclideanDomain ι) σ (x j) (x j + s j) ∧
      HasConstrainedBarrierDecrease (model j) (x j) (s j) g β (Δ j) σ
        (infDist (x j) (frontier (logBarrierEuclideanDomain ι))) τ κ

variable [DecidableEq ι]

/-- Algorithm 13.4.1 starts each finite inner minimization at the current
outer iterate, stops at the first qualifying point, and drives the
positive barrier parameter to zero. The terminal index may be zero. -/
structure PrimalLogBarrierOuterRun (P : BTRParams) (f : (ι → ℝ) → ℝ) where
  x : ℕ → EuclideanSpace ℝ ι
  μ : ℕ → ℝ
  σ : ℕ → ℝ
  εD : ℝ → ℝ
  εE : ℝ → ℝ
  inner : ℕ → ℕ → EuclideanSpace ℝ ι
  stopIndex : ℕ → ℕ
  initial_positive : ∀ i, 0 < (x 0).ofLp i
  parameter_pos : ∀ k, 0 < μ k
  parameter_limit : Tendsto μ atTop (𝓝 0)
  forcing_pos : ∀ μ > 0, 0 < εD μ ∧ 0 < εE μ
  forcing_limit : Tendsto εD (𝓝[>] 0) (𝓝 0) ∧ Tendsto εE (𝓝[>] 0) (𝓝 0)
  inner_trace : ∀ k, PrimalLogBarrierInnerPrefix P f (σ k) (μ k) (inner k) (stopIndex k)
  start_inner : ∀ k, inner k 0 = x k
  finish_inner : ∀ k, x (k + 1) = inner k (stopIndex k)
  stopping_test : ∀ k, BarrierSecondOrderStop f (x (k + 1)).ofLp (μ k) (εD (μ k)) (εE (μ k))
  first_stop : ∀ k j, j < stopIndex k →
    ¬ BarrierSecondOrderStop f (inner k j).ofLp (μ k) (εD (μ k)) (εE (μ k))

/-- The primal algorithm instantiates the generic barrier outer iteration
with one of its finite trust-region solvers at each stage. -/
def PrimalLogBarrierOuterRun.toBarrierOuterRun {P : BTRParams} {f : (ι → ℝ) → ℝ}
    (r : PrimalLogBarrierOuterRun P f) :
    BarrierOuterRun (logBarrierEuclideanDomain ι)
      (fun v μ ↦ logBarrierObjective f v.ofLp μ)
      (fun μ φ x J ↦ φ = (fun v ↦ logBarrierObjective f v.ofLp μ) ∧
        ∃ σ, Nonempty (PrimalLogBarrierInnerPrefix P f σ μ x J)) where
  x := r.x
  μ := r.μ
  inner := r.inner
  stopIndex := r.stopIndex
  initial_interior := interior_subset_intrinsicInterior (𝕜 := ℝ)
    ((mem_interior_logBarrierEuclideanDomain _).mpr r.initial_positive)
  parameter_pos := r.parameter_pos
  parameter_limit := r.parameter_limit
  inner_start_interior := fun k ↦ interior_subset_intrinsicInterior (𝕜 := ℝ)
    (r.inner_trace k).initial_interior
  inner_solved := fun k ↦ ⟨rfl, r.σ k, ⟨r.inner_trace k⟩⟩
  inner_finish_interior := fun k ↦ interior_subset_intrinsicInterior (𝕜 := ℝ)
    ((r.inner_trace k).toPrimalBarrierInnerPrefix.interior_iterate le_rfl)
  outer_update := r.finish_inner

private theorem PrimalLogBarrierOuterRun.forcing_tendsto {P : BTRParams}
    {f : (ι → ℝ) → ℝ} (r : PrimalLogBarrierOuterRun P f) :
    Tendsto (fun k ↦ r.εD (r.μ k)) atTop (𝓝 0) ∧
      Tendsto (fun k ↦ r.εE (r.μ k)) atTop (𝓝 0) := by
  have hμ : Tendsto r.μ atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨r.parameter_limit, Eventually.of_forall r.parameter_pos⟩
  exact ⟨r.forcing_limit.1.comp hμ, r.forcing_limit.2.comp hμ⟩

/-- Theorem 13.4.3 applied to the completed iterations of Algorithm 13.4.1.
The shifted sequence uses the barrier parameter that generated each
completed iterate. -/
theorem PrimalLogBarrierOuterRun.convergence {P : BTRParams} {f : (ι → ℝ) → ℝ}
    (r : PrimalLogBarrierOuterRun P f) :
    (∀ i η, 0 < η → ∀ᶠ k in atTop, -η ≤ barrierCoordinateGradient f (r.x (k + 1)).ofLp i) ∧
    (∀ i, (∃ δ > 0, ∀ᶠ k in atTop, δ ≤ (r.x (k + 1)).ofLp i) →
      Tendsto (fun k ↦ barrierCoordinateGradient f (r.x (k + 1)).ofLp i) atTop (𝓝 0)) ∧
    ∀ d : ι → ℝ, (∀ i, d i ≠ 0 → ∃ δ > 0, ∀ᶠ k in atTop, δ ≤ (r.x (k + 1)).ofLp i) →
      ∀ η, 0 < η → ∀ᶠ k in atTop, -η ≤ fderiv ℝ (fderiv ℝ f) (r.x (k + 1)).ofLp d d := by
  exact theorem_13_4_3 r.parameter_limit (fun k ↦ (r.parameter_pos k).le)
    r.forcing_tendsto.1 (fun k ↦ (r.forcing_pos _ (r.parameter_pos k)).1.le)
    r.forcing_tendsto.2 r.stopping_test

/-- Corollary 13.4.4 for a limit of completed primal barrier iterations.
The Hessian inequality is on the nullspace of all active bounds. -/
theorem PrimalLogBarrierOuterRun.weakSecondOrder_limit {P : BTRParams}
    {f : (ι → ℝ) → ℝ} (r : PrimalLogBarrierOuterRun P f) (hf : ContDiff ℝ 2 f)
    {j : ℕ → ℕ} (hj : Tendsto j atTop atTop) {xstar : ι → ℝ}
    (hx : Tendsto (fun k ↦ (r.x (j k + 1)).ofLp) atTop (𝓝 xstar)) :
    (∀ i, 0 ≤ xstar i) ∧
    (∀ i, 0 ≤ barrierCoordinateGradient f xstar i ∧
      (0 < xstar i → barrierCoordinateGradient f xstar i = 0)) ∧
    ∀ d : ι → ℝ, (∀ i, xstar i = 0 → d i = 0) → 0 ≤ fderiv ℝ (fderiv ℝ f) xstar d d := by
  exact corollary_13_4_4 hf hx (r.parameter_limit.comp hj) (fun k ↦ (r.parameter_pos (j k)).le)
    (r.forcing_tendsto.1.comp hj) (fun k ↦ (r.forcing_pos _ (r.parameter_pos (j k))).1.le)
    (r.forcing_tendsto.2.comp hj) (fun k ↦ r.stopping_test (j k))

end PrimalOuterRun

section StrongCounterexample

private noncomputable def logBarrierCounterVector : Fin 4 → ℝ :=
  fun i ↦ if i = 0 then -3 else 1

private noncomputable def logBarrierCounterLinear : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  ∑ i, logBarrierCounterVector i • ContinuousLinearMap.proj i

/-- The bilinear Hessian of (13.4.14) in dimension four. -/
noncomputable def logBarrierCounterHessian :
    (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) →L[ℝ] ℝ :=
  (∑ i, (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj i)) -
    (1 / 8 : ℝ) • logBarrierCounterLinear.smulRight logBarrierCounterLinear

private theorem logBarrierCounterHessian_apply (x d : Fin 4 → ℝ) :
    logBarrierCounterHessian x d =
      (∑ i, x i * d i) - (1 / 8 : ℝ) *
        (∑ i, logBarrierCounterVector i * x i) * (∑ i, logBarrierCounterVector i * d i) := by
  simp only [logBarrierCounterHessian, logBarrierCounterLinear, sub_apply, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

private theorem logBarrierCounterHessian_symm (x d : Fin 4 → ℝ) :
    logBarrierCounterHessian x d = logBarrierCounterHessian d x := by
  rw [logBarrierCounterHessian_apply, logBarrierCounterHessian_apply]
  simp only [mul_comm (x _) (d _)]
  ring

/-- The unregularized quadratic example (13.4.13). -/
noncomputable def logBarrierCounterObjective (x : Fin 4 → ℝ) : ℝ :=
  (1 / 2 : ℝ) * logBarrierCounterHessian x x

private theorem logBarrierCounterObjective_fderiv (x : Fin 4 → ℝ) :
    fderiv ℝ logBarrierCounterObjective x = logBarrierCounterHessian x := by
  have h := barrierQuadratic_hasFDerivAt (a := 0) (g := 0) logBarrierCounterHessian_symm x
  change fderiv ℝ (fun d ↦ (1 / 2 : ℝ) * logBarrierCounterHessian d d) x = _
  simpa only [zero_apply, zero_add] using h.fderiv

private theorem logBarrierCounterObjective_hessian (x : Fin 4 → ℝ) :
    fderiv ℝ (fderiv ℝ logBarrierCounterObjective) x = logBarrierCounterHessian := by
  rw [funext logBarrierCounterObjective_fderiv]
  exact logBarrierCounterHessian.hasFDerivAt.fderiv

/-- Exact stationary log-barrier points (13.4.19) satisfy the second-order
stopping tests with zero tolerances. Nevertheless, the Hessian of the
unregularized quadratic at their limit is negative on a feasible direction.
The example concerns the stopping tests themselves. Its quadratic objective
is unbounded below on the orthant. -/
theorem logBarrierCounterObjective_stops_and_negative_direction :
    (∀ r > 0, BarrierSecondOrderStop logBarrierCounterObjective (fun _ ↦ r) (r ^ 2) 0 0) ∧
    fderiv ℝ (fderiv ℝ logBarrierCounterObjective) 0 (Pi.single 0 1) (Pi.single 0 1) < 0 := by
  have hz : ∑ i, logBarrierCounterVector i = 0 := by
    norm_num [Fin.sum_univ_four, logBarrierCounterVector, Pi.single_apply]
  have hz2 : ∑ i, (logBarrierCounterVector i) ^ 2 = 12 := by
    norm_num [Fin.sum_univ_four, logBarrierCounterVector, Pi.single_apply]
  constructor
  · intro r hr
    refine ⟨fun _ ↦ hr, ?_, ?_⟩
    · have hg (i : Fin 4) :
          barrierCoordinateGradient logBarrierCounterObjective (fun _ ↦ r) i = r := by
        rw [barrierCoordinateGradient, logBarrierCounterObjective_fderiv,
          logBarrierCounterHessian_apply, ← Finset.sum_mul]
        simp only [hz, zero_mul, mul_zero, sub_zero]
        simp [Pi.single_apply]
      simp [hg, pow_two, mul_div_cancel_right₀ r hr.ne']
    · intro d
      rw [logBarrierCounterObjective_hessian, logBarrierCounterHessian_apply]
      have hsum : r ^ 2 * (∑ i, (r ^ 2)⁻¹ * d i * d i) = ∑ i, d i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [show r ^ 2 * ((r ^ 2)⁻¹ * d i * d i) =
          (r ^ 2 * (r ^ 2)⁻¹) * d i * d i by ring, mul_inv_cancel₀ (pow_ne_zero _ hr.ne')]
        ring
      change -(0 : ℝ) * (∑ i, d i ^ 2) ≤ _
      rw [hsum]
      have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ logBarrierCounterVector d
      rw [hz2] at hc
      have hd : 0 ≤ ∑ i, (d i) ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg (d i)
      simp_rw [← pow_two] at *
      nlinarith
  · rw [logBarrierCounterObjective_hessian, logBarrierCounterHessian_apply]
    norm_num [Fin.sum_univ_four, logBarrierCounterVector, Pi.single_apply]

private def logBarrierCounterBump : ContDiffBump (0 : Fin 4 → ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

private noncomputable def logBarrierCounterOuter (x : Fin 4 → ℝ) : ℝ := ∑ i, (x i) ^ 2

/-- A smooth bounded-below version of the counterexample. It agrees with
(13.4.13) near the origin and with a positive quadratic outside a ball. -/
noncomputable def logBarrierCounterRegularized (x : Fin 4 → ℝ) : ℝ :=
  logBarrierCounterBump x * logBarrierCounterObjective x +
    (1 - logBarrierCounterBump x) * logBarrierCounterOuter x

private theorem logBarrierCounterRegularized_inner {x : Fin 4 → ℝ}
    (hx : x ∈ ball (0 : Fin 4 → ℝ) 1) :
    logBarrierCounterRegularized =ᶠ[𝓝 x] logBarrierCounterObjective := by
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  have hb : logBarrierCounterBump y = 1 :=
    logBarrierCounterBump.one_of_mem_closedBall (ball_subset_closedBall hy)
  simp [logBarrierCounterRegularized, hb]

private theorem logBarrierCounterRegularized_outer {x : Fin 4 → ℝ}
    (hx : x ∉ closedBall (0 : Fin 4 → ℝ) 2) :
    logBarrierCounterRegularized =ᶠ[𝓝 x] logBarrierCounterOuter := by
  filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hx] with y hy
  have hb : logBarrierCounterBump y = 0 :=
    logBarrierCounterBump.zero_of_le_dist (le_of_not_ge hy)
  simp [logBarrierCounterRegularized, hb]

private noncomputable def logBarrierCounterOuterHessian :
    (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) →L[ℝ] ℝ :=
  (2 : ℝ) • ∑ i, (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj i)

private theorem logBarrierCounterOuterHessian_apply (x d : Fin 4 → ℝ) :
    logBarrierCounterOuterHessian x d = 2 * ∑ i, x i * d i := by
  simp only [logBarrierCounterOuterHessian, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

private theorem logBarrierCounterOuter_hessian (x : Fin 4 → ℝ) :
    fderiv ℝ (fderiv ℝ logBarrierCounterOuter) x = logBarrierCounterOuterHessian := by
  have hs (v w : Fin 4 → ℝ) :
      logBarrierCounterOuterHessian v w = logBarrierCounterOuterHessian w v := by
    simp only [logBarrierCounterOuterHessian_apply, mul_comm (v _) (w _)]
  have he : logBarrierCounterOuter = fun v ↦
      (0 : ℝ) + (0 : (Fin 4 → ℝ) →L[ℝ] ℝ) v + (1 / 2 : ℝ) * logBarrierCounterOuterHessian v v := by
    funext v
    rw [logBarrierCounterOuterHessian_apply]
    simp only [zero_apply, zero_add, logBarrierCounterOuter, pow_two]
    ring
  have hd (v : Fin 4 → ℝ) :
      fderiv ℝ logBarrierCounterOuter v = logBarrierCounterOuterHessian v := by
    rw [he]
    simpa only [zero_add] using (barrierQuadratic_hasFDerivAt (a := 0) (g := 0) hs v).fderiv
  rw [funext hd]
  exact logBarrierCounterOuterHessian.hasFDerivAt.fderiv

/-- The regularized example has a bounded objective Hessian and bounded-below
barrier objectives for every positive parameter. Its exact inner stopping
points converge to a point that fails strong second-order criticality. -/
theorem logBarrierCounterRegularized_example :
    ContDiff ℝ 2 logBarrierCounterRegularized ∧
    (∃ M : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ logBarrierCounterRegularized) x‖ ≤ M) ∧
    (∃ m : ℝ, ∀ x, m ≤ logBarrierCounterRegularized x) ∧
    (∀ μ > 0, ∃ m : ℝ, ∀ x : Fin 4 → ℝ, (∀ i, 0 < x i) →
      m ≤ logBarrierObjective logBarrierCounterRegularized x μ) ∧
    (∀ r ∈ Set.Ioo (0 : ℝ) 1,
      BarrierSecondOrderStop logBarrierCounterRegularized (fun _ ↦ r) (r ^ 2) 0 0) ∧
    barrierCoordinateGradient logBarrierCounterRegularized 0 = 0 ∧
    fderiv ℝ (fderiv ℝ logBarrierCounterRegularized) 0 (Pi.single 0 1) (Pi.single 0 1) < 0 := by
  have hχ : ContDiff ℝ 2 logBarrierCounterBump := logBarrierCounterBump.contDiff
  have hf : ContDiff ℝ 2 logBarrierCounterObjective := by
    unfold logBarrierCounterObjective
    fun_prop
  have hout : ContDiff ℝ 2 logBarrierCounterOuter := by
    unfold logBarrierCounterOuter
    fun_prop
  have hF : ContDiff ℝ 2 logBarrierCounterRegularized :=
    (hχ.mul hf).add ((contDiff_const.sub hχ).mul hout)
  have hH := (hF.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  let K := closedBall (0 : Fin 4 → ℝ) 2
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨M, hM⟩ := (hK.image hH.norm).bddAbove
  obtain ⟨m, hm⟩ := (hK.image hF.continuous).bddBelow
  refine ⟨hF, ⟨max M ‖logBarrierCounterOuterHessian‖, ?_⟩, ⟨min m 0, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ K
    · exact (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    · rw [(logBarrierCounterRegularized_outer hx).fderiv.fderiv_eq,
        logBarrierCounterOuter_hessian]
      exact le_max_right _ _
  · intro x
    by_cases hx : x ∈ K
    · exact (min_le_left _ _).trans (hm ⟨x, hx, rfl⟩)
    · rw [(logBarrierCounterRegularized_outer hx).eq_of_nhds]
      exact (min_le_right _ _).trans (Finset.sum_nonneg fun i _ ↦ sq_nonneg (x i))
  · intro μ hμ
    refine ⟨min (m - 8 * μ) (-(μ ^ 2)), fun x hx ↦ ?_⟩
    by_cases hxK : x ∈ K
    · apply (min_le_left _ _).trans
      have hcoord (i : Fin 4) : x i ≤ 2 := by
        have hdist := (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 2)).mp hxK i
        simpa [Real.dist_eq, abs_of_pos (hx i)] using hdist
      have hsum : (∑ i, Real.log (x i)) ≤ 8 := by
        calc
          _ ≤ ∑ _i : Fin 4, (2 : ℝ) := Finset.sum_le_sum fun i _ ↦
            (Real.log_le_self (hx i).le).trans (hcoord i)
          _ = 8 := by norm_num
      have hlow := hm ⟨x, hxK, rfl⟩
      change m - 8 * μ ≤ logBarrierCounterRegularized x + (-μ) * ∑ i, Real.log (x i)
      rw [neg_mul]
      linarith [mul_le_mul_of_nonneg_left hsum hμ.le]
    · apply (min_le_right _ _).trans
      change -(μ ^ 2) ≤ logBarrierCounterRegularized x + (-μ) * ∑ i, Real.log (x i)
      rw [neg_mul]
      rw [(logBarrierCounterRegularized_outer hxK).eq_of_nhds]
      simp only [logBarrierCounterOuter, Finset.mul_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
      calc
        _ = ∑ _i : Fin 4, -(μ ^ 2 / 4) := by norm_num; ring
        _ ≤ _ := Finset.sum_le_sum fun i _ ↦ by
          have hlog := mul_le_mul_of_nonneg_left (Real.log_le_self (hx i).le) hμ.le
          nlinarith [sq_nonneg (x i - μ / 2)]
  · intro r hr
    have hx : (fun _ : Fin 4 ↦ r) ∈ ball (0 : Fin 4 → ℝ) 1 := by
      apply (dist_pi_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
      intro i
      simpa [Real.dist_eq, abs_of_pos hr.1] using hr.2
    have he := logBarrierCounterRegularized_inner hx
    obtain ⟨hs, _⟩ := logBarrierCounterObjective_stops_and_negative_direction
    simpa only [BarrierSecondOrderStop, barrierCoordinateGradient, he.fderiv_eq,
      he.fderiv.fderiv_eq] using hs r hr.1
  · funext i
    have he := logBarrierCounterRegularized_inner (mem_ball_self (by norm_num : (0 : ℝ) < 1))
    simp [barrierCoordinateGradient, he.fderiv_eq, logBarrierCounterObjective_fderiv]
  · have he := logBarrierCounterRegularized_inner (mem_ball_self (by norm_num : (0 : ℝ) < 1))
    rw [he.fderiv.fderiv_eq]
    exact logBarrierCounterObjective_stops_and_negative_direction.2

/-- A vanishing barrier sequence can converge to a limit with negative
curvature in a feasible direction, even for the bounded-below repair. -/
theorem logBarrierCounterRegularized_convergent_stops :
    ∃ (x : ℕ → Fin 4 → ℝ) (μ : ℕ → ℝ),
      (∀ k, 0 < μ k) ∧ Tendsto μ atTop (𝓝 0) ∧ Tendsto x atTop (𝓝 0) ∧
      (∀ k, BarrierSecondOrderStop logBarrierCounterRegularized (x k) (μ k) 0 0) ∧
      barrierCoordinateGradient logBarrierCounterRegularized 0 = 0 ∧
      ∃ d : Fin 4 → ℝ, (∀ i, 0 ≤ d i) ∧
        fderiv ℝ (fderiv ℝ logBarrierCounterRegularized) 0 d d < 0 := by
  let r (k : ℕ) : ℝ := 1 / ((k : ℝ) + 2)
  have hr (k : ℕ) : r k ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨by dsimp [r]; positivity, ?_⟩
    dsimp [r]
    exact (div_lt_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have hlim : Tendsto r atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    simpa [r, Function.comp_def, Nat.cast_add, add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using h
  obtain ⟨_, _, _, _, hstop, hgrad, hneg⟩ := logBarrierCounterRegularized_example
  refine ⟨fun k _ ↦ r k, fun k ↦ r k ^ 2, fun k ↦ sq_pos_of_pos (hr k).1,
    by simpa using hlim.pow 2, tendsto_pi_nhds.mpr fun _ ↦ hlim,
    fun k ↦ hstop _ (hr k), hgrad, Pi.single 0 1, ?_, hneg⟩
  intro i
  by_cases hi : i = 0 <;> simp [hi]

end StrongCounterexample

section PrimalEscape

open Set

private noncomputable def escapeGap (p : ℝ) : ℝ := p - Real.log p

private theorem escapeGap_drop {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    u ^ 2 / 8 ≤ escapeGap (1 + u) - escapeGap (1 + u / 2) := by
  let f (p : ℝ) := escapeGap p - (u / 4) * p
  have ha : 1 + u / 2 ≤ 1 + u := by linarith
  have hD (p : ℝ) (hp : 0 < p) :
      HasDerivAt f (1 - p⁻¹ - u / 4) p := by
    have hd := ((hasDerivAt_id p).sub (Real.hasDerivAt_log hp.ne')).sub
      ((hasDerivAt_id p).const_mul (u / 4))
    change HasDerivAt f (1 - p⁻¹ - u / 4 * 1) p at hd
    simpa only [mul_one] using hd
  have hm : MonotoneOn f (Icc (1 + u / 2) (1 + u)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun p hp ↦ (hD p (by linarith [hp.1])).continuousAt.continuousWithinAt
    · intro p hp
      have hp' := interior_subset hp
      exact (hD p (by linarith [hp'.1])).differentiableAt.differentiableWithinAt
    · intro p hp
      have hp' := interior_subset hp
      have hpos : 0 < p := by linarith [hp'.1]
      rw [(hD p hpos).deriv]
      have hinv : p⁻¹ ≤ 1 - u / 4 := by
        rw [← one_div]
        apply (div_le_iff₀ hpos).mpr
        have hmul := mul_le_mul_of_nonneg_right hp'.2 hu.le
        nlinarith [hp'.1, hmul, mul_nonneg hu.le (sub_nonneg.mpr hu1)]
      linarith
  have hh := hm ⟨le_rfl, ha⟩ ⟨ha, le_rfl⟩ ha
  unfold f at hh
  nlinarith

private noncomputable def escapeY (u : ℝ) : ℝ := u + u ^ 2

private noncomputable def escapeQ (u : ℝ) : ℝ := -(2 + 3 * u) / (4 * (1 + u))

private noncomputable def escapeA (u : ℝ) : ℝ :=
  -2 * (u * (1 + escapeQ u) + (1 + u) * escapeQ u + (escapeQ u) ^ 2 / 2 + u ^ 2 / 16)

/-- The coordinate data of an accepted two-dimensional trial of the first
primal inner algorithm at parameter one. The true objective is `x*y`,
the barrier model is the exact logarithmic Taylor quadratic, and the
objective model adds a centered quadratic to the bilinear objective.
The decrease tests use a curvature bound and the least quadratic curvature. -/
structure PrimalBarrierEscapeTrial (u : ℝ) : Prop where
  parameter_pos : 0 < u
  parameter_le_half : u ≤ 1 / 2
  trial_inside :
    let x := 1 / u
    let y := escapeY u
    let x' := 2 * x
    let y' := escapeY (u / 2)
    0 < x' ∧ 0 < y' ∧ (1 / 4 : ℝ) * min x y ≤ min x' y' ∧
      (x' - x) ^ 2 + (y' - y) ^ 2 ≤ (2 * x) ^ 2
  model_matches :
    let x := 1 / u
    let y := escapeY u
    let a := (escapeA u - 1) * u ^ 2
    let g₁ := u ^ 2
    let g₂ := 1 / (1 + u)
    ∀ s t : ℝ,
      ((x + s) * (y + t) + a * s ^ 2 / 2 +
        (-Real.log x - Real.log y - s / x - t / y +
          (s ^ 2 / x ^ 2 + t ^ 2 / y ^ 2) / 2)) =
      escapeGap (1 + u) + g₁ * s + g₂ * t +
        ((escapeA u * u ^ 2) * s ^ 2 + 2 * s * t + t ^ 2 / y ^ 2) / 2
  objective_model_bound : |(escapeA u - 1) * u ^ 2| ≤ 9
  predicted_decrease :
    let x := 1 / u
    let y := escapeY u
    let s := x
    let t := escapeY (u / 2) - y
    show Prop from -(u ^ 2 * s + (1 / (1 + u)) * t +
      ((escapeA u * u ^ 2) * s ^ 2 + 2 * s * t + t ^ 2 / y ^ 2) / 2) = u ^ 2 / 16
  sufficient_decrease :
    let g := Real.sqrt ((u ^ 2) ^ 2 + (1 / (1 + u)) ^ 2)
    let y := escapeY u
    ∀ β τ : ℝ, 1 / y ^ 2 ≤ β → -(12 * u ^ 2) ≤ τ →
      (1 / 32768 : ℝ) * max (g * min (g / β) (2 / u))
        (-τ * min (τ ^ 2) ((2 / u) ^ 2)) ≤ u ^ 2 / 16
  curvature_lower :
    let y := escapeY u
    ∀ s t : ℝ, -(12 * u ^ 2) * (s ^ 2 + t ^ 2) ≤
      (escapeA u * u ^ 2) * s ^ 2 + 2 * s * t + t ^ 2 / y ^ 2
  actual_decrease : u ^ 2 / 8 ≤ escapeGap (1 + u) - escapeGap (1 + u / 2)
  fails_gradient_stop : 1 / 4 < 1 / (1 + u)

private theorem escapeQ_bounds {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1 / 2) :
    -1 ≤ escapeQ u ∧ escapeQ u ≤ 0 := by
  have hpos : 0 < 4 * (1 + u) := by positivity
  unfold escapeQ
  exact ⟨(le_div_iff₀ hpos).mpr (by linarith), div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le⟩

private theorem escapeA_bound {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1 / 2) :
    |escapeA u| ≤ 8 := by
  obtain ⟨hq₁, hq₂⟩ := escapeQ_bounds hu hu1
  have hq3 : (escapeQ u) ^ 2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hq₂) (show 0 ≤ 1 + escapeQ u by linarith)]
  unfold escapeA
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg hu.le (show 0 ≤ 1 + escapeQ u by linarith),
    mul_nonneg hu.le (neg_nonneg.mpr hq₂), mul_nonneg hu.le (sub_nonneg.mpr hu1),
    sq_nonneg (escapeQ u), sq_nonneg u]

private theorem escape_trial {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1 / 2) :
    PrimalBarrierEscapeTrial u := by
  have hu0 := hu.ne'
  have hp : 0 < 1 + u := by positivity
  have hy : 0 < escapeY u := by unfold escapeY; positivity
  have hy' : 0 < escapeY (u / 2) := by unfold escapeY; positivity
  have hY : escapeY u = u * (1 + u) := by unfold escapeY; ring
  have hQ : escapeY (u / 2) - escapeY u = escapeY u * escapeQ u := by
    rw [hY, escapeQ]
    unfold escapeY
    field_simp [hp.ne']
    ring
  have hA := abs_le.mp (escapeA_bound hu hu1)
  refine ⟨hu, hu1, ?_, ?_, ?_, ?_, ?_, ?_, escapeGap_drop hu (by linarith), ?_⟩
  · dsimp only
    refine ⟨by positivity, hy', ?_, ?_⟩
    · apply le_min
      · exact ((mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)).trans
          (by nlinarith [div_pos zero_lt_one hu]))
      · exact ((mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)).trans
          (by unfold escapeY; nlinarith))
    · have hyub : escapeY u ≤ 1 := by unfold escapeY; nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu1)]
      have hyt : escapeY (u / 2) ≤ escapeY u := by
        unfold escapeY
        nlinarith
      have hxs : (1 : ℝ) ≤ 1 / u := (le_div_iff₀ hu).mpr (by linarith)
      have ht1 : |escapeY (u / 2) - escapeY u| ≤ 1 := by
        rw [abs_of_nonpos (sub_nonpos.mpr hyt)]
        linarith
      have ht2 := (sq_le_sq₀ (abs_nonneg _) (zero_le_one : (0 : ℝ) ≤ 1)).mpr ht1
      rw [sq_abs] at ht2
      have hx2 := (sq_le_sq₀ zero_le_one (zero_le_one.trans hxs)).mpr hxs
      nlinarith
  · dsimp only
    intro s t
    have hxy : (1 / u) * escapeY u = 1 + u := by rw [hY]; field_simp [hu0]
    have hlog := Real.log_mul (show (1 / u : ℝ) ≠ 0 by positivity) hy.ne'
    rw [hxy] at hlog
    unfold escapeGap
    rw [hlog]
    rw [hY]
    field_simp [hu0, hp.ne']
    ring
  · have hh : |escapeA u - 1| ≤ 9 := by
      apply abs_le.mpr
      constructor <;> linarith [hA.1, hA.2]
    rw [abs_mul, abs_of_nonneg (sq_nonneg u)]
    exact (mul_le_mul_of_nonneg_right hh (sq_nonneg u)).trans
      (by nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu1)])
  · dsimp only
    rw [hQ, hY, escapeA]
    field_simp [hu0, hp.ne']
    ring
  · dsimp only
    intro β τ hβ hτ
    have hβp := (show 0 < 1 / escapeY u ^ 2 by positivity).trans_le hβ
    have hYb : escapeY u ≤ 2 * u := by
      unfold escapeY
      nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu1)]
    have hβinv : β⁻¹ ≤ 4 * u ^ 2 := calc
      _ ≤ (1 / escapeY u ^ 2)⁻¹ := inv_anti₀ (by positivity) hβ
      _ = escapeY u ^ 2 := by simp
      _ ≤ _ := by
        have h := (sq_le_sq₀ hy.le (by positivity : 0 ≤ 2 * u)).mpr hYb
        nlinarith
    let g := Real.sqrt ((u ^ 2) ^ 2 + (1 / (1 + u)) ^ 2)
    have hg : 0 ≤ g := Real.sqrt_nonneg _
    have hg2 : g ^ 2 ≤ 2 := by
      dsimp only [g]
      rw [Real.sq_sqrt (by positivity)]
      have hu2 : u ^ 2 ≤ 1 := by nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu1)]
      have hi : 1 / (1 + u) ≤ 1 := (div_le_one hp).mpr (by linarith)
      have h₁ := (sq_le_sq₀ (sq_nonneg u) zero_le_one).mpr hu2
      have h₂ := (sq_le_sq₀ (by positivity : 0 ≤ 1 / (1 + u)) zero_le_one).mpr hi
      linarith
    have hfirst : g * min (g / β) (2 / u) ≤ 8 * u ^ 2 := calc
      _ ≤ g * (g / β) := mul_le_mul_of_nonneg_left (min_le_left _ _) hg
      _ = g ^ 2 * β⁻¹ := by rw [div_eq_mul_inv]; ring
      _ ≤ _ := by
        have h := mul_le_mul hg2 hβinv (inv_nonneg.mpr hβp.le) (by norm_num : (0 : ℝ) ≤ 2)
        nlinarith
    have hsecond : -τ * min (τ ^ 2) ((2 / u) ^ 2) ≤ 1728 * u ^ 2 := by
      by_cases ht : 0 ≤ τ
      · exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht)
          (le_min (sq_nonneg _) (sq_nonneg _))).trans (by positivity)
      · have hneg : 0 ≤ -τ := by linarith
        have ha : -τ ≤ 12 * u ^ 2 := by linarith
        have h₁ := mul_le_mul_of_nonneg_left (min_le_left (τ ^ 2) ((2 / u) ^ 2)) hneg
        have h₂ : (-τ) ^ 3 ≤ (12 * u ^ 2) ^ 3 := pow_le_pow_left₀ hneg ha 3
        have hu2 : u ^ 2 ≤ 1 := by nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu1)]
        have hu4 : (u ^ 2) ^ 2 ≤ 1 := by
          simpa using (sq_le_sq₀ (sq_nonneg u) zero_le_one).mpr hu2
        have h₃ := mul_le_mul_of_nonneg_right hu4 (sq_nonneg u)
        exact h₁.trans (by nlinarith [h₂, h₃])
    change (1 / 32768 : ℝ) * max (g * min (g / β) (2 / u)) _ ≤ _
    have hmax : max (g * min (g / β) (2 / u)) (-τ * min (τ ^ 2) ((2 / u) ^ 2)) ≤ 1728 * u ^ 2 :=
      max_le (hfirst.trans (by nlinarith [sq_nonneg u])) hsecond
    nlinarith [hmax, sq_nonneg u]
  · dsimp only
    intro s t
    have h₁ : -8 * u ^ 2 ≤ escapeA u * u ^ 2 :=
      mul_le_mul_of_nonneg_right hA.1 (sq_nonneg u)
    have hYb : escapeY u ≤ 2 * u := by
      unfold escapeY
      nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu1)]
    have h₂ : escapeY u ^ 2 ≤ 4 * u ^ 2 := by
      have h := (sq_le_sq₀ hy.le (by positivity : 0 ≤ 2 * u)).mpr hYb
      nlinarith
    have hsq : 0 ≤ (escapeY u * s + t / escapeY u) ^ 2 := sq_nonneg _
    have hcross : -(escapeY u ^ 2) * s ^ 2 ≤ 2 * s * t + t ^ 2 / escapeY u ^ 2 := by
      have he : (escapeY u * s + t / escapeY u) ^ 2 =
          escapeY u ^ 2 * s ^ 2 + 2 * s * t + t ^ 2 / escapeY u ^ 2 := by
        field_simp [hy.ne']
        ring
      rw [he] at hsq
      linarith
    have h₃ := mul_le_mul_of_nonneg_right h₁ (sq_nonneg s)
    have h₄ := mul_le_mul_of_nonneg_right h₂ (sq_nonneg s)
    nlinarith [mul_nonneg (sq_nonneg u) (sq_nonneg t)]
  · apply (lt_div_iff₀ hp).mpr
    linarith

/-- The printed hypotheses of Theorem 13.4.2 permit a scalar-parameter
sequence of accepted two-coordinate trials with no first-order stop.
The coordinates are `(1/u, u+u²)` with `u=2⁻(j+1)`. The radius doubles,
the actual-to-predicted reduction ratio is at least two, the objective
models have a uniform Hessian bound, and the second component of the
barrier gradient stays above the stopping tolerance. -/
theorem theorem_13_4_2_unbounded_run_counterexample :
    ∃ u : ℕ → ℝ,
      Tendsto u atTop (𝓝 0) ∧
      (∀ j, u (j + 1) = u j / 2) ∧
      (∀ j, PrimalBarrierEscapeTrial (u j)) ∧
      (∀ j, 2 ≤ (escapeGap (1 + u j) - escapeGap (1 + u (j + 1))) / (u j ^ 2 / 16)) ∧
      (∀ μ > 0, ∃ A : ℝ, ∀ x y : ℝ, 0 < x → 0 < y →
        A ≤ x * y - μ * (Real.log x + Real.log y)) := by
  let u (j : ℕ) := (1 / 2 : ℝ) ^ (j + 1)
  have hu (j : ℕ) : 0 < u j := by dsimp [u]; positivity
  have hu1 (j : ℕ) : u j ≤ 1 / 2 := by
    simp only [u, pow_succ]
    exact mul_le_of_le_one_left (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))
  have hup (j : ℕ) : u (j + 1) = u j / 2 := by
    simp only [u, pow_succ]
    ring
  refine ⟨u, ?_, hup, fun j ↦ escape_trial (hu j) (hu1 j), ?_, ?_⟩
  · simpa only [u, pow_succ, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2 : ℝ)
  · intro j
    rw [hup]
    exact (le_div_iff₀ (by positivity)).mpr (by
      linarith [escapeGap_drop (hu j) (show u j ≤ 1 by linarith [hu1 j])])
  · intro μ hμ
    refine ⟨μ - μ * Real.log μ, fun x y hx hy ↦ ?_⟩
    rw [← Real.log_mul hx.ne' hy.ne']
    have hp := mul_pos hx hy
    have hl := Real.log_le_sub_one_of_pos (div_pos hp hμ)
    rw [Real.log_div hp.ne' hμ.ne'] at hl
    have hm := mul_le_mul_of_nonneg_left hl hμ.le
    simp only [mul_sub, mul_div_cancel₀ _ hμ.ne', mul_one] at hm
    linarith

private abbrev EscapeSpace := EuclideanSpace ℝ (Fin 2)

private noncomputable def escapePoint (u : ℝ) : EscapeSpace :=
  WithLp.toLp 2 ![1 / u, escapeY u]

private def escapeOrthant : Set EscapeSpace :=
  WithLp.ofLp ⁻¹' Optimization.nonnegativeOrthant (Fin 2)

private noncomputable def escapeObjective (p : EscapeSpace) : ℝ :=
  escapeGap (p.ofLp 0 * p.ofLp 1)

private noncomputable def escapeModel (u : ℝ) (p : EscapeSpace) : ℝ :=
  let s := p.ofLp 0 - 1 / u
  let t := p.ofLp 1 - escapeY u
  escapeGap (1 + u) + u ^ 2 * s + (1 / (1 + u)) * t +
    ((escapeA u * u ^ 2) * s ^ 2 + 2 * s * t + t ^ 2 / (escapeY u) ^ 2) / 2

private theorem escapeOrthant_interior {p : EscapeSpace}
    (hp : ∀ i, 0 < p.ofLp i) : p ∈ interior escapeOrthant := by
  let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).toHomeomorph
  change p ∈ interior (T ⁻¹' Optimization.nonnegativeOrthant (Fin 2))
  rw [← T.preimage_interior]
  change p.ofLp ∈ interior (Set.univ.pi (fun _ : Fin 2 ↦ Ici (0 : ℝ)))
  rw [interior_pi_set Set.finite_univ]
  simpa only [Set.mem_pi, Set.mem_univ, true_implies, interior_Ici, Set.mem_Ioi] using hp

private theorem escape_norm_sq (v : EscapeSpace) :
    ‖v‖ ^ 2 = (v.ofLp 0) ^ 2 + (v.ofLp 1) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
  · simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  · exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

private theorem escape_coord_abs_le_norm (v : EscapeSpace) (i : Fin 2) :
    |v.ofLp i| ≤ ‖v‖ := by
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs, escape_norm_sq]
  fin_cases i
  · change (v.ofLp 0) ^ 2 ≤ (v.ofLp 0) ^ 2 + (v.ofLp 1) ^ 2
    linarith [sq_nonneg (v.ofLp 1)]
  · change (v.ofLp 1) ^ 2 ≤ (v.ofLp 0) ^ 2 + (v.ofLp 1) ^ 2
    linarith [sq_nonneg (v.ofLp 0)]

private theorem escapeOrthant_boundary_dist {p : EscapeSpace} (hp : ∀ i, 0 < p.ofLp i) :
    infDist p (frontier escapeOrthant) = min (p.ofLp 0) (p.ofLp 1) := by
  let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).toHomeomorph
  have hfront : frontier escapeOrthant =
      T ⁻¹' frontier (Optimization.nonnegativeOrthant (Fin 2)) := (T.preimage_frontier _).symm
  have hz : (0 : EscapeSpace) ∈ frontier escapeOrthant := by
    rw [hfront]
    exact Optimization.mem_frontier_nonnegativeOrthant.mpr ⟨fun _ ↦ le_rfl, 0, rfl⟩
  apply le_antisymm
  · by_cases h : p.ofLp 0 ≤ p.ofLp 1
    · let z : EscapeSpace := WithLp.toLp 2 ![0, p.ofLp 1]
      have hz' : z ∈ frontier escapeOrthant := by
        rw [hfront]
        apply Optimization.mem_frontier_nonnegativeOrthant.mpr
        refine ⟨?_, 0, rfl⟩
        intro i
        fin_cases i
        · exact le_rfl
        · exact (hp 1).le
      have hdist : dist p z ≤ p.ofLp 0 := by
        rw [dist_eq_norm]
        apply (sq_le_sq₀ (norm_nonneg _) (hp 0).le).mp
        rw [escape_norm_sq]
        change (p.ofLp 0 - 0) ^ 2 + (p.ofLp 1 - p.ofLp 1) ^ 2 ≤ _
        ring_nf
        exact le_rfl
      exact (infDist_le_dist_of_mem hz').trans (hdist.trans_eq (min_eq_left h).symm)
    · let z : EscapeSpace := WithLp.toLp 2 ![p.ofLp 0, 0]
      have hz' : z ∈ frontier escapeOrthant := by
        rw [hfront]
        apply Optimization.mem_frontier_nonnegativeOrthant.mpr
        refine ⟨?_, 1, rfl⟩
        intro i
        fin_cases i
        · exact (hp 0).le
        · exact le_rfl
      have hdist : dist p z ≤ p.ofLp 1 := by
        rw [dist_eq_norm]
        apply (sq_le_sq₀ (norm_nonneg _) (hp 1).le).mp
        rw [escape_norm_sq]
        change (p.ofLp 0 - p.ofLp 0) ^ 2 + (p.ofLp 1 - 0) ^ 2 ≤ _
        ring_nf
        exact le_rfl
      exact (infDist_le_dist_of_mem hz').trans (hdist.trans_eq (min_eq_right (le_of_not_ge h)).symm)
  · apply (le_infDist ⟨0, hz⟩).mpr
    intro z hz'
    rw [hfront] at hz'
    obtain ⟨_, i, hi⟩ := Optimization.mem_frontier_nonnegativeOrthant.mp hz'
    have hi' : z.ofLp i = 0 := hi
    have hnorm := escape_coord_abs_le_norm (p - z) i
    rw [WithLp.ofLp_sub, Pi.sub_apply, hi', sub_zero, abs_of_pos (hp i)] at hnorm
    rw [dist_eq_norm]
    fin_cases i
    · exact (min_le_left _ _).trans hnorm
    · exact (min_le_right _ _).trans hnorm

private theorem escapePoint_positive {u : ℝ} (hu : 0 < u) :
    ∀ i, 0 < (escapePoint u).ofLp i := by
  intro i
  fin_cases i
  · change 0 < 1 / u
    positivity
  · change 0 < escapeY u
    unfold escapeY
    positivity

private theorem escapeObjective_at_point {u : ℝ} (hu : 0 < u) :
    escapeObjective (escapePoint u) = escapeGap (1 + u) := by
  change escapeGap ((1 / u) * escapeY u) = _
  congr 1
  unfold escapeY
  field_simp [hu.ne']

private theorem escapeModel_predicted {u : ℝ} (h : PrimalBarrierEscapeTrial u) :
    escapeModel u (escapePoint u) - escapeModel u (escapePoint (u / 2)) = u ^ 2 / 16 := by
  have he : 1 / (u / 2) - 1 / u = 1 / u := by
    field_simp [h.parameter_pos.ne']
    ring
  have hcenter : escapeModel u (escapePoint u) = escapeGap (1 + u) := by
    simp [escapeModel, escapePoint]
  rw [hcenter]
  change escapeGap (1 + u) -
    (escapeGap (1 + u) + u ^ 2 * (1 / (u / 2) - 1 / u) +
      1 / (1 + u) * (escapeY (u / 2) - escapeY u) +
      ((escapeA u * u ^ 2) * (1 / (u / 2) - 1 / u) ^ 2 +
        2 * (1 / (u / 2) - 1 / u) * (escapeY (u / 2) - escapeY u) +
        (escapeY (u / 2) - escapeY u) ^ 2 / (escapeY u) ^ 2) / 2) = _
  rw [he]
  have hp := h.predicted_decrease
  dsimp only at hp
  linarith

private def escapeL (i : Fin 2) : EscapeSpace →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).toContinuousLinearMap

private noncomputable def escapeG (u : ℝ) : EscapeSpace →L[ℝ] ℝ :=
  (u ^ 2) • escapeL 0 + (1 / (1 + u)) • escapeL 1

private noncomputable def escapeH (u : ℝ) : EscapeSpace →L[ℝ] EscapeSpace →L[ℝ] ℝ :=
  (escapeA u * u ^ 2) • (escapeL 0).smulRight (escapeL 0) +
    (escapeL 0).smulRight (escapeL 1) + (escapeL 1).smulRight (escapeL 0) +
    (1 / (escapeY u) ^ 2) • (escapeL 1).smulRight (escapeL 1)

private theorem escapeH_apply (u : ℝ) (v w : EscapeSpace) :
    escapeH u v w = (escapeA u * u ^ 2) * v.ofLp 0 * w.ofLp 0 +
      v.ofLp 0 * w.ofLp 1 + v.ofLp 1 * w.ofLp 0 +
      (1 / (escapeY u) ^ 2) * v.ofLp 1 * w.ofLp 1 := by
  simp [escapeH, escapeL, mul_assoc]

private theorem escapeModel_fderiv (u : ℝ) (p : EscapeSpace) :
    fderiv ℝ (escapeModel u) p = escapeG u + escapeH u (p - escapePoint u) := by
  let m (d : EscapeSpace) := escapeGap (1 + u) + escapeG u d + (1 / 2 : ℝ) * escapeH u d d
  have he : escapeModel u = fun p ↦ m (p - escapePoint u) := by
    funext v
    unfold m
    rw [escapeH_apply]
    have hL (i : Fin 2) (p : EscapeSpace) : escapeL i p = p.ofLp i := rfl
    simp only [escapeModel, escapeG, add_apply, smul_apply, smul_eq_mul, hL,
      WithLp.ofLp_sub, Pi.sub_apply]
    have hx0 : (escapePoint u).ofLp 0 = 1 / u := rfl
    have hx1 : (escapePoint u).ofLp 1 = escapeY u := rfl
    simp only [hx0, hx1]
    ring
  have hs (v w : EscapeSpace) : escapeH u v w = escapeH u w v := by
    simp only [escapeH_apply]
    ring
  rw [he]
  have hd := (barrierQuadratic_hasFDerivAt (a := escapeGap (1 + u)) (g := escapeG u) hs
    (p - escapePoint u)).comp p ((hasFDerivAt_id p).sub_const (escapePoint u))
  change HasFDerivAt (fun v ↦ m (v - escapePoint u)) _ p at hd
  rw [hd.fderiv, ContinuousLinearMap.comp_id]

private theorem escapeModel_hessian (u : ℝ) (p : EscapeSpace) :
    fderiv ℝ (fderiv ℝ (escapeModel u)) p = escapeH u := by
  rw [funext (escapeModel_fderiv u)]
  have hd := ((escapeH u).hasFDerivAt (x := p - escapePoint u)).comp p
    ((hasFDerivAt_id p).sub_const (escapePoint u))
  have hd' := (hd.const_add (escapeG u)).fderiv
  change fderiv ℝ (fun v ↦ escapeG u + escapeH u (v - escapePoint u)) p = _ at hd'
  simpa only [ContinuousLinearMap.comp_id] using hd'

private theorem escapeModel_gradient_norm (u : ℝ) :
    ‖gradient (escapeModel u) (escapePoint u)‖ =
      Real.sqrt ((u ^ 2) ^ 2 + (1 / (1 + u)) ^ 2) := by
  let g : EscapeSpace := WithLp.toLp 2 ![u ^ 2, 1 / (1 + u)]
  have hg : gradient (escapeModel u) (escapePoint u) = g := by
    apply (InnerProductSpace.toDual ℝ EscapeSpace).injective
    ext d
    change inner ℝ (gradient (escapeModel u) (escapePoint u)) d = inner ℝ g d
    rw [inner_gradient_left, escapeModel_fderiv, sub_self, map_zero, add_zero,
      EuclideanSpace.inner_eq_star_dotProduct]
    simp [escapeG, escapeL, g, dotProduct, Fin.sum_univ_two]
    ring
  rw [hg, EuclideanSpace.norm_eq]
  simp [g, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- The Euclidean gradient and actual model Hessian satisfy the first-
and second-order decrease conditions on the unbounded accepted path. -/
theorem escapeModel_adequate_decrease {u : ℝ} (h : PrimalBarrierEscapeTrial u) :
    let x := escapePoint u
    let s := escapePoint (u / 2) - x
    let H := fderiv ℝ (fderiv ℝ (escapeModel u)) x
    let β := 1 + ‖H‖
    let τ := min 0 (Chapter06.leastUnitCurvature H)
    Chapter06.HasSufficientModelDecrease (escapeModel u) x s
      (gradient (escapeModel u) x) β (2 / u) (1 / 32768) ∧
    Chapter06.HasNegativeCurvatureDecrease (escapeModel u) x s τ (2 / u) (1 / 32768) := by
  dsimp only
  rw [escapeModel_hessian]
  let e : EscapeSpace := WithLp.toLp 2 ![0, 1]
  have he : ‖e‖ = 1 := by simp [e, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hYe : 1 / (escapeY u) ^ 2 ≤ ‖escapeH u‖ := by
    have h₁ := ((escapeH u) e).le_opNorm e
    have h₂ := (escapeH u).le_opNorm e
    rw [he, mul_one] at h₁ h₂
    have hq : escapeH u e e = 1 / (escapeY u) ^ 2 := by simp [e, escapeH_apply]
    rw [hq, Real.norm_of_nonneg (by positivity)] at h₁
    exact h₁.trans h₂
  have hβ : 1 / (escapeY u) ^ 2 ≤ 1 + ‖escapeH u‖ := hYe.trans (by linarith)
  have ht : -(12 * u ^ 2) ≤ min 0 (Chapter06.leastUnitCurvature (escapeH u)) := by
    let : Nonempty (sphere (0 : EscapeSpace) 1) :=
      ⟨⟨e, mem_sphere_zero_iff_norm.mpr he⟩⟩
    apply le_min (by nlinarith [sq_nonneg u])
    apply le_ciInf
    intro v
    have hb := h.curvature_lower ((v : EscapeSpace).ofLp 0) ((v : EscapeSpace).ofLp 1)
    rw [← escape_norm_sq, norm_eq_of_mem_sphere v, one_pow, mul_one] at hb
    rw [escapeH_apply]
    convert hb using 1
    ring
  have hdec := h.sufficient_decrease _ _ hβ ht
  have hpred : escapeModel u (escapePoint u) -
      escapeModel u (escapePoint u + (escapePoint (u / 2) - escapePoint u)) = u ^ 2 / 16 := by
    rw [show escapePoint u + (escapePoint (u / 2) - escapePoint u) = escapePoint (u / 2) by abel]
    exact escapeModel_predicted h
  constructor
  · refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    rw [hpred, mul_assoc, escapeModel_gradient_norm]
    exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)).trans hdec
  · refine ⟨by norm_num, fun ht ↦ ?_⟩
    rw [hpred, abs_of_neg ht, mul_assoc]
    exact (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)).trans hdec

private noncomputable def escapeFModel (u a : ℝ) (p : EscapeSpace) : ℝ :=
  barrierBilinearObjective p.ofLp + a * (p.ofLp 0 - 1 / u) ^ 2 / 2

private noncomputable def escapeFCross : EscapeSpace →L[ℝ] EscapeSpace →L[ℝ] ℝ :=
  (escapeL 0).smulRight (escapeL 1) + (escapeL 1).smulRight (escapeL 0)

private noncomputable def escapeFDiagonal : EscapeSpace →L[ℝ] EscapeSpace →L[ℝ] ℝ :=
  (escapeL 0).smulRight (escapeL 0)

private noncomputable def escapeFH (a : ℝ) : EscapeSpace →L[ℝ] EscapeSpace →L[ℝ] ℝ :=
  escapeFCross + a • escapeFDiagonal

private noncomputable def escapeFG (u : ℝ) : EscapeSpace →L[ℝ] ℝ :=
  escapeY u • escapeL 0 + (1 / u) • escapeL 1

private theorem escapeFModel_fderiv (u a : ℝ) (p : EscapeSpace) :
    fderiv ℝ (escapeFModel u a) p = escapeFG u + escapeFH a (p - escapePoint u) := by
  let m (s : EscapeSpace) := (1 / u) * escapeY u + escapeFG u s +
    (1 / 2 : ℝ) * escapeFH a s s
  have he : escapeFModel u a = fun p ↦ m (p - escapePoint u) := by
    funext v
    have hx0 : (escapePoint u).ofLp 0 = 1 / u := rfl
    have hx1 : (escapePoint u).ofLp 1 = escapeY u := rfl
    simp [m, escapeFModel, barrierBilinearObjective, escapeFG, escapeFH, escapeFCross,
      escapeFDiagonal, escapeL, hx0, hx1]
    ring
  have hs (v w : EscapeSpace) : escapeFH a v w = escapeFH a w v := by
    simp [escapeFH, escapeFCross, escapeFDiagonal, escapeL]
    ring
  rw [he]
  have hd := (barrierQuadratic_hasFDerivAt (a := (1 / u) * escapeY u) (g := escapeFG u) hs
    (p - escapePoint u)).comp p ((hasFDerivAt_id p).sub_const (escapePoint u))
  change HasFDerivAt (fun v ↦ m (v - escapePoint u)) _ p at hd
  rw [hd.fderiv, ContinuousLinearMap.comp_id]

private theorem escapeFModel_hessian (u a : ℝ) (p : EscapeSpace) :
    fderiv ℝ (fderiv ℝ (escapeFModel u a)) p = escapeFH a := by
  rw [funext (escapeFModel_fderiv u a)]
  have hd := ((escapeFH a).hasFDerivAt (x := p - escapePoint u)).comp p
    ((hasFDerivAt_id p).sub_const (escapePoint u))
  have hd' := (hd.const_add (escapeFG u)).fderiv
  change fderiv ℝ (fun v ↦ escapeFG u + escapeFH a (v - escapePoint u)) p = _ at hd'
  simpa only [ContinuousLinearMap.comp_id] using hd'

/-- The objective model in the counterexample has the correct value and
gradient at the center and uniformly bounded Hessian. The total model
Hessian is constant throughout the trust region. The other model term
is the quadratic Taylor model of the logarithmic barrier. -/
theorem escapeModel_source_models :
    ∃ B : ℝ, ∀ u, PrimalBarrierEscapeTrial u → ∃ mf : EscapeSpace → ℝ,
      ContDiff ℝ 2 mf ∧
      mf (escapePoint u) = barrierBilinearObjective (escapePoint u).ofLp ∧
      fderiv ℝ mf (escapePoint u) =
        fderiv ℝ (fun p : EscapeSpace ↦ barrierBilinearObjective p.ofLp) (escapePoint u) ∧
      (∀ p, ‖fderiv ℝ (fderiv ℝ mf) p‖ ≤ B) ∧
      (∀ p q, fderiv ℝ (fderiv ℝ (escapeModel u)) p =
        fderiv ℝ (fderiv ℝ (escapeModel u)) q) ∧
      ∀ p, escapeModel u p = mf p +
        logBarrierModel (escapePoint u).ofLp (p - escapePoint u).ofLp 1 := by
  refine ⟨‖escapeFCross‖ + 9 * ‖escapeFDiagonal‖, fun u h ↦ ?_⟩
  let a := (escapeA u - 1) * u ^ 2
  have hx0 : (escapePoint u).ofLp 0 = 1 / u := rfl
  have hx1 : (escapePoint u).ofLp 1 = escapeY u := rfl
  refine ⟨escapeFModel u a, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold escapeFModel barrierBilinearObjective
    have h₀ : ContDiff ℝ 2 (escapeL 0) := (escapeL 0).contDiff
    have h₁ : ContDiff ℝ 2 (escapeL 1) := (escapeL 1).contDiff
    have hc : ContDiff ℝ 2 (fun p : EscapeSpace ↦ a * ((escapeL 0) p - 1 / u) ^ 2 / 2) :=
      (contDiff_const.mul ((h₀.sub contDiff_const).pow 2)).div_const 2
    exact (h₀.mul h₁).add hc
  · simp [escapeFModel, hx0]
  · have hf : (fun p : EscapeSpace ↦ barrierBilinearObjective p.ofLp) = escapeFModel u 0 := by
      funext p
      simp [escapeFModel]
    rw [hf, escapeFModel_fderiv, escapeFModel_fderiv, sub_self, map_zero, map_zero]
  · intro p
    rw [escapeFModel_hessian, escapeFH]
    have ha : |a| ≤ 9 := h.objective_model_bound
    have hd : ‖a • escapeFDiagonal‖ ≤ |a| * ‖escapeFDiagonal‖ := by
      simpa only [Real.norm_eq_abs] using ContinuousLinearMap.opNorm_smul_le a escapeFDiagonal
    calc
      ‖escapeFCross + a • escapeFDiagonal‖ ≤ ‖escapeFCross‖ + ‖a • escapeFDiagonal‖ :=
        norm_add_le escapeFCross (a • escapeFDiagonal)
      _ ≤ ‖escapeFCross‖ + 9 * ‖escapeFDiagonal‖ :=
        add_le_add le_rfl (hd.trans (mul_le_mul_of_nonneg_right ha (norm_nonneg escapeFDiagonal)))
  · intro p q
    rw [escapeModel_hessian, escapeModel_hessian]
  · intro p
    have hh := h.model_matches (p.ofLp 0 - 1 / u) (p.ofLp 1 - escapeY u)
    dsimp only at hh
    have h0 : 1 / u + (p.ofLp 0 - 1 / u) = p.ofLp 0 := by ring
    have h1 : escapeY u + (p.ofLp 1 - escapeY u) = p.ofLp 1 := by ring
    rw [h0, h1] at hh
    unfold escapeModel escapeFModel barrierBilinearObjective logBarrierModel
    simp only [hx0, hx1, WithLp.ofLp_sub, Pi.sub_apply, Fin.sum_univ_two, logBarrier,
      Optimization.logBarrier, one_mul]
    simp only [div_eq_mul_inv, ← inv_pow] at hh ⊢
    linear_combination -hh

private theorem escapePoint_no_first_order_stop {u εE : ℝ} (h : PrimalBarrierEscapeTrial u) :
    ¬ BarrierSecondOrderStop barrierBilinearObjective (escapePoint u).ofLp 1 (1 / 4) εE := by
  intro hstop
  let y := (escapePoint u).ofLp
  have hg : barrierCoordinateGradient barrierBilinearObjective y 1 - 1 / y 1 = 1 / (1 + u) := by
    unfold barrierCoordinateGradient
    rw [barrierBilinearObjective_fderiv_apply]
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide),
      mul_zero, mul_one, add_zero]
    change 1 / u - 1 / escapeY u = _
    unfold escapeY
    field_simp [h.parameter_pos.ne', show 1 + u ≠ 0 by linarith [h.parameter_pos]]
    ring
  have hsum := Finset.single_le_sum (s := Finset.univ)
    (fun i _ ↦ sq_nonneg (barrierCoordinateGradient barrierBilinearObjective y i - 1 / y i))
    (Finset.mem_univ (1 : Fin 2))
  have hs := hsum.trans hstop.2.1
  rw [hg] at hs
  exact (not_lt_of_ge ((sq_le_sq₀
    (div_nonneg zero_le_one (by linarith [h.parameter_pos])) (by norm_num)).mp hs))
    h.fails_gradient_stop

/-- The unbounded trial certificate yields an actual run of Algorithm
13.2.1 in the Euclidean orthant. Its ratios are computed from the true
logarithmic barrier and the certified model, and every trial is very
successful. At each iterate the certified gradient fails the tolerance. -/
theorem theorem_13_4_2_unbounded_primal_inner_run :
    ∃ r : PrimalBarrierInnerRun Chapter06.defaultBTRParams escapeOrthant (1 / 4) escapeObjective,
      (∀ p ∈ interior escapeOrthant,
        escapeObjective p = logBarrierObjective barrierBilinearObjective p.ofLp 1) ∧
      ContDiff ℝ 2 barrierBilinearObjective ∧
      (∃ H, ∀ p, ‖fderiv ℝ (fderiv ℝ barrierBilinearObjective) p‖ ≤ H) ∧
      (∀ μ > 0, ∃ A : ℝ, ∀ p : Fin 2 → ℝ, (∀ i, 0 < p i) →
        A ≤ logBarrierObjective barrierBilinearObjective p μ) ∧
      (∀ j εE, ¬ BarrierSecondOrderStop barrierBilinearObjective (r.x j).ofLp 1 (1 / 4) εE) ∧
      (¬ Tendsto (fun j ↦ ‖gradient (r.model j) (r.x j)‖) atTop (𝓝 0)) ∧
      (∀ j,
        let H := fderiv ℝ (fderiv ℝ (r.model j)) (r.x j)
        let β := 1 + ‖H‖
        let τ := min 0 (Chapter06.leastUnitCurvature H)
        Chapter06.HasSufficientModelDecrease (r.model j) (r.x j) (r.s j)
          (gradient (r.model j) (r.x j)) β (r.Δ j) (1 / 32768) ∧
        Chapter06.HasNegativeCurvatureDecrease (r.model j) (r.x j) (r.s j) τ (r.Δ j) (1 / 32768)) ∧
      ∃ u : ℕ → ℝ, Tendsto u atTop (𝓝 0) ∧ (∀ j, PrimalBarrierEscapeTrial (u j)) ∧
        (∀ j, r.x j = escapePoint (u j) ∧ r.Δ j = 2 / u j ∧ r.model j = escapeModel (u j)) ∧
        (∀ j, 2 ≤ primalBarrierRatio escapeOrthant (1 / 4) escapeObjective
          (r.model j) (r.x j) (r.s j)) := by
  obtain ⟨u, hu, hup, htrial, hratio, hAW⟩ := theorem_13_4_2_unbounded_run_counterexample
  let x (j : ℕ) := escapePoint (u j)
  let s (j : ℕ) := x (j + 1) - x j
  let Δ (j : ℕ) := 2 / u j
  let m (j : ℕ) := escapeModel (u j)
  have hxpos (j : ℕ) : ∀ i, 0 < (x j).ofLp i := escapePoint_positive (htrial j).parameter_pos
  have hstep (j : ℕ) : x j + s j = x (j + 1) := by dsimp [s]; abel
  have hdouble (j : ℕ) : (1 : ℝ) / u (j + 1) = 2 * (1 / u j) := by
    rw [hup]
    field_simp [(htrial j).parameter_pos.ne']
  have ha (j : ℕ) : BarrierAdmissibleTrial escapeOrthant (1 / 4) (x j) (x j + s j) := by
    rw [hstep]
    refine ⟨escapeOrthant_interior (hxpos _), ?_⟩
    rw [escapeOrthant_boundary_dist (hxpos _), escapeOrthant_boundary_dist (hxpos _)]
    change (1 / 4 : ℝ) * min (1 / u j) (escapeY (u j)) ≤
      min (1 / u (j + 1)) (escapeY (u (j + 1)))
    rw [hdouble, hup]
    exact (htrial j).trial_inside.2.2.1
  have hp (j : ℕ) : m j (x j) - m j (x j + s j) = u j ^ 2 / 16 := by
    rw [hstep]
    change escapeModel (u j) (escapePoint (u j)) -
      escapeModel (u j) (escapePoint (u (j + 1))) = _
    rw [hup]
    exact escapeModel_predicted (htrial j)
  have hr (j : ℕ) : 2 ≤ primalBarrierRatio escapeOrthant (1 / 4) escapeObjective (m j) (x j) (s j) := by
    rw [primalBarrierRatio, ite_eq_left (ha j), Chapter06.btrRatio, Optimization.reductionRatio, hp j,
      hstep, escapeObjective_at_point (htrial j).parameter_pos,
      escapeObjective_at_point (htrial (j + 1)).parameter_pos]
    exact hratio j
  have hη (j : ℕ) : Chapter06.defaultBTRParams.η₂ ≤
      primalBarrierRatio escapeOrthant (1 / 4) escapeObjective (m j) (x j) (s j) :=
    (Chapter06.defaultBTRParams.eta₂_lt_one.le.trans (by norm_num)).trans (hr j)
  let r : PrimalBarrierInnerRun Chapter06.defaultBTRParams escapeOrthant (1 / 4) escapeObjective :=
    { x := x
      s := s
      Δ := Δ
      model := m
      initial_interior := escapeOrthant_interior (hxpos 0)
      initial_radius_pos := div_pos (by norm_num) (htrial 0).parameter_pos
      step_feasible := fun j ↦ by
        apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (by norm_num) (htrial j).parameter_pos.le)).mp
        rw [escape_norm_sq]
        change (1 / u (j + 1) - 1 / u j) ^ 2 +
          (escapeY (u (j + 1)) - escapeY (u j)) ^ 2 ≤ (2 / u j) ^ 2
        rw [hdouble, hup]
        have h := (htrial j).trial_inside.2.2.2
        convert h using 1
        ring
      predicted_pos := fun j ↦ by rw [hp]; positivity [(htrial j).parameter_pos]
      iterate_update := fun j ↦ by
        rw [ite_eq_left (Chapter06.defaultBTRParams.eta₁_le_eta₂.trans (hη j)), hstep]
      radius_update := fun j ↦
        ⟨fun _ ↦ by
          have h : Δ (j + 1) = 2 * Δ j := by
            dsimp [Δ]
            rw [hup]
            field_simp [(htrial j).parameter_pos.ne']
          rw [h]
          linarith [div_pos (show (0 : ℝ) < 2 by norm_num) (htrial j).parameter_pos]
        , fun _ h ↦ (h.not_ge (hη j)).elim
        , fun h ↦ (h.not_ge (Chapter06.defaultBTRParams.eta₁_le_eta₂.trans (hη j))).elim⟩ }
  obtain ⟨hf, hH⟩ := barrierBilinearObjective_smooth_bounded_hessian
  have hbar : ∀ μ > 0, ∃ A : ℝ, ∀ p : Fin 2 → ℝ, (∀ i, 0 < p i) →
      A ≤ logBarrierObjective barrierBilinearObjective p μ := by
    intro μ hμ
    obtain ⟨A, hA⟩ := hAW μ hμ
    refine ⟨A, fun p hp ↦ ?_⟩
    change A ≤ p 0 * p 1 + (-μ) * (∑ i, Real.log (p i))
    rw [Fin.sum_univ_two]
    linarith [hA (p 0) (p 1) (hp 0) (hp 1)]
  have hnograd : ¬ Tendsto (fun j ↦ ‖gradient (r.model j) (r.x j)‖) atTop (𝓝 0) := by
    intro ht
    obtain ⟨j, hj⟩ := (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).exists
    change ‖gradient (escapeModel (u j)) (escapePoint (u j))‖ < (1 / 4 : ℝ) at hj
    rw [escapeModel_gradient_norm] at hj
    have hpos : 0 ≤ 1 / (1 + u j) := by
      have := (htrial j).parameter_pos
      positivity
    have hle : 1 / (1 + u j) ≤ Real.sqrt (((u j) ^ 2) ^ 2 + (1 / (1 + u j)) ^ 2) := by
      calc
        _ = Real.sqrt ((1 / (1 + u j)) ^ 2) := (Real.sqrt_sq hpos).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by linarith [sq_nonneg ((u j) ^ 2)])
    exact hj.not_ge ((htrial j).fails_gradient_stop.le.trans hle)
  have had (j : ℕ) :
      let H := fderiv ℝ (fderiv ℝ (r.model j)) (r.x j)
      Chapter06.HasSufficientModelDecrease (r.model j) (r.x j) (r.s j)
        (gradient (r.model j) (r.x j)) (1 + ‖H‖) (r.Δ j) (1 / 32768) ∧
      Chapter06.HasNegativeCurvatureDecrease (r.model j) (r.x j) (r.s j)
        (min 0 (Chapter06.leastUnitCurvature H)) (r.Δ j) (1 / 32768) := by
    have hh : s j = escapePoint (u j / 2) - escapePoint (u j) := by
      change escapePoint (u (j + 1)) - escapePoint (u j) = _
      rw [hup]
    change Chapter06.HasSufficientModelDecrease _ _ (s j) _ _ _ _ ∧
      Chapter06.HasNegativeCurvatureDecrease _ _ (s j) _ _ _
    rw [hh]
    exact escapeModel_adequate_decrease (htrial j)
  refine ⟨r, ?_, hf, hH, hbar, fun j _ ↦ escapePoint_no_first_order_stop (htrial j),
    hnograd, had, u, hu, htrial, fun _ ↦ ⟨rfl, rfl, rfl⟩, hr⟩
  intro p hp
  have hp' : p.ofLp ∈ interior (Optimization.nonnegativeOrthant (Fin 2)) := by
    let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).toHomeomorph
    change p ∈ interior (T ⁻¹' Optimization.nonnegativeOrthant (Fin 2)) at hp
    rw [← T.preimage_interior] at hp
    exact hp
  change p.ofLp ∈ interior (Set.univ.pi (fun _ : Fin 2 ↦ Ici (0 : ℝ))) at hp'
  rw [interior_pi_set Set.finite_univ] at hp'
  have hpos : ∀ i, 0 < p.ofLp i := by
    simpa only [Set.mem_pi, Set.mem_univ, true_implies, interior_Ici, Set.mem_Ioi] using hp'
  change p.ofLp 0 * p.ofLp 1 - Real.log (p.ofLp 0 * p.ofLp 1) =
    p.ofLp 0 * p.ofLp 1 + (-1 : ℝ) * ∑ i, Real.log (p.ofLp i)
  rw [Fin.sum_univ_two, Real.log_mul (hpos 0).ne' (hpos 1).ne']
  ring

end PrimalEscape

end ConnGouldToint.Chapter13
