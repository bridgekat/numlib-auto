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
theorem barrierQuadratic_hasFDerivAt {a : ℝ}
    {g : (ι → ℝ) →L[ℝ] ℝ} {H : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ}
    (hs : ∀ d e, H d e = H e d) (s : ι → ℝ) :
    HasFDerivAt (fun d ↦ a + g d + (1 / 2 : ℝ) * H d d) (g + H s) s := by
  have hquad₀ := H.hasFDerivAt.clm_apply (hasFDerivAt_id s)
  have heq : (H s).comp (ContinuousLinearMap.id ℝ (ι → ℝ)) + H.flip s = (2 : ℝ) • H s := by
    ext d
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply,
      smul_apply, smul_eq_mul, hs d s]
    ring
  simp only [id_eq] at hquad₀
  rw [heq] at hquad₀
  have hquad : HasFDerivAt (fun d : ι → ℝ ↦ H d d) ((2 : ℝ) • H s) s := by
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

open Chapter06

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

end ConnGouldToint.Chapter13
