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
