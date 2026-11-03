import Numlib.Optimization.Constrained
import NumlibSurface.ConnGouldToint.Chapter03.Section01
import NumlibSurface.ConnGouldToint.Chapter12.Section03
import NumlibSurface.ConnGouldToint.Chapter06.Section06

/-! # Lagrangian models on an identified face -/

open Set Optimization Filter Topology
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter12

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

/-- The fixed-multiplier model (12.4.3), for constraints written as (c_i ≥ 0). -/
def faceLagrangianModel (m : E → ℝ) (c : ι → E → ℝ) (y : ι → ℝ) (x : E) : ℝ :=
  Constrained.lagrangian m c x (fun i ↦ -y i)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The Lagrangian model agrees with the objective model on the active face. -/
theorem faceLagrangianModel_eq_of_active {m : E → ℝ} {c : ι → E → ℝ} {y : ι → ℝ}
    {x z : E} (hA : activeConstraintSet c z = activeConstraintSet c x)
    (hy : ∀ i ∉ activeConstraintSet c x, y i = 0) :
    faceLagrangianModel m c y z = m z := by
  unfold faceLagrangianModel Constrained.lagrangian
  suffices h : (∑ i, -y i * c i z) = 0 by rw [h, add_zero]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ activeConstraintSet c x
  · have hz : c i z = 0 := show i ∈ activeConstraintSet c z by rwa [hA]
    rw [hz, mul_zero]
  · rw [hy i hi, neg_zero, zero_mul]

private theorem exists_affine_ray_taylor {L : E → ℝ} (hL : ContDiff ℝ 2 L) (x s : E) :
    ∃ t ∈ Ioc (0 : ℝ) 1,
      L (x + s) = L x + fderiv ℝ L x s +
        (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ L) (x + t • s) s s := by
  let ray (t : ℝ) := L (x + t • s)
  have hray : ContDiff ℝ 2 ray := hL.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hderiv (t : ℝ) : deriv ray t = fderiv ℝ L (x + t • s) s :=
    ((hL.differentiable (by norm_num) _).hasDerivAt_comp_add_smul).deriv
  have hderiv₂ (t : ℝ) : iteratedDeriv 2 ray t = fderiv ℝ (fderiv ℝ L) (x + t • s) s s := by
    have hD : ContDiff ℝ 1 (fderiv ℝ L) := hL.fderiv_right (by norm_num)
    have hd := ((hD.differentiable (by norm_num) (x + t • s)).hasDerivAt_comp_add_smul).clm_apply
      (hasDerivAt_const t s)
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one, funext hderiv]
    simpa only [map_zero, add_zero] using hd.deriv
  have h01 : (0 : ℝ) ≠ 1 := by norm_num
  obtain ⟨t, ht, h⟩ := exists_taylorWithinEval_add_iteratedDeriv_mul
    (n := 1) h01 hray.contDiffOn
  rw [taylorWithinEval_eq_sum_of_contDiffAt h01 (hray.contDiffAt.of_le (by norm_num)),
    Finset.sum_range_succ, Finset.sum_range_one, iteratedDeriv_zero, iteratedDeriv_one,
    hderiv, hderiv₂] at h
  have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa only [uIoo_of_le zero_le_one] using ht
  refine ⟨t, ⟨ht'.1, ht'.2.le⟩, ?_⟩
  norm_num [ray] at h
  linarith only [h]

variable [CompleteSpace E]

/-- The projected gradient identity (12.4.1). The normal projection is
represented by the active multipliers, and the two projections add to
the negative objective gradient by the tangent/normal decomposition. -/
theorem fderiv_faceLagrangianModel_eq_tangent {C : Set E} {m f : E → ℝ}
    {c : ι → E → ℝ} {y : ι → ℝ} {x : E}
    (hm : DifferentiableAt ℝ m x) (hc : ∀ i, DifferentiableAt ℝ (c i) x)
    (hmatch : fderiv ℝ m x = fderiv ℝ f x)
    (hnormal : bestApprox (normalDirections C x) (-gradient f x) =
      -∑ i, y i • gradient (c i) x)
    (hmoreau : bestApprox (tangentDirections C x) (-gradient f x) +
      bestApprox (normalDirections C x) (-gradient f x) = -gradient f x)
    (v : E) :
    fderiv ℝ (faceLagrangianModel m c y) x v =
      -⟪bestApprox (tangentDirections C x) (-gradient f x), v⟫ := by
  have hd := (Constrained.lagrangian_hasFDerivAt hm.hasFDerivAt
    (fun i ↦ (hc i).hasFDerivAt) (fun i ↦ -y i)).fderiv
  unfold faceLagrangianModel
  rw [hd, add_apply, sum_apply, hmatch, ← inner_gradient_left]
  have h := congrArg (fun w : E ↦ ⟪w, v⟫) hmoreau
  rw [hnormal, inner_add_left, inner_neg_left, sum_inner, inner_neg_left] at h
  simp only [smul_apply, smul_eq_mul, ← inner_gradient_left, neg_mul]
  rw [Finset.sum_neg_distrib]
  simp only [real_inner_smul_left] at h
  linarith only [h]

/-- Equation (12.4.1) uses the normal projection to identify the multiplier
term. The tangent component then follows from Moreau's decomposition. -/
theorem fderiv_faceLagrangianModel_eq_tangent_of_normal_projection {C : Set E}
    {m f : E → ℝ} {c : ι → E → ℝ} {y : ι → ℝ} {x : E}
    (hm : DifferentiableAt ℝ m x) (hc : ∀ i, DifferentiableAt ℝ (c i) x)
    (hmatch : fderiv ℝ m x = fderiv ℝ f x)
    (hnormal : bestApprox (normalDirections C x) (-gradient f x) =
      -∑ i, y i • gradient (c i) x) (v : E) :
    fderiv ℝ (faceLagrangianModel m c y) x v =
      -⟪bestApprox (tangentDirections C x) (-gradient f x), v⟫ :=
  fderiv_faceLagrangianModel_eq_tangent hm hc hmatch hnormal
    (Chapter03.moreau_normal_tangent C x (-gradient f x)).1.symm v

/-- Lemma 12.4.1. On a fixed face the endpoint values of the model are those
of its Lagrangian. The first-order identity is (12.4.1), obtained from the
least-squares multipliers and the tangent/normal decomposition. -/
theorem lemma_12_4_1 {C : Set E} {m f : E → ℝ} {c : ι → E → ℝ} {y : ι → ℝ} {x s : E}
    (hA : activeConstraintSet c (x + s) = activeConstraintSet c x)
    (hy : ∀ i ∉ activeConstraintSet c x, y i = 0)
    (hL : ContDiff ℝ 2 (faceLagrangianModel m c y))
    (hgrad : fderiv ℝ (faceLagrangianModel m c y) x s =
      -⟪bestApprox (tangentDirections C x) (-gradient f x), s⟫) :
    ∃ t ∈ Ioc (0 : ℝ) 1, m (x + s) =
      m x - ⟪bestApprox (tangentDirections C x) (-gradient f x), s⟫ +
        (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ (faceLagrangianModel m c y)) (x + t • s) s s := by
  obtain ⟨t, ht, h⟩ := exists_affine_ray_taylor hL x s
  rw [faceLagrangianModel_eq_of_active hA hy, faceLagrangianModel_eq_of_active rfl hy, hgrad] at h
  exact ⟨t, ht, by simpa only [sub_eq_add_neg] using h⟩

/-- Lemma 12.4.2. Positive curvature on the step segment bounds the
step by its tangent linear decrease. The product inequality includes the
zero step. Division by its norm gives (12.4.5) for nonzero steps. -/
theorem lemma_12_4_2 {C : Set E} {m f : E → ℝ} {c : ι → E → ℝ} {y : ι → ℝ} {x s : E}
    (hA : activeConstraintSet c (x + s) = activeConstraintSet c x)
    (hy : ∀ i ∉ activeConstraintSet c x, y i = 0)
    (hL : ContDiff ℝ 2 (faceLagrangianModel m c y))
    (hgrad : fderiv ℝ (faceLagrangianModel m c y) x s =
      -⟪bestApprox (tangentDirections C x) (-gradient f x), s⟫)
    {ε : ℝ} (hε : 0 < ε) (hdec : m (x + s) ≤ m x)
    (hcurv : ∀ t ∈ Ioc (0 : ℝ) 1, ε * ‖s‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (faceLagrangianModel m c y)) (x + t • s) s s) :
    let l := ⟪bestApprox (tangentDirections C x) (-gradient f x), s⟫
    ε * ‖s‖ ^ 2 ≤ 2 * l ∧ (s ≠ 0 → ‖s‖ ≤ (2 * l) / (ε * ‖s‖)) := by
  obtain ⟨t, ht, h⟩ := lemma_12_4_1 hA hy hL hgrad
  have hb := hcurv t ht
  dsimp only
  have hprod : ε * ‖s‖ ^ 2 ≤ 2 * ⟪bestApprox (tangentDirections C x) (-gradient f x), s⟫ := by
    linarith only [h, hb, hdec]
  exact ⟨hprod, fun hs ↦ (le_div_iff₀ (mul_pos hε (norm_pos_iff.mpr hs))).mpr
    (by nlinarith only [hprod])⟩

omit [Fintype ι] [CompleteSpace E] in
/-- Theorem 12.4.3 in its identified-face form. A strict minimum on the
closed face and a locally vanishing step bound trap the monotone run
once a subsequence enters a sufficiently low objective sublevel. -/
theorem theorem_12_4_3 [ProperSpace E] {P : Chapter06.BTRParams} {f : E → ℝ}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop} (run : Chapter06.BTRRun f P sufficient)
    {F : Set E} (hF : IsClosed F) {z : E} {j : ℕ → ℕ} (hj : StrictMono j)
    (hz : Tendsto (run.x ∘ j) atTop (𝓝 z)) (hf : Continuous f)
    {ρ : ℝ} (hρ : 0 < ρ) (hmin : ∀ y ∈ F, 0 < dist y z → dist y z ≤ ρ → f z < f y)
    (hface : ∀ᶠ k in atTop, dist (run.x k) z ≤ ρ → run.x k ∈ F)
    (hsmall : ∀ ε > (0 : ℝ), ∃ R > (0 : ℝ), ∀ᶠ k in atTop, dist (run.x k) z < R →
      dist (run.x (k + 1)) (run.x k) ≤ ε) :
    Tendsto run.x atTop (𝓝 z) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let e := min (ε / 2) (ρ / 2)
  have he : 0 < e := lt_min (half_pos hε) (half_pos hρ)
  have heε : e ≤ ε / 2 := min_le_left _ _
  have heρ : e ≤ ρ / 2 := min_le_right _ _
  obtain ⟨R, hR, hstep⟩ := hsmall e he
  let r := min e R
  have hr : 0 < r := lt_min he hR
  have hre : r ≤ e := min_le_left _ _
  have hrR : r ≤ R := min_le_right _ _
  let A := (Metric.closedBall z (2 * e) ∩ F) ∩ {y : E | r ≤ dist y z}
  have hA : IsCompact A := ((isCompact_closedBall _ _).inter_right hF).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hgap : ∃ b > f z, ∀ y ∈ A, b ≤ f y := by
    by_cases hne : A.Nonempty
    · obtain ⟨u, hu, hmu⟩ := hA.exists_isMinOn hne hf.continuousOn
      have hu₀ : r ≤ dist u z := hu.2
      have huρ : dist u z ≤ ρ := (show dist u z ≤ 2 * e from hu.1.1).trans (by linarith)
      exact ⟨f u, hmin u hu.1.2 (hr.trans_le hu₀) huρ, fun y hy ↦ (isMinOn_iff.mp hmu) y hy⟩
    · exact ⟨f z + 1, by linarith, fun y hy ↦ (hne ⟨y, hy⟩).elim⟩
  obtain ⟨b, hb, hgap⟩ := hgap
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hface.and hstep)
  obtain ⟨i, hi, hiz, hif⟩ := ((hj.tendsto_atTop.eventually_ge_atTop N).and
    ((hz.eventually (Metric.ball_mem_nhds z hr)).and
      ((hf.continuousAt.tendsto.comp hz).eventually_lt_const hb))).exists
  let n := j i
  have hnear (p : ℕ) : dist (run.x (n + p)) z < r := by
    induction p with
    | zero => exact hiz
    | succ p ih =>
      let k := n + p
      have hkN := hi.trans (Nat.le_add_right n p)
      have hmove := (hN k hkN).2 (ih.trans_le hrR)
      have hd : dist (run.x (k + 1)) z ≤ 2 * e := by
        have ht := dist_triangle (run.x (k + 1)) (run.x k) z
        linarith only [ht, hmove, ih, hre]
      have hpρ : dist (run.x (k + 1)) z ≤ ρ := hd.trans (by linarith)
      have hfnext : f (run.x (k + 1)) < b :=
        (run.objective_antitone (show n ≤ k + 1 by omega)).trans_lt hif
      rw [Nat.add_succ]
      exact lt_of_not_ge fun hh ↦ hfnext.not_ge
        (hgap _ ⟨⟨hd, (hN _ (hkN.trans (Nat.le_succ k))).1 hpρ⟩, hh⟩)
  exact eventually_atTop.mpr ⟨n, fun k hk ↦ by
    have hh := hnear (k - n)
    rw [Nat.add_sub_of_le hk] at hh
    exact hh.trans_le (hre.trans (heε.trans (half_le_self hε.le)))⟩

/-- The convergence theorem on an identified face, with the local step
bound derived from the Lagrangian curvature and the small projected gradient. -/
theorem theorem_12_4_3_of_lagrangian [ProperSpace E] {P : Chapter06.BTRParams} {f : E → ℝ}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop} (run : Chapter06.BTRRun f P sufficient)
    {C F : Set E} (hF : IsClosed F) {z : E} {j : ℕ → ℕ} (hj : StrictMono j)
    (hz : Tendsto (run.x ∘ j) atTop (𝓝 z)) (hf : Continuous f)
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hmin : ∀ y ∈ F, 0 < dist y z → dist y z ≤ ρ → f z < f y)
    (hface : ∀ᶠ k in atTop, dist (run.x k) z ≤ ρ → run.x k ∈ F)
    {c : ι → E → ℝ} (y : ℕ → ι → ℝ)
    (hmodel : ∀ᶠ k in atTop, dist (run.x k) z < ρ → k ∈ run.successful →
      activeConstraintSet c (run.x k + run.s k) = activeConstraintSet c (run.x k) ∧
      (∀ i ∉ activeConstraintSet c (run.x k), y k i = 0) ∧
      ContDiff ℝ 2 (faceLagrangianModel (run.model k) c (y k)) ∧
      fderiv ℝ (faceLagrangianModel (run.model k) c (y k)) (run.x k) (run.s k) =
        -⟪bestApprox (tangentDirections C (run.x k)) (-gradient f (run.x k)), run.s k⟫ ∧
      ∀ t ∈ Ioc (0 : ℝ) 1, ε * ‖run.s k‖ ^ 2 ≤
        fderiv ℝ (fderiv ℝ (faceLagrangianModel (run.model k) c (y k)))
          (run.x k + t • run.s k) (run.s k) (run.s k))
    (hproj : ∀ a > (0 : ℝ), ∃ R > (0 : ℝ), ∀ᶠ k in atTop, dist (run.x k) z < R →
      ‖bestApprox (tangentDirections C (run.x k)) (-gradient f (run.x k))‖ ≤ a) :
    Tendsto run.x atTop (𝓝 z) := by
  apply theorem_12_4_3 run hF hj hz hf hρ hmin hface
  intro a ha
  obtain ⟨R, hR, hp⟩ := hproj (ε * a / 2) (by positivity)
  refine ⟨min R ρ, lt_min hR hρ, ?_⟩
  filter_upwards [hp, hmodel] with k hk hmk hnear
  by_cases hs : k ∈ run.successful
  · obtain ⟨hA, hy, hL, hg, hH⟩ := hmk (hnear.trans_le (min_le_right _ _)) hs
    have hprod := (lemma_12_4_2 hA hy hL hg hε (sub_nonneg.mp (run.predicted_pos k).le) hH).1
    have hinner := real_inner_le_norm
      (bestApprox (tangentDirections C (run.x k)) (-gradient f (run.x k))) (run.s k)
    have hupper := mul_le_mul_of_nonneg_right (hk (hnear.trans_le (min_le_left _ _)))
      (norm_nonneg (run.s k))
    rw [run.iterate_update, acceptStep_of_le hs, dist_eq_norm, add_sub_cancel_left]
    by_contra! hbig
    have hh := mul_pos (mul_pos hε (ha.trans hbig))
      (sub_pos.mpr hbig)
    nlinarith only [hprod, hinner, hupper, hh]
  · rw [run.iterate_eq_of_unsuccessful hs, dist_self]
    exact ha.le

omit [Fintype ι] [CompleteSpace E] in
/-- A face-preserving direction extends through the linear active
constraints. A uniform inactive slack and a local Lipschitz bound keep
the extension feasible for the same length in every such direction. -/
theorem extendStep_mem_of_linear_active_face {c : ι → E → ℝ} {x s : E}
    {a L σ : ℝ} (ha : 0 ≤ a) (hσ : L * a ≤ σ) (hs : s ≠ 0)
    (hA : activeConstraintSet c (x + s) = activeConstraintSet c x)
    (haff : ∀ i ∈ activeConstraintSet c x, ∀ t : ℝ,
      c i (x + t • s) = c i x + t * (c i (x + s) - c i x))
    (hslack : ∀ i ∉ activeConstraintSet c x, σ ≤ c i x)
    (hlip : ∀ i ∉ activeConstraintSet c x, ∀ z, ‖z - x‖ ≤ a →
      |c i z - c i x| ≤ L * ‖z - x‖) :
    x + (a / ‖s‖) • s ∈ {z | ∀ i, 0 ≤ c i z} := by
  intro i
  by_cases hi : i ∈ activeConstraintSet c x
  · have hx : c i x = 0 := hi
    have hz : c i (x + s) = 0 := show i ∈ activeConstraintSet c (x + s) by rwa [hA]
    rw [haff i hi, hx, hz, sub_self, mul_zero, add_zero]
  · let z := x + (a / ‖s‖) • s
    have hz : ‖z - x‖ = a := by
      dsimp [z]
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (div_nonneg ha (norm_nonneg _)),
        div_mul_cancel₀ _ (norm_pos_iff.mpr hs).ne']
    have h := neg_abs_le (c i z - c i x)
    have hc := hlip i hi z hz.le
    rw [hz] at hc
    change 0 ≤ c i z
    linarith only [h, hc, hσ, hslack i hi]

/-- Lemma 12.4.4 with explicit face geometry. An extension of the step
direction by a uniform feasible length transfers positive curvature to the
capped linear criticality. AA.1b then gives a uniform quadratic decrease.
For a linear active face the tangent linear term equals the full one. -/
theorem lemma_12_4_4 {C : Set E} {m f : E → ℝ} {x s : E}
    {ε a M Δ β κ : ℝ} (hε : 0 < ε) (ha : 0 < a) (ha₁ : a ≤ 1)
    (hM : 0 < M) (hβ : 0 < β) (hκ : 0 < κ)
    (hstep : ‖s‖ ≤ Δ) (hbound : ‖s‖ ≤ M)
    (hextend : s ≠ 0 → x + (a / ‖s‖) • s ∈ C)
    (hlin : ε * ‖s‖ ^ 2 ≤ 2 * ⟪-gradient f x, s⟫)
    (hdec : κ * cappedCriticality C f x * min (cappedCriticality C f x / β) Δ ≤
      m x - m (x + s)) :
    ∃ δ > 0, δ * ‖s‖ ^ 2 ≤ m x - m (x + s) := by
  let b := min (1 / M) (a * ε / 2)
  have hb : 0 < b := lt_min (one_div_pos.mpr hM) (by positivity)
  refine ⟨κ * b * min (b / β) 1, mul_pos (mul_pos hκ hb) (lt_min (div_pos hb hβ) zero_lt_one), ?_⟩
  by_cases hs : s = 0
  · simp [hs]
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hscaled : ‖(a / ‖s‖) • s‖ ≤ (1 : ℝ) := by
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg ha.le hsn.le), div_mul_cancel₀ _ hsn.ne']
    exact ha₁
  have hχ := inner_le_linearDecrease (v := -gradient f x) (hextend hs) hscaled
  have hscale : (a * ε / 2) * ‖s‖ ≤ ⟪-gradient f x, (a / ‖s‖) • s⟫ := by
    rw [real_inner_smul_right]
    calc
      _ ≤ (a * ⟪-gradient f x, s⟫) / ‖s‖ := by
        apply (le_div_iff₀ hsn).mpr
        nlinarith only [mul_le_mul_of_nonneg_left hlin ha.le]
      _ = _ := by ring
  have hbχ : b * ‖s‖ ≤ cappedCriticality C f x := by
    apply le_min
    · exact ((mul_le_mul_of_nonneg_right (min_le_left _ _) hsn.le).trans
        (mul_le_mul_of_nonneg_left hbound (one_div_nonneg.mpr hM.le))).trans_eq
          (one_div_mul_cancel hM.ne')
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hsn.le).trans (hscale.trans hχ)
  have hmin : min (b / β) 1 * ‖s‖ ≤ min (cappedCriticality C f x / β) Δ := by
    rw [min_mul_of_nonneg _ _ hsn.le, one_mul]
    refine min_le_min ?_ hstep
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hbχ hβ.le
  have hbmin : 0 ≤ min (b / β) 1 * ‖s‖ := by positivity
  have hpred := mul_le_mul (mul_le_mul_of_nonneg_left hbχ hκ.le) hmin hbmin
    (mul_nonneg hκ.le ((mul_nonneg hb.le hsn.le).trans hbχ))
  exact (le_trans (by nlinarith only [hpred]) hdec)

omit [Fintype ι] [CompleteSpace E] in
/-- Theorem 12.4.5. Uniform Hessian agreement on the trial segments, as in
(12.4.7) for linear active constraints, and the quadratic decrease from
Lemma 12.4.4 make every sufficiently late iteration very successful. -/
theorem theorem_12_4_5 {P : Chapter06.BTRParams} {f : E → ℝ}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop} (run : Chapter06.BTRRun f P sufficient)
    (hf : ContDiff ℝ 2 f)
    (hm : ∀ k z, z ∈ segment ℝ (run.x k) (run.x k + run.s k) →
      DifferentiableAt ℝ (run.model k) z)
    (hDm : ∀ k z, z ∈ segment ℝ (run.x k) (run.x k + run.s k) →
      DifferentiableAt ℝ (fderiv ℝ (run.model k)) z)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hgrad : ∀ k, fderiv ℝ f (run.x k) = fderiv ℝ (run.model k) (run.x k))
    (hagree : ∀ a > (0 : ℝ), ∀ᶠ k in atTop, ∀ z ∈ segment ℝ (run.x k) (run.x k + run.s k),
      ‖fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ (run.model k)) z‖ ≤ a)
    {δ : ℝ} (hδ : 0 < δ) (hdec : ∀ᶠ k in atTop, δ * ‖run.s k‖ ^ 2 ≤
      run.model k (run.x k) - run.model k (run.x k + run.s k)) :
    (∀ᶠ k in atTop, k ∈ run.verySuccessful) ∧ ∃ r > 0, ∀ k, r ≤ run.Δ k := by
  let a := 2 * (1 - P.η₂) * δ
  have hη : 0 < 1 - P.η₂ := sub_pos.mpr P.eta₂_lt_one
  have ha : 0 < a := by dsimp [a]; positivity
  have hv : ∀ᶠ k in atTop, k ∈ run.verySuccessful := by
    filter_upwards [hagree a ha, hdec] with k hh hd
    have herr := Chapter06.abs_model_error_le hf (hval k) (hgrad k) (hm k) (hDm k) hh
    have he : |f (run.x k + run.s k) -
        (f (run.x k) - (run.model k (run.x k) - run.model k (run.x k + run.s k)))| ≤
        (1 - P.η₂) * (run.model k (run.x k) - run.model k (run.x k + run.s k)) := by
      rw [hval k, sub_sub_cancel]
      refine herr.trans ?_
      dsimp [a]
      have hh' := mul_le_mul_of_nonneg_left hd hη.le
      linarith only [hh', show (1 / 2 : ℝ) * (2 * (1 - P.η₂) * δ) * ‖run.s k‖ ^ 2 =
        (1 - P.η₂) * (δ * ‖run.s k‖ ^ 2) by ring]
    simpa only [sub_sub_cancel, Chapter06.BTRRun.verySuccessful, Set.mem_ofPred_eq,
      Chapter06.btrRatio] using le_reductionRatio_of_abs_sub_le (run.predicted_pos k) he
  exact ⟨hv, run.exists_delta_lower_bound_of_eventually_verySuccessful hv⟩

section FaceBoundary

open scoped ENNReal

/-- The locus where all constraints active at the center vanish. -/
def activeEqualityLocus (c : ι → E → ℝ) (x : E) : Set E :=
  {z | ∀ i ∈ activeConstraintSet c x, c i z = 0}

/-- The distance in (12.4.16) uses the frontier relative to the active
equality locus. An empty frontier gives infinite distance. -/
noncomputable def activeFaceBoundaryDistance (C : Set E) (c : ι → E → ℝ) (x : E) :
    ℝ≥0∞ :=
  Metric.infEDist (⟨x, fun _ hi ↦ hi⟩ : activeEqualityLocus c x)
    (frontier ((↑) ⁻¹' C : Set (activeEqualityLocus c x)))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Strict slack in every inactive inequality makes the center interior
relative to the active equality locus, giving positive face clearance. -/
theorem activeFaceBoundaryDistance_pos {C : Set E} {c : ι → E → ℝ} {x : E}
    (hC : Chapter03.AC7 C c) (hc : ∀ i, Continuous (c i)) (hx : x ∈ C) :
    0 < activeFaceBoundaryDistance C c x := by
  classical
  let L := activeEqualityLocus c x
  let z : L := ⟨x, fun _ hi ↦ hi⟩
  let F : Set L := (↑) ⁻¹' C
  let U : Set L := ⋂ i : {i // i ∉ activeConstraintSet c x}, {y | 0 < c i y}
  have hU : IsOpen U := isOpen_iInter_of_finite fun i ↦
    isOpen_lt continuous_const ((hc i).comp continuous_subtype_val)
  have hzx : z ∈ U := by
    apply mem_iInter.mpr
    intro i
    have hge : 0 ≤ c i x := by
      have hx' := hx
      rw [hC] at hx'
      exact hx' i
    exact lt_of_le_of_ne hge (Ne.symm i.property)
  have hUF : U ⊆ F := by
    intro y hy
    change (y : E) ∈ C
    rw [hC]
    intro i
    by_cases hi : i ∈ activeConstraintSet c x
    · exact (y.property i hi).ge
    · exact (mem_iInter.mp hy ⟨i, hi⟩ : 0 < c i y).le
  have hzF : z ∈ interior F :=
    mem_interior_iff_mem_nhds.mpr (mem_of_superset (hU.mem_nhds hzx) hUF)
  change 0 < Metric.infEDist z (frontier F)
  rw [Metric.infEDist_pos_iff_notMem_closure, isClosed_frontier.closure_eq]
  exact fun h ↦ h.2 hzF

end FaceBoundary

omit [Fintype ι] [CompleteSpace E] in
/-- The generalized eigenpoint test (12.4.14), with the sign corrected
so that a negative eigenvalue requires a decrease, and with the active-face
test included in the backtrack. -/
def ProjectedEigenTrialAccepted (C F : Set E) (m : E → ℝ) (x u : E)
    (q b τ : ℝ) (j : ℕ) : Prop :=
  projectedRay C x u (Chapter06.eigenTrialTime q j) ∈ F ∧
  m (projectedRay C x u (Chapter06.eigenTrialTime q j)) ≤
    m x + b * τ * (Chapter06.eigenTrialTime q j * ‖u‖) ^ 2

private theorem sq_min_eq_min_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (min a b) ^ 2 = min (a ^ 2) (b ^ 2) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (pow_le_pow_left₀ ha h 2)]
  · rw [min_eq_right h, min_eq_right (pow_le_pow_left₀ hb h 2)]

/-- A quadratically small projection correction gives the generalized
eigenpoint Taylor bound. The change in the quadratic form is cubic
because both the trial and the projected step have length at most the
ray length. -/
theorem projectedRay_taylor_upper_of_face {C : Set E} {m : E → ℝ}
    {c : ι → E → ℝ} {y : ι → ℝ} {x u : E} {t B γ κ τ : ℝ} (ht : 0 ≤ t)
    (hA : activeConstraintSet c (projectedRay C x u t) = activeConstraintSet c x)
    (hy : ∀ i ∉ activeConstraintSet c x, y i = 0)
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hx : x ∈ C)
    (hproj : ‖projectedRay C x u t - (x + t • u)‖ ≤ B * (t * ‖u‖) ^ 2)
    {S : Set E} (hS : IsOpen S) (hL : ContDiffOn ℝ 2 (faceLagrangianModel m c y) S)
    (hseg : ∀ a ∈ Icc (0 : ℝ) 1, x + a • (projectedRay C x u t - x) ∈ S)
    (hlip : ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ (faceLagrangianModel m c y)) z -
      fderiv ℝ (fderiv ℝ (faceLagrangianModel m c y)) x‖ ≤ γ * ‖z - x‖)
    (hγ : 0 ≤ γ)
    (hcurv : fderiv ℝ (fderiv ℝ (faceLagrangianModel m c y)) x u u ≤ κ * τ * ‖u‖ ^ 2) :
    let L := faceLagrangianModel m c y
    let H := fderiv ℝ (fderiv ℝ L) x
    m (projectedRay C x u t) ≤ m x + t * fderiv ℝ L x u +
      (κ / 2 * τ + ‖fderiv ℝ L x‖ * B) * (t * ‖u‖) ^ 2 +
      (γ / 6 + ‖H‖ * B) * (t * ‖u‖) ^ 3 := by
  let L := faceLagrangianModel m c y
  let H := fderiv ℝ (fderiv ℝ L) x
  let z := projectedRay C x u t
  let v := z - x
  let w := t • u
  let a := t * ‖u‖
  have hself : bestApprox C x = x :=
    (bestApprox_eq_iff ⟨x, hx⟩ hclosed hconv).mpr ⟨hx, by simp⟩
  have hstep : ‖v‖ ≤ a := by
    have h := norm_bestApprox_sub_bestApprox_le ⟨x, hx⟩ hclosed hconv (x + t • u) x
    rw [hself, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht] at h
    exact h
  have hw : ‖w‖ = a := by simp [w, a, norm_smul, Real.norm_of_nonneg ht]
  have hvw : ‖v - w‖ ≤ B * a ^ 2 := by
    simpa only [v, w, z, sub_sub] using hproj
  have hB : 0 ≤ B * a ^ 2 := (norm_nonneg _).trans hvw
  have hnorm (p q : E) : |H p q| ≤ ‖H‖ * ‖p‖ * ‖q‖ := by
    rw [← Real.norm_eq_abs]
    exact ((H p).le_opNorm q).trans (mul_le_mul_of_nonneg_right (H.le_opNorm p) (norm_nonneg q))
  have hquad : H v v - H w w ≤ 2 * ‖H‖ * B * a ^ 3 := by
    have heq : H v v - H w w = H (v - w) v + H w (v - w) := by
      simp only [map_sub, sub_apply]
      ring
    rw [heq]
    have hb₁ := (le_abs_self _).trans ((hnorm (v - w) v).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hvw (norm_nonneg H)) hstep (norm_nonneg v)
        (mul_nonneg (norm_nonneg H) hB)))
    have hb₂ := (le_abs_self _).trans ((hnorm w (v - w)).trans
      (mul_le_mul_of_nonneg_left hvw (mul_nonneg (norm_nonneg H) (norm_nonneg w))))
    rw [hw] at hb₂
    nlinarith only [hb₁, hb₂]
  have hlinear : fderiv ℝ L x v - t * fderiv ℝ L x u ≤ ‖fderiv ℝ L x‖ * B * a ^ 2 := by
    calc
      _ = fderiv ℝ L x (v - w) := by simp only [map_sub, w, map_smul, smul_eq_mul]
      _ ≤ ‖fderiv ℝ L x (v - w)‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
      _ ≤ ‖fderiv ℝ L x‖ * ‖v - w‖ := (fderiv ℝ L x).le_opNorm _
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hvw (norm_nonneg _)
  have hq : H w w ≤ κ * τ * a ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hcurv (sq_nonneg t)
    dsimp [H, w, a] at *
    simp only [map_smul, smul_apply, smul_eq_mul]
    nlinarith only [h]
  have hTaylor := (le_of_abs_le
    (abs_sub_secondOrder_le_of_lipschitzAt_segment hS hL hseg hlip)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hstep 3) (by positivity))
  have hz : x + v = z := by dsimp [v]; abel
  change L (x + v) - (L x + fderiv ℝ L x v + (1 / 2 : ℝ) * H v v) ≤ _ at hTaylor
  rw [hz, show L z = m z from faceLagrangianModel_eq_of_active hA hy,
    show L x = m x from faceLagrangianModel_eq_of_active rfl hy] at hTaylor
  change m z ≤ m x + t * fderiv ℝ L x u + (κ / 2 * τ + ‖fderiv ℝ L x‖ * B) * a ^ 2 +
    (γ / 6 + ‖H‖ * B) * a ^ 3
  nlinarith only [hTaylor, hlinear, hquad, hq]

omit [Fintype ι] [CompleteSpace E] in
/-- Corrected Theorem 12.4.6. The local projection geometry gives a
positive face radius and a Taylor estimate on projected trials. The
quadratic distortion accounts for the tangent gradient and multiplier
errors. A negative eigenvalue gives a positive decrease proportional to
its magnitude, with the face radius included in the bound. -/
theorem theorem_12_4_6 {C F : Set E} {m : E → ℝ} {x u : E}
    {q b κ τ σ D R g : ℝ} (hq : 0 < q) (hq' : q < 1) (hb : 0 < b)
    (hbκ : b < κ / 2) (hτ : τ < 0) (hu : u ≠ 0) (hσ : 0 < σ) (hR : 0 < R)
    (hg : g ≤ 0) (hD : D ≤ (κ / 2 - b) * (-τ) / 2)
    (hface : ∀ t ∈ Ioc (0 : ℝ) 1, t * ‖u‖ ≤ σ → projectedRay C x u t ∈ F)
    (hTaylor : ∀ t ∈ Ioc (0 : ℝ) 1, t * ‖u‖ ≤ 1 → t * ‖u‖ ≤ σ →
      m (projectedRay C x u t) ≤
        m x + t * g + (κ / 2 * τ + D) * (t * ‖u‖) ^ 2 + R * (t * ‖u‖) ^ 3) :
    ∃ j, ProjectedEigenTrialAccepted C F m x u q b τ j ∧
      (∀ i < j, ¬ ProjectedEigenTrialAccepted C F m x u q b τ i) ∧
      b * (q * min 1 ((κ / 2 - b) / (2 * R))) ^ 2 * (-τ) *
        min (‖u‖ ^ 2) (min 1 (min (σ ^ 2) (τ ^ 2))) ≤
          m x - m (projectedRay C x u (Chapter06.eigenTrialTime q j)) := by
  let U := ‖u‖
  let d := (κ / 2 - b) / (2 * R)
  have hU : 0 < U := norm_pos_iff.mpr hu
  have hτ' : 0 < -τ := neg_pos.mpr hτ
  have hd : 0 < d := div_pos (sub_pos.mpr hbκ) (by positivity)
  let a := min 1 (min σ (d * (-τ)))
  have ha : 0 < a := lt_min zero_lt_one (lt_min hσ (mul_pos hd hτ'))
  have haccept (j : ℕ) (hj : Chapter06.eigenTrialTime q j * U ≤ a) :
      ProjectedEigenTrialAccepted C F m x u q b τ j := by
    let t := Chapter06.eigenTrialTime q j
    have ht : t ∈ Ioc (0 : ℝ) 1 := ⟨pow_pos hq j, pow_le_one₀ hq.le hq'.le⟩
    have ht₁ : t * U ≤ 1 := hj.trans (min_le_left _ _)
    have htσ : t * U ≤ σ := hj.trans ((min_le_right _ _).trans (min_le_left _ _))
    have htD : R * (t * U) ≤ (κ / 2 - b) * (-τ) / 2 := by
      have hh : t * U ≤ d * (-τ) := hj.trans ((min_le_right _ _).trans (min_le_right _ _))
      have hh' := mul_le_mul_of_nonneg_left hh hR.le
      have he : R * (d * (-τ)) = (κ / 2 - b) * (-τ) / 2 := by
        dsimp [d]
        field_simp
      exact hh'.trans_eq he
    refine ⟨hface t ht htσ, (hTaylor t ht ht₁ htσ).trans ?_⟩
    have hlin := mul_nonpos_of_nonneg_of_nonpos ht.1.le hg
    have hquad := mul_le_mul_of_nonneg_right hD (sq_nonneg (t * U))
    have hcubic := mul_le_mul_of_nonneg_right htD (sq_nonneg (t * U))
    change m x + t * g + (κ / 2 * τ + D) * (t * U) ^ 2 + R * (t * U) ^ 3 ≤
      m x + b * τ * (t * U) ^ 2
    nlinarith only [hlin, hquad, hcubic]
  obtain ⟨j, hj, hfirst, hlength⟩ :=
    Chapter06.exists_first_eigenTrial_of_small_length hq hq' ha haccept
  refine ⟨j, hj, hfirst, ?_⟩
  let w := min 1 d
  let v := min U (min 1 (min σ (-τ)))
  have hw : 0 < w := lt_min zero_lt_one hd
  have hv : 0 < v := lt_min hU (lt_min zero_lt_one (lt_min hσ hτ'))
  have hva : w * v ≤ a := by
    have hbound := mul_le_of_le_one_left hv.le (show w ≤ 1 from min_le_left _ _)
    refine le_min (hbound.trans ((min_le_right _ _).trans (min_le_left _ _))) (le_min ?_ ?_)
    · exact hbound.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    · exact mul_le_mul (show w ≤ d from min_le_right _ _)
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) hv.le hd.le
  have hqv : q * w * v ≤ min U (q * a) := by
    refine le_min ?_ ?_
    · have hqw : q * w ≤ 1 :=
        (mul_le_of_le_one_right hq.le (min_le_left _ _)).trans hq'.le
      exact (mul_le_of_le_one_left hv.le hqw).trans (min_le_left _ _)
    · rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hva hq.le
  have hsquare := pow_le_pow_left₀ (mul_nonneg (mul_nonneg hq.le hw.le) hv.le)
    (hqv.trans hlength) 2
  have hv2 : v ^ 2 = min (U ^ 2) (min 1 (min (σ ^ 2) (τ ^ 2))) := by
    dsimp [v]
    rw [sq_min_eq_min_sq hU.le (le_min zero_le_one (le_min hσ.le hτ'.le)),
      sq_min_eq_min_sq zero_le_one (le_min hσ.le hτ'.le), sq_min_eq_min_sq hσ.le hτ'.le]
    simp
  rw [mul_pow, hv2] at hsquare
  have hp := mul_le_mul_of_nonneg_left hsquare (mul_nonneg hb.le hτ'.le)
  have hmodel := hj.2
  change m (projectedRay C x u (Chapter06.eigenTrialTime q j)) ≤
    m x + b * τ * (Chapter06.eigenTrialTime q j * U) ^ 2 at hmodel
  change b * (q * w) ^ 2 * (-τ) * min (U ^ 2) (min 1 (min (σ ^ 2) (τ ^ 2))) ≤ _
  linarith only [hp, hmodel]

/-- The minus sign in the printed acceptance inequality (12.4.14) can
accept a strict model increase at the initial trial, even for a smooth
model with unit negative curvature and zero slope at the base point. -/
theorem eigenTrial_printed_sign_counterexample :
    ∃ m : ℝ → ℝ, ContDiff ℝ 2 m ∧ deriv m 0 = 0 ∧ iteratedDeriv 2 m 0 = -1 ∧
      m 1 ≤ m 0 - (1 / 4 : ℝ) * (-1) ∧ m 0 < m 1 := by
  let m (t : ℝ) := -(1 / 2 : ℝ) * t ^ 2 + (3 / 4 : ℝ) * t ^ 3
  have hderiv (t : ℝ) : deriv m t = -t + (9 / 4 : ℝ) * t ^ 2 := by
    have h := ((((hasDerivAt_id t).fun_pow 2).const_mul (-(1 / 2 : ℝ))).fun_add
      (((hasDerivAt_id t).fun_pow 3).const_mul (3 / 4 : ℝ))).deriv
    exact h.trans (by dsimp; ring)
  have hm : ContDiff ℝ 2 m := (contDiff_const.mul (contDiff_id.pow 2)).add
    (contDiff_const.mul (contDiff_id.pow 3))
  refine ⟨m, hm, ?_, ?_, ?_, ?_⟩
  · norm_num [hderiv]
  · rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one, funext hderiv]
    have h := ((hasDerivAt_id (0 : ℝ)).fun_neg.fun_add
      (((hasDerivAt_id (0 : ℝ)).fun_pow 2).const_mul (9 / 4 : ℝ))).deriv
    simpa using h
  · norm_num [m]
  · norm_num [m]

end ConnGouldToint.Chapter12
