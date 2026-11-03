import NumlibSurface.ConnGouldToint.Chapter11.Section01
import Numlib.Optimization.ModelBased.RatioTest
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Normalized model error and the success ratio

[conn2000trust], Section 11.2. Compactness of the parameter set does not upgrade
pointwise limits to uniform estimates without additional control. The corrected
uniformity lemma uses equicontinuity of the normalized errors.
-/

open Filter Metric Optimization
open scoped Topology NNReal RealInnerProductSpace

namespace ConnGouldToint.Chapter11

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The normalized model error (11.2.2). -/
noncomputable def normalizedModelError (f : E → ℝ) (m : E → P → E → ℝ)
    (x : E) (p : P) (s : E) : ℝ :=
  (f (x + s) - m x p s) / ‖s‖

private theorem tendsto_normalized_of_rays [FiniteDimensional ℝ E] {G : E → ℝ}
    {S : Set E} {L : NNReal} (hS : S ∈ 𝓝 (0 : E)) (hL : LipschitzOnWith L G S)
    (hdir : ∀ d ∈ sphere (0 : E) 1,
      Tendsto (fun t : ℝ ↦ G (t • d) / t) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun s ↦ G s / ‖s‖) (𝓝 0) (𝓝 0) := by
  have := FiniteDimensional.proper_real E
  rw [Metric.tendsto_nhds]
  intro ε hε
  let r := ε / (4 * ((L : ℝ) + 1))
  have hr : 0 < r := div_pos hε (by positivity)
  have hrL : (L : ℝ) * r ≤ ε / 4 := by
    have he : r * (4 * ((L : ℝ) + 1)) = ε := div_mul_cancel₀ _ (by positivity)
    linarith
  have he (d : E) (hd : d ∈ sphere (0 : E) 1) :
      ∀ᶠ z : ℝ × E in 𝓝 ((0 : ℝ), d), 0 < z.1 → |G (z.1 • z.2) / z.1| ≤ ε / 2 := by
    have ht : Tendsto Prod.fst (𝓝 ((0 : ℝ), d)) (𝓝 (0 : ℝ)) := continuous_fst.tendsto _
    have hv : Tendsto Prod.snd (𝓝 ((0 : ℝ), d)) (𝓝 d) := continuous_snd.tendsto _
    have hsd : Tendsto (fun z : ℝ × E ↦ z.1 • z.2) (𝓝 ((0 : ℝ), d)) (𝓝 (0 : E)) := by
      simpa only [zero_smul] using ht.smul hv
    have hs0 : Tendsto (fun z : ℝ × E ↦ z.1 • d) (𝓝 ((0 : ℝ), d)) (𝓝 (0 : E)) := by
      simpa only [zero_smul] using ht.smul (tendsto_const_nhds (x := d))
    have hpoint : ∀ᶠ t : ℝ in 𝓝 0, 0 < t → |G (t • d) / t| < ε / 4 := by
      have he' : ∀ᶠ t : ℝ in 𝓝[>] 0, |G (t • d) / t| < ε / 4 := by
        simpa only [Real.dist_eq, sub_zero] using
          Metric.tendsto_nhds.mp (hdir d hd) (ε / 4) (by positivity)
      exact eventually_nhdsWithin_iff.mp he'
    filter_upwards [hsd.eventually hS, hs0.eventually hS,
      hv.eventually (ball_mem_nhds d hr), ht.eventually hpoint] with z hz hz₀ hzd hzpoint
    intro hzpos
    have hdiff := hL.dist_le_mul _ hz _ hz₀
    rw [Real.dist_eq, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos hzpos] at hdiff
    have hdiv : |G (z.1 • z.2) / z.1 - G (z.1 • d) / z.1| ≤ (L : ℝ) * ‖z.2 - d‖ := by
      rw [← sub_div, abs_div, abs_of_pos hzpos]
      apply (div_le_iff₀ hzpos).mpr
      convert hdiff using 1
      ring
    have hnorm : ‖z.2 - d‖ ≤ r := by simpa [mem_ball, dist_eq_norm] using hzd.le
    have hfirst := hdiv.trans ((mul_le_mul_of_nonneg_left hnorm L.coe_nonneg).trans hrL)
    have htri := abs_sub_le (G (z.1 • z.2) / z.1) (G (z.1 • d) / z.1) 0
    simp only [sub_zero] at htri
    linarith [hzpoint hzpos]
  have hu := (isCompact_sphere (0 : E) 1).eventually_forall_of_forall_eventually
    (P := fun (t : ℝ) (d : E) ↦ 0 < t → |G (t • d) / t| ≤ ε / 2) he
  filter_upwards [(show Tendsto (fun s : E ↦ ‖s‖) (𝓝 0) (𝓝 0) by
      simpa only [norm_zero] using continuous_norm.tendsto (0 : E)).eventually hu] with s hs
  rw [Real.dist_eq, sub_zero]
  by_cases hs₀ : s = 0
  · simpa [hs₀] using hε
  let d := ‖s‖⁻¹ • s
  have hp := norm_pos_iff.mpr hs₀
  have hd : d ∈ sphere (0 : E) 1 := by
    rw [mem_sphere, dist_zero_right]
    simp [d, norm_smul, hp.ne']
  have hs' := hs d hd hp
  have heq : ‖s‖ • d = s := by simp [d, smul_smul, hp.ne']
  rw [heq] at hs'
  exact hs'.trans_lt (by linarith)

/-- Lemma 11.2.1 at a fixed base point and parameter. Regularity is expressed
by the positive-ray limits. Nontriviality excludes the zero-dimensional
case, where the normalized quotient does not detect value agreement. -/
theorem lemma_11_2_1 [FiniteDimensional ℝ E] [Nontrivial E] {f : E → ℝ}
    {m : E → P → E → ℝ} {x : E} {p : P} {U V : Set E} {Lf Lm : NNReal}
    (hU : U ∈ 𝓝 x) (hLf : LipschitzOnWith Lf f U)
    (hV : V ∈ 𝓝 (0 : E)) (hLm : LipschitzOnWith Lm (m x p) V)
    (hf : ∀ d : E, Tendsto (fun t : ℝ ↦ (f (x + t • d) - f x) / t)
      (𝓝[>] 0) (𝓝 (clarkeDerivative f x d)))
    (hm : ∀ d : E, Tendsto (fun t : ℝ ↦ (m x p (t • d) - m x p 0) / t)
      (𝓝[>] 0) (𝓝 (clarkeDerivative (m x p) 0 d))) :
    (m x p 0 = f x ∧ ∀ d : E, d ≠ 0 →
      clarkeDerivative (m x p) 0 d = clarkeDerivative f x d) ↔
      Tendsto (normalizedModelError f m x p) (𝓝 0) (𝓝 0) := by
  let G (s : E) := f (x + s) - m x p s
  let S := (fun s : E ↦ x + s) ⁻¹' U ∩ V
  have hxadd : Tendsto (fun s : E ↦ x + s) (𝓝 0) (𝓝 x) :=
    (continuous_const.add continuous_id).tendsto' _ _ (add_zero x)
  have hS : S ∈ 𝓝 (0 : E) := (hxadd.eventually hU).and hV
  have hG : LipschitzOnWith (Lf + Lm) G S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    have hfa := hLf.dist_le_mul _ ha.1 _ hb.1
    change dist (f (x + a)) (f (x + b)) ≤ (Lf : ℝ) * dist (x + a) (x + b) at hfa
    rw [dist_eq_norm (x + a) (x + b), add_sub_add_left_eq_sub, ← dist_eq_norm] at hfa
    have hma := hLm.dist_le_mul _ ha.2 _ hb.2
    rw [Real.dist_eq] at hfa hma ⊢
    change |f (x + a) - m x p a - (f (x + b) - m x p b)| ≤ _
    calc
      _ = |(f (x + a) - f (x + b)) + (m x p b - m x p a)| := by congr 1; ring
      _ ≤ |f (x + a) - f (x + b)| + |m x p b - m x p a| := abs_add_le _ _
      _ ≤ _ := by rw [abs_sub_comm (m x p b), NNReal.coe_add, add_mul]; exact add_le_add hfa hma
  constructor
  · rintro ⟨he, hd⟩
    apply tendsto_normalized_of_rays hS hG
    intro d hd'
    have hne : d ≠ 0 := by
      intro hh
      simp [hh] at hd'
    have h := (hf d).sub (hm d)
    rw [hd d hne, sub_self] at h
    convert h using 1
    funext t
    dsimp [G]
    rw [← sub_div, he]
    congr 1
    ring
  · intro hθ
    have hray (d : E) : Tendsto (fun t : ℝ ↦ t • d) (𝓝[>] 0) (𝓝 (0 : E)) := by
      have hc : Continuous (fun t : ℝ ↦ t • d) := continuous_id.smul continuous_const
      simpa only [zero_smul] using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have herror (d : E) : Tendsto (fun t : ℝ ↦ normalizedModelError f m x p (t • d))
        (𝓝[>] 0) (𝓝 0) := hθ.comp (hray d)
    obtain ⟨d, hd⟩ := exists_ne (0 : E)
    have hθnorm := (herror d).mul ((continuous_norm.tendsto (0 : E)).comp (hray d))
    simp only [norm_zero, mul_zero] at hθnorm
    have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
    have hGzero : Tendsto (fun t : ℝ ↦ G (t • d)) (𝓝[>] 0) (𝓝 0) := by
      apply hθnorm.congr'
      filter_upwards [hpos] with t ht
      exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (smul_ne_zero ht.ne' hd))
    have hc : ContinuousAt G 0 := (hG.continuousOn 0 (mem_of_mem_nhds hS)).continuousAt hS
    have hval := tendsto_nhds_unique (hc.tendsto.comp (hray d)) hGzero
    have hval' : m x p 0 = f x := by
      simpa only [G, add_zero, sub_eq_zero, eq_comm] using hval
    refine ⟨hval', fun e he ↦ ?_⟩
    have ht := (herror e).mul_const ‖e‖
    rw [zero_mul] at ht
    have hq : Tendsto (fun t : ℝ ↦ G (t • e) / t) (𝓝[>] 0) (𝓝 0) := by
      apply ht.congr'
      filter_upwards [hpos] with t ht
      rw [normalizedModelError, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      dsimp [G]
      field_simp [ht.ne', norm_ne_zero_iff.mpr he]
    have hh : Tendsto (fun t : ℝ ↦ G (t • e) / t) (𝓝[>] 0)
        (𝓝 (clarkeDerivative f x e - clarkeDerivative (m x p) 0 e)) := by
      convert (hf e).sub (hm e) using 1
      funext t
      dsimp [G]
      rw [← sub_div, hval']
      congr 1
      ring
    exact (sub_eq_zero.mp (tendsto_nhds_unique hh hq)).symm

/-- The normalized model error tends to zero uniformly in the base point near
`x` and in all admissible parameters. -/
def UniformNormalizedModelAgreementAt (f : E → ℝ) (m : E → P → E → ℝ) (x : E) : Prop :=
  ∀ a : ℝ, 0 < a → ∃ ε Δ : ℝ, 0 < ε ∧ 0 < Δ ∧
    ∀ y ∈ ball x ε, ∀ (p : P) (s : E), ‖s‖ ≤ Δ → |normalizedModelError f m y p s| ≤ a

/-- Equicontinuity in the base point and parameter for the family of normalized
errors indexed by small steps. -/
def ModelErrorEquicontinuousAt [TopologicalSpace P] (f : E → ℝ)
    (m : E → P → E → ℝ) (x : E) (p : P) : Prop :=
  ∀ a : ℝ, 0 < a → ∀ᶠ z : E × P in 𝓝 (x, p),
    ∀ s : E, ‖s‖ ≤ 1 → |normalizedModelError f m z.1 z.2 s -
      normalizedModelError f m x p s| ≤ a

omit [InnerProductSpace ℝ E] in
/-- Corrected Lemma 11.2.2. Pointwise agreement at the reference base point
becomes uniform under equicontinuity of the normalized errors and compactness
of the admissible parameter space. -/
theorem lemma_11_2_2 [TopologicalSpace P] [CompactSpace P] {f : E → ℝ}
    {m : E → P → E → ℝ} {x : E}
    (hpoint : ∀ p, Tendsto (normalizedModelError f m x p) (𝓝 0) (𝓝 0))
    (hequi : ∀ p, ModelErrorEquicontinuousAt f m x p) :
    UniformNormalizedModelAgreementAt f m x := by
  intro a ha
  have he (p : P) : ∀ᶠ z : (E × E) × P in 𝓝 ((x, (0 : E)), p),
      |normalizedModelError f m z.1.1 z.2 z.1.2| ≤ a := by
    have hbase : Tendsto (fun z : (E × E) × P ↦ (z.1.1, z.2))
        (𝓝 ((x, (0 : E)), p)) (𝓝 (x, p)) :=
      (continuous_fst.comp continuous_fst).tendsto' _ _ rfl |>.prodMk_nhds
        (continuous_snd.tendsto' _ _ rfl)
    have hstep : Tendsto (fun z : (E × E) × P ↦ z.1.2)
        (𝓝 ((x, (0 : E)), p)) (𝓝 0) :=
      (continuous_snd.comp continuous_fst).tendsto' _ _ rfl
    have hsmall := (Metric.tendsto_nhds.mp (hpoint p) (a / 2) (half_pos ha)).mono
      fun s hs ↦ (show |normalizedModelError f m x p s| < a / 2 by
        simpa only [Real.dist_eq, sub_zero] using hs).le
    have hstepOne : ∀ᶠ z : (E × E) × P in 𝓝 ((x, (0 : E)), p), ‖z.1.2‖ ≤ 1 :=
      hstep.eventually (Filter.mem_of_superset (Metric.ball_mem_nhds _ zero_lt_one) fun s hs ↦
        (mem_ball_zero_iff.mp hs).le)
    filter_upwards [hbase.eventually (hequi p (a / 2) (half_pos ha)),
      hstep.eventually hsmall, hstepOne] with z hz hs hnorm
    have hsum := add_le_add (hz z.1.2 hnorm) hs
    have htriangle := abs_sub_le (normalizedModelError f m z.1.1 z.2 z.1.2)
      (normalizedModelError f m x p z.1.2) 0
    simp only [sub_zero] at htriangle
    linarith
  have hu : ∀ᶠ z : E × E in 𝓝 (x, (0 : E)), ∀ p : P,
      |normalizedModelError f m z.1 p z.2| ≤ a := by
    have hK : IsCompact (Set.univ : Set P) := isCompact_univ
    simpa using hK.eventually_forall_of_forall_eventually (fun p _ ↦ he p)
  rw [nhds_prod_eq] at hu
  obtain ⟨A, hA, B, hB, hab⟩ := eventually_prod_iff.mp hu
  obtain ⟨ε, hε, hεA⟩ := Metric.mem_nhds_iff.mp hA
  obtain ⟨r, hr, hrB⟩ := Metric.mem_nhds_iff.mp hB
  refine ⟨ε, r / 2, hε, half_pos hr, fun y hy p s hs ↦ ?_⟩
  apply hab (hεA hy) (hrB ?_) p
  exact mem_ball_zero_iff.mpr (hs.trans_lt (half_lt_self hr))

/-- Corrected Lemma 11.2.3. Uniform model agreement, together with sufficient
model decrease and a nonstationary reference point, forces acceptance for every
sufficiently small radius. -/
theorem lemma_11_2_3 [CompleteSpace E] {f : E → ℝ} {m : E → P → E → ℝ}
    {x : E} {U : Set E} {L : NNReal} (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U)
    (hx : (0 : E) ∉ clarkeSubgradient f x) (hmatch : modelValueMatches f m)
    (herr : UniformNormalizedModelAgreementAt f m x) {η κ δ : ℝ}
    (hη : η < 1) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ ε Δmax : ℝ, 0 < ε ∧ 0 < Δmax ∧
      ∀ y ∈ ball x ε, ∀ (p : P) (Δ : ℝ), 0 < Δ → Δ < Δmax →
      ∀ s : E, ‖s‖ ≤ Δ →
      κ * ‖minimumNormSubgradient f y‖ * min δ Δ ≤ m y p 0 - m y p s →
      η ≤ reductionRatio f y s (m y p 0 - m y p s) := by
  obtain ⟨ε₀, γ, hε₀, hγ, hgrad⟩ := lemma_11_1_2 hU hL hx
  let a := (1 - η) * (κ * γ)
  have ha : 0 < a := mul_pos (sub_pos.mpr hη) (mul_pos hκ hγ)
  obtain ⟨ε₁, Δ₁, hε₁, hΔ₁, herror⟩ := herr a ha
  refine ⟨min ε₀ ε₁, min δ Δ₁, lt_min hε₀ hε₁, lt_min hδ hΔ₁, ?_⟩
  intro y hy p Δ hΔ hΔmax s hs hdec
  have hy₀ := ball_subset_ball (min_le_left ε₀ ε₁) hy
  have hy₁ := ball_subset_ball (min_le_right ε₀ ε₁) hy
  have hΔδ := hΔmax.le.trans (min_le_left δ Δ₁)
  have hΔ₁' := hΔmax.le.trans (min_le_right δ Δ₁)
  let pred := m y p 0 - m y p s
  have hpred : κ * γ * Δ ≤ pred := by
    rw [min_eq_right hΔδ] at hdec
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hgrad y hy₀) hκ.le) hΔ.le).trans hdec
  have hpredpos : 0 < pred := (mul_pos (mul_pos hκ hγ) hΔ).trans_le hpred
  have hs₀ : s ≠ 0 := by
    intro he
    simp [pred, he] at hpredpos
  have hθ := (le_abs_self _).trans (herror y hy₁ p s (hs.trans hΔ₁'))
  have herr' : f (y + s) - m y p s ≤ (1 - η) * pred := by
    calc
      f (y + s) - m y p s ≤ a * ‖s‖ := (div_le_iff₀ (norm_pos_iff.mpr hs₀)).mp hθ
      _ ≤ a * Δ := mul_le_mul_of_nonneg_left hs ha.le
      _ = (1 - η) * (κ * γ * Δ) := by ring
      _ ≤ (1 - η) * pred := mul_le_mul_of_nonneg_left hpred (sub_nonneg.mpr hη.le)
  apply (le_reductionRatio_iff hpredpos).2
  rw [← hmatch y p]
  dsimp [pred] at herr' ⊢
  linarith

private theorem NonsmoothTRParams.gamma₁_pos (Q : NonsmoothTRParams) : 0 < Q.γ₁ :=
  (one_div_pos.mpr (zero_lt_one.trans Q.gamma₃_gt_one)).trans_le Q.inv_gamma₃_le_gamma₁

omit [InnerProductSpace ℝ E] in
private theorem NonsmoothTRRun.radius_bounds {Q : NonsmoothTRParams}
    {f : E → ℝ} {m : E → P → E → ℝ} (R : NonsmoothTRRun Q f m) :
    ∀ k, 0 < R.Δ k ∧ R.Δ k ≤ Q.Δmax ∧ Q.γ₁ * R.Δ k ≤ R.Δ (k + 1) := by
  have hstep (k : ℕ) (hpos : 0 < R.Δ k) (hmax : R.Δ k ≤ Q.Δmax) :
      Q.γ₁ * R.Δ k ≤ R.Δ (k + 1) ∧ R.Δ (k + 1) ≤ Q.Δmax := by
    have h := R.next_radius k
    have hγ₁ : Q.γ₁ ≤ 1 := (Q.gamma₁_le_gamma₂.trans Q.gamma₂_lt_one.le)
    have hγ₂ : Q.γ₂ ≤ 1 := Q.gamma₂_lt_one.le
    by_cases h₂ : Q.η₂ ≤ R.ratio k
    · obtain ⟨hlo, hhi⟩ := h.very_successful h₂
      refine ⟨(le_min ?_ ?_).trans hlo, hhi⟩
      · exact mul_le_mul_of_nonneg_right (hγ₁.trans Q.gamma₃_gt_one.le) hpos.le
      · exact (mul_le_of_le_one_left hpos.le hγ₁).trans hmax
    by_cases h₁ : Q.η₁ ≤ R.ratio k
    · obtain ⟨hlo, hhi⟩ := h.successful h₁ (lt_of_not_ge h₂)
      exact ⟨(mul_le_mul_of_nonneg_right Q.gamma₁_le_gamma₂ hpos.le).trans hlo, hhi.trans hmax⟩
    · obtain ⟨hlo, hhi⟩ := h.unsuccessful (lt_of_not_ge h₁)
      exact ⟨hlo, hhi.trans ((mul_le_of_le_one_left hpos.le hγ₂).trans hmax)⟩
  intro k
  induction k with
  | zero =>
    exact ⟨R.radius_initial_pos, R.radius_initial_le,
      (hstep 0 R.radius_initial_pos R.radius_initial_le).1⟩
  | succ k ih =>
    have hpos := (mul_pos Q.gamma₁_pos ih.1).trans_le ih.2.2
    have hmax := (hstep k ih.1 ih.2.1).2
    exact ⟨hpos, hmax, (hstep (k + 1) hpos hmax).1⟩

omit [InnerProductSpace ℝ E] in
private theorem NonsmoothTRRun.next_x_eq_ite {Q : NonsmoothTRParams}
    {f : E → ℝ} {m : E → P → E → ℝ} (R : NonsmoothTRRun Q f m) (k : ℕ) :
    R.x (k + 1) = if Q.η₁ ≤ R.ratio k then R.x k + R.s k else R.x k :=
  R.next_x k

omit [InnerProductSpace ℝ E] in
private theorem NonsmoothTRRun.dist_next_le_radius {Q : NonsmoothTRParams}
    {f : E → ℝ} {m : E → P → E → ℝ} (R : NonsmoothTRRun Q f m) (k : ℕ) :
    dist (R.x k) (R.x (k + 1)) ≤ R.Δ k := by
  rw [R.next_x_eq_ite]
  by_cases h : Q.η₁ ≤ R.ratio k
  · rw [ite_eq_left h, dist_comm, dist_eq_norm, add_sub_cancel_left]
    exact R.step_bound k
  · rw [ite_eq_right h, dist_self]
    exact (R.radius_bounds k).1.le

/-- Lemma 11.2.4. Around a nonstationary reference point, all visiting iterates
have a common positive lower radius bound. The proof propagates a small radius
backwards using a distance-plus-radius bound and the very-successful expansion. -/
theorem lemma_11_2_4 [CompleteSpace E] {Q : NonsmoothTRParams} {f : E → ℝ}
    {m : E → P → E → ℝ} (R : NonsmoothTRRun Q f m) {x : E} {U : Set E} {L : NNReal}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U)
    (hx : (0 : E) ∉ clarkeSubgradient f x) (hmatch : modelValueMatches f m)
    (herr : UniformNormalizedModelAgreementAt f m x) (hAA : R.HasLocalSufficientDecrease x) :
    ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧ ∀ k, R.x k ∈ ball x ε → r ≤ R.Δ k := by
  obtain ⟨ε₀, δ, κ, hε₀, hδ, hκ, _, hdec⟩ := hAA
  obtain ⟨ε₁, T₁, hε₁, hT₁, hη⟩ := lemma_11_2_3 hU hL hx hmatch herr Q.eta₂_lt_one hκ hδ
  let ε := min ε₀ ε₁
  let T := min T₁ (Q.Δmax / Q.γ₃)
  have hε : 0 < ε := lt_min hε₀ hε₁
  have hγ₃ := zero_lt_one.trans Q.gamma₃_gt_one
  have hT : 0 < T := lt_min hT₁ (div_pos Q.radiusMax_pos hγ₃)
  let C := max (1 / Q.γ₁) (1 / (Q.γ₃ - 1))
  have hC₁ : 1 / Q.γ₁ ≤ C := le_max_left _ _
  have hC₂ : 1 / (Q.γ₃ - 1) ≤ C := le_max_right _ _
  have hC : 0 < C := (one_div_pos.mpr Q.gamma₁_pos).trans_le hC₁
  have hCexp : C + 1 ≤ C * Q.γ₃ := by
    have h := (div_le_iff₀ (sub_pos.mpr Q.gamma₃_gt_one)).1 hC₂
    linarith only [h]
  let D := min (R.Δ 0) (Q.γ₁ * T)
  have hD : 0 < D := lt_min R.radius_initial_pos (mul_pos Q.gamma₁_pos hT)
  let bad (k : ℕ) := R.Δ k < D ∧ dist (R.x k) x + C * R.Δ k < ε
  have hback (k : ℕ) (hn : bad (k + 1)) : bad k := by
    have hΔpos := (R.radius_bounds k).1
    have hΔnextpos := (R.radius_bounds (k + 1)).1
    have hΔnext := (R.radius_bounds k).2.2
    have hsmall : R.Δ k < T := lt_of_mul_lt_mul_left
      (hΔnext.trans_lt (hn.1.trans_le (min_le_right _ _))) Q.gamma₁_pos.le
    have hpre : R.Δ k ≤ C * R.Δ (k + 1) := by
      calc
        R.Δ k ≤ R.Δ (k + 1) / Q.γ₁ := (le_div_iff₀ Q.gamma₁_pos).2
          (by simpa only [mul_comm] using hΔnext)
        _ = (1 / Q.γ₁) * R.Δ (k + 1) := by ring
        _ ≤ C * R.Δ (k + 1) := mul_le_mul_of_nonneg_right hC₁ hΔnextpos.le
    have hdist := (dist_triangle (R.x k) (R.x (k + 1)) x).trans
      (add_le_add (R.dist_next_le_radius k) le_rfl)
    have hnear : R.x k ∈ ball x ε := by
      rw [mem_ball]
      linarith only [hdist, hpre, hn.2]
    have hρ := hη (R.x k) (ball_subset_ball (min_le_right _ _) hnear)
      (R.parameter k) (R.Δ k) hΔpos (hsmall.trans_le (min_le_left _ _))
      (R.s k) (R.step_bound k) (hdec k (ball_subset_ball (min_le_left _ _) hnear))
    have hcap : Q.γ₃ * R.Δ k ≤ Q.Δmax := by
      have h := (le_div_iff₀ hγ₃).1 (hsmall.le.trans (min_le_right _ _))
      simpa only [mul_comm] using h
    have hexp := ((R.next_radius k).very_successful hρ).1
    rw [min_eq_left hcap] at hexp
    have hnondec : R.Δ k ≤ R.Δ (k + 1) :=
      (le_mul_of_one_le_left hΔpos.le Q.gamma₃_gt_one.le).trans hexp
    refine ⟨hnondec.trans_lt hn.1, ?_⟩
    have hbudget : (C + 1) * R.Δ k ≤ C * R.Δ (k + 1) := calc
      _ ≤ (C * Q.γ₃) * R.Δ k := mul_le_mul_of_nonneg_right hCexp hΔpos.le
      _ = C * (Q.γ₃ * R.Δ k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp hC.le
    linarith only [hdist, hbudget, hn.2]
  have hgood (k : ℕ) : ¬ bad k := by
    induction k with
    | zero => exact fun h ↦ not_lt_of_ge (min_le_left _ _) h.1
    | succ k ih => exact fun h ↦ ih (hback k h)
  let r := min D (ε / (2 * C))
  refine ⟨ε / 2, r, half_pos hε, lt_min hD (div_pos hε (by positivity)), ?_⟩
  intro k hk
  by_contra! hr
  have hdist := mem_ball.1 hk
  have hrD : R.Δ k < D := hr.trans_le (min_le_left _ _)
  have hrε := (lt_div_iff₀ (mul_pos (by norm_num : 0 < (2 : ℝ)) hC)).1
    (hr.trans_le (min_le_right _ _))
  exact hgood k ⟨hrD, by linarith only [hdist, hrε]⟩

private theorem NonsmoothTRRun.pred_nonneg {Q : NonsmoothTRParams}
    {f : E → ℝ} {m : E → P → E → ℝ} (R : NonsmoothTRRun Q f m)
    (hAA : ∀ x, R.HasLocalSufficientDecrease x) (k : ℕ) :
    0 ≤ R.pred k := by
  obtain ⟨ε, δ, κ, hε, hδ, hκ, _, hdec⟩ := hAA (R.x k)
  exact (mul_nonneg (mul_nonneg hκ.le (norm_nonneg _))
    (le_min hδ.le (R.radius_bounds k).1.le)).trans (hdec k (mem_ball_self hε))

private theorem NonsmoothTRRun.acceptedDecrease {Q : NonsmoothTRParams}
    {f : E → ℝ} {m : E → P → E → ℝ} (R : NonsmoothTRRun Q f m)
    (hAA : ∀ x, R.HasLocalSufficientDecrease x) {k : ℕ} (h : Q.η₁ ≤ R.ratio k) :
    Q.η₁ * R.pred k ≤ f (R.x k) - f (R.x (k + 1)) := by
  have hp : 0 < R.pred k := by
    refine lt_of_le_of_ne (R.pred_nonneg hAA k) (fun he ↦ ?_)
    have hz : R.ratio k = 0 := by simp [NonsmoothTRRun.ratio, reductionRatio, ← he]
    exact Q.eta₁_pos.not_ge (hz ▸ h)
  rw [R.next_x_eq_ite, ite_eq_left h]
  exact (le_reductionRatio_iff hp).1 h

private theorem NonsmoothTRRun.antitone_value {Q : NonsmoothTRParams}
    {f : E → ℝ} {m : E → P → E → ℝ} (R : NonsmoothTRRun Q f m)
    (hAA : ∀ x, R.HasLocalSufficientDecrease x) :
    Antitone (fun k ↦ f (R.x k)) := by
  apply antitone_nat_of_succ_le
  intro k
  by_cases h : Q.η₁ ≤ R.ratio k
  · exact sub_nonneg.1 ((mul_nonneg Q.eta₁_pos.le (R.pred_nonneg hAA k)).trans
      (R.acceptedDecrease hAA h))
  · rw [R.next_x_eq_ite, ite_eq_right h]

/-- Theorem 11.2.5 with the uniform normalized model agreement required
by corrected Lemma 11.2.3. Every limit point of a run is Clarke stationary.
If the run stopped accepting near a nonstationary limit point, rejection
would shrink the radius below the local lower bound. -/
theorem theorem_11_2_5 [CompleteSpace E] {Q : NonsmoothTRParams} {f : E → ℝ}
    {m : E → P → E → ℝ} (R : NonsmoothTRRun Q f m) {x : E} {U : Set E} {L : NNReal}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U)
    (hmatch : modelValueMatches f m) (herr : UniformNormalizedModelAgreementAt f m x)
    (hAA : ∀ y, R.HasLocalSufficientDecrease y)
    {j : ℕ → ℕ} (hj : StrictMono j) (hx : Tendsto (R.x ∘ j) atTop (𝓝 x)) :
    (0 : E) ∈ clarkeSubgradient f x := by
  by_contra hnoncrit
  obtain ⟨εr, r, hεr, hr, hrad⟩ := lemma_11_2_4 R hU hL hnoncrit hmatch herr (hAA x)
  obtain ⟨εg, γ, hεg, hγ, hgrad⟩ := lemma_11_1_2 hU hL hnoncrit
  obtain ⟨εa, δ, κ, hεa, hδ, hκ, _, hdec⟩ := hAA x
  let ε := min εr (min εg εa)
  have hε : 0 < ε := lt_min hεr (lt_min hεg hεa)
  have hεr' : ε ≤ εr := min_le_left _ _
  have hεg' : ε ≤ εg := (min_le_right _ _).trans (min_le_left _ _)
  have hεa' : ε ≤ εa := (min_le_right _ _).trans (min_le_right _ _)
  let d := κ * γ * min δ r
  have hd : 0 < d := mul_pos (mul_pos hκ hγ) (lt_min hδ hr)
  let a := Q.η₁ * d
  have ha : 0 < a := mul_pos Q.eta₁_pos hd
  have hvalue := R.antitone_value hAA
  have hfx : Tendsto (fun n ↦ f (R.x (j n))) atTop (𝓝 (f x)) :=
    (hL.continuousOn.continuousAt hU).tendsto.comp hx
  have hfloor (k : ℕ) : f x ≤ f (R.x k) := by
    apply le_of_tendsto hfx
    filter_upwards [hj.tendsto_atTop.eventually_ge_atTop k] with n hn
    exact hvalue hn
  obtain ⟨n₀, hn₀⟩ := (hfx.eventually_lt_const (lt_add_of_pos_right _ ha)).exists
  let K₀ := j n₀
  have hlate (k : ℕ) (hk : K₀ ≤ k) (hnear : R.x k ∈ ball x ε) : R.ratio k < Q.η₁ := by
    by_contra! h
    have hg := hgrad (R.x k) (ball_subset_ball hεg' hnear)
    have hΔ := hrad k (ball_subset_ball hεr' hnear)
    have hp : d ≤ R.pred k := by
      apply le_trans _ (hdec k (ball_subset_ball hεa' hnear))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hg hκ.le) (min_le_min le_rfl hΔ)
        (le_min hδ.le hr.le) (mul_nonneg hκ.le (norm_nonneg _))
    have hdrop := (mul_le_mul_of_nonneg_left hp Q.eta₁_pos.le).trans
      (R.acceptedDecrease hAA h)
    change a ≤ f (R.x k) - f (R.x (k + 1)) at hdrop
    have hupper := (hvalue hk).trans_lt hn₀
    linarith only [hdrop, hupper, hfloor (k + 1)]
  obtain ⟨n₁, hn₁, hnear⟩ :
      ∃ n, K₀ ≤ j n ∧ R.x (j n) ∈ ball x ε :=
    ((hj.tendsto_atTop.eventually_ge_atTop K₀).and (hx.eventually (ball_mem_nhds x hε))).exists
  let K := j n₁
  have hγ₂ : 0 ≤ Q.γ₂ := Q.gamma₁_pos.le.trans Q.gamma₁_le_gamma₂
  have htail (n : ℕ) :
      R.x (K + n) = R.x K ∧ R.Δ (K + n) ≤ Q.γ₂ ^ n * R.Δ K := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hk : K₀ ≤ K + n := hn₁.trans (Nat.le_add_right _ _)
      have hnear' : R.x (K + n) ∈ ball x ε := ih.1.symm ▸ hnear
      have hf := hlate (K + n) hk hnear'
      refine ⟨?_, ?_⟩
      · rw [← Nat.add_assoc, R.next_x_eq_ite, ite_eq_right hf.not_ge, ih.1]
      · calc
          R.Δ (K + (n + 1)) ≤ Q.γ₂ * R.Δ (K + n) := by
            rw [← Nat.add_assoc]
            exact ((R.next_radius (K + n)).unsuccessful hf).2
          _ ≤ Q.γ₂ * (Q.γ₂ ^ n * R.Δ K) := mul_le_mul_of_nonneg_left ih.2 hγ₂
          _ = Q.γ₂ ^ (n + 1) * R.Δ K := by ring
  have hpow : Tendsto (fun n : ℕ ↦ Q.γ₂ ^ n * R.Δ K) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hγ₂ Q.gamma₂_lt_one).mul_const (R.Δ K)
  obtain ⟨n, hn⟩ := (hpow.eventually_lt_const hr).exists
  have hnear' : R.x (K + n) ∈ ball x ε := (htail n).1.symm ▸ hnear
  exact (not_lt_of_ge (hrad _ (ball_subset_ball hεr' hnear'))) ((htail n).2.trans_lt hn)

/-! ### A compact-parameter counterexample -/

/-- The compact parameter set for the model-error counterexample. -/
abbrev CompactModelParameter := Set.Icc (0 : ℝ) 1

/-- The smooth model perturbation has amplitude at most the parameter, while
its frequency grows as the parameter tends to zero. -/
noncomputable def compactPerturbedModel (x : ℝ) (p : CompactModelParameter) (s : ℝ) : ℝ :=
  oscillatoryObjective (x + s) - p.val * Real.sin (s / p.val) ^ 2

private theorem compactPerturbedModel_error (x : ℝ) (p : CompactModelParameter) (s : ℝ) :
    normalizedModelError oscillatoryObjective compactPerturbedModel x p s =
      p.val * Real.sin (s / p.val) ^ 2 / ‖s‖ := by
  unfold normalizedModelError compactPerturbedModel
  congr 1
  ring

private theorem continuous_perturbation_parameter (s : ℝ) :
    Continuous (fun p : ℝ ↦ p * Real.sin (s / p) ^ 2) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p = 0
  · subst p
    change Tendsto (fun p : ℝ ↦ p * Real.sin (s / p) ^ 2) (𝓝 0)
      (𝓝 (0 * Real.sin (s / 0) ^ 2))
    simp only [zero_mul]
    apply tendsto_iff_dist_tendsto_zero.mpr
    refine squeeze_zero (g := fun q : ℝ ↦ |q|) (fun _ ↦ dist_nonneg) (fun q ↦ ?_) ?_
    · rw [Real.dist_eq, sub_zero, abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg q)
        (pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one _))
    · simpa using continuous_abs.tendsto (0 : ℝ)
  · exact continuousAt_id.mul ((Real.continuous_sin.continuousAt.comp
      (continuousAt_const.div continuousAt_id hp)).pow 2)

/-- The counterexample satisfies the matching conditions and the model's
pointwise smoothness and parameter continuity assumptions. -/
theorem compactPerturbedModel_matches :
    CompactSpace CompactModelParameter ∧
    (∀ x p, ContDiff ℝ ⊤ (compactPerturbedModel x p)) ∧
    (∀ s, Continuous (fun xp : ℝ × CompactModelParameter ↦ compactPerturbedModel xp.1 xp.2 s)) ∧
    modelValueMatches oscillatoryObjective compactPerturbedModel ∧
    modelDerivativeMatches oscillatoryObjective compactPerturbedModel := by
  refine ⟨isCompact_iff_compactSpace.mp isCompact_Icc, ?_, ?_, ?_, ?_⟩
  · intro x p
    unfold compactPerturbedModel oscillatoryObjective
    fun_prop
  · intro s
    unfold compactPerturbedModel oscillatoryObjective
    have hp := (continuous_perturbation_parameter s).comp
      (continuous_subtype_val.comp (continuous_snd (X := ℝ) (Y := CompactModelParameter)))
    fun_prop
  · intro x p
    simp [compactPerturbedModel]
  · intro x p d _
    have hf (z : ℝ) : HasStrictDerivAt oscillatoryObjective (2 * z - 1) z := by
      unfold oscillatoryObjective
      convert (hasStrictDerivAt_pow 2 z).sub (hasStrictDerivAt_id z) using 1
      · rfl
      · ring
    have hx : HasStrictDerivAt (fun s : ℝ ↦ x + s) 1 0 :=
      (hasStrictDerivAt_id (0 : ℝ)).const_add x
    have hm : HasStrictDerivAt (fun s : ℝ ↦ oscillatoryObjective (x + s)) (2 * x - 1) 0 := by
      simpa only [Function.comp_def, add_zero, mul_one] using (hf (x + 0)).comp 0 hx
    have hpert : HasStrictDerivAt (fun s : ℝ ↦ p.val * Real.sin (s / p.val) ^ 2) 0 0 := by
      simpa using ((((hasStrictDerivAt_id (0 : ℝ)).div_const p.val).sin).pow 2).const_mul p.val
    have hm' : HasStrictDerivAt (compactPerturbedModel x p) (2 * x - 1) 0 := by
      unfold compactPerturbedModel
      rw [← sub_zero (2 * x - 1)]
      exact hm.fun_sub hpert
    rw [clarkeDerivative_eq_of_hasStrictFDerivAt hm'.hasStrictFDerivAt,
      clarkeDerivative_eq_of_hasStrictFDerivAt (hf x).hasStrictFDerivAt]

/-- For each fixed parameter the normalized model error converges to zero. -/
theorem compactPerturbedModel_pointwise (x : ℝ) (p : CompactModelParameter) :
    Tendsto (normalizedModelError oscillatoryObjective compactPerturbedModel x p) (𝓝 0) (𝓝 0) := by
  by_cases hp : p.val = 0
  · have he : normalizedModelError oscillatoryObjective compactPerturbedModel x p =
        fun _ ↦ 0 := by
      funext s
      simp [compactPerturbedModel_error, hp]
    rw [he]
    exact tendsto_const_nhds
  have hp' : 0 < p.val := lt_of_le_of_ne p.prop.1 (Ne.symm hp)
  refine squeeze_zero (g := fun s : ℝ ↦ |s| / p.val) (fun s ↦ ?_) (fun s ↦ ?_) ?_
  · rw [compactPerturbedModel_error]
    positivity
  · by_cases hs : s = 0
    · simp [hs, compactPerturbedModel_error]
    rw [compactPerturbedModel_error, Real.norm_eq_abs]
    have hsn : 0 < |s| := abs_pos.mpr hs
    have hsin : Real.sin (s / p.val) ^ 2 ≤ (|s| / p.val) ^ 2 := by
      have hb : |Real.sin (s / p.val)| ≤ |s / p.val| := Real.abs_sin_le_abs
      rw [abs_div, abs_of_pos hp'] at hb
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb _
    apply (div_le_iff₀ hsn).mpr
    calc
      p.val * Real.sin (s / p.val) ^ 2 ≤ p.val * (|s| / p.val) ^ 2 :=
        mul_le_mul_of_nonneg_left hsin hp'.le
      _ = |s| / p.val * |s| := by field_simp
  · simpa only [abs_zero, zero_div] using (continuous_abs.div_const p.val).tendsto (0 : ℝ)

/-- Despite compactness and pointwise agreement, the normalized error stays
away from zero along a sequence of parameter-dependent steps. -/
theorem compactPerturbedModel_not_uniform :
    ¬ UniformNormalizedModelAgreementAt oscillatoryObjective compactPerturbedModel 0 := by
  intro h
  obtain ⟨ε, Δ, hε, hΔ, he⟩ := h (1 / Real.pi) (one_div_pos.mpr Real.pi_pos)
  let p₀ := min 1 (Δ / Real.pi)
  have hp₀ : 0 < p₀ := lt_min zero_lt_one (div_pos hΔ Real.pi_pos)
  let p : CompactModelParameter := ⟨p₀, hp₀.le, min_le_left _ _⟩
  let s := p₀ * (Real.pi / 2)
  have hs : 0 < s := mul_pos hp₀ (half_pos Real.pi_pos)
  have hnorm : ‖s‖ ≤ Δ := by
    rw [Real.norm_eq_abs, abs_of_pos hs]
    have hmul := (le_div_iff₀ Real.pi_pos).mp (min_le_right (1 : ℝ) (Δ / Real.pi))
    dsimp [s, p₀]
    linarith
  have hh := he 0 (mem_ball_self hε) p s hnorm
  have harg : s / p.val = Real.pi / 2 := by
    change p₀ * (Real.pi / 2) / p₀ = Real.pi / 2
    field_simp
  rw [compactPerturbedModel_error, harg, Real.sin_pi_div_two, one_pow, mul_one,
    Real.norm_eq_abs, abs_of_pos hs, abs_of_nonneg (div_nonneg hp₀.le hs.le)] at hh
  have hval : p.val / s = 2 / Real.pi := by
    change p₀ / (p₀ * (Real.pi / 2)) = 2 / Real.pi
    field_simp
  rw [hval] at hh
  have hfalse := (div_le_div_iff_of_pos_right Real.pi_pos).mp hh
  norm_num at hfalse

/-- Literal Lemma 11.2.3 fails with compact parameters. For each positive radius
bound there is a boundary step satisfying the sufficient-decrease test with
constant one half whose ratio is below three quarters. -/
theorem compactPerturbedModel_rejected {D : ℝ} (hD : 0 < D) :
    ∃ (p : CompactModelParameter) (Δ : ℝ), 0 < Δ ∧ Δ < D ∧
      (1 / 2 : ℝ) * ‖minimumNormSubgradient oscillatoryObjective 0‖ * min 1 Δ ≤
        compactPerturbedModel 0 p 0 - compactPerturbedModel 0 p Δ ∧
      reductionRatio oscillatoryObjective 0 Δ
        (compactPerturbedModel 0 p 0 - compactPerturbedModel 0 p Δ) < 3 / 4 := by
  let Δ := min (D / 2) (1 / 2)
  have hΔ : 0 < Δ := lt_min (half_pos hD) (by norm_num)
  have hΔhalf : Δ ≤ 1 / 2 := min_le_right _ _
  let p₀ := Δ / (Real.pi / 2)
  have hp₀ : 0 < p₀ := div_pos hΔ (half_pos Real.pi_pos)
  have hp₁ : p₀ ≤ 1 := (div_le_one (half_pos Real.pi_pos)).mpr
    (hΔhalf.trans (by linarith [Real.pi_gt_three]))
  let p : CompactModelParameter := ⟨p₀, hp₀.le, hp₁⟩
  have harg : Δ / p.val = Real.pi / 2 := by
    change Δ / (Δ / (Real.pi / 2)) = Real.pi / 2
    field_simp [hΔ.ne', Real.pi_pos.ne']
  have hpred : compactPerturbedModel 0 p 0 - compactPerturbedModel 0 p Δ =
      Δ - Δ ^ 2 + p₀ := by
    simp [compactPerturbedModel, oscillatoryObjective, harg, p]
    ring
  have hact : oscillatoryObjective 0 - oscillatoryObjective (0 + Δ) = Δ - Δ ^ 2 := by
    simp [oscillatoryObjective]
  have hlow : Δ / 2 ≤ Δ - Δ ^ 2 := by nlinarith [mul_nonneg hΔ.le (sub_nonneg.mpr hΔhalf)]
  have hpredpos : 0 < compactPerturbedModel 0 p 0 - compactPerturbedModel 0 p Δ := by
    rw [hpred]
    linarith
  refine ⟨p, Δ, hΔ, (min_le_left _ _).trans_lt (half_lt_self hD), ?_, ?_⟩
  · rw [oscillatoryObjective_minimumNorm, norm_neg, norm_one,
      min_eq_right (hΔhalf.trans (by norm_num)), hpred]
    linarith
  · apply (reductionRatio_lt_iff hpredpos).mpr
    rw [hpred, hact]
    have hh : Δ < 3 * p₀ := by
      have he : p₀ * (Real.pi / 2) = Δ := div_mul_cancel₀ _ (half_pos Real.pi_pos).ne'
      nlinarith [mul_pos hp₀ (show 0 < 3 - Real.pi / 2 by linarith [Real.pi_lt_four])]
    nlinarith [sq_nonneg Δ]

end ConnGouldToint.Chapter11
