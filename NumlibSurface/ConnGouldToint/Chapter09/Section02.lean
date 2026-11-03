import NumlibSurface.ConnGouldToint.Chapter09.Section01
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecificLimits.Basic

/-! # First-order criticality transfer -/

open Filter Topology

namespace ConnGouldToint.Chapter09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radius and reference-radius part of Algorithm 9.1.1. Here `ref k`
is the reference before the test at iteration `k`; `ref (k + 1)` is the value
used in the update (9.1.6). -/
structure ConditionalRadiusRun (η₀ η₁ γ₁ γ₂ : ℝ) (contractOnInvalid : Prop) where
  radius : ℕ → ℝ
  ref : ℕ → ℝ
  raw : ℕ → ℝ
  selected : ℕ → ℝ
  valid : ℕ → Prop
  initial_pos : 0 < radius 0
  initial_ref : ref 0 = radius 0
  ref_reset : ∀ k, η₀ ≤ selected k ∨ valid k → ref (k + 1) = radius k
  ref_keep : ∀ k, ¬(η₀ ≤ selected k ∨ valid k) → ref (k + 1) = ref k
  high_update : ∀ k, η₁ ≤ raw k → ref (k + 1) ≤ radius (k + 1)
  low_update : ∀ k, raw k < η₁ → valid k ∨ contractOnInvalid →
    γ₁ * ref (k + 1) ≤ radius (k + 1) ∧ radius (k + 1) ≤ γ₂ * ref (k + 1)
  invalid_update : ∀ k, raw k < η₁ → ¬valid k → ¬contractOnInvalid →
    radius (k + 1) = radius k

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The ratio estimate in the proof of Theorem 9.2.1. The two endpoint bounds
allow for conditional models that need not interpolate the center. -/
theorem conditionalRatio_ge_eta_of_small_valid_radius {f m : E → ℝ} {x trial : E}
    {Δ a β κ C η : ℝ} (hΔ : 0 < Δ) (ha : 0 < a) (hβ : 0 < β)
    (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hη₀ : 0 ≤ η) (hη₁ : η < 1)
    (hC : 2 * C ≤ β) (hsmall : Δ ≤ κ * a * (1 - η) / β)
    (hdec : κ * a * min (a / β) Δ ≤ m x - m trial)
    (hx : |f x - m x| ≤ C * Δ ^ 2) (ht : |f trial - m trial| ≤ C * Δ ^ 2) :
    η ≤ selectedTrialRatio f m x trial trial := by
  have hsmall' := (le_div_iff₀ hβ).mp hsmall
  have hη : 0 ≤ 1 - η := by linarith
  have hprod : κ * (1 - η) ≤ 1 := by
    calc
      κ * (1 - η) ≤ 1 * (1 - η) := mul_le_mul_of_nonneg_right hκ₁ hη
      _ ≤ 1 := by linarith
  have haΔ : Δ ≤ a / β := by
    apply (le_div_iff₀ hβ).mpr
    calc
      Δ * β ≤ κ * a * (1 - η) := hsmall'
      _ = (κ * (1 - η)) * a := by ring
      _ ≤ a := mul_le_of_le_one_left ha.le hprod
  rw [min_eq_right haΔ] at hdec
  let p := m x - m trial
  have hp : 0 < p := (mul_pos (mul_pos hκ ha) hΔ).trans_le hdec
  have herror : |(f x - f trial) - p| ≤ (1 - η) * p := by
    calc
      |(f x - f trial) - p| = |(f x - m x) - (f trial - m trial)| := by
        congr 1
        dsimp [p]
        ring
      _ ≤ |f x - m x| + |f trial - m trial| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (f x - m x) (f trial - m trial)
      _ ≤ 2 * C * Δ ^ 2 := by linarith
      _ ≤ β * Δ ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg Δ)
      _ ≤ (1 - η) * p := by
        have hb := mul_le_mul_of_nonneg_right hsmall' hΔ.le
        have hd := mul_le_mul_of_nonneg_left hdec hη
        nlinarith only [hb, hd]
  change η ≤ (f x - f trial) / p
  apply (le_div_iff₀ hp).mpr
  linarith [(abs_le.mp herror).1]

/-- Corrected Theorem 9.2.1. A low raw ratio can contract the radius only
after model validity has been certified. A low-ratio invalid iteration
keeps its current radius. The lower bound
includes the initial radius. -/
theorem theorem_9_2_1 {η₀ η₁ γ₁ γ₂ : ℝ}
    (run : ConditionalRadiusRun η₀ η₁ γ₁ γ₂ False) {t : ℝ}
    (ht : 0 < t) (hγ : 0 < γ₁)
    (hsmall : ∀ k, run.valid k → run.radius k ≤ t → η₁ ≤ run.raw k) :
    ∃ r > 0, ∀ k, r < run.radius k := by
  let b := min (run.radius 0) (γ₁ * t)
  have hb : 0 < b := lt_min run.initial_pos (mul_pos hγ ht)
  have hinv (k : ℕ) : b ≤ run.ref k ∧ b ≤ run.radius k := by
    induction k with
    | zero =>
      rw [run.initial_ref]
      exact ⟨min_le_left _ _, min_le_left _ _⟩
    | succ k ih =>
      have href : b ≤ run.ref (k + 1) := by
        by_cases h : η₀ ≤ run.selected k ∨ run.valid k
        · rw [run.ref_reset k h]
          exact ih.2
        · rw [run.ref_keep k h]
          exact ih.1
      refine ⟨href, ?_⟩
      by_cases hr : η₁ ≤ run.raw k
      · exact href.trans (run.high_update k hr)
      · have hr' := lt_of_not_ge hr
        by_cases hv : run.valid k
        · have hlarge : t < run.radius k := lt_of_not_ge fun h ↦ hr (hsmall k hv h)
          have hl := (run.low_update k hr' (Or.inl hv)).1
          rw [run.ref_reset k (Or.inr hv)] at hl
          exact (min_le_right _ _).trans
            ((mul_le_mul_of_nonneg_left hlarge.le hγ.le).trans hl)
        · rw [run.invalid_update k hr' hv not_false]
          exact ih.2
  exact ⟨b / 2, by positivity, fun k ↦ (half_lt_self hb).trans_le (hinv k).2⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The model-bound form of the corrected Theorem 9.2.1. A common upper
bound `β` covers the curvature denominator in AA.1 and twice the endpoint
error constant measured in the trust-region radius. -/
theorem theorem_9_2_1_of_model_bounds {f : E → ℝ} {m : ℕ → E → ℝ} {x trial : ℕ → E}
    {η₀ η₁ γ₁ γ₂ κ C β amin : ℝ} (run : ConditionalRadiusRun η₀ η₁ γ₁ γ₂ False)
    {a : ℕ → ℝ} (ha : 0 < amin) (hgrad : ∀ k, amin ≤ a k)
    (hγ : 0 < γ₁) (hβ : 0 < β) (hκ : 0 < κ) (hκ₁ : κ ≤ 1)
    (hη₀ : 0 ≤ η₁) (hη₁ : η₁ < 1) (hC : 2 * C ≤ β)
    (hraw : ∀ k, run.raw k = selectedTrialRatio f (m k) (x k) (trial k) (trial k))
    (hdec : ∀ k, κ * a k * min (a k / β) (run.radius k) ≤ m k (x k) - m k (trial k))
    (herr : ∀ k, run.valid k →
      |f (x k) - m k (x k)| ≤ C * (run.radius k) ^ 2 ∧
      |f (trial k) - m k (trial k)| ≤ C * (run.radius k) ^ 2) :
    ∃ r > 0, ∀ k, r < run.radius k := by
  have hpos (k : ℕ) : 0 < run.ref k ∧ 0 < run.radius k := by
    induction k with
    | zero =>
      rw [run.initial_ref]
      exact ⟨run.initial_pos, run.initial_pos⟩
    | succ k ih =>
      have href : 0 < run.ref (k + 1) := by
        by_cases h : η₀ ≤ run.selected k ∨ run.valid k
        · rw [run.ref_reset k h]
          exact ih.2
        · rw [run.ref_keep k h]
          exact ih.1
      refine ⟨href, ?_⟩
      by_cases hr : η₁ ≤ run.raw k
      · exact href.trans_le (run.high_update k hr)
      · by_cases hv : run.valid k
        · exact (mul_pos hγ href).trans_le
            (run.low_update k (lt_of_not_ge hr) (Or.inl hv)).1
        · rw [run.invalid_update k (lt_of_not_ge hr) hv not_false]
          exact ih.2
  let t := κ * amin * (1 - η₁) / β
  have hη : 0 < 1 - η₁ := sub_pos.mpr hη₁
  have ht : 0 < t := by dsimp [t]; positivity
  apply theorem_9_2_1 run ht hγ
  intro k hv hs
  rw [hraw k]
  refine conditionalRatio_ge_eta_of_small_valid_radius (hpos k).2 (ha.trans_le (hgrad k))
    hβ hκ hκ₁ hη₀ hη₁ hC ?_ (hdec k) (herr k hv).1 (herr k hv).2
  exact hs.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hgrad k) hκ.le) hη.le) hβ.le)

/-- A bounded-below quadratic objective and affine conditional models realize
the failing radius behavior. An exact replacement model is available in a
single improvement, but selection of the improved trial makes Step 5 move
to a new center, where it may construct another invalid model. -/
theorem theorem_9_2_1_quadratic_counterexample :
    let f : ℝ → ℝ := fun z ↦ (2 - z) ^ 2
    ∃ (run : ConditionalRadiusRun (1 / 4) (1 / 2) (1 / 2) (1 / 2) True)
      (x : ℕ → ℝ) (m : ℕ → ℝ → ℝ),
      ContDiff ℝ 2 f ∧ (∀ z, 0 ≤ f z ∧ deriv (deriv f) z = 2) ∧
      (∀ k, ContDiff ℝ 2 (m k) ∧ ∀ z, deriv (deriv (m k)) z = 0) ∧
      (∀ k,
        let Δ := run.radius k
        let trial := x k - Δ
        let chosen := x (k + 1)
        run.raw k = selectedTrialRatio f (m k) (x k) trial trial ∧
        run.selected k = selectedTrialRatio f (m k) (x k) trial chosen ∧
        run.raw k < 1 / 2 ∧ 1 / 4 ≤ run.selected k ∧
        (run.valid k ↔ modelValidOnBall f (m k) (x k) Δ 1) ∧
        ¬run.valid k ∧ modelValidOnBall f f (x k) Δ 1 ∧
        chosen ∈ Metric.closedBall (x k) Δ ∧ IsMinOn f {x k, chosen} chosen ∧
        ‖fderiv ℝ (m k) (x k)‖ = 1 ∧
        (1 / 2 : ℝ) * min 1 Δ ≤ m k (x k) - m k trial) ∧
      Tendsto run.radius atTop (𝓝 0) := by
  dsimp only
  let f : ℝ → ℝ := fun z ↦ (2 - z) ^ 2
  let Δ (k : ℕ) : ℝ := (1 / 2) ^ k
  let x (k : ℕ) := 1 - Δ k
  let m (k : ℕ) (z : ℝ) := f (x k) + (z - x k)
  have hpos (k : ℕ) : 0 < Δ k := by dsimp [Δ]; positivity
  have hle (k : ℕ) : Δ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hstep (k : ℕ) : Δ (k + 1) = Δ k / 2 := by dsimp [Δ]; rw [pow_succ]; ring
  let run : ConditionalRadiusRun (1 / 4) (1 / 2) (1 / 2) (1 / 2) True :=
    { radius := Δ
      ref := fun k ↦ Δ (k - 1)
      raw := fun k ↦ -(2 + 3 * Δ k)
      selected := fun k ↦ 1 + 3 * Δ k / 4
      valid := fun _ ↦ False
      initial_pos := hpos 0
      initial_ref := rfl
      ref_reset := by intro k _; simp
      ref_keep := by
        intro k h
        exact (h (Or.inl (by linarith [hpos k]))).elim
      high_update := by intro k h; linarith [hpos k]
      low_update := by
        intro k _ _
        simp only [Nat.add_sub_cancel, hstep]
        constructor <;> linarith
      invalid_update := by intro _ _ _ h; exact (h trivial).elim }
  have hdf : deriv f = fun z ↦ 2 * (z - 2) := by
    funext z
    have hd : HasDerivAt (fun y : ℝ ↦ 2 - y) (-1) z := (hasDerivAt_id z).const_sub 2
    change deriv ((fun y : ℝ ↦ 2 - y) ^ 2) z = _
    rw [(hd.pow 2).deriv]
    ring
  have hdm (k : ℕ) (z : ℝ) : HasDerivAt (m k) 1 z := by
    simpa [m] using (hasDerivAt_id z).sub_const (x k) |>.const_add (f (x k))
  refine ⟨run, x, m, (contDiff_const.sub contDiff_id).pow 2, ?_, ?_, ?_, ?_⟩
  · intro z
    refine ⟨sq_nonneg _, ?_⟩
    rw [hdf]
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id z).sub_const (2 : ℝ)).const_mul (2 : ℝ)).deriv
  · intro k
    refine ⟨contDiff_const.add (contDiff_id.sub contDiff_const), fun z ↦ ?_⟩
    rw [show deriv (m k) = Function.const ℝ (1 : ℝ) by
      funext y
      exact (hdm k y).deriv]
    exact deriv_const z _
  · intro k
    have hp := hpos k
    have hmdec : m k (x k) - m k (x k - Δ k) = Δ k := by dsimp [m]; ring
    have hraw : f (x k) - f (x k - Δ k) = -(2 + 3 * Δ k) * Δ k := by
      dsimp [f, x]; ring
    have hchosen : f (x k) - f (x (k + 1)) = (1 + 3 * Δ k / 4) * Δ k := by
      dsimp [f, x]; rw [hstep]; ring
    have hbad : ¬modelValidOnBall f (m k) (x k) (Δ k) 1 := by
      intro hv
      have hb : x k - Δ k ∈ Metric.closedBall (x k) (Δ k) := by
        rw [Metric.mem_closedBall, Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hp]
      have he := (abs_le.mp (hv _ hb)).2
      have hferr : f (x k - Δ k) - m k (x k - Δ k) = (3 + 3 * Δ k) * Δ k := by
        dsimp [f, m, x]; ring
      rw [hferr, one_mul] at he
      nlinarith
    have hc : x (k + 1) ∈ Metric.closedBall (x k) (Δ k) := by
      rw [Metric.mem_closedBall, Real.dist_eq]
      have hh : x (k + 1) - x k = Δ k / 2 := by dsimp [x]; rw [hstep]; ring
      rw [hh, abs_of_pos (half_pos hp)]
      linarith
    have hmin : IsMinOn f {x k, x (k + 1)} (x (k + 1)) := by
      rw [isMinOn_iff]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · have : 0 ≤ (1 + 3 * Δ k / 4) * Δ k := by positivity
        linarith
      · exact le_rfl
    have hd : ‖fderiv ℝ (m k) (x k)‖ = 1 := by
      rw [← norm_deriv_eq_norm_fderiv, (hdm k (x k)).deriv, norm_one]
    change _ ∧ _ ∧ _ ∧ _ ∧ (False ↔ _) ∧ ¬False ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
    refine ⟨?_, ?_, by change -(2 + 3 * Δ k) < 1 / 2; linarith,
      by change 1 / 4 ≤ 1 + 3 * Δ k / 4; linarith,
      ⟨False.elim, hbad⟩, not_false, ?_, hc, hmin, hd, ?_⟩
    · change -(2 + 3 * Δ k) = (f (x k) - f (x k - Δ k)) / _
      rw [hmdec, hraw, mul_div_cancel_right₀ _ hp.ne']
    · change 1 + 3 * Δ k / 4 = (f (x k) - f (x (k + 1))) / _
      rw [hmdec, hchosen, mul_div_cancel_right₀ _ hp.ne']
    · intro z _
      simp [sq_nonneg]
    · rw [hmdec, min_eq_right (hle k)]
      linarith
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Under continued rejection, each certified-valid iteration contracts the
radius and each intervening invalid iteration retains it. Repeated certification
then gives valid iterations at arbitrarily small radii. -/
theorem ConditionalRadiusRun.exists_valid_small_radius {η₀ η₁ γ₁ γ₂ : ℝ}
    (run : ConditionalRadiusRun η₀ η₁ γ₁ γ₂ False) (N : ℕ) (hγ₂ : 0 < γ₂) (hγ₂' : γ₂ < 1)
    (hpos : ∀ k, 0 < run.radius k)
    (hraw : ∀ k ≥ N, run.raw k < η₁)
    (hvalid : ∀ j ≥ N, ∃ k ≥ j, run.valid k) {t : ℝ} (ht : 0 < t) :
    ∃ k ≥ N, run.valid k ∧ run.radius k < t := by
  have hcontract (k : ℕ) (hk : N ≤ k) (hv : run.valid k) :
      run.radius (k + 1) ≤ γ₂ * run.radius k := by
    have h := (run.low_update k (hraw k hk) (Or.inl hv)).2
    rwa [run.ref_reset k (Or.inr hv)] at h
  have hmono (i j : ℕ) (hi : N ≤ i) (hij : i ≤ j) : run.radius j ≤ run.radius i := by
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih =>
      have hj := hi.trans hij
      by_cases hv : run.valid j
      · exact (hcontract j hj hv).trans
          ((mul_le_of_le_one_left (hpos j).le hγ₂'.le).trans ih)
      · rw [run.invalid_update j (hraw j hj) hv not_false]
        exact ih
  have hgeom (n : ℕ) : ∃ k ≥ N, run.valid k ∧ run.radius k ≤ γ₂ ^ n * run.radius N := by
    induction n with
    | zero =>
      obtain ⟨k, hk, hv⟩ := hvalid N le_rfl
      exact ⟨k, hk, hv, by simpa using hmono N k le_rfl hk⟩
    | succ n ih =>
      obtain ⟨j, hj, hv, hb⟩ := ih
      have hj' := hj.trans (Nat.le_succ j)
      obtain ⟨k, hk, hv'⟩ := hvalid (j + 1) hj'
      refine ⟨k, hj'.trans hk, hv', ?_⟩
      calc
        run.radius k ≤ run.radius (j + 1) := hmono (j + 1) k hj' hk
        _ ≤ γ₂ * run.radius j := hcontract j hj hv
        _ ≤ γ₂ * (γ₂ ^ n * run.radius N) := mul_le_mul_of_nonneg_left hb hγ₂.le
        _ = γ₂ ^ (n + 1) * run.radius N := by rw [pow_succ', mul_assoc]
  have hlim : Tendsto (fun n ↦ γ₂ ^ n * run.radius N) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hγ₂.le hγ₂').mul_const (run.radius N)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds ht)).exists
  obtain ⟨k, hk, hv, hb⟩ := hgeom n
  exact ⟨k, hk, hv, hb.trans_lt hn⟩

/-- Corrected Theorem 9.2.2 for an infinite outer run. The finite-improvement
condition is applied to the rejected tail, where the center and the radius
stay fixed between valid models. The conclusion also follows from Lemma
9.1.2(iii) when the inner refinement loop does not terminate. -/
theorem theorem_9_2_2 {f : E → ℝ} (hf : ContDiff ℝ 2 f) {m : ℕ → E → ℝ}
    (hm : ∀ k, Differentiable ℝ (m k)) (hDm : ∀ k, Differentiable ℝ (fderiv ℝ (m k)))
    {x trial : ℕ → E} {η₀ η₁ γ₁ γ₂ κv κ β ν Bf Bm : ℝ}
    (run : ConditionalRadiusRun η₀ η₁ γ₁ γ₂ False)
    (hη₀ : 0 ≤ η₁) (hη₁ : η₁ < 1) (hγ₂ : 0 < γ₂) (hγ₂' : γ₂ < 1)
    (hκv : 0 < κv) (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hβ : 0 < β) (hν : 0 < ν)
    (hC : 2 * (κv * ν ^ 2) ≤ β) (hBf : 0 ≤ Bf) (hBm : 0 ≤ Bm)
    (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ Bf)
    (hM : ∀ k z, ‖fderiv ℝ (fderiv ℝ (m k)) z‖ ≤ Bm)
    (hpos : ∀ k, 0 < run.radius k)
    (hraw : ∀ k, run.raw k = selectedTrialRatio f (m k) (x k) (trial k) (trial k))
    (haccept : ∀ k, η₁ ≤ run.raw k → η₀ ≤ run.selected k)
    (hpoint : ∀ k, run.selected k < η₀ → x (k + 1) = x k)
    (hvalid : ∀ k, run.valid k →
      modelValidOnBall f (m k) (x k) (ν * run.radius k) κv ∧
        trial k ∈ Metric.closedBall (x k) (ν * run.radius k))
    (hdec : ∀ k, let a := ‖fderiv ℝ (m k) (x k)‖
      κ * a * min (a / β) (run.radius k) ≤ m k (x k) - m k (trial k))
    (N : ℕ) (hstop : ∀ k ≥ N, run.selected k < η₀)
    (himprove : ∀ j ≥ N, ∃ k ≥ j, run.valid k) :
    ∃ xstar, (∀ k ≥ N, x k = xstar) ∧ fderiv ℝ f xstar = 0 := by
  have hx (k : ℕ) (hk : N ≤ k) : x k = x N := by
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih => rw [hpoint k (hstop k hk), ih]
  refine ⟨x N, hx, ?_⟩
  by_contra hzero
  let a := ‖fderiv ℝ f (x N)‖ / 2
  have ha : 0 < a := half_pos (norm_pos_iff.mpr hzero)
  let D := (2 * κv + (Bf + Bm) / 2) * ν
  have hD : 0 < D := by dsimp [D]; positivity
  let t := min (a / D) (κ * a * (1 - η₁) / β)
  have ht : 0 < t := lt_min (div_pos ha hD)
    (div_pos (mul_pos (mul_pos hκ ha) (sub_pos.mpr hη₁)) hβ)
  have hlow (k : ℕ) (hk : N ≤ k) : run.raw k < η₁ :=
    lt_of_not_ge fun h ↦ (not_le_of_gt (hstop k hk)) (haccept k h)
  obtain ⟨k, hk, hv, hsmall⟩ :=
    run.exists_valid_small_radius N hγ₂ hγ₂' hpos hlow himprove ht
  have hδ := mul_pos hν (hpos k)
  have hgrad := theorem_9_1_1 hf (hm k) (hDm k) hδ hκv hBf hBm hF (hM k) (hvalid k hv).1
  have hda : D * run.radius k ≤ a := by
    rw [mul_comm]
    exact (le_div_iff₀ hD).mp (hsmall.le.trans (min_le_left _ _))
  have hab : a ≤ ‖fderiv ℝ (m k) (x k)‖ := by
    let p := fderiv ℝ f (x k)
    let q := fderiv ℝ (m k) (x k)
    have he : ‖p - q‖ ≤ a := by
      refine hgrad.trans ?_
      simpa only [D, mul_assoc] using hda
    have hn : ‖p‖ ≤ ‖p - q‖ + ‖q‖ := by
      simpa only [sub_add_cancel] using norm_add_le (p - q) q
    change a ≤ ‖q‖
    have hpn : ‖p‖ = 2 * a := by dsimp [p, a]; rw [hx k hk]; ring
    linarith
  have hsmall' : run.radius k ≤ κ * ‖fderiv ℝ (m k) (x k)‖ * (1 - η₁) / β :=
    (hsmall.le.trans (min_le_right _ _)).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hab hκ.le)
          (sub_nonneg.mpr hη₁.le)) hβ.le)
  have herr (z : E) (hz : z ∈ Metric.closedBall (x k) (ν * run.radius k)) :
      |f z - m k z| ≤ (κv * ν ^ 2) * (run.radius k) ^ 2 := by
    simpa only [mul_pow, mul_assoc] using (hvalid k hv).1 z hz
  have hgood : η₁ ≤ run.raw k := by
    rw [hraw k]
    exact conditionalRatio_ge_eta_of_small_valid_radius (hpos k) (ha.trans_le hab)
      hβ hκ hκ₁ hη₀ hη₁ hC hsmall' (hdec k)
      (herr _ (Metric.mem_closedBall_self hδ.le)) (herr _ (hvalid k hv).2)
  exact (not_le_of_gt (hlow k hk)) hgood

/-- Lemma 9.2.4, with the eventual accepted-model condition of Step 1 made explicit.
The sequences may already be restricted to the subsequence in (9.2.6). -/
theorem lemma_9_2_4 {f : E → ℝ} (hf : ContDiff ℝ 2 f) {m : ℕ → E → ℝ}
    (hm : ∀ k, Differentiable ℝ (m k)) (hDm : ∀ k, Differentiable ℝ (fderiv ℝ (m k)))
    {x : ℕ → E} {δ : ℕ → ℝ} {κ Bf Bm μ : ℝ} (hκ : 0 < κ)
    (hBf : 0 ≤ Bf) (hBm : 0 ≤ Bm)
    (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ Bf)
    (hM : ∀ k z, ‖fderiv ℝ (fderiv ℝ (m k)) z‖ ≤ Bm)
    (hvalid : ∀ᶠ k in atTop, 0 < δ k ∧ δ k ≤ μ * ‖fderiv ℝ (m k) (x k)‖ ∧
      modelValidOnBall f (m k) (x k) (δ k) κ)
    (hg : Tendsto (fun k ↦ ‖fderiv ℝ (m k) (x k)‖) atTop (𝓝 0)) :
    Tendsto (fun k ↦ ‖fderiv ℝ f (x k)‖) atTop (𝓝 0) := by
  let C := 2 * κ + (Bf + Bm) / 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlim : Tendsto (fun k ↦ (1 + C * μ) * ‖fderiv ℝ (m k) (x k)‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hg (f := fun _ ↦ 1 + C * μ)
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [hvalid] with k hk
  have he := theorem_9_1_1 hf (hm k) (hDm k) hk.1 hκ hBf hBm hF (hM k) hk.2.2
  let a := fderiv ℝ f (x k)
  let b := fderiv ℝ (m k) (x k)
  have hab : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    simpa only [sub_add_cancel] using norm_add_le (a - b) b
  change ‖a‖ ≤ (1 + C * μ) * ‖b‖
  calc
    ‖a‖ ≤ ‖a - b‖ + ‖b‖ := hab
    _ ≤ C * δ k + ‖b‖ := add_le_add he le_rfl
    _ ≤ C * (μ * ‖b‖) + ‖b‖ := add_le_add (mul_le_mul_of_nonneg_left hk.2.1 hC) le_rfl
    _ = _ := by ring

end ConnGouldToint.Chapter09
