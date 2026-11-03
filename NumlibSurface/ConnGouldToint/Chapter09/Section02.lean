import NumlibSurface.ConnGouldToint.Chapter09.Section01
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Order.MonotoneConvergence
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
/-- Corrected Lemma 9.1.2(ii). The finite-improvement guarantee applies to
a block of rejected invalid models because the repaired update keeps both
the center and the radius fixed until the next reference reset. -/
theorem lemma_9_1_2_ii {η₀ η₁ γ₁ γ₂ : ℝ}
    (run : ConditionalRadiusRun η₀ η₁ γ₁ γ₂ False) (x : ℕ → E)
    (haccept : ∀ k, η₁ ≤ run.raw k → η₀ ≤ run.selected k)
    (hstay : ∀ k, run.selected k < η₀ → x (k + 1) = x k)
    (hfinish : ∀ N, ∃ j ≥ N,
      (∀ k, N ≤ k → k < j → run.raw k < η₁ ∧ ¬run.valid k ∧
        x k = x N ∧ run.radius k = run.radius N) → run.valid j) (N : ℕ) :
    ∃ k ≥ N, η₀ ≤ run.selected k ∨ run.valid k := by
  by_contra! h
  have hraw (k : ℕ) (hk : N ≤ k) : run.raw k < η₁ :=
    lt_of_not_ge fun hgood ↦ (not_le_of_gt (h k hk).1) (haccept k hgood)
  have hconst (k : ℕ) (hk : N ≤ k) : x k = x N ∧ run.radius k = run.radius N := by
    induction k, hk using Nat.le_induction with
    | base => exact ⟨rfl, rfl⟩
    | succ k hk ih =>
      exact ⟨(hstay k (h k hk).1).trans ih.1,
        (run.invalid_update k (hraw k hk) (h k hk).2 not_false).trans ih.2⟩
  obtain ⟨j, hj, hcert⟩ := hfinish N
  exact (h j hj).2 (hcert fun k hk _ ↦ ⟨hraw k hk, (h k hk).2, hconst k hk⟩)

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

/-- The corrected update preserves positivity of the radius and the reference. -/
theorem ConditionalRadiusRun.radius_and_ref_pos {η₀ η₁ γ₁ γ₂ : ℝ}
    (run : ConditionalRadiusRun η₀ η₁ γ₁ γ₂ False) (hγ : 0 < γ₁) :
    ∀ k, 0 < run.ref k ∧ 0 < run.radius k := by
  intro k
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

/-- A radius floor on a tail where valid small-radius trials are accepted. -/
theorem ConditionalRadiusRun.tail_radius_floor {η₀ η₁ γ₁ γ₂ : ℝ}
    (run : ConditionalRadiusRun η₀ η₁ γ₁ γ₂ False) (N : ℕ) {t : ℝ}
    (ht : 0 < t) (hγ : 0 < γ₁)
    (hsmall : ∀ k ≥ N, run.valid k → run.radius k ≤ t → η₁ ≤ run.raw k) :
    ∃ r > 0, ∀ k ≥ N, r < run.radius k := by
  let b := min (min (run.ref N) (run.radius N)) (γ₁ * t)
  obtain ⟨href₀, hrad₀⟩ := run.radius_and_ref_pos hγ N
  have hb : 0 < b := lt_min (lt_min href₀ hrad₀) (mul_pos hγ ht)
  have hinv (k : ℕ) (hk : N ≤ k) : b ≤ run.ref k ∧ b ≤ run.radius k := by
    induction k, hk using Nat.le_induction with
    | base =>
      exact ⟨(min_le_left _ _).trans (min_le_left _ _),
        (min_le_left _ _).trans (min_le_right _ _)⟩
    | succ k hk ih =>
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
        · have hlarge : t < run.radius k := lt_of_not_ge fun h ↦ hr (hsmall k hk hv h)
          have hl := (run.low_update k hr' (Or.inl hv)).1
          rw [run.ref_reset k (Or.inr hv)] at hl
          exact (min_le_right _ _).trans
            ((mul_le_mul_of_nonneg_left hlarge.le hγ.le).trans hl)
        · rw [run.invalid_update k hr' hv not_false]
          exact ih.2
  exact ⟨b / 2, by positivity, fun k hk ↦ (half_lt_self hb).trans_le (hinv k hk).2⟩

/-- Corrected Theorem 9.2.1. A low raw ratio can contract the radius only
after model validity has been certified. A low-ratio invalid iteration
keeps its current radius. The lower bound includes the initial radius. -/
theorem theorem_9_2_1 {η₀ η₁ γ₁ γ₂ : ℝ}
    (run : ConditionalRadiusRun η₀ η₁ γ₁ γ₂ False) {t : ℝ}
    (ht : 0 < t) (hγ : 0 < γ₁)
    (hsmall : ∀ k, run.valid k → run.radius k ≤ t → η₁ ≤ run.raw k) :
    ∃ r > 0, ∀ k, r < run.radius k := by
  obtain ⟨r, hr, h⟩ := run.tail_radius_floor 0 ht hγ (fun k _ ↦ hsmall k)
  exact ⟨r, hr, fun k ↦ h k (Nat.zero_le k)⟩

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
  let t := κ * amin * (1 - η₁) / β
  have hη : 0 < 1 - η₁ := sub_pos.mpr hη₁
  have ht : 0 < t := by dsimp [t]; positivity
  apply theorem_9_2_1 run ht hγ
  intro k hv hs
  rw [hraw k]
  refine conditionalRatio_ge_eta_of_small_valid_radius (run.radius_and_ref_pos hγ k).2
    (ha.trans_le (hgrad k)) hβ hκ hκ₁ hη₀ hη₁ hC ?_ (hdec k) (herr k hv).1 (herr k hv).2
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
        2 ≤ ‖fderiv ℝ f (x k)‖ ∧
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
    change _ ∧ _ ∧ _ ∧ _ ∧ (False ↔ _) ∧ ¬False ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
    refine ⟨?_, ?_, by change -(2 + 3 * Δ k) < 1 / 2; linarith,
      by change 1 / 4 ≤ 1 + 3 * Δ k / 4; linarith,
      ⟨False.elim, hbad⟩, not_false, ?_, hc, hmin, hd, ?_, ?_⟩
    · change -(2 + 3 * Δ k) = (f (x k) - f (x k - Δ k)) / _
      rw [hmdec, hraw, mul_div_cancel_right₀ _ hp.ne']
    · change 1 + 3 * Δ k / 4 = (f (x k) - f (x (k + 1))) / _
      rw [hmdec, hchosen, mul_div_cancel_right₀ _ hp.ne']
    · intro z _
      simp [sq_nonneg]
    · rw [← norm_deriv_eq_norm_fderiv, hdf, Real.norm_eq_abs]
      have hxk : x k ≤ 1 := by dsimp [x]; linarith
      rw [abs_of_nonpos (by linarith : 2 * (x k - 2) ≤ 0)]
      linarith
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

private theorem liminf_eq_zero_of_frequently_lt {a : ℕ → ℝ}
    (ha : ∀ k, 0 ≤ a k) (hf : ∀ ε > 0, ∃ᶠ k in atTop, a k < ε) :
    liminf a atTop = 0 := by
  have hb : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) a :=
    ⟨0, show ∀ᶠ k in atTop, 0 ≤ a k from Eventually.of_forall ha⟩
  have hc : (atTop : Filter ℕ).IsCoboundedUnder (· ≥ ·) a := by
    refine ⟨1, fun b h ↦ ?_⟩
    obtain ⟨k, hk, hbk⟩ := ((hf 1 zero_lt_one).and_eventually h).exists
    exact hbk.trans hk.le
  refine le_antisymm ?_ (le_liminf_of_le hc (Eventually.of_forall ha))
  by_contra! hp
  have hlim := liminf_le_of_frequently_le ((hf _ (half_pos hp)).mono fun _ h ↦ h.le) hb
  linarith

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Corrected Theorem 9.2.3 for Algorithm 9.1.1 with the validity-gated radius
update. On a tail with model gradients bounded below, valid small-radius
trials are accepted. The resulting radius floor rules out both infinitely
many uniformly productive steps and an infinite rejected tail. -/
theorem theorem_9_2_3 {f : E → ℝ} {m : ℕ → E → ℝ} {x trial : ℕ → E}
    {η₀ η₁ γ₁ γ₂ κ C β : ℝ} (run : ConditionalRadiusRun η₀ η₁ γ₁ γ₂ False)
    (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (hη₀ : 0 < η₀) (hη : η₀ ≤ η₁)
    (hη₁ : η₁ < 1) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₂' : γ₂ < 1)
    (hβ : 0 < β) (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hC : 2 * C ≤ β)
    (hraw : ∀ k, run.raw k = selectedTrialRatio f (m k) (x k) (trial k) (trial k))
    (hdec : ∀ k, κ * a k * min (a k / β) (run.radius k) ≤ m k (x k) - m k (trial k))
    (herr : ∀ k, run.valid k →
      |f (x k) - m k (x k)| ≤ C * (run.radius k) ^ 2 ∧
      |f (trial k) - m k (trial k)| ≤ C * (run.radius k) ^ 2)
    (haccept : ∀ k, η₁ ≤ run.raw k → η₀ ≤ run.selected k)
    (hprogress : ∀ k, η₀ ≤ run.selected k →
      η₀ * (m k (x k) - m k (trial k)) ≤ f (x k) - f (x (k + 1)))
    (hstay : ∀ k, run.selected k < η₀ → x (k + 1) = x k)
    (hcertify : ∀ n, (∀ k ≥ n, run.selected k < η₀) → ∃ k ≥ n, run.valid k)
    (hlower : BddBelow (Set.range f)) :
    liminf a atTop = 0 ∧ ∀ ε > 0, ∃ᶠ k in atTop, a k < ε := by
  have hpos (k : ℕ) := (run.radius_and_ref_pos hγ₁ k).2
  have hfreq (ε : ℝ) (hε : 0 < ε) : ∃ᶠ k in atTop, a k < ε := by
    by_contra! hbad
    obtain ⟨N, hN⟩ := eventually_atTop.mp hbad
    let t := κ * ε * (1 - η₁) / β
    have hη' : 0 < 1 - η₁ := sub_pos.mpr hη₁
    have ht : 0 < t := by dsimp [t]; positivity
    have hsmall (k : ℕ) (hk : N ≤ k) (hv : run.valid k) (hs : run.radius k ≤ t) :
        η₁ ≤ run.raw k := by
      rw [hraw k]
      refine conditionalRatio_ge_eta_of_small_valid_radius (hpos k) (hε.trans_le (hN k hk))
        hβ hκ hκ₁ (hη₀.le.trans hη) hη₁ hC ?_ (hdec k) (herr k hv).1 (herr k hv).2
      exact hs.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hN k hk) hκ.le) hη'.le) hβ.le)
    obtain ⟨r, hr, hfloor⟩ := run.tail_radius_floor N ht hγ₁ hsmall
    let c := η₀ * (κ * ε * min (ε / β) r)
    have hc : 0 < c := by
      exact mul_pos hη₀ (mul_pos (mul_pos hκ hε) (lt_min (div_pos hε hβ) hr))
    have hpred (k : ℕ) (hk : N ≤ k) :
        κ * ε * min (ε / β) r ≤ m k (x k) - m k (trial k) := by
      apply le_trans _ (hdec k)
      have hm : min (ε / β) r ≤ min (a k / β) (run.radius k) :=
        min_le_min (div_le_div_of_nonneg_right (hN k hk) hβ.le) (hfloor k hk).le
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hN k hk) hκ.le) hm
        (le_min (div_nonneg hε.le hβ.le) hr.le) (mul_nonneg hκ.le (ha k))
    let v (k : ℕ) := f (x k)
    have hmono : Antitone v := by
      apply antitone_nat_of_succ_le
      intro k
      by_cases hs : η₀ ≤ run.selected k
      · have hnonneg : 0 ≤ m k (x k) - m k (trial k) :=
          (mul_nonneg (mul_nonneg hκ.le (ha k))
            (le_min (div_nonneg (ha k) hβ.le) (hpos k).le)).trans (hdec k)
        exact sub_nonneg.mp ((mul_nonneg hη₀.le hnonneg).trans (hprogress k hs))
      · change f (x (k + 1)) ≤ f (x k)
        rw [hstay k (lt_of_not_ge hs)]
    have hb : BddBelow (Set.range v) := hlower.mono (Set.range_comp_subset_range x f)
    have hlim := tendsto_atTop_ciInf hmono hb
    have hdiff : Tendsto (fun k ↦ v k - v (k + 1)) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, sub_self] using
        hlim.sub (hlim.comp (tendsto_add_atTop_nat 1))
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (hdiff.eventually (gt_mem_nhds hc))
    let M := max J N
    have hstop (k : ℕ) (hk : M ≤ k) : run.selected k < η₀ := by
      apply lt_of_not_ge
      intro hs
      have hp := hpred k ((le_max_right _ _).trans hk)
      have hle := (mul_le_mul_of_nonneg_left hp hη₀.le).trans (hprogress k hs)
      exact (not_le_of_gt (hJ k ((le_max_left _ _).trans hk))) hle
    have hlow (k : ℕ) (hk : M ≤ k) : run.raw k < η₁ :=
      lt_of_not_ge fun h ↦ (not_le_of_gt (hstop k hk)) (haccept k h)
    have hvalid (j : ℕ) (hj : M ≤ j) : ∃ k ≥ j, run.valid k :=
      hcertify j (fun k hk ↦ hstop k (hj.trans hk))
    obtain ⟨k, hk, _, hs⟩ := run.exists_valid_small_radius M hγ₂ hγ₂' hpos hlow hvalid hr
    exact (not_lt_of_ge (hfloor k ((le_max_right _ _).trans hk)).le) hs
  exact ⟨liminf_eq_zero_of_frequently_lt ha hfreq, hfreq⟩

/-- Equation (9.2.8) and its triangle-inequality consequence at one
accepted criticality test. -/
theorem norm_fderiv_le_of_accepted_criticality {f m : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hm : Differentiable ℝ m) (hDm : Differentiable ℝ (fderiv ℝ m)) {x : E}
    {δ κ Bf Bm μ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hBf : 0 ≤ Bf) (hBm : 0 ≤ Bm)
    (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ Bf)
    (hM : ∀ z, ‖fderiv ℝ (fderiv ℝ m) z‖ ≤ Bm)
    (hvalid : modelValidOnBall f m x δ κ) (hcap : δ ≤ μ * ‖fderiv ℝ m x‖) :
    ‖fderiv ℝ f x‖ ≤ (1 + (2 * κ + (Bf + Bm) / 2) * μ) * ‖fderiv ℝ m x‖ := by
  let C := 2 * κ + (Bf + Bm) / 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he := theorem_9_1_1 hf hm hDm hδ hκ hBf hBm hF hM hvalid
  let a := fderiv ℝ f x
  let b := fderiv ℝ m x
  change ‖a‖ ≤ (1 + C * μ) * ‖b‖
  calc
    ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by simpa only [sub_add_cancel] using norm_add_le (a - b) b
    _ ≤ C * δ + ‖b‖ := add_le_add he le_rfl
    _ ≤ C * (μ * ‖b‖) + ‖b‖ := add_le_add (mul_le_mul_of_nonneg_left hcap hC) le_rfl
    _ = _ := by ring

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
  have hlim : Tendsto (fun k ↦ (1 + C * μ) * ‖fderiv ℝ (m k) (x k)‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hg (f := fun _ ↦ 1 + C * μ)
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [hvalid] with k hk
  exact norm_fderiv_le_of_accepted_criticality hf (hm k) (hDm k) hk.1 hκ hBf hBm
    hF (hM k) hk.2.2 hk.2.1

/-- The liminf conclusion of Theorem 9.2.5. The accepted-model test is
needed only at sufficiently small model gradients, as in Step 1. -/
theorem theorem_9_2_5 {f : E → ℝ} (hf : ContDiff ℝ 2 f) {m : ℕ → E → ℝ}
    (hm : ∀ k, Differentiable ℝ (m k)) (hDm : ∀ k, Differentiable ℝ (fderiv ℝ (m k)))
    {x : ℕ → E} {δ : ℕ → ℝ} {κ Bf Bm μ εc : ℝ} (hκ : 0 < κ) (hεc : 0 < εc)
    (hBf : 0 ≤ Bf) (hBm : 0 ≤ Bm) (hμ : 0 ≤ μ)
    (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ Bf)
    (hM : ∀ k z, ‖fderiv ℝ (fderiv ℝ (m k)) z‖ ≤ Bm)
    (hvalid : ∀ k, ‖fderiv ℝ (m k) (x k)‖ ≤ εc →
      0 < δ k ∧ δ k ≤ μ * ‖fderiv ℝ (m k) (x k)‖ ∧ modelValidOnBall f (m k) (x k) (δ k) κ)
    (hg : ∀ ε > 0, ∃ᶠ k in atTop, ‖fderiv ℝ (m k) (x k)‖ < ε) :
    liminf (fun k ↦ ‖fderiv ℝ f (x k)‖) atTop = 0 ∧
      ∀ ε > 0, ∃ᶠ k in atTop, ‖fderiv ℝ f (x k)‖ < ε := by
  let C := 2 * κ + (Bf + Bm) / 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hK : 0 < 1 + C * μ := by positivity
  have hfreq (ε : ℝ) (hε : 0 < ε) : ∃ᶠ k in atTop, ‖fderiv ℝ f (x k)‖ < ε := by
    refine (hg _ (lt_min hεc (div_pos hε hK))).mono fun k hk ↦ ?_
    have hv := hvalid k ((lt_of_lt_of_le hk (min_le_left _ _)).le)
    have he := norm_fderiv_le_of_accepted_criticality hf (hm k) (hDm k) hv.1 hκ hBf hBm
      hF (hM k) hv.2.2 hv.2.1
    apply he.trans_lt
    have hk' := (lt_div_iff₀ hK).mp (hk.trans_le (min_le_right _ _))
    simpa only [C, mul_comm] using hk'
  exact ⟨liminf_eq_zero_of_frequently_lt (fun _ ↦ norm_nonneg _) hfreq, hfreq⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- An unsuccessful iterate stays fixed until the next successful iteration.
If successes are infinite, small gradient norms therefore occur frequently
also among successful iterations. -/
theorem frequently_successful_small_gradient {x : ℕ → E} {u : E → ℝ} {S : Set ℕ}
    (hS : ∃ᶠ k in atTop, k ∈ S) (hstay : ∀ k ∉ S, x (k + 1) = x k)
    (hfreq : ∀ ε > 0, ∃ᶠ k in atTop, u (x k) < ε) :
    ∀ ε > 0, ∃ᶠ k in atTop, k ∈ S ∧ u (x k) < ε := by
  classical
  intro ε hε
  apply frequently_atTop.mpr
  intro N
  obtain ⟨k, hk, hsmall⟩ := frequently_atTop.mp (hfreq ε hε) N
  have hex : ∃ j, k ≤ j ∧ j ∈ S := frequently_atTop.mp hS k
  let j := Nat.find hex
  have hj : k ≤ j ∧ j ∈ S := Nat.find_spec hex
  have hx (i : ℕ) (hi : k ≤ i) : i ≤ j → x i = x k := by
    induction i, hi using Nat.le_induction with
    | base => intro _; rfl
    | succ i hi ih =>
      intro hij
      have hlt : i < j := Nat.lt_of_succ_le hij
      have hn : i ∉ S := fun hs ↦ Nat.find_min hex hlt ⟨hi, hs⟩
      rw [hstay i hn, ih hlt.le]
  exact ⟨j, hk.trans hj.1, hj.2, by simpa only [hx j hj.1 le_rfl] using hsmall⟩

/-- Compact containment of the successful iterates gives an actual convergent
subsequence in Theorem 9.2.5, provided that successful small-gradient
iterations occur frequently. -/
theorem theorem_9_2_5_exists_critical_subseq {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    {x : ℕ → E} {K : Set E} {S : Set ℕ} (hK : IsCompact K) (hx : ∀ k ∈ S, x k ∈ K)
    (hfreq : ∀ ε > 0, ∃ᶠ k in atTop, k ∈ S ∧ ‖fderiv ℝ f (x k)‖ < ε) :
    ∃ z ∈ K, ∃ j : ℕ → ℕ, StrictMono j ∧ (∀ n, j n ∈ S) ∧
      Tendsto (x ∘ j) atTop (𝓝 z) ∧ fderiv ℝ f z = 0 := by
  obtain ⟨j, hj, hjS⟩ := extraction_forall_of_frequently fun n : ℕ ↦
    hfreq (1 / ((n : ℝ) + 1)) (by positivity)
  have hja : Tendsto (fun n ↦ ‖fderiv ℝ f (x (j n))‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ (hjS n).2.le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨z, hz, i, hi, hzi⟩ := hK.isSeqCompact (fun n ↦ hx (j n) (hjS n).1)
  have hgrad : Continuous (fun y ↦ ‖fderiv ℝ f y‖) := (hf.continuous_fderiv (by norm_num)).norm
  have hn : ‖fderiv ℝ f z‖ = 0 :=
    tendsto_nhds_unique (hgrad.continuousAt.tendsto.comp hzi) (hja.comp hi.tendsto_atTop)
  exact ⟨z, hz, j ∘ i, hj.comp hi, fun n ↦ (hjS (i n)).1, hzi, norm_eq_zero.mp hn⟩

/-- Corrected Theorem 9.2.6. The criticality test supplies the comparison
between the objective and model gradients when the model gradient is small.
Combined with valid selected steps and the small-gradient subsequence, the
objective gradient norms tend to zero along the full run. -/
theorem theorem_9_2_6 {f : E → ℝ} {x : ℕ → E} {a pred Δ : ℕ → ℝ} {S : Set ℕ}
    {η κ β εc A L K : ℝ} (hη : 0 < η) (hκ : 0 < κ) (hβ : 0 < β)
    (hεc : 0 < εc) (hA : 0 < A) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (ha : ∀ k, 0 ≤ a k) (hΔ : ∀ k, 0 < Δ k)
    (hcompare : ∀ k, a k ≤ εc → ‖fderiv ℝ f (x k)‖ ≤ A * a k)
    (hgrad : ∀ y z, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖)
    (hdec : ∀ k, κ * a k * min (a k / β) (Δ k) ≤ pred k)
    (hprogress : ∀ k ∈ S, η * pred k ≤ f (x k) - f (x (k + 1)))
    (hstep : ∀ k ∈ S, ‖x k - x (k + 1)‖ ≤ K * Δ k)
    (hstay : ∀ k ∉ S, x (k + 1) = x k)
    (hlower : BddBelow (Set.range f))
    (hfreq : ∀ ε > 0, ∃ᶠ k in atTop, ‖fderiv ℝ f (x k)‖ < ε) :
    Tendsto (fun k ↦ ‖fderiv ℝ f (x k)‖) atTop (𝓝 0) ∧
      ∀ z (j : ℕ → ℕ), Tendsto j atTop atTop → Tendsto (x ∘ j) atTop (𝓝 z) →
        fderiv ℝ f z = 0 := by
  classical
  let u (k : ℕ) := ‖fderiv ℝ f (x k)‖
  let v (k : ℕ) := f (x k)
  have hmono : Antitone v := by
    apply antitone_nat_of_succ_le
    intro k
    by_cases hs : k ∈ S
    · have hp : 0 ≤ pred k :=
        (mul_nonneg (mul_nonneg hκ.le (ha k))
          (le_min (div_nonneg (ha k) hβ.le) (hΔ k).le)).trans (hdec k)
      exact sub_nonneg.mp ((mul_nonneg hη.le hp).trans (hprogress k hs))
    · change f (x (k + 1)) ≤ f (x k)
      rw [hstay k hs]
  have hb : BddBelow (Set.range v) := hlower.mono (Set.range_comp_subset_range x f)
  have hlim := tendsto_atTop_ciInf hmono hb
  have hdiff : Tendsto (fun k ↦ v k - v (k + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using hlim.sub (hlim.comp (tendsto_add_atTop_nat 1))
  have htail : Tendsto (fun k ↦ v k - ⨅ i, v i) atTop (𝓝 0) := by
    simpa only [sub_self] using hlim.sub_const (⨅ i, v i)
  have hLK : 0 ≤ L * K := mul_nonneg hL hK
  have hLK₁ : 0 < L * K + 1 := by positivity
  have hu : Tendsto u atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    let e := ε / 2
    let b := min εc (e / A)
    let c := η * (κ * b)
    have he : 0 < e := half_pos hε
    have hb₀ : 0 < b := lt_min hεc (div_pos he hA)
    have hc : 0 < c := mul_pos hη (mul_pos hκ hb₀)
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (hdiff.eventually (gt_mem_nhds (mul_pos hc (div_pos hb₀ hβ))))
    obtain ⟨J, hJ⟩ := eventually_atTop.mp
      (htail.eventually (gt_mem_nhds (div_pos (mul_pos hc he) hLK₁)))
    have hlocal (k : ℕ) (hk : N ≤ k) (hhigh : e ≤ u k) :
        c * (u k - u (k + 1)) ≤ (L * K) * (v k - v (k + 1)) := by
      by_cases hs : k ∈ S
      · have hab : b ≤ a k := by
          by_cases hsmall : a k ≤ εc
          · exact (min_le_right _ _).trans ((div_le_iff₀ hA).mpr
              (by simpa only [mul_comm] using hhigh.trans (hcompare k hsmall)))
          · exact (min_le_left _ _).trans (le_of_lt (lt_of_not_ge hsmall))
        have hm : κ * b * min (b / β) (Δ k) ≤ pred k :=
          (mul_le_mul (mul_le_mul_of_nonneg_left hab hκ.le)
            (min_le_min (div_le_div_of_nonneg_right hab hβ.le) le_rfl)
            (le_min (div_nonneg hb₀.le hβ.le) (hΔ k).le)
            (mul_nonneg hκ.le (ha k))).trans (hdec k)
        have hdrop : c * min (b / β) (Δ k) ≤ v k - v (k + 1) := by
          simpa only [c, mul_assoc] using
            (mul_le_mul_of_nonneg_left hm hη.le).trans (hprogress k hs)
        have hrad : Δ k ≤ b / β := by
          by_contra! hn
          rw [min_eq_left hn.le] at hdrop
          exact (hN k hk).not_ge hdrop
        rw [min_eq_right hrad] at hdrop
        have hnorm : u k - u (k + 1) ≤ (L * K) * Δ k := calc
          _ ≤ ‖fderiv ℝ f (x k) - fderiv ℝ f (x (k + 1))‖ := norm_sub_norm_le _ _
          _ ≤ L * ‖x k - x (k + 1)‖ := hgrad _ _
          _ ≤ L * (K * Δ k) := mul_le_mul_of_nonneg_left (hstep k hs) hL
          _ = _ := by ring
        calc
          _ ≤ c * ((L * K) * Δ k) := mul_le_mul_of_nonneg_left hnorm hc.le
          _ = (L * K) * (c * Δ k) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hdrop hLK
      · simp only [u, v, hstay k hs, sub_self, mul_zero, le_refl]
    refine ⟨max N J, fun k hk ↦ ?_⟩
    have hkN := (le_max_left N J).trans hk
    have hkJ := (le_max_right N J).trans hk
    change dist (u k) 0 < ε
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    by_contra! hhigh
    have hExists : ∃ j, k ≤ j ∧ u j < e := frequently_atTop.mp (hfreq e he) k
    let j := Nat.find hExists
    have hj : k ≤ j ∧ u j < e := Nat.find_spec hExists
    have htel (i : ℕ) (hi : k ≤ i) : i ≤ j →
        c * (u k - u i) ≤ (L * K) * (v k - v i) := by
      induction i, hi using Nat.le_induction with
      | base => simp
      | succ i hi ih =>
        intro hij
        have hbelow : i < j := Nat.lt_of_succ_le hij
        have hui : e ≤ u i := le_of_not_gt fun hu ↦ (Nat.find_min hExists hbelow) ⟨hi, hu⟩
        linarith only [ih hbelow.le, hlocal i (hkN.trans hi) hui]
    have hgap : e < u k - u j := by dsimp [e] at hj ⊢; linarith [hj.2]
    have hlast : (L * K) * (v k - v j) < c * e := calc
      _ ≤ (L * K + 1) * (v k - v j) :=
        mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.mpr (hmono hj.1))
      _ ≤ (L * K + 1) * (v k - ⨅ i, v i) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_left (ciInf_le hb j) _) hLK₁.le
      _ < _ := by
        simpa only [mul_comm (L * K + 1)] using (lt_div_iff₀ hLK₁).mp (hJ k hkJ)
    exact (not_lt_of_ge (htel j hj.1 le_rfl))
      (hlast.trans (mul_lt_mul_of_pos_left hgap hc))
  refine ⟨hu, fun z j hj hxj ↦ ?_⟩
  have hcont : Continuous (fderiv ℝ f) := by
    refine (LipschitzWith.of_dist_le_mul (K := ⟨L, hL⟩) fun y z ↦ ?_).continuous
    rw [dist_eq_norm, dist_eq_norm]
    exact hgrad y z
  have hn := tendsto_nhds_unique (hcont.norm.continuousAt.tendsto.comp hxj) (hu.comp hj)
  exact norm_eq_zero.mp hn

end ConnGouldToint.Chapter09
