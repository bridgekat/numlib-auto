import NumlibSurface.ConnGouldToint.Chapter10.Section03

/-! # The backtracking trust-region algorithm -/

open Filter Optimization ConnGouldToint.Chapter06
open scoped RealInnerProductSpace Topology

namespace ConnGouldToint.Chapter10

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Reuse a rejected descent direction. If the rejected step points
uphill, use the negative gradient instead. Normalize in the current norm. -/
noncomputable def backtrackingTRDirection (p : Seminorm ℝ E) (Δ : ℝ) (g previous : E) : E :=
  let d := if ⟪g, previous⟫ < 0 then previous else -g
  (Δ / p d) • d

/-- The corrected direction lies on the incoming trust-region boundary
and has a strictly negative slope at nonstationary points. -/
theorem backtrackingTRDirection_spec (p : Seminorm ℝ E)
    (hp : ∀ v, p v = 0 → v = 0) {Δ : ℝ} {g previous : E}
    (hΔ : 0 < Δ) (hg : g ≠ 0) :
    let d := backtrackingTRDirection p Δ g previous
    p d = Δ ∧ ⟪g, d⟫ < 0 := by
  let d := if ⟪g, previous⟫ < 0 then previous else -g
  have hslope : ⟪g, d⟫ < 0 := by
    dsimp [d]
    split
    · assumption
    · rw [inner_neg_right, real_inner_self_eq_norm_sq]
      exact neg_neg_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hg))
  have hd : d ≠ 0 := by
    intro h
    simp [h] at hslope
  have hpd : 0 < p d := lt_of_le_of_ne (apply_nonneg p d) (fun h ↦ hd (hp d h.symm))
  have hscale := div_pos hΔ hpd
  change p ((Δ / p d) • d) = Δ ∧ ⟪g, (Δ / p d) • d⟫ < 0
  constructor
  · rw [map_smul_eq_mul, Real.norm_of_nonneg hscale.le, div_mul_cancel₀ _ hpd.ne']
  · rw [real_inner_smul_right]
    exact mul_neg_of_pos_of_neg hscale hslope

/-- The Armijo test (10.3.5) with the same candidate exponent on both sides. -/
def backtrackingTRArmijo (f : E → ℝ) (x d : E) (q b slope : ℝ) (j : ℕ) : Prop :=
  f (x + q ^ j • d) ≤ f x + b * q ^ j * slope

/-- A negative slope and a quadratic upper estimate guarantee a first
accepted backtracking index. -/
theorem exists_backtrackingTRArmijo {f : E → ℝ} {x d : E}
    {q b slope L : ℝ} (hq : q ∈ Set.Ioo 0 1) (hb : b < 1)
    (hs : slope < 0) (hL : 0 < L)
    (hTaylor : ∀ t ∈ Set.Ioc (0 : ℝ) 1, f (x + t • d) ≤ f x + t * slope + L * t ^ 2) :
    ∃ j, backtrackingTRArmijo f x d q b slope j ∧
      ∀ i < j, ¬ backtrackingTRArmijo f x d q b slope i := by
  classical
  let r := (1 - b) * (-slope) / L
  have hr : 0 < r := div_pos (mul_pos (sub_pos.mpr hb) (neg_pos.mpr hs)) hL
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hq.1.le hq.2).eventually (gt_mem_nhds hr)
  obtain ⟨j, hj⟩ := ht.exists
  have hpow : 0 < q ^ j := pow_pos hq.1 _
  have hqj : q ^ j ≤ 1 := pow_le_one₀ hq.1.le hq.2.le
  have hsmall : L * q ^ j ≤ (1 - b) * (-slope) := by
    have h := (le_div_iff₀ hL).mp hj.le
    linarith only [h]
  have hgood : backtrackingTRArmijo f x d q b slope j := by
    unfold backtrackingTRArmijo
    exact (hTaylor _ ⟨hpow, hqj⟩).trans (by
      nlinarith only [mul_le_mul_of_nonneg_right hsmall hpow.le])
  let hex : ∃ i, backtrackingTRArmijo f x d q b slope i := ⟨j, hgood⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun _ hi ↦ Nat.find_min hex hi⟩

/-- An Armijo probe can be used in the ratio test only when its
predicted reduction is positive. -/
def backtrackingTRTrial (f m : E → ℝ) (x d : E) (q b slope : ℝ) (j : ℕ) : Prop :=
  backtrackingTRArmijo f x d q b slope j ∧ m (x + q ^ j • d) < m x

/-- When the objective and model share the negative slope and a
quadratic upper estimate, both trial tests eventually pass. -/
theorem exists_backtrackingTRTrial {f m : E → ℝ} {x d : E}
    {q b slope L : ℝ} (hq : q ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1)
    (hs : slope < 0) (hL : 0 < L)
    (hTaylor : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      f (x + t • d) - f x ≤ t * slope + L * t ^ 2 ∧
      m (x + t • d) - m x ≤ t * slope + L * t ^ 2) :
    ∃ j, backtrackingTRTrial f m x d q b slope j ∧
      ∀ i < j, ¬ backtrackingTRTrial f m x d q b slope i := by
  classical
  let h (y : E) := max (f y - f x) (m y - m x)
  obtain ⟨j, hj, _⟩ := exists_backtrackingTRArmijo (f := h) (x := x) (d := d)
    hq hb.2 hs hL (fun t ht ↦ by
      have hbound := hTaylor t ht
      simpa [h] using (max_le hbound.1 hbound.2))
  have hh : h (x + q ^ j • d) ≤ b * q ^ j * slope := by
    simpa [backtrackingTRArmijo, h] using hj
  have hneg : b * q ^ j * slope < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hb.1 (pow_pos hq.1 _)) hs
  have hgood : backtrackingTRTrial f m x d q b slope j := by
    constructor
    · unfold backtrackingTRArmijo
      linarith only [(le_max_left _ _).trans hh]
    · exact sub_neg.mp ((le_max_right _ _).trans_lt (hh.trans_lt hneg))
  let hex : ∃ i, backtrackingTRTrial f m x d q b slope i := ⟨j, hgood⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun _ hi ↦ Nat.find_min hex hi⟩

/-- A nonterminal run of Algorithm 10.3.2. Incoming and reset radii
are separate, so the radius reset does not masquerade as a BTR update. -/
structure BacktrackingTRRun [CompleteSpace E] (f : E → ℝ) (P : BTRParams)
    (q b Δmax κ₁ κ₂ : ℝ) (angle : E → ℝ) where
  x : ℕ → E
  step : ℕ → E
  incomingRadius : ℕ → ℝ
  radius : ℕ → ℝ
  norm : ℕ → Seminorm ℝ E
  model : ℕ → E → ℝ
  β : ℕ → ℝ
  curvature : ℕ → ℝ
  q_range : q ∈ Set.Ioo 0 1
  b_range : b ∈ Set.Ioo 0 (1 / 2)
  separates : ∀ k v, norm k v = 0 → v = 0
  incoming_pos : ∀ k, 0 < incomingRadius k
  incoming_cap : ∀ k, incomingRadius k ≤ Δmax
  feasible : ∀ k, norm k (step k) ≤ radius k
  predicted_pos : ∀ k, 0 < model k (x k) - model k (x k + step k)
  fresh_trial : ∀ k,
    (k = 0 ∨ P.η₁ ≤ btrRatio f (model (k - 1)) (x (k - 1)) (step (k - 1))) →
    radius k = incomingRadius k ∧
    HasSufficientModelDecrease (model k) (x k) (step k) (gradient f (x k)) (β k) (radius k) κ₁ ∧
    HasNegativeCurvatureDecrease (model k) (x k) (step k) (curvature k) (radius k) κ₂ ∧
    angle (x k) * ‖gradient f (x k)‖ * ‖step k‖ ≤ |⟪gradient f (x k), step k⟫|
  rejected_trial : ∀ k, btrRatio f (model k) (x k) (step k) < P.η₁ →
    let i := k + 1
    let g := gradient f (x i)
    let d := backtrackingTRDirection (norm i) (incomingRadius i) g (step k)
    model i = model k ∧ g ≠ 0 ∧
    ∃ j, backtrackingTRTrial f (model i) (x i) d q b ⟪g, d⟫ j ∧
      (∀ l < j, ¬ backtrackingTRTrial f (model i) (x i) d q b ⟪g, d⟫ l) ∧
      step i = q ^ j • d ∧ radius i = norm i (step i)
  iterate_update : ∀ k,
    x (k + 1) = acceptStep P.η₁ f (x k) (step k) (model k (x k) - model k (x k + step k))
  radius_update : ∀ k, BTRRadiusUpdate P (btrRatio f (model k) (x k) (step k))
    (radius k) (incomingRadius (k + 1))

/-- The printed absolute angle condition allows a rejected step to
point uphill. Here it gives model decrease, but every positive reuse
of the step fails the Armijo test for the objective. -/
theorem backtrackingTR_ascent_reuse_counterexample :
    let f : ℝ → ℝ := fun x ↦ x + x ^ 2
    let m : ℝ → ℝ := fun x ↦ x - 2 * x ^ 2
    ContDiff ℝ 2 f ∧ BddBelow (Set.range f) ∧ ContDiff ℝ 2 m ∧
      m 0 = f 0 ∧ deriv m 0 = deriv f 0 ∧ deriv f 0 = 1 ∧
      HasSufficientModelDecrease m 0 1 (gradient f 0) 5 1 (1 / 2) ∧
      btrRatio f m 0 1 < defaultBTRParams.η₁ ∧
      ∀ t > 0, f 0 + (1 / 4) * t * deriv f 0 < f (0 + t) := by
  dsimp only
  let f : ℝ → ℝ := fun x ↦ x + x ^ 2
  let m : ℝ → ℝ := fun x ↦ x - 2 * x ^ 2
  have hf : HasDerivAt f 1 0 := by
    convert (hasDerivAt_id (0 : ℝ)).add ((hasDerivAt_id (0 : ℝ)).pow 2) using 1
    · rfl
    · norm_num [id]
  have hm : HasDerivAt m 1 0 := by
    convert (hasDerivAt_id (0 : ℝ)).sub (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul 2) using 1
    · rfl
    · norm_num [id]
  change ContDiff ℝ 2 f ∧ BddBelow (Set.range f) ∧ ContDiff ℝ 2 m ∧
    m 0 = f 0 ∧ deriv m 0 = deriv f 0 ∧ deriv f 0 = 1 ∧
    HasSufficientModelDecrease m 0 1 (gradient f 0) 5 1 (1 / 2) ∧
    btrRatio f m 0 1 < defaultBTRParams.η₁ ∧
    ∀ t > 0, f 0 + (1 / 4) * t * deriv f 0 < f (0 + t)
  refine ⟨by unfold f; fun_prop, ⟨-1 / 4, ?_⟩, by unfold m; fun_prop,
    by norm_num [f, m], hm.deriv.trans hf.deriv.symm, hf.deriv, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    change -1 / 4 ≤ x + x ^ 2
    nlinarith [sq_nonneg (x + 1 / 2)]
  · rw [hf.hasGradientAt.gradient]
    norm_num [HasSufficientModelDecrease, m]
  · norm_num [btrRatio, reductionRatio, f, m, defaultBTRParams]
  · intro t ht
    rw [hf.deriv]
    dsimp [f]
    nlinarith [sq_nonneg t]

end ConnGouldToint.Chapter10
