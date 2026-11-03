import NumlibSurface.ConnGouldToint.Chapter06.Section06
import NumlibSurface.ConnGouldToint.Chapter13.Section01

/-! # First primal barrier inner algorithm -/

open Filter Metric Set
open scoped Topology

namespace ConnGouldToint.Chapter13

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- AC.8 for a fixed barrier parameter and a feasible set in its ambient affine hull. -/
def BarrierDivergesAtBoundary (C : Set E) (b : E → ℝ) : Prop :=
  ∀ y : ℕ → E, (∀ j, y j ∈ interior C) →
    Tendsto (fun j ↦ infDist (y j) (frontier C)) atTop (𝓝 0) →
    Tendsto (fun j ↦ b (y j)) atTop atTop

omit [NormedSpace ℝ E] in
/-- Distance to a set satisfies the triangle estimate (13.1.5). -/
theorem barrierBoundary_dist_le_add (C : Set E) (x s : E) :
    infDist (x + s) (frontier C) ≤ infDist x (frontier C) + ‖s‖ := by
  simpa only [dist_eq_norm, add_sub_cancel_left] using
    (infDist_le_infDist_add_dist (x := x + s) (y := x) (s := frontier C))

/-- The interior and fraction-to-boundary test (13.2.1). -/
def BarrierAdmissibleTrial (C : Set E) (σ : ℝ) (x y : E) : Prop :=
  y ∈ interior C ∧ σ * infDist x (frontier C) ≤ infDist y (frontier C)

/-- Algorithm 13.2.1 evaluates the usual ratio on admissible trials.
Zero represents the rejection sentinel, since the two thresholds are positive. -/
noncomputable def primalBarrierRatio (C : Set E) (σ : ℝ) (φ m : E → ℝ) (x s : E) : ℝ :=
  open Classical in
  if BarrierAdmissibleTrial C σ x (x + s) then Chapter06.btrRatio φ m x s else 0

/-- The state and update rules of Algorithm 13.2.1 for a fixed barrier parameter.
A run consists of trials with positive predicted decrease. -/
structure PrimalBarrierInnerRun (P : Chapter06.BTRParams) (C : Set E) (σ : ℝ) (φ : E → ℝ) where
  x : ℕ → E
  s : ℕ → E
  Δ : ℕ → ℝ
  model : ℕ → E → ℝ
  initial_interior : x 0 ∈ interior C
  initial_radius_pos : 0 < Δ 0
  step_feasible : ∀ j, ‖s j‖ ≤ Δ j
  predicted_pos : ∀ j, 0 < model j (x j) - model j (x j + s j)
  iterate_update : ∀ j,
    x (j + 1) = if P.η₁ ≤ primalBarrierRatio C σ φ (model j) (x j) (s j)
      then x j + s j else x j
  radius_update : ∀ j,
    Chapter06.BTRRadiusUpdate P (primalBarrierRatio C σ φ (model j) (x j) (s j)) (Δ j) (Δ (j + 1))

omit [NormedSpace ℝ E] in
/-- Accepted trials and retained iterates both stay in the interior. -/
theorem PrimalBarrierInnerRun.interior_iterate {P : Chapter06.BTRParams} {C : Set E}
    {σ : ℝ} {φ : E → ℝ} (r : PrimalBarrierInnerRun P C σ φ) (j : ℕ) :
    r.x j ∈ interior C := by
  classical
  induction j with
  | zero => exact r.initial_interior
  | succ j ih =>
    by_cases ha : BarrierAdmissibleTrial C σ (r.x j) (r.x j + r.s j)
    · by_cases hρ : P.η₁ ≤ Chapter06.btrRatio φ (r.model j) (r.x j) (r.s j)
      · rw [r.iterate_update, primalBarrierRatio, ite_eq_left ha, ite_eq_left hρ]
        exact ha.1
      · rw [r.iterate_update, primalBarrierRatio, ite_eq_left ha,
          ite_eq_right hρ]
        exact ih
    · rw [r.iterate_update, primalBarrierRatio, ite_eq_right ha,
        ite_eq_right (not_le_of_gt P.eta₁_pos)]
      exact ih

omit [NormedSpace ℝ E] in
/-- Positive predicted decrease and a positive acceptance threshold give a
nonincreasing barrier-objective sequence. -/
theorem PrimalBarrierInnerRun.objective_antitone {P : Chapter06.BTRParams} {C : Set E}
    {σ : ℝ} {φ : E → ℝ} (r : PrimalBarrierInnerRun P C σ φ) :
    Antitone (fun j ↦ φ (r.x j)) := by
  classical
  apply antitone_nat_of_succ_le
  intro j
  change φ (r.x (j + 1)) ≤ φ (r.x j)
  by_cases ha : BarrierAdmissibleTrial C σ (r.x j) (r.x j + r.s j)
  · by_cases hρ : P.η₁ ≤ Chapter06.btrRatio φ (r.model j) (r.x j) (r.s j)
    · rw [r.iterate_update, primalBarrierRatio, ite_eq_left ha, ite_eq_left hρ]
      have hr := (P.eta₁_pos.trans_le hρ).le
      unfold Chapter06.btrRatio Optimization.reductionRatio at hr
      exact sub_nonneg.mp (by simpa only [zero_mul] using (le_div_iff₀ (r.predicted_pos j)).mp hr)
    · rw [r.iterate_update, primalBarrierRatio, ite_eq_left ha, ite_eq_right hρ]
  · rw [r.iterate_update, primalBarrierRatio, ite_eq_right ha,
      ite_eq_right (not_le_of_gt P.eta₁_pos)]

omit [NormedSpace ℝ E] in
/-- A sequence with bounded barrier values stays uniformly separated from the
boundary under AC.8. The argument only requires divergence along paths in the
class that contains the sequence and its reindexings. -/
theorem barrier_boundary_separation {C : Set E} {b : E → ℝ} {x : ℕ → E}
    (hx : ∀ j, x j ∈ interior C) {M : ℝ} (hb : ∀ j, b (x j) ≤ M)
    (hdiv : ∀ p : ℕ → ℕ, (∀ n, x (p n) ∈ interior C) →
      Tendsto (fun n ↦ infDist (x (p n)) (frontier C)) atTop (𝓝 0) →
      Tendsto (fun n ↦ b (x (p n))) atTop atTop) :
    ∃ ε ∈ Ioo (0 : ℝ) 1, ∀ j, ε ≤ infDist (x j) (frontier C) := by
  by_contra! h
  have hsmall (n : ℕ) : ∃ j, infDist (x j) (frontier C) < 1 / ((n : ℝ) + 2) := by
    apply h _ ⟨by positivity, ?_⟩
    apply (div_lt_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  choose p hp using hsmall
  have hu : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, Nat.cast_add, add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using ht
  have hd : Tendsto (fun n ↦ infDist (x (p n)) (frontier C)) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ infDist_nonneg) (fun n ↦ (hp n).le) hu
  obtain ⟨n, hn⟩ := ((tendsto_atTop.mp (hdiv p (fun n ↦ hx (p n)) hd)) (M + 1)).exists
  linarith [hb (p n)]

omit [NormedSpace ℝ E] in
private theorem PrimalBarrierInnerRun.boundary_separation_of_reindexings
    {P : Chapter06.BTRParams} {C : Set E} {σ : ℝ} {f b : E → ℝ}
    (r : PrimalBarrierInnerRun P C σ (f + b)) {L : ℝ} (hf : ∀ j, L ≤ f (r.x j))
    (hdiv : ∀ p : ℕ → ℕ, (∀ n, r.x (p n) ∈ interior C) →
      Tendsto (fun n ↦ infDist (r.x (p n)) (frontier C)) atTop (𝓝 0) →
      Tendsto (fun n ↦ b (r.x (p n))) atTop atTop) :
    ∃ ε ∈ Ioo (0 : ℝ) 1, ∀ j, ε ≤ infDist (r.x j) (frontier C) := by
  have hlevel (j : ℕ) : b (r.x j) ≤ (f + b) (r.x 0) - L := by
    have h := r.objective_antitone (Nat.zero_le j)
    change f (r.x j) + b (r.x j) ≤ (f + b) (r.x 0) at h
    linarith [hf j]
  exact barrier_boundary_separation r.interior_iterate hlevel hdiv

omit [NormedSpace ℝ E] in
/-- AC.8 separates an inner run from the boundary whenever the objective is
bounded below along that run. -/
theorem PrimalBarrierInnerRun.boundary_separation
    {P : Chapter06.BTRParams} {C : Set E} {σ : ℝ} {f b : E → ℝ}
    (r : PrimalBarrierInnerRun P C σ (f + b)) {L : ℝ} (hf : ∀ j, L ≤ f (r.x j))
    (hb : BarrierDivergesAtBoundary C b) :
    ∃ ε ∈ Ioo (0 : ℝ) 1, ∀ j, ε ≤ infDist (r.x j) (frontier C) :=
  r.boundary_separation_of_reindexings hf (fun p ↦ hb (r.x ∘ p))

section Geometry

variable [FiniteDimensional ℝ E]

/-- A displacement no larger than the admissible fraction of the boundary
distance stays in the interior and retains the prescribed clearance. -/
theorem barrierBoundary_clearance {C : Set E} (hC : C ≠ univ)
    {x y : E} (hx : x ∈ interior C) {σ ε : ℝ}
    (hσ : σ ∈ Ioo (0 : ℝ) 1) (hε : 0 < ε) (hd : ε ≤ infDist x (frontier C))
    (hy : dist y x ≤ (1 - σ) * infDist x (frontier C)) :
    BarrierAdmissibleTrial C σ x y ∧ σ * ε ≤ infDist y (frontier C) := by
  have hD : 0 < infDist x (frontier C) := hε.trans_le hd
  have hI : interior C ≠ univ := by
    intro he
    exact hC (univ_subset_iff.mp (he ▸ interior_subset))
  obtain ⟨z, hz, hzdist⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hI
  have hcomp : infDist x (frontier C) ≤ infDist x (interior C)ᶜ :=
    hzdist ▸ infDist_le_dist_of_mem (frontier_interior_subset hz)
  have hball : dist y x < infDist x (interior C)ᶜ := by
    apply lt_of_lt_of_le _ hcomp
    exact hy.trans_lt (by nlinarith [mul_pos hσ.1 hD])
  have hmem : y ∈ interior C := ball_infDist_compl_subset hball
  have htri := infDist_le_infDist_add_dist (x := x) (y := y) (s := frontier C)
  rw [dist_comm x y] at htri
  have hkeep : σ * infDist x (frontier C) ≤ infDist y (frontier C) := by linarith
  exact ⟨⟨hmem, hkeep⟩, (mul_le_mul_of_nonneg_left hd hσ.1.le).trans hkeep⟩

/-- Corrected Theorem 13.2.1. A lower bound on the objective converts the
accepted-level bound to an upper bound on barrier values. AC.8, or its
restriction to reindexings of this run, then separates all iterates from the
boundary. The layer bounds for the barrier and model Hessians apply throughout
the resulting reduced balls. -/
theorem theorem_13_2_1 {P : Chapter06.BTRParams} {C : Set E} (hC : C ≠ univ)
    {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) {f b : E → ℝ}
    (r : PrimalBarrierInnerRun P C σ (f + b)) {mB : ℕ → E → ℝ}
    {L : ℝ} (hf : ∀ j, L ≤ f (r.x j))
    (hdiv : ∀ p : ℕ → ℕ, (∀ n, r.x (p n) ∈ interior C) →
      Tendsto (fun n ↦ infDist (r.x (p n)) (frontier C)) atTop (𝓝 0) →
      Tendsto (fun n ↦ b (r.x (p n))) atTop atTop)
    (Bh Bm : ℝ → ℝ)
    (hb : ∀ ε > 0, ∀ y ∈ interior C, ε ≤ infDist y (frontier C) →
      ‖fderiv ℝ (fderiv ℝ b) y‖ ≤ Bh ε)
    (hm : ∀ ε > 0, ∀ j, ∀ y ∈ interior C, dist y (r.x j) ≤ r.Δ j →
      ε ≤ infDist y (frontier C) → ‖fderiv ℝ (fderiv ℝ (mB j)) y‖ ≤ Bm ε) :
    ∃ ε ∈ Ioo (0 : ℝ) 1, (∀ j, ε ≤ infDist (r.x j) (frontier C)) ∧
      ∀ j y, dist y (r.x j) ≤ (1 - σ) * infDist (r.x j) (frontier C) →
        y ∈ interior C ∧ ‖fderiv ℝ (fderiv ℝ b) y‖ ≤ Bh (σ * ε) ∧
        (dist y (r.x j) ≤ r.Δ j → ‖fderiv ℝ (fderiv ℝ (mB j)) y‖ ≤ Bm (σ * ε)) := by
  obtain ⟨ε, hε, hbound⟩ := r.boundary_separation_of_reindexings hf hdiv
  refine ⟨ε, hε, hbound, fun j y hy ↦ ?_⟩
  obtain ⟨htrial, hclear⟩ := barrierBoundary_clearance hC (r.interior_iterate j) hσ hε.1
    (hbound j) hy
  exact ⟨htrial.1, hb _ (mul_pos hσ.1 hε.1) y htrial.1 hclear,
    fun hyΔ ↦ hm _ (mul_pos hσ.1 hε.1) j y htrial.1 hyΔ hclear⟩

omit [FiniteDimensional ℝ E] in
private theorem barrierTaylorRemainder {F : E → ℝ} {x s : E} {Δ B : ℝ}
    (hΔ : 0 ≤ Δ) (hs : ‖s‖ ≤ Δ)
    (hd : ∀ y ∈ closedBall x Δ, ContDiffAt ℝ 2 F y)
    (hB : ∀ y ∈ closedBall x Δ, ‖fderiv ℝ (fderiv ℝ F) y‖ ≤ B) :
    |F (x + s) - (F x + fderiv ℝ F x s)| ≤ (1 / 2 : ℝ) * B * ‖s‖ ^ 2 := by
  have hx : x ∈ closedBall x Δ := mem_closedBall_self hΔ
  have hy : x + s ∈ closedBall x Δ := by
    simpa [mem_closedBall, dist_eq_norm] using hs
  have h₁ (y : E) (hy : y ∈ closedBall x Δ) : DifferentiableAt ℝ F y :=
    (hd y hy).differentiableAt (by norm_num)
  have h₂ (y : E) (hy : y ∈ closedBall x Δ) : DifferentiableAt ℝ (fderiv ℝ F) y :=
    ((hd y hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  simpa only [Real.norm_eq_abs] using
    norm_sub_firstOrder_le_of_hessian_bound (convex_closedBall x Δ) hx hy h₁ h₂ hB

/-- The constant κ_ubh in Theorem 13.2.2 combines the objective and barrier
bounds for the exact function and for the model. -/
noncomputable def primalBarrierHessianConstant (F B M MB : ℝ) : ℝ := max (F + B) (M + MB)

/-- Theorem 13.2.2. A small trust region lies in the separated interior
layer. Taylor remainder estimates for the two exact terms and their two
model terms give the combined error bound. -/
theorem theorem_13_2_2 {C : Set E} (hC : C ≠ univ) {σ ε : ℝ}
    (hσ : σ ∈ Ioo (0 : ℝ) 1) (hε : 0 < ε)
    {x s : E} (hx : x ∈ interior C) (hclear : ε ≤ infDist x (frontier C))
    {Δ : ℝ} (hs : ‖s‖ ≤ Δ) (hΔ : Δ ≤ (1 - σ) * ε)
    {f b mf mb : E → ℝ}
    (hf : ∀ y, ContDiffAt ℝ 2 f y) (hb : ∀ y ∈ interior C, ContDiffAt ℝ 2 b y)
    (hmf : ∀ y ∈ closedBall x Δ ∩ interior C, ContDiffAt ℝ 2 mf y)
    (hmb : ∀ y ∈ closedBall x Δ ∩ interior C, ContDiffAt ℝ 2 mb y)
    (hvalf : f x = mf x) (hvalb : b x = mb x)
    (hgradf : fderiv ℝ f x = fderiv ℝ mf x) (hgradb : fderiv ℝ b x = fderiv ℝ mb x)
    {F B M MB : ℝ}
    (hF : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ F)
    (hB : ∀ y ∈ interior C, σ * ε ≤ infDist y (frontier C) →
      ‖fderiv ℝ (fderiv ℝ b) y‖ ≤ B)
    (hM : ∀ y ∈ closedBall x Δ ∩ interior C, ‖fderiv ℝ (fderiv ℝ mf) y‖ ≤ M)
    (hMB : ∀ y ∈ closedBall x Δ ∩ interior C, σ * ε ≤ infDist y (frontier C) →
      ‖fderiv ℝ (fderiv ℝ mb) y‖ ≤ MB) :
    BarrierAdmissibleTrial C σ x (x + s) ∧
      |(f + b) (x + s) - (mf + mb) (x + s)| ≤
        primalBarrierHessianConstant F B M MB * Δ ^ 2 := by
  have hΔ₀ : 0 ≤ Δ := (norm_nonneg _).trans hs
  have hnear (y : E) (hy : y ∈ closedBall x Δ) :
      BarrierAdmissibleTrial C σ x y ∧ σ * ε ≤ infDist y (frontier C) :=
    barrierBoundary_clearance hC hx hσ hε hclear
      ((mem_closedBall.mp hy).trans (hΔ.trans
        (mul_le_mul_of_nonneg_left hclear (sub_nonneg.mpr hσ.2.le))))
  have hys : x + s ∈ closedBall x Δ := by
    simpa [mem_closedBall, dist_eq_norm] using hs
  refine ⟨(hnear _ hys).1, ?_⟩
  have ef := abs_le.mp (barrierTaylorRemainder (x := x) hΔ₀ hs (fun y _ ↦ hf y) (fun y _ ↦ hF y))
  have eb := abs_le.mp (barrierTaylorRemainder (x := x) hΔ₀ hs
    (fun y hy ↦ hb y (hnear y hy).1.1)
    (fun y hy ↦ hB y (hnear y hy).1.1 (hnear y hy).2))
  have em := abs_le.mp (barrierTaylorRemainder (x := x) hΔ₀ hs
    (fun y hy ↦ hmf y ⟨hy, (hnear y hy).1.1⟩)
    (fun y hy ↦ hM y ⟨hy, (hnear y hy).1.1⟩))
  have emb := abs_le.mp (barrierTaylorRemainder (x := x) hΔ₀ hs
    (fun y hy ↦ hmb y ⟨hy, (hnear y hy).1.1⟩)
    (fun y hy ↦ hMB y ⟨hy, (hnear y hy).1.1⟩ (hnear y hy).2))
  rw [← hvalf, ← hgradf] at em
  rw [← hvalb, ← hgradb] at emb
  let K := primalBarrierHessianConstant F B M MB
  have hK₁ : F + B ≤ K := le_max_left _ _
  have hK₂ : M + MB ≤ K := le_max_right _ _
  have hF₀ := (norm_nonneg (fderiv ℝ (fderiv ℝ f) x)).trans (hF x)
  have hxball : x ∈ closedBall x Δ := mem_closedBall_self hΔ₀
  have hB₀ := (norm_nonneg (fderiv ℝ (fderiv ℝ b) x)).trans (hB x hx (hnear x hxball).2)
  have hK₀ : 0 ≤ K := (add_nonneg hF₀ hB₀).trans hK₁
  have he : |(f + b) (x + s) - (mf + mb) (x + s)| ≤ K * ‖s‖ ^ 2 := by
    rw [abs_le]
    change -(K * ‖s‖ ^ 2) ≤ f (x + s) + b (x + s) - (mf (x + s) + mb (x + s)) ∧
      f (x + s) + b (x + s) - (mf (x + s) + mb (x + s)) ≤ K * ‖s‖ ^ 2
    have hk1 := mul_le_mul_of_nonneg_right hK₁ (sq_nonneg ‖s‖)
    have hk2 := mul_le_mul_of_nonneg_right hK₂ (sq_nonneg ‖s‖)
    exact ⟨by linarith [ef.1, eb.1, em.2, emb.2], by linarith [ef.2, eb.2, em.1, emb.1]⟩
  exact he.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) hΔ₀).mpr hs) hK₀)

/-- Theorem 13.2.3. The radius bound has two parts. The boundary bound makes
the trial admissible, and the usual agreement bound makes it very successful. -/
theorem theorem_13_2_3 {P : Chapter06.BTRParams} {C : Set E} (hC : C ≠ univ)
    {σ ε : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) (hε : 0 < ε)
    {φ m : E → ℝ} {x s g : E} (hx : x ∈ interior C)
    (hclear : ε ≤ infDist x (frontier C))
    {β Δ Δ' κ K : ℝ} (hβ : 0 < β) (hβK : β ≤ K) (hΔ : 0 < Δ) (hg : g ≠ 0)
    (hs : ‖s‖ ≤ Δ) (hval : φ x = m x)
    (hdec : Chapter06.HasSufficientModelDecrease m x s g β Δ κ)
    (herr : |φ (x + s) - m (x + s)| ≤ K * Δ ^ 2)
    (hsmall : Δ ≤ min (κ * ‖g‖ * (1 - P.η₂) / K) ((1 - σ) * ε))
    (hupdate : Chapter06.BTRRadiusUpdate P (primalBarrierRatio C σ φ m x s) Δ Δ') :
    BarrierAdmissibleTrial C σ x (x + s) ∧ P.η₂ ≤ primalBarrierRatio C σ φ m x s ∧ Δ ≤ Δ' := by
  have hd : dist (x + s) x ≤ (1 - σ) * infDist x (frontier C) := by
    rw [dist_eq_norm, add_sub_cancel_left]
    exact hs.trans ((hsmall.trans (min_le_right _ _)).trans
      (mul_le_mul_of_nonneg_left hclear (sub_nonneg.mpr hσ.2.le)))
  have ha := (barrierBoundary_clearance hC hx hσ hε hclear hd).1
  have hr : P.η₂ ≤ primalBarrierRatio C σ φ m x s := by
    classical
    rw [primalBarrierRatio, ite_eq_left ha]
    exact Chapter06.btrRatio_ge_eta₂_of_small_radius hβ hβK hΔ hg hval hdec herr
      (hsmall.trans (min_le_left _ _))
  exact ⟨ha, hr, hupdate.very_successful hr⟩

omit [FiniteDimensional ℝ E] in
private theorem primalBarrier_model_curvature_le {C : Set E} {x : E}
    {Δ M MB : ℝ} (hΔ : 0 < Δ) (hx : x ∈ interior C)
    {mf mb : E → ℝ}
    (hmf : ∀ y ∈ closedBall x Δ ∩ interior C, ContDiffAt ℝ 2 mf y)
    (hmb : ∀ y ∈ closedBall x Δ ∩ interior C, ContDiffAt ℝ 2 mb y)
    (hMf : ‖fderiv ℝ (fderiv ℝ mf) x‖ ≤ M - 1)
    (hMb : ‖fderiv ℝ (fderiv ℝ mb) x‖ ≤ MB) :
    1 + ‖fderiv ℝ (fderiv ℝ (mf + mb)) x‖ ≤ M + MB := by
  have hxc : x ∈ closedBall x Δ ∩ interior C := ⟨mem_closedBall_self hΔ.le, hx⟩
  have hnear : closedBall x Δ ∩ interior C ∈ 𝓝 x :=
    inter_mem (closedBall_mem_nhds x hΔ) (isOpen_interior.mem_nhds hx)
  have he : fderiv ℝ (mf + mb) =ᶠ[𝓝 x] fderiv ℝ mf + fderiv ℝ mb := by
    filter_upwards [hnear] with y hy
    exact (((hmf y hy).differentiableAt (by norm_num)).hasFDerivAt.add
      ((hmb y hy).differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hf' := ((hmf x hxc).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hb' := ((hmb x hxc).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [he.fderiv_eq, (hf'.hasFDerivAt.add hb'.hasFDerivAt).fderiv]
  linarith [norm_add_le (fderiv ℝ (fderiv ℝ mf) x) (fderiv ℝ (fderiv ℝ mb) x)]

/-- Theorem 13.2.3 under the objective and barrier Taylor-model assumptions.
The curvature denominator is the usual one plus the norm of the model
Hessian at the center. -/
theorem theorem_13_2_3_of_models {P : Chapter06.BTRParams} {C : Set E} (hC : C ≠ univ)
    {σ ε : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) (hε : 0 < ε)
    {x s g : E} (hx : x ∈ interior C) (hclear : ε ≤ infDist x (frontier C))
    {Δ Δ' κ : ℝ} (hΔ : 0 < Δ) (hg : g ≠ 0) (hs : ‖s‖ ≤ Δ)
    {f b mf mb : E → ℝ}
    (hf : ∀ y, ContDiffAt ℝ 2 f y) (hb : ∀ y ∈ interior C, ContDiffAt ℝ 2 b y)
    (hmf : ∀ y ∈ closedBall x Δ ∩ interior C, ContDiffAt ℝ 2 mf y)
    (hmb : ∀ y ∈ closedBall x Δ ∩ interior C, ContDiffAt ℝ 2 mb y)
    (hvalf : f x = mf x) (hvalb : b x = mb x)
    (hgradf : fderiv ℝ f x = fderiv ℝ mf x) (hgradb : fderiv ℝ b x = fderiv ℝ mb x)
    {F B M MB : ℝ}
    (hF : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ F)
    (hB : ∀ y ∈ interior C, σ * ε ≤ infDist y (frontier C) →
      ‖fderiv ℝ (fderiv ℝ b) y‖ ≤ B)
    (hM : ∀ y ∈ closedBall x Δ ∩ interior C, ‖fderiv ℝ (fderiv ℝ mf) y‖ ≤ M - 1)
    (hMB : ∀ y ∈ closedBall x Δ ∩ interior C, σ * ε ≤ infDist y (frontier C) →
      ‖fderiv ℝ (fderiv ℝ mb) y‖ ≤ MB)
    (hdec : Chapter06.HasSufficientModelDecrease (mf + mb) x s g
      (1 + ‖fderiv ℝ (fderiv ℝ (mf + mb)) x‖) Δ κ)
    (hsmall : Δ ≤ min (κ * ‖g‖ * (1 - P.η₂) / primalBarrierHessianConstant F B M MB)
      ((1 - σ) * ε))
    (hupdate : Chapter06.BTRRadiusUpdate P (primalBarrierRatio C σ (f + b) (mf + mb) x s) Δ Δ') :
    BarrierAdmissibleTrial C σ x (x + s) ∧
      P.η₂ ≤ primalBarrierRatio C σ (f + b) (mf + mb) x s ∧ Δ ≤ Δ' := by
  have hxC : x ∈ closedBall x Δ ∩ interior C := ⟨mem_closedBall_self hΔ.le, hx⟩
  have hσclear : σ * ε ≤ infDist x (frontier C) :=
    (mul_le_of_le_one_left hε.le hσ.2.le).trans hclear
  have hβ := (primalBarrier_model_curvature_le hΔ hx hmf hmb (hM x hxC) (hMB x hxC hσclear)).trans
    (le_max_right (F + B) (M + MB))
  have herr := (theorem_13_2_2 hC hσ hε hx hclear hs (hsmall.trans (min_le_right _ _))
    hf hb hmf hmb hvalf hvalb hgradf hgradb hF hB
    (fun y hy ↦ (hM y hy).trans (sub_le_self _ zero_le_one)) hMB).2
  exact theorem_13_2_3 hC hσ hε hx hclear (by positivity) hβ hΔ hg hs
    (congrArg₂ (· + ·) hvalf hvalb) hdec herr hsmall hupdate

end Geometry

/-- For the logarithmic barrier, the corrected separation result applies to
uniformly bounded positive iterates. A lower bound on the objective and an
upper bound on its barrier level supply the required barrier-value bound. -/
theorem logBarrier_bounded_level_separation {ι : Type*} [Fintype ι] [Nonempty ι]
    {μ L M U : ℝ} (hμ : 0 < μ) {f : (ι → ℝ) → ℝ} {x : ℕ → ι → ℝ}
    (hx : ∀ j i, 0 < x j i) (hM : ∀ j i, x j i ≤ M)
    (hf : ∀ j, L ≤ f (x j)) (hu : ∀ j, logBarrierObjective f (x j) μ ≤ U) :
    ∃ ε ∈ Ioo (0 : ℝ) 1, ∀ j, ε ≤ infDist (x j) (frontier (Optimization.nonnegativeOrthant ι)) := by
  have hi (j : ℕ) : x j ∈ interior (Optimization.nonnegativeOrthant ι) := by
    rw [Optimization.nonnegativeOrthant, interior_pi_set Set.finite_univ]
    simpa only [Set.mem_pi, Set.mem_univ, true_implies, interior_Ici, Set.mem_Ioi] using hx j
  have hb (j : ℕ) : logBarrier (x j) μ ≤ U - L := by
    have h := hu j
    unfold logBarrierObjective at h
    linarith [hf j]
  exact barrier_boundary_separation hi hb fun p _ hp ↦
    logBarrier_boundary_divergence hμ (fun j ↦ hx (p j)) (fun j ↦ hM (p j)) hp

/-- A lower-bounded objective and lower-bounded log-barrier objectives for
every positive parameter do not, by themselves, separate all fixed-level
points from the boundary. The two coordinates can compensate each other. -/
theorem logBarrier_unbounded_level_counterexample :
    ∃ (f : (Fin 2 → ℝ) → ℝ) (x : ℕ → Fin 2 → ℝ),
      ContDiff ℝ 2 f ∧ (∀ y, 0 ≤ f y) ∧
      (∀ μ > 0, ∃ L : ℝ, ∀ y : Fin 2 → ℝ, (∀ i, 0 < y i) →
        L ≤ logBarrierObjective f y μ) ∧
      (∀ j i, 0 < x j i) ∧ (∀ j, logBarrierObjective f (x j) 1 = 1) ∧
      Tendsto (fun j ↦ infDist (x j) (frontier (Optimization.nonnegativeOrthant (Fin 2))))
        atTop (𝓝 0) := by
  obtain ⟨x, hx, hd, hb, _⟩ := logBarrier_unbounded_boundary_counterexample
  let f (y : Fin 2 → ℝ) : ℝ := (y 0 * y 1) ^ 2
  have hf : ContDiff ℝ 2 f := by
    unfold f
    fun_prop
  refine ⟨f, x, hf, fun y ↦ sq_nonneg _, ?_, hx, ?_, hd⟩
  · intro μ hμ
    refine ⟨-(μ ^ 2 / 4), fun y hy ↦ ?_⟩
    have hlog : Real.log (y 0 * y 1) ≤ y 0 * y 1 :=
      Real.log_le_self (mul_nonneg (hy 0).le (hy 1).le)
    have hμlog := mul_le_mul_of_nonneg_left hlog hμ.le
    change -(μ ^ 2 / 4) ≤ (y 0 * y 1) ^ 2 + (-μ) * ∑ i, Real.log (y i)
    rw [Fin.sum_univ_two, ← Real.log_mul (hy 0).ne' (hy 1).ne']
    nlinarith [sq_nonneg (y 0 * y 1 - μ / 2)]
  · intro j
    have h := hb j
    change (-1 : ℝ) * ∑ i, Real.log (x j i) = 0 at h
    rw [Fin.sum_univ_two, ← Real.log_mul (hx j 0).ne' (hx j 1).ne'] at h
    have hlog : Real.log (x j 0 * x j 1) = 0 := by linarith
    have hprod : x j 0 * x j 1 = 1 := by
      have he := congrArg Real.exp hlog
      rwa [Real.exp_log (mul_pos (hx j 0) (hx j 1)), Real.exp_zero] at he
    change (x j 0 * x j 1) ^ 2 + logBarrier (x j) 1 = 1
    rw [hprod, hb j]
    norm_num

section GlobalLowerBound

variable {ι : Type*} [Fintype ι]

/-- Under a global lower bound on the objective and a bounded objective
Hessian, a lower bound on the log-barrier objective at a larger parameter
forces every fixed sublevel of the smaller-parameter barrier to be
bounded. The proof compares each point to its translate by the all-ones
vector, where every coordinate is at least one. -/
theorem logBarrier_sublevel_coordinate_bound {f : (ι → ℝ) → ℝ} {μ ν L A U H : ℝ}
    (hμ : 0 < μ) (hν : μ < ν) (hf : ContDiff ℝ 2 f)
    (hlower : ∀ y, L ≤ f y)
    (hH : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (hbar : ∀ y : ι → ℝ, (∀ i, 0 < y i) → A ≤ logBarrierObjective f y ν) :
    ∃ M : ℝ, ∀ x : ι → ℝ, (∀ i, 0 < x i) →
      logBarrierObjective f x μ ≤ U → ∀ i, x i ≤ M := by
  let e : ι → ℝ := fun _ ↦ 1
  let B := U + μ * ((U - A) / (ν - μ))
  let D := 2 * B - L + H * ‖e‖ ^ 2
  have hνpos : 0 < ν := hμ.trans hν
  have hDf := hf.fderiv_right (m := 1) (by norm_num)
  refine ⟨Real.exp ((D - A) / ν), fun x hx hlevel i ↦ ?_⟩
  have hbarx := hbar x hx
  change A ≤ f x + (-ν) * (∑ i, Real.log (x i)) at hbarx
  change f x + (-μ) * (∑ i, Real.log (x i)) ≤ U at hlevel
  have hlog : (∑ i, Real.log (x i)) ≤ (U - A) / (ν - μ) := by
    apply (le_div_iff₀ (sub_pos.mpr hν)).mpr
    linarith
  have hfB : f x ≤ B := by
    dsimp [B]
    linarith [mul_le_mul_of_nonneg_left hlog hμ.le]
  have htaylor (s : ι → ℝ) :
      |f (x + s) - (f x + fderiv ℝ f x s)| ≤ (1 / 2 : ℝ) * H * ‖s‖ ^ 2 := by
    rw [← Real.norm_eq_abs]
    exact norm_sub_firstOrder_le_of_hessian_bound (convex_univ : Convex ℝ (univ : Set (ι → ℝ)))
      (mem_univ x) (mem_univ (x + s))
      (fun z _ ↦ hf.differentiable (by norm_num) z)
      (fun z _ ↦ hDf.differentiable (by norm_num) z) (fun z _ ↦ hH z)
  have hforward := (abs_le.mp (htaylor e)).2
  have hback := (abs_le.mp (htaylor (-e))).2
  rw [map_neg, norm_neg] at hback
  have hfxe : f (x + e) ≤ D := by
    dsimp [D]
    linarith [hlower (x + -e)]
  have hy (j : ι) : 0 < (x + e) j := by
    change 0 < x j + 1
    linarith [hx j]
  have hbarxe := hbar (x + e) hy
  change A ≤ f (x + e) + (-ν) * ∑ j, Real.log ((x + e) j) at hbarxe
  have hs : (∑ j, Real.log ((x + e) j)) ≤ (D - A) / ν := by
    apply (le_div_iff₀ hνpos).mpr
    linarith
  have hp (j : ι) : 0 ≤ Real.log ((x + e) j) := by
    apply Real.log_nonneg
    change 1 ≤ x j + 1
    linarith [hx j]
  have hi := (Finset.single_le_sum (fun j _ ↦ hp j) (Finset.mem_univ i)).trans hs
  have he := Real.exp_le_exp.mpr hi
  rw [Real.exp_log (hy i)] at he
  change x i + 1 ≤ _ at he
  linarith

/-- The stronger global objective lower bound, together with AF.1, AF.3,
and AW.2 at a larger parameter, supplies the clearance needed in the
logarithmic barrier inner convergence proof. -/
theorem logBarrier_sublevel_separation_of_global_lower [Nonempty ι]
    {f : (ι → ℝ) → ℝ} {x : ℕ → ι → ℝ} {μ ν L A U H : ℝ}
    (hμ : 0 < μ) (hν : μ < ν) (hf : ContDiff ℝ 2 f)
    (hlower : ∀ y, L ≤ f y) (hH : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (hbar : ∀ y : ι → ℝ, (∀ i, 0 < y i) → A ≤ logBarrierObjective f y ν)
    (hx : ∀ j i, 0 < x j i) (hlevel : ∀ j, logBarrierObjective f (x j) μ ≤ U) :
    ∃ ε ∈ Ioo (0 : ℝ) 1, ∀ j,
      ε ≤ infDist (x j) (frontier (Optimization.nonnegativeOrthant ι)) := by
  obtain ⟨M, hM⟩ := logBarrier_sublevel_coordinate_bound hμ hν hf hlower hH hbar
  exact logBarrier_bounded_level_separation hμ hx (fun j ↦ hM (x j) (hx j) (hlevel j))
    (fun j ↦ hlower (x j)) hlevel

end GlobalLowerBound

private def barrierProjection (i : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj i

private noncomputable def barrierBilinearObjective (x : Fin 2 → ℝ) : ℝ := x 0 * x 1

private theorem barrierBilinearObjective_hessian (x : Fin 2 → ℝ) :
    fderiv ℝ (fderiv ℝ barrierBilinearObjective) x =
      (barrierProjection 0).smulRight (barrierProjection 1) +
        (barrierProjection 1).smulRight (barrierProjection 0) := by
  have hd (y : Fin 2 → ℝ) : fderiv ℝ barrierBilinearObjective y =
      y 0 • barrierProjection 1 + y 1 • barrierProjection 0 := by
    exact ((barrierProjection 0).hasFDerivAt.mul (barrierProjection 1).hasFDerivAt).fderiv
  rw [funext hd]
  have h := ((barrierProjection 0).hasFDerivAt (x := x) |>.smul_const (barrierProjection 1)).add
    ((barrierProjection 1).hasFDerivAt (x := x) |>.smul_const (barrierProjection 0))
  exact h.fderiv

/-- AF.1, AF.3, and AW.2 as printed in Theorem 13.4.2 do not imply
uniform clearance of log-barrier sublevels. For the bilinear objective
the Hessian is constant, and all the barrier objectives are bounded below
on the positive orthant. A constant-product path still approaches its
boundary. This refutes the sublevel-separation implication, independently
of whether a particular inner algorithm follows that path. -/
theorem logBarrier_level_clearance_counterexample_of_bounded_hessian :
    ∃ (f : (Fin 2 → ℝ) → ℝ) (x : ℕ → Fin 2 → ℝ),
      ContDiff ℝ 2 f ∧ (∃ H, ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H) ∧
      (∀ y : Fin 2 → ℝ, (∀ i, 0 < y i) → 0 ≤ f y) ∧
      (∀ μ > 0, ∃ A : ℝ, ∀ y : Fin 2 → ℝ, (∀ i, 0 < y i) →
        A ≤ logBarrierObjective f y μ) ∧
      (∀ j i, 0 < x j i) ∧ (∀ j, logBarrierObjective f (x j) 1 = 1) ∧
      Tendsto (fun j ↦ infDist (x j) (frontier (Optimization.nonnegativeOrthant (Fin 2))))
        atTop (𝓝 0) := by
  obtain ⟨x, hx, hd, hb, _⟩ := logBarrier_unbounded_boundary_counterexample
  refine ⟨barrierBilinearObjective, x, by unfold barrierBilinearObjective; fun_prop,
    ⟨_, fun y ↦ (congrArg norm (barrierBilinearObjective_hessian y)).le⟩,
    fun y hy ↦ mul_nonneg (hy 0).le (hy 1).le, ?_, hx, ?_, hd⟩
  · intro μ hμ
    refine ⟨μ - μ * Real.log μ, fun y hy ↦ ?_⟩
    have hp := mul_pos (hy 0) (hy 1)
    have hl := Real.log_le_sub_one_of_pos (div_pos hp hμ)
    rw [Real.log_div hp.ne' hμ.ne'] at hl
    have hmul := mul_le_mul_of_nonneg_left hl hμ.le
    simp only [mul_sub, mul_div_cancel₀ _ hμ.ne', mul_one] at hmul
    change μ - μ * Real.log μ ≤ y 0 * y 1 + (-μ) * ∑ i, Real.log (y i)
    rw [Fin.sum_univ_two, ← Real.log_mul (hy 0).ne' (hy 1).ne']
    linarith [hmul]
  · intro j
    have h := hb j
    change (-1 : ℝ) * ∑ i, Real.log (x j i) = 0 at h
    rw [Fin.sum_univ_two, ← Real.log_mul (hx j 0).ne' (hx j 1).ne'] at h
    have hlog : Real.log (x j 0 * x j 1) = 0 := by linarith
    have hprod : x j 0 * x j 1 = 1 := by
      have he := congrArg Real.exp hlog
      rwa [Real.exp_log (mul_pos (hx j 0) (hx j 1)), Real.exp_zero] at he
    change x j 0 * x j 1 + logBarrier (x j) 1 = 1
    rw [hprod, hb j, add_zero]

section FirstOrderLimit

open Chapter06

omit [NormedSpace ℝ E] in
private theorem PrimalBarrierInnerRun.delta_pos' {P : BTRParams} {C : Set E} {σ : ℝ}
    {φ : E → ℝ} (r : PrimalBarrierInnerRun P C σ φ) (j : ℕ) : 0 < r.Δ j := by
  induction j with
  | zero => exact r.initial_radius_pos
  | succ j ih => exact (r.radius_update j).pos ih

omit [NormedSpace ℝ E] in
private theorem PrimalBarrierInnerRun.objective_drop {P : BTRParams} {C : Set E} {σ : ℝ}
    {φ : E → ℝ} (r : PrimalBarrierInnerRun P C σ φ) {j : ℕ}
    (h : P.η₁ ≤ primalBarrierRatio C σ φ (r.model j) (r.x j) (r.s j)) :
    P.η₁ * (r.model j (r.x j) - r.model j (r.x j + r.s j)) ≤ φ (r.x j) - φ (r.x (j + 1)) := by
  classical
  have ha : BarrierAdmissibleTrial C σ (r.x j) (r.x j + r.s j) := by
    by_contra ha
    rw [primalBarrierRatio, ite_eq_right ha] at h
    exact P.eta₁_pos.not_ge h
  have hr := h
  rw [primalBarrierRatio, ite_eq_left ha, btrRatio, Optimization.reductionRatio] at hr
  rw [r.iterate_update, ite_eq_left h]
  exact (le_div_iff₀ (r.predicted_pos j)).mp hr

omit [NormedSpace ℝ E] in
private theorem PrimalBarrierInnerRun.value_tendsto {P : BTRParams} {C : Set E} {σ : ℝ}
    {φ : E → ℝ} (r : PrimalBarrierInnerRun P C σ φ)
    (hlower : BddBelow (range fun j ↦ φ (r.x j))) :
    Tendsto (fun j ↦ φ (r.x j)) atTop (𝓝 (⨅ j, φ (r.x j))) :=
  tendsto_atTop_ciInf r.objective_antitone hlower

omit [NormedSpace ℝ E] in
/-- A guarded inner run has arbitrarily small criticality values if
sufficiently short trials become very successful away from zero criticality,
and a successful trial with radius bounded below gives a uniform positive
objective decrease. This argument uses the actual guarded ratio. -/
theorem PrimalBarrierInnerRun.frequently_small_criticality
    {P : BTRParams} {C : Set E} {σ : ℝ} {φ : E → ℝ}
    (r : PrimalBarrierInnerRun P C σ φ) (a : ℕ → ℝ)
    (hlower : BddBelow (range fun j ↦ φ (r.x j)))
    (hvery : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ᶠ j in atTop, ε ≤ a j → r.Δ j ≤ δ →
      P.η₂ ≤ primalBarrierRatio C σ φ (r.model j) (r.x j) (r.s j))
    (hdrop : ∀ ε > (0 : ℝ), ∀ d > (0 : ℝ), ∃ q > (0 : ℝ), ∀ j,
      ε ≤ a j → d ≤ r.Δ j →
      P.η₁ ≤ primalBarrierRatio C σ φ (r.model j) (r.x j) (r.s j) →
      q ≤ φ (r.x j) - φ (r.x (j + 1))) :
    ∀ ε > (0 : ℝ), ∃ᶠ j in atTop, a j < ε := by
  intro ε hε
  by_contra! hn
  obtain ⟨δ, hδ, hvery⟩ := hvery ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hn.and hvery)
  let d := min (r.Δ N) (P.γ₁ * δ)
  have hd : 0 < d := lt_min (r.delta_pos' N) (mul_pos P.gamma₁_pos hδ)
  have hrad (j : ℕ) (hj : N ≤ j) : d ≤ r.Δ j := by
    induction j, hj using Nat.le_induction with
    | base => exact min_le_left _ _
    | succ j hj ih =>
      let ρ := primalBarrierRatio C σ φ (r.model j) (r.x j) (r.s j)
      have hu := r.radius_update j
      by_cases hv : P.η₂ ≤ ρ
      · exact ih.trans (hu.very_successful hv)
      · have hΔ : δ < r.Δ j := lt_of_not_ge (fun h ↦ hv ((hN j hj).2 (hN j hj).1 h))
        have hstep : P.γ₁ * r.Δ j ≤ r.Δ (j + 1) := by
          by_cases hs : P.η₁ ≤ ρ
          · exact (mul_le_mul_of_nonneg_right P.gamma₁_le_gamma₂ (r.delta_pos' j).le).trans
              (hu.successful hs (lt_of_not_ge hv)).1
          · exact (hu.unsuccessful (lt_of_not_ge hs)).1
        exact (min_le_right _ _).trans
          ((mul_le_mul_of_nonneg_left hΔ.le P.gamma₁_pos.le).trans hstep)
  obtain ⟨q, hq, hdrop⟩ := hdrop ε hε d hd
  have ht := r.value_tendsto hlower
  have hdiff : Tendsto (fun j ↦ φ (r.x j) - φ (r.x (j + 1))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using ht.sub (ht.comp (tendsto_add_atTop_nat 1))
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hdiff.eventually (gt_mem_nhds hq))
  let I := max N J
  have hfail (j : ℕ) (hj : I ≤ j) :
      primalBarrierRatio C σ φ (r.model j) (r.x j) (r.s j) < P.η₁ := by
    have hn := (le_max_left N J).trans hj
    exact lt_of_not_ge (fun h ↦ (hJ j ((le_max_right N J).trans hj)).not_ge
      (hdrop j (hN j hn).1 (hrad j hn) h))
  have hγ := P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂
  have hshrink (j : ℕ) : r.Δ (I + j) ≤ P.γ₂ ^ j * r.Δ I := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hp := ((r.radius_update (I + j)).unsuccessful
        (hfail (I + j) (Nat.le_add_right _ _))).2
      rw [show I + (j + 1) = I + j + 1 by omega]
      exact hp.trans ((mul_le_mul_of_nonneg_left ih hγ.le).trans_eq (by rw [pow_succ]; ring))
  have hlim : Tendsto (fun j : ℕ ↦ P.γ₂ ^ j * r.Δ I) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hγ.le P.gamma₂_lt_one).mul_const (r.Δ I)
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hd)).exists
  exact hj.not_ge ((hrad _ ((le_max_left N J).trans (Nat.le_add_right I j))).trans (hshrink j))

/-- The first-order inner limit of Algorithm 13.2.1 under fixed clearance,
the uniform short-trial Taylor estimate, and a Lipschitz bound on the
variation of the criticality measure between successive iterates. The
fraction-to-boundary sentinel is kept throughout the acceptance proof. -/
theorem PrimalBarrierInnerRun.gradient_norm_tendsto_zero
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {P : BTRParams} {C : Set F} {σ : ℝ} {φ : F → ℝ}
    (r : PrimalBarrierInnerRun P C σ φ) (hC : C ≠ univ)
    (hσ : σ ∈ Ioo (0 : ℝ) 1) {δ : ℝ} (hδ : 0 < δ)
    (hclear : ∀ j, δ ≤ infDist (r.x j) (frontier C))
    (g : ℕ → F) (β : ℕ → ℝ) {κ K L : ℝ}
    (hβ : ∀ j, 0 < β j) (hβK : ∀ j, β j ≤ K) (hL : 0 ≤ L)
    (hval : ∀ j, φ (r.x j) = r.model j (r.x j))
    (hdec : ∀ j, HasSufficientModelDecrease (r.model j) (r.x j) (r.s j) (g j) (β j) (r.Δ j) κ)
    (herr : ∀ j, r.Δ j ≤ (1 - σ) * δ →
      |φ (r.x j + r.s j) - r.model j (r.x j + r.s j)| ≤ K * (r.Δ j) ^ 2)
    (hlower : BddBelow (range fun j ↦ φ (r.x j)))
    (hvar : ∀ j, ‖g j‖ - ‖g (j + 1)‖ ≤ L * ‖r.x j - r.x (j + 1)‖) :
    Tendsto (fun j ↦ ‖g j‖) atTop (𝓝 0) := by
  let u (j : ℕ) := ‖g j‖
  let v (j : ℕ) := φ (r.x j)
  have hκ := (hdec 0).1.1
  have hK := (hβ 0).trans_le (hβK 0)
  have hgap : 0 < 1 - P.η₂ := sub_pos.mpr P.eta₂_lt_one
  have hclearance : 0 < (1 - σ) * δ := mul_pos (sub_pos.mpr hσ.2) hδ
  have hdrop {e : ℝ} (he : 0 < e) {j : ℕ} (hu : e ≤ u j)
      (hs : P.η₁ ≤ primalBarrierRatio C σ φ (r.model j) (r.x j) (r.s j)) :
      (P.η₁ * (κ * e)) * min (e / K) (r.Δ j) ≤ v j - v (j + 1) := by
    have hquot := div_le_div₀ (norm_nonneg (g j)) hu (hβ j) (hβK j)
    have hm := min_le_min hquot (le_refl (r.Δ j))
    have hp := (mul_le_mul (mul_le_mul_of_nonneg_left hu hκ.le) hm
      (le_min (div_nonneg he.le hK.le) (r.delta_pos' j).le) (by positivity)).trans (hdec j).2
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left hp P.eta₁_pos.le).trans (r.objective_drop hs)
  have hfreq : ∀ e > (0 : ℝ), ∃ᶠ j in atTop, u j < e := by
    apply r.frequently_small_criticality u hlower
    · intro e he
      let D := min (κ * e * (1 - P.η₂) / K) ((1 - σ) * δ)
      refine ⟨D, lt_min (div_pos (mul_pos (mul_pos hκ he) hgap) hK) hclearance,
        Eventually.of_forall fun j hu hD ↦ ?_⟩
      have hg : g j ≠ 0 := norm_pos_iff.mp (he.trans_le hu)
      have hsmall : r.Δ j ≤ min (κ * ‖g j‖ * (1 - P.η₂) / K) ((1 - σ) * δ) :=
        le_min ((hD.trans (min_le_left _ _)).trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu hκ.le) hgap.le) hK.le))
          (hD.trans (min_le_right _ _))
      exact (theorem_13_2_3 hC hσ hδ (r.interior_iterate j) (hclear j) (hβ j) (hβK j)
        (r.delta_pos' j) hg (r.step_feasible j) (hval j) (hdec j)
        (herr j (hD.trans (min_le_right _ _))) hsmall (r.radius_update j)).2.1
    · intro e he d hd
      refine ⟨(P.η₁ * (κ * e)) * min (e / K) d,
        mul_pos (mul_pos P.eta₁_pos (mul_pos hκ he)) (lt_min (div_pos he hK) hd),
        fun j hu hj hs ↦ ?_⟩
      exact (mul_le_mul_of_nonneg_left (min_le_min le_rfl hj)
        (mul_nonneg P.eta₁_pos.le (mul_nonneg hκ.le he.le))).trans (hdrop he hu hs)
  have ht := r.value_tendsto hlower
  have hdiff : Tendsto (fun j ↦ v j - v (j + 1)) atTop (𝓝 0) := by
    simpa only [v, Function.comp_apply, sub_self] using ht.sub (ht.comp (tendsto_add_atTop_nat 1))
  have htail : Tendsto (fun j ↦ v j - ⨅ i, v i) atTop (𝓝 0) := by
    simpa only [v, sub_self] using ht.sub_const (⨅ i, v i)
  rw [Metric.tendsto_atTop]
  intro ε hε
  let e := ε / 2
  have he : 0 < e := half_pos hε
  let c := P.η₁ * (κ * e)
  have hc : 0 < c := mul_pos P.eta₁_pos (mul_pos hκ he)
  have hL1 : 0 < L + 1 := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hdiff.eventually (gt_mem_nhds (mul_pos hc (div_pos he hK))))
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (htail.eventually (gt_mem_nhds (div_pos (mul_pos hc he) hL1)))
  have hstep (j : ℕ) (hj : N ≤ j) (huj : e ≤ u j) :
      c * (u j - u (j + 1)) ≤ L * (v j - v (j + 1)) := by
    let ρ := primalBarrierRatio C σ φ (r.model j) (r.x j) (r.s j)
    by_cases hs : P.η₁ ≤ ρ
    · have hd := hdrop he huj hs
      have hr : r.Δ j ≤ e / K := by
        by_contra! hn
        rw [min_eq_left hn.le] at hd
        exact (hN j hj).not_ge hd
      rw [min_eq_right hr] at hd
      have hv := hvar j
      rw [r.iterate_update, ite_eq_left hs, sub_add_cancel_left, norm_neg] at hv
      have hstep := hv.trans (mul_le_mul_of_nonneg_left (r.step_feasible j) hL)
      calc
        _ ≤ c * (L * r.Δ j) := mul_le_mul_of_nonneg_left hstep hc.le
        _ = L * (c * r.Δ j) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hd hL
    · have heq : r.x (j + 1) = r.x j := by rw [r.iterate_update, ite_eq_right hs]
      have hh := hvar j
      rw [heq, sub_self, norm_zero, mul_zero] at hh
      simpa only [v, heq, sub_self, mul_zero] using mul_nonpos_of_nonneg_of_nonpos hc.le hh
  refine ⟨max N J, fun k hk ↦ ?_⟩
  change dist (u k) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  by_contra! hhigh
  have hex := frequently_atTop.mp (hfreq e he) k
  let j := Nat.find hex
  have hj : k ≤ j ∧ u j < e := Nat.find_spec hex
  have htel (i : ℕ) (hi : k ≤ i) : i ≤ j →
      c * (u k - u i) ≤ L * (v k - v i) := by
    induction i, hi using Nat.le_induction with
    | base => simp
    | succ i hi ih =>
      intro hij
      have hb : i < j := Nat.lt_of_succ_le hij
      have hui : e ≤ u i := le_of_not_gt fun hh ↦ (Nat.find_min hex hb) ⟨hi, hh⟩
      linarith only [ih hb.le, hstep i (((le_max_left N J).trans hk).trans hi) hui]
  have hgap' : e < u k - u j := by dsimp [e] at hj ⊢; linarith [hj.2]
  have hb : v k - ⨅ i, v i < c * e / (L + 1) := hJ k ((le_max_right N J).trans hk)
  have hvle : (⨅ i, v i) ≤ v j := ciInf_le hlower j
  have hdval : 0 ≤ v k - v j := sub_nonneg.mpr (r.objective_antitone hj.1)
  have hlast : L * (v k - v j) < c * e := calc
    _ ≤ (L + 1) * (v k - v j) := by gcongr; linarith
    _ ≤ (L + 1) * (v k - ⨅ i, v i) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hvle _) hL1.le
    _ < _ := by
      have hh := (lt_div_iff₀ hL1).mp hb
      rwa [mul_comm]
  exact hlast.not_ge ((mul_le_mul_of_nonneg_left hgap'.le hc.le).trans (htel j hj.1 le_rfl))

/-- The second-order inner curvature bound of Algorithm 13.2.1. The
normalized model error is required only on sufficiently short trials,
which pass the fraction-to-boundary test by the uniform clearance. -/
theorem PrimalBarrierInnerRun.frequently_near_nonnegative_curvature
    [FiniteDimensional ℝ E] {P : BTRParams} {C : Set E} {σ : ℝ} {φ : E → ℝ}
    (r : PrimalBarrierInnerRun P C σ φ) (hC : C ≠ univ)
    (hσ : σ ∈ Ioo (0 : ℝ) 1) {δ : ℝ} (hδ : 0 < δ)
    (hclear : ∀ j, δ ≤ infDist (r.x j) (frontier C))
    {curv τ : ℕ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hval : ∀ j, φ (r.x j) = r.model j (r.x j))
    (hdec : ∀ j, HasNegativeCurvatureDecrease (r.model j) (r.x j) (r.s j)
      (τ j) (r.Δ j) κ)
    (herr : ∀ e > (0 : ℝ), ∃ D > (0 : ℝ), ∀ᶠ j in atTop, r.Δ j ≤ D →
      |φ (r.x j + r.s j) - r.model j (r.x j + r.s j)| ≤ e * (r.Δ j) ^ 2)
    (hagree : Tendsto (fun j ↦ |curv j - τ j|) atTop (𝓝 0))
    (hlower : BddBelow (range fun j ↦ φ (r.x j))) :
    ∀ ε > (0 : ℝ), ∃ᶠ j in atTop, -ε < curv j := by
  have hη : 0 < 1 - P.η₂ := sub_pos.mpr P.eta₂_lt_one
  have hΔc : 0 < (1 - σ) * δ := mul_pos (sub_pos.mpr hσ.2) hδ
  have hfreq : ∀ e > (0 : ℝ), ∃ᶠ j in atTop, -τ j < e := by
    apply r.frequently_small_criticality (fun j ↦ -τ j) hlower
    · intro e he
      obtain ⟨D, hD, hsmall⟩ := herr ((1 - P.η₂) * (κ * e)) (by positivity)
      refine ⟨min e (min D ((1 - σ) * δ)), lt_min he (lt_min hD hΔc), ?_⟩
      filter_upwards [hsmall] with j herr hj hd
      have hD' := hd.trans (min_le_right _ _)
      have hstep : dist (r.x j + r.s j) (r.x j) ≤
          (1 - σ) * infDist (r.x j) (frontier C) := by
        rw [dist_eq_norm, add_sub_cancel_left]
        exact (r.step_feasible j).trans ((hD'.trans (min_le_right _ _)).trans
          (mul_le_mul_of_nonneg_left (hclear j) (sub_nonneg.mpr hσ.2.le)))
      have ha := (barrierBoundary_clearance hC (r.interior_iterate j) hσ hδ (hclear j) hstep).1
      have hp := negativeCurvatureDecrease_lower_bound (hdec j) he (r.delta_pos' j).le
        le_rfl (by linarith : τ j ≤ -e)
      rw [min_eq_right ((sq_le_sq₀ (r.delta_pos' j).le he.le).mpr
        (hd.trans (min_le_left _ _)))] at hp
      have heq : |φ (r.x j + r.s j) -
          (φ (r.x j) - (r.model j (r.x j) - r.model j (r.x j + r.s j)))| ≤
          (1 - P.η₂) * (r.model j (r.x j) - r.model j (r.x j + r.s j)) := by
        rw [hval j, sub_sub_cancel]
        exact (herr (hD'.trans (min_le_left _ _))).trans
          (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hη.le)
      rw [primalBarrierRatio, ite_eq_left ha, btrRatio]
      simpa only [sub_sub_cancel] using
        Optimization.le_reductionRatio_of_abs_sub_le (r.predicted_pos j) heq
    · intro e he d hd
      refine ⟨P.η₁ * (κ * e * min (e ^ 2) (d ^ 2)), mul_pos P.eta₁_pos
        (mul_pos (mul_pos hκ he) (lt_min (sq_pos_of_pos he) (sq_pos_of_pos hd))),
        fun j hj hrad hs ↦ ?_⟩
      exact (mul_le_mul_of_nonneg_left
        (negativeCurvatureDecrease_lower_bound (hdec j) he hd.le hrad (by linarith))
        P.eta₁_pos.le).trans (r.objective_drop hs)
  intro ε hε
  refine ((hfreq (ε / 2) (half_pos hε)).and_eventually
    (hagree.eventually (gt_mem_nhds (half_pos hε)))).mono ?_
  intro j hj
  linarith [neg_abs_le (curv j - τ j), hj.1, hj.2]

private theorem barrier_hessian_sub {f m : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hm : ContDiffAt ℝ 2 m x) :
    fderiv ℝ (fderiv ℝ (f - m)) x =
      fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ m) x := by
  have he : fderiv ℝ (f - m) =ᶠ[𝓝 x] fderiv ℝ f - fderiv ℝ m := by
    filter_upwards [hf.eventually (by norm_num), hm.eventually (by norm_num)] with y hfy hmy
    exact ((hfy.differentiableAt (by norm_num)).hasFDerivAt.sub
      (hmy.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hdf := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hdm := ((hm.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  rw [he.fderiv_eq]
  exact (hdf.hasFDerivAt.sub hdm.hasFDerivAt).fderiv

/-- Center Hessian agreement and uniform Hessian variation on short
interior trust regions give the normalized model error used by the
second-order inner convergence proof. -/
theorem PrimalBarrierInnerRun.small_radius_model_error_of_hessians
    [FiniteDimensional ℝ E] {P : BTRParams} {C : Set E} {σ : ℝ} {φ : E → ℝ}
    (r : PrimalBarrierInnerRun P C σ φ) (hC : C ≠ univ)
    (hσ : σ ∈ Ioo (0 : ℝ) 1) {δ : ℝ} (hδ : 0 < δ)
    (hclear : ∀ j, δ ≤ infDist (r.x j) (frontier C))
    (hf : ∀ y ∈ interior C, ContDiffAt ℝ 2 φ y)
    (hm : ∀ j y, y ∈ closedBall (r.x j) (r.Δ j) → y ∈ interior C →
      ContDiffAt ℝ 2 (r.model j) y)
    (hval : ∀ j, φ (r.x j) = r.model j (r.x j))
    (hgrad : ∀ j, fderiv ℝ φ (r.x j) = fderiv ℝ (r.model j) (r.x j))
    (hagree : Tendsto (fun j ↦ ‖fderiv ℝ (fderiv ℝ φ) (r.x j) -
      fderiv ℝ (fderiv ℝ (r.model j)) (r.x j)‖) atTop (𝓝 0))
    (hvar : ∀ e > (0 : ℝ), ∃ D > (0 : ℝ), ∀ j, r.Δ j ≤ D →
      ∀ y ∈ closedBall (r.x j) (r.Δ j), y ∈ interior C →
        ‖fderiv ℝ (fderiv ℝ φ) y - fderiv ℝ (fderiv ℝ φ) (r.x j)‖ +
        ‖fderiv ℝ (fderiv ℝ (r.model j)) y -
          fderiv ℝ (fderiv ℝ (r.model j)) (r.x j)‖ ≤ e) :
    ∀ e > (0 : ℝ), ∃ D > (0 : ℝ), ∀ᶠ j in atTop, r.Δ j ≤ D →
      |φ (r.x j + r.s j) - r.model j (r.x j + r.s j)| ≤ e * (r.Δ j) ^ 2 := by
  intro e he
  obtain ⟨D, hD, hv⟩ := hvar e he
  refine ⟨min D ((1 - σ) * δ), lt_min hD (mul_pos (sub_pos.mpr hσ.2) hδ), ?_⟩
  filter_upwards [hagree.eventually (gt_mem_nhds he)] with j hj hrad
  have hΔ := (r.delta_pos' j).le
  have hins (y : E) (hy : y ∈ closedBall (r.x j) (r.Δ j)) : y ∈ interior C :=
    (barrierBoundary_clearance hC (r.interior_iterate j) hσ hδ (hclear j)
      ((mem_closedBall.mp hy).trans ((hrad.trans (min_le_right _ _)).trans
        (mul_le_mul_of_nonneg_left (hclear j) (sub_nonneg.mpr hσ.2.le))))).1.1
  have hB (y : E) (hy : y ∈ closedBall (r.x j) (r.Δ j)) :
      ‖fderiv ℝ (fderiv ℝ (φ - r.model j)) y‖ ≤ 2 * e := by
    let F := fderiv ℝ (fderiv ℝ φ)
    let M := fderiv ℝ (fderiv ℝ (r.model j))
    rw [barrier_hessian_sub (hf y (hins y hy)) (hm j y hy (hins y hy))]
    change ‖F y - M y‖ ≤ 2 * e
    rw [show F y - M y = (F y - F (r.x j)) + (F (r.x j) - M (r.x j)) -
      (M y - M (r.x j)) by abel]
    have htri := norm_sub_le ((F y - F (r.x j)) + (F (r.x j) - M (r.x j)))
      (M y - M (r.x j))
    have hsum := norm_add_le (F y - F (r.x j)) (F (r.x j) - M (r.x j))
    change ‖F (r.x j) - M (r.x j)‖ < e at hj
    have hh := hv j (hrad.trans (min_le_left _ _)) y hy (hins y hy)
    change ‖F y - F (r.x j)‖ + ‖M y - M (r.x j)‖ ≤ e at hh
    linarith only [htri, hsum, hj, hh]
  have ht := barrierTaylorRemainder (F := φ - r.model j) hΔ (r.step_feasible j)
    (fun y hy ↦ (hf y (hins y hy)).sub (hm j y hy (hins y hy))) hB
  have hd : fderiv ℝ (φ - r.model j) (r.x j) = 0 := by
    have hx := r.interior_iterate j
    have hcx : r.x j ∈ closedBall (r.x j) (r.Δ j) := mem_closedBall_self hΔ
    rw [((hf _ hx).differentiableAt (by norm_num)).hasFDerivAt.sub
      ((hm j _ hcx hx).differentiableAt (by norm_num)).hasFDerivAt |>.fderiv,
      hgrad, sub_self]
  simp only [Pi.sub_apply, hval, sub_self, hd, zero_apply, add_zero,
    sub_zero] at ht
  have hs := (sq_le_sq₀ (norm_nonneg _) hΔ).mpr (r.step_feasible j)
  nlinarith only [ht, mul_le_mul_of_nonneg_left hs he.le]

/-- A uniform Hessian bound on a convex region containing the accepted
iterates supplies the gradient variation estimate for Algorithm 13.2.1. -/
theorem PrimalBarrierInnerRun.gradient_norm_variation_of_hessian_bound
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {P : BTRParams} {C S : Set F} {σ : ℝ} {φ : F → ℝ}
    (r : PrimalBarrierInnerRun P C σ φ)
    (hS : Convex ℝ S) (hx : ∀ j, r.x j ∈ S)
    (hf : ∀ x ∈ S, ContDiffAt ℝ 2 φ x)
    {L : ℝ} (hH : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ L) :
    ∀ j, ‖gradient φ (r.x j)‖ - ‖gradient φ (r.x (j + 1))‖ ≤
      L * ‖r.x j - r.x (j + 1)‖ := by
  intro j
  have he := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x h ↦ ((hf x h).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    hH hS (hx (j + 1)) (hx j)
  exact (norm_sub_norm_le _ _).trans (by
    simpa only [gradient, ← map_sub, LinearIsometryEquiv.norm_map] using he)

end FirstOrderLimit

end ConnGouldToint.Chapter13
