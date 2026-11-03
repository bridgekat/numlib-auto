import NumlibSurface.ConnGouldToint.Chapter06.Section04
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

end ConnGouldToint.Chapter13
