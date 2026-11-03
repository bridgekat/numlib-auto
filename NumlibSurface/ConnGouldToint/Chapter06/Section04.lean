import Numlib.Analysis.Calculus.Taylor
import NumlibSurface.ConnGouldToint.Chapter06.Section03

/-! # Convergence to first-order critical points -/

namespace ConnGouldToint.Chapter06

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The ratio (6.4.2) of the step norm to its trust-region norm. -/
noncomputable def stepNormRatio (p : Seminorm ℝ E) (s : E) : ℝ :=
  ‖s‖ / p s

/-- The uniform error constant (6.4.4) from norm equivalence and Hessian bounds. -/
noncomputable def uniformHessianConstant (K κf κm : ℝ) : ℝ :=
  K ^ 2 * max κf κm

/-- Theorem 6.4.1. Agreement of the function and model values and derivatives
at the center gives quadratic accuracy throughout the trust region. -/
theorem theorem_6_4_1 {f m : E → ℝ} {x s : E} (p : Seminorm ℝ E)
    (hp : ∀ v, p v = 0 → v = 0) {Δ κf κm : ℝ} (hΔ : 0 ≤ Δ) (hκm : 1 ≤ κm)
    (hs : p s ≤ Δ) (hf : ContDiff ℝ 2 f)
    (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ κf)
    (hm : ∀ z ∈ p.closedBall x Δ, DifferentiableAt ℝ m z)
    (hDm : ∀ z ∈ p.closedBall x Δ, DifferentiableAt ℝ (fderiv ℝ m) z)
    (hM : ∀ z ∈ p.closedBall x Δ, ‖fderiv ℝ (fderiv ℝ m) z‖ ≤ κm - 1)
    (hval : m x = f x) (hgrad : fderiv ℝ m x = fderiv ℝ f x) :
    |f (x + s) - m (x + s)| ≤ stepNormRatio p s ^ 2 * max κf κm * Δ ^ 2 ∧
      ∀ K : ℝ, 0 ≤ K → (∀ v, ‖v‖ ≤ K * p v) →
        |f (x + s) - m (x + s)| ≤ uniformHessianConstant K κf κm * Δ ^ 2 := by
  let B := max κf κm
  have hB : 0 ≤ B := (by linarith : 0 ≤ κm).trans (le_max_right _ _)
  have hxs : x + s ∈ p.closedBall x Δ := by
    rw [Seminorm.mem_closedBall, add_sub_cancel_left]
    exact hs
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h₁ := norm_sub_firstOrder_le_of_hessian_bound (convex_univ : Convex ℝ (Set.univ : Set E))
    (Set.mem_univ x) (Set.mem_univ (x + s))
    (fun z _ ↦ hf.differentiable (by norm_num) z)
    (fun z _ ↦ hDf.differentiable (by norm_num) z)
    (fun z _ ↦ (hF z).trans (le_max_left κf κm))
  have h₂ := norm_sub_firstOrder_le_of_hessian_bound (p.convex_closedBall x Δ)
    (p.mem_closedBall_self hΔ) hxs hm hDm
    (fun z hz ↦ (hM z hz).trans ((by linarith : κm - 1 ≤ κm).trans (le_max_right κf κm)))
  rw [Real.norm_eq_abs] at h₁ h₂
  rw [hval, hgrad] at h₂
  have herror : |f (x + s) - m (x + s)| ≤ B * ‖s‖ ^ 2 := by
    rcases abs_le.mp h₁ with ⟨h₁l, h₁u⟩
    rcases abs_le.mp h₂ with ⟨h₂l, h₂u⟩
    exact abs_le.mpr ⟨by linarith [h₁l, h₂u], by linarith [h₁u, h₂l]⟩
  constructor
  · by_cases hzero : s = 0
    · simp [hzero, hval, stepNormRatio]
    have hp₀ : 0 < p s := lt_of_le_of_ne (apply_nonneg p s) (fun h ↦ hzero (hp s h.symm))
    have hratio : 0 ≤ stepNormRatio p s := div_nonneg (norm_nonneg _) hp₀.le
    have hstep : ‖s‖ ≤ stepNormRatio p s * Δ := by
      calc
        ‖s‖ = stepNormRatio p s * p s := (div_mul_cancel₀ _ hp₀.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hs hratio
    calc
      _ ≤ B * ‖s‖ ^ 2 := herror
      _ ≤ B * (stepNormRatio p s * Δ) ^ 2 := by gcongr
      _ = _ := by dsimp [B]; ring
  · intro K hK hnorm
    have hstep := (hnorm s).trans (mul_le_mul_of_nonneg_left hs hK)
    calc
      _ ≤ B * ‖s‖ ^ 2 := herror
      _ ≤ B * (K * Δ) ^ 2 := by gcongr
      _ = _ := by unfold uniformHessianConstant; ring

omit [NormedSpace ℝ E] in
/-- Theorem 6.4.2. Under the quadratic error bound (6.4.3), a small enough radius
gives a very successful iteration. The curvature bound β is at most the error
constant C by (6.3.2) and (6.4.4). -/
theorem theorem_6_4_2 {P : BTRParams} {f m : E → ℝ} {x s g : E}
    {β Δ Δ' κ C : ℝ} (hβ : 0 < β) (hβC : β ≤ C) (hΔ : 0 < Δ) (hg : g ≠ 0)
    (hval : f x = m x) (hdec : HasSufficientModelDecrease m x s g β Δ κ)
    (herr : |f (x + s) - m (x + s)| ≤ C * Δ ^ 2)
    (hsmall : Δ ≤ κ * ‖g‖ * (1 - P.η₂) / C)
    (hupdate : BTRRadiusUpdate P (btrRatio f m x s) Δ Δ') :
    P.η₂ ≤ btrRatio f m x s ∧ Δ ≤ Δ' := by
  have hC : 0 < C := hβ.trans_le hβC
  have hη : 0 < P.η₂ := P.eta₁_pos.trans_le P.eta₁_le_eta₂
  have hη' : 0 ≤ 1 - P.η₂ := sub_nonneg.mpr P.eta₂_lt_one.le
  have hκ : 0 < κ := hdec.1.1
  have hκ' : κ < 1 := hdec.1.2
  have hgn : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have hsmall' := (le_div_iff₀ hC).mp hsmall
  have hfactor : κ * (1 - P.η₂) ≤ 1 :=
    (mul_le_of_le_one_right hκ.le (by linarith)).trans hκ'.le
  have hΔβ : Δ ≤ ‖g‖ / β := by
    apply (le_div_iff₀ hβ).mpr
    calc
      Δ * β ≤ Δ * C := mul_le_mul_of_nonneg_left hβC hΔ.le
      _ ≤ κ * ‖g‖ * (1 - P.η₂) := hsmall'
      _ = (κ * (1 - P.η₂)) * ‖g‖ := by ring
      _ ≤ ‖g‖ := mul_le_of_le_one_left hgn.le hfactor
  have hlower := hdec.2
  rw [min_eq_right hΔβ] at hlower
  have hpred : 0 < m x - m (x + s) := (mul_pos (mul_pos hκ hgn) hΔ).trans_le hlower
  have hprod := mul_le_mul_of_nonneg_right hsmall' hΔ.le
  have hbound := mul_le_mul_of_nonneg_left hlower hη'
  have herr' : |f (x + s) - (f x - (m x - m (x + s)))| ≤
      (1 - P.η₂) * (m x - m (x + s)) := by
    rw [hval, sub_sub_cancel]
    exact herr.trans (by nlinarith only [hprod, hbound])
  have hsuccess : P.η₂ ≤ btrRatio f m x s := by
    simpa [btrRatio] using Optimization.le_reductionRatio_of_abs_sub_le hpred herr'
  exact ⟨hsuccess, hupdate.very_successful hsuccess⟩

/-- Theorem 6.4.3. Uniformly nonzero gradients keep the radius bounded away
from zero. The explicit bound includes the initial radius. -/
theorem theorem_6_4_3 {P : BTRParams} {f : E → ℝ}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop} (run : BTRRun f P sufficient)
    (g : ℕ → E) (β : ℕ → ℝ) {κ C gmin : ℝ} (hgmin : 0 < gmin)
    (hg : ∀ k, gmin ≤ ‖g k‖) (hβ : ∀ k, 0 < β k) (hβC : ∀ k, β k ≤ C)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (g k) (β k) (run.Δ k) κ)
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤
      C * (run.Δ k) ^ 2) :
    ∃ r > 0, ∀ k, r ≤ run.Δ k := by
  let θ := κ * gmin * (1 - P.η₂) / C
  have hκ : 0 < κ := (hdec 0).1.1
  have hC : 0 < C := (hβ 0).trans_le (hβC 0)
  have hη : 0 < 1 - P.η₂ := sub_pos.mpr P.eta₂_lt_one
  have hθ : 0 < θ := div_pos (mul_pos (mul_pos hκ hgmin) hη) hC
  refine ⟨min (run.Δ 0) (P.γ₁ * θ), lt_min (run.delta_pos 0) (mul_pos P.gamma₁_pos hθ),
    run.delta_lower_bound ?_⟩
  intro k hk
  have hsmall : run.Δ k ≤ κ * ‖g k‖ * (1 - P.η₂) / C := by
    exact hk.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hg k) hκ.le) hη.le) hC.le)
  have hg₀ : g k ≠ 0 := norm_pos_iff.mp (hgmin.trans_le (hg k))
  exact (theorem_6_4_2 (hβ k) (hβC k) (run.delta_pos k) hg₀ (hval k) (hdec k)
    (herr k) hsmall (run.radius_update k)).1

end ConnGouldToint.Chapter06
