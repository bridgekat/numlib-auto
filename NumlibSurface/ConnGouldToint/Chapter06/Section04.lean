import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Numlib.Analysis.Calculus.Taylor
import NumlibSurface.ConnGouldToint.Chapter06.Section03

/-! # Convergence to first-order critical points -/

open Filter Topology

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
/-- A small radius ensures very successful acceptance when the decrease bound
uses a positive scalar criticality measure. -/
theorem btrRatio_ge_eta₂_of_small_radius_of_decrease {P : BTRParams}
    {f m : E → ℝ} {x s : E} {β Δ κ C a : ℝ}
    (hβ : 0 < β) (hβC : β ≤ C) (hΔ : 0 < Δ) (ha : 0 < a)
    (hκ : 0 < κ) (hκ' : κ < 1) (hval : f x = m x)
    (hdec : κ * a * min (a / β) Δ ≤ m x - m (x + s))
    (herr : |f (x + s) - m (x + s)| ≤ C * Δ ^ 2)
    (hsmall : Δ ≤ κ * a * (1 - P.η₂) / C) :
    P.η₂ ≤ btrRatio f m x s := by
  have hC : 0 < C := hβ.trans_le hβC
  have hη : 0 < P.η₂ := P.eta₁_pos.trans_le P.eta₁_le_eta₂
  have hη' : 0 ≤ 1 - P.η₂ := sub_nonneg.mpr P.eta₂_lt_one.le
  have hsmall' := (le_div_iff₀ hC).mp hsmall
  have hfactor : κ * (1 - P.η₂) ≤ 1 :=
    (mul_le_of_le_one_right hκ.le (by linarith)).trans hκ'.le
  have hΔβ : Δ ≤ a / β := by
    apply (le_div_iff₀ hβ).mpr
    calc
      Δ * β ≤ Δ * C := mul_le_mul_of_nonneg_left hβC hΔ.le
      _ ≤ κ * a * (1 - P.η₂) := hsmall'
      _ = (κ * (1 - P.η₂)) * a := by ring
      _ ≤ a := mul_le_of_le_one_left ha.le hfactor
  have hlower := hdec
  rw [min_eq_right hΔβ] at hlower
  have hpred : 0 < m x - m (x + s) := (mul_pos (mul_pos hκ ha) hΔ).trans_le hlower
  have hprod := mul_le_mul_of_nonneg_right hsmall' hΔ.le
  have hbound := mul_le_mul_of_nonneg_left hlower hη'
  have herr' : |f (x + s) - (f x - (m x - m (x + s)))| ≤
      (1 - P.η₂) * (m x - m (x + s)) := by
    rw [hval, sub_sub_cancel]
    exact herr.trans (by nlinarith only [hprod, hbound])
  simpa [btrRatio] using Optimization.le_reductionRatio_of_abs_sub_le hpred herr'

omit [NormedSpace ℝ E] in
/-- The acceptance-ratio estimate (6.4.12) before applying the radius update. -/
theorem btrRatio_ge_eta₂_of_small_radius {P : BTRParams} {f m : E → ℝ} {x s g : E}
    {β Δ κ C : ℝ} (hβ : 0 < β) (hβC : β ≤ C) (hΔ : 0 < Δ) (hg : g ≠ 0)
    (hval : f x = m x) (hdec : HasSufficientModelDecrease m x s g β Δ κ)
    (herr : |f (x + s) - m (x + s)| ≤ C * Δ ^ 2)
    (hsmall : Δ ≤ κ * ‖g‖ * (1 - P.η₂) / C) :
    P.η₂ ≤ btrRatio f m x s := by
  exact btrRatio_ge_eta₂_of_small_radius_of_decrease hβ hβC hΔ
    (norm_pos_iff.mpr hg) hdec.1.1 hdec.1.2 hval hdec.2 herr hsmall

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
  have hsuccess := btrRatio_ge_eta₂_of_small_radius hβ hβC hΔ hg hval hdec herr hsmall
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

/-- Theorem 6.4.4. A run with finitely many successful iterations is eventually
constant at a first-order critical point. -/
theorem theorem_6_4_4 {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] {P : BTRParams} {f : F → ℝ}
    {sufficient : ℕ → (F → ℝ) → F → F → Prop} (run : BTRRun f P sufficient)
    (β : ℕ → ℝ) {κ C : ℝ} (hβ : ∀ k, 0 < β k) (hβC : ∀ k, β k ≤ C)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤
      C * (run.Δ k) ^ 2) (hfinite : run.successful.Finite) :
    ∃ x, (∀ᶠ k in atTop, run.x k = x) ∧ gradient f x = 0 := by
  obtain ⟨N, hN⟩ := hfinite.bddAbove
  let n := N + 1
  have hfail (j : ℕ) :
      btrRatio f (run.model (n + j)) (run.x (n + j)) (run.s (n + j)) < P.η₁ := by
    apply lt_of_not_ge
    intro h
    have hle := hN (show n + j ∈ run.successful from h)
    dsimp [n] at hle
    omega
  have hx (j : ℕ) : run.x (n + j) = run.x n := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [show n + (j + 1) = n + j + 1 by omega, run.iterate_update,
        Optimization.acceptStep_of_lt (hfail j), ih]
  refine ⟨run.x n, eventually_atTop.mpr ⟨n, fun k hk ↦ ?_⟩, ?_⟩
  · simpa only [Nat.add_sub_of_le hk] using hx (k - n)
  · by_contra hg
    have hγ : 0 < P.γ₂ := P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂
    have hrad (j : ℕ) : run.Δ (n + j) ≤ P.γ₂ ^ j * run.Δ n := by
      induction j with
      | zero => simp
      | succ j ih =>
        calc
          run.Δ (n + (j + 1)) ≤ P.γ₂ * run.Δ (n + j) :=
            ((run.radius_update (n + j)).unsuccessful (hfail j)).2
          _ ≤ P.γ₂ * (P.γ₂ ^ j * run.Δ n) := mul_le_mul_of_nonneg_left ih hγ.le
          _ = P.γ₂ ^ (j + 1) * run.Δ n := by rw [pow_succ]; ring
    let θ := κ * ‖gradient f (run.x n)‖ * (1 - P.η₂) / C
    have hθ : 0 < θ := div_pos (mul_pos (mul_pos (hdec n).1.1 (norm_pos_iff.mpr hg))
      (sub_pos.mpr P.eta₂_lt_one)) ((hβ n).trans_le (hβC n))
    have ht : Tendsto (fun j : ℕ ↦ P.γ₂ ^ j * run.Δ n) atTop (𝓝 0) := by
      simpa only [zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hγ.le P.gamma₂_lt_one).mul_const (run.Δ n)
    obtain ⟨j, hj⟩ := (ht.eventually (gt_mem_nhds hθ)).exists
    have hsmall : run.Δ (n + j) ≤ κ * ‖gradient f (run.x (n + j))‖ * (1 - P.η₂) / C := by
      rw [hx]
      exact (hrad j).trans hj.le
    have hgj : gradient f (run.x (n + j)) ≠ 0 := by rwa [hx]
    have hs := (theorem_6_4_2 (hβ (n + j)) (hβC (n + j)) (run.delta_pos (n + j))
      hgj (hval (n + j)) (hdec (n + j)) (herr (n + j)) hsmall
      (run.radius_update (n + j))).1
    exact (hfail j).not_ge (P.eta₁_le_eta₂.trans hs)

/-- A trust-region decrease estimate expressed in a scalar criticality
measure guarantees arbitrarily late small values. The measure need not be
a norm or depend on the point continuously. -/
theorem frequently_criticality_lt_of_model_decrease
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {P : BTRParams} {f : F → ℝ} {sufficient : ℕ → (F → ℝ) → F → F → Prop}
    (run : BTRRun f P sufficient) (u β : ℕ → ℝ) {κ B ε : ℝ}
    (hκ : κ ∈ Set.Ioo (0 : ℝ) 1) (hε : 0 < ε)
    (hβ : ∀ k, 0 < β k) (hβB : ∀ k, β k ≤ B)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, κ * u k * min (u k / β k) (run.Δ k) ≤
      run.model k (run.x k) - run.model k (run.x k + run.s k))
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤ B * run.Δ k ^ 2)
    (hlower : BddBelow (Set.range (f ∘ run.x))) :
    ∃ᶠ k in atTop, u k < ε := by
  classical
  by_contra! hn
  obtain ⟨N, hN⟩ := eventually_atTop.mp hn
  have hB : 0 < B := (hβ 0).trans_le (hβB 0)
  let θ := κ * ε * (1 - P.η₂) / B
  have hθ : 0 < θ := div_pos (mul_pos (mul_pos hκ.1 hε) (sub_pos.mpr P.eta₂_lt_one)) hB
  let R := run.tail N
  have hforce (k : ℕ) (hk : R.Δ k ≤ θ) : k ∈ R.verySuccessful := by
    let j := N + k
    have hu : ε ≤ u j := hN _ (Nat.le_add_right _ _)
    have hθj : θ ≤ κ * u j * (1 - P.η₂) / B := by
      dsimp only [θ]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu hκ.1.le)
          (sub_nonneg.mpr P.eta₂_lt_one.le)) hB.le
    exact btrRatio_ge_eta₂_of_small_radius_of_decrease (hβ j) (hβB j) (run.delta_pos j)
      (hε.trans_le hu) hκ.1 hκ.2 (hval j) (hdec j) (herr j) (hk.trans hθj)
  let r := min (R.Δ 0) (P.γ₁ * θ)
  have hr : 0 < r := lt_min (R.delta_pos 0) (mul_pos P.gamma₁_pos hθ)
  have hrad (k : ℕ) (hk : N ≤ k) : r ≤ run.Δ k := by
    have hh := R.delta_lower_bound hforce (k - N)
    change r ≤ run.Δ (N + (k - N)) at hh
    simpa only [Nat.add_sub_of_le hk] using hh
  let v := f ∘ run.x
  have hv : Tendsto v atTop (𝓝 (⨅ k, v k)) := tendsto_atTop_ciInf run.objective_antitone hlower
  have hdiff : Tendsto (fun k ↦ v k - v (k + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using hv.sub (hv.comp (tendsto_add_atTop_nat 1))
  let d := P.η₁ * (κ * ε * min (ε / B) r)
  have hd : 0 < d := mul_pos P.eta₁_pos
    (mul_pos (mul_pos hκ.1 hε) (lt_min (div_pos hε hB) hr))
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hdiff.eventually (gt_mem_nhds hd))
  let M := max N J
  have hrejected (k : ℕ) (hk : M ≤ k) : k ∉ run.successful := by
    intro hs
    have hkn := (le_max_left N J).trans hk
    have hku := hN k hkn
    have hq := div_le_div₀ (hε.le.trans hku) hku (hβ k) (hβB k)
    have hmin := min_le_min hq (hrad k hkn)
    have hp : κ * ε * min (ε / B) r ≤ run.model k (run.x k) - run.model k (run.x k + run.s k) :=
      (mul_le_mul (mul_le_mul_of_nonneg_left hku hκ.1.le) hmin
        (le_min (div_nonneg hε.le hB.le) hr.le)
        (mul_nonneg hκ.1.le (hε.le.trans hku))).trans (hdec k)
    have hdrop : d ≤ v k - v (k + 1) :=
      (mul_le_mul_of_nonneg_left hp P.eta₁_pos.le).trans (run.objective_drop_of_successful hs)
    exact (hJ k ((le_max_right N J).trans hk)).not_ge hdrop
  have hγ : 0 < P.γ₂ := P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂
  have hgeom (n : ℕ) : run.Δ (M + n) ≤ P.γ₂ ^ n * run.Δ M := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hrej := hrejected (M + n) (Nat.le_add_right _ _)
      calc
        run.Δ (M + (n + 1)) ≤ P.γ₂ * run.Δ (M + n) :=
          (run.radius_update (M + n)).unsuccessful (lt_of_not_ge hrej) |>.2
        _ ≤ P.γ₂ * (P.γ₂ ^ n * run.Δ M) := mul_le_mul_of_nonneg_left ih hγ.le
        _ = _ := by rw [pow_succ]; ring
  have hlim : Tendsto (fun n : ℕ ↦ P.γ₂ ^ n * run.Δ M) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hγ.le P.gamma₂_lt_one).mul_const (run.Δ M)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hr)).exists
  exact hn.not_ge ((hrad _ ((le_max_left N J).trans (Nat.le_add_right M n))).trans (hgeom n))

private theorem frequently_gradient_norm_lt {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] {P : BTRParams} {f : F → ℝ}
    {sufficient : ℕ → (F → ℝ) → F → F → Prop} (run : BTRRun f P sufficient)
    (β : ℕ → ℝ) {κ C : ℝ} (hβ : ∀ k, 0 < β k) (hβC : ∀ k, β k ≤ C)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤
      C * (run.Δ k) ^ 2) (hlower : BddBelow (Set.range f)) :
    ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, ‖gradient f (run.x k)‖ < ε := by
  intro ε hε
  have hb : BddBelow (Set.range (f ∘ run.x)) :=
    hlower.mono (show Set.range (f ∘ run.x) ⊆ Set.range f from
      fun _ ⟨k, hk⟩ ↦ ⟨run.x k, hk⟩)
  exact frequently_criticality_lt_of_model_decrease run (fun k ↦ ‖gradient f (run.x k)‖)
    β (hdec 0).1 hε hβ hβC hval (fun k ↦ (hdec k).2) herr hb

/-- Theorem 6.4.5. The gradient norms on a basic trust-region run have zero
limit inferior when the objective is bounded below. -/
theorem theorem_6_4_5 {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] {P : BTRParams} {f : F → ℝ}
    {sufficient : ℕ → (F → ℝ) → F → F → Prop} (run : BTRRun f P sufficient)
    (β : ℕ → ℝ) {κ C : ℝ} (hβ : ∀ k, 0 < β k) (hβC : ∀ k, β k ≤ C)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤
      C * (run.Δ k) ^ 2) (hlower : BddBelow (Set.range f)) :
    liminf (fun k ↦ ‖gradient f (run.x k)‖) atTop = 0 := by
  let g (k : ℕ) := gradient f (run.x k)
  have hfreq := frequently_gradient_norm_lt run β hβ hβC hval hdec herr hlower
  have hb : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) (fun k ↦ ‖g k‖) :=
    ⟨0, show ∀ᶠ k in atTop, 0 ≤ ‖g k‖ from Eventually.of_forall fun _ ↦ norm_nonneg _⟩
  have hco : (atTop : Filter ℕ).IsCoboundedUnder (· ≥ ·) (fun k ↦ ‖g k‖) := by
    refine ⟨1, fun b hb' ↦ ?_⟩
    obtain ⟨k, hk, hk'⟩ := ((hfreq 1 zero_lt_one).and_eventually hb').exists
    exact hk'.trans hk.le
  change liminf (fun k ↦ ‖g k‖) atTop = 0
  refine le_antisymm ?_ (le_liminf_of_le hco (Eventually.of_forall fun _ ↦ norm_nonneg _))
  by_contra! hp
  have hlim := liminf_le_of_frequently_le ((hfreq _ (half_pos hp)).mono fun _ h ↦ h.le) hb
  linarith

/-- A uniformly continuous first-order criticality measure tends to zero
on a basic trust-region run. On excursions away from zero, the objective
drop bounds the path length until the next small criticality value. -/
theorem tendsto_criticality_zero_of_uniformContinuousOn
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {P : BTRParams} {f : F → ℝ} {sufficient : ℕ → (F → ℝ) → F → F → Prop}
    (run : BTRRun f P sufficient) (u : F → ℝ) (β : ℕ → ℝ) {S : Set F} {κ B K : ℝ}
    (hκ : κ ∈ Set.Ioo (0 : ℝ) 1) (hβ : ∀ k, 0 < β k) (hβB : ∀ k, β k ≤ B)
    (hK : 0 ≤ K) (hstep : ∀ k, ‖run.s k‖ ≤ K * run.Δ k)
    (hx : ∀ k, run.x k ∈ S) (hu : UniformContinuousOn u S) (hun : ∀ k, 0 ≤ u (run.x k))
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, κ * u (run.x k) * min (u (run.x k) / β k) (run.Δ k) ≤
      run.model k (run.x k) - run.model k (run.x k + run.s k))
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤ B * run.Δ k ^ 2)
    (hlower : BddBelow (Set.range (f ∘ run.x))) :
    Tendsto (u ∘ run.x) atTop (𝓝 0) := by
  classical
  let v := f ∘ run.x
  let a := u ∘ run.x
  have hv : Tendsto v atTop (𝓝 (⨅ k, v k)) := tendsto_atTop_ciInf run.objective_antitone hlower
  have hdiff : Tendsto (fun k ↦ v k - v (k + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using hv.sub (hv.comp (tendsto_add_atTop_nat 1))
  have htail : Tendsto (fun k ↦ v k - ⨅ j, v j) atTop (𝓝 0) := by
    simpa only [sub_self] using hv.sub_const (⨅ j, v j)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let e := ε / 2
  have he : 0 < e := half_pos hε
  let c := P.η₁ * (κ * e)
  have hc : 0 < c := mul_pos P.eta₁_pos (mul_pos hκ.1 he)
  have hB : 0 < B := (hβ 0).trans_le (hβB 0)
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp hu e he
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hdiff.eventually (gt_mem_nhds (mul_pos hc (div_pos he hB))))
  obtain ⟨J, hJ⟩ := eventually_atTop.mp
    (htail.eventually (gt_mem_nhds (div_pos (mul_pos hc hδ) (by linarith : 0 < K + 1))))
  have hlength (k : ℕ) (hk : N ≤ k) (hka : e ≤ a k) :
      c * dist (run.x k) (run.x (k + 1)) ≤ K * (v k - v (k + 1)) := by
    by_cases hs : k ∈ run.successful
    · have hquot : e / B ≤ a k / β k := div_le_div₀ (hun k) hka (hβ k) (hβB k)
      have hp : κ * e * min (e / B) (run.Δ k) ≤
          run.model k (run.x k) - run.model k (run.x k + run.s k) :=
        (mul_le_mul (mul_le_mul_of_nonneg_left hka hκ.1.le) (min_le_min hquot le_rfl)
          (le_min (div_nonneg he.le hB.le) (run.delta_pos k).le)
          (mul_nonneg hκ.1.le (hun k))).trans (hdec k)
      have hdrop : c * min (e / B) (run.Δ k) ≤ v k - v (k + 1) := by
        simpa only [c, v, Function.comp_apply, mul_assoc] using
          (mul_le_mul_of_nonneg_left hp P.eta₁_pos.le).trans (run.objective_drop_of_successful hs)
      have hrad : run.Δ k ≤ e / B := by
        by_contra! hh
        rw [min_eq_left hh.le] at hdrop
        exact (hN k hk).not_ge hdrop
      rw [min_eq_right hrad] at hdrop
      have hupdate : run.x (k + 1) = run.x k + run.s k := by
        rw [run.iterate_update, Optimization.acceptStep_of_le hs]
      calc
        _ = c * ‖run.s k‖ := by
          rw [hupdate, dist_eq_norm, sub_add_cancel_left, norm_neg]
        _ ≤ c * (K * run.Δ k) := mul_le_mul_of_nonneg_left (hstep k) hc.le
        _ = K * (c * run.Δ k) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hdrop hK
    · simp only [v, Function.comp_apply, run.iterate_eq_of_unsuccessful hs, dist_self,
        sub_self, mul_zero, le_rfl]
  refine ⟨max N J, fun k hk ↦ ?_⟩
  have hkN := (le_max_left N J).trans hk
  have hkJ := (le_max_right N J).trans hk
  change dist (a k) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (show 0 ≤ a k from hun k)]
  by_contra! hhigh
  have hExists : ∃ j, k ≤ j ∧ a j < e :=
    frequently_atTop.mp (frequently_criticality_lt_of_model_decrease run a β
      hκ he hβ hβB hval hdec herr hlower) k
  let j := Nat.find hExists
  have hj : k ≤ j ∧ a j < e := Nat.find_spec hExists
  have htel (i : ℕ) (hi : k ≤ i) : i ≤ j →
      c * dist (run.x k) (run.x i) ≤ K * (v k - v i) := by
    induction i, hi using Nat.le_induction with
    | base => simp
    | succ i hi ih =>
      intro hij
      have hbelow : i < j := Nat.lt_of_succ_le hij
      have hai : e ≤ a i := le_of_not_gt fun hh ↦ (Nat.find_min hExists hbelow) ⟨hi, hh⟩
      have htri := mul_le_mul_of_nonneg_left (dist_triangle (run.x k) (run.x i)
        (run.x (i + 1))) hc.le
      linarith only [htri, ih hbelow.le, hlength i (hkN.trans hi) hai]
  have hvle : (⨅ i, v i) ≤ v j := ciInf_le hlower j
  have hlast : K * (v k - v j) < c * δ := calc
    _ ≤ (K + 1) * (v k - v j) :=
      mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.mpr (run.objective_antitone hj.1))
    _ ≤ (K + 1) * (v k - ⨅ i, v i) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hvle _) (by linarith)
    _ < _ := by
      have hh := (lt_div_iff₀ (by linarith : 0 < K + 1)).mp (hJ k hkJ)
      rwa [mul_comm]
  have hdist := lt_of_mul_lt_mul_left ((htel j hj.1 le_rfl).trans_lt hlast) hc.le
  have hsmall := hclose _ (hx k) _ (hx j) hdist
  rw [Real.dist_eq] at hsmall
  have hgap : a k - a j < e := (le_abs_self _).trans_lt hsmall
  dsimp only [e] at hgap hj
  linarith only [hgap, hj.2, hhigh]

/-- Theorem 6.4.6. With the norm comparison of AN.1 and the global Lipschitz bound
on the objective gradient from AF.3, the whole gradient norm sequence tends to zero. -/
theorem theorem_6_4_6 {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] {P : BTRParams} {f : F → ℝ}
    {sufficient : ℕ → (F → ℝ) → F → F → Prop} (run : BTRRun f P sufficient)
    (β : ℕ → ℝ) {κ C L K : ℝ} (hβ : ∀ k, 0 < β k) (hβC : ∀ k, β k ≤ C)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤
      C * (run.Δ k) ^ 2) (hlower : BddBelow (Set.range f))
    (hf : ContDiff ℝ 2 f) (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ L) (hK : 0 ≤ K)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v) :
    Tendsto (fun k ↦ ‖gradient f (run.x k)‖) atTop (𝓝 0) := by
  have hL : 0 ≤ L := (norm_nonneg (fderiv ℝ (fderiv ℝ f) (0 : F))).trans (hH 0)
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hgrad (x y : F) : ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖ := by
    unfold gradient
    rw [← map_sub, LinearIsometryEquiv.norm_map]
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ ↦ hDf.differentiable (by norm_num) z)
      (fun z _ ↦ hH z) (convex_univ : Convex ℝ (Set.univ : Set F)) (Set.mem_univ y) (Set.mem_univ x)
  have hu : LipschitzWith ⟨L, hL⟩ (fun x ↦ ‖gradient f x‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, dist_eq_norm]
    exact (abs_norm_sub_norm_le _ _).trans (hgrad x y)
  have hstep (k : ℕ) : ‖run.s k‖ ≤ K * run.Δ k :=
    (hnorm k _).trans (mul_le_mul_of_nonneg_left
      (by simpa [trustRegion] using run.feasible k) hK)
  have hbelow : BddBelow (Set.range (f ∘ run.x)) :=
    hlower.mono (show Set.range (f ∘ run.x) ⊆ Set.range f from
      fun _ ⟨k, hk⟩ ↦ ⟨run.x k, hk⟩)
  exact tendsto_criticality_zero_of_uniformContinuousOn run
    (fun x ↦ ‖gradient f x‖) β (hdec 0).1 hβ hβC hK hstep
    (fun _ ↦ Set.mem_univ _) hu.uniformContinuous.uniformContinuousOn
    (fun _ ↦ norm_nonneg _) hval (fun k ↦ (hdec k).2) herr hbelow

end ConnGouldToint.Chapter06
