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

/-- Theorem 6.4.5. For an objective bounded below, the liminf of the gradient norms
on a basic trust-region run is zero. The bounds on model error and curvature are
those established from the smooth model and norm assumptions in (6.4.3) and (6.3.2). -/
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
  let value (k : ℕ) := f (run.x k)
  let g (k : ℕ) := gradient f (run.x k)
  let pred (k : ℕ) := run.model k (run.x k) - run.model k (run.x k + run.s k)
  have hsuccess (k : ℕ) (hk : k ∈ run.successful) :
      P.η₁ * pred k ≤ value k - value (k + 1) := by
    have hr : P.η₁ ≤ Optimization.reductionRatio f (run.x k) (run.s k) (pred k) := hk
    change P.η₁ * pred k ≤ f (run.x k) - f (run.x (k + 1))
    rw [run.iterate_update, Optimization.acceptStep_of_le hr]
    exact (Optimization.le_reductionRatio_iff (run.predicted_pos k)).mp hr
  have hmono : Antitone value := by
    apply antitone_nat_of_succ_le
    intro k
    by_cases hk : k ∈ run.successful
    · exact sub_nonneg.mp ((mul_pos P.eta₁_pos (run.predicted_pos k)).le.trans (hsuccess k hk))
    · have hr : Optimization.reductionRatio f (run.x k) (run.s k) (pred k) < P.η₁ :=
        lt_of_not_ge hk
      change f (run.x (k + 1)) ≤ f (run.x k)
      rw [run.iterate_update, Optimization.acceptStep_of_lt hr]
  have ht := tendsto_atTop_ciInf hmono
    (hlower.mono (show Set.range value ⊆ Set.range f from fun _ ⟨k, hk⟩ ↦ ⟨run.x k, hk⟩))
  have hdiff : Tendsto (fun k ↦ value k - value (k + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using ht.sub (ht.comp (tendsto_add_atTop_nat 1))
  have hfreq (ε : ℝ) (hε : 0 < ε) : ∃ᶠ k in atTop, ‖g k‖ < ε := by
    by_contra hn
    have hev : ∀ᶠ k in atTop, ε ≤ ‖g k‖ := by
      simpa only [Filter.Frequently, not_not, not_lt] using hn
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    obtain ⟨r, hr, hrad⟩ := theorem_6_4_3 (run.tail N) (fun k ↦ g (N + k))
      (fun k ↦ β (N + k)) hε (fun k ↦ hN _ (Nat.le_add_right N k))
      (fun k ↦ hβ _) (fun k ↦ hβC _) (fun k ↦ hval _) (fun k ↦ hdec _)
      (fun k ↦ herr _)
    have hr' (k : ℕ) (hk : N ≤ k) : r ≤ run.Δ k := by
      have h := hrad (k - N)
      change r ≤ run.Δ (N + (k - N)) at h
      simpa only [Nat.add_sub_of_le hk] using h
    have hC : 0 < C := (hβ 0).trans_le (hβC 0)
    have hκ : 0 < κ := (hdec 0).1.1
    let a := P.η₁ * (κ * ε * min (ε / C) r)
    have ha : 0 < a := mul_pos P.eta₁_pos (mul_pos (mul_pos hκ hε)
      (lt_min (div_pos hε hC) hr))
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (hdiff.eventually (gt_mem_nhds ha))
    have hfinite : run.successful.Finite := by
      refine (Set.finite_le_nat (max N J)).subset fun k hk ↦ ?_
      change k ≤ max N J
      by_contra! hlarge
      have hkN := (le_max_left N J).trans hlarge.le
      have hkJ := (le_max_right N J).trans hlarge.le
      have hquot : ε / C ≤ ‖g k‖ / β k :=
        div_le_div₀ (norm_nonneg _) (hN _ hkN) (hβ k) (hβC k)
      have hmin := min_le_min hquot (hr' k hkN)
      have hpred : κ * ε * min (ε / C) r ≤ pred k :=
        (mul_le_mul (mul_le_mul_of_nonneg_left (hN _ hkN) hκ.le) hmin
          (le_min (div_nonneg hε.le hC.le) hr.le) (by positivity)).trans (hdec k).2
      have hlowerStep := (mul_le_mul_of_nonneg_left hpred P.eta₁_pos.le).trans (hsuccess k hk)
      exact (hJ _ hkJ).not_ge hlowerStep
    obtain ⟨x, hx, hxg⟩ := theorem_6_4_4 run β hβ hβC hval hdec herr hfinite
    obtain ⟨k, hk, hkg⟩ := (hx.and hev).exists
    exact hε.not_ge (by simpa [g, hk, hxg] using hkg)
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

end ConnGouldToint.Chapter06
