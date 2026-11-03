import NumlibSurface.ConnGouldToint.Chapter06.Section04
import NumlibSurface.ConnGouldToint.Chapter09.Section02

/-! # Trust-region iterations with an objective-improving correction -/

open Filter Topology
open ConnGouldToint.Chapter06

namespace ConnGouldToint.Chapter10

variable {E : Type*} [NormedAddCommGroup E]

/-- The predicted decrease augmented by the exact improvement from the correction. -/
def magicalStepDecrease (f m : E → ℝ) (x s c : E) : ℝ :=
  m x - m (x + s) + (f (x + s) - f (x + s + c))

/-- The acceptance ratio (10.4.2) for the composite step. -/
noncomputable def magicalStepRatio (f m : E → ℝ) (x s c : E) : ℝ :=
  (f x - f (x + s + c)) / magicalStepDecrease f m x s c

/-- An infinite run of Algorithm 10.4.1. The norm bound on the original
trial and the model decrease requirement are supplied separately. -/
structure MagicalStepRun (P : BTRParams) (f : E → ℝ) where
  x : ℕ → E
  s : ℕ → E
  correction : ℕ → E
  model : ℕ → E → ℝ
  radius : ℕ → ℝ
  initial_pos : 0 < radius 0
  base_decrease : ∀ k, 0 < model k (x k) - model k (x k + s k)
  correction_improves : ∀ k, f (x k + s k + correction k) ≤ f (x k + s k)
  iterate_update : ∀ k, x (k + 1) =
    if P.η₁ ≤ magicalStepRatio f (model k) (x k) (s k) (correction k) then
      x k + s k + correction k else x k
  radius_update : ∀ k, BTRRadiusUpdate P
    (magicalStepRatio f (model k) (x k) (s k) (correction k)) (radius k) (radius (k + 1))

/-- In (10.4.3) the correction improvement cancels from the ratio error.
The error in the original trial model is divided by the augmented decrease. -/
theorem magicalStepRatio_sub_one {f m : E → ℝ} {x s c : E}
    (hval : f x = m x) (hpred : 0 < magicalStepDecrease f m x s c) :
    |magicalStepRatio f m x s c - 1| =
      |m (x + s) - f (x + s)| / magicalStepDecrease f m x s c := by
  rw [magicalStepRatio, show (f x - f (x + s + c)) / magicalStepDecrease f m x s c - 1 =
    (m (x + s) - f (x + s)) / magicalStepDecrease f m x s c by
      field_simp [hpred.ne']; unfold magicalStepDecrease; rw [hval]; ring,
    abs_div, abs_of_pos hpred]

/-- Corrected Theorem 10.4.1. The lower bound from (10.4.6) applies to the
augmented denominator. Nonnegativity of the correction improvement does
not imply the printed lower bound for the original model decrease. -/
theorem theorem_10_4_1 {P : BTRParams} {f m : E → ℝ} {x s c : E}
    {κ a C Δ Δ' : ℝ} (hκ : 0 < κ) (hκ' : κ ≤ 1) (ha : 0 < a)
    (hC : 0 < C) (hΔ : 0 < Δ) (hval : f x = m x)
    (hdec : κ * a * min (a / C) Δ ≤ magicalStepDecrease f m x s c)
    (herr : |m (x + s) - f (x + s)| ≤ C * Δ ^ 2)
    (hsmall : Δ ≤ κ * a * (1 - P.η₂) / C)
    (hupdate : BTRRadiusUpdate P (magicalStepRatio f m x s c) Δ Δ') :
    P.η₂ ≤ magicalStepRatio f m x s c ∧ Δ ≤ Δ' := by
  have hη : 0 < P.η₂ := P.eta₁_pos.trans_le P.eta₁_le_eta₂
  have hη' : 0 ≤ 1 - P.η₂ := sub_nonneg.mpr P.eta₂_lt_one.le
  have hs := (le_div_iff₀ hC).mp hsmall
  have hΔ' : Δ ≤ a / C := by
    apply (le_div_iff₀ hC).mpr
    refine hs.trans ?_
    have hh := mul_le_mul_of_nonneg_right (mul_le_of_le_one_left ha.le hκ') hη'
    exact hh.trans (mul_le_of_le_one_right ha.le (by linarith))
  rw [min_eq_right hΔ'] at hdec
  have hp := (mul_pos (mul_pos hκ ha) hΔ).trans_le hdec
  have hr : |magicalStepRatio f m x s c - 1| ≤ 1 - P.η₂ := by
    rw [magicalStepRatio_sub_one hval hp]
    apply (div_le_iff₀ hp).mpr
    refine herr.trans ?_
    nlinarith only [mul_le_mul_of_nonneg_right hs hΔ.le,
      mul_le_mul_of_nonneg_left hdec hη']
  have hsuccess : P.η₂ ≤ magicalStepRatio f m x s c := by
    linarith only [hr, neg_abs_le (magicalStepRatio f m x s c - 1)]
  exact ⟨hsuccess, hupdate.very_successful hsuccess⟩

private def MagicalStepRun.successful {P : BTRParams} {f : E → ℝ}
    (run : MagicalStepRun P f) : Set ℕ :=
  {k | P.η₁ ≤ magicalStepRatio f (run.model k) (run.x k) (run.s k) (run.correction k)}

private theorem MagicalStepRun.radius_pos {P : BTRParams} {f : E → ℝ}
    (run : MagicalStepRun P f) (k : ℕ) : 0 < run.radius k := by
  induction k with
  | zero => exact run.initial_pos
  | succ k ih => exact (run.radius_update k).pos ih

private theorem MagicalStepRun.decrease_pos {P : BTRParams} {f : E → ℝ}
    (run : MagicalStepRun P f) (k : ℕ) :
    0 < magicalStepDecrease f (run.model k) (run.x k) (run.s k) (run.correction k) :=
  add_pos_of_pos_of_nonneg (run.base_decrease k) (sub_nonneg.mpr (run.correction_improves k))

private theorem MagicalStepRun.objective_drop {P : BTRParams} {f : E → ℝ}
    (run : MagicalStepRun P f) {k : ℕ} (hk : k ∈ run.successful) :
    P.η₁ * magicalStepDecrease f (run.model k) (run.x k) (run.s k) (run.correction k) ≤
      f (run.x k) - f (run.x (k + 1)) := by
  have hr : P.η₁ ≤ magicalStepRatio f (run.model k) (run.x k) (run.s k) (run.correction k) := hk
  rw [run.iterate_update, ite_eq_left hr]
  exact (le_div_iff₀ (run.decrease_pos k)).mp hr

private theorem MagicalStepRun.stay {P : BTRParams} {f : E → ℝ}
    (run : MagicalStepRun P f) {k : ℕ} (hk : k ∉ run.successful) : run.x (k + 1) = run.x k := by
  have hn : ¬ P.η₁ ≤ magicalStepRatio f (run.model k) (run.x k) (run.s k)
      (run.correction k) := hk
  rw [run.iterate_update, ite_eq_right hn]

private theorem MagicalStepRun.objective_antitone {P : BTRParams} {f : E → ℝ}
    (run : MagicalStepRun P f) : Antitone (fun k ↦ f (run.x k)) := by
  apply antitone_nat_of_succ_le
  intro k
  by_cases hk : k ∈ run.successful
  · exact sub_nonneg.mp ((mul_pos P.eta₁_pos (run.decrease_pos k)).le.trans
      (run.objective_drop hk))
  · rw [run.stay hk]

variable [NormedSpace ℝ E]

/-- Theorem 10.4.2 in its frequently-small-gradient form. The result uses
only the agreement and decrease estimates of the magical-step run. -/
theorem theorem_10_4_2 {P : BTRParams} {f : E → ℝ} (run : MagicalStepRun P f)
    {κ C : ℝ} (hκ : 0 < κ) (hκ' : κ ≤ 1) (hC : 0 < C)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, κ * ‖fderiv ℝ f (run.x k)‖ *
      min (‖fderiv ℝ f (run.x k)‖ / C) (run.radius k) ≤
      magicalStepDecrease f (run.model k) (run.x k) (run.s k) (run.correction k))
    (herr : ∀ k, |run.model k (run.x k + run.s k) - f (run.x k + run.s k)| ≤ C * run.radius k ^ 2)
    (hlower : BddBelow (Set.range f)) :
    ∀ ε > (0 : ℝ), ∃ᶠ k in atTop, ‖fderiv ℝ f (run.x k)‖ < ε := by
  intro ε hε
  by_contra! h
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  let θ := κ * ε * (1 - P.η₂) / C
  have hη : 0 < 1 - P.η₂ := sub_pos.mpr P.eta₂_lt_one
  have hθ : 0 < θ := div_pos (mul_pos (mul_pos hκ hε) hη) hC
  have hforce (k : ℕ) (hk : N ≤ k) (hsmall : run.radius k ≤ θ) :
      P.η₂ ≤ magicalStepRatio f (run.model k) (run.x k) (run.s k) (run.correction k) := by
    have hg := hN k hk
    refine (theorem_10_4_1 hκ hκ' (hε.trans_le hg) hC (run.radius_pos k)
      (hval k) (hdec k) (herr k) (hsmall.trans ?_) (run.radius_update k)).1
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hκ.le) hη.le) hC.le
  let r := min (run.radius N) (P.γ₁ * θ)
  have hr : 0 < r := lt_min (run.radius_pos N) (mul_pos P.gamma₁_pos hθ)
  have hrad (k : ℕ) (hk : N ≤ k) : r ≤ run.radius k := by
    induction k, hk using Nat.le_induction with
    | base => exact min_le_left _ _
    | succ k hk ih =>
      let ρ := magicalStepRatio f (run.model k) (run.x k) (run.s k) (run.correction k)
      have hu := run.radius_update k
      by_cases hv : P.η₂ ≤ ρ
      · exact ih.trans (hu.very_successful hv)
      have hlarge : θ < run.radius k := lt_of_not_ge (fun hs ↦ hv (hforce k hk hs))
      have hγ : P.γ₁ * run.radius k ≤ run.radius (k + 1) := by
        by_cases hs : P.η₁ ≤ ρ
        · exact (mul_le_mul_of_nonneg_right P.gamma₁_le_gamma₂ (run.radius_pos k).le).trans
            (hu.successful hs (lt_of_not_ge hv)).1
        · exact (hu.unsuccessful (lt_of_not_ge hs)).1
      exact (min_le_right _ _).trans
        ((mul_le_mul_of_nonneg_left hlarge.le P.gamma₁_pos.le).trans hγ)
  let v (k : ℕ) := f (run.x k)
  have ht := tendsto_atTop_ciInf run.objective_antitone
    (hlower.mono (show Set.range v ⊆ Set.range f from fun _ ⟨k, hk⟩ ↦ ⟨run.x k, hk⟩))
  have hdiff : Tendsto (fun k ↦ v k - v (k + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using ht.sub (ht.comp (tendsto_add_atTop_nat 1))
  let d := P.η₁ * (κ * ε * min (ε / C) r)
  have hd : 0 < d := mul_pos P.eta₁_pos
    (mul_pos (mul_pos hκ hε) (lt_min (div_pos hε hC) hr))
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hdiff.eventually_lt_const hd)
  let L := max N M
  have hfail (k : ℕ) (hk : L ≤ k) : k ∉ run.successful := by
    intro hs
    have hkN := (le_max_left N M).trans hk
    have hg := hN k hkN
    have hp := (mul_le_mul (mul_le_mul_of_nonneg_left hg hκ.le)
      (min_le_min (div_le_div_of_nonneg_right hg hC.le) (hrad k hkN))
      (le_min (div_nonneg hε.le hC.le) hr.le) (by positivity)).trans (hdec k)
    exact (hM k ((le_max_right N M).trans hk)).not_ge
      ((mul_le_mul_of_nonneg_left hp P.eta₁_pos.le).trans (run.objective_drop hs))
  have hγ := P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂
  have hpow (j : ℕ) : run.radius (L + j) ≤ P.γ₂ ^ j * run.radius L := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hh := ((run.radius_update (L + j)).unsuccessful
        (lt_of_not_ge (hfail _ (Nat.le_add_right _ _)))).2
      rw [Nat.add_succ, pow_succ, mul_comm (P.γ₂ ^ j), mul_assoc]
      exact hh.trans (mul_le_mul_of_nonneg_left ih hγ.le)
  have hlim : Tendsto (fun j : ℕ ↦ P.γ₂ ^ j * run.radius L) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ.le P.gamma₂_lt_one).mul_const
      (run.radius L)
  obtain ⟨j, hj⟩ := (hlim.eventually_lt_const hr).exists
  exact hj.not_ge ((hrad _ ((le_max_left N M).trans (Nat.le_add_right L j))).trans (hpow j))

/-- Theorem 10.4.3. If both the original and corrective steps are bounded
by multiples of the radius, the whole derivative norm sequence tends to zero. -/
theorem theorem_10_4_3 {P : BTRParams} {f : E → ℝ} (run : MagicalStepRun P f)
    {κ C K M L : ℝ} (hκ : 0 < κ) (hκ' : κ ≤ 1) (hC : 0 < C)
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, κ * ‖fderiv ℝ f (run.x k)‖ *
      min (‖fderiv ℝ f (run.x k)‖ / C) (run.radius k) ≤
      magicalStepDecrease f (run.model k) (run.x k) (run.s k) (run.correction k))
    (herr : ∀ k, |run.model k (run.x k + run.s k) - f (run.x k + run.s k)| ≤ C * run.radius k ^ 2)
    (hs : ∀ k, ‖run.s k‖ ≤ K * run.radius k)
    (hc : ∀ k, ‖run.correction k‖ ≤ M * run.radius k)
    (hgrad : ∀ y z, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖)
    (hlower : BddBelow (Set.range f)) :
    Tendsto (fun k ↦ ‖fderiv ℝ f (run.x k)‖) atTop (𝓝 0) := by
  refine (Chapter09.theorem_9_2_6 (S := run.successful) P.eta₁_pos hκ hC
    (εc := 1) (A := 1) zero_lt_one zero_lt_one hL (add_nonneg hK hM)
    (fun _ ↦ norm_nonneg _) run.radius_pos (fun _ _ ↦ by rw [one_mul])
    hgrad hdec (fun _ hk ↦ run.objective_drop hk) ?_ (fun _ hk ↦ run.stay hk)
    hlower (theorem_10_4_2 run hκ hκ' hC hval hdec herr hlower)).1
  intro k hk
  have hratio : P.η₁ ≤ magicalStepRatio f (run.model k) (run.x k) (run.s k)
      (run.correction k) := hk
  have he : run.x k - (run.x k + run.s k + run.correction k) =
      -(run.s k + run.correction k) := by abel
  rw [run.iterate_update, ite_eq_left hratio, he, norm_neg, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hs k) (hc k))

end ConnGouldToint.Chapter10
