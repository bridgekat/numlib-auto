import NumlibSurface.ConnGouldToint.Chapter06.Section04
import NumlibSurface.ConnGouldToint.Chapter06.Section05

/-! # Approximate derivatives in trust-region models -/

open Filter Topology
open ConnGouldToint.Chapter06

namespace ConnGouldToint.Chapter08

variable {E : Type*} [NormedAddCommGroup E]

/-- Lemma 8.4.1. Relative error smaller than one makes convergence of either
gradient sequence to zero equivalent to convergence of the other. The index
set may already be restricted to a subsequence. -/
theorem lemma_8_4_1 {g df : ℕ → E} {κ : ℝ} (hκ₁ : κ < 1)
    (herr : ∀ k, ‖df k - g k‖ ≤ κ * ‖g k‖) :
    Tendsto g atTop (𝓝 0) ↔ Tendsto df atTop (𝓝 0) := by
  have htop (k : ℕ) : ‖df k‖ ≤ (κ + 1) * ‖g k‖ := by
    have hb := norm_add_le (df k - g k) (g k)
    rw [sub_add_cancel] at hb
    linarith [herr k]
  have hbottom (k : ℕ) : ‖g k‖ ≤ (1 - κ)⁻¹ * ‖df k‖ := by
    have hb := norm_add_le (g k - df k) (df k)
    rw [sub_add_cancel, norm_sub_rev] at hb
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ (sub_pos.mpr hκ₁)).mpr (by linarith [herr k])
  rw [tendsto_iff_norm_sub_tendsto_zero (f := g),
    tendsto_iff_norm_sub_tendsto_zero (f := df)]
  simp only [sub_zero]
  constructor <;> intro h
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => norm_nonneg _) htop
    simpa only [mul_zero] using (tendsto_const_nhds (x := κ + 1)).mul h
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => norm_nonneg _) hbottom
    simpa only [mul_zero] using (tendsto_const_nhds (x := (1 - κ)⁻¹)).mul h

section ModelAccuracy

variable [NormedSpace ℝ E]

/-- Theorem 8.4.2. The gradient mismatch contributes linearly in the radius,
while the objective and model curvature contribute quadratically. The bound
on the derivative mismatch is in the operator norm. -/
theorem theorem_8_4_2 {f m : E → ℝ} {x s : E} (p : Seminorm ℝ E)
    {Δ κf φ κg K a : ℝ} (hΔ : 0 ≤ Δ) (hφ : 1 ≤ φ) (hκf : 0 ≤ κf)
    (hκg : 0 ≤ κg) (hK : 0 ≤ K) (ha : 0 ≤ a)
    (hs : p s ≤ Δ) (hnorm : ‖s‖ ≤ K * p s)
    (hf : ContDiff ℝ 2 f) (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ κf)
    (hm : ∀ z ∈ p.closedBall x Δ, DifferentiableAt ℝ m z)
    (hDm : ∀ z ∈ p.closedBall x Δ, DifferentiableAt ℝ (fderiv ℝ m) z)
    (hM : ∀ z ∈ p.closedBall x Δ, ‖fderiv ℝ (fderiv ℝ m) z‖ ≤ φ)
    (hval : m x = f x) (hgrad : ‖fderiv ℝ f x - fderiv ℝ m x‖ ≤ κg * a) :
    |f (x + s) - m (x + s)| ≤
      κg * K * a * Δ + ((κf + 1) / 2 * K ^ 2) * φ * Δ ^ 2 := by
  have hxs : x + s ∈ p.closedBall x Δ := by
    rw [Seminorm.mem_closedBall, add_sub_cancel_left]
    exact hs
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hfrem := norm_sub_firstOrder_le_of_hessian_bound
    (convex_univ : Convex ℝ (Set.univ : Set E)) (Set.mem_univ x) (Set.mem_univ (x + s))
    (fun z _ => hf.differentiable (by norm_num) z)
    (fun z _ => hDf.differentiable (by norm_num) z) (fun z _ => hF z)
  have hmrem := norm_sub_firstOrder_le_of_hessian_bound (p.convex_closedBall x Δ)
    (p.mem_closedBall_self hΔ) hxs hm hDm hM
  have hlin : |fderiv ℝ f x s - fderiv ℝ m x s| ≤ κg * a * ‖s‖ := by
    rw [← Real.norm_eq_abs, ← sub_apply]
    exact ((fderiv ℝ f x - fderiv ℝ m x).le_opNorm s).trans
      (mul_le_mul_of_nonneg_right hgrad (norm_nonneg _))
  rw [Real.norm_eq_abs] at hfrem hmrem
  have herr : |f (x + s) - m (x + s)| ≤
      κg * a * ‖s‖ + (κf + φ) / 2 * ‖s‖ ^ 2 := by
    obtain ⟨hflo, hfhi⟩ := abs_le.mp hfrem
    obtain ⟨hmlo, hmhi⟩ := abs_le.mp hmrem
    obtain ⟨hllo, hlhi⟩ := abs_le.mp hlin
    rw [hval] at hmlo hmhi
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hstep : ‖s‖ ≤ K * Δ := hnorm.trans (mul_le_mul_of_nonneg_left hs hK)
  have hcurv : (κf + φ) / 2 ≤ ((κf + 1) / 2) * φ := by
    nlinarith [mul_nonneg hκf (sub_nonneg.mpr hφ)]
  calc
    _ ≤ κg * a * ‖s‖ + (κf + φ) / 2 * ‖s‖ ^ 2 := herr
    _ ≤ κg * a * (K * Δ) + (((κf + 1) / 2) * φ) * (K * Δ) ^ 2 := by gcongr
    _ = _ := by ring

end ModelAccuracy

/-- Theorem 8.4.3. Small radius relative to the model gradient and curvature
forces a very successful iteration under the inexact model error bound. -/
theorem theorem_8_4_3 {P : BTRParams} {f m : E → ℝ} {x s g : E}
    {φ Δ Δ' κ C e : ℝ} (hφ : 0 < φ) (hC : 1 ≤ C) (he : 0 ≤ e)
    (hΔ : 0 < Δ) (hg : g ≠ 0) (hval : f x = m x)
    (hdec : HasSufficientModelDecrease m x s g φ Δ κ)
    (herr : |f (x + s) - m (x + s)| ≤ e * ‖g‖ * Δ + C * φ * Δ ^ 2)
    (hsmall : Δ ≤ κ * ‖g‖ / (C * φ) * (1 - P.η₂ - e / κ))
    (hupdate : BTRRadiusUpdate P (btrRatio f m x s) Δ Δ') :
    P.η₂ ≤ btrRatio f m x s ∧ Δ ≤ Δ' := by
  have hκ := hdec.1.1
  have hg₀ := norm_pos_iff.mpr hg
  have hC₀ : 0 < C := zero_lt_one.trans_le hC
  have hη : 0 ≤ 1 - P.η₂ := sub_nonneg.mpr P.eta₂_lt_one.le
  have hη₀ : 0 < P.η₂ := P.eta₁_pos.trans_le P.eta₁_le_eta₂
  have hbudget : Δ * (C * φ) ≤ (κ * (1 - P.η₂) - e) * ‖g‖ := by
    apply (le_div_iff₀ (mul_pos hC₀ hφ)).mp
    refine hsmall.trans_eq ?_
    field_simp
  have hΔφ : Δ ≤ ‖g‖ / φ := by
    apply (le_div_iff₀ hφ).mpr
    calc
      Δ * φ ≤ Δ * (C * φ) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hφ.le hC) hΔ.le
      _ ≤ (κ * (1 - P.η₂) - e) * ‖g‖ := hbudget
      _ ≤ 1 * ‖g‖ := by
        have hb := mul_le_of_le_one_right hκ.le (by linarith : 1 - P.η₂ ≤ 1)
        gcongr
        linarith [hdec.1.2]
      _ = _ := one_mul _
  have hpredLower := hdec.2
  rw [min_eq_right hΔφ] at hpredLower
  have hpred : 0 < m x - m (x + s) := (mul_pos (mul_pos hκ hg₀) hΔ).trans_le hpredLower
  have herr' : |f (x + s) - (f x - (m x - m (x + s)))| ≤
      (1 - P.η₂) * (m x - m (x + s)) := by
    rw [hval, sub_sub_cancel]
    exact herr.trans (by nlinarith only [mul_le_mul_of_nonneg_right hbudget hΔ.le,
      mul_le_mul_of_nonneg_left hpredLower hη])
  have hρ : P.η₂ ≤ btrRatio f m x s := by
    simpa only [btrRatio, sub_sub_cancel] using Optimization.le_reductionRatio_of_abs_sub_le hpred herr'
  exact ⟨hρ, hupdate.very_successful hρ⟩

/-- Theorem 8.4.4. A uniform positive lower bound on the model gradient
prevents the radius from vanishing faster than the inverse running curvature.
The explicit constant accounts for a possibly smaller initial radius. -/
theorem theorem_8_4_4 [NormedSpace ℝ E] {P : BTRParams} {f : E → ℝ}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop} (run : BTRRun f P sufficient)
    (g : ℕ → E) (φ : ℕ → ℝ) {κ C e a : ℝ} (hC : 1 ≤ C) (he : 0 ≤ e)
    (ha : 0 < a) (hg : ∀ k, a ≤ ‖g k‖) (hφ : ∀ k, 0 < φ k) (hmono : Monotone φ)
    (hmargin : 0 < 1 - P.η₂ - e / κ)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (g k) (φ k) (run.Δ k) κ)
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤
      e * ‖g k‖ * run.Δ k + C * φ k * (run.Δ k) ^ 2) :
    ∃ r > 0, ∀ k, r / φ k ≤ run.Δ k := by
  let θ := κ * a / C * (1 - P.η₂ - e / κ)
  have hκ := (hdec 0).1.1
  have hC₀ : 0 < C := zero_lt_one.trans_le hC
  have hθ : 0 < θ := mul_pos (div_pos (mul_pos hκ ha) hC₀) hmargin
  let r := min (run.Δ 0 * φ 0) (P.γ₁ * θ)
  have hr : 0 < r := lt_min (mul_pos (run.delta_pos 0) (hφ 0)) (mul_pos P.gamma₁_pos hθ)
  refine ⟨r, hr, ?_⟩
  have hforce (k : ℕ) (hk : run.Δ k ≤ θ / φ k) : k ∈ run.verySuccessful := by
    have hsmall : run.Δ k ≤ κ * ‖g k‖ / (C * φ k) * (1 - P.η₂ - e / κ) := by
      refine hk.trans ?_
      have hrew : θ / φ k = κ * a / (C * φ k) * (1 - P.η₂ - e / κ) := by
        dsimp [θ]
        field_simp
      rw [hrew]
      gcongr
      · exact (mul_pos hC₀ (hφ k)).le
      · exact hg k
    exact (theorem_8_4_3 (hφ k) hC he (run.delta_pos k)
      (norm_pos_iff.mp (ha.trans_le (hg k))) (hval k) (hdec k)
      (herr k) hsmall (run.radius_update k)).1
  intro k
  induction k with
  | zero =>
    exact (div_le_iff₀ (hφ 0)).mpr (min_le_left _ _)
  | succ k ih =>
    have hdiv : r / φ (k + 1) ≤ r / φ k :=
      div_le_div_of_nonneg_left hr.le (hφ k) (hmono (Nat.le_succ k))
    have hup := run.radius_update k
    by_cases hk : k ∈ run.verySuccessful
    · exact hdiv.trans (ih.trans (hup.very_successful hk))
    · have hrad : θ / φ k < run.Δ k := lt_of_not_ge (fun h => hk (hforce k h))
      have hstep : P.γ₁ * run.Δ k ≤ run.Δ (k + 1) := by
        by_cases hk' : k ∈ run.successful
        · exact (mul_le_mul_of_nonneg_right P.gamma₁_le_gamma₂ (run.delta_pos k).le).trans
            (hup.successful hk' (lt_of_not_ge hk)).1
        · exact (hup.unsuccessful (lt_of_not_ge hk')).1
      calc
        _ ≤ r / φ k := hdiv
        _ ≤ (P.γ₁ * θ) / φ k :=
          div_le_div_of_nonneg_right (min_le_right _ _) (hφ k).le
        _ = P.γ₁ * (θ / φ k) := mul_div_assoc ..
        _ ≤ P.γ₁ * run.Δ k := mul_le_mul_of_nonneg_left hrad.le P.gamma₁_pos.le
        _ ≤ _ := hstep

private theorem summable_of_successful_summable {w Δ : ℕ → ℝ} {S : Set ℕ} [DecidablePred (· ∈ S)] {γ Γ r : ℝ}
    (hw : ∀ k, 0 ≤ w k) (hwmono : Antitone w)
    (hΔ : ∀ k, 0 < Δ k) (hγ : 0 < γ) (hγ₁ : γ < 1) (hΓ : 1 ≤ Γ) (hr : 0 < r)
    (hrad : ∀ k, r * w k ≤ Δ k) (hup : ∀ k, Δ (k + 1) ≤ (if k ∈ S then Γ else γ) * Δ k)
    (hsum : Summable (fun k => if k ∈ S then w k else 0)) :
    Summable w := by
  classical
  let σ (n : ℕ) := ((Finset.range n).filter (· ∈ S)).card
  have hσ₀ : σ 0 = 0 := by simp [σ]
  have hσle (n : ℕ) : σ n ≤ n := by simpa [σ] using Finset.card_filter_le (Finset.range n) (· ∈ S)
  have hσmono : Monotone σ := fun _ _ h =>
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h))
  have hσsucc (n : ℕ) : σ (n + 1) = σ n + if n ∈ S then 1 else 0 := by
    by_cases h : n ∈ S <;> simp [σ, Finset.range_add_one, Finset.filter_insert, h]
  have hgeom (n : ℕ) : Δ n ≤ Δ 0 * Γ ^ σ n * γ ^ (n - σ n) := by
    induction n with
    | zero => simp [hσ₀]
    | succ n ih =>
      have hbound := (hup n).trans (mul_le_mul_of_nonneg_left ih (by split <;> positivity))
      rw [hσsucc]
      by_cases h : n ∈ S
      · simp only [h, ite_true] at hbound ⊢
        rw [Nat.add_sub_add_right, pow_succ]
        convert hbound using 1; ring
      · simp only [h, ite_false, add_zero] at hbound ⊢
        have he : n + 1 - σ n = (n - σ n) + 1 := by have := hσle n; omega
        rw [he, pow_succ]
        convert hbound using 1; ring
  let q := (1 + γ) / 2
  let d := γ / q
  let a := Γ / q
  have hq : 0 < q := by dsimp [q]; linarith
  have hq₁ : q < 1 := by dsimp [q]; linarith
  have hd : 0 < d := div_pos hγ hq
  have hd₁ : d < 1 := (div_lt_one hq).mpr (by dsimp [q]; linarith)
  have ha : 0 ≤ a := div_nonneg (zero_le_one.trans hΓ) hq.le
  have hlim : Tendsto (fun m : ℕ => a * d ^ m) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := a)).mul (tendsto_pow_atTop_nhds_zero_of_lt_one hd.le hd₁)
  obtain ⟨m, hm⟩ := (hlim.eventually_lt_const one_pos).exists
  let p := m + 1
  let D : Set ℕ := {k | k + 1 ≤ p * σ k}
  have hsmall (n : ℕ) (hn : n ∉ D) : w n ≤ (Δ 0 / r) * q ^ n := by
    have hp : p * σ n ≤ n := by
      change ¬ n + 1 ≤ p * σ n at hn
      omega
    have hpow : m * σ n ≤ n - σ n := by
      change (m + 1) * σ n ≤ n at hp
      rw [Nat.add_mul, one_mul] at hp
      omega
    have he : σ n + (n - σ n) = n := Nat.add_sub_of_le (hσle n)
    have hfactor : a ^ σ n * d ^ (n - σ n) ≤ 1 := calc
      _ ≤ a ^ σ n * d ^ (m * σ n) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hd.le hd₁.le hpow) (pow_nonneg ha _)
      _ = (a * d ^ m) ^ σ n := by rw [pow_mul, mul_pow]
      _ ≤ 1 := pow_le_one₀ (mul_nonneg ha (pow_nonneg hd.le _)) hm.le
    have hscaled : Δ n ≤ Δ 0 * q ^ n := calc
      _ ≤ Δ 0 * Γ ^ σ n * γ ^ (n - σ n) := hgeom n
      _ = (Δ 0 * q ^ n) * (a ^ σ n * d ^ (n - σ n)) := by
        have hqa : q * a = Γ := by dsimp [a]; field_simp
        have hqd : q * d = γ := by dsimp [d]; field_simp
        have hqn : q ^ n = q ^ σ n * q ^ (n - σ n) := by rw [← pow_add, he]
        rw [hqn, ← hqa, ← hqd, mul_pow, mul_pow]
        ring
      _ ≤ _ := mul_le_of_le_one_right (mul_nonneg (hΔ 0).le (pow_nonneg hq.le _)) hfactor
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hr).mpr (by rw [mul_comm]; exact (hrad n).trans hscaled)
  have hDcount (n : ℕ) : ((Finset.range n).filter (· ∈ D)).card ≤ p * σ n := by
    calc
      _ ≤ (Finset.range (p * σ n)).card := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨hin, hiD⟩ := Finset.mem_filter.mp hi
        have hle := hσmono (Finset.mem_range.mp hin).le
        exact Finset.mem_range.mpr (Nat.lt_of_succ_le
          (hiD.trans (Nat.mul_le_mul_left p hle)))
      _ = _ := Finset.card_range _
  let b (n : ℕ) := (p : ℝ) * σ n - (((Finset.range n).filter (· ∈ D)).card : ℝ)
  have hb (n : ℕ) : 0 ≤ b n := by
    apply sub_nonneg.mpr
    exact_mod_cast hDcount n
  have hbsucc (n : ℕ) : b (n + 1) = b n +
      (if n ∈ S then (p : ℝ) else 0) - (if n ∈ D then 1 else 0) := by
    dsimp only [b]
    rw [hσsucc]
    by_cases hS : n ∈ S <;> by_cases hD : n ∈ D <;>
      simp [hS, hD, Finset.range_add_one, Finset.filter_insert] <;> ring
  have hprefix (n : ℕ) :
      (∑ i ∈ Finset.range n, if i ∈ D then w i else 0) + b n * w n ≤
        (p : ℝ) * ∑ i ∈ Finset.range n, if i ∈ S then w i else 0 := by
    induction n with
    | zero => simp [b, hσ₀]
    | succ n ih =>
      have hmono := mul_le_mul_of_nonneg_left (hwmono (Nat.le_succ n)) (hb (n + 1))
      rw [hbsucc] at hmono
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hbsucc]
      by_cases hS : n ∈ S <;> by_cases hD : n ∈ D <;>
        simp only [hS, hD, ite_true, ite_false] at hmono ⊢ <;> nlinarith only [ih, hmono]
  have hDsum : Summable (fun k => if k ∈ D then w k else 0) := by
    apply summable_of_sum_range_le (c := (p : ℝ) * ∑' k, if k ∈ S then w k else 0)
    · intro k; split <;> simp_all
    · intro n
      have hsumle := hsum.sum_le_tsum (Finset.range n) (fun i _ => by split <;> simp_all)
      have h := (hprefix n).trans (mul_le_mul_of_nonneg_left hsumle (Nat.cast_nonneg _))
      exact le_of_add_le_of_nonneg_left h (mul_nonneg (hb n) (hw n))
  have hrest : Summable (fun k => if k ∈ D then 0 else w k) := by
    have hqsum := (summable_geometric_of_lt_one hq.le hq₁).mul_left (Δ 0 / r)
    refine Summable.of_nonneg_of_le (fun k => by split <;> simp_all) (fun k => ?_) hqsum
    by_cases hk : k ∈ D
    · simpa only [hk, ite_true] using mul_nonneg (div_nonneg (hΔ 0).le hr.le) (pow_nonneg hq.le k)
    · simpa [hk] using hsmall k hk
  convert hDsum.add hrest using 1
  funext k
  by_cases hk : k ∈ D <;> simp [hk]

/-- Under the inexact gradient and running-curvature bounds, every positive
model-gradient threshold is crossed arbitrarily late. -/
theorem frequently_model_gradient_norm_lt [NormedSpace ℝ E] {P : BTRParams} {f : E → ℝ}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop} (run : BTRRun f P sufficient)
    (g : ℕ → E) (φ : ℕ → ℝ) {κ C e Γ : ℝ} (hC : 1 ≤ C) (he : 0 ≤ e)
    (hφ : ∀ k, 0 < φ k) (hmono : Monotone φ) (hdiv : ¬ Summable (fun k => (φ k)⁻¹))
    (hmargin : 0 < 1 - P.η₂ - e / κ) (hΓ : 1 ≤ Γ)
    (hΓup : ∀ k ∈ run.verySuccessful, run.Δ (k + 1) ≤ Γ * run.Δ k)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (g k) (φ k) (run.Δ k) κ)
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤
      e * ‖g k‖ * run.Δ k + C * φ k * (run.Δ k) ^ 2)
    (hlower : BddBelow (Set.range f)) :
    ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, ‖g k‖ < ε := by
  classical
  intro ε hε
  by_contra hn
  have hev : ∀ᶠ k in atTop, ε ≤ ‖g k‖ := by
    simpa only [Filter.Frequently, not_not, not_lt] using hn
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  let R := run.tail N
  let w (k : ℕ) := (φ (N + k))⁻¹
  obtain ⟨r, hr, hrad⟩ := theorem_8_4_4 R (fun k => g (N + k)) (fun k => φ (N + k))
    hC he hε (fun k => hN _ (Nat.le_add_right N k)) (fun _ => hφ _)
    (fun _ _ h => hmono (Nat.add_le_add_left h N)) hmargin
    (fun _ => hval _) (fun _ => hdec _) (fun _ => herr _)
  let a := P.η₁ * (κ * ε * min ε r)
  have hκ := (hdec 0).1.1
  have ha : 0 < a := mul_pos P.eta₁_pos (mul_pos (mul_pos hκ hε) (lt_min hε hr))
  have hw (k : ℕ) : 0 ≤ w k := inv_nonneg.mpr (hφ _).le
  have hdrop (k : ℕ) : a * (if k ∈ R.successful then w k else 0) ≤
      f (R.x k) - f (R.x (k + 1)) := by
    by_cases hk : k ∈ R.successful
    · simp only [hk, ite_true]
      have hgk := hN (N + k) (Nat.le_add_right N k)
      have hmin : min ε r * w k ≤ min (‖g (N + k)‖ / φ (N + k)) (R.Δ k) := by
        apply le_min
        · exact mul_le_mul_of_nonneg_right ((min_le_left _ _).trans hgk) (hw k)
        · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (hw k)).trans
            (by simpa only [div_eq_mul_inv] using hrad k)
      have hmodel := (hdec (N + k)).2
      change κ * ‖g (N + k)‖ * min (‖g (N + k)‖ / φ (N + k)) (R.Δ k) ≤
        R.model k (R.x k) - R.model k (R.x k + R.s k) at hmodel
      calc
        _ = P.η₁ * ((κ * ε) * (min ε r * w k)) := by dsimp [a]; ring
        _ ≤ P.η₁ * (R.model k (R.x k) - R.model k (R.x k + R.s k)) := by
          apply mul_le_mul_of_nonneg_left _ P.eta₁_pos.le
          exact (mul_le_mul (mul_le_mul_of_nonneg_left hgk hκ.le) hmin
            (mul_nonneg (le_min hε.le hr.le) (hw k))
            (mul_nonneg hκ.le (norm_nonneg _))).trans hmodel
        _ ≤ _ := R.objective_drop_of_successful hk
    · simp [hk, R.iterate_eq_of_unsuccessful hk]
  obtain ⟨L, hL⟩ := hlower
  have hsum : Summable (fun k => if k ∈ R.successful then w k else 0) := by
    refine summable_of_sum_range_le (c := (f (R.x 0) - L) / a)
      (fun k => by split <;> simp_all) fun n => ?_
    apply (le_div_iff₀ ha).mpr
    rw [mul_comm, Finset.mul_sum]
    calc
      _ ≤ ∑ k ∈ Finset.range n, (f (R.x k) - f (R.x (k + 1))) :=
        Finset.sum_le_sum (fun k _ => hdrop k)
      _ = f (R.x 0) - f (R.x n) := Finset.sum_range_sub' (fun k => f (R.x k)) n
      _ ≤ _ := sub_le_sub_left (hL ⟨R.x n, rfl⟩) _
  apply hdiv
  apply (summable_nat_add_iff N).mp
  simp only [Nat.add_comm _ N]
  apply summable_of_successful_summable (S := R.successful) (Δ := R.Δ) hw
    (fun _ _ h => inv_anti₀ (hφ _) (hmono (Nat.add_le_add_left h N)))
    R.delta_pos (P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂) P.gamma₂_lt_one hΓ hr
    (fun k => by simpa only [div_eq_mul_inv] using hrad k) _ hsum
  intro k
  have hup := R.radius_update k
  by_cases hk : k ∈ R.successful
  · rw [ite_eq_left hk]
    by_cases hk' : k ∈ R.verySuccessful
    · exact hΓup (N + k) hk'
    · exact (hup.successful hk (lt_of_not_ge hk')).2.trans
        (le_mul_of_one_le_left (R.delta_pos k).le hΓ)
  · rw [ite_eq_right hk]
    exact (hup.unsuccessful (lt_of_not_ge hk)).2

/-- Theorem 8.4.5. The model gradient norms have zero lower limit. -/
theorem theorem_8_4_5 [NormedSpace ℝ E] {P : BTRParams} {f : E → ℝ}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop} (run : BTRRun f P sufficient)
    (g : ℕ → E) (φ : ℕ → ℝ) {κ C e Γ : ℝ} (hC : 1 ≤ C) (he : 0 ≤ e)
    (hφ : ∀ k, 0 < φ k) (hmono : Monotone φ) (hdiv : ¬ Summable (fun k => (φ k)⁻¹))
    (hmargin : 0 < 1 - P.η₂ - e / κ) (hΓ : 1 ≤ Γ)
    (hΓup : ∀ k ∈ run.verySuccessful, run.Δ (k + 1) ≤ Γ * run.Δ k)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (g k) (φ k) (run.Δ k) κ)
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤
      e * ‖g k‖ * run.Δ k + C * φ k * (run.Δ k) ^ 2)
    (hlower : BddBelow (Set.range f)) :
    liminf (fun k => ‖g k‖) atTop = 0 := by
  have hfreq := frequently_model_gradient_norm_lt run g φ hC he hφ hmono hdiv hmargin
    hΓ hΓup hval hdec herr hlower
  have hb : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) (fun k ↦ ‖g k‖) :=
    ⟨0, show ∀ᶠ k in atTop, 0 ≤ ‖g k‖ from Eventually.of_forall fun _ ↦ norm_nonneg _⟩
  have hco : (atTop : Filter ℕ).IsCoboundedUnder (· ≥ ·) (fun k ↦ ‖g k‖) := by
    refine ⟨1, fun b hb' ↦ ?_⟩
    obtain ⟨k, hk, hk'⟩ := ((hfreq 1 zero_lt_one).and_eventually hb').exists
    exact hk'.trans hk.le
  refine le_antisymm ?_ (le_liminf_of_le hco (Eventually.of_forall fun _ ↦ norm_nonneg _))
  by_contra! hp
  have hlim := liminf_le_of_frequently_le ((hfreq _ (half_pos hp)).mono fun _ h ↦ h.le) hb
  linarith

/-- Theorem 8.4.6. With finitely many successes, the run is stationary at a
first-order critical point. The small model gradients supplied by Theorem
8.4.5 transfer to the true gradient via AM.3b. -/
theorem theorem_8_4_6 [NormedSpace ℝ E] {P : BTRParams} {f : E → ℝ}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop} (run : BTRRun f P sufficient)
    (g : ℕ → E) (df : E → E) {κ : ℝ} (hκ : 0 ≤ κ)
    (herr : ∀ k, ‖df (run.x k) - g k‖ ≤ κ * ‖g k‖)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, ‖g k‖ < ε)
    (hfinite : run.successful.Finite) :
    ∃ x, (∀ᶠ k in atTop, run.x k = x) ∧ df x = 0 := by
  obtain ⟨n, hn⟩ := hfinite.bddAbove
  have hx (j : ℕ) : run.x (n + 1 + j) = run.x (n + 1) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      exact (run.iterate_eq_of_unsuccessful (fun hk => by
        have hle : n + 1 + j ≤ n := hn hk
        omega)).trans ih
  have heq : ∀ᶠ k in atTop, run.x k = run.x (n + 1) := by
    apply eventually_atTop.mpr
    exact ⟨n + 1, fun k hk => by simpa only [Nat.add_sub_of_le hk] using hx (k - (n + 1))⟩
  refine ⟨run.x (n + 1), heq, ?_⟩
  by_contra hdf
  have hpos := norm_pos_iff.mpr hdf
  have hκ' : 0 < κ + 1 := by linarith
  obtain ⟨k, hk, hk'⟩ := ((hsmall _ (div_pos hpos hκ')).and_eventually heq).exists
  have hbound := norm_add_le (df (run.x k) - g k) (g k)
  rw [sub_add_cancel, hk'] at hbound
  have hrel := herr k
  rw [hk'] at hrel
  have hlt := (lt_div_iff₀ hκ').mp hk
  nlinarith only [hbound, hrel, hlt]

/-- Theorem 8.4.7. Once the scaled objective drops tend to zero on successful
iterations, every excursion with gradient bounded away from zero is too short
to reach the next small gradient. The weak convergence input is Theorem 8.4.5. -/
theorem theorem_8_4_7 [NormedSpace ℝ E] {P : BTRParams} {f : E → ℝ}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop} (run : BTRRun f P sufficient)
    (g : ℕ → E) (df : E → E) (φ : ℕ → ℝ) {κ e K L : ℝ}
    (he : 0 ≤ e) (he₁ : e < 1) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hφ : ∀ k, 0 < φ k)
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (g k) (φ k) (run.Δ k) κ)
    (hstep : ∀ k, ‖run.s k‖ ≤ K * run.Δ k)
    (herr : ∀ k, ‖df (run.x k) - g k‖ ≤ e * ‖g k‖)
    (hLip : ∀ x y, ‖df x - df y‖ ≤ L * ‖x - y‖)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, ‖g k‖ < ε)
    (hscaled : Tendsto (fun k => φ k * (f (run.x k) - f (run.x (k + 1))))
      (atTop ⊓ 𝓟 run.successful) (𝓝 0))
    (hlower : BddBelow (Set.range f)) :
    Tendsto (fun k => ‖g k‖) atTop (𝓝 0) ∧
      Tendsto (fun k => ‖df (run.x k)‖) atTop (𝓝 0) := by
  let F (k : ℕ) := f (run.x k)
  have hF := run.objective_antitone
  have hFbound : BddBelow (Set.range F) :=
    hlower.mono (show Set.range F ⊆ Set.range f from fun _ ⟨k, hk⟩ => ⟨run.x k, hk⟩)
  have hlim := tendsto_atTop_ciInf hF hFbound
  have htrue : Tendsto (fun k => ‖df (run.x k)‖) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    refine ⟨fun b hb => Eventually.of_forall (fun k => hb.trans_le (norm_nonneg _)), ?_⟩
    intro ε hε
    let δ := ε / (2 * (e + 1))
    have he' : 0 < e + 1 := by linarith
    have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) he')
    have hδeq : (e + 1) * δ = ε / 2 := by
      dsimp [δ]
      field_simp
    let c := P.η₁ * (κ * δ)
    have hc : 0 < c := mul_pos P.eta₁_pos (mul_pos (hdec 0).1.1 hδ)
    have hbelow := hscaled.eventually (gt_mem_nhds (mul_pos hc hδ))
    rw [eventually_inf_principal] at hbelow
    obtain ⟨N, hN⟩ := eventually_atTop.mp hbelow
    let B := L * (K / c)
    have hB : 0 ≤ B := mul_nonneg hL (div_nonneg hK hc.le)
    let τ := (ε / 2) / (B + 1)
    have hB' : 0 < B + 1 := by linarith
    have hτ : 0 < τ := div_pos (half_pos hε) hB'
    obtain ⟨M, hM⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (lt_add_of_pos_right _ hτ)))
    apply eventually_atTop.mpr
    refine ⟨max N M, fun n hn => ?_⟩
    have hnN : N ≤ n := (le_max_left _ _).trans hn
    have hnM : M ≤ n := (le_max_right _ _).trans hn
    have hex : ∃ k, n ≤ k ∧ ‖g k‖ < δ := by
      obtain ⟨k, hk, hkn⟩ := ((hsmall δ hδ).and_eventually (eventually_ge_atTop n)).exists
      exact ⟨k, hkn, hk⟩
    let j := Nat.find hex
    obtain ⟨hnj, hj⟩ := Nat.find_spec hex
    have hpath (t : ℕ) (ht : n + t ≤ j) :
        ‖run.x n - run.x (n + t)‖ ≤ (K / c) * (F n - F (n + t)) := by
      induction t with
      | zero => simp
      | succ t ih =>
        let k := n + t
        have hkj : k < j := by dsimp [k]; omega
        have hgk : δ ≤ ‖g k‖ := le_of_not_gt fun hgk =>
          Nat.find_min hex hkj ⟨Nat.le_add_right n t, hgk⟩
        have hkN := hnN.trans (Nat.le_add_right n t)
        have hmove : ‖run.x k - run.x (k + 1)‖ ≤ (K / c) * (F k - F (k + 1)) := by
          by_cases hk : k ∈ run.successful
          · have hmd := (hdec k).2
            have hm : κ * δ * min (δ / φ k) (run.Δ k) ≤
                run.model k (run.x k) - run.model k (run.x k + run.s k) := by
              refine (mul_le_mul (mul_le_mul_of_nonneg_left hgk (hdec k).1.1.le)
                (min_le_min (div_le_div_of_nonneg_right hgk (hφ k).le) le_rfl)
                (le_min (div_nonneg hδ.le (hφ k).le) (run.delta_pos k).le)
                (mul_nonneg (hdec k).1.1.le (norm_nonneg _))).trans hmd
            have hdrop : c * min (δ / φ k) (run.Δ k) ≤ F k - F (k + 1) := by
              simpa only [c, mul_assoc] using
                (mul_le_mul_of_nonneg_left hm P.eta₁_pos.le).trans (run.objective_drop_of_successful hk)
            have hrad : run.Δ k ≤ δ / φ k := by
              by_contra! hn'
              rw [min_eq_left hn'.le] at hdrop
              have hb := mul_le_mul_of_nonneg_left hdrop (hφ k).le
              have heq : φ k * (c * (δ / φ k)) = c * δ := by field_simp [(hφ k).ne']
              rw [heq] at hb
              exact (hN k hkN hk).not_ge hb
            rw [min_eq_right hrad] at hdrop
            have hx : run.x (k + 1) = run.x k + run.s k := by
              rw [run.iterate_update, Optimization.acceptStep_of_le hk]
            rw [hx, sub_add_cancel_left, norm_neg]
            apply (hstep k).trans
            have hdiv : run.Δ k ≤ (F k - F (k + 1)) / c :=
              (le_div_iff₀ hc).mpr (by rwa [mul_comm])
            rw [div_mul_eq_mul_div, mul_div_assoc]
            exact mul_le_mul_of_nonneg_left hdiv hK
          · simp [run.iterate_eq_of_unsuccessful hk, F]
        have hprev := ih hkj.le
        calc
          _ ≤ ‖run.x n - run.x k‖ + ‖run.x k - run.x (k + 1)‖ := by
            simpa only [sub_add_sub_cancel, k, Nat.add_assoc] using
              norm_add_le (run.x n - run.x k) (run.x k - run.x (k + 1))
          _ ≤ _ := by
            have hb := add_le_add hprev hmove
            change _ ≤ (K / c) * (F n - F (k + 1))
            linarith only [hb]
    have hnj' : n + (j - n) = j := Nat.add_sub_of_le hnj
    have hdist := hpath (j - n) hnj'.le
    rw [hnj'] at hdist
    have hchange := (hLip (run.x n) (run.x j)).trans (mul_le_mul_of_nonneg_left hdist hL)
    rw [← mul_assoc] at hchange
    have hdrop : F n - F j < τ := by
      have hlimle := ciInf_le hFbound j
      have hnear : F n < (⨅ k, F k) + τ := hM n hnM
      linarith
    have hBτ : B * τ < ε / 2 := by
      have hτeq : (B + 1) * τ = ε / 2 := by dsimp [τ]; field_simp
      linarith
    have hdif : ‖df (run.x n) - df (run.x j)‖ < ε / 2 :=
      hchange.trans_lt ((mul_le_mul_of_nonneg_left hdrop.le hB).trans_lt hBτ)
    have hend := norm_add_le (df (run.x j) - g j) (g j)
    rw [sub_add_cancel] at hend
    have hend' : ‖df (run.x j)‖ < ε / 2 := by
      have hh := mul_lt_mul_of_pos_left hj he'
      rw [hδeq] at hh
      linarith [herr j]
    have hstart := norm_add_le (df (run.x n) - df (run.x j)) (df (run.x j))
    rw [sub_add_cancel] at hstart
    linarith
  refine ⟨?_, htrue⟩
  have hfzero : Tendsto (fun k => df (run.x k)) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero] using htrue)
  have hgzero := (lemma_8_4_1 he₁ herr).mpr hfzero
  simpa only [sub_zero] using tendsto_iff_norm_sub_tendsto_zero.mp hgzero

/-- Corrected Theorem 8.4.8. Near the nondegenerate limit point, eventual model
convexity must control every trial segment used in the neighborhood trapping
argument. Convexity only along the convergent subsequence supplies no such
control at the intervening iterates. The gradient convergence is Theorem 8.4.7. -/
theorem theorem_8_4_8 [NormedSpace ℝ E] {P : BTRParams} {f : E → ℝ}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop} (run : BTRRun f P sufficient)
    {x₀ : E} {j : ℕ → ℕ} (hj : Tendsto j atTop atTop)
    (hx : Tendsto (run.x ∘ j) atTop (𝓝 x₀)) (hf : ContDiff ℝ 2 f)
    (hzero : fderiv ℝ f x₀ = 0)
    (hcrit : Tendsto (fun k => ‖fderiv ℝ f (run.x k)‖) atTop (𝓝 0))
    {σ R μ e : ℝ} (hσ : 0 < σ) (hR : 0 < R) (hμ : 0 < μ) (he : 0 ≤ e)
    (hH : ∀ v, σ * ‖v‖ ≤ ‖fderiv ℝ (fderiv ℝ f) x₀ v‖)
    (hm : ∀ k z, z ∈ segment ℝ (run.x k) (run.x k + run.s k) →
      DifferentiableAt ℝ (run.model k) z)
    (hDm : ∀ k z, z ∈ segment ℝ (run.x k) (run.x k + run.s k) →
      DifferentiableAt ℝ (fderiv ℝ (run.model k)) z)
    (hgrad : ∀ k, ‖fderiv ℝ (run.model k) (run.x k) - fderiv ℝ f (run.x k)‖ ≤
      e * ‖fderiv ℝ f (run.x k)‖)
    (hcurv : ∀ᶠ k in atTop, ‖run.x k - x₀‖ < R →
      ∀ z ∈ segment ℝ (run.x k) (run.x k + run.s k), μ * ‖run.s k‖ ^ 2 ≤
        fderiv ℝ (fderiv ℝ (run.model k)) z (run.s k) (run.s k)) :
    Tendsto run.x atTop (𝓝 x₀) := by
  have hd := (hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiable
    (by norm_num) x₀
  obtain ⟨r, hr, hlow⟩ := norm_fderiv_lower_bound hd hzero hσ hH
  refine tendsto_of_local_step_bound (C := (2 / μ) * (e + 1)) (lt_min hR hr) (half_pos hσ)
    hcrit hj hx (fun k hk => hlow _ (hk.trans_le (min_le_right _ _))) ?_
  filter_upwards [hcurv] with k hk hnear
  have hseg (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      run.x k + t • run.s k ∈ segment ℝ (run.x k) (run.x k + run.s k) := by
    simpa only [add_sub_cancel_left] using
      (convex_segment (𝕜 := ℝ) (run.x k) (run.x k + run.s k)).add_smul_sub_mem
        (left_mem_segment ℝ (run.x k) _) (right_mem_segment ℝ (run.x k) _) ht
  have hs := lemma_6_5_1 hμ (fun t ht => hm k _ (hseg t ht))
    (fun t ht => hDm k _ (hseg t ht))
    (fun t ht => hk (hnear.trans_le (min_le_left _ _)) _ (hseg t ht))
    (sub_nonneg.mp (run.predicted_pos k).le)
  have hnorm : ‖fderiv ℝ (run.model k) (run.x k)‖ ≤ (e + 1) * ‖fderiv ℝ f (run.x k)‖ := by
    have hb := norm_add_le (fderiv ℝ (run.model k) (run.x k) - fderiv ℝ f (run.x k))
      (fderiv ℝ f (run.x k))
    rw [sub_add_cancel] at hb
    linarith [hgrad k]
  by_cases hsucc : k ∈ run.successful
  · rw [run.iterate_update, Optimization.acceptStep_of_le hsucc, add_sub_cancel_left, mul_assoc]
    exact hs.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))
  · rw [run.iterate_eq_of_unsuccessful hsucc, sub_self, norm_zero]
    positivity

end ConnGouldToint.Chapter08
