import Numlib.Analysis.InnerProductSpace.PiL2
import Numlib.Optimization.Complexity.SlowExample.Basic
import Numlib.Optimization.Complexity.SlowExample.DynamicAccuracy
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpIDA

/-!
# A slow ARqpIDA run on a nonconvex feasible set

The criterion of ARqpIDA ([cartis2022evaluation], Algorithm 13.1.2, `Optimization.arqpIDATest`)
asks for approximate optimality for *some* radii `δ ∈ (0, 1]^q`. On a line, the gradient spikes
`β_k ≈ ε^q/q!` of the slow example of [cartis2022evaluation], Theorem 12.2.17 meet it at radius
`1`, so the lower-bound mode of the radii control does not slow the method down there. On the
closed nonconvex set `X = {v | v 1 = 0} ∪ {v | ρ ≤ v 1} ⊂ ℝ²` (a line and a parallel half-plane at
distance `ρ ∈ (ε, 2ε]`, `Optimization.slitSet`) with `∂f/∂(v 1) = -1`, every radius `δ ≥ ρ` sees
the half-plane and fails the criterion, while radii `δ < ρ` (among them the radii `ε` of the run)
only see the line. With `ρ^n = ε^n (1 + 1/k_ε)`, `n = max(q - 1, 1)`, the first approximately
optimal iterate is `x_{k_ε}`, `k_ε = ⌈ε^{-q(p+1)/p}⌉`. After `k_ε` the run makes one more step, to
a point where the derivatives along the line vanish, and continues with accuracy-improving
iterations there.

## Main results

* `Optimization.exists_isARqpIDARun_slit`: an ARqpIDA run on `X` in the lower-bound mode of the
  radii control whose first approximately optimal iterate is `x_{k_ε}`.
-/

open Set Metric
open scoped Nat RealInnerProductSpace

namespace Optimization

section Slit

variable {e₁ e₂ : EuclideanSpace ℝ (Fin 2)}

/-- The weight `σ = (3/(p+2))^p` of the slit example satisfies `σ/(p+1)! ≤ 1/(2 q!)` for
`q ≤ p`. -/
private theorem slit_sigma_le {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    (3 / ((p : ℝ) + 2)) ^ p / ((p + 1)! : ℝ) ≤ 1 / (2 * q !) := by
  have hσ1 : (3 / ((p : ℝ) + 2)) ^ p ≤ 1 := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    exact pow_le_one₀ (by positivity) (by rw [div_le_one (by positivity)]; linarith)
  have hσ0 : 0 ≤ (3 / ((p : ℝ) + 2)) ^ p := by positivity
  have h2 : (2 * q ! : ℝ) ≤ (p + 1)! := by
    have h1 : 2 * q ! ≤ (q + 1)! := by
      rw [Nat.factorial_succ]; exact Nat.mul_le_mul_right _ (by omega)
    exact_mod_cast h1.trans (Nat.factorial_le (by omega))
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  nlinarith

/-- **A slow ARqpIDA run on a nonconvex feasible set** in the lower-bound mode of the radii
control, with exact derivatives, for every `1 ≤ q ≤ p`. There are `f_low`, `L ≥ 1` and `ε₀ > 0`
such that, for every `ε ∈ (0, ε₀]` (all `ε_j = ε`) and all ARqpIDA constants with orders `p, q`,
weight `σ₀ = (3/(p+2))^p`, initial radii `δ₀ = ε` and initial accuracies
`h_{0,i} ≤ κ_s ε^{p-i+1}`, there are `ρ ∈ (ε, 2ε]`, the closed feasible set
`X = {v | v 1 = 0} ∪ {v | ρ ≤ v 1}` (`v 1` is the second coordinate; a line and a parallel
half-plane at distance `ρ`), a `C^p` function `f ≥ f_low` with `L`-Lipschitz derivatives of orders
`0, …, p` and an ARqpIDA run on `X` with exact derivatives from `x₀ = 0` satisfying the radii
control in the lower-bound mode (`Optimization.ARqpDARadiiControl False` for every `L̄ ≥ 1`; all
radii are `ε`), whose first iterate that is `(ε, δ)`-approximately optimal on `X` for some radii
`δ ∈ (0, 1]^q` (`Optimization.arqpIDATest`) is `x_{k_ε}`, `k_ε = ⌈ε^{-q(p+1)/p}⌉`, after
`k_ε + 1 ≥ ε^{-q(p+1)/p} + 1` function and derivative evaluations.

The run follows the slow example of [cartis2022evaluation], Theorem 12.2.17 (`r = p`) on the line
`v 1 = 0`: `f(v) = G(v 0) + H(v 1)` with gradient spikes `G'(x_k) = -β_k`,
`β_k = (ε^q + ε^q (k_ε - k)/k_ε)/q!`, steps the minimizers of the model on the line (admissible
Step-2 steps, since (13.1.55)–(13.1.57) are local conditions, but not global minimizers of the
model on `X`, which are in the half-plane), `σ_k = σ₀`, `ρ_k = 1`, and `H'(0) = -1`, so that the
half-plane lowers the Taylor models by at least `ρ > ε`. Radii `δ < ρ` only see the line, where
the measure of order `q` is `β_k δ`; with `ρ^n = ε^n (1 + 1/k_ε)`, `n = max(q - 1, 1)`, this
exceeds `ε δ^q/q!` for every `δ < ρ` exactly when `k < k_ε`, and radii `δ ≥ ρ` reach the
half-plane. So the criterion fails at every radius before `k_ε`, while the Step-1 and Step-2 radii
`ε < ρ` only see the line, where the model measures at the steps vanish ([cartis2022evaluation],
Example 12.1.3). After `k_ε` one more step reaches a point where all derivatives of `G` vanish,
and the run continues with accuracy-improving iterations there. -/
theorem exists_isARqpIDARun_slit {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    ∃ flow L ε₀ : ℝ, 1 ≤ L ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ P : ARqpIDAParams,
      P.p = p → P.q = q → P.σ₀ = (3 / ((p : ℝ) + 2)) ^ p → (∀ j ∈ Finset.Icc 1 q, P.δ₀ j = ε) →
      (∀ i ∈ Finset.Icc 1 p, P.h₀ i ≤ P.κs * ε ^ (p - i + 1)) →
      ∃ (ρ : ℝ) (X : Set (EuclideanSpace ℝ (Fin 2))) (f : EuclideanSpace ℝ (Fin 2) → ℝ),
        ε < ρ ∧ ρ ≤ 2 * ε ∧ X = {v | v 1 = 0} ∪ {v | ρ ≤ v 1} ∧ IsClosed X ∧
        (∀ y, flow ≤ f y) ∧ LipschitzDerivsAnchored f univ univ 0 p (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 2)) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ)
          (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 2)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 2)) (acc : ℕ → Prop),
          IsARqpIDARun f X (fun _ => 0) P (fun _ => ε) 0 x σ δ δ₁ δs h D dd jk s
            acc ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k)) ∧
          (∀ Lb : ℝ, 1 ≤ Lb → ∀ k, ARqpDARadiiControl False P (fun _ => ε) Lb σ δs s acc k) ∧
          IsFirstHit (arqpIDATest f X P (fun _ => ε) x)
            ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ ∧
          ε ^ (-((q : ℝ) * (p + 1) / p)) + 1 ≤
            (derivEvalCount (fun i => ¬ acc i) ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) ∧
          ε ^ (-((q : ℝ) * (p + 1) / p)) + 1 ≤ (derivEvalCount
            (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i))
              ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) := by
  obtain ⟨e₁, he₁def⟩ : ∃ e : EuclideanSpace ℝ (Fin 2), e = EuclideanSpace.single 0 1 := ⟨_, rfl⟩
  obtain ⟨e₂, he₂def⟩ : ∃ e : EuclideanSpace ℝ (Fin 2), e = EuclideanSpace.single 1 1 := ⟨_, rfl⟩
  have hE : ‖e₁‖ = 1 ∧ ‖e₂‖ = 1 ∧ ⟪e₁, e₂⟫ = 0 := by
    subst he₁def he₂def
    exact ⟨by rw [PiLp.norm_single, norm_one], by rw [PiLp.norm_single, norm_one],
      EuclideanSpace.inner_single_single_of_ne (by decide)⟩
  have hq1 : 1 ≤ q := hq
  have hp1 : 1 ≤ p := hq1.trans hqp
  have hp0 : p ≠ 0 := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp1
  set σI : ℝ := (3 / ((p : ℝ) + 2)) ^ p with hσI
  have hσI0 : 0 < σI := by positivity
  have hσI1 : σI ≤ 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp1
    exact pow_le_one₀ (by positivity) (by rw [div_le_one (by positivity)]; linarith)
  have hpf : (0 : ℝ) < p ! := by positivity
  have hqf : (0 : ℝ) < q ! := by positivity
  obtain ⟨LG, BG, hLG, hBG, hGint⟩ := exists_slowGradSpike_interpolant hq1 hqp hσI0
  obtain ⟨LH, BH, hLH, hBH, H, hHc, hHL, hHB, hHd⟩ := exists_contDiff_isSpikeJetOf_one p hp1
  set L : ℝ := max 1 (max LG BG) + max 1 (max LH BH) with hL
  refine ⟨-(BG + BH), L, min (1 / 4) (σI / (4 * p !)), ?_, by positivity,
    fun ε hε hε0 P hPp hPq hσ hδ₀ hh₀ => ?_⟩
  · have := le_max_left 1 (max LG BG); have := le_max_left 1 (max LH BH); linarith
  have hε4 : ε ≤ 1 / 4 := hε0.trans (min_le_left _ _)
  have hεσ : ε ≤ σI / (4 * p !) := hε0.trans (min_le_right _ _)
  have hε1 : ε ≤ 1 := by linarith
  -- the data of the slow gradient example
  set e : ℝ := (q : ℝ) * (p + 1) / p with he
  set κ : ℕ := ⌈ε ^ (-e)⌉₊ with hκ
  have hκge : ε ^ (-e) ≤ κ := Nat.le_ceil _
  have hκ1 : 1 ≤ κ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hε _)).ne'
  have hκpos : (0 : ℝ) < κ := by exact_mod_cast hκ1
  set β : ℕ → ℝ := fun k => (ε ^ q + ε ^ q * ((κ : ℝ) - k) / κ) / q ! with hβ
  set ts : ℕ → ℝ := fun k => (p ! * β k / σI) ^ (1 / (p : ℝ)) with hts
  set ξ : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, ts i with hξ
  have hξ1 : ∀ k, ξ (k + 1) = ξ k + ts k := fun k => Finset.sum_range_succ _ _
  obtain ⟨G, hGc, hGL, hGB, hGs, hGz, hGv⟩ :=
    hGint ε κ ξ β hε hε1 rfl (fun _ => rfl) fun k _ => hξ1 k
  have hβb : ∀ k ≤ κ, ε ^ q / q ! ≤ β k ∧ β k ≤ 2 * ε ^ q / q ! := fun k hk => by
    have h0 := slowGap_nonneg (pow_pos hε q).le hk
    have h1 := slowGap_le (pow_pos hε q).le κ k
    exact ⟨div_le_div_of_nonneg_right (by linarith) hqf.le,
      div_le_div_of_nonneg_right (by linarith) hqf.le⟩
  have hβlt : ∀ k < κ, ε ^ q * (1 + 1 / κ) / q ! ≤ β k := fun k hk => by
    have hk' : (k : ℝ) + 1 ≤ κ := by exact_mod_cast hk
    refine div_le_div_of_nonneg_right ?_ hqf.le
    have : ε ^ q * (1 / κ) ≤ ε ^ q * ((κ : ℝ) - k) / κ := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hκpos.le)
        (by positivity)
    rw [mul_add, mul_one]
    linarith
  have hβκ : β κ = ε ^ q / q ! := by simp only [hβ, sub_self, mul_zero, zero_div, add_zero]
  have hβpos : ∀ k ≤ κ, 0 < β k := fun k hk => lt_of_lt_of_le (by positivity) (hβb k hk).1
  -- the steps
  have htsp : ∀ k ≤ κ, ts k ^ p = p ! * β k / σI := fun k hk => by
    have := hβpos k hk
    simp only [hts]
    rw [one_div, Real.rpow_inv_natCast_pow (by positivity) hp0]
  have hts0 : ∀ k ≤ κ, 0 < ts k := fun k hk => by
    have := hβpos k hk
    exact Real.rpow_pos_of_pos (by positivity) _
  have hts_ge : ∀ k ≤ κ, ε * ((p : ℝ) + 2) / 3 ≤ ts k := fun k hk => by
    have h1 : (ε * ((p : ℝ) + 2) / 3) ^ p = ε ^ p / σI := by
      rw [hσI, div_pow, mul_pow, div_pow, div_div_eq_mul_div]
    have h2 : ε ^ p ≤ p ! * β k := by
      have hεpq : ε ^ p ≤ ε ^ q := pow_le_pow_of_le_one hε.le hε1 hqp
      have hfq : (q ! : ℝ) ≤ p ! := by exact_mod_cast Nat.factorial_le hqp
      have := (hβb k hk).1
      calc ε ^ p ≤ ε ^ q := hεpq
        _ = q ! * (ε ^ q / q !) := by field_simp
        _ ≤ p ! * β k := mul_le_mul hfq this (by positivity) hpf.le
    have h3 : (ε * ((p : ℝ) + 2) / 3) ^ p ≤ ts k ^ p := by
      rw [h1, htsp k hk]; exact div_le_div_of_nonneg_right h2 hσI0.le
    exact (pow_le_pow_iff_left₀ (by positivity) (hts0 k hk).le hp0).1 h3
  have hts_ge' : ∀ k ≤ κ, ε ≤ ts k := fun k hk => by
    have := hts_ge k hk
    have : ε ≤ ε * ((p : ℝ) + 2) / 3 := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp1
      rw [le_div_iff₀ (by norm_num)]
      exact mul_le_mul_of_nonneg_left (by linarith) hε.le
    linarith
  have hts1 : ∀ k ≤ κ, ts k < 1 := fun k hk => by
    by_contra hcon
    have h1 : 1 ≤ ts k ^ p := one_le_pow₀ (not_lt.1 hcon)
    rw [htsp k hk] at h1
    have h2 : p ! * β k / σI ≤ 1 / 2 := by
      rw [div_le_iff₀ hσI0]
      have hb := (hβb k hk).2
      have hεq : ε ^ q ≤ ε := pow_le_of_le_one hε.le hε1 (by omega)
      have : β k ≤ 2 * ε := hb.trans (by
        rw [div_le_iff₀ hqf]
        have : (1 : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_pos q
        calc 2 * ε ^ q ≤ 2 * ε * 1 := by linarith
          _ ≤ 2 * ε * q ! := mul_le_mul_of_nonneg_left this (by positivity))
      have h4 : 4 * p ! * ε ≤ σI := by
        rw [le_div_iff₀ (by positivity)] at hεσ; linarith
      calc p ! * β k ≤ p ! * (2 * ε) := mul_le_mul_of_nonneg_left this hpf.le
        _ ≤ 1 / 2 * σI := by linarith
    linarith
  -- the function
  have hG1 : (fun t => 1 * G t) = G := funext fun t => one_mul _
  have hH1 : (fun t => 1 * H t) = H := funext fun t => one_mul _
  obtain ⟨hGr, hGb, hGl⟩ := ridge_const_mul_slow_bounds (G := G) (lam := 1) (e := e₁) hGc hBG
    hGL hGB one_pos le_rfl hE.1.le
  obtain ⟨hHr, hHb, hHl⟩ := ridge_const_mul_slow_bounds (G := H) (lam := 1) (e := e₂) hHc hBH
    hHL hHB one_pos le_rfl hE.2.1.le
  rw [hG1] at hGr hGb hGl
  rw [hH1] at hHr hHb hHl
  set f : EuclideanSpace ℝ (Fin 2) → ℝ := ridge G e₁ + ridge H e₂ with hfdef
  have hfc : ContDiff ℝ p f := hGr.add hHr
  have hf : LipschitzDerivsAnchored f univ univ 0 p (fun _ => L) := by
    refine .of_contDiff hfc (fun j hj => ?_) univ
    have hj := (Finset.mem_Icc.1 hj).2
    exact (hGl j hj).add (hHl j hj)
      (fun y _ => (hGr.of_le (by exact_mod_cast hj)).contDiffAt)
      (fun y _ => (hHr.of_le (by exact_mod_cast hj)).contDiffAt)
  have hfb : ∀ y, -(BG + BH) ≤ f y := fun y => by
    have := hGb y; have := hHb y; simp only [hfdef, Pi.add_apply]; linarith
  -- the feasible set
  set ρ : ℝ := ε * (1 + 1 / κ) ^ (((max (q - 1) 1 : ℕ) : ℝ)⁻¹) with hρ
  have hq0 : max (q - 1) 1 ≠ 0 := by omega
  have hqR : (0 : ℝ) < ((max (q - 1) 1 : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have ha1 : 1 < 1 + 1 / (κ : ℝ) := by
    have : 0 < 1 / (κ : ℝ) := by positivity
    linarith
  have ha2 : 1 + 1 / (κ : ℝ) ≤ 2 := by
    have : 1 / (κ : ℝ) ≤ 1 := by rw [div_le_one hκpos]; exact_mod_cast hκ1
    linarith
  have hερ : ε < ρ := lt_mul_of_one_lt_right hε (Real.one_lt_rpow ha1 (inv_pos.2 hqR))
  have hρ2 : ρ ≤ 2 * ε := by
    rw [hρ, mul_comm 2]
    refine mul_le_mul_of_nonneg_left ?_ hε.le
    calc (1 + 1 / (κ : ℝ)) ^ (((max (q - 1) 1 : ℕ) : ℝ)⁻¹) ≤ (1 + 1 / (κ : ℝ)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ha1.le (inv_le_one_of_one_le₀ (by
            exact_mod_cast Nat.one_le_iff_ne_zero.2 hq0))
      _ ≤ 2 := by rw [Real.rpow_one]; exact ha2
  have hρpow : ρ ^ max (q - 1) 1 = ε ^ max (q - 1) 1 * (1 + 1 / κ) := by
    rw [hρ, mul_pow, Real.rpow_inv_natCast_pow (by positivity) hq0]
  have hρ0 : 0 < ρ := hε.trans hερ
  set X : Set (EuclideanSpace ℝ (Fin 2)) := slitSet e₂ ρ with hX
  have hXeq : X = {v | v 1 = 0} ∪ {v | ρ ≤ v 1} := by
    ext v; simp [hX, slitSet, he₂def, EuclideanSpace.inner_single_left]
  have hXc : IsClosed X := isClosed_slitSet e₂ ρ
  -- the run
  subst hPp hPq
  have h11 : ∀ c : ℝ, ⟪e₁, c • e₁⟫ = c := fun c => by
    rw [inner_smul_right, inner_self_eq_one_of_norm_eq_one hE.1, mul_one]
  have h21 : ∀ c : ℝ, ⟪e₂, c • e₁⟫ = 0 := fun c => by
    rw [inner_smul_right, real_inner_comm, hE.2.2, mul_zero]
  have hn1 : ∀ c : ℝ, ‖c • e₁‖ = |c| := fun c => by
    rw [norm_smul, hE.1, mul_one, Real.norm_eq_abs]
  have hspan : ∀ v, ⟪e₂, v⟫ = 0 → ‖v‖ = |⟪e₁, v⟫| := fun v hv => by
    rw [he₁def]
    exact EuclideanSpace.norm_eq_abs_inner_single_of_forall_ne fun j hj => by
      rw [Fin.eq_one_of_ne_zero j hj, ← he₂def]; exact hv
  obtain ⟨xv, hxv⟩ : ∃ xv : ℕ → EuclideanSpace ℝ (Fin 2), ∀ k, xv k = ξ (min k (κ + 1)) • e₁ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨δv, hδv⟩ : ∃ δv : ℕ → ℕ → ℝ, ∀ k, δv k = if k = 0 then P.δ₀ else fun _ => ε :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨hv, hhv⟩ : ∃ hv : ℕ → ℕ → ℝ, ∀ k, hv k = fun i => P.γh ^ (k - (κ + 1)) * P.h₀ i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Dv, hDv⟩ : ∃ Dv : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 2)) ℝ,
      ∀ k, Dv k = ftaylorSeries ℝ f (xv k) := ⟨_, fun _ => rfl⟩
  obtain ⟨ddv, hddv⟩ : ∃ ddv : ℕ → ℕ → EuclideanSpace ℝ (Fin 2),
      ∀ k, ddv k = fun _ => if k ≤ κ then (P.ς * ε) • e₁ else 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨sv, hsv⟩ : ∃ sv : ℕ → EuclideanSpace ℝ (Fin 2),
      ∀ k, sv k = if k ≤ κ then ts k • e₁ else 0 := ⟨_, fun _ => rfl⟩
  have hxle : ∀ k ≤ κ + 1, xv k = ξ k • e₁ := fun k hk => by rw [hxv, min_eq_left hk]
  have hxgt : ∀ k, κ + 1 ≤ k → xv k = ξ (κ + 1) • e₁ := fun k hk => by rw [hxv, min_eq_right hk]
  have hx1 : ∀ k, ⟪e₂, xv k⟫ = 0 := fun k => by rw [hxv, h21]
  have hHk : ∀ k, IsSpikeJetOf P.p H 1 ⟪e₂, xv k⟫ 1 := fun k => by rw [hx1]; exact hHd
  have hGk : ∀ k ≤ κ, IsSpikeJetOf P.p G 1 ⟪e₁, xv k⟫ (β k) := fun k hk => by
    rw [hxle k (by omega), h11]; exact hGs k hk
  have hGz' : ∀ k, κ < k → IsSpikeJetOf P.p G 1 ⟪e₁, xv k⟫ 0 := fun k hk => by
    rw [hxgt k hk, h11]; exact hGz
  have hdecT : ∀ k ≤ κ, ∀ j ∈ Finset.Icc 1 P.p, ∀ d,
      (Dv k).taylorDecrement j d = β k * ⟪e₁, d⟫ + ⟪e₂, d⟫ := fun k hk j hj d => by
    rw [hDv, taylorDecrement_ridge_add_ridge hGc hHc (hGk k hk) (hHk k) (Finset.mem_Icc.1 hj).1
      (Finset.mem_Icc.1 hj).2, one_mul]
  have hdecZ : ∀ k, κ < k → ∀ j ∈ Finset.Icc 1 P.p, ∀ d,
      (Dv k).taylorDecrement j d = ⟪e₂, d⟫ := fun k hk j hj d => by
    rw [hDv, taylorDecrement_ridge_add_ridge hGc hHc (hGz' k hk) (hHk k) (Finset.mem_Icc.1 hj).1
      (Finset.mem_Icc.1 hj).2, one_mul, zero_mul, zero_add]
  have hfline : ∀ c : ℝ, f (c • e₁) = G c + H 0 := fun c => by
    simp only [hfdef, Pi.add_apply, ridge_apply, h11,
      h21]
  have hxs : ∀ k ≤ κ, xv (k + 1) = xv k + sv k := fun k hk => by
    rw [hxle (k + 1) (by omega), hxle k (by omega), hsv, ite_eq_left hk, hξ1, add_smul]
  have hdecs : ∀ k ≤ κ, (Dv k).taylorDecrement P.p (sv k) = β k * ts k := fun k hk => by
    rw [hdecT k hk _ (Finset.mem_Icc.2 ⟨hp1, le_rfl⟩), hsv, ite_eq_left hk,
        h11,
      h21, add_zero]
  have hρ1 : ∀ k ≤ κ, arqpIDARatio f P Dv xv sv k = 1 := fun k hk => by
    have hpos : 0 < β k * ts k := mul_pos (hβpos k hk) (hts0 k hk)
    rw [arqpIDARatio, reductionRatio_def, hdecs k hk, ← hxs k hk, hxle k (by omega),
      hxle (k + 1) (by omega), hfline, hfline, hGv k hk, hξ1]
    rw [show G (ξ k) + H 0 - (G (ξ k) - β k * (ξ k + ts k - ξ k) + H 0) = β k * ts k by ring,
      div_self hpos.ne']
  -- the model along the line
  have hmin : ∀ k ≤ κ, ∀ c : ℝ, regularizedModel (Dv k) P.p P.σ₀ (sv k) ≤
      regularizedModel (Dv k) P.p P.σ₀ (c • e₁) := fun k hk c => by
    obtain ⟨hm, -, -⟩ := isMinOn_neg_monomial_add_regularization le_rfl hp1 (σ := P.σ₀)
      (by rw [hσ]; exact hσI0) (hβpos k hk)
    have e : (β k / (P.σ₀ * (1 - 1)! / P.p !)) ^ (1 / ((P.p - 1 + 1 : ℕ) : ℝ)) = ts k := by
      rw [Nat.sub_add_cancel hp1, hσ]
      simp only [hts, Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one]
      congr 1; field_simp
    rw [e] at hm
    rw [hsv, ite_eq_left hk, hDv, regularizedModel_ridge_add_ridge hspan hp1 hGc hHc (hGk k
        hk) (hHk k) _
      (h21 _), regularizedModel_ridge_add_ridge hspan hp1 hGc hHc (hGk k hk)
          (hHk k) _
      (h21 _), h11, h11]
    exact (add_le_add_iff_left _).2 (isMinOn_iff.1 hm _ (mem_univ _))
  have hmodel : ∀ k ≤ κ, ∀ ℓ ∈ Finset.Icc 1 P.q, ∀ d, ‖d‖ ≤ ε → ⟪e₂, d⟫ = 0 →
      (ftaylorSeries ℝ (regularizedModel (Dv k) P.p P.σ₀) (sv k)).taylorDecrement ℓ d ≤ 0 :=
    fun k hk ℓ hℓ d hd hd1 => by
      have hℓp : ℓ ≤ P.p := (Finset.mem_Icc.1 hℓ).2.trans P.q_le_p
      have hσ0 : 0 < P.σ₀ := by rw [hσ]; exact hσI0
      rw [hsv, ite_eq_left hk, hDv, taylorDecrement_regularizedModel_ridge_add_ridge hE.1
          hE.2.2 hspan hp1 hGc hHc (hGk k hk)
        (hHk k) P.σ₀ (ts k) hd1 hℓp]
      have hm : negMonomialRegModel P.p 1 P.σ₀ (β k) =
          fun t : ℝ => -β k * t + P.σ₀ * |t| ^ (P.p + 1) / (P.p + 1)! := by
        funext t; simp [negMonomialRegModel]
      have ht : ts k = (β k * P.p ! / P.σ₀) ^ (1 / (P.p : ℝ)) := by
        simp only [hts, hσ]; ring_nf
      have h0 := taylorMeasure_linearRegModel_eq_zero (p := P.p) (j := ℓ)
        ⟨(Finset.mem_Icc.1 hℓ).1, hℓp⟩ (hβpos k hk) hσ0 (δ := ε) (Or.inr (by
          rw [← ht]
          have := hts_ge k hk
          nlinarith))
      have hle := taylorDecrement_le_taylorMeasure
        (ftaylorSeries ℝ (fun t : ℝ => -β k * t + P.σ₀ * |t| ^ (P.p + 1) / (P.p + 1)!)
          ((β k * P.p ! / P.σ₀) ^ (1 / (P.p : ℝ)))) ℓ (S := univ) (δ := ε) (d := ⟪e₁, d⟫)
        ⟨mem_closedBall_zero_iff.2 (by rw [Real.norm_eq_abs]; exact ((abs_real_inner_le_norm e₁
            d).trans (by rw [hE.1, one_mul])).trans hd),
          mem_univ _⟩
      rw [h0] at hle
      rw [hm, ht]
      exact hle
  -- the iterations
  have hσ54 : P.σ₀ / ((P.p + 1)! : ℝ) ≤ 1 / (2 * P.q !) := by
    rw [hσ]; exact slit_sigma_le P.one_le_q P.q_le_p
  have hstep : ∀ k, ARqpDAStep X P (fun _ => ε) xv (fun _ => P.σ₀) δv δv (fun _ _ => ε) hv Dv
      ddv (fun _ => P.q) sv (fun k => κ < k) (arqpIDARatio f P Dv xv sv) k := by
    intro k
    have hδk : ∀ j ∈ Finset.Icc 1 P.q, δv k j = ε := fun j hj => by
      rw [hδv]
      split_ifs
      · exact hδ₀ j hj
      · rfl
    by_cases hk : k ≤ κ
    · refine slit_arqpDAStep (t := ts k) hE.1 hE.2.1 hE.2.2 hε hε4 hερ (hβb k hk).1 (hβb k hk).2
        hσ54 (hx1 k) hδk
        (by rw [hδv, ite_eq_right (Nat.succ_ne_zero k)]) rfl (fun _ _ => rfl)
        (fun j => by rw [hddv, ite_eq_left hk]) rfl (hdecT k hk)
        (by rw [hsv, ite_eq_left hk]) (hmin k hk) (hmodel k hk)
        (by rw [hsv, ite_eq_left hk, hn1, abs_of_pos (hts0 k hk)]; exact hts1 k hk)
        (fun i hi => ?_) (not_lt.2 hk) (hxs k hk) rfl P.σmin_le_σ₀
        (by rw [hhv, hhv, Nat.sub_eq_zero_of_le (by omega), Nat.sub_eq_zero_of_le (by omega)])
        (hρ1 k hk)
      rw [hhv]
      dsimp only
      rw [Nat.sub_eq_zero_of_le (by omega), pow_zero, one_mul, hsv, ite_eq_left hk,
        hn1, abs_of_pos (hts0 k hk)]
      exact (hh₀ i hi).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hε.le (hts_ge' k hk) _) P.κs_pos.le)
    · have hk' : κ < k := not_le.1 hk
      refine slit_arqpDAStep_of_acc hE.2.1.le hε hερ (hx1 k) hδk rfl (fun j => by rw [hddv,
          ite_eq_right hk])
        (hdecZ k hk') hk' (by rw [hxgt k hk', hxgt (k + 1) (by omega)])
        (by rw [hδv, hδv, ite_eq_right (Nat.succ_ne_zero k), ite_eq_right (by omega)]) rfl
        fun i => ?_
      rw [hhv, hhv, show k + 1 - (κ + 1) = k - (κ + 1) + 1 by omega, pow_succ]
      ring
  have hrun : IsARqpIDARun f X (fun _ => 0) P (fun _ => ε) 0 xv (fun _ => P.σ₀) δv
      δv (fun _ _ => ε) hv Dv ddv (fun _ => P.q) sv (fun k => κ < k) :=
    ⟨fun _ _ => ⟨hε, hε1⟩, fun j hj => by rw [hδ₀ j hj], fun _ _ => le_rfl,
      by rw [hxle 0 (Nat.zero_le _)]; simp [hξ], Or.inl (inner_zero_right _), rfl,
      by rw [hδv, ite_eq_left rfl], by funext i; rw [hhv]; simp,
      fun k => by rw [hDv]; exact (jetApprox_self _ _).mono_err fun i _ => by simp, hstep⟩
  -- the criterion
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have htest : ∀ k ≤ κ, (arqpIDATest f X P (fun _ => ε) xv k ↔ k = κ) := by
    intro k hk
    have hdk : ∀ j ∈ Finset.Icc 1 P.q, ∀ d,
        (ftaylorSeries ℝ f (xv k)).taylorDecrement j d = β k * ⟪e₁, d⟫ + ⟪e₂, d⟫ :=
      fun j hj d => by rw [← hDv]; exact hdecT k hk j (P.Icc_q_subset hj) d
    constructor
    · rintro ⟨δ', hδ', ht'⟩
      by_contra hne
      exact not_isEpsDeltaApprox_slitSet hE.1 hE.2.1 hE.2.2 hε hερ hρpow (by positivity)
        (hβpos k hk).le (hβlt k (lt_of_le_of_ne hk hne)) (hx1 k) hq hdk hδ' ht'
    · rintro rfl
      exact ⟨fun _ => ε, fun _ _ => ⟨hε, hε1⟩,
        isEpsDeltaApprox_slitSet hE.1 hE.2.1.le hE.2.2 hε hε1 hερ (hβpos _ hk).le hβκ.le
          (hx1 _) hdk⟩
  refine ⟨ρ, X, f, hερ, hρ2, hXeq, hXc, hfb, hf, xv, fun _ => P.σ₀, δv, δv, fun _ _ => ε, hv,
    Dv, ddv, fun _ => P.q, sv, fun k => κ < k, hrun, hDv, fun Lb hLb k _ _ => ⟨fun h => h.elim,
      fun _ j _ => ?_⟩, ⟨(htest κ le_rfl).2 rfl, fun i hi ht' => hi.ne ((htest i hi.le).1 ht')⟩,
    ?_, ?_⟩
  · have hM : 1 ≤ max Lb P.σ₀ := hLb.trans (le_max_left _ _)
    have h0 : P.ς * P.θ ≤ 1 := (mul_le_of_le_one_left P.θ_pos.le P.ς_le_one).trans P.θ_lt_one.le
    rw [div_le_iff₀ (by positivity)]
    have h1 : P.ς * P.θ * ε ≤ ε := mul_le_of_le_one_left hε.le h0
    exact h1.trans (le_mul_of_one_le_right hε.le (by linarith only [hM]))
  · rw [derivEvalCount_of_forall fun i hi => not_lt.2 hi.le, Nat.cast_add, Nat.cast_one]
    linarith only [hκge]
  · rw [derivEvalCount_of_forall fun i hi => Or.inr ⟨not_lt.2 hi.le, by
      rw [hρ1 i hi.le]; exact P.η₁_le_η₂.trans P.η₂_lt_one.le⟩, Nat.cast_add, Nat.cast_one]
    linarith only [hκge]

end Slit

end Optimization
