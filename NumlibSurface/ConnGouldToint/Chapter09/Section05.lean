/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter09.Section02
import NumlibSurface.ConnGouldToint.Chapter06.Section04
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

/-! # Conditional models with memory -/

namespace ConnGouldToint.Chapter09

variable {E : Type*}

/-- The memory model (9.5.1), with the initial model equal to the initial local model. -/
noncomputable def memoryModel (q : ℕ → E → ℝ) (α : ℕ → ℝ) : ℕ → E → ℝ
  | 0 => q 0
  | k + 1 => fun z ↦ (1 - α (k + 1)) * q (k + 1) z + α (k + 1) * memoryModel q α k z

/-- The unrolled formula (9.5.2) for the memory model. -/
theorem memoryModel_eq_sum (q : ℕ → E → ℝ) (α : ℕ → ℝ) (hα₀ : α 0 = 0) (k : ℕ) (z : E) :
    memoryModel q α k z = ∑ i ∈ Finset.range (k + 1),
      (1 - α i) * (∏ j ∈ Finset.Ioc i k, α j) * q i z := by
  induction k with
  | zero => simp [memoryModel, hα₀]
  | succ k ih =>
    simp only [memoryModel, Finset.sum_range_succ (n := k + 1), Finset.Ioc_self,
      Finset.prod_empty, mul_one]
    rw [ih, Finset.mul_sum, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.prod_Ioc_succ_top (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    ring

/-- After the last accepted step, the local model stays fixed. The remaining
memory error is the initial error multiplied by exactly the intervening weights. -/
theorem memoryModel_sub_local_eq_prod (q : ℕ → E → ℝ) (α : ℕ → ℝ)
    {t k : ℕ} (ht : t ≤ k) {z : E} {v : ℝ} (hq : ∀ j, t < j → j ≤ k → q j z = v) :
    memoryModel q α k z - v =
      (∏ j ∈ Finset.Ioc t k, α j) * (memoryModel q α t z - v) := by
  induction k, ht using Nat.le_induction with
  | base => simp
  | succ k htk ih =>
    have hqk : q (k + 1) z = v := hq _ (Nat.lt_succ_of_le htk) le_rfl
    simp only [memoryModel, hqk]
    rw [Finset.prod_Ioc_succ_top htk]
    have hprev := ih (fun j hj hjk ↦ hq j hj (hjk.trans (Nat.le_succ k)))
    linear_combination α (k + 1) * hprev

private theorem abs_memoryModel_le (q : ℕ → E → ℝ) (α : ℕ → ℝ)
    {k : ℕ} {z : E} {B : ℝ} (hα : ∀ j, 0 ≤ α j ∧ α j ≤ 1)
    (hq : ∀ j ≤ k, |q j z| ≤ B) : |memoryModel q α k z| ≤ B := by
  induction k with
  | zero => exact hq 0 le_rfl
  | succ k ih =>
    have hprev := ih (fun j hj ↦ hq j (hj.trans (Nat.le_succ k)))
    change |(1 - α (k + 1)) * q (k + 1) z + α (k + 1) * memoryModel q α k z| ≤ B
    calc
      _ ≤ |(1 - α (k + 1)) * q (k + 1) z| + |α (k + 1) * memoryModel q α k z| :=
        abs_add_le _ _
      _ ≤ (1 - α (k + 1)) * B + α (k + 1) * B := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr (hα (k + 1)).2),
          abs_of_nonneg (hα (k + 1)).1]
        exact add_le_add (mul_le_mul_of_nonneg_left (hq _ le_rfl)
          (sub_nonneg.mpr (hα (k + 1)).2)) (mul_le_mul_of_nonneg_left hprev (hα (k + 1)).1)
      _ = B := by ring

/-- Theorem 9.5.1. The memory error after a fixed-center block decays
geometrically. The constant (B) bounds the earlier local models and the
new fixed local model at the point under consideration. -/
theorem theorem_9_5_1 (q : ℕ → E → ℝ) (α : ℕ → ℝ)
    {t k : ℕ} (ht : t < k) {z : E} {B a : ℝ} (ha : 0 ≤ a)
    (hα : ∀ j, 0 ≤ α j ∧ α j ≤ 1)
    (hcap : ∀ j ∈ Finset.Ioc t k, α j ≤ a)
    (hq : ∀ j ≤ t, |q j z| ≤ B) (hnew : |q k z| ≤ B)
    (hfixed : ∀ j, t < j → j ≤ k → q j z = q k z) :
    |memoryModel q α k z - q k z| ≤ 2 * B * a ^ (k - t) := by
  rw [memoryModel_sub_local_eq_prod q α ht.le hfixed, abs_mul,
    abs_of_nonneg (Finset.prod_nonneg fun j _ ↦ (hα j).1)]
  have hprod : (∏ j ∈ Finset.Ioc t k, α j) ≤ a ^ (k - t) := by
    calc
      _ ≤ ∏ _j ∈ Finset.Ioc t k, a := Finset.prod_le_prod₀ (fun j _ ↦ (hα j).1) hcap
      _ = _ := by simp
  have herr : |memoryModel q α t z - q k z| ≤ 2 * B :=
    (abs_sub _ _).trans (by linarith [abs_memoryModel_le q α hα hq])
  calc
    _ ≤ a ^ (k - t) * (2 * B) :=
      mul_le_mul hprod herr (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- The corrected conditional radius update satisfies the adjacent lower
factor required in (9.5.16). -/
theorem ConditionalRadiusRun.radius_next_ge_factor {η₀ η₁ γ₁ γ₂ : ℝ}
    (run : ConditionalRadiusRun η₀ η₁ γ₁ γ₂ False) (hγ : 0 < γ₁) (hγ₁ : γ₁ ≤ 1)
    (haccept : ∀ k, η₁ ≤ run.raw k → η₀ ≤ run.selected k) (k : ℕ) :
    γ₁ * run.radius k ≤ run.radius (k + 1) := by
  have hrad := mul_le_of_le_one_left (run.radius_and_ref_pos hγ k).2.le hγ₁
  by_cases h : η₁ ≤ run.raw k
  · have hnext := run.high_update k h
    rw [run.ref_reset k (Or.inl (haccept k h))] at hnext
    exact hrad.trans hnext
  · by_cases hv : run.valid k
    · have hnext := (run.low_update k (lt_of_not_ge h) (Or.inl hv)).1
      rwa [run.ref_reset k (Or.inr hv)] at hnext
    · rwa [run.invalid_update k (lt_of_not_ge h) hv not_false]

/-- The step-size restriction in AM.10 yields the radius bound (9.5.16)
under the adjacent lower update factor. -/
theorem memoryWeight_le_radius_rpow {α Δ Δ' s κ K γ ψ : ℝ}
    (hΔ' : 0 ≤ Δ') (hs : 0 ≤ s)
    (hκ : 0 ≤ κ) (hK : 0 ≤ K) (hγ : 0 < γ) (hψ : 0 ≤ ψ)
    (hstep : s ≤ K * Δ) (hupdate : γ * Δ ≤ Δ')
    (hweight : α ≤ κ * s ^ ψ) (hscale : κ * (K / γ) ^ ψ ≤ 1) :
    α ≤ Δ' ^ ψ := by
  have hprev : Δ ≤ Δ' / γ := (le_div_iff₀ hγ).mpr (by simpa only [mul_comm] using hupdate)
  have hbound : s ≤ (K / γ) * Δ' := by
    calc
      s ≤ K * Δ := hstep
      _ ≤ K * (Δ' / γ) := mul_le_mul_of_nonneg_left hprev hK
      _ = _ := by ring
  calc
    α ≤ κ * s ^ ψ := hweight
    _ ≤ κ * ((K / γ) * Δ') ^ ψ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs hbound hψ) hκ
    _ = (κ * (K / γ) ^ ψ) * Δ' ^ ψ := by
      rw [Real.mul_rpow (div_nonneg hK hγ.le) hΔ', mul_assoc]
    _ ≤ _ := mul_le_of_le_one_left (Real.rpow_nonneg hΔ' _) hscale

/-- A fixed number of recent memory factors suffices for a quadratic
error bound. The radius may vary throughout the rejected block. -/
theorem memoryProduct_le_radius_sq {α Δ : ℕ → ℝ} {γ ψ : ℝ}
    (hγ : 0 < γ) (hγ₁ : γ ≤ 1) (hψ : 0 < ψ)
    (hΔ : ∀ k, 0 < Δ k) (hstep : ∀ k, γ * Δ k ≤ Δ (k + 1))
    (hα : ∀ k, 0 ≤ α k ∧ α k ≤ 1) (hcap : ∀ k, α k ≤ (Δ k) ^ ψ) :
    ∃ (p : ℕ) (C : ℝ), 0 < C ∧
      ∀ t k, t + p ≤ k → (∏ j ∈ Finset.Ioc t k, α j) ≤ C * (Δ k) ^ 2 := by
  obtain ⟨p, hp⟩ := exists_nat_ge (2 / ψ)
  have hexp : 2 ≤ ψ * (p : ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hψ).mp hp
  let D := (γ ^ p) ^ (ψ * (p : ℝ))
  have hD : 0 < D := Real.rpow_pos_of_pos (pow_pos hγ _) _
  refine ⟨p, max 1 D⁻¹, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro t k htk
  by_cases hsmall : Δ k ≤ 1
  · have hback (j l : ℕ) (hj : j ≤ l) : γ ^ (l - j) * Δ j ≤ Δ l := by
      induction l, hj using Nat.le_induction with
      | base => simp
      | succ l hjl ih =>
        have hsub : l + 1 - j = l - j + 1 := by omega
        rw [hsub, pow_succ', mul_assoc]
        exact (mul_le_mul_of_nonneg_left ih hγ.le).trans (hstep l)
    have hlast (j : ℕ) (hj : j ∈ Finset.Ioc (k - p) k) :
        α j ≤ (Δ k / γ ^ p) ^ ψ := by
      have hj' := Finset.mem_Ioc.mp hj
      have hkp : k - j ≤ p := by omega
      have hjΔ : Δ j ≤ Δ k / γ ^ p := by
        apply (le_div_iff₀ (pow_pos hγ p)).mpr
        rw [mul_comm]
        exact (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hγ.le hγ₁ hkp)
          (hΔ j).le).trans (hback j k hj'.2)
      exact (hcap j).trans (Real.rpow_le_rpow (hΔ j).le hjΔ hψ.le)
    have hsubset : Finset.Ioc (k - p) k ⊆ Finset.Ioc t k := by
      intro j hj
      have hj' := Finset.mem_Ioc.mp hj
      exact Finset.mem_Ioc.mpr ⟨by omega, hj'.2⟩
    have hlen : k - (k - p) = p := by omega
    calc
      _ ≤ ∏ j ∈ Finset.Ioc (k - p) k, α j :=
        Finset.prod_le_prod_of_subset_of_le_one₀ hsubset (fun j _ ↦ (hα j).1)
          (fun j _ _ ↦ (hα j).2)
      _ ≤ ∏ _j ∈ Finset.Ioc (k - p) k, (Δ k / γ ^ p) ^ ψ :=
        Finset.prod_le_prod₀ (fun j _ ↦ (hα j).1) hlast
      _ = (Δ k / γ ^ p) ^ (ψ * (p : ℝ)) := by
        rw [Finset.prod_const, Nat.card_Ioc, hlen,
          Real.rpow_mul_natCast (div_nonneg (hΔ k).le (pow_nonneg hγ.le _))]
      _ = (Δ k) ^ (ψ * (p : ℝ)) / D := Real.div_rpow (hΔ k).le (pow_nonneg hγ.le _) _
      _ ≤ (Δ k) ^ (2 : ℕ) / D := by
        apply div_le_div_of_nonneg_right _ hD.le
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_ge (hΔ k) hsmall (by exact_mod_cast hexp)
      _ ≤ max 1 D⁻¹ * (Δ k) ^ 2 := by
        rw [div_eq_mul_inv, mul_comm ((Δ k) ^ 2)]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
  · have hprod : (∏ j ∈ Finset.Ioc t k, α j) ≤ 1 :=
      Finset.prod_le_one₀ (fun j _ ↦ (hα j).1) (fun j _ ↦ (hα j).2)
    have hsq : 1 ≤ (Δ k) ^ 2 := by nlinarith [le_of_not_ge hsmall, sq_nonneg (Δ k - 1)]
    exact hprod.trans (hsq.trans (le_mul_of_one_le_left (sq_nonneg _) (le_max_left _ _)))

/-- Corrected Theorem 9.5.2. The current local model has quadratic accuracy,
and after sufficiently many rejected steps the memory term has the same
order. The radius hypothesis is the adjacent lower update factor, which
allows varying radii during the rejection block. -/
theorem theorem_9_5_2 (f : E → ℝ) (q : ℕ → E → ℝ) {α Δ : ℕ → ℝ}
    {γ ψ A B : ℝ} (hγ : 0 < γ) (hγ₁ : γ ≤ 1) (hψ : 0 < ψ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hΔ : ∀ k, 0 < Δ k) (hstep : ∀ k, γ * Δ k ≤ Δ (k + 1))
    (hα : ∀ k, 0 ≤ α k ∧ α k ≤ 1) (hcap : ∀ k, α k ≤ (Δ k) ^ ψ)
    (t : ℕ) (region : ℕ → Set E)
    (hlocal : ∀ k, ∀ z ∈ region k, |f z - q k z| ≤ A * (Δ k) ^ 2)
    (hold : ∀ k > t, ∀ z ∈ region k, ∀ j ≤ t, |q j z| ≤ B)
    (hnew : ∀ k > t, ∀ z ∈ region k, |q k z| ≤ B)
    (hfixed : ∀ k > t, ∀ z ∈ region k, ∀ j, t < j → j ≤ k → q j z = q k z) :
    ∃ (p : ℕ) (C : ℝ), 0 < C ∧
      ∀ k > t, t + p ≤ k → ∀ z ∈ region k,
        |f z - memoryModel q α k z| ≤ C * (Δ k) ^ 2 := by
  obtain ⟨p, D, hD, hpow⟩ := memoryProduct_le_radius_sq hγ hγ₁ hψ hΔ hstep hα hcap
  refine ⟨p, 1 + A + 2 * B * D, by positivity, ?_⟩
  intro k hk hpk z hz
  have hinit : |memoryModel q α t z - q k z| ≤ 2 * B :=
    (abs_sub _ _).trans (by linarith [abs_memoryModel_le q α hα (hold k hk z hz), hnew k hk z hz])
  have herr : |memoryModel q α k z - q k z| ≤ 2 * B * D * (Δ k) ^ 2 := by
    rw [memoryModel_sub_local_eq_prod q α hk.le (hfixed k hk z hz), abs_mul,
      abs_of_nonneg (Finset.prod_nonneg fun j _ ↦ (hα j).1)]
    calc
      _ ≤ (D * (Δ k) ^ 2) * (2 * B) :=
        mul_le_mul (hpow t k hpk) hinit (abs_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    _ = |(f z - q k z) - (memoryModel q α k z - q k z)| := by congr 1; ring
    _ ≤ |f z - q k z| + |memoryModel q α k z - q k z| := abs_sub _ _
    _ ≤ A * (Δ k) ^ 2 + 2 * B * D * (Δ k) ^ 2 := add_le_add (hlocal k z hz) herr
    _ ≤ _ := by nlinarith [sq_nonneg (Δ k)]

open Chapter06 in
/-- The conditional-run form of Theorem 9.5.2. The local model depends only
on its center, and the norm comparison transfers step feasibility to AM.10. -/
theorem theorem_9_5_2_of_conditional_run {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → ℝ} (hf : ContDiff ℝ 2 f)
    (q : F → F → ℝ) (x s : ℕ → F) (p : ℕ → Seminorm ℝ F) (α : ℕ → ℝ)
    {η₀ η₁ γ₁ γ₂ K κ ψ B κf κm : ℝ}
    (run : ConditionalRadiusRun η₀ η₁ γ₁ γ₂ False)
    (hγ : 0 < γ₁) (hγ₁ : γ₁ ≤ 1) (hK : 0 ≤ K) (hκ : 0 ≤ κ) (hψ : 0 < ψ)
    (hB : 0 ≤ B) (hκm : 1 ≤ κm)
    (haccept : ∀ k, η₁ ≤ run.raw k → η₀ ≤ run.selected k)
    (hsep : ∀ k v, p k v = 0 → v = 0)
    (hnorm : ∀ k v, ‖v‖ ≤ K * p k v) (hstep : ∀ k, p k (s k) ≤ run.radius k)
    (hα : ∀ k, 0 ≤ α k ∧ α k ≤ 1) (hα₀ : α 0 = 0)
    (hweight : ∀ k, α (k + 1) ≤ κ * ‖s k‖ ^ ψ) (hscale : κ * (K / γ₁) ^ ψ ≤ 1)
    (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ κf)
    (hq : ∀ k, ContDiff ℝ 2 (q (x k)))
    (hval : ∀ k, q (x k) (x k) = f (x k))
    (hgrad : ∀ k, fderiv ℝ (q (x k)) (x k) = fderiv ℝ f (x k))
    (hHq : ∀ k z, z ∈ (p k).closedBall (x k) (run.radius k) →
      ‖fderiv ℝ (fderiv ℝ (q (x k))) z‖ ≤ κm - 1)
    (t : ℕ) (hfixed : ∀ k > t, x k = x (t + 1))
    (hlocalBound : ∀ k > t, ∀ z ∈ (p k).closedBall (x k) (run.radius k),
      ∀ j ≤ t + 1, |q (x j) z| ≤ B) :
    ∃ (n : ℕ) (C : ℝ), 0 < C ∧ ∀ k > t, t + n ≤ k →
      ∀ z ∈ (p k).closedBall (x k) (run.radius k),
        |f z - memoryModel (fun j ↦ q (x j)) α k z| ≤ C * (run.radius k) ^ 2 := by
  have hpos (k : ℕ) := (run.radius_and_ref_pos hγ k).2
  have hadj := run.radius_next_ge_factor hγ hγ₁ haccept
  have hcap (k : ℕ) : α k ≤ (run.radius k) ^ ψ := by
    cases k with
    | zero => rw [hα₀]; exact Real.rpow_nonneg (hpos 0).le _
    | succ k =>
      exact memoryWeight_le_radius_rpow (hpos (k + 1)).le (norm_nonneg _) hκ hK hγ hψ.le
        ((hnorm k _).trans (mul_le_mul_of_nonneg_left (hstep k) hK))
        (hadj k) (hweight k) hscale
  let A := uniformHessianConstant K κf κm
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg _)
    ((show 0 ≤ κm from zero_le_one.trans hκm).trans (le_max_right _ _))
  refine theorem_9_5_2 f (fun k ↦ q (x k)) hγ hγ₁ hψ hA hB
    hpos hadj hα hcap t (fun k ↦ (p k).closedBall (x k) (run.radius k)) ?_ ?_ ?_ ?_
  · intro k z hz
    have hz' : p k (z - x k) ≤ run.radius k := (Seminorm.mem_closedBall (p k)).mp hz
    have hDq := (hq k).fderiv_right (m := 1) (by norm_num)
    have he := (theorem_6_4_1 (p k) (hsep k) (hpos k).le hκm hz' hf hF
      (fun y _ ↦ (hq k).differentiable (by norm_num) y)
      (fun y _ ↦ hDq.differentiable (by norm_num) y) (hHq k) (hval k) (hgrad k)).2
      K hK (hnorm k)
    simpa only [add_comm (x k) (z - x k), sub_add_cancel] using he
  · exact fun k hk z hz j hj ↦ hlocalBound k hk z hz j (hj.trans (Nat.le_succ t))
  · intro k hk z hz
    rw [hfixed k hk]
    exact hlocalBound k hk z hz (t + 1) le_rfl
  · intro k hk z _ j hj _
    rw [hfixed j hj, hfixed k hk]

end ConnGouldToint.Chapter09
