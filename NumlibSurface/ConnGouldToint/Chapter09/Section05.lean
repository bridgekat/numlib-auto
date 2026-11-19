/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter09.Section02
import NumlibSurface.ConnGouldToint.Chapter06.Section04
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

/-!
# Conn, Gould and Toint, Section 9.5: Conditional models with memory

This module formalizes the models with memory of Section 9.5 of [conn2000trust]. Given local models
$q_k$ and weights $\alpha_k$, the **memory model** is $m_0 = q_0$ and $m_{k+1} = (1 - \alpha_{k+1})
q_{k+1} + \alpha_{k+1} m_k$ (9.5.1), a convex combination of the local models. After the last
accepted step the local model stays fixed, and the memory error decays like the product of the
weights since that step (Theorem 9.5.1). If the weights are bounded by a power of the radius and the
radius cannot drop by more than a fixed factor per iteration, a fixed number of recent weights makes
the memory error quadratic in the radius (Theorem 9.5.2). The run of Algorithm 9.1.1 is
`ConnGouldToint.Chapter09.ConditionalRadiusRun` from
`NumlibSurface.ConnGouldToint.Chapter09.Section02`, and the local error bound comes from Theorem
6.4.1 in `NumlibSurface.ConnGouldToint.Chapter06.Section04`.

## Main definitions

* Equation (9.5.1), `ConnGouldToint.Chapter09.memoryModel`: the memory model built from local models
  and weights.

## Main results

* Equation (9.5.2), `ConnGouldToint.Chapter09.memoryModel_eq_sum`: the memory model as a weighted
  sum of the local models.
* Equation (9.5.3), `ConnGouldToint.Chapter09.memoryModel_sub_local_eq_prod`: after the last
  accepted step, the memory error is the earlier error times the product of the intervening weights.
* Theorem 9.5.1, `ConnGouldToint.Chapter09.theorem_9_5_1`: the memory error after a block with a
  fixed center decays geometrically.
* Equation (9.5.16), `ConnGouldToint.Chapter09.ConditionalRadiusRun.radius_next_ge_factor`: the
  corrected radius update satisfies $\gamma_1 \Delta_k \le \Delta_{k+1}$.
* Equation (9.5.16), `ConnGouldToint.Chapter09.memoryWeight_le_radius_rpow`: the step-size
  restriction AM.10 bounds a weight by a power of the next radius.
* Theorem 9.5.2, `ConnGouldToint.Chapter09.memoryProduct_le_radius_sq`: a fixed number of recent
  weights has product of order $\Delta_k^2$.
* Theorem 9.5.2, `ConnGouldToint.Chapter09.theorem_9_5_2`: after enough rejected steps, the memory
  model has error of order $\Delta_k^2$.
* Theorem 9.5.2, `ConnGouldToint.Chapter09.theorem_9_5_2_of_conditional_run`: the same conclusion
  for a run of Algorithm 9.1.1 under AM.10, AM.11 and AN.1.

## Conventions

* Products such as $\prod_{j=t+1}^{k} \alpha_j$ run over the integers $j$ with $t < j \le k$, and
  are $1$ when $t = k$.

## Deviations from the source

* **Theorem 9.5.1 and (9.5.8)** (correction). The exact weight on the past is
  $\prod_{j=t+1}^k\alpha_j$. The geometric-series expression in (9.5.8) is an upper bound.
  The proof uses the exact weight and a common pointwise model bound to obtain the factor
  $2B$ in (9.5.3).
* **Theorem 9.5.2** (correction). The memory estimate uses the bound on the past local models at the
  last accepted center. The product of recent weights is controlled by the lower radius factor
  $\gamma \Delta_k \le \Delta_{k+1}$ of adjacent iterations, so that the radii can vary during a
  block of rejected iterations. See `ConnGouldToint.Chapter09.theorem_9_5_2`.
-/

namespace ConnGouldToint.Chapter09

variable {E : Type*}

/-- **Equation (9.5.1)** of [conn2000trust]. Given local models $q_k : E \to \mathbb{R}$ and weights
$\alpha_k \in \mathbb{R}$, the **memory model** is defined by $m_0 = q_0$ and
$$m_{k+1}(z) = (1 - \alpha_{k+1}) q_{k+1}(z) + \alpha_{k+1} m_k(z).$$

The initial memory model is the initial local model. -/
noncomputable def memoryModel (q : ℕ → E → ℝ) (α : ℕ → ℝ) : ℕ → E → ℝ
  | 0 => q 0
  | k + 1 => fun z ↦ (1 - α (k + 1)) * q (k + 1) z + α (k + 1) * memoryModel q α k z

/-- **Equation (9.5.2)** of [conn2000trust]. If $\alpha_0 = 0$, then for every $k$ and $z$
$$m_k(z) = \sum_{i=0}^{k} (1 - \alpha_i) \Big(\prod_{j=i+1}^{k} \alpha_j\Big) q_i(z).$$
-/
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

/-- **Equation (9.5.3)** of [conn2000trust], the memory error identity. Let $t \le k$, $z \in E$ and
$v \in \mathbb{R}$ with $q_j(z) = v$ for all $j$ with $t < j \le k$. Then
$$m_k(z) - v = \Big(\prod_{j=t+1}^{k} \alpha_j\Big) (m_t(z) - v).$$

After the last accepted step $t$ the local model stays fixed, and the remaining memory error is
the error at $t$ multiplied by exactly the intervening weights.

**Reading.** Exact recent-weight product replaces the printed geometric-series equality.
-/
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

/-- **Theorem 9.5.1** of [conn2000trust]. Let $t < k$, $z \in E$, $B \in \mathbb{R}$ and $a \ge 0$.
Let $0 \le \alpha_j \le 1$ for all $j$, and $\alpha_j \le a$ for $t < j \le k$. Suppose that
$|q_j(z)| \le B$ for all $j \le t$, that $|q_k(z)| \le B$, and that $q_j(z) = q_k(z)$ for
$t < j \le k$. Then
$$|m_k(z) - q_k(z)| \le 2 B a^{k - t}.$$

The constant $B$ bounds the earlier local models and the new fixed local model at the point $z$.

**Reading.** Pointwise model bounds, exact memory weight and explicit coefficient 2.
-/
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

/-- **Equation (9.5.16)** of [conn2000trust], adjacent radius factor. Let a conditional radius run
with the corrected update be given, with $0 < \gamma_1 \le 1$, and suppose that
$\rho_k \ge \eta_1$ implies $\hat{\rho}_k \ge \eta_0$ for every $k$. Then
$\gamma_1 \Delta_k \le \Delta_{k+1}$ for every $k$.

**Correction.** Adjacent radius lower factor derived for the corrected update.
-/
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

/-- **Equation (9.5.16)** of [conn2000trust]. Let $\Delta' \ge 0$, $s \ge 0$, $\kappa \ge 0$,
$K \ge 0$, $\gamma > 0$ and $\psi \ge 0$. Suppose that $s \le K \Delta$,
$\gamma \Delta \le \Delta'$, $\alpha \le \kappa s^\psi$ and $\kappa (K / \gamma)^\psi \le 1$.
Then $\alpha \le (\Delta')^\psi$.

The hypothesis $\alpha \le \kappa s^\psi$ is the step-size restriction of AM.10, and
$\gamma \Delta \le \Delta'$ is the lower update factor of adjacent radii. The powers are real
powers `Real.rpow`.

**Reading.** Transfers the step-weight bound through an explicit adjacent-radius comparison.
-/
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

/-- **Theorem 9.5.2** of [conn2000trust], bound on the memory factor. Let $0 < \gamma \le 1$ and
$\psi > 0$. Let $\Delta_k > 0$ with $\gamma \Delta_k \le \Delta_{k+1}$, and let
$0 \le \alpha_k \le 1$ with $\alpha_k \le \Delta_k^\psi$, for all $k$. Then there are
$p \in \mathbb{N}$ and $C > 0$ such that for all $t, k$ with $t + p \le k$,
$$\prod_{j=t+1}^{k} \alpha_j \le C \Delta_k^2.$$

**Correction.** The bound uses only the lower factor of adjacent radii, so the radius may vary
during the block of rejected iterations. -/
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

/-- **Theorem 9.5.2** of [conn2000trust]. Let $f : E \to \mathbb{R}$, local models $q_k$, weights
$\alpha_k$ and radii $\Delta_k$ be given, with $0 < \gamma \le 1$, $\psi > 0$, $A \ge 0$ and
$B \ge 0$. Suppose that for all $k$, $\Delta_k > 0$, $\gamma \Delta_k \le \Delta_{k+1}$,
$0 \le \alpha_k \le 1$ and $\alpha_k \le \Delta_k^\psi$. Let $t \in \mathbb{N}$ and let
$R_k \subseteq E$ be regions with $|f(z) - q_k(z)| \le A \Delta_k^2$ for all $k$ and
$z \in R_k$. Suppose that for every $k > t$ and $z \in R_k$, $|q_j(z)| \le B$ for $j \le t$,
$|q_k(z)| \le B$, and $q_j(z) = q_k(z)$ for $t < j \le k$. Then there are $p \in \mathbb{N}$ and
$C > 0$ such that for all $k > t$ with $k \ge t + p$ and all $z \in R_k$,
$$|f(z) - m_k(z)| \le C \Delta_k^2.$$

**Correction.** The radius hypothesis is the lower factor $\gamma \Delta_k \le \Delta_{k+1}$ of
adjacent radii, which allows the radii to vary during the block of rejected iterations.

The current local model has quadratic accuracy, and after enough rejected iterations the memory
term has the same order. -/
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
/-- **Theorem 9.5.2** of [conn2000trust], for a run of Algorithm 9.1.1. Let $F$ be a real normed
space and let $f : F \to \mathbb{R}$ be twice continuously differentiable with
$\|\nabla^2 f(z)\| \le \kappa_f$ for all $z$. For each center $c$ let $q(c) : F \to \mathbb{R}$
be a local model. Let centers $x_k$, steps $s_k$, trust-region seminorms $p_k$ and weights
$\alpha_k$ be given, together with a conditional radius run with the corrected update. Let
$0 < \gamma_1 \le 1$, $K \ge 0$, $\kappa \ge 0$, $\psi > 0$, $B \ge 0$ and $\kappa_m \ge 1$.
Suppose that for every $k$:

* $\rho_k \ge \eta_1$ implies $\hat{\rho}_k \ge \eta_0$;
* $p_k(v) = 0$ only for $v = 0$, and $\|v\| \le K p_k(v)$ for all $v$ (AN.1);
* $p_k(s_k) \le \Delta_k$;
* $0 \le \alpha_k \le 1$, $\alpha_0 = 0$, and $\alpha_{k+1} \le \kappa \|s_k\|^\psi$ (AM.10),
  with $\kappa (K / \gamma_1)^\psi \le 1$;
* $q(x_k)$ is twice continuously differentiable, $q(x_k)(x_k) = f(x_k)$,
  $\nabla q(x_k)(x_k) = \nabla f(x_k)$, and $\|\nabla^2 q(x_k)(z)\| \le \kappa_m - 1$ on the
  ball $\{z : p_k(z - x_k) \le \Delta_k\}$.

Let $t \in \mathbb{N}$ with $x_k = x_{t+1}$ for all $k > t$, and suppose that
$|q(x_j)(z)| \le B$ for all $k > t$, all $z$ in the ball of iteration $k$ and all $j \le t + 1$.
Then there are $n \in \mathbb{N}$ and $C > 0$ such that for all $k > t$ with $k \ge t + n$ and
all $z$ in the ball of iteration $k$,
$$|f(z) - m_k(z)| \le C \Delta_k^2,$$
where $m_k$ is the memory model (9.5.1) of the local models $q(x_j)$.

**Correction.** As in `ConnGouldToint.Chapter09.theorem_9_5_2`, the memory estimate uses the
bound on the past local models at the last accepted center and the lower factor of adjacent
radii.

The local model depends only on its center. The norm comparison turns the trust-region bound on
the steps into the step-size condition of AM.10. The local error bound is Theorem 6.4.1
(`ConnGouldToint.Chapter06.theorem_6_4_1`). -/
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
