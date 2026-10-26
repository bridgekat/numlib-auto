import Numlib.Optimization.Complexity.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Counting for scaled-restart outer loops

Some methods of [cartis2022evaluation] (LENq-SC, Algorithm 14.3.1) run an outer loop in which
each iteration calls an inner solver with a tolerance proportional to the current residual
`r_{k-1}`, and the residual contracts geometrically, `r_k < β r_{k-1}`, as long as the outer
termination test fails. This file contains the two real-variable counting facts behind
Theorems 14.3.3 and 14.3.4.

* `Optimization.le_ceil_log_of_contract`: the outer loop terminates after at most
  `⌈log (ε₀ / r₀) / log β⌉₊` iterations.
* `Optimization.sum_rpow_le_of_geometric_lower`: if `r_{k-1} ≥ β^{k-K} ε₀` for `k ∈ [1, K]`, then
  `∑_{k=1}^K r_{k-1}^{1-π} ≤ ε₀^{1-π} β^{1-π} / (β^{1-π} - 1)` for `π > 1` (the series bounding
  the total cost of the inner calls).
-/

open Finset

namespace Optimization

variable {r : ℕ → ℝ} {test : ℕ → Prop} {β ε₀ : ℝ}

/-- Geometric decrease of a contracting residual: if `r_j < β r_{j-1}` at every `j ∈ [1, k]` and
`0 < β`, then `r_k ≤ β^k r_0`, with strict inequality for `k ≥ 1`. -/
theorem lt_pow_mul_of_contract (hβ : 0 < β) {k : ℕ}
    (hcontr : ∀ j, 1 ≤ j → j ≤ k → r j < β * r (j - 1)) :
    r k ≤ β ^ k * r 0 ∧ (1 ≤ k → r k < β ^ k * r 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih fun j hj hjk => hcontr j hj (hjk.trans k.le_succ)
    have h := hcontr (k + 1) le_add_self le_rfl
    simp only [Nat.add_sub_cancel] at h
    have : r (k + 1) < β ^ (k + 1) * r 0 := by
      calc r (k + 1) < β * r k := h
        _ ≤ β * (β ^ k * r 0) := mul_le_mul_of_nonneg_left ih'.1 hβ.le
        _ = β ^ (k + 1) * r 0 := by ring
    exact ⟨this.le, fun _ => this⟩

/-- **Termination of a scaled-restart outer loop** ([cartis2022evaluation], Theorem 14.3.3,
with the integer ceiling). Let `0 < β < 1` and `0 < ε₀`. Suppose that the outer test `test k`
holds whenever `r_k ≤ ε₀`, and that at every iteration `k ≥ 1` reached without termination
(`test j` fails for `j ≤ k`) the residual contracts: `r_k < β r_{k-1}`. Then the loop terminates
at an index `k ≤ ⌈log (ε₀ / r_0) / log β⌉₊`. (For LENq-SC, `test k` is (14.3.23); the plain
residual test is `test k ↔ r k ≤ ε₀`. The book's bound `log (ε₀ / r_0) / log β` must be rounded
up: if it equals `2.5`, termination may happen at iteration `3`.) -/
theorem le_ceil_log_of_contract (hβ : 0 < β) (hβ1 : β < 1) (hε₀ : 0 < ε₀)
    (htest : ∀ k, ¬ test k → ε₀ < r k)
    (hcontr : ∀ k, 1 ≤ k → (∀ j ≤ k, ¬ test j) → r k < β * r (k - 1)) :
    ∃ k, IsFirstHit test k ∧ k ≤ ⌈Real.log (ε₀ / r 0) / Real.log β⌉₊ := by
  set N := ⌈Real.log (ε₀ / r 0) / Real.log β⌉₊
  suffices h : ∃ j ≤ N, test j by
    obtain ⟨j, hjN, hj⟩ := h
    obtain ⟨k, hkj, hk⟩ := exists_isFirstHit_le hj
    exact ⟨k, hk, hkj.trans hjN⟩
  by_contra hcon
  push Not at hcon
  have hr0 : ε₀ < r 0 := htest 0 (hcon 0 (Nat.zero_le _))
  have hr0pos : 0 < r 0 := hε₀.trans hr0
  have hdec := (lt_pow_mul_of_contract hβ (k := N) fun j hj hjN =>
    hcontr j hj fun i hi => hcon i (hi.trans hjN)).1
  have hlogβ : Real.log β < 0 := Real.log_neg hβ hβ1
  have hpow : β ^ N ≤ ε₀ / r 0 := by
    have hN : Real.log (ε₀ / r 0) / Real.log β ≤ N := Nat.le_ceil _
    rw [div_le_iff_of_neg hlogβ] at hN
    rw [← Real.log_le_log_iff (pow_pos hβ N) (div_pos hε₀ hr0pos), Real.log_pow]
    linarith
  have hrN := htest N (hcon N le_rfl)
  have : β ^ N * r 0 ≤ ε₀ := by rwa [le_div_iff₀ hr0pos] at hpow
  linarith

/-- **Geometric cost sum** (the series in the proof of [cartis2022evaluation], Theorem 14.3.4, for
one exponent `π`). Let `0 < β < 1`, `0 < ε₀`, `1 < π`, and `r_{k-1} ≥ β^{k-K} ε₀` for
`k ∈ [1, K]`. Then
`∑_{k=1}^K r_{k-1}^{1-π} ≤ ε₀^{1-π} β^{1-π} / (β^{1-π} - 1)` (the denominator is positive). -/
theorem sum_rpow_le_of_geometric_lower (hβ : 0 < β) (hβ1 : β < 1) (hε₀ : 0 < ε₀) {π : ℝ}
    (hπ : 1 < π) {K : ℕ} (hr : ∀ k ∈ Icc 1 K, β ^ ((k : ℤ) - K) * ε₀ ≤ r (k - 1)) :
    ∑ k ∈ Icc 1 K, r (k - 1) ^ (1 - π) ≤
      ε₀ ^ (1 - π) * β ^ (1 - π) / (β ^ (1 - π) - 1) := by
  set q := β ^ (π - 1) with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg hβ.le _
  have hq1 : q < 1 := Real.rpow_lt_one hβ.le hβ1 (by linarith)
  -- termwise bound
  have hterm : ∀ k ∈ Icc 1 K, r (k - 1) ^ (1 - π) ≤ ε₀ ^ (1 - π) * q ^ (K - k) := by
    intro k hk
    have hkK : k ≤ K := (mem_Icc.1 hk).2
    have hzpow : β ^ ((k : ℤ) - K) = (β ^ (K - k))⁻¹ := by
      rw [← zpow_natCast, ← zpow_neg, Nat.cast_sub hkK]
      congr 1
      ring
    have hlow := hr k hk
    rw [hzpow] at hlow
    have hpos : 0 < (β ^ (K - k))⁻¹ * ε₀ := mul_pos (inv_pos.2 (pow_pos hβ _)) hε₀
    calc r (k - 1) ^ (1 - π) ≤ ((β ^ (K - k))⁻¹ * ε₀) ^ (1 - π) :=
          Real.rpow_le_rpow_of_nonpos hpos hlow (by linarith)
      _ = ε₀ ^ (1 - π) * q ^ (K - k) := by
          rw [Real.mul_rpow (inv_nonneg.2 (pow_nonneg hβ.le _)) hε₀.le,
            Real.inv_rpow (pow_nonneg hβ.le _), ← Real.rpow_neg (pow_nonneg hβ.le _),
            hq, Real.rpow_pow_comm hβ.le, neg_sub, mul_comm]
  have hsum : ∑ k ∈ Icc 1 K, q ^ (K - k) = ∑ m ∈ range K, q ^ m := by
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    rw [← sum_range_reflect]
    refine sum_congr rfl fun m hm => ?_
    have := mem_range.1 hm
    congr 1
    omega
  have hgeom : ∑ m ∈ range K, q ^ m ≤ 1 / (1 - q) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := K) hq0 hq1
    rwa [← range_eq_Ico, pow_zero] at this
  have hc : β ^ (1 - π) = q⁻¹ := by
    rw [hq, ← Real.rpow_neg hβ.le, neg_sub]
  have hqpos : 0 < q := Real.rpow_pos_of_pos hβ _
  calc ∑ k ∈ Icc 1 K, r (k - 1) ^ (1 - π) ≤ ∑ k ∈ Icc 1 K, ε₀ ^ (1 - π) * q ^ (K - k) :=
        sum_le_sum hterm
    _ = ε₀ ^ (1 - π) * ∑ m ∈ range K, q ^ m := by rw [← mul_sum, hsum]
    _ ≤ ε₀ ^ (1 - π) * (1 / (1 - q)) :=
        mul_le_mul_of_nonneg_left hgeom (Real.rpow_nonneg hε₀.le _)
    _ = ε₀ ^ (1 - π) * β ^ (1 - π) / (β ^ (1 - π) - 1) := by
        rw [hc]
        have : 1 - q ≠ 0 := by linarith
        field_simp

end Optimization
