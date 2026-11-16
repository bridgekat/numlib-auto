/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Algebra.Order.Archimedean.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dyadic brackets

Every real number $r \in (0, \tfrac12]$ lies between two consecutive dyadic numbers
$2^{-m} \le r < 2 \cdot 2^{-m}$ with $m \ge 1$. The number $2^{-m}$ is the first term of the
sequence $1, \tfrac12, \tfrac14, \dots$ of repeated halvings that is at most $r$.

## Main results

* `exists_one_div_two_pow_le_lt`: for $0 < r \le \tfrac12$ there is $m \ge 1$ with
  $2^{-m} \le r < 2 \cdot 2^{-m}$.
-/

/-- Let $r$ be a real number with $0 < r$ and $2r \le 1$. Then there is a natural number $m \ge 1$
such that
$$\frac{1}{2^m} \le r < 2 \cdot \frac{1}{2^m}.$$
-/
theorem exists_one_div_two_pow_le_lt {r : ℝ} (hr : 0 < r) (hr1 : 2 * r ≤ 1) :
    ∃ m : ℕ, 1 ≤ m ∧ 1 / 2 ^ m ≤ r ∧ r < 2 * (1 / 2 ^ m) := by
  classical
  have hex : ∃ m : ℕ, 1 / (2 : ℝ) ^ m ≤ r := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, by rw [one_div_pow] at hn; exact hn.le⟩
  set m := Nat.find hex with hmdef
  have hm : 1 / (2 : ℝ) ^ m ≤ r := Nat.find_spec hex
  have hm1 : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    rw [this, pow_zero, div_one] at hm
    linarith
  refine ⟨m, hm1, hm, ?_⟩
  have hlt : ¬ 1 / (2 : ℝ) ^ (m - 1) ≤ r := Nat.find_min hex (show m - 1 < m by omega)
  rw [not_le] at hlt
  have e : (1 : ℝ) / 2 ^ (m - 1) = 2 * (1 / 2 ^ m) := by
    obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, pow_succ]; field_simp
  rwa [e] at hlt
