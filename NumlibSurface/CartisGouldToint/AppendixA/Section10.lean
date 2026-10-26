import Numlib.Analysis.SpecialFunctions.FactorialSum
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Cartis–Gould–Toint §A.10: Simple series bounds

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §A.10: bounds on partial sums of
the exponential series `∑ δ^ℓ/ℓ!`, specialized from `Numlib.Analysis.SpecialFunctions.FactorialSum`.
Sums `∑_{ℓ=a}^b` are over `Finset.Icc a b`.

## Main results

* `lemma_A_10_1` — the two bounds (A.33) for `δ ∈ [0, 1]`.
* `eq_A_34`, `eq_A_35`, `eq_A_36` — the consequences (A.34) (`δ ∈ [0, 1]`), (A.35) (`δ ≥ 1`)
  and (A.36) (`δ = 1`).
-/

open Finset
open scoped Nat

namespace CartisGouldToint.AppendixA

/-- **Lemma A.10.1 (Sum bounds)** of [cartis2022evaluation]. Let `δ ∈ [0, 1]`. Then for any
`j ≥ 0` and `p ≥ j`, (A.33):
`∑_{ℓ=j}^p δ^{ℓ-j}/(ℓ-j)! ≤ 1 + 2δ` and `∑_{ℓ=j+1}^{p+1} δ^ℓ/ℓ! ≤ 2δ^{j+1}/j!`. -/
theorem lemma_A_10_1 {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {j p : ℕ} (_hjp : j ≤ p) :
    ∑ ℓ ∈ Icc j p, δ ^ (ℓ - j) / ((ℓ - j)! : ℝ) ≤ 1 + 2 * δ ∧
      ∑ ℓ ∈ Icc (j + 1) (p + 1), δ ^ ℓ / (ℓ ! : ℝ) ≤ 2 * δ ^ (j + 1) / (j ! : ℝ) :=
  ⟨sum_pow_div_factorial_le_one_add_two_mul h0 h1 j p,
    sum_pow_div_factorial_Icc_succ_le h0 h1 j p⟩

/-- **(A.34)** of [cartis2022evaluation]: for `δ ∈ [0, 1]`,
`∑_{ℓ=1}^j δ^ℓ/ℓ! ≤ 2δ ≤ 2 < 3`. -/
theorem eq_A_34 {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (j : ℕ) :
    ∑ ℓ ∈ Icc 1 j, δ ^ ℓ / (ℓ ! : ℝ) ≤ 2 * δ ∧ 2 * δ ≤ 2 ∧ (2 : ℝ) < 3 :=
  ⟨sum_pow_div_factorial_le_two_mul h0 h1 j, by linarith, by norm_num⟩

/-- **(A.35)** of [cartis2022evaluation]: for `δ ≥ 1`, `∑_{ℓ=1}^j δ^ℓ/ℓ! ≤ 2δ^j`. -/
theorem eq_A_35 {δ : ℝ} (h1 : 1 ≤ δ) (j : ℕ) :
    ∑ ℓ ∈ Icc 1 j, δ ^ ℓ / (ℓ ! : ℝ) ≤ 2 * δ ^ j :=
  sum_pow_div_factorial_le_two_mul_pow h1 j

@[deprecated _root_.sum_inv_factorial_sub_le_exp_one (since := "2026-10-26")]
alias sum_inv_factorial_sub_le_exp_one := _root_.sum_inv_factorial_sub_le_exp_one

/-- **(A.36)** of [cartis2022evaluation] (the case `δ = 1`): for `j ≤ p`,
`∑_{ℓ=1}^j 1/ℓ! ≤ 2`, `∑_{ℓ=j}^p 1/(ℓ-j)! < 3` and `∑_{ℓ=j+1}^{p+1} 1/ℓ! ≤ 2/j!`. -/
theorem eq_A_36 {j p : ℕ} (_hjp : j ≤ p) :
    ∑ ℓ ∈ Icc 1 j, 1 / (ℓ ! : ℝ) ≤ 2 ∧ ∑ ℓ ∈ Icc j p, 1 / ((ℓ - j)! : ℝ) < 3 ∧
      ∑ ℓ ∈ Icc (j + 1) (p + 1), 1 / (ℓ ! : ℝ) ≤ 2 / (j ! : ℝ) := by
  refine ⟨?_, (_root_.sum_inv_factorial_sub_le_exp_one j p).trans_lt ?_, ?_⟩
  · simpa using sum_pow_div_factorial_le_two_mul zero_le_one le_rfl j
  · exact Real.exp_one_lt_d9.trans (by norm_num)
  · simpa using sum_pow_div_factorial_Icc_succ_le zero_le_one le_rfl j p

end CartisGouldToint.AppendixA
