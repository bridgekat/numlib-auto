import Mathlib.Analysis.Complex.Exponential

/-!
# Bounds on partial sums of the exponential series

Elementary bounds on the sums `∑ δ^ℓ/ℓ!` that control Taylor sums ([cartis2022evaluation],
Lemma A.10.1 and (A.34)–(A.35)). They all follow from `∑_{i < n} δ^i/i! ≤ exp δ`
(`Real.sum_le_exp_of_nonneg`) and `exp δ - 1 ≤ 2 δ` for `δ ∈ [0, 1]` (`Real.abs_exp_sub_one_le`).

* `sum_pow_div_factorial_le_one_add_two_mul`: `∑_{ℓ=j}^p δ^{ℓ-j}/(ℓ-j)! ≤ 1 + 2δ`;
* `sum_pow_div_factorial_Icc_succ_le`: `∑_{ℓ=j+1}^{p+1} δ^ℓ/ℓ! ≤ 2 δ^{j+1}/j!`;
* `sum_pow_div_factorial_le_two_mul`: `∑_{ℓ=1}^j δ^ℓ/ℓ! ≤ 2δ` for `δ ∈ [0, 1]` (A.34);
* `sum_pow_div_factorial_le_two_mul_pow`: `∑_{ℓ=1}^j δ^ℓ/ℓ! ≤ 2δ^j` for `δ ≥ 1` (A.35);
* `sum_inv_factorial_sub_le_exp_one`: `∑_{ℓ=j}^p 1/(ℓ-j)! ≤ e` (towards (A.36));
* `half_mul_pow_div_factorial_le`: the closing step of the model-decrease lemmas
  (Lemmas 12.2.8, 13.1.10, 14.1.2).
-/

open Finset
open scoped Nat

/-- A sum over `Icc (j + 1) (n + j)` shifted to `Icc 1 n`. -/
private theorem sum_Icc_add_eq {f : ℕ → ℝ} (j n : ℕ) :
    ∑ ℓ ∈ Icc (j + 1) (n + j), f ℓ = ∑ i ∈ Icc 1 n, f (i + j) := by
  refine sum_nbij' (· - j) (· + j) ?_ ?_ ?_ ?_ ?_ <;> intro a ha <;>
    simp only [mem_Icc] at ha ⊢ <;> first | omega | (congr 1; omega)

/-- `∑_{ℓ=1}^{j} δ^ℓ/ℓ! = ∑_{ℓ<j+1} δ^ℓ/ℓ! - 1`. -/
private theorem sum_Icc_one_eq (δ : ℝ) (j : ℕ) :
    ∑ ℓ ∈ Icc 1 j, δ ^ ℓ / (ℓ ! : ℝ) = ∑ ℓ ∈ range (j + 1), δ ^ ℓ / (ℓ ! : ℝ) - 1 := by
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos j), ← Ico_add_one_right_eq_Icc]
  simp

/-- **(A.34)** For `δ ∈ [0, 1]`: `∑_{ℓ=1}^{j} δ^ℓ/ℓ! ≤ 2 δ`. -/
theorem sum_pow_div_factorial_le_two_mul {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (j : ℕ) :
    ∑ ℓ ∈ Icc 1 j, δ ^ ℓ / (ℓ ! : ℝ) ≤ 2 * δ := by
  rw [sum_Icc_one_eq]
  have h := Real.sum_le_exp_of_nonneg h0 (j + 1)
  have h' := Real.abs_exp_sub_one_le (x := δ) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at h'
  linarith [le_abs_self (Real.exp δ - 1)]

/-- **[cartis2022evaluation], Lemma A.10.1, first bound of (A.33).** For `δ ∈ [0, 1]`:
`∑_{ℓ=j}^{p} δ^{ℓ-j}/(ℓ-j)! ≤ 1 + 2δ` (the book assumes `j ≤ p`; otherwise the sum is empty). -/
theorem sum_pow_div_factorial_le_one_add_two_mul {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (j p : ℕ) :
    ∑ ℓ ∈ Icc j p, δ ^ (ℓ - j) / ((ℓ - j)! : ℝ) ≤ 1 + 2 * δ := by
  have e : ∑ ℓ ∈ Icc j p, δ ^ (ℓ - j) / ((ℓ - j)! : ℝ) =
      ∑ i ∈ range (p + 1 - j), δ ^ i / (i ! : ℝ) := by
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    simp
  rw [e]
  have h := sum_pow_div_factorial_le_two_mul h0 h1 (p - j)
  rw [sum_Icc_one_eq] at h
  have : p - j + 1 = p + 1 - j ∨ p < j := by omega
  rcases this with h' | h'
  · rw [h'] at h; linarith
  · rw [show p + 1 - j = 0 by omega]; simp; linarith

/-- **[cartis2022evaluation], Lemma A.10.1, second bound of (A.33).** For `δ ∈ [0, 1]`:
`∑_{ℓ=j+1}^{p+1} δ^ℓ/ℓ! ≤ 2 δ^{j+1}/j!` (the book assumes `j ≤ p`; otherwise the sum is empty). -/
theorem sum_pow_div_factorial_Icc_succ_le {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (j p : ℕ) :
    ∑ ℓ ∈ Icc (j + 1) (p + 1), δ ^ ℓ / (ℓ ! : ℝ) ≤ 2 * δ ^ (j + 1) / (j ! : ℝ) := by
  rcases lt_or_ge p j with hpj | hjp
  · rw [Icc_eq_empty (by omega), sum_empty]
    positivity
  set n := p + 1 - j
  rw [show p + 1 = n + j by omega, sum_Icc_add_eq]
  have hterm : ∀ i ∈ Icc 1 n, δ ^ (i + j) / ((i + j)! : ℝ) ≤
      δ ^ j / (j ! : ℝ) * (δ ^ i / (i ! : ℝ)) := by
    intro i _
    have hf : ((i ! * j ! : ℕ) : ℝ) ≤ ((i + j)! : ℕ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _)
        (Nat.factorial_mul_factorial_dvd_factorial_add i j)
    rw [Nat.cast_mul] at hf
    rw [pow_add, div_mul_div_comm, mul_comm (δ ^ j), mul_comm ((j ! : ℝ))]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hf
  calc ∑ i ∈ Icc 1 n, δ ^ (i + j) / ((i + j)! : ℝ)
      ≤ ∑ i ∈ Icc 1 n, δ ^ j / (j ! : ℝ) * (δ ^ i / (i ! : ℝ)) := sum_le_sum hterm
    _ = δ ^ j / (j ! : ℝ) * ∑ i ∈ Icc 1 n, δ ^ i / (i ! : ℝ) := by rw [mul_sum]
    _ ≤ δ ^ j / (j ! : ℝ) * (2 * δ) := by
        gcongr; exact sum_pow_div_factorial_le_two_mul h0 h1 n
    _ = 2 * δ ^ (j + 1) / (j ! : ℝ) := by ring

/-- **(A.35)** For `δ ≥ 1`: `∑_{ℓ=1}^{j} δ^ℓ/ℓ! ≤ 2 δ^j`. (The book states it for `j ≥ 1`; for
`j = 0` both sides are `0` and `2`.) -/
theorem sum_pow_div_factorial_le_two_mul_pow {δ : ℝ} (h1 : 1 ≤ δ) (j : ℕ) :
    ∑ ℓ ∈ Icc 1 j, δ ^ ℓ / (ℓ ! : ℝ) ≤ 2 * δ ^ j := by
  calc ∑ ℓ ∈ Icc 1 j, δ ^ ℓ / (ℓ ! : ℝ) ≤ ∑ ℓ ∈ Icc 1 j, δ ^ j * ((1 : ℝ) ^ ℓ / (ℓ ! : ℝ)) := by
        refine sum_le_sum fun ℓ hℓ => ?_
        rw [one_pow, mul_one_div]
        gcongr
        exact (mem_Icc.1 hℓ).2
    _ = δ ^ j * ∑ ℓ ∈ Icc 1 j, (1 : ℝ) ^ ℓ / (ℓ ! : ℝ) := by rw [mul_sum]
    _ ≤ δ ^ j * 2 := by
        gcongr
        simpa using sum_pow_div_factorial_le_two_mul zero_le_one le_rfl j
    _ = 2 * δ ^ j := mul_comm _ _

/-- `∑_{ℓ=j}^p 1/(ℓ-j)! ≤ e`: a partial sum of the exponential series at `1`. -/
theorem sum_inv_factorial_sub_le_exp_one (j p : ℕ) :
    ∑ ℓ ∈ Icc j p, 1 / ((ℓ - j)! : ℝ) ≤ Real.exp 1 := by
  have e : ∑ ℓ ∈ Icc j p, 1 / ((ℓ - j)! : ℝ) = ∑ i ∈ range (p + 1 - j), 1 ^ i / (i ! : ℝ) := by
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    simp
  rw [e]
  exact Real.sum_le_exp_of_nonneg zero_le_one _

/-- **Half of a decrement survives a perturbation of order `δ^{j+1}`** (the closing step of
[cartis2022evaluation], Lemmas 12.2.8, 13.1.10 and 14.1.2): if `δ ≥ 0`, `4 K δ ≤ α`,
`a ≥ α δ^j/j!` and `b ≥ a - 2 K δ^{j+1}/j!`, then `b ≥ (α/2) δ^j/j!`. -/
theorem half_mul_pow_div_factorial_le {K α δ a b : ℝ} {j : ℕ} (hδ : 0 ≤ δ)
    (hKα : 4 * K * δ ≤ α) (ha : α * δ ^ j / j ! ≤ a)
    (hb : a - 2 * K * δ ^ (j + 1) / j ! ≤ b) : α / 2 * δ ^ j / j ! ≤ b := by
  have hf : (0 : ℝ) < (j ! : ℝ) := by positivity
  have hpow : 0 ≤ δ ^ j := by positivity
  have key : 2 * K * δ ^ (j + 1) / (j ! : ℝ) ≤ α / 2 * δ ^ j / j ! := by
    rw [div_le_div_iff_of_pos_right hf, pow_succ]
    nlinarith
  have e : α / 2 * δ ^ j / (j ! : ℝ) = α * δ ^ j / (j ! : ℝ) - α / 2 * δ ^ j / (j ! : ℝ) := by
    ring
  linarith
