/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.Exponential

/-!
# Bounds on partial sums of the exponential series

This file proves elementary bounds on sums of the form $\sum_\ell \delta^\ell / \ell!$, which
control Taylor sums in the complexity analysis of high-order methods. They follow
[cartis2022evaluation], Lemma A.10.1 and (A.34)–(A.35). All of them follow from
$\sum_{i < n} \delta^i / i! \le e^\delta$ (`Real.sum_le_exp_of_nonneg`) and from
$e^\delta - 1 \le 2\delta$ for $\delta \in [0, 1]$ (`Real.abs_exp_sub_one_le`). A sum
$\sum_{\ell = j}^p$ with $j > p$ is empty and equal to $0$.

## Main results

* `sum_pow_div_factorial_le_two_mul`: $\sum_{\ell=1}^j \delta^\ell/\ell! \le 2\delta$ for
  $\delta \in [0, 1]$; this is (A.34) of [cartis2022evaluation].
* `sum_pow_div_factorial_le_one_add_two_mul`: $\sum_{\ell=j}^p \delta^{\ell-j}/(\ell-j)! \le 1 +
  2\delta$ for $\delta \in [0, 1]$.
* `sum_pow_div_factorial_Icc_succ_le`: $\sum_{\ell=j+1}^{p+1} \delta^\ell/\ell! \le
  2\delta^{j+1}/j!$ for $\delta \in [0, 1]$.
* `sum_pow_div_factorial_le_two_mul_pow`: $\sum_{\ell=1}^j \delta^\ell/\ell! \le 2\delta^j$ for
  $\delta \ge 1$; this is (A.35) of [cartis2022evaluation].
* `sum_inv_factorial_sub_le_exp_one`: $\sum_{\ell=j}^p 1/(\ell-j)! \le e$.
* `half_mul_pow_div_factorial_le`: half of a decrement $\alpha \delta^j/j!$ survives a perturbation
  of order $\delta^{j+1}$.
* `pow_div_factorial_le_of_lt`: $\varepsilon^q/q! \le \varepsilon^j/(c\,j!)$ for $j < q$,
  $\varepsilon \in [0, 1]$ and $c \varepsilon \le 1$.
-/

open Finset
open scoped Nat

/-- For $f : \mathbb{N} \to \mathbb{R}$ and natural numbers $j, n$, the sum of $f(\ell)$ over
$j + 1 \le \ell \le n + j$ equals the sum of $f(i + j)$ over $1 \le i \le n$. -/
private theorem sum_Icc_add_eq {f : ℕ → ℝ} (j n : ℕ) :
    ∑ ℓ ∈ Icc (j + 1) (n + j), f ℓ = ∑ i ∈ Icc 1 n, f (i + j) := by
  refine sum_nbij' (· - j) (· + j) ?_ ?_ ?_ ?_ ?_ <;> intro a ha <;>
    simp only [mem_Icc] at ha ⊢ <;> first | omega | (congr 1; omega)

/-- For $\delta \in \mathbb{R}$ and a natural number $j$, $\sum_{\ell=1}^j \delta^\ell/\ell! =
\sum_{\ell=0}^j \delta^\ell/\ell! - 1$. -/
private theorem sum_Icc_one_eq (δ : ℝ) (j : ℕ) :
    ∑ ℓ ∈ Icc 1 j, δ ^ ℓ / (ℓ ! : ℝ) = ∑ ℓ ∈ range (j + 1), δ ^ ℓ / (ℓ ! : ℝ) - 1 := by
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos j), ← Ico_add_one_right_eq_Icc]
  simp

/-- Let $0 \le \delta \le 1$, and let $j$ be a natural number. Then
$$\sum_{\ell=1}^j \frac{\delta^\ell}{\ell!} \le 2\delta.$$
This is (A.34) of [cartis2022evaluation]. -/
theorem sum_pow_div_factorial_le_two_mul {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (j : ℕ) :
    ∑ ℓ ∈ Icc 1 j, δ ^ ℓ / (ℓ ! : ℝ) ≤ 2 * δ := by
  rw [sum_Icc_one_eq]
  have h := Real.sum_le_exp_of_nonneg h0 (j + 1)
  have h' := Real.abs_exp_sub_one_le (x := δ) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at h'
  linarith [le_abs_self (Real.exp δ - 1)]

/-- Let $0 \le \delta \le 1$, and let $j, p$ be natural numbers. Then
$$\sum_{\ell=j}^p \frac{\delta^{\ell-j}}{(\ell-j)!} \le 1 + 2\delta.$$
For $j > p$ the sum is empty. This is the first bound of (A.33) in Lemma A.10.1 of
[cartis2022evaluation]. -/
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

/-- Let $0 \le \delta \le 1$, and let $j, p$ be natural numbers. Then
$$\sum_{\ell=j+1}^{p+1} \frac{\delta^\ell}{\ell!} \le \frac{2\delta^{j+1}}{j!}.$$
For $j > p$ the sum is empty. This is the second bound of (A.33) in Lemma A.10.1 of
[cartis2022evaluation]. -/
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

/-- Let $\delta \ge 1$, and let $j$ be a natural number. Then
$$\sum_{\ell=1}^j \frac{\delta^\ell}{\ell!} \le 2\delta^j.$$
For $j = 0$ the two sides are $0$ and $2$. This is (A.35) of [cartis2022evaluation]. -/
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

/-- For natural numbers $j$ and $p$, $\sum_{\ell=j}^p 1/(\ell-j)! \le e$. This is a partial sum of
the exponential series at $1$, and it is a step towards (A.36) of [cartis2022evaluation]. -/
theorem sum_inv_factorial_sub_le_exp_one (j p : ℕ) :
    ∑ ℓ ∈ Icc j p, 1 / ((ℓ - j)! : ℝ) ≤ Real.exp 1 := by
  have e : ∑ ℓ ∈ Icc j p, 1 / ((ℓ - j)! : ℝ) = ∑ i ∈ range (p + 1 - j), 1 ^ i / (i ! : ℝ) := by
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    simp
  rw [e]
  exact Real.sum_le_exp_of_nonneg zero_le_one _

/-- **Half of a decrement survives a perturbation of order $\delta^{j+1}$.** Let
$K, \alpha, \delta, a, b$ be real numbers and $j$ a natural number, with $\delta \ge 0$ and
$4K\delta \le \alpha$. If $a \ge \alpha \delta^j/j!$ and $b \ge a - 2K\delta^{j+1}/j!$, then
$$b \ge \frac{\alpha}{2} \cdot \frac{\delta^j}{j!}.$$
This is the closing step of Lemmas 12.2.8, 13.1.10 and 14.1.2 of [cartis2022evaluation]. -/
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

/-- Let $0 \le \varepsilon \le 1$ and $c > 0$ with $c\varepsilon \le 1$, and let $j < q$ be natural
numbers. Then
$$\frac{\varepsilon^q}{q!} \le \frac{\varepsilon^j}{c\,j!}.$$
Thus the higher-order thresholds of the Step 1 test in the high-order methods of
[cartis2022evaluation] are dominated by the lower-order ones. -/
theorem pow_div_factorial_le_of_lt {ε c : ℝ} {j q : ℕ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : 0 < c)
    (hcε : c * ε ≤ 1) (hjq : j < q) : ε ^ q / q ! ≤ ε ^ j / j ! / c := by
  have h1 : ε ^ q ≤ ε ^ j / c := by
    have e : ε ^ q = ε ^ j * ε ^ (q - j) := by rw [← pow_add]; congr 1; omega
    have h2 : ε ^ (q - j) ≤ ε := pow_le_of_le_one hε hε1 (by omega)
    rw [e, le_div_iff₀ hc]
    have hj := pow_nonneg hε j
    calc ε ^ j * ε ^ (q - j) * c ≤ ε ^ j * ε * c := by gcongr
      _ = ε ^ j * (c * ε) := by ring
      _ ≤ ε ^ j * 1 := by gcongr
      _ = ε ^ j := mul_one _
  have hjf : (j ! : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_le hjq.le
  have hj0 : (0 : ℝ) < j ! := by positivity
  calc ε ^ q / q ! ≤ ε ^ j / c / q ! := div_le_div_of_nonneg_right h1 (by positivity)
    _ ≤ ε ^ j / c / j ! := div_le_div_of_nonneg_left (by positivity) hj0 hjf
    _ = ε ^ j / j ! / c := by ring
