/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.SpecialFunctions.FactorialSum
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Cartis, Gould and Toint, Section A.10: Simple series bounds

This module formalizes §A.10 of [cartis2022evaluation]: bounds on partial sums of the exponential
series $\sum_\ell \delta^\ell / \ell!$. For $\delta \in [0, 1]$ the shifted partial sums are at most
$1 + 2\delta$ and the tails are at most $2\delta^{j+1}/j!$ (A.33). The consequences (A.34)–(A.36)
treat $\delta \in [0, 1]$, $\delta \ge 1$ and $\delta = 1$. The proofs specialize the backbone
module `Numlib.Analysis.SpecialFunctions.FactorialSum`.

## Main results

* Lemma A.10.1, `CartisGouldToint.AppendixA.lemma_A_10_1`: the two bounds (A.33) for
  $\delta \in [0, 1]$.
* Equation (A.34), `CartisGouldToint.AppendixA.eq_A_34`: $\sum_{\ell=1}^j \delta^\ell/\ell! \le
  2\delta \le 2 < 3$ for $\delta \in [0, 1]$.
* Equation (A.35), `CartisGouldToint.AppendixA.eq_A_35`: $\sum_{\ell=1}^j \delta^\ell/\ell! \le
  2\delta^j$ for $\delta \ge 1$.
* Equation (A.36), `CartisGouldToint.AppendixA.eq_A_36`: the case $\delta = 1$ of these bounds.

## Conventions

* A sum $\sum_{\ell=a}^b$ is a sum over `Finset.Icc a b`, and it is $0$ when $a > b$.
-/

open Finset
open scoped Nat

namespace CartisGouldToint.AppendixA

/-- **Lemma A.10.1** of [cartis2022evaluation] (sum bounds). Let $\delta \in [0, 1]$ and let
$j \le p$ be natural numbers. Then the bounds (A.33) hold:
$$\sum_{\ell=j}^p \frac{\delta^{\ell-j}}{(\ell-j)!} \le 1 + 2\delta \qquad \text{and} \qquad
  \sum_{\ell=j+1}^{p+1} \frac{\delta^\ell}{\ell!} \le \frac{2\delta^{j+1}}{j!}.$$
-/
theorem lemma_A_10_1 {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {j p : ℕ} (_hjp : j ≤ p) :
    ∑ ℓ ∈ Icc j p, δ ^ (ℓ - j) / ((ℓ - j)! : ℝ) ≤ 1 + 2 * δ ∧
      ∑ ℓ ∈ Icc (j + 1) (p + 1), δ ^ ℓ / (ℓ ! : ℝ) ≤ 2 * δ ^ (j + 1) / (j ! : ℝ) :=
  ⟨sum_pow_div_factorial_le_one_add_two_mul h0 h1 j p,
    sum_pow_div_factorial_Icc_succ_le h0 h1 j p⟩

/-- **Equation (A.34)** of [cartis2022evaluation]. For $\delta \in [0, 1]$ and every
$j \in \mathbb{N}$,
$$\sum_{\ell=1}^j \frac{\delta^\ell}{\ell!} \le 2\delta \le 2 < 3.$$
-/
theorem eq_A_34 {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (j : ℕ) :
    ∑ ℓ ∈ Icc 1 j, δ ^ ℓ / (ℓ ! : ℝ) ≤ 2 * δ ∧ 2 * δ ≤ 2 ∧ (2 : ℝ) < 3 :=
  ⟨sum_pow_div_factorial_le_two_mul h0 h1 j, by linarith, by norm_num⟩

/-- **Equation (A.35)** of [cartis2022evaluation]. For $\delta \ge 1$ and every $j \in \mathbb{N}$,
$$\sum_{\ell=1}^j \frac{\delta^\ell}{\ell!} \le 2\delta^j.$$
-/
theorem eq_A_35 {δ : ℝ} (h1 : 1 ≤ δ) (j : ℕ) :
    ∑ ℓ ∈ Icc 1 j, δ ^ ℓ / (ℓ ! : ℝ) ≤ 2 * δ ^ j :=
  sum_pow_div_factorial_le_two_mul_pow h1 j

/-- **Equation (A.36)** of [cartis2022evaluation], the case $\delta = 1$. For natural numbers
$j \le p$,
$$\sum_{\ell=1}^j \frac{1}{\ell!} \le 2, \qquad \sum_{\ell=j}^p \frac{1}{(\ell-j)!} < 3 \qquad
  \text{and} \qquad \sum_{\ell=j+1}^{p+1} \frac{1}{\ell!} \le \frac{2}{j!}.$$
-/
theorem eq_A_36 {j p : ℕ} (_hjp : j ≤ p) :
    ∑ ℓ ∈ Icc 1 j, 1 / (ℓ ! : ℝ) ≤ 2 ∧ ∑ ℓ ∈ Icc j p, 1 / ((ℓ - j)! : ℝ) < 3 ∧
      ∑ ℓ ∈ Icc (j + 1) (p + 1), 1 / (ℓ ! : ℝ) ≤ 2 / (j ! : ℝ) := by
  refine ⟨?_, (_root_.sum_inv_factorial_sub_le_exp_one j p).trans_lt ?_, ?_⟩
  · simpa using sum_pow_div_factorial_le_two_mul zero_le_one le_rfl j
  · exact Real.exp_one_lt_d9.trans (by norm_num)
  · simpa using sum_pow_div_factorial_Icc_succ_le zero_le_one le_rfl j p

end CartisGouldToint.AppendixA
