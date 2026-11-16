/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Complexity.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Telescoping sums over successful iterations

Let $(\varphi_k)_{k \ge 0}$ be a real sequence, typically $\varphi_k = f(x_k)$ for the iterates
$x_k$ of a method, and let a predicate mark some iterations as successful. Let $\mathcal{S}_k = \{j
\in [0, k] \mid j \text{ is successful}\}$. If $\varphi$ is unchanged at unsuccessful iterations,
the decreases over $\mathcal{S}_k$ telescope:
$$\sum_{j \in \mathcal{S}_k} (\varphi_j - \varphi_{j+1}) = \varphi_0 - \varphi_{k+1}.$$
Hence, if every successful iteration decreases $\varphi$ by at least $c$ and
$\varphi_{k+1} \ge \varphi_{\mathrm{low}}$, then $c |\mathcal{S}_k| \le \varphi_0 -
\varphi_{\mathrm{low}}$. This is the argument of (2.2.12)–(2.2.13) of [cartis2022evaluation] and of
every lemma there that bounds the number of successful iterations.

## Main results

* `Optimization.sum_successSet_sub_eq`: if $\varphi$ is unchanged at unsuccessful iterations, then
  $\sum_{j \in \mathcal{S}_k} (\varphi_j - \varphi_{j+1}) = \varphi_0 - \varphi_{k+1}$.
* `Optimization.card_successSet_mul_le_of_decrease`: if, in addition, every successful iteration
  decreases $\varphi$ by at least $c$, then $c |\mathcal{S}_k| \le \varphi_0 -
  \varphi_{\mathrm{low}}$.
* `Optimization.card_successSet_le_div_of_decrease`: the same bound in the form $|\mathcal{S}_k| \le
  (\varphi_0 - \varphi_{\mathrm{low}})/c$ for $c > 0$.
* `Optimization.card_mul_le_of_decrease`: for a nonincreasing $\varphi$ and any set $T$ of
  iterations (for example the "good" successful iterations) at which $\varphi$ decreases by at least
  $c$, $c |T| \le \varphi_0 - \varphi_{\mathrm{low}}$.
* `Optimization.exists_last_succ`: if unsuccessful steps do not move a sequence, a final point
  different from the first one was reached by a successful step.

## Implementation notes

* The successful iterations are given by a predicate `succ : ℕ → Prop`, and $\mathcal{S}_k$ is
  `Optimization.successSet succ k`, which contains $k$ itself if $k$ is successful.
-/

open Finset

namespace Optimization

variable {φ : ℕ → ℝ} {succ : ℕ → Prop} {k : ℕ} {c φlow : ℝ}

/-- Let $(\varphi_j)$ be a real sequence and $k \in \mathbb{N}$. If $\varphi_{j+1} = \varphi_j$ for
every unsuccessful iteration $j \le k$, then the decreases over the successful iterations
$\mathcal{S}_k$ telescope:
$$\sum_{j \in \mathcal{S}_k} (\varphi_j - \varphi_{j+1}) = \varphi_0 - \varphi_{k+1}.$$

Here $\mathcal{S}_k$ is `Optimization.successSet succ k`, the set of $j \in [0, k]$ with
`succ j`. -/
theorem sum_successSet_sub_eq (h : ∀ j ≤ k, ¬ succ j → φ (j + 1) = φ j) :
    ∑ j ∈ successSet succ k, (φ j - φ (j + 1)) = φ 0 - φ (k + 1) := by
  classical
  rw [successSet_eq_filter, sum_filter_of_ne, sum_range_sub']
  intro j hj hne
  by_contra hs
  exact hne (by rw [h j (Nat.lt_succ_iff.1 (mem_range.1 hj)) hs, sub_self])

/-- Let $(\varphi_j)$ be a real sequence, $k \in \mathbb{N}$ and
$c, \varphi_{\mathrm{low}} \in \mathbb{R}$. Suppose that $\varphi_{j+1} = \varphi_j$ for every
unsuccessful iteration $j \le k$, that $\varphi_j - \varphi_{j+1} \ge c$ for every successful
iteration $j \le k$, and that $\varphi_{\mathrm{low}} \le \varphi_{k+1}$. Then
$$c \, |\mathcal{S}_k| \le \varphi_0 - \varphi_{\mathrm{low}}.$$

Here $\mathcal{S}_k$ is `Optimization.successSet succ k`. The proof applies
`Optimization.sum_successSet_sub_eq`. -/
theorem card_successSet_mul_le_of_decrease (h : ∀ j ≤ k, ¬ succ j → φ (j + 1) = φ j)
    (hdec : ∀ j ≤ k, succ j → c ≤ φ j - φ (j + 1)) (hlow : φlow ≤ φ (k + 1)) :
    c * (successSet succ k).card ≤ φ 0 - φlow := by
  have hsum : ∑ _j ∈ successSet succ k, c ≤ ∑ j ∈ successSet succ k, (φ j - φ (j + 1)) :=
    sum_le_sum fun j hj => by
      rw [mem_successSet] at hj
      exact hdec j hj.1 hj.2
  rw [sum_successSet_sub_eq h, sum_const, nsmul_eq_mul] at hsum
  linarith

/-- Let $(\varphi_j)$ be a real sequence, $k \in \mathbb{N}$, $c > 0$ and
$\varphi_{\mathrm{low}} \in \mathbb{R}$. Suppose that $\varphi_{j+1} = \varphi_j$ for every
unsuccessful iteration $j \le k$, that $\varphi_j - \varphi_{j+1} \ge c$ for every successful
iteration $j \le k$, and that $\varphi_{\mathrm{low}} \le \varphi_{k+1}$. Then
$$|\mathcal{S}_k| \le \frac{\varphi_0 - \varphi_{\mathrm{low}}}{c}.$$

This is `Optimization.card_successSet_mul_le_of_decrease` divided by $c$. -/
theorem card_successSet_le_div_of_decrease (hc : 0 < c)
    (h : ∀ j ≤ k, ¬ succ j → φ (j + 1) = φ j)
    (hdec : ∀ j ≤ k, succ j → c ≤ φ j - φ (j + 1)) (hlow : φlow ≤ φ (k + 1)) :
    ((successSet succ k).card : ℝ) ≤ (φ 0 - φlow) / c := by
  rw [le_div_iff₀ hc, mul_comm]
  exact card_successSet_mul_le_of_decrease h hdec hlow

/-- Let $(\varphi_j)$ be a real sequence, $N \in \mathbb{N}$, $c \in \mathbb{R}$ and
$T \subseteq [0, N)$ a finite set of indices. If $\varphi_{j+1} \le \varphi_j$ for all $j < N$
and $\varphi_j - \varphi_{j+1} \ge c$ for all $j \in T$, then
$|T| \, c \le \varphi_0 - \varphi_N$. -/
theorem card_mul_le_sub_of_decrease {T : Finset ℕ} {N : ℕ} (hT : T ⊆ range N)
    (hmono : ∀ j < N, φ (j + 1) ≤ φ j) (hdec : ∀ j ∈ T, c ≤ φ j - φ (j + 1)) :
    (T.card : ℝ) * c ≤ φ 0 - φ N := by
  have h1 : ∑ _j ∈ T, c ≤ ∑ j ∈ T, (φ j - φ (j + 1)) := sum_le_sum hdec
  have h2 : ∑ j ∈ T, (φ j - φ (j + 1)) ≤ ∑ j ∈ range N, (φ j - φ (j + 1)) :=
    sum_le_sum_of_subset_of_nonneg hT fun j hj _ => sub_nonneg.2 (hmono j (mem_range.1 hj))
  rw [sum_range_sub', sum_const, nsmul_eq_mul] at *
  linarith

/-- Let $(\varphi_j)$ be a real sequence, $k \in \mathbb{N}$,
$c, \varphi_{\mathrm{low}} \in \mathbb{R}$ and $T \subseteq [0, k]$ a finite set of indices.
Suppose that $\varphi_{j+1} \le \varphi_j$ for all $j \le k$, that
$\varphi_j - \varphi_{j+1} \ge c$ for all $j \in T$, and that
$\varphi_{\mathrm{low}} \le \varphi_{k+1}$. Then
$$c \, |T| \le \varphi_0 - \varphi_{\mathrm{low}}.$$

A typical $T$ is a subset of the successful iterations, such as the successful iterations at
which a stronger decrease condition holds. -/
theorem card_mul_le_of_decrease {T : Finset ℕ} (hT : T ⊆ range (k + 1))
    (hmono : ∀ j ≤ k, φ (j + 1) ≤ φ j) (hdec : ∀ j ∈ T, c ≤ φ j - φ (j + 1))
    (hlow : φlow ≤ φ (k + 1)) :
    c * T.card ≤ φ 0 - φlow := by
  have := card_mul_le_sub_of_decrease hT (fun j hj => hmono j (Nat.lt_succ_iff.1 hj)) hdec
  linarith

/-- Let $(\varphi_j)$ be a real sequence, $k \in \mathbb{N}$, $c > 0$,
$\varphi_{\mathrm{low}} \in \mathbb{R}$ and $T \subseteq [0, k]$ a finite set of indices. If
$\varphi_{j+1} \le \varphi_j$ for all $j \le k$, $\varphi_j - \varphi_{j+1} \ge c$ for all
$j \in T$, and $\varphi_{\mathrm{low}} \le \varphi_{k+1}$, then
$|T| \le (\varphi_0 - \varphi_{\mathrm{low}})/c$. -/
theorem card_le_div_of_decrease {T : Finset ℕ} (hc : 0 < c) (hT : T ⊆ range (k + 1))
    (hmono : ∀ j ≤ k, φ (j + 1) ≤ φ j) (hdec : ∀ j ∈ T, c ≤ φ j - φ (j + 1))
    (hlow : φlow ≤ φ (k + 1)) :
    (T.card : ℝ) ≤ (φ 0 - φlow) / c := by
  rw [le_div_iff₀ hc, mul_comm]
  exact card_mul_le_of_decrease hT hmono hdec hlow

/-- Let $(y_i)$ be a sequence in a type $\alpha$ and $N \in \mathbb{N}$. If $y_{i+1} = y_i$ for
every unsuccessful $i < N$ and $y_N \neq y_0$, then some successful $i < N$ has $y_{i+1} = y_N$:
the final point was reached by a successful step. -/
theorem exists_last_succ {α : Type*} {y : ℕ → α} {succ : ℕ → Prop} :
    ∀ N, (∀ i < N, ¬ succ i → y (i + 1) = y i) → y N ≠ y 0 →
      ∃ i < N, succ i ∧ y (i + 1) = y N := by
  intro N
  induction N with
  | zero => exact fun _ h0 => absurd rfl h0
  | succ N ih =>
    intro hstay hne
    by_cases hs : succ N
    · exact ⟨N, N.lt_succ_self, hs, rfl⟩
    · have heq := hstay N N.lt_succ_self hs
      obtain ⟨i, hi, hsi, hyi⟩ := ih (fun j hj => hstay j (hj.trans N.lt_succ_self))
        (heq ▸ hne)
      exact ⟨i, hi.trans N.lt_succ_self, hsi, hyi.trans heq.symm⟩

end Optimization
