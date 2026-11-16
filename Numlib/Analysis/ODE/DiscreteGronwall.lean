/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.ODE.DiscreteGronwall
import Mathlib.Analysis.Normed.Group.Basic

/-!
# The discrete Gronwall lemma in summed form

The **discrete Gronwall lemma** in summed form states the following. Let $g_0 \ge 0$, and let
$k_s \ge 0$ and $p_s \ge 0$ for all $s \in \mathbb{N}$. If a real sequence $(\varphi_n)$ satisfies
$$\varphi_n \le g_0 + \sum_{s < n} p_s + \sum_{s < n} k_s \varphi_s \quad \text{for every } n,$$
then
$$\varphi_n \le \Big(g_0 + \sum_{s < n} p_s\Big) \exp\Big(\sum_{s < n} k_s\Big) \quad \text{for
  every } n.$$
This is Lemma 11.2 of [quarteroni2000numerical], which refers to [quarteroni1994numerical] for the
proof. Mathlib's `discrete_gronwall` is the recursive form: from $u_{n+1} \le (1 + c_n) u_n + b_n$
it concludes $u_n \le (u_{n_0} + \sum b) \exp(\sum c)$.

The file also proves the constant-coefficient case $p_s = h \delta$, $k_s = h \Lambda$ with the sums
evaluated, which has the shape of the estimates of Theorems 11.1 and 11.2 of
[quarteroni2000numerical], and the form for the norms of a sequence in a normed group. The variants
with the suffix `_of_le` assume the summed inequality only up to a horizon $N$ and conclude up to
$N$. A recursion that is controlled only while the grid nodes stay in the time interval delivers
exactly this.

## Main results

* `Gronwall.discrete_sum`: the discrete Gronwall lemma in summed form.
* `Gronwall.discrete_sum_of_le`: the same on a finite horizon $n \le N$.
* `Gronwall.discrete_sum_const` and `Gronwall.discrete_sum_const_of_le`: the constant-coefficient
  case, $\varphi_n \le (g_0 + n h \delta) \exp(n h \Lambda)$.
* `Gronwall.norm_discrete_sum`: the lemma for the norms $\|w_n\|$ of a sequence in a normed group.

## Proof outline

The summed form follows from the recursive one, applied to the majorant $\psi_n = g_0 + \sum_{s < n}
p_s + \sum_{s < n} k_s \varphi_s$. It satisfies $\varphi_n \le \psi_n$ and $\psi_{n+1} = \psi_n +
p_n + k_n \varphi_n \le (1 + k_n) \psi_n + p_n$.

## Implementation notes

* The source states the hypothesis as $\varphi_0 \le g_0$ together with the summed bound for
  $n \ge 1$. The sums are empty at $n = 0$, so this is the single hypothesis for all $n$ used here.
  No sign condition on $\varphi$ is needed.
* The continuous counterpart, Gronwall's lemma in integral form, is in
  `Numlib.Analysis.ODE.Gronwall`, in the same namespace `Gronwall`. The discrete lemma is used for
  the zero-stability and the convergence of one-step and multistep methods in `Numlib.ODE`.
-/

open Finset Real

namespace Gronwall

/-- The **discrete Gronwall lemma**, summed form. Let $g_0 \ge 0$, and let $k_s \ge 0$ and
$p_s \ge 0$ for every $s \in \mathbb{N}$. Suppose that the real sequence $(\varphi_n)$ satisfies
$$\varphi_n \le g_0 + \sum_{s < n} p_s + \sum_{s < n} k_s \varphi_s \quad \text{for every } n
  \in \mathbb{N},$$
which at $n = 0$ is $\varphi_0 \le g_0$. Then for every $n \in \mathbb{N}$,
$$\varphi_n \le \Big(g_0 + \sum_{s < n} p_s\Big) \exp\Big(\sum_{s < n} k_s\Big).$$
This is Lemma 11.2 of [quarteroni2000numerical]. -/
theorem discrete_sum {φ k p : ℕ → ℝ} {g₀ : ℝ} (hg₀ : 0 ≤ g₀) (hk : ∀ s, 0 ≤ k s)
    (hp : ∀ s, 0 ≤ p s)
    (h : ∀ n, φ n ≤ g₀ + ∑ s ∈ range n, p s + ∑ s ∈ range n, k s * φ s) (n : ℕ) :
    φ n ≤ (g₀ + ∑ s ∈ range n, p s) * exp (∑ s ∈ range n, k s) := by
  set ψ : ℕ → ℝ := fun n => g₀ + ∑ s ∈ range n, p s + ∑ s ∈ range n, k s * φ s with hψ
  have hψ0 : ψ 0 = g₀ := by simp [ψ]
  have hrec : ∀ m ≥ 0, ψ (m + 1) ≤ (1 + k m) * ψ m + p m := by
    intro m _
    have : ψ (m + 1) = ψ m + p m + k m * φ m := by
      simp only [ψ, sum_range_succ]
      ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left (h m) (hk m)]
  have key := discrete_gronwall (u := ψ) (b := p) (c := k) (n₀ := 0) (hψ0 ▸ hg₀) hrec
    (fun m _ => hk m) (fun m _ => hp m) (Nat.zero_le n)
  rw [hψ0, ← range_eq_Ico] at key
  exact (h n).trans key

/-- The **discrete Gronwall lemma on a finite horizon**. Let $N \in \mathbb{N}$, let $g_0 \ge 0$,
and let $k_s \ge 0$ and $p_s \ge 0$ for every $s$. Suppose that
$$\varphi_n \le g_0 + \sum_{s < n} p_s + \sum_{s < n} k_s \varphi_s \quad \text{for every } n
  \le N.$$
Then for every $n \le N$,
$$\varphi_n \le \Big(g_0 + \sum_{s < n} p_s\Big) \exp\Big(\sum_{s < n} k_s\Big).$$

This is the form that the one-step and multistep theories use, where the recursion is controlled
only while the nodes stay in the time interval. The proof applies `Gronwall.discrete_sum` to the
sequence $\varphi'_n = \max(\varphi_n, 0)$ for $n \le N$ and $\varphi'_n = 0$ for $n > N$, which
satisfies the hypothesis for every $n$. -/
theorem discrete_sum_of_le {φ k p : ℕ → ℝ} {g₀ : ℝ} {N : ℕ} (hg₀ : 0 ≤ g₀) (hk : ∀ s, 0 ≤ k s)
    (hp : ∀ s, 0 ≤ p s)
    (h : ∀ n ≤ N, φ n ≤ g₀ + ∑ s ∈ range n, p s + ∑ s ∈ range n, k s * φ s) {n : ℕ}
    (hn : n ≤ N) : φ n ≤ (g₀ + ∑ s ∈ range n, p s) * exp (∑ s ∈ range n, k s) := by
  set φ' : ℕ → ℝ := fun m => if m ≤ N then max (φ m) 0 else 0 with hφ'
  have hφ'0 : ∀ m, 0 ≤ φ' m := fun m => by
    simp only [φ']; split_ifs <;> simp
  have hle : ∀ m ≤ N, φ m ≤ φ' m := fun m hm => by
    simp only [φ', hm, ite_true]; exact le_max_left _ _
  have hsum : ∀ m, φ' m ≤ g₀ + ∑ s ∈ range m, p s + ∑ s ∈ range m, k s * φ' s := by
    intro m
    have hnn : 0 ≤ g₀ + ∑ s ∈ range m, p s + ∑ s ∈ range m, k s * φ' s :=
      add_nonneg (add_nonneg hg₀ (sum_nonneg fun s _ => hp s))
        (sum_nonneg fun s _ => mul_nonneg (hk s) (hφ'0 s))
    have hm' : φ' m = if m ≤ N then max (φ m) 0 else 0 := rfl
    rw [hm']
    split_ifs with hm
    · refine max_le ((h m hm).trans ?_) hnn
      exact add_le_add_right (sum_le_sum fun s hs =>
        mul_le_mul_of_nonneg_left (hle s ((mem_range.1 hs).le.trans hm)) (hk s)) _
    · exact hnn
  exact (hle n hn).trans (discrete_sum hg₀ hk hp hsum n)

/-- The **constant-coefficient discrete Gronwall lemma on a finite horizon**. Let $N \in \mathbb{N}$
and let $g_0, h, \delta, \Lambda \ge 0$. Suppose that
$$\varphi_n \le g_0 + n h \delta + h \Lambda \sum_{s < n} \varphi_s \quad \text{for every } n
  \le N.$$
Then for every $n \le N$,
$$\varphi_n \le (g_0 + n h \delta) \exp(n h \Lambda).$$
-/
theorem discrete_sum_const_of_le {φ : ℕ → ℝ} {g₀ h δ Λ : ℝ} {N : ℕ} (hg₀ : 0 ≤ g₀) (hh : 0 ≤ h)
    (hδ : 0 ≤ δ) (hΛ : 0 ≤ Λ)
    (hφ : ∀ n ≤ N, φ n ≤ g₀ + n * h * δ + h * Λ * ∑ s ∈ range n, φ s) {n : ℕ} (hn : n ≤ N) :
    φ n ≤ (g₀ + n * h * δ) * exp (n * h * Λ) := by
  have key := discrete_sum_of_le (φ := φ) (k := fun _ => h * Λ) (p := fun _ => h * δ) hg₀
    (fun _ => mul_nonneg hh hΛ) (fun _ => mul_nonneg hh hδ) (fun m hm => by
      simpa [sum_const, card_range, nsmul_eq_mul, mul_sum, mul_assoc] using hφ m hm) hn
  simpa [sum_const, card_range, nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using key

/-- The **constant-coefficient discrete Gronwall lemma**. Let $g_0, h, \delta, \Lambda \ge 0$, and
suppose that
$$\varphi_n \le g_0 + n h \delta + h \Lambda \sum_{s < n} \varphi_s \quad \text{for every } n
  \in \mathbb{N}.$$
Then for every $n \in \mathbb{N}$,
$$\varphi_n \le (g_0 + n h \delta) \exp(n h \Lambda).$$
This has the shape of the estimates of Theorems 11.1 and 11.2 of [quarteroni2000numerical].

It is `Gronwall.discrete_sum_const_of_le` with the horizon $N = n$. -/
theorem discrete_sum_const {φ : ℕ → ℝ} {g₀ h δ Λ : ℝ} (hg₀ : 0 ≤ g₀) (hh : 0 ≤ h) (hδ : 0 ≤ δ)
    (hΛ : 0 ≤ Λ) (hφ : ∀ n, φ n ≤ g₀ + n * h * δ + h * Λ * ∑ s ∈ range n, φ s) (n : ℕ) :
    φ n ≤ (g₀ + n * h * δ) * exp (n * h * Λ) :=
  discrete_sum_const_of_le hg₀ hh hδ hΛ (fun m _ => hφ m) le_rfl

variable {E : Type*} [SeminormedAddGroup E]

/-- The **discrete Gronwall lemma for a sequence in a normed group**. Let $E$ be a seminormed
additive group, let $(w_n)$ be a sequence in $E$, let $g_0 \ge 0$, and let $k_s \ge 0$ and
$p_s \ge 0$ for every $s$. Suppose that
$$\|w_n\| \le g_0 + \sum_{s < n} p_s + \sum_{s < n} k_s \|w_s\| \quad \text{for every } n \in
  \mathbb{N}.$$
Then for every $n \in \mathbb{N}$,
$$\|w_n\| \le \Big(g_0 + \sum_{s < n} p_s\Big) \exp\Big(\sum_{s < n} k_s\Big).$$

This is `Gronwall.discrete_sum` applied to $n \mapsto \|w_n\|$. It is typically applied to the
difference of two orbits. -/
theorem norm_discrete_sum {w : ℕ → E} {k p : ℕ → ℝ} {g₀ : ℝ} (hg₀ : 0 ≤ g₀) (hk : ∀ s, 0 ≤ k s)
    (hp : ∀ s, 0 ≤ p s)
    (h : ∀ n, ‖w n‖ ≤ g₀ + ∑ s ∈ range n, p s + ∑ s ∈ range n, k s * ‖w s‖) (n : ℕ) :
    ‖w n‖ ≤ (g₀ + ∑ s ∈ range n, p s) * exp (∑ s ∈ range n, k s) :=
  discrete_sum hg₀ hk hp h n

end Gronwall
