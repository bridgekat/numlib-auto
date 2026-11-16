/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Two-level difference schemes: consistency and stability give convergence

A two-level scheme advances an approximation by a fixed amplification operator $Q$ and a source
term, $v^{m+1} = Q v^m + h g^m$, where $h$ is the step in the evolution variable. The exact values
$u^m$ of the approximated problem satisfy the same recursion up to a local truncation error,
$u^{m+1} = Q u^m + h g^m + h \tau^m$. The error $e^m = u^m - v^m$ therefore satisfies
$e^{m+1} = Q e^m + h \tau^m$ with $e^0 = 0$, and its closed form is
$$e^m = h \sum_{l < m} Q^{m-1-l} \tau^l.$$

The convergence theorem is a geometric-sum estimate on this formula. If the powers of $Q$ are
bounded by $M_0$ up to step $N$ (stability) and the truncation errors are bounded by $\delta$
(consistency), then over a finite horizon $N h \le T$ the error is at most $M_0 T \delta$. This is
Theorem 6.3.2 of [han2009theoretical], where $\delta = c (h_x^{p_1} + h^{p_2})$ turns the bound into
the convergence order of a scheme.

## Main results

* `FiniteDifference.sub_eq_smul_sum`: the discrete Duhamel formula
  $u^k - v^k = h \sum_{l < k} Q^{k-1-l} \tau^l$.
* `FiniteDifference.norm_sub_le_of_stable`: a stable, consistent two-level scheme has the error
  bound $\|u^m - v^m\| \le M_0 T \delta$ for $m \le N$.

## Implementation notes

* The statement is an inequality with explicit constants. It has no limit, no order symbol, and no
  family indexed by a mesh parameter. Consistency, order, stability and convergence of a family of
  schemes as the mesh is refined are each this inequality together with a limit, and they are
  defined with that family, as in `FiniteDifference.IsStableFamily`.
* The space is a real normed space, because the step $h$ is a real scalar that acts on its elements.
-/

namespace FiniteDifference

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **discrete Duhamel formula**. Let $E$ be a real normed space, let $Q \colon E \to E$ be a
continuous linear map, let $h \in \mathbb{R}$, and let $N \in \mathbb{N}$. Let the sequences
$u, v, g, \tau$ in $E$ satisfy $v^{m+1} = Q v^m + h g^m$ and
$u^{m+1} = Q u^m + h g^m + h \tau^m$ for $m < N$, and $u^0 = v^0$. Then for every $k \le N$,
$$u^k - v^k = h \sum_{l < k} Q^{k-1-l} \tau^l.$$

The proof uses only the linearity of $Q$. It needs no bound on the powers of $Q$, no bound on
the truncation errors $\tau^l$, and no sign condition on $h$. -/
theorem sub_eq_smul_sum {Q : E →L[ℝ] E} {u v g τ : ℕ → E} {h : ℝ} {N : ℕ}
    (hv : ∀ m < N, v (m + 1) = Q (v m) + h • g m)
    (hu : ∀ m < N, u (m + 1) = Q (u m) + h • g m + h • τ m) (h0 : u 0 = v 0) {k : ℕ}
    (hk : k ≤ N) : u k - v k = h • ∑ l ∈ Finset.range k, (Q ^ (k - 1 - l)) (τ l) := by
  induction k with
  | zero => simp [h0]
  | succ n ih =>
    have hnN : n < N := hk
    have hn := ih (Nat.le_of_succ_le hk)
    have hstep : Q (u n) + h • g n + h • τ n - (Q (v n) + h • g n)
        = Q (u n - v n) + h • τ n := by
      rw [map_sub]
      abel
    have hrhs : ∑ l ∈ Finset.range (n + 1), (Q ^ (n + 1 - 1 - l)) (τ l)
        = (∑ l ∈ Finset.range n, Q ((Q ^ (n - 1 - l)) (τ l))) + τ n := by
      rw [Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl fun l hl => ?_
        have hl' : l < n := Finset.mem_range.mp hl
        have hidx : n + 1 - 1 - l = n - 1 - l + 1 := by omega
        rw [hidx, pow_succ']
        rfl
      · simp
    rw [hu n hnN, hv n hnN, hstep, hn, map_smul, map_sum, hrhs, smul_add]

/-- **Convergence of a stable, consistent two-level scheme.** Let $E$ be a real normed space, let
$Q \colon E \to E$ be a continuous linear map, let $h \ge 0$, $\delta \ge 0$, $T$ and $M_0$ be
real numbers, and let $N \in \mathbb{N}$ with $N h \le T$. Let the computed values $v$ satisfy
$v^{m+1} = Q v^m + h g^m$ and the exact values $u$ satisfy $u^{m+1} = Q u^m + h g^m + h \tau^m$
for $m < N$, with $u^0 = v^0$. Assume that the scheme is stable up to step $N$, that is
$\|Q^m\| \le M_0$ for $m \le N$, and that the local truncation errors satisfy
$\|\tau^m\| \le \delta$ for $m < N$. Then
$$\|u^m - v^m\| \le M_0 T \delta \quad \text{for every } m \le N.$$

This is Theorem 6.3.2 of [han2009theoretical]. The bound is uniform in $m$: the error grows at
most linearly in the number of steps, and the condition $N h \le T$ turns this growth into a
constant that depends only on the horizon. The proof bounds the discrete Duhamel formula
`FiniteDifference.sub_eq_smul_sum` term by term. -/
theorem norm_sub_le_of_stable {Q : E →L[ℝ] E} {u v g τ : ℕ → E} {h T M₀ δ : ℝ} {N : ℕ}
    (hh : 0 ≤ h) (hδ : 0 ≤ δ) (hT : (N : ℝ) * h ≤ T)
    (hv : ∀ m < N, v (m + 1) = Q (v m) + h • g m)
    (hu : ∀ m < N, u (m + 1) = Q (u m) + h • g m + h • τ m) (h0 : u 0 = v 0)
    (hQ : ∀ m ≤ N, ‖Q ^ m‖ ≤ M₀) (hτ : ∀ m < N, ‖τ m‖ ≤ δ) {m : ℕ} (hm : m ≤ N) :
    ‖u m - v m‖ ≤ M₀ * T * δ := by
  have hM₀ : 0 ≤ M₀ := le_trans (norm_nonneg _) (hQ 0 (Nat.zero_le N))
  have hsum : ‖∑ l ∈ Finset.range m, (Q ^ (m - 1 - l)) (τ l)‖ ≤ (m : ℝ) * (M₀ * δ) := by
    calc ‖∑ l ∈ Finset.range m, (Q ^ (m - 1 - l)) (τ l)‖
        ≤ ∑ l ∈ Finset.range m, ‖(Q ^ (m - 1 - l)) (τ l)‖ := norm_sum_le _ _
      _ ≤ ∑ _l ∈ Finset.range m, M₀ * δ := by
          refine Finset.sum_le_sum fun l hl => ?_
          have hl' : l < m := Finset.mem_range.mp hl
          exact le_trans (ContinuousLinearMap.le_opNorm _ _)
            (mul_le_mul (hQ _ (by omega)) (hτ l (by omega)) (norm_nonneg _) hM₀)
      _ = (m : ℝ) * (M₀ * δ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmh : (m : ℝ) * h ≤ T :=
    le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hh) hT
  rw [sub_eq_smul_sum hv hu h0 hm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
  calc h * ‖∑ l ∈ Finset.range m, (Q ^ (m - 1 - l)) (τ l)‖ ≤ h * ((m : ℝ) * (M₀ * δ)) :=
        mul_le_mul_of_nonneg_left hsum hh
    _ = (m : ℝ) * h * (M₀ * δ) := by ring
    _ ≤ T * (M₀ * δ) := mul_le_mul_of_nonneg_right hmh (mul_nonneg hM₀ hδ)
    _ = M₀ * T * δ := by ring

end FiniteDifference
