/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Constrained.TargetResidual
import Numlib.Optimization.Complexity.Telescoping

/-!
# Targets of two-phase target-following methods

The two-phase methods TPp-GC (Algorithm 7.2.1) and TPqp-GC (Algorithm 14.3.2) of
[cartis2022evaluation] solve $\min f(x)$ subject to $x \in \mathcal{X}$ and $c(x) = 0$. Phase 1
finds an approximately feasible point $x_1$ with $\|c(x_1)\| \le \theta \varepsilon_0$. Phase 2
follows a decreasing sequence of targets $t_k$. At outer iteration $k$ an inner method decreases the
residual norm $\|r(x, t_k)\|$ (`Constrained.targetResidual`) from $x_k$ to $x_{k+1}$. The target is
then reset either by (7.2.11), in case (a) where the residual has become small, or by the reflection
(7.2.13), in case (b) where $f(x_{k+1}) < t_k$.

This file records the bookkeeping of the targets, independently of the inner method. It proves their
properties (Lemmas 7.2.3 and 7.2.4, which hold verbatim for TPqp-GC), and it gives the counting
lemmas behind the telescoping arguments of Lemmas 7.2.6 and 14.3.8. The outer loop itself is
`Constrained.IsTargetFollowingRun` in `Numlib.Optimization.Constrained.TwoPhase.Run`, and its
complexity is in `Numlib.Optimization.Constrained.TwoPhase.Complexity`.

## Main definitions

* `Constrained.IsTargetSequence`: the outer iterates $x_k$, the targets $t_k$ and the set
  $\mathcal{K}_a$ of case-(a) iterations satisfy Steps 0, 1 and 2 of Phase 2 for the outer
  iterations $k \in [1, K)$.

## Main results

* `Constrained.IsTargetSequence.props`: Lemma 7.2.3, the properties (7.2.26)–(7.2.31) of the
  targets.
* `Constrained.IsTargetSequence.card_mul_le_of_target_drop`: the iterations that lower the target by
  at least $\tau$ are at most $(f_{\mathrm{up}} - f_{\mathrm{low}} + 1) / \tau$ in number.
* `Constrained.IsTargetSequence.card_Ka_le`: Lemma 7.2.4, $|\mathcal{K}_a| \le (f_{\mathrm{up}} -
  f_{\mathrm{low}} + 1) / ((1 - \theta) \varepsilon_0)$.
* `Constrained.IsTargetSequence.sum_max_sub_le`: the decrease of the residual above
  $\theta \varepsilon_0$ over the outer iterations $[1, K]$ is at most $(1 - \theta) \varepsilon_0
  (|\mathcal{K}_a \cap [1, K)| + 1)$.
* `Constrained.le_card_add_sum_of_cover`: a count of the outer iterations by case-(a) iterations,
  bad iterations and productive iterations.
* `Constrained.sub_ge_of_residual_decrease`, `Constrained.sub_ge_of_merit_decrease`: a merit
  decrease that the inner method guarantees lowers the residual by a fixed amount.
* `Constrained.card_le_of_residual_block`: the number of good successful inner iterations between
  two consecutive case-(a) iterations is $O\big((1 - \theta) \max_l \varepsilon_0^{2 - \pi_l}
  \varepsilon_l^{-\pi_l}\big)$ (Lemmas 7.2.6 and 14.3.8).

## Implementation notes

* The set $\mathcal{K}_a$ is a parameter `Ka`, constrained only by the two cases. Case (a) (`Ka k`)
  needs $\|r(x_{k+1}, t_k)\| \le \theta \varepsilon_0$, and case (b) (`¬ Ka k`) needs
  $\|r(x_{k+1}, t_k)\| \ge \theta \varepsilon_0$ and $f(x_{k+1}) < t_k$. This covers the residual
  test of Step 2(a) both in the form $\le \theta \varepsilon_0$ and in the strict form
  $< \theta \varepsilon_0$.
* The terminating case (c) does not occur before the horizon $K$.
-/
open Finset
open scoped Topology

namespace Constrained

variable {E F : Type*} [NormedAddCommGroup F]

/-- **Outer bookkeeping of Phase 2** of TPp-GC (Algorithm 7.2.1) and TPqp-GC (Algorithm 14.3.2) of
[cartis2022evaluation]. Let $x_k$ be the outer iterates, $t_k$ the targets, $K$ a horizon, and
$\mathcal{K}_a$ the set of case-(a) iterations ((7.2.25), (14.3.36)). The sequence is a **target
sequence** if:
* Step 0: $\|c(x_1)\| \le \theta \varepsilon_0$ (Phase 1 did not terminate) and $t_1 = f(x_1) -
  \sqrt{\varepsilon_0^2 - \|c(x_1)\|^2}$;
* Step 1, for $1 \le k < K$: the inner method does not increase the residual,
  $\|r(x_{k+1}, t_k)\| \le \|r(x_k, t_k)\|$;
* Step 2(a), for $1 \le k < K$ with $k \in \mathcal{K}_a$:
  $\|r(x_{k+1}, t_k)\| \le \theta \varepsilon_0$ and $t_{k+1} = f(x_{k+1}) -
  \sqrt{\varepsilon_0^2 - \|c(x_{k+1})\|^2}$, as in (7.2.11);
* Step 2(b), for $1 \le k < K$ with $k \notin \mathcal{K}_a$:
  $\|r(x_{k+1}, t_k)\| \ge \theta \varepsilon_0$, $f(x_{k+1}) < t_k$ and
  $t_{k+1} = 2 f(x_{k+1}) - t_k$, as in (7.2.13).

Algorithm 7.2.1, with the test $\le \theta \varepsilon_0$ in Step 2(a), takes
$k \in \mathcal{K}_a$ if and only if $\|r(x_{k+1}, t_k)\| \le \theta \varepsilon_0$. Algorithm
14.3.2 takes $k \in \mathcal{K}_a$ if and only if $\|r(x_{k+1}, t_k)\| < \theta \varepsilon_0$. -/
structure IsTargetSequence (f : E → ℝ) (c : E → F) (θ ε₀ : ℝ) (x : ℕ → E) (t : ℕ → ℝ)
    (Ka : ℕ → Prop) (K : ℕ) : Prop where
  /-- Phase 1 ended with $\|c(x_1)\| \le \theta \varepsilon_0$. -/
  norm_one_le : ‖c (x 1)‖ ≤ θ * ε₀
  /-- Step 0: the first target is $t_1 = f(x_1) - \sqrt{\varepsilon_0^2 - \|c(x_1)\|^2}$. -/
  target_one : t 1 = f (x 1) - √(ε₀ ^ 2 - ‖c (x 1)‖ ^ 2)
  /-- Step 1: for $1 \le k < K$, the inner method does not increase the residual,
  $\|r(x_{k+1}, t_k)\| \le \|r(x_k, t_k)\|$. -/
  residual_succ_le : ∀ k, 1 ≤ k → k < K →
    targetResidual f c (t k) (x (k + 1)) ≤ targetResidual f c (t k) (x k)
  /-- Step 2(a) is entered only when $\|r(x_{k+1}, t_k)\| \le \theta \varepsilon_0$. -/
  residual_le_of_Ka : ∀ k, 1 ≤ k → k < K → Ka k → targetResidual f c (t k) (x (k + 1)) ≤ θ * ε₀
  /-- Step 2(a): the target update (7.2.11), $t_{k+1} = f(x_{k+1}) - \sqrt{\varepsilon_0^2 -
  \|c(x_{k+1})\|^2}$. -/
  target_succ_of_Ka : ∀ k, 1 ≤ k → k < K → Ka k →
    t (k + 1) = f (x (k + 1)) - √(ε₀ ^ 2 - ‖c (x (k + 1))‖ ^ 2)
  /-- Step 2(b) is entered only when $\|r(x_{k+1}, t_k)\| \ge \theta \varepsilon_0$. -/
  le_residual_of_not_Ka : ∀ k, 1 ≤ k → k < K → ¬ Ka k →
    θ * ε₀ ≤ targetResidual f c (t k) (x (k + 1))
  /-- Step 2(b) is entered only when $f(x_{k+1}) < t_k$. -/
  lt_target_of_not_Ka : ∀ k, 1 ≤ k → k < K → ¬ Ka k → f (x (k + 1)) < t k
  /-- Step 2(b): the target update (7.2.13), $t_{k+1} = 2 f(x_{k+1}) - t_k$. -/
  target_succ_of_not_Ka : ∀ k, 1 ≤ k → k < K → ¬ Ka k → t (k + 1) = 2 * f (x (k + 1)) - t k

namespace IsTargetSequence

variable {f : E → ℝ} {c : E → F} {θ ε₀ : ℝ} {x : ℕ → E} {t : ℕ → ℝ} {Ka : ℕ → Prop} {K : ℕ}
  {k : ℕ}

/-- A target sequence up to the horizon $K$ is a target sequence up to every horizon $K' \le K$. -/
theorem mono (h : IsTargetSequence f c θ ε₀ x t Ka K) {K' : ℕ} (hK : K' ≤ K) :
    IsTargetSequence f c θ ε₀ x t Ka K' where
  norm_one_le := h.norm_one_le
  target_one := h.target_one
  residual_succ_le k h1 hk := h.residual_succ_le k h1 (hk.trans_le hK)
  residual_le_of_Ka k h1 hk := h.residual_le_of_Ka k h1 (hk.trans_le hK)
  target_succ_of_Ka k h1 hk := h.target_succ_of_Ka k h1 (hk.trans_le hK)
  le_residual_of_not_Ka k h1 hk := h.le_residual_of_not_Ka k h1 (hk.trans_le hK)
  lt_target_of_not_Ka k h1 hk := h.lt_target_of_not_Ka k h1 (hk.trans_le hK)
  target_succ_of_not_Ka k h1 hk := h.target_succ_of_not_Ka k h1 (hk.trans_le hK)

/-- Let $x_k$, $t_k$ be a target sequence up to the horizon $K$. For $1 \le k \le K$, the iterates
lie above their targets: $f(x_k) \ge t_k$. This is (7.2.26) of [cartis2022evaluation]. -/
theorem sub_target_nonneg (h : IsTargetSequence f c θ ε₀ x t Ka K) (hk1 : 1 ≤ k)
    (hkK : k ≤ K) : 0 ≤ f (x k) - t k := by
  obtain rfl | ⟨j, rfl, hj⟩ : k = 1 ∨ ∃ j, k = j + 1 ∧ 1 ≤ j := by
    rcases Nat.lt_or_ge 1 k with hk | hk
    · exact Or.inr ⟨k - 1, by omega, by omega⟩
    · exact Or.inl (by omega)
  · rw [h.target_one, sub_sub_cancel]
    exact Real.sqrt_nonneg _
  · by_cases ha : Ka j
    · rw [h.target_succ_of_Ka j hj (by omega) ha, sub_sub_cancel]
      exact Real.sqrt_nonneg _
    · rw [h.target_succ_of_not_Ka j hj (by omega) ha]
      linarith [h.lt_target_of_not_Ka j hj (by omega) ha]

/-- Let $x_k$, $t_k$ be a target sequence up to the horizon $K$. Let $\theta \le 1$ and
$\varepsilon_0 \ge 0$. After a case-(a) iteration $k$ with $1 \le k < K$, the residual is reset
to $\|r(x_{k+1}, t_{k+1})\| = \varepsilon_0$. This is (7.2.27) of [cartis2022evaluation]. -/
theorem residual_succ_of_Ka (h : IsTargetSequence f c θ ε₀ x t Ka K) (hθ : θ ≤ 1)
    (hε₀ : 0 ≤ ε₀) (hk1 : 1 ≤ k) (hkK : k < K) (ha : Ka k) :
    targetResidual f c (t (k + 1)) (x (k + 1)) = ε₀ := by
  rw [h.target_succ_of_Ka k hk1 hkK ha]
  refine targetResidual_sub_sqrt hε₀ ?_
  calc ‖c (x (k + 1))‖ ≤ targetResidual f c (t k) (x (k + 1)) := norm_le_targetResidual
    _ ≤ θ * ε₀ := h.residual_le_of_Ka k hk1 hkK ha
    _ ≤ ε₀ := mul_le_of_le_one_left hε₀ hθ

/-- Let $x_k$, $t_k$ be a target sequence up to the horizon $K$. After a case-(b) iteration $k$ with
$1 \le k < K$, the target update does not change the residual:
$\|r(x_{k+1}, t_{k+1})\| = \|r(x_{k+1}, t_k)\|$. This is (7.2.28) and (7.2.41) of
[cartis2022evaluation]. -/
theorem residual_succ_of_not_Ka (h : IsTargetSequence f c θ ε₀ x t Ka K) (hk1 : 1 ≤ k)
    (hkK : k < K) (ha : ¬ Ka k) :
    targetResidual f c (t (k + 1)) (x (k + 1)) = targetResidual f c (t k) (x (k + 1)) := by
  rw [h.target_succ_of_not_Ka k hk1 hkK ha, targetResidual_two_mul_sub]

/-- Let $x_k$, $t_k$ be a target sequence up to the horizon $K$. Let $\theta \le 1$ and
$\varepsilon_0 \ge 0$. Then $\|r(x_k, t_k)\| \le \varepsilon_0$ for $1 \le k \le K$. This is
(7.2.27)–(7.2.28) of [cartis2022evaluation]. -/
theorem residual_le (h : IsTargetSequence f c θ ε₀ x t Ka K) (hθ : θ ≤ 1) (hε₀ : 0 ≤ ε₀)
    (hk1 : 1 ≤ k) (hkK : k ≤ K) : targetResidual f c (t k) (x k) ≤ ε₀ := by
  induction k, hk1 using Nat.le_induction with
  | base =>
    rw [h.target_one, targetResidual_sub_sqrt hε₀
      (h.norm_one_le.trans (mul_le_of_le_one_left hε₀ hθ))]
  | succ j hj ih =>
    by_cases ha : Ka j
    · exact (h.residual_succ_of_Ka hθ hε₀ hj (by omega) ha).le
    · rw [h.residual_succ_of_not_Ka hj (by omega) ha]
      exact (h.residual_succ_le j hj (by omega)).trans (ih (by omega))

/-- Let $x_k$, $t_k$ be a target sequence up to the horizon $K$. Let $\theta \le 1$ and
$\varepsilon_0 \ge 0$. Then $\|c(x_k)\| \le \varepsilon_0$ for $1 \le k \le K$. This is (7.2.29)
of [cartis2022evaluation]. -/
theorem norm_le (h : IsTargetSequence f c θ ε₀ x t Ka K) (hθ : θ ≤ 1) (hε₀ : 0 ≤ ε₀)
    (hk1 : 1 ≤ k) (hkK : k ≤ K) : ‖c (x k)‖ ≤ ε₀ :=
  norm_le_targetResidual.trans (h.residual_le hθ hε₀ hk1 hkK)

/-- Let $x_k$, $t_k$ be a target sequence up to the horizon $K$. Let $\theta \le 1$ and
$\varepsilon_0 \ge 0$. Then $f(x_k) - t_k \le \varepsilon_0$ for $1 \le k \le K$. This is
(7.2.29) of [cartis2022evaluation]. -/
theorem sub_target_le (h : IsTargetSequence f c θ ε₀ x t Ka K) (hθ : θ ≤ 1) (hε₀ : 0 ≤ ε₀)
    (hk1 : 1 ≤ k) (hkK : k ≤ K) : f (x k) - t k ≤ ε₀ :=
  sub_le_targetResidual.trans (h.residual_le hθ hε₀ hk1 hkK)

/-- Let $x_k$, $t_k$ be a target sequence up to the horizon $K$. Let $0 \le \theta \le 1$ and
$\varepsilon_0 \ge 0$. A case-(a) iteration $k$ with $1 \le k < K$ decreases the target by at
least $(1 - \theta) \varepsilon_0$: $t_k - t_{k+1} \ge (1 - \theta) \varepsilon_0$. This is
(7.2.30) of [cartis2022evaluation], proved with Lemma B.7.1 (`neg_add_sqrt_sq_sub_sq_ge`). -/
theorem sub_target_succ_ge_of_Ka (h : IsTargetSequence f c θ ε₀ x t Ka K) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ 1) (hε₀ : 0 ≤ ε₀) (hk1 : 1 ≤ k) (hkK : k < K) (ha : Ka k) :
    (1 - θ) * ε₀ ≤ t k - t (k + 1) := by
  have hr := h.residual_le_of_Ka k hk1 hkK ha
  have huv : (f (x (k + 1)) - t k) ^ 2 + ‖c (x (k + 1))‖ ^ 2 ≤ (θ * ε₀) ^ 2 := by
    rw [add_comm, ← targetResidual_sq]
    exact pow_le_pow_left₀ targetResidual_nonneg hr 2
  have key := neg_add_sqrt_sq_sub_sq_ge (mul_nonneg hθ0 hε₀) (mul_le_of_le_one_left hε₀ hθ) huv
  rw [h.target_succ_of_Ka k hk1 hkK ha]
  linarith

/-- Let $x_k$, $t_k$ be a target sequence up to the horizon $K$. Let $0 \le \theta < 1$ and
$\varepsilon_0 > 0$. Then the targets decrease strictly: $t_{k+1} < t_k$ for $1 \le k < K$. This
is part of Lemma 7.2.3 of [cartis2022evaluation]. -/
theorem target_succ_lt (h : IsTargetSequence f c θ ε₀ x t Ka K) (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (hε₀ : 0 < ε₀) (hk1 : 1 ≤ k) (hkK : k < K) : t (k + 1) < t k := by
  by_cases ha : Ka k
  · have := h.sub_target_succ_ge_of_Ka hθ0 hθ.le hε₀.le hk1 hkK ha
    nlinarith
  · rw [h.target_succ_of_not_Ka k hk1 hkK ha]
    linarith [h.lt_target_of_not_Ka k hk1 hkK ha]

/-- Let $x_k$, $t_k$ be a target sequence up to the horizon $K$. Let $0 \le \theta < 1$ and
$\varepsilon_0 > 0$. Then the targets are nonincreasing on $[1, K]$: $t_j \le t_i$ for
$1 \le i \le j \le K$. -/
theorem target_le_of_le (h : IsTargetSequence f c θ ε₀ x t Ka K) (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (hε₀ : 0 < ε₀) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hjK : j ≤ K) : t j ≤ t i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (h.target_succ_lt hθ0 hθ hε₀ (hi.trans hij) (by omega)).le.trans (ih (by omega))

/-- Let $x_k$, $t_k$ be a target sequence up to the horizon $K$. Let $\theta \le 1$ and
$0 \le \varepsilon_0 \le 1$, and let $x_k \in X$ for $1 \le k \le K$. Assume f.B.Fb of
[cartis2022evaluation]: $f_{\mathrm{low}} \le f(z) \le f_{\mathrm{up}}$ for every $z \in X$ with
$\|c(z)\| \le \varepsilon_0$. Then $t_k \in [f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$ for
$1 \le k \le K$. This is (7.2.31) of [cartis2022evaluation]. -/
theorem target_mem_Icc (h : IsTargetSequence f c θ ε₀ x t Ka K) (hθ : θ ≤ 1) (hε₀ : 0 ≤ ε₀)
    (hε₀1 : ε₀ ≤ 1) {X : Set E} {flow fup : ℝ} (hxX : ∀ k, 1 ≤ k → k ≤ K → x k ∈ X)
    (hB : ∀ z ∈ X, ‖c z‖ ≤ ε₀ → flow ≤ f z ∧ f z ≤ fup) (hk1 : 1 ≤ k) (hkK : k ≤ K) :
    t k ∈ Set.Icc (flow - 1) fup := by
  have hb := hB (x k) (hxX k hk1 hkK) (h.norm_le hθ hε₀ hk1 hkK)
  have h1 := h.sub_target_nonneg hk1 hkK
  have h2 := h.sub_target_le hθ hε₀ hk1 hkK
  constructor <;> linarith [hb.1, hb.2]

/-- **Lemma 7.2.3** of [cartis2022evaluation], which holds verbatim for TPqp-GC. Let $x_k$, $t_k$ be
a target sequence up to the horizon $K$, with $0 \le \theta < 1$ and $\varepsilon_0 > 0$. Then:
* the targets decrease strictly: $t_{k+1} < t_k$ for $1 \le k < K$;
* for $1 \le k \le K$: $0 \le f(x_k) - t_k \le \varepsilon_0$ and
  $\|c(x_k)\| \le \varepsilon_0$, by (7.2.26) and (7.2.29);
* for $1 \le k < K$ with $k \in \mathcal{K}_a$: $\|r(x_{k+1}, t_{k+1})\| = \varepsilon_0$ and
  $t_k - t_{k+1} \ge (1 - \theta) \varepsilon_0$, by (7.2.27) and (7.2.30);
* for $1 \le k < K$ with $k \notin \mathcal{K}_a$: $\|r(x_{k+1}, t_{k+1})\| = \|r(x_{k+1},
  t_k)\| \le \varepsilon_0$, by (7.2.28);
* if $\varepsilon_0 \le 1$, then for every set $X$ that contains $x_k$ for $1 \le k \le K$ and
  all $f_{\mathrm{low}}, f_{\mathrm{up}}$ with f.B.Fb
  ($f_{\mathrm{low}} \le f(z) \le f_{\mathrm{up}}$ for $z \in X$ with
  $\|c(z)\| \le \varepsilon_0$), $t_k \in [f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$ for
  $1 \le k \le K$, by (7.2.31). -/
theorem props (h : IsTargetSequence f c θ ε₀ x t Ka K) (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (hε₀ : 0 < ε₀) :
    (∀ k, 1 ≤ k → k < K → t (k + 1) < t k) ∧
    (∀ k, 1 ≤ k → k ≤ K → 0 ≤ f (x k) - t k ∧ f (x k) - t k ≤ ε₀ ∧ ‖c (x k)‖ ≤ ε₀) ∧
    (∀ k, 1 ≤ k → k < K → Ka k →
      targetResidual f c (t (k + 1)) (x (k + 1)) = ε₀ ∧ (1 - θ) * ε₀ ≤ t k - t (k + 1)) ∧
    (∀ k, 1 ≤ k → k < K → ¬ Ka k →
      targetResidual f c (t (k + 1)) (x (k + 1)) = targetResidual f c (t k) (x (k + 1)) ∧
        targetResidual f c (t (k + 1)) (x (k + 1)) ≤ ε₀) ∧
    (ε₀ ≤ 1 → ∀ (X : Set E) (flow fup : ℝ), (∀ k, 1 ≤ k → k ≤ K → x k ∈ X) →
      (∀ z ∈ X, ‖c z‖ ≤ ε₀ → flow ≤ f z ∧ f z ≤ fup) →
      ∀ k, 1 ≤ k → k ≤ K → t k ∈ Set.Icc (flow - 1) fup) :=
  ⟨fun _ hk1 hkK => h.target_succ_lt hθ0 hθ hε₀ hk1 hkK,
    fun _ hk1 hkK => ⟨h.sub_target_nonneg hk1 hkK, h.sub_target_le hθ.le hε₀.le hk1 hkK,
      h.norm_le hθ.le hε₀.le hk1 hkK⟩,
    fun _ hk1 hkK ha => ⟨h.residual_succ_of_Ka hθ.le hε₀.le hk1 hkK ha,
      h.sub_target_succ_ge_of_Ka hθ0 hθ.le hε₀.le hk1 hkK ha⟩,
    fun k hk1 hkK ha => ⟨h.residual_succ_of_not_Ka hk1 hkK ha,
      h.residual_le hθ.le hε₀.le (by omega) (by omega)⟩,
    fun hε₀1 _ _ _ hxX hB _ hk1 hkK => h.target_mem_Icc hθ.le hε₀.le hε₀1 hxX hB hk1 hkK⟩

/-- **Telescoping the targets.** Let $0 \le \theta < 1$, $0 < \varepsilon_0 \le 1$ and $K \ge 1$.
Let $x_k$, $t_k$ be a target sequence up to the horizon $K$. Let $x_k \in X$ for
$1 \le k \le K$, and assume f.B.Fb: $f_{\mathrm{low}} \le f(z) \le f_{\mathrm{up}}$ for every
$z \in X$ with $\|c(z)\| \le \varepsilon_0$. Let $S \subseteq [1, K)$ be a finite set of outer
iterations, each of which lowers the target by at least $\tau$: $t_k - t_{k+1} \ge \tau$ for
$k \in S$. Then
$$|S| \, \tau \le f_{\mathrm{up}} - f_{\mathrm{low}} + 1.$$

The targets do not increase and stay in $[f_{\mathrm{low}} - 1, f_{\mathrm{up}}]$. -/
theorem card_mul_le_of_target_drop (h : IsTargetSequence f c θ ε₀ x t Ka K) (hθ0 : 0 ≤ θ)
    (hθ : θ < 1) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1) (hK : 1 ≤ K) {X : Set E} {flow fup : ℝ}
    (hxX : ∀ k, 1 ≤ k → k ≤ K → x k ∈ X) (hB : ∀ z ∈ X, ‖c z‖ ≤ ε₀ → flow ≤ f z ∧ f z ≤ fup)
    {S : Finset ℕ} (hS : S ⊆ Ico 1 K) {τ : ℝ} (hτ : ∀ k ∈ S, τ ≤ t k - t (k + 1)) :
    S.card * τ ≤ fup - flow + 1 := by
  have h1 : ∑ _k ∈ S, τ ≤ ∑ k ∈ S, (t k - t (k + 1)) := sum_le_sum hτ
  have h2 : ∑ k ∈ S, (t k - t (k + 1)) ≤ ∑ k ∈ Ico 1 K, (t k - t (k + 1)) :=
    sum_le_sum_of_subset_of_nonneg hS fun k hk _ => by
      rw [mem_Ico] at hk
      exact sub_nonneg.2 (h.target_succ_lt hθ0 hθ hε₀ hk.1 hk.2).le
  have htel : ∑ k ∈ Ico 1 K, (t k - t (k + 1)) = t 1 - t K := by
    have := sum_Ico_sub (f := t) hK
    rw [← neg_sub (t K), ← this, ← sum_neg_distrib]
    simp
  rw [sum_const, nsmul_eq_mul] at h1
  rw [htel] at h2
  have ht1 := h.target_mem_Icc hθ.le hε₀.le hε₀1 hxX hB le_rfl hK
  have htK := h.target_mem_Icc hθ.le hε₀.le hε₀1 hxX hB hK le_rfl
  linarith [ht1.2, htK.1]

/-- **Lemma 7.2.4** of [cartis2022evaluation]. Let $x_k$, $t_k$ be a target sequence up to the
horizon $K$. Let $0 \le \theta < 1$, $0 < \varepsilon_0 \le 1$ and $K \ge 1$. Let $x_k \in X$
for $1 \le k \le K$, and assume f.B.Fb: $f_{\mathrm{low}} \le f(z) \le f_{\mathrm{up}}$ for
every $z \in X$ with $\|c(z)\| \le \varepsilon_0$. Then the number of case-(a) iterations among
the outer iterations $k \in [1, K)$ satisfies
$$|\mathcal{K}_a \cap [1, K)| \le \frac{f_{\mathrm{up}} - f_{\mathrm{low}} + 1}{(1 - \theta)
  \varepsilon_0}.$$

The bound $f_{\mathrm{up}} - f_{\mathrm{low}} - 1$ in Theorem 14.3.9 of the source is a sign
slip for $f_{\mathrm{up}} - f_{\mathrm{low}} + 1$. -/
theorem card_Ka_le [DecidablePred Ka] (h : IsTargetSequence f c θ ε₀ x t Ka K) (hθ0 : 0 ≤ θ)
    (hθ : θ < 1) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1) (hK : 1 ≤ K) {X : Set E} {flow fup : ℝ}
    (hxX : ∀ k, 1 ≤ k → k ≤ K → x k ∈ X) (hB : ∀ z ∈ X, ‖c z‖ ≤ ε₀ → flow ≤ f z ∧ f z ≤ fup) :
    (((Ico 1 K).filter Ka).card : ℝ) ≤ (fup - flow + 1) / ((1 - θ) * ε₀) := by
  rw [le_div_iff₀ (mul_pos (sub_pos.2 hθ) hε₀)]
  refine h.card_mul_le_of_target_drop hθ0 hθ hε₀ hε₀1 hK hxX hB (filter_subset _ _) fun k hk => ?_
  rw [mem_filter, mem_Ico] at hk
  exact h.sub_target_succ_ge_of_Ka hθ0 hθ.le hε₀.le hk.1.1 hk.1.2 hk.2

/-- The number of case-(a) iterations in $[1, K + 1)$ is the number in $[1, K)$, plus $1$ if $K$ is
a case-(a) iteration. -/
private theorem card_filter_Ico_succ (Ka : ℕ → Prop) [DecidablePred Ka] {K : ℕ} (hK1 : 1 ≤ K) :
    (((Finset.Ico 1 (K + 1)).filter Ka).card : ℝ) =
      ((Finset.Ico 1 K).filter Ka).card + if Ka K then 1 else 0 := by
  rw [← Nat.succ_eq_add_one, Nat.Ico_succ_right_eq_insert_Ico hK1, Finset.filter_insert]
  split_ifs with ha
  · rw [Finset.card_insert_of_notMem (by simp)]; push_cast; ring
  · simp

/-- **Telescoping over the outer iterations**, the sums behind (7.2.37)–(7.2.39) and
(14.3.69)–(14.3.71) of [cartis2022evaluation]. Let $x_k$, $t_k$ be a target sequence up to the
horizon $K$. Let $\theta \le 1$, $\varepsilon_0 \ge 0$ and $K \ge 1$. Let $a_k = \max(\|r(x_k,
t_k)\|, \theta \varepsilon_0)$ and $b_k = \max(\|r(x_{k+1}, t_k)\|, \theta \varepsilon_0)$. Then
$$\sum_{k=1}^{K} (a_k - b_k) + b_K \le a_1 + (1 - \theta) \varepsilon_0 \, |\mathcal{K}_a \cap
  [1, K)|.$$
-/
theorem sum_max_sub_add_le [DecidablePred Ka] (h : IsTargetSequence f c θ ε₀ x t Ka K)
    (hθ : θ ≤ 1) (hε₀ : 0 ≤ ε₀) (hK1 : 1 ≤ K) :
    ∑ k ∈ Finset.Icc 1 K,
        (max (targetResidual f c (t k) (x k)) (θ * ε₀) -
          max (targetResidual f c (t k) (x (k + 1))) (θ * ε₀)) +
      max (targetResidual f c (t K) (x (K + 1))) (θ * ε₀) ≤
      max (targetResidual f c (t 1) (x 1)) (θ * ε₀) +
        (1 - θ) * ε₀ * ((Finset.Ico 1 K).filter Ka).card := by
  induction K, hK1 using Nat.le_induction with
  | base => simp
  | succ K hK1 ih =>
    have ih := ih (h.mono K.le_succ)
    have hθε : θ * ε₀ ≤ ε₀ := mul_le_of_le_one_left hε₀ hθ
    rw [Finset.sum_Icc_succ_top (by omega), card_filter_Ico_succ Ka hK1]
    have key : max (targetResidual f c (t (K + 1)) (x (K + 1))) (θ * ε₀) -
        max (targetResidual f c (t K) (x (K + 1))) (θ * ε₀) ≤
        (1 - θ) * ε₀ * (if Ka K then 1 else 0) := by
      split_ifs with ha
      · rw [h.residual_succ_of_Ka hθ hε₀ hK1 K.lt_succ_self ha, max_eq_left hθε,
          max_eq_right (h.residual_le_of_Ka K hK1 K.lt_succ_self ha)]
        linarith
      · rw [h.residual_succ_of_not_Ka hK1 K.lt_succ_self ha]
        simp
    linarith

/-- **The outer telescoping bound.** Let $0 \le \theta \le 1$, $\varepsilon_0 \ge 0$ and $K \ge 1$,
and let $a_k$, $b_k$ be as in `Constrained.IsTargetSequence.sum_max_sub_add_le`. Let $x_k$,
$t_k$ be a target sequence up to the horizon $K$. Then
$$\sum_{k=1}^{K} (a_k - b_k) \le (1 - \theta) \varepsilon_0 \big(|\mathcal{K}_a \cap [1, K)| +
  1\big).$$
So the decrease of the residual above $\theta \varepsilon_0$ within the inner runs accumulates
at most $(1 - \theta) \varepsilon_0$ per block between two case-(a) iterations. -/
theorem sum_max_sub_le [DecidablePred Ka] (h : IsTargetSequence f c θ ε₀ x t Ka K)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1) (hε₀ : 0 ≤ ε₀) (hK1 : 1 ≤ K) :
    ∑ k ∈ Finset.Icc 1 K,
        (max (targetResidual f c (t k) (x k)) (θ * ε₀) -
          max (targetResidual f c (t k) (x (k + 1))) (θ * ε₀)) ≤
      (1 - θ) * ε₀ * (((Finset.Ico 1 K).filter Ka).card + 1) := by
  have hs := h.sum_max_sub_add_le hθ hε₀ hK1
  have ha1 : max (targetResidual f c (t 1) (x 1)) (θ * ε₀) ≤ ε₀ :=
    max_le (h.residual_le hθ hε₀ le_rfl hK1) (mul_le_of_le_one_left hε₀ hθ)
  have hbK := le_max_right (targetResidual f c (t K) (x (K + 1))) (θ * ε₀)
  have : 0 ≤ θ * ε₀ := mul_nonneg hθ0 hε₀
  nlinarith

end IsTargetSequence

/-- **Counting the outer iterations**, for Lemmas 7.2.6 and 14.3.8 of [cartis2022evaluation]. Let
$A$ and $B$ be predicates on $\mathbb{N}$ and $g : \mathbb{N} \to \mathbb{N}$. Suppose that
every outer iteration $k \in [1, K)$ is a case-(a) iteration ($A(k)$), a bad iteration ($B(k)$),
or contains at least one counted inner iteration ($g(k) \ge 1$). Then
$$K \le |A \cap [1, K)| + \sum_{k=1}^{K} g(k) + |B \cap [1, K)| + 1.$$
-/
theorem le_card_add_sum_of_cover (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B]
    (g : ℕ → ℕ) {K : ℕ} (hcov : ∀ k ∈ Finset.Ico 1 K, A k ∨ B k ∨ 1 ≤ g k) :
    K ≤ ((Finset.Ico 1 K).filter A).card + ∑ k ∈ Finset.Icc 1 K, g k +
      ((Finset.Ico 1 K).filter B).card + 1 := by
  classical
  have hsub : Finset.Ico 1 K ⊆ ((Finset.Ico 1 K).filter A ∪ (Finset.Ico 1 K).filter B) ∪
      (Finset.Ico 1 K).filter (fun k => 1 ≤ g k) := by
    intro k hk
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases hcov k hk with ha | hb | hg
    · exact Or.inl (Or.inl ⟨hk, ha⟩)
    · exact Or.inl (Or.inr ⟨hk, hb⟩)
    · exact Or.inr ⟨hk, hg⟩
  have hcard := (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hgood : ((Finset.Ico 1 K).filter (fun k => 1 ≤ g k)).card ≤ ∑ k ∈ Finset.Icc 1 K, g k := by
    rw [Finset.card_eq_sum_ones]
    calc ∑ _k ∈ (Finset.Ico 1 K).filter (fun k => 1 ≤ g k), 1
        ≤ ∑ k ∈ (Finset.Ico 1 K).filter (fun k => 1 ≤ g k), g k :=
          Finset.sum_le_sum fun k hk => (Finset.mem_filter.1 hk).2
      _ ≤ ∑ k ∈ Finset.Icc 1 K, g k :=
          Finset.sum_le_sum_of_subset ((Finset.filter_subset _ _).trans
            Finset.Ico_subset_Icc_self)
  rw [Nat.card_Ico] at hcard
  omega


/-! ### Counting inner iterations within a block -/

section Block

/-- Let $\rho : \mathbb{N} \to \mathbb{R}$ satisfy $\rho_{i+1} \le \rho_i$ for all $i < N$. Then
$\rho_j \le \rho_i$ for $i \le j \le N$. -/
theorem antitone_of_succ_le {ρ : ℕ → ℝ} {N : ℕ} (hmono : ∀ i < N, ρ (i + 1) ≤ ρ i) {i j : ℕ}
    (hij : i ≤ j) (hjN : j ≤ N) : ρ j ≤ ρ i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (hmono j (by omega)).trans (ih (by omega))

/-- **The decrease of one good iteration** in the block argument of Lemmas 7.2.6 and 14.3.8 of
[cartis2022evaluation] (Appendix B, proof of Lemma 14.3.8). Let $\theta \varepsilon_0 \le \rho'
\le \rho \le \varepsilon_0$, $0 \le \pi \le \pi_{\max}$, $0 < \theta \le 1$,
$\varepsilon_0 > 0$, $\kappa > 0$ and $e > 0$, and suppose $\kappa (\rho' e)^\pi \le \rho^2 /
2 - \rho'^2 / 2$. Then
$$\rho - \rho' \ge \kappa \, \theta^{\pi_{\max}} \varepsilon_0^{\pi - 1} e^\pi.$$

Indeed $(\rho - \rho') \rho \ge \frac12 (\rho^2 - \rho'^2) \ge \kappa (\theta \varepsilon_0
e)^\pi$ and $\rho \le \varepsilon_0$. -/
theorem sub_ge_of_residual_decrease {ρ ρ' θ ε₀ κ π πmax e : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hε₀ : 0 < ε₀) (hκ : 0 < κ) (hπ : 0 ≤ π) (hπmax : π ≤ πmax) (he : 0 < e)
    (hlow : θ * ε₀ ≤ ρ') (hρρ' : ρ' ≤ ρ) (hρ : ρ ≤ ε₀)
    (hdec : κ * (ρ' * e) ^ π ≤ ρ ^ 2 / 2 - ρ' ^ 2 / 2) :
    κ * θ ^ πmax * (ε₀ ^ (π - 1) * e ^ π) ≤ ρ - ρ' := by
  have hρ'0 : 0 < ρ' := lt_of_lt_of_le (mul_pos hθ0 hε₀) hlow
  have hρ0 : 0 < ρ := hρ'0.trans_le hρρ'
  -- `(ρ - ρ') ρ ≥ ρ²/2 - ρ'²/2 ≥ κ (θ ε₀ e)^π`
  have h1 : κ * (ρ' * e) ^ π ≤ (ρ - ρ') * ρ := by nlinarith
  have h2 : (θ * ε₀ * e) ^ π ≤ (ρ' * e) ^ π :=
    Real.rpow_le_rpow (by positivity) (by gcongr) hπ
  -- `(θ ε₀ e)^π = θ^π ε₀^{π-1} e^π ε₀`
  have h3 : (θ * ε₀ * e) ^ π = θ ^ π * (ε₀ ^ (π - 1) * e ^ π) * ε₀ := by
    rw [Real.mul_rpow (by positivity) he.le, Real.mul_rpow hθ0.le hε₀.le,
      Real.rpow_sub_one hε₀.ne']
    field_simp
  have h4 : θ ^ πmax ≤ θ ^ π := Real.rpow_le_rpow_of_exponent_ge hθ0 hθ1 hπmax
  have hA : 0 ≤ ε₀ ^ (π - 1) * e ^ π := by positivity
  have hsub : 0 ≤ ρ - ρ' := sub_nonneg.2 hρρ'
  have h5 : κ * θ ^ π * (ε₀ ^ (π - 1) * e ^ π) * ε₀ ≤ (ρ - ρ') * ε₀ := by
    calc κ * θ ^ π * (ε₀ ^ (π - 1) * e ^ π) * ε₀ = κ * (θ * ε₀ * e) ^ π := by rw [h3]; ring
      _ ≤ κ * (ρ' * e) ^ π := by gcongr
      _ ≤ (ρ - ρ') * ρ := h1
      _ ≤ (ρ - ρ') * ε₀ := mul_le_mul_of_nonneg_left hρ hsub
  calc κ * θ ^ πmax * (ε₀ ^ (π - 1) * e ^ π) ≤ κ * θ ^ π * (ε₀ ^ (π - 1) * e ^ π) := by gcongr
    _ ≤ ρ - ρ' := le_of_mul_le_mul_right h5 hε₀

/-- Let $\varepsilon_0 > 0$ and $e > 0$, and let $\varepsilon_0^{2 - \pi} e^{-\pi} \le M$. Then
$\varepsilon_0^{\pi - 1} e^\pi \ge \varepsilon_0 / M$. -/
theorem div_le_rpow_mul_rpow {ε₀ e π M : ℝ} (hε₀ : 0 < ε₀) (he : 0 < e)
    (hM : ε₀ ^ (2 - π) * e ^ (-π) ≤ M) : ε₀ / M ≤ ε₀ ^ (π - 1) * e ^ π := by
  have hQ : 0 < ε₀ ^ (2 - π) * e ^ (-π) := by positivity
  have hprod : ε₀ ^ (π - 1) * e ^ π * (ε₀ ^ (2 - π) * e ^ (-π)) = ε₀ := by
    calc ε₀ ^ (π - 1) * e ^ π * (ε₀ ^ (2 - π) * e ^ (-π))
        = ε₀ ^ ((π - 1) + (2 - π)) * e ^ (π + -π) := by
          rw [Real.rpow_add hε₀, Real.rpow_add he]; ring
      _ = ε₀ := by norm_num
  calc ε₀ / M ≤ ε₀ / (ε₀ ^ (2 - π) * e ^ (-π)) := div_le_div_of_nonneg_left hε₀.le hQ hM
    _ = ε₀ ^ (π - 1) * e ^ π := by rw [div_eq_iff hQ.ne', hprod]

/-- **The decrease of one good iteration** in the form of (14.2.11), from the proof of Lemma 14.3.8
of [cartis2022evaluation], (B.14.20)–(B.14.21). Here the merit decrease is measured with the
residual $r$ at the start of the inner call: $\kappa (\beta r \varepsilon)^\pi \le \rho^2 / 2 -
\rho'^2 / 2$. Let $\theta \varepsilon_0 \le r \le \varepsilon_0$, $\rho' \le \rho \le r$,
$\beta > 0$, $\theta > 0$, $\beta \theta \le 1$, $\varepsilon_0 > 0$,
$0 \le \pi \le \pi_{\max}$, $\kappa > 0$, $\varepsilon > 0$, $M > 0$ and $\varepsilon_0^{2 -
\pi} \varepsilon^{-\pi} \le M$. Then
$$\rho - \rho' \ge \frac{\kappa (\beta \theta)^{\pi_{\max}} \varepsilon_0}{M}.$$

The merit decrease is at least $\kappa (\beta \theta)^{\pi_{\max}} \varepsilon_0^2 / M$, and
$\rho + \rho' \le 2 \varepsilon_0$. -/
theorem sub_ge_of_merit_decrease {ρ ρ' r β θ ε₀ κ π πmax ε M : ℝ} (hβ : 0 < β) (hθ : 0 < θ)
    (hβθ : β * θ ≤ 1) (hε₀ : 0 < ε₀) (hκ : 0 < κ) (hπ : 0 ≤ π) (hπmax : π ≤ πmax) (hε : 0 < ε)
    (hM0 : 0 < M) (hM : ε₀ ^ (2 - π) * ε ^ (-π) ≤ M) (hr_ge : θ * ε₀ ≤ r) (hr_le : r ≤ ε₀)
    (hρr : ρ ≤ r) (hρ'ρ : ρ' ≤ ρ)
    (hdec : κ * (β * r * ε) ^ π ≤ ρ ^ 2 / 2 - ρ' ^ 2 / 2) :
    κ * (β * θ) ^ πmax * ε₀ / M ≤ ρ - ρ' := by
  have hbase : (β * θ * (ε₀ * ε)) ^ π ≤ (β * r * ε) ^ π := by
    refine Real.rpow_le_rpow (by positivity) ?_ hπ
    have : β * (θ * ε₀) * ε ≤ β * r * ε := by gcongr
    linarith
  have hpow : (β * θ) ^ πmax ≤ (β * θ) ^ π :=
    Real.rpow_le_rpow_of_exponent_ge (by positivity) hβθ hπmax
  have hεε : ε₀ ^ 2 / M ≤ (ε₀ * ε) ^ π := by
    rw [div_le_iff₀ hM0]
    have e : (ε₀ * ε) ^ π * (ε₀ ^ (2 - π) * ε ^ (-π)) = ε₀ ^ 2 := by
      rw [Real.mul_rpow hε₀.le hε.le, Real.rpow_sub hε₀, Real.rpow_neg hε.le]
      have : (0 : ℝ) < ε₀ ^ π := Real.rpow_pos_of_pos hε₀ _
      have : (0 : ℝ) < ε ^ π := Real.rpow_pos_of_pos hε _
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
    calc ε₀ ^ 2 = (ε₀ * ε) ^ π * (ε₀ ^ (2 - π) * ε ^ (-π)) := e.symm
      _ ≤ (ε₀ * ε) ^ π * M := by gcongr
  have hDmin : κ * (β * θ) ^ πmax * (ε₀ ^ 2 / M) ≤ ρ ^ 2 / 2 - ρ' ^ 2 / 2 := by
    refine le_trans ?_ hdec
    rw [Real.mul_rpow (by positivity) (by positivity)] at hbase
    calc κ * (β * θ) ^ πmax * (ε₀ ^ 2 / M)
        ≤ κ * ((β * θ) ^ π * (ε₀ * ε) ^ π) := by
          rw [mul_assoc]
          gcongr
      _ ≤ κ * (β * r * ε) ^ π := by gcongr
  have hsum_le : ρ + ρ' ≤ 2 * ε₀ := by linarith
  have hgd : κ * (β * θ) ^ πmax * ε₀ / M = κ * (β * θ) ^ πmax * (ε₀ ^ 2 / M) / ε₀ := by
    field_simp
  rw [hgd, div_le_iff₀ hε₀]
  have hd0 : 0 ≤ ρ - ρ' := sub_nonneg.2 hρ'ρ
  nlinarith [mul_le_mul_of_nonneg_left hsum_le hd0]

/-- **Counting good inner iterations in a block**, the telescoping argument of Lemmas 7.2.6 and
14.3.8 of [cartis2022evaluation]. Let $0 < \theta \le 1$, $\varepsilon_0 > 0$ and $\kappa > 0$.
Let $\rho : \mathbb{N} \to \mathbb{R}$ (the residuals $\|r(x_{j,i}, t_j)\|$ of the inner
iterates of a block, concatenated) be nonincreasing on $[0, N]$, with $\rho_0 \le \varepsilon_0$
and $\rho_N \ge \theta \varepsilon_0$. Let $L$ be a nonempty finite set of criticality orders,
with $0 \le \pi_l \le \pi_{\max}$, $\varepsilon_l > 0$ and $\varepsilon_0^{2 - \pi_l}
\varepsilon_l^{-\pi_l} \le M$ for every $l \in L$. Let $T \subseteq [0, N)$ be a set of
iterations such that for every $i \in T$ there is $l \in L$ with
$$\kappa (\rho_{i+1} \varepsilon_l)^{\pi_l} \le \rho_i^2 / 2 - \rho_{i+1}^2 / 2,$$
which is the merit decrease $\mu(x_{j,i}) - \mu(x_{j,i+1})$ that the inner method guarantees at
a successful iteration whose new iterate fails the criticality test. Then
$$|T| \le \frac{1 - \theta}{\kappa \theta^{\pi_{\max}}} M.$$

Only the iterations of $T$ are counted. The entries with $i = 0$ of the set $\mathcal{I}_k^s$ of
successful inner iterations, and the last successful iteration of case-(b) calls that end on the
criticality test, are counted separately. For TPp-GC ($L = \{1\}$, $\pi = (p+1)/p$,
$\kappa = \kappa_1$) the constant is $\kappa_1^{-1} \theta^{-(p+1)/p}$. For TPqp-GC ($\kappa =
\kappa^\mu_{\mathrm{decr}} \beta^{\pi_{\max}}$) it is $[\kappa^\mu_{\mathrm{decr}}]^{-1} (\beta
\theta)^{-\pi_{\max}}$, as in (14.3.71). The proof uses $\rho_{i+1}^\pi / \rho_i \ge (\theta
\varepsilon_0)^\pi / \varepsilon_0$; no ratio condition $\rho_{i+1} \ge \theta \rho_i$ is
needed. -/
theorem card_le_of_residual_block {ι : Type*} {ρ : ℕ → ℝ} {N : ℕ} {T : Finset ℕ} {L : Finset ι}
    {π ε : ι → ℝ} {θ ε₀ κ πmax M : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hε₀ : 0 < ε₀) (hκ : 0 < κ)
    (hL : L.Nonempty) (hπ : ∀ l ∈ L, 0 ≤ π l ∧ π l ≤ πmax) (hε : ∀ l ∈ L, 0 < ε l)
    (hM : ∀ l ∈ L, ε₀ ^ (2 - π l) * ε l ^ (-π l) ≤ M)
    (hT : T ⊆ range N) (hmono : ∀ i < N, ρ (i + 1) ≤ ρ i) (h0 : ρ 0 ≤ ε₀) (hN : θ * ε₀ ≤ ρ N)
    (hdec : ∀ i ∈ T, ∃ l ∈ L, κ * (ρ (i + 1) * ε l) ^ π l ≤ ρ i ^ 2 / 2 - ρ (i + 1) ^ 2 / 2) :
    (T.card : ℝ) ≤ (1 - θ) / (κ * θ ^ πmax) * M := by
  obtain ⟨l₀, hl₀⟩ := hL
  have hM0 : 0 < M := lt_of_lt_of_le (by have := hε l₀ hl₀; positivity) (hM l₀ hl₀)
  have hθp : 0 < θ ^ πmax := Real.rpow_pos_of_pos hθ0 _
  set δ := κ * θ ^ πmax * (ε₀ / M) with hδ
  have hδ0 : 0 < δ := by positivity
  -- every iteration of `T` decreases `ρ` by at least `δ`
  have hstep : ∀ i ∈ T, δ ≤ ρ i - ρ (i + 1) := by
    intro i hi
    have hiN : i < N := mem_range.1 (hT hi)
    obtain ⟨l, hl, hdl⟩ := hdec i hi
    have hlow : θ * ε₀ ≤ ρ (i + 1) := hN.trans (antitone_of_succ_le hmono (by omega) le_rfl)
    have hρi : ρ i ≤ ε₀ := (antitone_of_succ_le hmono (Nat.zero_le i) hiN.le).trans h0
    have key := sub_ge_of_residual_decrease hθ0 hθ1 hε₀ hκ (hπ l hl).1
      (hπ l hl).2 (hε l hl) hlow (hmono i hiN) hρi hdl
    have hq := div_le_rpow_mul_rpow hε₀ (hε l hl) (hM l hl)
    calc δ ≤ κ * θ ^ πmax * (ε₀ ^ (π l - 1) * ε l ^ π l) := by
          rw [hδ]; gcongr
      _ ≤ ρ i - ρ (i + 1) := key
  -- telescoping
  have hsum : ∑ i ∈ T, (ρ i - ρ (i + 1)) ≤ ρ 0 - ρ N := by
    rw [← sum_range_sub' ρ N]
    exact sum_le_sum_of_subset_of_nonneg hT fun i hi _ =>
      sub_nonneg.2 (hmono i (mem_range.1 hi))
  have hcard : T.card * δ ≤ (1 - θ) * ε₀ := by
    have : ∑ _i ∈ T, δ ≤ ∑ i ∈ T, (ρ i - ρ (i + 1)) := sum_le_sum hstep
    rw [sum_const, nsmul_eq_mul] at this
    linarith
  rw [← le_div_iff₀ hδ0] at hcard
  refine hcard.trans (le_of_eq ?_)
  rw [hδ]
  field_simp

end Block

end Constrained
