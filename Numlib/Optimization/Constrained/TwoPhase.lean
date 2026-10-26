import Numlib.Optimization.Constrained.TargetResidual
import Numlib.Optimization.Complexity.Telescoping

/-!
# Outer bookkeeping of the two-phase target-following methods

The two-phase methods TPp-GC (Algorithm 7.2.1) and TPqp-GC (Algorithm 14.3.2) of
[cartis2022evaluation] for `min f(x)` subject to `x ∈ 𝒳`, `c(x) = 0` first find an approximately
feasible point `x₁` (`‖c(x₁)‖ ≤ θε₀`), then follow a decreasing sequence of targets `t_k`: at outer
iteration `k` an inner method decreases the residual `‖r(x, t_k)‖` (`Constrained.targetResidual`)
from `x_k` to `x_{k+1}`, and the target is reset either by (7.2.11) (case (a), the residual became
small) or by the reflection (7.2.13) (case (b), `f(x_{k+1}) < t_k`). This file records this
bookkeeping, independently of the inner method, and proves the properties of the targets
(Lemmas 7.2.3 and 7.2.4, used verbatim for TPqp-GC) and the counting of inner iterations within a
block of outer iterations (the telescoping argument of Lemmas 7.2.6 and 14.3.8).

## Main definitions

* `Constrained.IsTargetSequence f c θ ε₀ x t Ka K`: outer iterates `x`, targets `t` and the set
  `Ka` of case-(a) iterations satisfy Steps 0 and 2 of Phase 2 for the outer iterations
  `k ∈ [1, K)`.

## Main results

* `Constrained.IsTargetSequence.props`: Lemma 7.2.3 ((7.2.26)–(7.2.31));
* `Constrained.IsTargetSequence.card_Ka_le`: Lemma 7.2.4, `|𝒦_a| ≤ (f_up - f_low + 1)/((1-θ)ε₀)`;
* `Constrained.card_le_of_residual_block`: the number of "good" successful inner iterations
  between two consecutive case-(a) iterations is `O((1-θ) max_l ε₀^{2-π_l} ε_l^{-π_l})`
  (Lemmas 7.2.6 and 14.3.8).

## Implementation notes

Step 2(a) of Algorithm 7.2.1 is printed with `‖r(x_{k+1}, t_k)‖ < θε₀`, while the inner stopping
test (7.2.10) uses `≤ θε₀`; with `<`, an inner run stopped at `‖r‖ = θε₀` exactly may end in
Step 2(c) without the guarantees of Lemma 7.2.1. Algorithm 14.3.2 uses `<` in both places. The
predicate `Ka` is left as a parameter constrained only by the two cases: case (a) (`Ka k`) needs
`‖r(x_{k+1}, t_k)‖ ≤ θε₀`, case (b) (`¬ Ka k`) needs `‖r(x_{k+1}, t_k)‖ ≥ θε₀` and
`f(x_{k+1}) < t_k`. This covers both the corrected `≤` (Chapter 7) and the printed `<`
(Chapter 14) variants. The terminating case (c) does not occur before the horizon `K`.

The printed proofs of Lemmas 7.2.6 and 14.3.8 bound only the successful inner iterations whose
new iterate fails the third (approximate criticality) stopping test; the number of case-(b) outer
iterations whose inner run stops on that test is never bounded in the book. The counting lemma
`Constrained.card_le_of_residual_block` therefore bounds a given set `T` of such "good"
iterations only; the remaining elements of the book's `𝓘_k^s` (the `i = 0` entries, and the last
successful iteration of case-(b) calls ending on the criticality test) must be counted separately
by the caller.
-/

open Finset
open scoped Topology

namespace Constrained

variable {E F : Type*} [NormedAddCommGroup F]

/-- **Outer bookkeeping of Phase 2** of TPp-GC (Algorithm 7.2.1) and TPqp-GC (Algorithm 14.3.2)
of [cartis2022evaluation]. For outer iterates `x`, targets `t`, a horizon `K` and the set `Ka` of
case-(a) iterations (the book's `𝒦_a`, (7.2.25), (14.3.36)):
* Step 0: `‖c(x₁)‖ ≤ θε₀` (Phase 1 did not terminate) and `t₁ = f(x₁) - √(ε₀² - ‖c(x₁)‖²)`;
* Step 1, for `1 ≤ k < K`: the inner method does not increase the residual,
  `‖r(x_{k+1}, t_k)‖ ≤ ‖r(x_k, t_k)‖`;
* Step 2(a), for `1 ≤ k < K` with `Ka k`: `‖r(x_{k+1}, t_k)‖ ≤ θε₀` and
  `t_{k+1} = f(x_{k+1}) - √(ε₀² - ‖c(x_{k+1})‖²)` (7.2.11);
* Step 2(b), for `1 ≤ k < K` with `¬ Ka k`: `‖r(x_{k+1}, t_k)‖ ≥ θε₀`, `f(x_{k+1}) < t_k` and
  `t_{k+1} = 2 f(x_{k+1}) - t_k` (7.2.13).
Algorithm 7.2.1 with the corrected Step 2(a) takes `Ka k ↔ ‖r(x_{k+1}, t_k)‖ ≤ θε₀`;
Algorithm 14.3.2 takes `Ka k ↔ ‖r(x_{k+1}, t_k)‖ < θε₀`. -/
structure IsTargetSequence (f : E → ℝ) (c : E → F) (θ ε₀ : ℝ) (x : ℕ → E) (t : ℕ → ℝ)
    (Ka : ℕ → Prop) (K : ℕ) : Prop where
  /-- Phase 1 ended with `‖c(x₁)‖ ≤ θε₀`. -/
  norm_one_le : ‖c (x 1)‖ ≤ θ * ε₀
  /-- Step 0: `t₁ = f(x₁) - √(ε₀² - ‖c(x₁)‖²)`. -/
  target_one : t 1 = f (x 1) - √(ε₀ ^ 2 - ‖c (x 1)‖ ^ 2)
  /-- Step 1: the inner method does not increase the residual. -/
  residual_succ_le : ∀ k, 1 ≤ k → k < K →
    targetResidual f c (t k) (x (k + 1)) ≤ targetResidual f c (t k) (x k)
  /-- Step 2(a) is entered only when `‖r(x_{k+1}, t_k)‖ ≤ θε₀`. -/
  residual_le_of_Ka : ∀ k, 1 ≤ k → k < K → Ka k → targetResidual f c (t k) (x (k + 1)) ≤ θ * ε₀
  /-- Step 2(a): the target update (7.2.11). -/
  target_succ_of_Ka : ∀ k, 1 ≤ k → k < K → Ka k →
    t (k + 1) = f (x (k + 1)) - √(ε₀ ^ 2 - ‖c (x (k + 1))‖ ^ 2)
  /-- Step 2(b) is entered only when `‖r(x_{k+1}, t_k)‖ ≥ θε₀`. -/
  le_residual_of_not_Ka : ∀ k, 1 ≤ k → k < K → ¬ Ka k →
    θ * ε₀ ≤ targetResidual f c (t k) (x (k + 1))
  /-- Step 2(b) is entered only when `f(x_{k+1}) < t_k`. -/
  lt_target_of_not_Ka : ∀ k, 1 ≤ k → k < K → ¬ Ka k → f (x (k + 1)) < t k
  /-- Step 2(b): the target update (7.2.13). -/
  target_succ_of_not_Ka : ∀ k, 1 ≤ k → k < K → ¬ Ka k → t (k + 1) = 2 * f (x (k + 1)) - t k

namespace IsTargetSequence

variable {f : E → ℝ} {c : E → F} {θ ε₀ : ℝ} {x : ℕ → E} {t : ℕ → ℝ} {Ka : ℕ → Prop} {K : ℕ}
  {k : ℕ}

/-- A target sequence up to `K` is one up to any earlier horizon. -/
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

/-- `f(x_k) ≥ t_k` for `1 ≤ k ≤ K` ([cartis2022evaluation], (7.2.26)). -/
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

/-- After a case-(a) iteration the residual is reset to `ε₀` ([cartis2022evaluation], (7.2.27)). -/
theorem residual_succ_of_Ka (h : IsTargetSequence f c θ ε₀ x t Ka K) (hθ : θ ≤ 1)
    (hε₀ : 0 ≤ ε₀) (hk1 : 1 ≤ k) (hkK : k < K) (ha : Ka k) :
    targetResidual f c (t (k + 1)) (x (k + 1)) = ε₀ := by
  rw [h.target_succ_of_Ka k hk1 hkK ha]
  refine targetResidual_sub_sqrt hε₀ ?_
  calc ‖c (x (k + 1))‖ ≤ targetResidual f c (t k) (x (k + 1)) := norm_le_targetResidual
    _ ≤ θ * ε₀ := h.residual_le_of_Ka k hk1 hkK ha
    _ ≤ ε₀ := mul_le_of_le_one_left hε₀ hθ

/-- After a case-(b) iteration the residual is unchanged by the target update
([cartis2022evaluation], (7.2.28), (7.2.41)). -/
theorem residual_succ_of_not_Ka (h : IsTargetSequence f c θ ε₀ x t Ka K) (hk1 : 1 ≤ k)
    (hkK : k < K) (ha : ¬ Ka k) :
    targetResidual f c (t (k + 1)) (x (k + 1)) = targetResidual f c (t k) (x (k + 1)) := by
  rw [h.target_succ_of_not_Ka k hk1 hkK ha, targetResidual_two_mul_sub]

/-- The residual `‖r(x_k, t_k)‖` is at most `ε₀` for `1 ≤ k ≤ K` ([cartis2022evaluation],
(7.2.27)–(7.2.28)). -/
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

/-- `‖c(x_k)‖ ≤ ε₀` for `1 ≤ k ≤ K` ([cartis2022evaluation], (7.2.29)). -/
theorem norm_le (h : IsTargetSequence f c θ ε₀ x t Ka K) (hθ : θ ≤ 1) (hε₀ : 0 ≤ ε₀)
    (hk1 : 1 ≤ k) (hkK : k ≤ K) : ‖c (x k)‖ ≤ ε₀ :=
  norm_le_targetResidual.trans (h.residual_le hθ hε₀ hk1 hkK)

/-- `f(x_k) - t_k ≤ ε₀` for `1 ≤ k ≤ K` ([cartis2022evaluation], (7.2.29)). -/
theorem sub_target_le (h : IsTargetSequence f c θ ε₀ x t Ka K) (hθ : θ ≤ 1) (hε₀ : 0 ≤ ε₀)
    (hk1 : 1 ≤ k) (hkK : k ≤ K) : f (x k) - t k ≤ ε₀ :=
  sub_le_targetResidual.trans (h.residual_le hθ hε₀ hk1 hkK)

/-- A case-(a) iteration decreases the target by at least `(1 - θ)ε₀` ([cartis2022evaluation],
(7.2.30), via Lemma B.7.1). -/
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

/-- The targets decrease strictly ([cartis2022evaluation], Lemma 7.2.3). -/
theorem target_succ_lt (h : IsTargetSequence f c θ ε₀ x t Ka K) (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (hε₀ : 0 < ε₀) (hk1 : 1 ≤ k) (hkK : k < K) : t (k + 1) < t k := by
  by_cases ha : Ka k
  · have := h.sub_target_succ_ge_of_Ka hθ0 hθ.le hε₀.le hk1 hkK ha
    nlinarith
  · rw [h.target_succ_of_not_Ka k hk1 hkK ha]
    linarith [h.lt_target_of_not_Ka k hk1 hkK ha]

/-- The targets are nonincreasing on `[1, K]`. -/
theorem target_le_of_le (h : IsTargetSequence f c θ ε₀ x t Ka K) (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (hε₀ : 0 < ε₀) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hjK : j ≤ K) : t j ≤ t i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (h.target_succ_lt hθ0 hθ hε₀ (hi.trans hij) (by omega)).le.trans (ih (by omega))

/-- Under f.B.Fb (`f_low ≤ f ≤ f_up` on the points of `X` with `‖c‖ ≤ ε₀`) and `ε₀ ≤ 1`, the
targets stay in `[f_low - 1, f_up]` ([cartis2022evaluation], (7.2.31)). -/
theorem target_mem_Icc (h : IsTargetSequence f c θ ε₀ x t Ka K) (hθ : θ ≤ 1) (hε₀ : 0 ≤ ε₀)
    (hε₀1 : ε₀ ≤ 1) {X : Set E} {flow fup : ℝ} (hxX : ∀ k, 1 ≤ k → k ≤ K → x k ∈ X)
    (hB : ∀ z ∈ X, ‖c z‖ ≤ ε₀ → flow ≤ f z ∧ f z ≤ fup) (hk1 : 1 ≤ k) (hkK : k ≤ K) :
    t k ∈ Set.Icc (flow - 1) fup := by
  have hb := hB (x k) (hxX k hk1 hkK) (h.norm_le hθ hε₀ hk1 hkK)
  have h1 := h.sub_target_nonneg hk1 hkK
  have h2 := h.sub_target_le hθ hε₀ hk1 hkK
  constructor <;> linarith [hb.1, hb.2]

/-- **Lemma 7.2.3** of [cartis2022evaluation] (valid verbatim for TPqp-GC). For a target
sequence with `0 ≤ θ < 1` and `ε₀ > 0`: the targets decrease strictly on `[1, K]`; for
`1 ≤ k ≤ K`, `0 ≤ f(x_k) - t_k ≤ ε₀` and `‖c(x_k)‖ ≤ ε₀` ((7.2.26), (7.2.29)); for `1 ≤ k < K`,
`‖r(x_{k+1}, t_{k+1})‖ = ε₀` and `t_k - t_{k+1} ≥ (1-θ)ε₀` if `k ∈ 𝒦_a` ((7.2.27), (7.2.30)),
`‖r(x_{k+1}, t_{k+1})‖ = ‖r(x_{k+1}, t_k)‖ ≤ ε₀` otherwise ((7.2.28)); and, under f.B.Fb with
`ε₀ ≤ 1`, `t_k ∈ [f_low - 1, f_up]` ((7.2.31)). -/
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

/-- **Lemma 7.2.4** of [cartis2022evaluation]: under f.B.Fb (`f_low ≤ f ≤ f_up` on the points
of `X` with `‖c‖ ≤ ε₀`), `0 ≤ θ < 1` and `0 < ε₀ ≤ 1`, the number of case-(a) iterations among
the outer iterations `k ∈ [1, K)` is at most `(f_up - f_low + 1)/((1 - θ)ε₀)`. (Theorem 14.3.9's
`f_up - f_low - 1` is a sign slip for this `+ 1`.) -/
theorem card_Ka_le [DecidablePred Ka] (h : IsTargetSequence f c θ ε₀ x t Ka K) (hθ0 : 0 ≤ θ)
    (hθ : θ < 1) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1) (hK : 1 ≤ K) {X : Set E} {flow fup : ℝ}
    (hxX : ∀ k, 1 ≤ k → k ≤ K → x k ∈ X) (hB : ∀ z ∈ X, ‖c z‖ ≤ ε₀ → flow ≤ f z ∧ f z ≤ fup) :
    (((Ico 1 K).filter Ka).card : ℝ) ≤ (fup - flow + 1) / ((1 - θ) * ε₀) := by
  have hc : 0 < (1 - θ) * ε₀ := mul_pos (sub_pos.2 hθ) hε₀
  rw [le_div_iff₀ hc, mul_comm]
  have h1 : ∑ _k ∈ (Ico 1 K).filter Ka, (1 - θ) * ε₀ ≤
      ∑ k ∈ (Ico 1 K).filter Ka, (t k - t (k + 1)) := by
    refine sum_le_sum fun k hk => ?_
    rw [mem_filter, mem_Ico] at hk
    exact h.sub_target_succ_ge_of_Ka hθ0 hθ.le hε₀.le hk.1.1 hk.1.2 hk.2
  have h2 : ∑ k ∈ (Ico 1 K).filter Ka, (t k - t (k + 1)) ≤ ∑ k ∈ Ico 1 K, (t k - t (k + 1)) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k hk _ => by
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

end IsTargetSequence

/-! ### Counting inner iterations within a block -/

section Block

/-- A sequence that is nonincreasing at every step before `N` is antitone on `[0, N]`. -/
theorem antitone_of_succ_le {ρ : ℕ → ℝ} {N : ℕ} (hmono : ∀ i < N, ρ (i + 1) ≤ ρ i) {i j : ℕ}
    (hij : i ≤ j) (hjN : j ≤ N) : ρ j ≤ ρ i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (hmono j (by omega)).trans (ih (by omega))

/-- The decrease of one "good" iteration in the block argument of [cartis2022evaluation],
Lemmas 7.2.6 and 14.3.8 (Appendix B, proof of Lemma 14.3.8). If `θ ε₀ ≤ ρ' ≤ ρ ≤ ε₀`,
`0 ≤ π ≤ π_max`, `0 < θ ≤ 1`, `e > 0`, and `κ (ρ' e)^π ≤ ρ²/2 - ρ'²/2`, then
`ρ - ρ' ≥ κ θ^{π_max} ε₀^{π-1} e^π`: indeed `(ρ - ρ') ρ ≥ ½ (ρ² - ρ'²) ≥ κ (θ ε₀ e)^π` and
`ρ ≤ ε₀`. -/
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

/-- `ε₀^{π-1} e^π ≥ ε₀ / M` whenever `ε₀^{2-π} e^{-π} ≤ M`. -/
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

/-- **Counting "good" inner iterations in a block** (the telescoping argument of
[cartis2022evaluation], Lemmas 7.2.6 and 14.3.8). Let `ρ` (the residuals `‖r(x_{j,i}, t_j)‖` of
the inner iterates of a block, concatenated) be nonincreasing on `[0, N]` with `ρ_0 ≤ ε₀` and
`ρ_N ≥ θ ε₀` (`0 < θ ≤ 1`, `ε₀ > 0`), and let `T ⊆ [0, N)` be a set of iterations at which, for
some `l ∈ L` (the criticality orders), `ρ_i²/2 - ρ_{i+1}²/2 ≥ κ (ρ_{i+1} ε_l)^{π_l}` (the merit
decrease `μ(x_{j,i}) - μ(x_{j,i+1})` guaranteed by the inner method at a successful iteration
whose new iterate fails the criticality test), with `κ > 0`, `0 ≤ π_l ≤ π_max`, `ε_l > 0`. If
`ε₀^{2-π_l} ε_l^{-π_l} ≤ M` for every `l ∈ L`, then `|T| ≤ (1 - θ) M / (κ θ^{π_max})`.

Only the iterations of `T` are counted: the book's `|𝓘_k^s|` also contains the `i = 0` entries
and the last successful iteration of case-(b) calls that end on the criticality test, which must be
counted separately. For TPp-GC (`L = {1}`, `π = (p+1)/p`, `κ = κ₁`) the constant is
`κ₁⁻¹ θ^{-(p+1)/p}`, sharper than the book's `κ₁⁻¹ θ^{-(p+2)/p}` (7.2.47); for TPqp-GC
(`κ = κ^μ_decr β^{π_max}`) it is the book's `[κ^μ_decr]⁻¹ (βθ)^{-π_max}` of (14.3.71). The
book's proof bounds `‖r(x_{j,s})‖^{π_l-1}` from below by `ε₀^{π_l-1}`, which is invalid
(only `(θε₀)^{π_l-1}` is available, (B.14.20)), but the constant is correct, via
`ρ_{i+1}^π / ρ_i ≥ (θε₀)^π / ε₀`; the ratio condition `ρ_{i+1} ≥ θ ρ_i` is not needed. -/
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
