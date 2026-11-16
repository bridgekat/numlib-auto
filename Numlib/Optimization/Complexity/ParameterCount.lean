/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Complexity.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Bounding all iterations by the successful ones

Trust-region and adaptive-regularization methods update a positive parameter multiplicatively: the
regularization weight $\sigma_k$, or the inverse radius $1/\Delta_k$. The parameter changes by a
factor of at least $\gamma_S \in (0, 1]$ at a successful iteration and by a factor of at least
$\gamma_U > 1$ at an unsuccessful one, and it does not decrease at the remaining ("neutral")
iterations, for example the iterations that improve the accuracy. If the parameter stays bounded
above, then the number of unsuccessful iterations is bounded in terms of the number of successful
ones. This is the mechanism of Lemmas 2.3.1, 2.4.1, 13.1.1 and 13.1.9 of [cartis2022evaluation],
which every later chapter of that book uses.

Below, $\mathcal{S}_k$ and $\mathcal{U}_k$ are the sets of iterations $j \in \{0, \dots, k\}$ that
satisfy the predicate $\mathrm{succ}$ and the predicate $\mathrm{fail}$, respectively. The general
statements require neither that the two predicates are complementary nor that they are disjoint. The
neutral iterations are those that satisfy neither predicate.

## Main results

* `Optimization.mul_pow_card_le`: $\sigma_0 \gamma_S^{|\mathcal{S}_k|} \gamma_U^{|\mathcal{U}_k|}
  \le \sigma_{k+1}$.
* `Optimization.card_fail_mul_log_le`: if $\sigma_{k+1} \le \sigma_{\max}$, then $|\mathcal{U}_k|
  \log \gamma_U \le \log(\sigma_{\max}/\sigma_0) + |\mathcal{S}_k| \, |\log \gamma_S|$.
* `Optimization.card_fail_le_of_lower_ratio`: the same bound, divided by $\log \gamma_U > 0$.
* `Optimization.succ_le_card_successSet_of_lower_ratio`: if every iteration that is not successful
  is unsuccessful, then $k + 1 \le |\mathcal{S}_k| (1 + |\log \gamma_S| / \log \gamma_U) +
  \log(\sigma_{\max}/\sigma_0) / \log \gamma_U$.
* `Optimization.le_card_successSet_of_lower_ratio`: the same bound with the indexing of Lemma 2.4.1
  of [cartis2022evaluation].
* `Optimization.card_successSet_or_le_of_lower_ratio`: the form with neutral iterations (Lemma
  13.1.9 of [cartis2022evaluation]).
* `Optimization.card_fail_le_of_upper_ratio`: the trust-region form, for a radius that shrinks by at
  least $\gamma_2 \in (0, 1)$ at failures, grows by at most $\gamma_3 \ge 1$ at successes, and stays
  above $\Delta_{\min} > 0$, with the sharp constant $\log(\Delta_0/\Delta_{\min})$.
* `Optimization.card_fail_le_of_upper_ratio_abs`: the same bound with the constant
  $|\log(\Delta_{\min}/\Delta_0)|$ of the book.
* `Optimization.succ_le_card_successSet_of_upper_ratio` and
  `Optimization.le_card_successSet_of_upper_ratio`: the trust-region bound on all iterations (Lemma
  2.3.1 of [cartis2022evaluation]).
* `Optimization.card_successSet_or_le_of_upper_ratio`: the trust-region form with neutral iterations
  (Lemma 13.1.1 of [cartis2022evaluation]).

## Proof outline

The product bound follows by induction on $k$. Taking logarithms gives the bound on
$|\mathcal{U}_k|$. The trust-region statements follow from the adaptive-regularization statements
applied to $\sigma_k = 1/\Delta_k$, $\gamma_S = 1/\gamma_3$ and $\gamma_U = 1/\gamma_2$.

## Implementation notes

* The sets $\mathcal{S}_k$ and $\mathcal{U}_k$ are `Optimization.successSet succ k` and
  `Optimization.successSet fail k`. Both contain $k$ itself when it satisfies the predicate.
-/

open Finset

namespace Optimization

section lower

variable {σ : ℕ → ℝ} {succ fail : ℕ → Prop} {γS γU σmax : ℝ} {k : ℕ}

/-- The product bound of `Optimization.mul_pow_card_le`, with the counts given by `Nat.count` over
$\{0, \dots, n - 1\}$, together with $\sigma_n > 0$. -/
private theorem mul_pow_count_le [DecidablePred succ] [DecidablePred fail] (hσ0 : 0 < σ 0)
    (hγS : 0 < γS) (hγS1 : γS ≤ 1) (hγU : 1 ≤ γU) (n : ℕ)
    (hsucc : ∀ j < n, succ j → γS * σ j ≤ σ (j + 1))
    (hfail : ∀ j < n, fail j → γU * σ j ≤ σ (j + 1))
    (hneutral : ∀ j < n, ¬ succ j → ¬ fail j → σ j ≤ σ (j + 1)) :
    0 < σ n ∧ σ 0 * γS ^ Nat.count succ n * γU ^ Nat.count fail n ≤ σ n := by
  induction n with
  | zero => simp [hσ0]
  | succ n ih =>
    obtain ⟨hpos, hle⟩ := ih (fun j hj => hsucc j (hj.trans n.lt_succ_self))
      (fun j hj => hfail j (hj.trans n.lt_succ_self))
      (fun j hj => hneutral j (hj.trans n.lt_succ_self))
    have hγU0 : 0 < γU := zero_lt_one.trans_le hγU
    set P := σ 0 * γS ^ Nat.count succ n * γU ^ Nat.count fail n
    rw [Nat.count_succ, Nat.count_succ]
    by_cases hs : succ n <;> by_cases hf : fail n <;> simp only [hs, hf, ite_true, ite_false,
      add_zero, pow_succ]
    · -- both: `γS γU σ_n ≤ γU σ_n ≤ σ_{n+1}`
      have h := hfail n n.lt_succ_self hf
      have h1 : γS * (γU * σ n) ≤ γU * σ n :=
        mul_le_of_le_one_left (by positivity) hγS1
      refine ⟨by nlinarith, ?_⟩
      calc σ 0 * (γS ^ Nat.count succ n * γS) * (γU ^ Nat.count fail n * γU)
          = γS * γU * P := by simp only [P]; ring
        _ ≤ γS * γU * σ n := by gcongr
        _ ≤ σ (n + 1) := by nlinarith
    · have h := hsucc n n.lt_succ_self hs
      refine ⟨by nlinarith, ?_⟩
      calc σ 0 * (γS ^ Nat.count succ n * γS) * γU ^ Nat.count fail n
          = γS * P := by simp only [P]; ring
        _ ≤ γS * σ n := by gcongr
        _ ≤ σ (n + 1) := h
    · have h := hfail n n.lt_succ_self hf
      refine ⟨by nlinarith, ?_⟩
      calc σ 0 * γS ^ Nat.count succ n * (γU ^ Nat.count fail n * γU)
          = γU * P := by simp only [P]; ring
        _ ≤ γU * σ n := by gcongr
        _ ≤ σ (n + 1) := h
    · have h := hneutral n n.lt_succ_self hs hf
      exact ⟨hpos.trans_le h, hle.trans h⟩

/-- **Multiplicative parameter growth.** Let $\sigma_0, \sigma_1, \dots$ be real numbers with
$\sigma_0 > 0$, and let $0 < \gamma_S \le 1 \le \gamma_U$. Suppose that for every $j \le k$:
$$\sigma_{j+1} \ge \gamma_S \sigma_j \text{ if } \mathrm{succ}(j), \qquad \sigma_{j+1} \ge
  \gamma_U \sigma_j \text{ if } \mathrm{fail}(j), \qquad \sigma_{j+1} \ge \sigma_j \text{ if
  neither holds}.$$
Then $\sigma_{k+1} > 0$ and
$$\sigma_0 \, \gamma_S^{|\mathcal{S}_k|} \, \gamma_U^{|\mathcal{U}_k|} \le \sigma_{k+1},$$
where $\mathcal{S}_k$ and $\mathcal{U}_k$ are the sets of iterations $j \le k$ that satisfy
$\mathrm{succ}$ and $\mathrm{fail}$, respectively.

The sets are `Optimization.successSet succ k` and `Optimization.successSet fail k`. The
predicates need not be disjoint. -/
theorem mul_pow_card_le (hσ0 : 0 < σ 0) (hγS : 0 < γS) (hγS1 : γS ≤ 1) (hγU : 1 ≤ γU)
    (hsucc : ∀ j ≤ k, succ j → γS * σ j ≤ σ (j + 1))
    (hfail : ∀ j ≤ k, fail j → γU * σ j ≤ σ (j + 1))
    (hneutral : ∀ j ≤ k, ¬ succ j → ¬ fail j → σ j ≤ σ (j + 1)) :
    0 < σ (k + 1) ∧
      σ 0 * γS ^ (successSet succ k).card * γU ^ (successSet fail k).card ≤ σ (k + 1) := by
  classical
  rw [card_successSet_eq_count, card_successSet_eq_count]
  exact mul_pow_count_le hσ0 hγS hγS1 hγU (k + 1)
    (fun j hj => hsucc j (Nat.lt_succ_iff.1 hj)) (fun j hj => hfail j (Nat.lt_succ_iff.1 hj))
    (fun j hj => hneutral j (Nat.lt_succ_iff.1 hj))

/-- **Counting failures through a bounded parameter.** Under the hypotheses of
`Optimization.mul_pow_card_le` ($\sigma_0 > 0$, $0 < \gamma_S \le 1 \le \gamma_U$, and the three
growth conditions for $j \le k$), suppose also that $\sigma_{k+1} \le \sigma_{\max}$. Then
$$|\mathcal{U}_k| \log \gamma_U \le \log(\sigma_{\max}/\sigma_0) + |\mathcal{S}_k| \, |\log
  \gamma_S|.$$

This is the argument of the proof of Lemma 2.4.1 of [cartis2022evaluation], in general form. -/
theorem card_fail_mul_log_le (hσ0 : 0 < σ 0) (hγS : 0 < γS) (hγS1 : γS ≤ 1) (hγU : 1 ≤ γU)
    (hsucc : ∀ j ≤ k, succ j → γS * σ j ≤ σ (j + 1))
    (hfail : ∀ j ≤ k, fail j → γU * σ j ≤ σ (j + 1))
    (hneutral : ∀ j ≤ k, ¬ succ j → ¬ fail j → σ j ≤ σ (j + 1)) (hmax : σ (k + 1) ≤ σmax) :
    ((successSet fail k).card : ℝ) * Real.log γU ≤
      Real.log (σmax / σ 0) + (successSet succ k).card * |Real.log γS| := by
  obtain ⟨hpos, hle⟩ := mul_pow_card_le hσ0 hγS hγS1 hγU hsucc hfail hneutral
  have hγU0 : 0 < γU := zero_lt_one.trans_le hγU
  have hP : 0 < σ 0 * γS ^ (successSet succ k).card * γU ^ (successSet fail k).card := by
    positivity
  have hlog := Real.log_le_log hP (hle.trans hmax)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow] at hlog
  rw [Real.log_div (hpos.trans_le hmax).ne' hσ0.ne',
    abs_of_nonpos (Real.log_nonpos hγS.le hγS1)]
  linarith

/-- **Counting failures, adaptive-regularization form.** Under the hypotheses of
`Optimization.card_fail_mul_log_le`, with $\gamma_U > 1$ in place of $\gamma_U \ge 1$,
$$|\mathcal{U}_k| \le |\mathcal{S}_k| \frac{|\log \gamma_S|}{\log \gamma_U} +
  \frac{\log(\sigma_{\max}/\sigma_0)}{\log \gamma_U}.$$
-/
theorem card_fail_le_of_lower_ratio (hσ0 : 0 < σ 0) (hγS : 0 < γS) (hγS1 : γS ≤ 1)
    (hγU : 1 < γU)
    (hsucc : ∀ j ≤ k, succ j → γS * σ j ≤ σ (j + 1))
    (hfail : ∀ j ≤ k, fail j → γU * σ j ≤ σ (j + 1))
    (hneutral : ∀ j ≤ k, ¬ succ j → ¬ fail j → σ j ≤ σ (j + 1)) (hmax : σ (k + 1) ≤ σmax) :
    ((successSet fail k).card : ℝ) ≤
      (successSet succ k).card * (|Real.log γS| / Real.log γU) +
        Real.log (σmax / σ 0) / Real.log γU := by
  have hlog : 0 < Real.log γU := Real.log_pos hγU
  have h := card_fail_mul_log_le hσ0 hγS hγS1 hγU.le hsucc hfail hneutral hmax
  rw [mul_div_assoc', ← add_div, le_div_iff₀ hlog]
  linarith

/-- **Bounding all iterations, adaptive-regularization form.** Let $\sigma_0 > 0$ and
$0 < \gamma_S \le 1 < \gamma_U$. Suppose that for every $j \le k$,
$\sigma_{j+1} \ge \gamma_S \sigma_j$ if $\mathrm{succ}(j)$ and
$\sigma_{j+1} \ge \gamma_U \sigma_j$ otherwise. If $\sigma_{k+1} \le \sigma_{\max}$, then
$$k + 1 \le |\mathcal{S}_k| \left(1 + \frac{|\log \gamma_S|}{\log \gamma_U}\right) +
  \frac{\log(\sigma_{\max}/\sigma_0)}{\log \gamma_U}.$$

This is the mechanism of Lemma 2.4.1 of [cartis2022evaluation]. The form with the indexing of
the book is `Optimization.le_card_successSet_of_lower_ratio`. -/
theorem succ_le_card_successSet_of_lower_ratio (hσ0 : 0 < σ 0) (hγS : 0 < γS) (hγS1 : γS ≤ 1)
    (hγU : 1 < γU)
    (hsucc : ∀ j ≤ k, succ j → γS * σ j ≤ σ (j + 1))
    (hfail : ∀ j ≤ k, ¬ succ j → γU * σ j ≤ σ (j + 1)) (hmax : σ (k + 1) ≤ σmax) :
    (k + 1 : ℝ) ≤
      (successSet succ k).card * (1 + |Real.log γS| / Real.log γU) +
        Real.log (σmax / σ 0) / Real.log γU := by
  have h := card_fail_le_of_lower_ratio (fail := fun j => ¬ succ j) hσ0 hγS hγS1 hγU hsucc
    hfail (fun _ _ hs hf => absurd hs hf) hmax
  have hcard : ((successSet succ k).card : ℝ) + (failureSet succ k).card = k + 1 := by
    exact_mod_cast card_successSet_add_card_failureSet
  rw [failureSet] at hcard
  linarith

/-- **Bounding all iterations, adaptive-regularization form, with the indexing of the book.** Let
$\sigma_0 > 0$ and $0 < \gamma_S \le 1 < \gamma_U$. Suppose that for every $j < k$,
$\sigma_{j+1} \ge \gamma_S \sigma_j$ if $\mathrm{succ}(j)$ and
$\sigma_{j+1} \ge \gamma_U \sigma_j$ otherwise. If $\sigma_k \le \sigma_{\max}$, then
$$k \le |\mathcal{S}_k| \left(1 + \frac{|\log \gamma_S|}{\log \gamma_U}\right) +
  \frac{\log(\sigma_{\max}/\sigma_0)}{\log \gamma_U},$$
where $\mathcal{S}_k$ is the set of $j \in \{0, \dots, k\}$ with $\mathrm{succ}(j)$.

This is Lemma 2.4.1 of [cartis2022evaluation]. -/
theorem le_card_successSet_of_lower_ratio (hσ0 : 0 < σ 0) (hγS : 0 < γS) (hγS1 : γS ≤ 1)
    (hγU : 1 < γU)
    (hsucc : ∀ j < k, succ j → γS * σ j ≤ σ (j + 1))
    (hfail : ∀ j < k, ¬ succ j → γU * σ j ≤ σ (j + 1)) (hmax : σ k ≤ σmax) :
    (k : ℝ) ≤
      (successSet succ k).card * (1 + |Real.log γS| / Real.log γU) +
        Real.log (σmax / σ 0) / Real.log γU := by
  have hlog : 0 < Real.log γU := Real.log_pos hγU
  have hA : 0 ≤ 1 + |Real.log γS| / Real.log γU := by positivity
  cases k with
  | zero =>
    have : 0 ≤ Real.log (σmax / σ 0) :=
      Real.log_nonneg ((one_le_div hσ0).2 hmax)
    simp only [Nat.cast_zero]
    positivity
  | succ k =>
    have h := succ_le_card_successSet_of_lower_ratio hσ0 hγS hγS1 hγU
      (fun j hj => hsucc j (Nat.lt_succ_iff.2 hj)) (fun j hj => hfail j (Nat.lt_succ_iff.2 hj))
      hmax
    have hmono : ((successSet succ k).card : ℝ) ≤ (successSet succ (k + 1)).card := by
      exact_mod_cast card_successSet_mono k.le_succ
    push_cast
    nlinarith

/-- **Bounding the successful and failed iterations, with neutral iterations.** Let $\sigma_0 > 0$
and $0 < \gamma_S \le 1 < \gamma_U$. Suppose that no $j \le k$ satisfies both $\mathrm{succ}$
and $\mathrm{fail}$, and that for every $j \le k$:
$$\sigma_{j+1} \ge \gamma_S \sigma_j \text{ if } \mathrm{succ}(j), \qquad \sigma_{j+1} \ge
  \gamma_U \sigma_j \text{ if } \mathrm{fail}(j), \qquad \sigma_{j+1} \ge \sigma_j \text{
  otherwise}.$$
If $\sigma_{k+1} \le \sigma_{\max}$, then the set $\mathcal{T}_k$ of iterations $j \le k$ that
satisfy $\mathrm{succ}$ or $\mathrm{fail}$ has
$$|\mathcal{T}_k| \le |\mathcal{S}_k| \left(1 + \frac{|\log \gamma_S|}{\log \gamma_U}\right) +
  \frac{\log(\sigma_{\max}/\sigma_0)}{\log \gamma_U}.$$
This is the mechanism of Lemma 13.1.9 of [cartis2022evaluation].

The bound is needed at $\sigma_{k+1}$, the parameter after iteration $k$. With the bound only at
$\sigma_k$, the statement fails for $k = 0$, an unsuccessful iteration $0$ and
$\sigma_{\max} = \sigma_0$: the left side is $1$ and the right side is $0$. -/
theorem card_successSet_or_le_of_lower_ratio (hσ0 : 0 < σ 0) (hγS : 0 < γS) (hγS1 : γS ≤ 1)
    (hγU : 1 < γU) (hdisj : ∀ j ≤ k, succ j → ¬ fail j)
    (hsucc : ∀ j ≤ k, succ j → γS * σ j ≤ σ (j + 1))
    (hfail : ∀ j ≤ k, fail j → γU * σ j ≤ σ (j + 1))
    (hneutral : ∀ j ≤ k, ¬ succ j → ¬ fail j → σ j ≤ σ (j + 1)) (hmax : σ (k + 1) ≤ σmax) :
    ((successSet (fun j => succ j ∨ fail j) k).card : ℝ) ≤
      (successSet succ k).card * (1 + |Real.log γS| / Real.log γU) +
        Real.log (σmax / σ 0) / Real.log γU := by
  have h := card_fail_le_of_lower_ratio hσ0 hγS hγS1 hγU hsucc hfail hneutral hmax
  rw [card_successSet_or hdisj]
  push_cast
  linarith

end lower

section upper

variable {Δ : ℕ → ℝ} {succ fail : ℕ → Prop} {γ₂ γ₃ Δmin : ℝ} {k : ℕ}

/-- A sequence $\Delta$ with $\Delta_{k+1} > 0$ and $\Delta_{j+1} \le c_j \Delta_j$ for some
$c_j > 0$ at each $j \le k$ is positive at all $j \le k + 1$. -/
private theorem pos_of_le_mul (hΔ : 0 < Δ (k + 1))
    (h : ∀ j ≤ k, ∃ c, 0 < c ∧ Δ (j + 1) ≤ c * Δ j) : ∀ j ≤ k + 1, 0 < Δ j := by
  have key : ∀ m ≤ k + 1, 0 < Δ (k + 1 - m) := by
    intro m
    induction m with
    | zero => exact fun _ => hΔ
    | succ m ih =>
      intro hm
      have hpos := ih (by omega)
      obtain ⟨c, hc, hle⟩ := h (k - m) (by omega)
      have heq : k - m + 1 = k + 1 - m := by omega
      rw [heq] at hle
      have h' : k + 1 - (m + 1) = k - m := by omega
      rw [h']
      by_contra hneg
      push Not at hneg
      nlinarith
  intro j hj
  have := key (k + 1 - j) (by omega)
  rwa [show k + 1 - (k + 1 - j) = j by omega] at this

/-- **Counting failures through a radius bounded below, trust-region form.** Let
$0 < \gamma_2 < 1 \le \gamma_3$. Suppose that for every $j \le k$:
$$\Delta_{j+1} \le \gamma_3 \Delta_j \text{ if } \mathrm{succ}(j), \qquad \Delta_{j+1} \le
  \gamma_2 \Delta_j \text{ if } \mathrm{fail}(j), \qquad \Delta_{j+1} \le \Delta_j \text{ if
  neither holds}.$$
If $0 < \Delta_{\min} \le \Delta_{k+1}$, then
$$|\mathcal{U}_k| \le |\mathcal{S}_k| \frac{\log \gamma_3}{|\log \gamma_2|} +
  \frac{\log(\Delta_0/\Delta_{\min})}{|\log \gamma_2|}.$$

The positivity of $\Delta_0, \dots, \Delta_k$ follows from the hypotheses. This is the sharp
form. The form with the constant $|\log(\Delta_{\min}/\Delta_0)|$ is
`Optimization.card_fail_le_of_upper_ratio_abs`. The proof applies
`Optimization.card_fail_le_of_lower_ratio` to $\sigma_j = 1/\Delta_j$, $\gamma_S = 1/\gamma_3$
and $\gamma_U = 1/\gamma_2$. -/
theorem card_fail_le_of_upper_ratio (hγ₂ : 0 < γ₂) (hγ₂1 : γ₂ < 1) (hγ₃ : 1 ≤ γ₃)
    (hsucc : ∀ j ≤ k, succ j → Δ (j + 1) ≤ γ₃ * Δ j)
    (hfail : ∀ j ≤ k, fail j → Δ (j + 1) ≤ γ₂ * Δ j)
    (hneutral : ∀ j ≤ k, ¬ succ j → ¬ fail j → Δ (j + 1) ≤ Δ j)
    (hmin : 0 < Δmin) (hΔmin : Δmin ≤ Δ (k + 1)) :
    ((successSet fail k).card : ℝ) ≤
      (successSet succ k).card * (Real.log γ₃ / |Real.log γ₂|) +
        Real.log (Δ 0 / Δmin) / |Real.log γ₂| := by
  have hpos : ∀ j ≤ k + 1, 0 < Δ j := by
    refine pos_of_le_mul (hmin.trans_le hΔmin) fun j hj => ?_
    by_cases hs : succ j
    · exact ⟨γ₃, zero_lt_one.trans_le hγ₃, hsucc j hj hs⟩
    by_cases hf : fail j
    · exact ⟨γ₂, hγ₂, hfail j hj hf⟩
    · exact ⟨1, zero_lt_one, (one_mul (Δ j)).symm ▸ hneutral j hj hs hf⟩
  have hγ₃0 : 0 < γ₃ := zero_lt_one.trans_le hγ₃
  have hinv : ∀ {c : ℝ}, 0 < c → ∀ j ≤ k, Δ (j + 1) ≤ c * Δ j → c⁻¹ * (Δ j)⁻¹ ≤ (Δ (j + 1))⁻¹ :=
    fun {c} hc j hj h => by
      rw [← mul_inv]
      exact inv_anti₀ (hpos (j + 1) (by omega)) h
  have h := card_fail_le_of_lower_ratio (σ := fun j => (Δ j)⁻¹) (γS := γ₃⁻¹) (γU := γ₂⁻¹)
    (σmax := Δmin⁻¹) (succ := succ) (fail := fail) (k := k)
    (inv_pos.2 (hpos 0 (Nat.zero_le _))) (inv_pos.2 hγ₃0) (inv_le_one_of_one_le₀ hγ₃)
    ((one_lt_inv₀ hγ₂).2 hγ₂1)
    (fun j hj hs => hinv hγ₃0 j hj (hsucc j hj hs))
    (fun j hj hf => hinv hγ₂ j hj (hfail j hj hf))
    (fun j hj hs hf => inv_anti₀ (hpos (j + 1) (by omega)) (hneutral j hj hs hf))
    (inv_anti₀ hmin hΔmin)
  have hl2 : Real.log γ₂ < 0 := Real.log_neg hγ₂ hγ₂1
  have hl3 : 0 ≤ Real.log γ₃ := Real.log_nonneg hγ₃
  simp only [Real.log_inv, abs_neg, abs_of_nonneg hl3, inv_div_inv] at h
  rwa [abs_of_neg hl2]

/-- For all real $a$ and $b$, $\log(a/b) \le |\log(b/a)|$. This converts the sharp trust-region
bounds to the form of [cartis2022evaluation]. -/
theorem log_div_le_abs_log_div (a b : ℝ) : Real.log (a / b) ≤ |Real.log (b / a)| := by
  rw [← inv_div, Real.log_inv]
  exact neg_le_abs _

/-- **Counting failures, trust-region form with the constant of the book.** Under the hypotheses of
`Optimization.card_fail_le_of_upper_ratio`,
$$|\mathcal{U}_k| \le |\mathcal{S}_k| \frac{\log \gamma_3}{|\log \gamma_2|} +
  \frac{|\log(\Delta_{\min}/\Delta_0)|}{|\log \gamma_2|}.$$
-/
theorem card_fail_le_of_upper_ratio_abs (hγ₂ : 0 < γ₂) (hγ₂1 : γ₂ < 1) (hγ₃ : 1 ≤ γ₃)
    (hsucc : ∀ j ≤ k, succ j → Δ (j + 1) ≤ γ₃ * Δ j)
    (hfail : ∀ j ≤ k, fail j → Δ (j + 1) ≤ γ₂ * Δ j)
    (hneutral : ∀ j ≤ k, ¬ succ j → ¬ fail j → Δ (j + 1) ≤ Δ j)
    (hmin : 0 < Δmin) (hΔmin : Δmin ≤ Δ (k + 1)) :
    ((successSet fail k).card : ℝ) ≤
      (successSet succ k).card * (Real.log γ₃ / |Real.log γ₂|) +
        |Real.log (Δmin / Δ 0)| / |Real.log γ₂| :=
  (card_fail_le_of_upper_ratio hγ₂ hγ₂1 hγ₃ hsucc hfail hneutral hmin hΔmin).trans
    (add_le_add_right (div_le_div_of_nonneg_right (log_div_le_abs_log_div _ _) (abs_nonneg _)) _)

/-- **Bounding all iterations, trust-region form.** Let $0 < \gamma_2 < 1 \le \gamma_3$. Suppose
that for every $j \le k$, $\Delta_{j+1} \le \gamma_3 \Delta_j$ if $\mathrm{succ}(j)$ and
$\Delta_{j+1} \le \gamma_2 \Delta_j$ otherwise. If $0 < \Delta_{\min} \le \Delta_{k+1}$, then
$$k + 1 \le |\mathcal{S}_k| \left(1 + \frac{\log \gamma_3}{|\log \gamma_2|}\right) +
  \frac{|\log(\Delta_{\min}/\Delta_0)|}{|\log \gamma_2|}.$$

This is the mechanism of Lemma 2.3.1 of [cartis2022evaluation]. The form with the indexing of
the book is `Optimization.le_card_successSet_of_upper_ratio`. -/
theorem succ_le_card_successSet_of_upper_ratio (hγ₂ : 0 < γ₂) (hγ₂1 : γ₂ < 1) (hγ₃ : 1 ≤ γ₃)
    (hsucc : ∀ j ≤ k, succ j → Δ (j + 1) ≤ γ₃ * Δ j)
    (hfail : ∀ j ≤ k, ¬ succ j → Δ (j + 1) ≤ γ₂ * Δ j)
    (hmin : 0 < Δmin) (hΔmin : Δmin ≤ Δ (k + 1)) :
    (k + 1 : ℝ) ≤
      (successSet succ k).card * (1 + Real.log γ₃ / |Real.log γ₂|) +
        |Real.log (Δmin / Δ 0)| / |Real.log γ₂| := by
  have h := card_fail_le_of_upper_ratio_abs (fail := fun j => ¬ succ j) hγ₂ hγ₂1 hγ₃ hsucc hfail
    (fun _ _ hs hf => absurd hs hf) hmin hΔmin
  have hcard : ((successSet succ k).card : ℝ) + (failureSet succ k).card = k + 1 := by
    exact_mod_cast card_successSet_add_card_failureSet
  rw [failureSet] at hcard
  linarith

/-- **Bounding all iterations, trust-region form, with the indexing of the book.** Let
$0 < \gamma_2 < 1 \le \gamma_3$. Suppose that for every $j < k$,
$\Delta_{j+1} \le \gamma_3 \Delta_j$ if $\mathrm{succ}(j)$ and
$\Delta_{j+1} \le \gamma_2 \Delta_j$ otherwise. If $0 < \Delta_{\min} \le \Delta_k$, then
$$k \le |\mathcal{S}_k| \left(1 + \frac{\log \gamma_3}{|\log \gamma_2|}\right) +
  \frac{|\log(\Delta_{\min}/\Delta_0)|}{|\log \gamma_2|},$$
where $\mathcal{S}_k$ is the set of $j \in \{0, \dots, k\}$ with $\mathrm{succ}(j)$.

This is Lemma 2.3.1 of [cartis2022evaluation]. -/
theorem le_card_successSet_of_upper_ratio (hγ₂ : 0 < γ₂) (hγ₂1 : γ₂ < 1) (hγ₃ : 1 ≤ γ₃)
    (hsucc : ∀ j < k, succ j → Δ (j + 1) ≤ γ₃ * Δ j)
    (hfail : ∀ j < k, ¬ succ j → Δ (j + 1) ≤ γ₂ * Δ j)
    (hmin : 0 < Δmin) (hΔmin : Δmin ≤ Δ k) :
    (k : ℝ) ≤
      (successSet succ k).card * (1 + Real.log γ₃ / |Real.log γ₂|) +
        |Real.log (Δmin / Δ 0)| / |Real.log γ₂| := by
  have hl3 : 0 ≤ Real.log γ₃ := Real.log_nonneg hγ₃
  have hA : 0 ≤ 1 + Real.log γ₃ / |Real.log γ₂| := by positivity
  cases k with
  | zero =>
    simp only [Nat.cast_zero]
    positivity
  | succ k =>
    have h := succ_le_card_successSet_of_upper_ratio hγ₂ hγ₂1 hγ₃
      (fun j hj => hsucc j (Nat.lt_succ_iff.2 hj)) (fun j hj => hfail j (Nat.lt_succ_iff.2 hj))
      hmin hΔmin
    have hmono : ((successSet succ k).card : ℝ) ≤ (successSet succ (k + 1)).card := by
      exact_mod_cast card_successSet_mono k.le_succ
    push_cast
    nlinarith

/-- **Bounding the successful and failed iterations, trust-region form with neutral iterations.**
Let $0 < \gamma_2 < 1 \le \gamma_3$. Suppose that no $j \le k$ satisfies both $\mathrm{succ}$
and $\mathrm{fail}$, and that for every $j \le k$:
$$\Delta_{j+1} \le \gamma_3 \Delta_j \text{ if } \mathrm{succ}(j), \qquad \Delta_{j+1} \le
  \gamma_2 \Delta_j \text{ if } \mathrm{fail}(j), \qquad \Delta_{j+1} \le \Delta_j \text{
  otherwise}.$$
If $0 < \Delta_{\min} \le \Delta_{k+1}$, then the set $\mathcal{T}_k$ of iterations $j \le k$
that satisfy $\mathrm{succ}$ or $\mathrm{fail}$ has
$$|\mathcal{T}_k| \le |\mathcal{S}_k| \left(1 + \frac{\log \gamma_3}{|\log \gamma_2|}\right) +
  \frac{|\log(\Delta_{\min}/\Delta_0)|}{|\log \gamma_2|}.$$
This is the mechanism of Lemma 13.1.1 of [cartis2022evaluation].

The bound is needed at $\Delta_{k+1}$, the radius after iteration $k$. With the bound only at
$\Delta_k$, the statement fails for $k = 0$, an unsuccessful iteration $0$ and
$\Delta_{\min} = \Delta_0$: the left side is $1$ and the right side is $0$. -/
theorem card_successSet_or_le_of_upper_ratio (hγ₂ : 0 < γ₂) (hγ₂1 : γ₂ < 1) (hγ₃ : 1 ≤ γ₃)
    (hdisj : ∀ j ≤ k, succ j → ¬ fail j)
    (hsucc : ∀ j ≤ k, succ j → Δ (j + 1) ≤ γ₃ * Δ j)
    (hfail : ∀ j ≤ k, fail j → Δ (j + 1) ≤ γ₂ * Δ j)
    (hneutral : ∀ j ≤ k, ¬ succ j → ¬ fail j → Δ (j + 1) ≤ Δ j)
    (hmin : 0 < Δmin) (hΔmin : Δmin ≤ Δ (k + 1)) :
    ((successSet (fun j => succ j ∨ fail j) k).card : ℝ) ≤
      (successSet succ k).card * (1 + Real.log γ₃ / |Real.log γ₂|) +
        |Real.log (Δmin / Δ 0)| / |Real.log γ₂| := by
  have h := card_fail_le_of_upper_ratio_abs hγ₂ hγ₂1 hγ₃ hsucc hfail hneutral hmin hΔmin
  rw [card_successSet_or hdisj]
  push_cast
  linarith

end upper

end Optimization
