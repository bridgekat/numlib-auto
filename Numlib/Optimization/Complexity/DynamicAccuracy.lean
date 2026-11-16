/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.TrustRegionUpdate
import Numlib.Optimization.ModelBased.RegularizationUpdate

/-!
# Counting with accuracy-improving iterations

The dynamic-accuracy methods of Chapter 13 of [cartis2022evaluation] (TRqIDA, ARqpIDA, TRqEDA and
ARqpEDA) have three kinds of iterations. Successful iterations ($\mathcal{S}$) and unsuccessful
iterations ($\mathcal{U}$) together form the trial iterations
$\mathcal{T} = \mathcal{S} \cup \mathcal{U}$, each of which evaluates the objective once.
Accuracy-improving iterations ($\mathcal{A}$) multiply the requested accuracies by a factor
$\gamma_h \in (0, 1)$ and leave the iterate and the trust-region radius (or the regularization
parameter) unchanged. This module contains the counting arguments for such methods: a bound on the
number of accuracy-improving iterations, and the complexity skeleton that turns bounds on
$|\mathcal{T}_k|$ and $|\mathcal{A}_k|$ into a bound on the termination index and on the evaluation
counts.

The bounds on the radius and on the regularization parameter that allow such neutral iterations are
`Optimization.le_delta_of_trUpdate_of_neutral` (in
`Numlib.Optimization.ModelBased.TrustRegionUpdate`) and
`Optimization.sigma_le_max_of_arUpdate_of_neutral` (in
`Numlib.Optimization.ModelBased.RegularizationUpdate`). The counts of trial iterations in terms of
successful ones, Lemmas 13.1.1 and 13.1.9 of [cartis2022evaluation], are
`Optimization.card_successSet_or_le_of_upper_ratio` and
`Optimization.card_successSet_or_le_of_lower_ratio`, which already allow neutral iterations.

## Main results

* `Optimization.card_accuracyImproving_le`: if an accuracy-improving iteration can happen only while
  the largest requested accuracy exceeds $c$, then there are at most $\lceil \log(c / \kappa_h) /
  \log \gamma_h \rceil$ accuracy-improving iterations. This is the count $i_{h,\epsilon}$ in the
  proofs of Theorems 13.1.8 and 13.1.19 of [cartis2022evaluation].
* `Optimization.card_accuracyImproving_le_of_pow`: the same bound for the threshold
  $c = \kappa_{\mathrm{acc}} \epsilon^N$, in the form (13.1.44).
* `Optimization.card_trial_add_card_acc`: every iteration is either a trial iteration or an
  accuracy-improving one.
* `Optimization.exists_firstHit_le_of_dynamicAccuracy`: bounds on the numbers of trial and of
  accuracy-improving iterations before termination bound the termination index and the evaluation
  counts.
-/

open Finset

namespace Optimization

section accuracy

variable {acc : ℕ → Prop} {hmax : ℕ → ℝ} {γh κh c : ℝ}

/-- If the largest requested accuracy $h_{\max}$ is multiplied by $\gamma_h \ge 0$ at the
accuracy-improving iterations $j \le k$, is unchanged at the other iterations $j \le k$,
satisfies $h_{\max}(0) \le \kappa_h$, and exceeds $c$ at every accuracy-improving iteration
$j \le k$, then $h_{\max}(k + 1) = \gamma_h^{|\mathcal{A}_k|} h_{\max}(0)$, and either
$\mathcal{A}_k = \emptyset$ or $c < \gamma_h^{|\mathcal{A}_k| - 1} \kappa_h$. -/
private theorem accuracy_aux (hh0 : hmax 0 ≤ κh) (hγh : 0 ≤ γh)
    (k : ℕ) (hacc : ∀ j ≤ k, acc j → hmax (j + 1) = γh * hmax j)
    (hnacc : ∀ j ≤ k, ¬ acc j → hmax (j + 1) = hmax j) (hc : ∀ j ≤ k, acc j → c < hmax j) :
    hmax (k + 1) = γh ^ (successSet acc k).card * hmax 0 ∧
      ((successSet acc k).card = 0 ∨ c < γh ^ ((successSet acc k).card - 1) * κh) := by
  induction k with
  | zero =>
    by_cases h0 : acc 0
    · rw [successSet_zero_of_succ h0, hacc 0 le_rfl h0]
      exact ⟨by simp, Or.inr (by simpa using (hc 0 le_rfl h0).trans_le hh0)⟩
    · rw [successSet_zero_of_not_succ h0, hnacc 0 le_rfl h0]
      simp
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun j hj => hacc j (hj.trans k.le_succ))
      (fun j hj => hnacc j (hj.trans k.le_succ)) fun j hj => hc j (hj.trans k.le_succ)
    by_cases hk : acc (k + 1)
    · rw [card_successSet_add_one_of_succ hk, hacc _ le_rfl hk, ih1]
      refine ⟨by ring, Or.inr ?_⟩
      rw [Nat.add_sub_cancel]
      have := hc (k + 1) le_rfl hk
      rw [ih1] at this
      exact this.trans_le (mul_le_mul_of_nonneg_left hh0 (pow_nonneg hγh _))
    · rw [card_successSet_add_one_of_not_succ hk, hnacc _ le_rfl hk, ih1]
      exact ⟨rfl, ih2⟩

/-- **Number of accuracy-improving iterations.** Let $0 < \gamma_h < 1$, $\kappa_h > 0$ and $c > 0$,
let $k \in \mathbb{N}$, and let $h_{\max} \colon \mathbb{N} \to \mathbb{R}$ (the largest
requested accuracy) satisfy $h_{\max}(0) \le \kappa_h$. Let $\mathcal{A}_k$ be the set of
accuracy-improving iterations in $\{0, \dots, k\}$. Suppose that for every $j \le k$
$$h_{\max}(j + 1) = \gamma_h h_{\max}(j) \text{ if } j \in \mathcal{A}_k, \qquad
  h_{\max}(j + 1) = h_{\max}(j) \text{ otherwise},$$
and that $c < h_{\max}(j)$ for every $j \in \mathcal{A}_k$. Then
$$|\mathcal{A}_k| \le \left\lceil \frac{\log(c / \kappa_h)}{\log \gamma_h} \right\rceil.$$

This is the count $i_{h,\epsilon}$ in the proofs of Theorems 13.1.8 and 13.1.19 of
[cartis2022evaluation]. The ceiling is `Nat.ceil`, and $\mathcal{A}_k$ is
`Optimization.successSet acc k`. -/
theorem card_accuracyImproving_le (hγh : 0 < γh) (hγh1 : γh < 1) (hκh : 0 < κh) (hc0 : 0 < c)
    (hh0 : hmax 0 ≤ κh)
    {k : ℕ} (hacc : ∀ j ≤ k, acc j → hmax (j + 1) = γh * hmax j)
    (hnacc : ∀ j ≤ k, ¬ acc j → hmax (j + 1) = hmax j) (hc : ∀ j ≤ k, acc j → c < hmax j) :
    (successSet acc k).card ≤ ⌈Real.log (c / κh) / Real.log γh⌉₊ := by
  rcases (accuracy_aux hh0 hγh.le k hacc hnacc hc).2 with h0 | hlt
  · rw [h0]; exact Nat.zero_le _
  set n := (successSet acc k).card
  have hlog : Real.log γh < 0 := Real.log_neg hγh hγh1
  have hlt' : ((n - 1 : ℕ) : ℝ) < Real.log (c / κh) / Real.log γh := by
    rw [lt_div_iff_of_neg hlog, Real.log_div hc0.ne' hκh.ne']
    have := Real.log_lt_log hc0 hlt
    rw [Real.log_mul (pow_pos hγh _).ne' hκh.ne', Real.log_pow] at this
    linarith
  have : n - 1 < ⌈Real.log (c / κh) / Real.log γh⌉₊ := by
    exact_mod_cast hlt'.trans_le (Nat.le_ceil _)
  omega

/-- Real form of `Optimization.card_accuracyImproving_le`: under the same hypotheses,
$$|\mathcal{A}_k| \le \frac{|\log(c / \kappa_h)|}{|\log \gamma_h|} + 1.$$
-/
theorem card_accuracyImproving_le_abs (hγh : 0 < γh) (hγh1 : γh < 1) (hκh : 0 < κh)
    (hc0 : 0 < c) (hh0 : hmax 0 ≤ κh)
    {k : ℕ} (hacc : ∀ j ≤ k, acc j → hmax (j + 1) = γh * hmax j)
    (hnacc : ∀ j ≤ k, ¬ acc j → hmax (j + 1) = hmax j) (hc : ∀ j ≤ k, acc j → c < hmax j) :
    ((successSet acc k).card : ℝ) ≤ |Real.log (c / κh)| / |Real.log γh| + 1 := by
  have h := card_accuracyImproving_le hγh hγh1 hκh hc0 hh0 hacc hnacc hc
  set L := Real.log (c / κh) / Real.log γh
  have hL : L ≤ |Real.log (c / κh)| / |Real.log γh| := by
    rw [← abs_div]; exact le_abs_self _
  have hnn : 0 ≤ |Real.log (c / κh)| / |Real.log γh| := by positivity
  rcases le_or_gt L 0 with hL0 | hL0
  · rw [Nat.ceil_eq_zero.2 hL0] at h
    have : (successSet acc k).card = 0 := Nat.le_zero.1 h
    rw [this, Nat.cast_zero]; linarith
  · have := Nat.ceil_lt_add_one hL0.le
    have : ((successSet acc k).card : ℝ) ≤ ⌈L⌉₊ := by exact_mod_cast h
    linarith

/-- Let $0 < \gamma_h < 1$, $\kappa_h > 0$, $\kappa_{\mathrm{acc}} > 0$, $\epsilon > 0$ and
$N \in \mathbb{N}$, let $k \in \mathbb{N}$, and let $h_{\max} \colon \mathbb{N} \to \mathbb{R}$
satisfy $h_{\max}(0) \le \kappa_h$. Suppose that for every $j \le k$,
$h_{\max}(j + 1) = \gamma_h h_{\max}(j)$ if $j \in \mathcal{A}_k$ and
$h_{\max}(j + 1) = h_{\max}(j)$ otherwise, and that
$\kappa_{\mathrm{acc}} \epsilon^N < h_{\max}(j)$ for every $j \in \mathcal{A}_k$. Then
$$|\mathcal{A}_k| \le \frac{N |\log \epsilon| + |\log(\kappa_{\mathrm{acc}} / \kappa_h)|}{|\log
  \gamma_h|} + 1.$$

This is the form (13.1.44) of [cartis2022evaluation] of
`Optimization.card_accuracyImproving_le`, for the threshold
$c = \kappa_{\mathrm{acc}} \epsilon^N$. -/
theorem card_accuracyImproving_le_of_pow {κacc ε : ℝ} {N : ℕ} (hγh : 0 < γh) (hγh1 : γh < 1)
    (hκh : 0 < κh) (hκacc : 0 < κacc) (hε : 0 < ε) (hh0 : hmax 0 ≤ κh)
    {k : ℕ} (hacc : ∀ j ≤ k, acc j → hmax (j + 1) = γh * hmax j)
    (hnacc : ∀ j ≤ k, ¬ acc j → hmax (j + 1) = hmax j)
    (hc : ∀ j ≤ k, acc j → κacc * ε ^ N < hmax j) :
    ((successSet acc k).card : ℝ) ≤
      (N * |Real.log ε| + |Real.log (κacc / κh)|) / |Real.log γh| + 1 := by
  have h := card_accuracyImproving_le_abs hγh hγh1 hκh (mul_pos hκacc (pow_pos hε N)) hh0
    hacc hnacc hc
  have hsplit : Real.log (κacc * ε ^ N / κh) = N * Real.log ε + Real.log (κacc / κh) := by
    rw [mul_div_right_comm, Real.log_mul (div_pos hκacc hκh).ne' (pow_pos hε N).ne',
      Real.log_pow]
    ring
  have habs : |Real.log (κacc * ε ^ N / κh)| ≤ N * |Real.log ε| + |Real.log (κacc / κh)| := by
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, Nat.abs_cast]
  have hlog : 0 < |Real.log γh| := abs_pos.2 (Real.log_neg hγh hγh1).ne
  have := div_le_div_of_nonneg_right habs hlog.le
  linarith

/-- Let $0 < \gamma_h < 1$, $\kappa_h \ge 0$, $\kappa_{\mathrm{acc}} > 0$, $\epsilon > 0$ and
$N \in \mathbb{N}$, let $k \in \mathbb{N}$, and let $h_{\max} \colon \mathbb{N} \to \mathbb{R}$
satisfy $h_{\max}(0) \le \kappa_h$ and $h_{\max}(j) \le \kappa_h$ for every $j \le k$. Suppose
that for every $j \le k$, $h_{\max}(j + 1) = \gamma_h h_{\max}(j)$ if $j \in \mathcal{A}_k$ and
$h_{\max}(j + 1) = h_{\max}(j)$ otherwise, and that
$\kappa_{\mathrm{acc}} \epsilon^N < h_{\max}(j)$ for every $j \in \mathcal{A}_k$. Then
$$|\mathcal{A}_k| \le \frac{N |\log \epsilon| + |\log(\kappa_{\mathrm{acc}} / \kappa_h)|}{|\log
  \gamma_h|} + 1.$$

This is `Optimization.card_accuracyImproving_le_of_pow` with $\kappa_h = 0$ allowed. For
$\kappa_h = 0$ no iteration is accuracy-improving, because the threshold
$\kappa_{\mathrm{acc}} \epsilon^N$ is positive, and the bound holds with the Lean value
$\log(\kappa_{\mathrm{acc}} / 0) = \log 0 = 0$. -/
theorem card_accuracyImproving_le_of_pow_of_nonneg
    {κacc ε : ℝ} {N : ℕ} (hγh : 0 < γh) (hγh1 : γh < 1) (hκh : 0 ≤ κh) (hκacc : 0 < κacc)
    (hε : 0 < ε) (hh0 : hmax 0 ≤ κh) {k : ℕ} (hle : ∀ j ≤ k, hmax j ≤ κh)
    (hacc : ∀ j ≤ k, acc j → hmax (j + 1) = γh * hmax j)
    (hnacc : ∀ j ≤ k, ¬ acc j → hmax (j + 1) = hmax j)
    (hc : ∀ j ≤ k, acc j → κacc * ε ^ N < hmax j) :
    ((successSet acc k).card : ℝ) ≤
      (N * |Real.log ε| + |Real.log (κacc / κh)|) / |Real.log γh| + 1 := by
  rcases hκh.lt_or_eq with hκh | hκh
  · exact card_accuracyImproving_le_of_pow hγh hγh1 hκh hκacc hε hh0 hacc hnacc hc
  · have h0 : successSet acc k = ∅ := by
      ext j
      simp only [mem_successSet, Finset.notMem_empty, iff_false, not_and]
      intro hj ha
      have := hc j hj ha
      have := hle j hj
      have : 0 < κacc * ε ^ N := by positivity
      linarith
    rw [h0, Finset.card_empty, Nat.cast_zero]
    positivity

end accuracy

section skeleton

variable {test acc : ℕ → Prop} {NT NA : ℝ}

/-- Let $\mathrm{acc}$ be a predicate on $\mathbb{N}$ (the accuracy-improving iterations) and
$k \in \mathbb{N}$. Every iteration is either a trial iteration or an accuracy-improving one:
$$|\mathcal{T}_k| + |\mathcal{A}_k| = k + 1,$$
where $\mathcal{T}_k = \{ j \le k : \lnot \mathrm{acc}(j) \}$ and $\mathcal{A}_k = \{ j \le k :
\mathrm{acc}(j) \}$. -/
theorem card_trial_add_card_acc (acc : ℕ → Prop) (k : ℕ) :
    (successSet (fun j => ¬ acc j) k).card + (successSet acc k).card = k + 1 := by
  have h := card_successSet_add_card_failureSet (succ := fun j => ¬ acc j) (k := k)
  have hfail : failureSet (fun j => ¬ acc j) k = successSet acc k := by
    ext j; simp
  rwa [hfail] at h

/-- **Complexity skeleton with accuracy-improving iterations.** Let $t$ be the termination test and
$\mathrm{acc}$ a predicate on $\mathbb{N}$ that marks the accuracy-improving iterations; the
other iterations are the trial iterations. Let $N_T \ge 0$ and $N_A \ge 0$, and suppose that at
every iteration $k$ before termination
$$|\mathcal{T}_k| \le N_T \quad\text{and}\quad |\mathcal{A}_k| \le N_A.$$
Then the method terminates at some iteration $k_\epsilon \le N_T + N_A$, and
$$|\{ j < k_\epsilon : \lnot \mathrm{acc}(j) \}| + 1 \le N_T + 1, \qquad |\{ j < k_\epsilon :
  \mathrm{acc}(j) \}| + 1 \le N_A + 1.$$
For the IDA methods, the first count is the number of function evaluations, including the
initial one.

This is the counting argument in the proofs of Theorems 13.1.8, 13.1.19, 13.3.4 and 13.3.8 of
[cartis2022evaluation]. The two counts are `Optimization.derivEvalCount` for the predicates
$\lnot \mathrm{acc}$ and $\mathrm{acc}$. -/
theorem exists_firstHit_le_of_dynamicAccuracy (hNT : 0 ≤ NT) (hNA : 0 ≤ NA)
    (hT : ∀ k, (∀ j ≤ k, ¬ test j) → ((successSet (fun j => ¬ acc j) k).card : ℝ) ≤ NT)
    (hA : ∀ k, (∀ j ≤ k, ¬ test j) → ((successSet acc k).card : ℝ) ≤ NA) :
    ∃ kε, IsFirstHit test kε ∧ (kε : ℝ) ≤ NT + NA ∧
      (derivEvalCount (fun j => ¬ acc j) kε : ℝ) ≤ NT + 1 ∧
      (derivEvalCount acc kε : ℝ) ≤ NA + 1 := by
  have hcount : ∀ k, (∀ j ≤ k, ¬ test j) →
      (k + 1 : ℝ) ≤ 1 * (successSet (fun j => ¬ acc j) k).card + NA := by
    intro k hk
    have : ((k + 1 : ℕ) : ℝ) =
        (successSet (fun j => ¬ acc j) k).card + (successSet acc k).card := by
      exact_mod_cast (card_trial_add_card_acc acc k).symm
    push_cast at this
    linarith [hA k hk]
  obtain ⟨k, hk, hkle⟩ := exists_isFirstHit_le_of_counting zero_le_one (by linarith) hcount hT
  exact ⟨k, hk, by linarith, derivEvalCount_le_of_isFirstHit hNT hk hT,
    derivEvalCount_le_of_isFirstHit hNA hk hA⟩

end skeleton

end Optimization
