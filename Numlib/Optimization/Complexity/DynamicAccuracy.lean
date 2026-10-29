import Numlib.Optimization.ModelBased.TrustRegionUpdate
import Numlib.Optimization.ModelBased.RegularizationUpdate

/-!
# Counting with accuracy-improving iterations

The dynamic-accuracy methods of [cartis2022evaluation] (Chapter 13: TRqIDA, ARqpIDA, TRqEDA,
ARqpEDA) have three kinds of iterations: successful (`𝒮`) and unsuccessful (`𝒰`) ones, together
the *trial* iterations `𝒯 = 𝒮 ∪ 𝒰` that evaluate the objective once, and *accuracy-improving*
ones (`𝒜`) that multiply the requested accuracies by `γ_h ∈ (0, 1)` and leave the iterate and the
trust-region radius (or the regularization parameter) unchanged. The radius and regularization
bounds allowing such *neutral* iterations are `Optimization.le_delta_of_trUpdate_of_neutral` and
`Optimization.sigma_le_max_of_arUpdate_of_neutral` (in `ModelBased/TrustRegionUpdate` and
`ModelBased/RegularizationUpdate`). This file contains the counting arguments.

* `Optimization.card_accuracyImproving_le`: the number of accuracy-improving iterations is at most
  `⌈log (c / κ_h) / log γ_h⌉₊` if such an iteration can only happen while the largest requested
  accuracy exceeds `c` (the root `i_{h,ε}` in the proofs of Theorems 13.1.8, 13.1.19).
* `Optimization.card_trial_add_card_acc`: every iteration is a trial or an accuracy-improving one.
* `Optimization.exists_firstHit_le_of_dynamicAccuracy`: the complexity skeleton: bounds on the
  numbers of trial and of accuracy-improving iterations before termination bound the termination
  index and the evaluation counts.

The counts of Lemmas 13.1.1 and 13.1.9 (trial iterations in terms of successful ones) are the
core `Optimization.card_successSet_or_le_of_upper_ratio` and
`Optimization.card_successSet_or_le_of_lower_ratio`, which already allow neutral iterations.
-/

open Finset

namespace Optimization

section accuracy

variable {acc : ℕ → Prop} {hmax : ℕ → ℝ} {γh κh c : ℝ}

/-- The requested accuracy after `k + 1` iterations is `γ_h^{|𝒜_k|} h_0`, and while it exceeds `c`
at every accuracy-improving iteration, `c < γ_h^{|𝒜_k| - 1} κ_h` unless `𝒜_k = ∅`. -/
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

/-- **Number of accuracy-improving iterations** ([cartis2022evaluation], proofs of
Theorems 13.1.8, 13.1.19: the root `i_{h,ε}`). Let the largest requested accuracy `h_max` satisfy
`h_max(0) ≤ κ_h`, be multiplied by `γ_h ∈ (0, 1)` at accuracy-improving iterations `j ≤ k` and
be unchanged at the other iterations `j ≤ k`, and let `0 < c`, `0 < κ_h`. If every
accuracy-improving iteration `j ≤ k` has `c < h_max(j)`, then the number of accuracy-improving
iterations in `[0, k]` is at most `⌈log (c / κ_h) / log γ_h⌉₊`. -/
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

/-- Real form of `Optimization.card_accuracyImproving_le`:
`|𝒜_k| ≤ |log (c / κ_h)| / |log γ_h| + 1`. -/
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

/-- The book's form of `Optimization.card_accuracyImproving_le` ([cartis2022evaluation], (13.1.44)):
if the threshold is `c = κ_acc ε^N` with `ε, κ_acc > 0`, then
`|𝒜_k| ≤ (N |log ε| + |log (κ_acc / κ_h)|) / |log γ_h| + 1`. -/
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

/-- `card_accuracyImproving_le_of_pow` allowing `κ_h = 0`: if moreover
`h_max(j) ≤ κ_h` for `j ≤ k`, then for `κ_h = 0` no iteration is accuracy-improving (the threshold
`κ_acc ε^N` is positive), and the bound holds with `log(κ_acc/0) = 0`. -/
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

/-- Every iteration is a trial iteration or an accuracy-improving one: `|𝒯_k| + |𝒜_k| = k + 1`,
where `𝒯_k = {j ≤ k | ¬ acc j}` and `𝒜_k = {j ≤ k | acc j}`. -/
theorem card_trial_add_card_acc (acc : ℕ → Prop) (k : ℕ) :
    (successSet (fun j => ¬ acc j) k).card + (successSet acc k).card = k + 1 := by
  have h := card_successSet_add_card_failureSet (succ := fun j => ¬ acc j) (k := k)
  have hfail : failureSet (fun j => ¬ acc j) k = successSet acc k := by
    ext j; simp
  rwa [hfail] at h

/-- **Complexity skeleton with accuracy-improving iterations** ([cartis2022evaluation], proofs of
Theorems 13.1.8, 13.1.19, 13.3.4, 13.3.8). Let `acc k` mark the accuracy-improving iterations and
`¬ acc k` the trial ones. Suppose that at every iteration `k` before termination, the numbers of
trial and of accuracy-improving iterations in `[0, k]` are at most `NT ≥ 0` and `NA ≥ 0`. Then the
method terminates at some `kε ≤ NT + NA`, and before `kε` at most `NT` trial and at most `NA`
accuracy-improving iterations took place: `derivEvalCount (¬ acc) kε ≤ NT + 1` (the function
evaluations of IDA methods, including the initial one) and `derivEvalCount acc kε ≤ NA + 1`. -/
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
