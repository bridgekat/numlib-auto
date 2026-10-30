import Numlib.Optimization.Complexity.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Bounding all iterations by the successful ones

In trust-region and adaptive-regularization methods a positive parameter (the regularization
weight `σ_k` or the inverse radius `1/Δ_k`) changes multiplicatively: by a factor of at least
`γ_S ∈ (0, 1]` at successful iterations, by a factor of at least `γ_U > 1` at unsuccessful ones,
and it does not decrease at the remaining ("neutral", e.g. accuracy-improving) iterations. If the
parameter stays bounded above, the number of unsuccessful iterations is bounded in terms of the
successful ones ([cartis2022evaluation], Lemmas 2.3.1, 2.4.1 and 13.1.1, used in every later
chapter).

* `Optimization.mul_pow_card_le`: `σ_0 γ_S^{|𝒮_k|} γ_U^{|𝒰_k|} ≤ σ_{k+1}`.
* `Optimization.card_fail_mul_log_le`: if `σ_{k+1} ≤ σ_max`, then
  `|𝒰_k| log γ_U ≤ log (σ_max / σ_0) + |𝒮_k| |log γ_S|`.
* Lower-ratio (adaptive-regularization) forms: `Optimization.card_fail_le_of_lower_ratio`,
  `Optimization.succ_le_card_successSet_of_lower_ratio` (`k + 1 ≤ |𝒮_k| (1 + |log γ_S|/log γ_U) +
  log(σ_max/σ_0)/log γ_U`) and its form with the book's indexing
  `Optimization.le_card_successSet_of_lower_ratio` (Lemma 2.4.1), and
  `Optimization.card_successSet_or_le_of_lower_ratio` (Lemma 13.1.9, with neutral iterations).
* Upper-ratio (trust-region) forms, for a radius `Δ` decreasing by at least `γ₂ ∈ (0, 1)` at
  failures and increasing by at most `γ₃ ≥ 1` at successes, as long as `Δ ≥ Δ_min > 0`:
  `Optimization.card_fail_le_of_upper_ratio` (sharp constant `log (Δ_0/Δ_min)`; the book's
  `|log (Δ_min/Δ_0)|` in `Optimization.card_fail_le_of_upper_ratio_abs`),
  `Optimization.succ_le_card_successSet_of_upper_ratio`,
  `Optimization.le_card_successSet_of_upper_ratio` (Lemma 2.3.1) and
  `Optimization.card_successSet_or_le_of_upper_ratio` (Lemma 13.1.1, with neutral iterations).
  They are obtained from the lower-ratio statements applied to `σ_k = 1/Δ_k`.

The predicates `succ` and `fail` need not be complementary nor even disjoint in the general
statements; the "neutral" iterations are those satisfying neither.
-/

open Finset

namespace Optimization

section lower

variable {σ : ℕ → ℝ} {succ fail : ℕ → Prop} {γS γU σmax : ℝ} {k : ℕ}

/-- Auxiliary form of `Optimization.mul_pow_card_le`, counting with `Nat.count` over `[0, n)`. -/
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

/-- **Multiplicative parameter growth.** Let `σ_0 > 0`, `0 < γS ≤ 1 ≤ γU`, and for `j ≤ k`:
`σ_{j+1} ≥ γS σ_j` if `succ j`, `σ_{j+1} ≥ γU σ_j` if `fail j`, and `σ_{j+1} ≥ σ_j` otherwise.
Then `σ_{k+1} > 0` and `σ_0 γS^{|𝒮_k|} γU^{|𝒰_k|} ≤ σ_{k+1}`, where `𝒮_k`, `𝒰_k` are the
iterations `j ≤ k` satisfying `succ`, resp. `fail`. -/
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

/-- **Counting failures through a bounded parameter** (proof of [cartis2022evaluation],
Lemma 2.4.1, in general form). Under the hypotheses of `Optimization.mul_pow_card_le`, if
`σ_{k+1} ≤ σmax` then `|𝒰_k| log γU ≤ log (σmax / σ_0) + |𝒮_k| |log γS|`. -/
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

/-- Lower-ratio form of `Optimization.card_fail_mul_log_le` with `γU > 1`:
`|𝒰_k| ≤ |𝒮_k| |log γS| / log γU + log (σmax / σ_0) / log γU`. -/
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

/-- **Lemma 2.4.1 mechanism** (adaptive-regularization form, [cartis2022evaluation]). Let
`σ_0 > 0`, `0 < γS ≤ 1 < γU`, and for `j ≤ k`: `σ_{j+1} ≥ γS σ_j` if `succ j` and
`σ_{j+1} ≥ γU σ_j` otherwise. If `σ_{k+1} ≤ σmax`, then
`k + 1 ≤ |𝒮_k| (1 + |log γS| / log γU) + log (σmax / σ_0) / log γU`. -/
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

/-- **Lemma 2.4.1** ([cartis2022evaluation]) with the book's indexing. Let `σ_0 > 0`,
`0 < γS ≤ 1 < γU`, and for `j < k`: `σ_{j+1} ≥ γS σ_j` if `succ j` and `σ_{j+1} ≥ γU σ_j`
otherwise. If `σ_k ≤ σmax`, then
`k ≤ |𝒮_k| (1 + |log γS| / log γU) + log (σmax / σ_0) / log γU`. -/
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

/-- **Lemma 13.1.9 mechanism** ([cartis2022evaluation]): adaptive-regularization counting with
neutral iterations. Let `σ_0 > 0`, `0 < γS ≤ 1 < γU`, `succ` and `fail` incompatible, and for
`j ≤ k`: `σ_{j+1} ≥ γS σ_j` if `succ j`, `σ_{j+1} ≥ γU σ_j` if `fail j`, `σ_{j+1} ≥ σ_j`
otherwise. If `σ_{k+1} ≤ σmax`, the number `|𝒯_k|` of iterations `j ≤ k` that are successful or
failed satisfies `|𝒯_k| ≤ |𝒮_k| (1 + |log γS| / log γU) + log (σmax / σ_0) / log γU`.

The bound is needed at `σ_{k+1}`, the parameter after iteration `k`: with it only at `σ_k` the
statement fails for `k = 0`, an unsuccessful iteration `0` and `σmax = σ_0` (the left side is `1`,
the right side `0`). -/
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

/-- A sequence that shrinks by at most a positive factor at each step and is positive at
`k + 1` is positive on `[0, k + 1]`. -/
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

/-- **Counting failures through a radius bounded below** (trust-region form). Let `0 < γ₂ < 1`,
`1 ≤ γ₃` and for `j ≤ k`: `Δ_{j+1} ≤ γ₃ Δ_j` if `succ j`, `Δ_{j+1} ≤ γ₂ Δ_j` if `fail j`, and
`Δ_{j+1} ≤ Δ_j` otherwise. If `0 < Δmin ≤ Δ_{k+1}` (positivity of `Δ_0, …, Δ_k` follows), then
`|𝒰_k| ≤ |𝒮_k| log γ₃ / |log γ₂| + log (Δ_0 / Δmin) / |log γ₂|`. (This is the sharp form; the
form with `|log (Δmin / Δ_0)|` is `Optimization.card_fail_le_of_upper_ratio_abs`.) Proof: apply
`Optimization.card_fail_le_of_lower_ratio` to `σ_j = 1/Δ_j`, `γS = 1/γ₃`, `γU = 1/γ₂`. -/
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

/-- `log (a / b) ≤ |log (b / a)|`: converts the sharp trust-region bounds to the book's form. -/
theorem log_div_le_abs_log_div (a b : ℝ) : Real.log (a / b) ≤ |Real.log (b / a)| := by
  rw [← inv_div, Real.log_inv]
  exact neg_le_abs _

/-- `Optimization.card_fail_le_of_upper_ratio` with the book's constant `|log (Δmin / Δ_0)|`. -/
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

/-- **Lemma 2.3.1 mechanism** (trust-region form, [cartis2022evaluation]). Let `0 < γ₂ < 1 ≤ γ₃`
and for `j ≤ k`: `Δ_{j+1} ≤ γ₃ Δ_j` if `succ j` and `Δ_{j+1} ≤ γ₂ Δ_j` otherwise. If
`0 < Δmin ≤ Δ_{k+1}`, then
`k + 1 ≤ |𝒮_k| (1 + log γ₃ / |log γ₂|) + |log (Δmin / Δ_0)| / |log γ₂|`. -/
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

/-- **Lemma 2.3.1** ([cartis2022evaluation]) with the book's indexing. Let `0 < γ₂ < 1 ≤ γ₃` and
for `j < k`: `Δ_{j+1} ≤ γ₃ Δ_j` if `succ j` and `Δ_{j+1} ≤ γ₂ Δ_j` otherwise. If
`0 < Δmin ≤ Δ_k`, then `k ≤ |𝒮_k| (1 + log γ₃ / |log γ₂|) + |log (Δmin / Δ_0)| / |log γ₂|`. -/
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

/-- **Lemma 13.1.1 mechanism** ([cartis2022evaluation]): trust-region counting with neutral
iterations. Let `0 < γ₂ < 1 ≤ γ₃`, `succ` and `fail` incompatible, and for `j ≤ k`:
`Δ_{j+1} ≤ γ₃ Δ_j` if `succ j`, `Δ_{j+1} ≤ γ₂ Δ_j` if `fail j`, `Δ_{j+1} ≤ Δ_j` otherwise. If
`0 < Δmin ≤ Δ_{k+1}`, the number `|𝒯_k|` of iterations `j ≤ k` that are successful or failed
satisfies `|𝒯_k| ≤ |𝒮_k| (1 + log γ₃ / |log γ₂|) + |log (Δmin / Δ_0)| / |log γ₂|`.

The bound is needed at `Δ_{k+1}`, the radius after iteration `k`: with it only at `Δ_k` the
statement fails for `k = 0`, an unsuccessful iteration `0` and `Δmin = Δ_0` (the left side is `1`,
the right side `0`). -/
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
