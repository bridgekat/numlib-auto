import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Safe finite counts for quadratic recurrences

A positive correction inside the double logarithm accounts for the first
quadratic step and makes the iteration bound valid even near the initial
accuracy. Every budget is a natural number, including an initial successful test.
-/

namespace EvaluationComplexity

/-- A nonnegative finite quadratic recurrence contracts by the explicit
power-of-two exponent, with every endpoint included. -/
theorem quadratic_recurrence_bound {g : ℕ → ℝ} {c ζ : ℝ} {N : ℕ}
    (hc : 0 ≤ c) (hζ : 0 ≤ ζ) (hstart : g 0 ≤ ζ) (hsmall : c * ζ ≤ 1 / 2)
    (hpos : ∀ n ≤ N, 0 ≤ g n) (hrec : ∀ n < N, g (n + 1) ≤ c * (g n) ^ 2) :
    ∀ n ≤ N, g n ≤ 2 * ζ * (1 / 2 : ℝ) ^ ((2 : ℕ) ^ n) := by
  intro n
  induction n with
  | zero => intro _; convert hstart using 1; ring
  | succ n ih =>
    intro hn
    have hi := ih (by omega)
    have hsq := pow_le_pow_left₀ (hpos n (by omega)) hi 2
    have hs := mul_le_mul_of_nonneg_left hsq hc
    have hcoef : c * (2 * ζ) ^ 2 ≤ 2 * ζ := by
      have hh := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ 4 * ζ by positivity)
      nlinarith
    have he : ((1 / 2 : ℝ) ^ ((2 : ℕ) ^ n)) ^ 2 = (1 / 2 : ℝ) ^ ((2 : ℕ) ^ (n + 1)) := by
      rw [← pow_mul, pow_succ]
    calc
      g (n + 1) ≤ c * (g n) ^ 2 := hrec n (by omega)
      _ ≤ c * (2 * ζ * (1 / 2 : ℝ) ^ ((2 : ℕ) ^ n)) ^ 2 := hs
      _ = c * (2 * ζ) ^ 2 * (1 / 2 : ℝ) ^ ((2 : ℕ) ^ (n + 1)) := by rw [mul_pow, he]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)

/-- The corrected natural double-logarithm iteration budget, for every
positive requested accuracy without a negative or zero-count artifact. -/
noncomputable def quadraticIterationBudget (ζ ε : ℝ) : ℕ :=
  ⌈Real.logb 2 (1 + max 0 (Real.logb 2 (ζ / ε)))⌉₊

/-- The explicit corrected budget makes the finite recurrence accuracy pass,
including accuracies at least as large as the initialized gradient bound. -/
theorem quadraticIterationBudget_sufficient {g : ℕ → ℝ} {c ζ ε : ℝ}
    (hc : 0 ≤ c) (hζ : 0 < ζ) (hε : 0 < ε) (hstart : g 0 ≤ ζ)
    (hsmall : c * ζ ≤ 1 / 2)
    (hpos : ∀ n ≤ quadraticIterationBudget ζ ε, 0 ≤ g n)
    (hrec : ∀ n < quadraticIterationBudget ζ ε, g (n + 1) ≤ c * (g n) ^ 2) :
    g (quadraticIterationBudget ζ ε) ≤ ε := by
  let N := quadraticIterationBudget ζ ε
  have hN : Real.logb 2 (1 + max 0 (Real.logb 2 (ζ / ε))) ≤ (N : ℝ) :=
    Nat.le_ceil _
  have hbound := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2)
    (show 0 < 1 + max 0 (Real.logb 2 (ζ / ε)) by positivity)).mp hN
  rw [Real.rpow_natCast] at hbound
  have hlog : Real.logb 2 (2 * ζ / ε) ≤ (Nat.cast ((2 : ℕ) ^ N) : ℝ) := by
    have he : 2 * ζ / ε = 2 * (ζ / ε) := by ring
    rw [he, Real.logb_mul (by norm_num) (div_ne_zero hζ.ne' hε.ne')]
    rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2)]
    have hm := le_max_right (0 : ℝ) (Real.logb 2 (ζ / ε))
    have hb : 1 + max 0 (Real.logb 2 (ζ / ε)) ≤ (Nat.cast ((2 : ℕ) ^ N) : ℝ) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hbound
    linarith only [hm, hb]
  have hexp := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2)
    (show 0 < 2 * ζ / ε by positivity)).mp hlog
  rw [Real.rpow_natCast] at hexp
  have hh := quadratic_recurrence_bound hc hζ.le hstart hsmall hpos hrec N le_rfl
  have hd : 0 < (2 : ℝ) ^ ((2 : ℕ) ^ N) := by positivity
  have he : 2 * ζ * (1 / 2 : ℝ) ^ ((2 : ℕ) ^ N) = 2 * ζ / (2 : ℝ) ^ ((2 : ℕ) ^ N) := by
    rw [div_pow, one_pow, div_eq_mul_inv, div_eq_mul_inv, one_mul]
  rw [he] at hh
  apply hh.trans
  apply (div_le_iff₀ hd).mpr
  have hm := (div_le_iff₀ hε).mp hexp
  nlinarith

/-- A globally defined actual quadratic recurrence reaches its first target
within the safe explicit natural budget. -/
theorem exists_first_quadratic_target {g : ℕ → ℝ} {c ζ ε : ℝ}
    (hc : 0 ≤ c) (hζ : 0 < ζ) (hε : 0 < ε) (hstart : g 0 ≤ ζ)
    (hsmall : c * ζ ≤ 1 / 2) (hpos : ∀ n, 0 ≤ g n)
    (hrec : ∀ n, g (n + 1) ≤ c * (g n) ^ 2) :
    ∃ K ≤ quadraticIterationBudget ζ ε, g K ≤ ε ∧ ∀ k < K, ε < g k := by
  have hex : ∃ n, g n ≤ ε := ⟨quadraticIterationBudget ζ ε,
    quadraticIterationBudget_sufficient hc hζ hε hstart hsmall
      (fun n _ => hpos n) (fun n _ => hrec n)⟩
  refine ⟨Nat.find hex, Nat.find_min' hex ?_, Nat.find_spec hex, ?_⟩
  · exact quadraticIterationBudget_sufficient hc hζ hε hstart hsmall
      (fun n _ => hpos n) (fun n _ => hrec n)
  · intro k hk
    exact lt_of_not_ge (Nat.find_min hex hk)

end EvaluationComplexity
