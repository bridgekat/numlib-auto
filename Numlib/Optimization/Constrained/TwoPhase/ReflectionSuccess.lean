import Numlib.Optimization.Constrained.TwoPhase.ReflectionBlock

/-!
# Successful movement in actual reflection calls

A reflected call overshoots its old target, whereas its starting objective is
at least that target. Its endpoint therefore differs from its start. Actual
unsuccessful point updates force at least one genuine successful trial in
each such call. Counting the initial index adds at most a factor of two.
-/

namespace Constrained.TwoPhase.Reflection
open scoped BigOperators
variable {E F : Type*}
  {f : E → ℝ} {c : E → F} {x : ℕ → ℕ → E}
  {t : ℕ → ℝ} {length : ℕ → ℕ} {N : ℕ}

/-- A reset block begins above its target; every subsequent reflection also
puts its actual starting point above its new target. -/
theorem Block.start_gap_nonneg (h : Block f c x t length N)
    (hfirst : t 0 ≤ f (x 0 0))
    (hover : ∀ j < N, f (x j (length j)) < t j)
    {j : ℕ} (hj : j ≤ N) : t j ≤ f (x j 0) := by
  cases j with
  | zero => exact hfirst
  | succ j =>
    rw [h.next_point j (by omega), h.reflected_target j (by omega)]
    have hh := hover j (by omega)
    unfold reflectTarget
    linarith

/-- An actual overshooting reflection call must contain a genuine successful
trial: otherwise its unsuccessful point updates would preserve its start. -/
theorem Block.exists_success (h : Block f c x t length N)
    (S : Set (ℕ × ℕ)) (hfirst : t 0 ≤ f (x 0 0))
    (hover : ∀ j < N, f (x j (length j)) < t j)
    (hu : ∀ j < N, ∀ i < length j, (j, i) ∉ S → x j (i + 1) = x j i)
    {j : ℕ} (hj : j < N) : ∃ i < length j, (j, i) ∈ S := by
  by_contra hn
  have hnone : ∀ i < length j, (j, i) ∉ S := by
    intro i hi hs
    exact hn ⟨i, hi, hs⟩
  have hp : ∀ i ≤ length j, x j i = x j 0 := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [hu j hj i (by omega) (hnone i (by omega)), ih (by omega)]
  have hs := h.start_gap_nonneg hfirst hover hj.le
  have he := hover j hj
  rw [hp (length j) le_rfl] at he
  linarith

/-- Each actual reflection call contributes at least one genuine successful
trial, so its call count is absorbed by the genuine successful count. -/
theorem Block.calls_le_successfulCount (h : Block f c x t length N)
    (S : Set (ℕ × ℕ)) (hfirst : t 0 ≤ f (x 0 0))
    (hover : ∀ j < N, f (x j (length j)) < t j)
    (hu : ∀ j < N, ∀ i < length j, (j, i) ∉ S → x j (i + 1) = x j i) :
    N ≤ successfulCount S length N := by
  classical
  have hc (j : ℕ) (hj : j ∈ Finset.range N) : 1 ≤
      (EvaluationComplexity.successfulIterations {i | (j, i) ∈ S} (length j)).card := by
    obtain ⟨i, hi, hs⟩ := h.exists_success S hfirst hover hu (Finset.mem_range.mp hj)
    exact Finset.one_le_card.mpr ⟨i,
      EvaluationComplexity.mem_successfulIterations.mpr ⟨hi, hs⟩⟩
  simpa only [successfulCount, Finset.sum_const, Finset.card_range, smul_eq_mul,
    mul_one] using Finset.sum_le_sum hc

/-- For actual reflection calls, the source initial-or-successful convention
costs at most twice the genuine successful count, with no independent overhead. -/
theorem Block.initialOrSuccessfulCount_le_twice (h : Block f c x t length N)
    (S : Set (ℕ × ℕ)) (hfirst : t 0 ≤ f (x 0 0))
    (hover : ∀ j < N, f (x j (length j)) < t j)
    (hu : ∀ j < N, ∀ i < length j, (j, i) ∉ S → x j (i + 1) = x j i) :
    initialOrSuccessfulCount S length N ≤ 2 * successfulCount S length N := by
  have hc := h.calls_le_successfulCount S hfirst hover hu
  have hi := initialOrSuccessfulCount_le S length N
  omega

variable [NormedAddCommGroup F]

/-- Actual reflection movement absorbs every initial-index charge into twice
the genuine residual-band budget. The decrease hypotheses concern genuine
successful trials, and unsuccessful trials use their actual unchanged point. -/
theorem Block.initialOrSuccessful_le_two_band (h : Block f c x t length N)
    (S : Set (ℕ × ℕ)) {d ε θ : ℝ} (hd : 0 < d)
    (hε : 0 ≤ ε) (hθ : 0 ≤ θ)
    (hfirst : t 0 ≤ f (x 0 0))
    (hover : ∀ j < N, f (x j (length j)) < t j)
    (hupper : residualNorm f c x t 0 0 ≤ ε)
    (hlower : θ * ε ≤ residualNorm f c x t N 0)
    (hs : ∀ j < N, ∀ i < length j, (j, i) ∈ S → d ≤
      targetMerit f c (t j) (x j i) - targetMerit f c (t j) (x j (i + 1)))
    (hu : ∀ j < N, ∀ i < length j, (j, i) ∉ S → x j (i + 1) = x j i) :
    (initialOrSuccessfulCount S length N : ℝ) ≤ 2 * (1 - θ) * ε ^ 2 / d := by
  have hb := h.successful_le_band S hd hε hθ hupper hlower hs
    (fun j hj i hi hn => by rw [hu j hj i hi hn])
  have hc : (initialOrSuccessfulCount S length N : ℝ) ≤
      2 * (successfulCount S length N : ℝ) := by
    exact_mod_cast h.initialOrSuccessfulCount_le_twice S hfirst hover hu
  calc
    _ ≤ 2 * (successfulCount S length N : ℝ) := hc
    _ ≤ 2 * ((1 - θ) * ε ^ 2 / d) := by linarith
    _ = _ := by ring

end Constrained.TwoPhase.Reflection
