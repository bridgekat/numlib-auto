import Numlib.Optimization.Constrained.TwoPhase.Target
import Numlib.Optimization.EvaluationComplexity.Decrease

/-!
# Actual target-reflection chains and their finite budgets

Consecutive inner calls share their endpoint and starting point, while the
literal reflection update preserves the actual residual norm and merit.
Telescoping therefore crosses call boundaries without an assumed identity.
Genuine successful trials and the source convention adding each initial
inner index have separate counts; the latter has an explicit call overhead.
-/

noncomputable section
namespace Constrained.TwoPhase.Reflection
open scoped BigOperators
variable {E F : Type*} [NormedAddCommGroup F]

/-- The actual augmented residual norm along a two-index inner-call array. -/
def residualNorm (f : E → ℝ) (c : E → F) (x : ℕ → ℕ → E)
    (t : ℕ → ℝ) (j i : ℕ) : ℝ := ‖residual f c (t j) (x j i)‖

/-- Consecutive actual inner endpoints are reused, and each target obeys the
literal reflection formula. No decrease or count estimate is a field. -/
structure Block (f : E → ℝ) (c : E → F) (x : ℕ → ℕ → E)
    (t : ℕ → ℝ) (length : ℕ → ℕ) (N : ℕ) : Prop where
  next_point : ∀ j < N, x (j + 1) 0 = x j (length j)
  reflected_target : ∀ j < N, t (j + 1) = reflectTarget f (t j) (x j (length j))

/-- The actual successful count over all individual inner-call prefixes. -/
def successfulCount (S : Set (ℕ × ℕ)) (length : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ j ∈ Finset.range N,
    (EvaluationComplexity.successfulIterations {i | (j, i) ∈ S} (length j)).card

/-- The source's initial-or-successful index count, which also counts index
zero of each nonempty call even if that trial is unsuccessful. -/
def initialOrSuccessfulCount (S : Set (ℕ × ℕ)) (length : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ j ∈ Finset.range N,
    (EvaluationComplexity.successfulIterations {i | i = 0 ∨ (j, i) ∈ S} (length j)).card

variable {f : E → ℝ} {c : E → F} {x : ℕ → ℕ → E}
  {t : ℕ → ℝ} {length : ℕ → ℕ} {N : ℕ}

/-- The operational point and target updates derive the actual residual-norm
identity across every reflected call boundary. -/
theorem Block.residual_bridge (h : Block f c x t length N) {j : ℕ} (hj : j < N) :
    residualNorm f c x t (j + 1) 0 = residualNorm f c x t j (length j) := by
  unfold residualNorm
  rw [h.next_point j hj, h.reflected_target j hj, residual_reflect]

/-- The operational reflection also preserves the genuine least-squares merit. -/
theorem Block.merit_bridge (h : Block f c x t length N) {j : ℕ} (hj : j < N) :
    targetMerit f c (t (j + 1)) (x (j + 1) 0) =
      targetMerit f c (t j) (x j (length j)) := by
  simp only [targetMerit_eq_residual]
  rw [show ‖residual f c (t (j + 1)) (x (j + 1) 0)‖ =
    ‖residual f c (t j) (x j (length j))‖ from h.residual_bridge hj]

/-- Actual residual differences telescope through every reflected call. -/
theorem Block.sum_residual_decrease (h : Block f c x t length N) :
    (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (length j),
      (residualNorm f c x t j i - residualNorm f c x t j (i + 1))) =
        residualNorm f c x t 0 0 - residualNorm f c x t N 0 := by
  calc
    _ = ∑ j ∈ Finset.range N,
        (residualNorm f c x t j 0 - residualNorm f c x t (j + 1) 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_range_sub', h.residual_bridge (Finset.mem_range.mp hj)]
    _ = _ := Finset.sum_range_sub' (fun j => residualNorm f c x t j 0) N

/-- Actual merit differences telescope through every reflected call. -/
theorem Block.sum_merit_decrease (h : Block f c x t length N) :
    (∑ j ∈ Finset.range N,
      (targetMerit f c (t j) (x j 0) - targetMerit f c (t j) (x j (length j)))) =
        targetMerit f c (t 0) (x 0 0) - targetMerit f c (t N) (x N 0) := by
  calc
    _ = ∑ j ∈ Finset.range N,
        (targetMerit f c (t j) (x j 0) - targetMerit f c (t (j + 1)) (x (j + 1) 0)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [h.merit_bridge (Finset.mem_range.mp hj)]
    _ = _ := Finset.sum_range_sub' (fun j => targetMerit f c (t j) (x j 0)) N

/-- A positive per-successful-trial merit decrease consumes the actual common
merit budget across target reflections. All other trials merely need nonincrease. -/
theorem Block.successful_mul_le_gap (h : Block f c x t length N)
    (S : Set (ℕ × ℕ)) {d : ℝ}
    (hs : ∀ j < N, ∀ i < length j, (j, i) ∈ S → d ≤
      targetMerit f c (t j) (x j i) - targetMerit f c (t j) (x j (i + 1)))
    (hu : ∀ j < N, ∀ i < length j, (j, i) ∉ S →
      targetMerit f c (t j) (x j (i + 1)) ≤ targetMerit f c (t j) (x j i)) :
    (successfulCount S length N : ℝ) * d ≤
      targetMerit f c (t 0) (x 0 0) - targetMerit f c (t N) (x N 0) := by
  rw [← h.sum_merit_decrease]
  unfold successfulCount
  rw [Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  exact EvaluationComplexity.card_successful_mul_le_gap le_rfl
    (hs j (Finset.mem_range.mp hj)) (hu j (Finset.mem_range.mp hj))

/-- The actual residual band bounds its common merit budget by the source's
`(1-theta) * epsilon^2` coefficient. -/
theorem merit_gap_le_of_band {ε θ : ℝ} (hε : 0 ≤ ε) (hθ : 0 ≤ θ)
    (hfirst : residualNorm f c x t 0 0 ≤ ε)
    (hlast : θ * ε ≤ residualNorm f c x t N 0) :
    targetMerit f c (t 0) (x 0 0) - targetMerit f c (t N) (x N 0) ≤
      (1 - θ) * ε ^ 2 := by
  have h0 : 0 ≤ residualNorm f c x t 0 0 := norm_nonneg _
  have hN : 0 ≤ residualNorm f c x t N 0 := norm_nonneg _
  have hup := pow_le_pow_left₀ h0 hfirst 2
  have hlo := pow_le_pow_left₀ (mul_nonneg hθ hε) hlast 2
  simp only [targetMerit_eq_residual]
  change residualNorm f c x t 0 0 ^ 2 / 2 - residualNorm f c x t N 0 ^ 2 / 2 ≤ _
  nlinarith [sq_nonneg ((1 - θ) * ε)]

/-- Genuine successful trials obey the residual-band cardinality bound. -/
theorem Block.successful_le_band (h : Block f c x t length N)
    (S : Set (ℕ × ℕ)) {d ε θ : ℝ} (hd : 0 < d)
    (hε : 0 ≤ ε) (hθ : 0 ≤ θ)
    (hfirst : residualNorm f c x t 0 0 ≤ ε)
    (hlast : θ * ε ≤ residualNorm f c x t N 0)
    (hs : ∀ j < N, ∀ i < length j, (j, i) ∈ S → d ≤
      targetMerit f c (t j) (x j i) - targetMerit f c (t j) (x j (i + 1)))
    (hu : ∀ j < N, ∀ i < length j, (j, i) ∉ S →
      targetMerit f c (t j) (x j (i + 1)) ≤ targetMerit f c (t j) (x j i)) :
    (successfulCount S length N : ℝ) ≤ (1 - θ) * ε ^ 2 / d := by
  apply (le_div_iff₀ hd).mpr
  exact (h.successful_mul_le_gap S hs hu).trans
    (merit_gap_le_of_band hε hθ hfirst hlast)

/-- Counting each initial index adds at most one index per INNER call. -/
theorem initialOrSuccessfulCount_le (S : Set (ℕ × ℕ)) (length : ℕ → ℕ) (N : ℕ) :
    initialOrSuccessfulCount S length N ≤ N + successfulCount S length N := by
  classical
  have hcard (j : ℕ) :
      (EvaluationComplexity.successfulIterations {i | i = 0 ∨ (j, i) ∈ S}
        (length j)).card ≤
      (EvaluationComplexity.successfulIterations {i | (j, i) ∈ S} (length j)).card + 1 := by
    apply (Finset.card_le_card (show EvaluationComplexity.successfulIterations
      {i | i = 0 ∨ (j, i) ∈ S} (length j) ⊆
      insert 0 (EvaluationComplexity.successfulIterations
        {i | (j, i) ∈ S} (length j)) from ?_)).trans
      (Finset.card_insert_le _ _)
    intro i hi
    obtain ⟨hi, he | hs⟩ := EvaluationComplexity.mem_successfulIterations.mp hi
    · subst i
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (EvaluationComplexity.mem_successfulIterations.mpr ⟨hi, hs⟩)
  calc
    _ ≤ ∑ j ∈ Finset.range N,
        ((EvaluationComplexity.successfulIterations {i | (j, i) ∈ S} (length j)).card + 1) :=
      Finset.sum_le_sum (fun j _ => hcard j)
    _ = _ := by simp [successfulCount, Finset.sum_add_distrib, Nat.add_comm]

/-- The literal reset formula gives the exact initial residual of a block
following a reset, with no assumed residual identity. -/
theorem reset_initial_residual {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ‖c (x 0 0)‖ ≤ ε) (ht : t 0 = resetTarget f c ε (x 0 0)) :
    residualNorm f c x t 0 0 = ε := by
  unfold residualNorm
  rw [ht]
  exact residual_reset hε hc

/-- The source's initial-or-successful convention has a valid band budget
with the explicit number of INNER calls retained as overhead. This separates
that bookkeeping cost from genuine successful-trial decrease. -/
theorem Block.initialOrSuccessful_le_band (h : Block f c x t length N)
    (S : Set (ℕ × ℕ)) {d ε θ : ℝ} (hd : 0 < d)
    (hε : 0 ≤ ε) (hθ : 0 ≤ θ)
    (hfirst : residualNorm f c x t 0 0 ≤ ε)
    (hlast : θ * ε ≤ residualNorm f c x t N 0)
    (hs : ∀ j < N, ∀ i < length j, (j, i) ∈ S → d ≤
      targetMerit f c (t j) (x j i) - targetMerit f c (t j) (x j (i + 1)))
    (hu : ∀ j < N, ∀ i < length j, (j, i) ∉ S →
      targetMerit f c (t j) (x j (i + 1)) ≤ targetMerit f c (t j) (x j i)) :
    (initialOrSuccessfulCount S length N : ℝ) ≤ (N : ℝ) + (1 - θ) * ε ^ 2 / d := by
  calc
    _ ≤ (N : ℝ) + successfulCount S length N := by
      exact_mod_cast initialOrSuccessfulCount_le S length N
    _ ≤ _ := by
      have hb := h.successful_le_band S hd hε hθ hfirst hlast hs hu
      linarith

end Constrained.TwoPhase.Reflection
