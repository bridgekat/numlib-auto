import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Counting successful and unsuccessful iterations

A run is described by its set of successful iteration indices. All counts use the
half-open prefix `0 ≤ i < k`, so that exactly `k` updates have occurred. Bounds on an
additive potential telescope; logarithms then give the standard iteration counts for
trust-region radii and adaptive regularization parameters.
-/

open scoped BigOperators

namespace EvaluationComplexity

/-- Successful iterations among the first `k` updates. -/
noncomputable def successfulIterations (S : Set ℕ) (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range k).filter (· ∈ S)

/-- Unsuccessful iterations among the first `k` updates. -/
noncomputable def unsuccessfulIterations (S : Set ℕ) (k : ℕ) : Finset ℕ :=
  successfulIterations Sᶜ k

/-- Membership in the successful prefix means both the prefix bound and success. -/
@[simp]
theorem mem_successfulIterations {S : Set ℕ} {k i : ℕ} :
    i ∈ successfulIterations S k ↔ i < k ∧ i ∈ S := by
  classical
  simp [successfulIterations]

/-- Membership in the unsuccessful prefix means the prefix bound and failure. -/
@[simp]
theorem mem_unsuccessfulIterations {S : Set ℕ} {k i : ℕ} :
    i ∈ unsuccessfulIterations S k ↔ i < k ∧ i ∉ S := by
  simp [unsuccessfulIterations]

/-- The two classes partition the first `k` iteration indices. -/
theorem card_successful_add_card_unsuccessful (S : Set ℕ) (k : ℕ) :
    (successfulIterations S k).card + (unsuccessfulIterations S k).card = k := by
  classical
  simpa [successfulIterations, unsuccessfulIterations] using
    (Finset.card_filter_add_card_filter_not (s := Finset.range k) (· ∈ S))

/-- Telescoping an upper bound for each change in a potential, with a separate
constant for successful and unsuccessful steps. -/
theorem potential_change_le {S : Set ℕ} {v : ℕ → ℝ} {a b : ℝ} {k : ℕ}
    (hs : ∀ i < k, i ∈ S → v (i + 1) - v i ≤ a)
    (hu : ∀ i < k, i ∉ S → v (i + 1) - v i ≤ b) :
    v k - v 0 ≤ (successfulIterations S k).card * a +
      (unsuccessfulIterations S k).card * b := by
  classical
  calc
    v k - v 0 = ∑ i ∈ Finset.range k, (v (i + 1) - v i) :=
      (Finset.sum_range_sub v k).symm
    _ ≤ ∑ i ∈ Finset.range k, if i ∈ S then a else b := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs with h
      · exact hs i (Finset.mem_range.mp hi) h
      · exact hu i (Finset.mem_range.mp hi) h
    _ = _ := by simp [Finset.sum_ite, successfulIterations, unsuccessfulIterations]

/-- Telescoping a lower bound for the change in an additive potential. -/
theorem le_potential_change {S : Set ℕ} {v : ℕ → ℝ} {a b : ℝ} {k : ℕ}
    (hs : ∀ i < k, i ∈ S → a ≤ v (i + 1) - v i)
    (hu : ∀ i < k, i ∉ S → b ≤ v (i + 1) - v i) :
    (successfulIterations S k).card * a +
      (unsuccessfulIterations S k).card * b ≤ v k - v 0 := by
  have h := potential_change_le (S := S) (v := fun i => -v i) (a := -a) (b := -b)
    (k := k) (fun i hi hS => by linarith [hs i hi hS])
    (fun i hi hS => by linarith [hu i hi hS])
  linarith

/-- A lower bound on a shrinking parameter controls the total number of updates.
Successful updates can enlarge it by at most `γs`, and unsuccessful updates shrink
it by at least the factor `γu < 1`. -/
theorem iteration_bound_of_parameter_lower {S : Set ℕ} {δ : ℕ → ℝ}
    {γs γu δmin : ℝ} {k : ℕ} (hδ : ∀ i ≤ k, 0 < δ i)
    (hγs : 0 < γs) (hγu : 0 < γu) (hγu1 : γu < 1)
    (hmin : δmin ≤ δ k) (hminpos : 0 < δmin)
    (hs : ∀ i < k, i ∈ S → δ (i + 1) ≤ γs * δ i)
    (hu : ∀ i < k, i ∉ S → δ (i + 1) ≤ γu * δ i) :
    (k : ℝ) ≤ (successfulIterations S k).card *
        (1 + Real.log γs / |Real.log γu|) +
      |Real.log (δmin / δ 0)| / |Real.log γu| := by
  have hstep (i : ℕ) (hi : i < k) (γ : ℝ) (hγ : 0 < γ)
      (h : δ (i + 1) ≤ γ * δ i) :
      Real.log (δ (i + 1)) - Real.log (δ i) ≤ Real.log γ := by
    have he := Real.log_le_log (hδ (i + 1) (by omega)) h
    rw [Real.log_mul hγ.ne' (hδ i (by omega)).ne'] at he
    linarith
  have htel := potential_change_le (S := S) (v := fun i => Real.log (δ i))
    (fun i hi hS => hstep i hi γs hγs (hs i hi hS))
    (fun i hi hS => hstep i hi γu hγu (hu i hi hS))
  have hlog := Real.log_le_log hminpos hmin
  have hneg := Real.log_neg hγu hγu1
  have habs : |Real.log γu| = -Real.log γu := abs_of_neg hneg
  have hpos : 0 < |Real.log γu| := abs_pos.mpr hneg.ne
  have hratio : Real.log (δmin / δ 0) = Real.log δmin - Real.log (δ 0) :=
    Real.log_div hminpos.ne' (hδ 0 (Nat.zero_le _)).ne'
  have habsratio := neg_abs_le (Real.log (δmin / δ 0))
  have hcard : (k : ℝ) = (successfulIterations S k).card +
      (unsuccessfulIterations S k).card := by
    exact_mod_cast (card_successful_add_card_unsuccessful S k).symm
  apply (mul_le_mul_iff_of_pos_right hpos).mp
  rw [add_mul, div_mul_cancel₀ _ hpos.ne']
  have he : (successfulIterations S k).card *
      (1 + Real.log γs / |Real.log γu|) * |Real.log γu| =
      (successfulIterations S k).card * (|Real.log γu| + Real.log γs) := by
    field_simp
  rw [he, hcard]
  rw [habs] at *
  nlinarith

/-- An upper bound on a growing parameter controls the total number of updates.
Successful updates can reduce it by at most a factor `γs`, while unsuccessful
updates increase it by at least `γu > 1`. -/
theorem iteration_bound_of_parameter_upper {S : Set ℕ} {σ : ℕ → ℝ}
    {γs γu σmax : ℝ} {k : ℕ} (hσ : ∀ i ≤ k, 0 < σ i)
    (hγs : 0 < γs) (hγs1 : γs < 1) (hγu : 1 < γu)
    (hmax : σ k ≤ σmax)
    (hs : ∀ i < k, i ∈ S → γs * σ i ≤ σ (i + 1))
    (hu : ∀ i < k, i ∉ S → γu * σ i ≤ σ (i + 1)) :
    (k : ℝ) ≤ (successfulIterations S k).card *
        (1 + |Real.log γs| / Real.log γu) +
      Real.log (σmax / σ 0) / Real.log γu := by
  have hstep (i : ℕ) (hi : i < k) (γ : ℝ) (hγ : 0 < γ)
      (h : γ * σ i ≤ σ (i + 1)) :
      Real.log γ ≤ Real.log (σ (i + 1)) - Real.log (σ i) := by
    have he := Real.log_le_log (mul_pos hγ (hσ i (by omega))) h
    rw [Real.log_mul hγ.ne' (hσ i (by omega)).ne'] at he
    linarith
  have htel := le_potential_change (S := S) (v := fun i => Real.log (σ i))
    (fun i hi hS => hstep i hi γs hγs (hs i hi hS))
    (fun i hi hS => hstep i hi γu (by linarith) (hu i hi hS))
  have hlog := Real.log_le_log (hσ k le_rfl) hmax
  have hpos := Real.log_pos hγu
  have habs : |Real.log γs| = -Real.log γs := abs_of_neg (Real.log_neg hγs hγs1)
  have hratio : Real.log (σmax / σ 0) = Real.log σmax - Real.log (σ 0) :=
    Real.log_div (lt_of_lt_of_le (hσ k le_rfl) hmax).ne'
      (hσ 0 (Nat.zero_le _)).ne'
  have hcard : (k : ℝ) = (successfulIterations S k).card +
      (unsuccessfulIterations S k).card := by
    exact_mod_cast (card_successful_add_card_unsuccessful S k).symm
  apply (mul_le_mul_iff_of_pos_right hpos).mp
  rw [add_mul, div_mul_cancel₀ _ hpos.ne']
  have he : (successfulIterations S k).card *
      (1 + |Real.log γs| / Real.log γu) * Real.log γu =
      (successfulIterations S k).card * (Real.log γu + |Real.log γs|) := by
    field_simp
  rw [he, hcard, habs, hratio]
  nlinarith

end EvaluationComplexity
