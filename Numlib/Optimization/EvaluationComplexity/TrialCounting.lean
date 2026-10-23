import Numlib.Optimization.EvaluationComplexity.Updates

/-!
# Counting parameter updates when some iterations only improve accuracy

The trial set `T` splits into successful and unsuccessful trials. Iterations outside `T`
leave the parameter unchanged and contribute zero to its additive log potential.
Every prefix here is half-open: the first `N` updates end at parameter index `N`.
-/

namespace EvaluationComplexity

/-- The successful and unsuccessful trial counts partition the trial count. -/
theorem card_trials_eq_add {S T : Set ℕ} (hST : S ⊆ T) (N : ℕ) :
    (successfulIterations T N).card = (successfulIterations S N).card +
      (successfulIterations (T \ S) N).card := by
  classical
  have hs : ((successfulIterations T N).filter (· ∈ S)) = successfulIterations S N := by
    ext i
    simp only [Finset.mem_filter, mem_successfulIterations]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hST h.2⟩, h.2⟩⟩
  have hu : ((successfulIterations T N).filter (· ∉ S)) =
      successfulIterations (T \ S) N := by
    ext i
    simp only [Finset.mem_filter, mem_successfulIterations, Set.mem_sdiff]
    tauto
  have h := Finset.card_filter_add_card_filter_not (s := successfulIterations T N) (· ∈ S)
  rw [hs, hu] at h
  exact h.symm

/-- An additive potential counts successful and unsuccessful trials, while all other iterations
leave it unchanged. -/
theorem potential_change_le_on_trials {S T : Set ℕ} {v : ℕ → ℝ} {a b : ℝ} {N : ℕ}
    (hs : ∀ i < N, i ∈ S → v (i + 1) - v i ≤ a)
    (hu : ∀ i < N, i ∈ T → i ∉ S → v (i + 1) - v i ≤ b)
    (ha : ∀ i < N, i ∉ T → v (i + 1) = v i) :
    v N - v 0 ≤ (successfulIterations S N).card * a +
      (successfulIterations (T \ S) N).card * b := by
  classical
  calc
    v N - v 0 = ∑ i ∈ Finset.range N, (v (i + 1) - v i) :=
      (Finset.sum_range_sub v N).symm
    _ ≤ ∑ i ∈ Finset.range N,
        ((if i ∈ S then a else 0) + (if i ∈ T \ S then b else 0)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      by_cases hS : i ∈ S
      · simpa [hS, Set.mem_sdiff] using hs i hi' hS
      · by_cases hT : i ∈ T
        · simpa [hS, hT, Set.mem_sdiff] using hu i hi' hT hS
        · simp [hS, hT, ha i hi' hT]
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_ite, successfulIterations]

/-- The lower-potential form of the trial telescoping estimate. -/
theorem le_potential_change_on_trials {S T : Set ℕ} {v : ℕ → ℝ} {a b : ℝ} {N : ℕ}
    (hs : ∀ i < N, i ∈ S → a ≤ v (i + 1) - v i)
    (hu : ∀ i < N, i ∈ T → i ∉ S → b ≤ v (i + 1) - v i)
    (ha : ∀ i < N, i ∉ T → v (i + 1) = v i) :
    (successfulIterations S N).card * a +
      (successfulIterations (T \ S) N).card * b ≤ v N - v 0 := by
  have h := potential_change_le_on_trials (v := fun i => -v i) (a := -a) (b := -b)
    (fun i hi hS => by linarith [hs i hi hS])
    (fun i hi hT hS => by linarith [hu i hi hT hS])
    (fun i hi hT => by rw [ha i hi hT])
  linarith

/-- A lower bound on a shrinking parameter bounds the number of its trial updates. -/
theorem iteration_bound_of_parameter_lower_on_trials {S T : Set ℕ} {δ : ℕ → ℝ}
    {γs γu δmin : ℝ} {N : ℕ} (hST : S ⊆ T) (hδ : ∀ i ≤ N, 0 < δ i)
    (hγs : 0 < γs) (hγu : 0 < γu) (hγu1 : γu < 1)
    (hmin : δmin ≤ δ N) (hminpos : 0 < δmin)
    (hs : ∀ i < N, i ∈ S → δ (i + 1) ≤ γs * δ i)
    (hu : ∀ i < N, i ∈ T → i ∉ S → δ (i + 1) ≤ γu * δ i)
    (ha : ∀ i < N, i ∉ T → δ (i + 1) = δ i) :
    ((successfulIterations T N).card : ℝ) ≤ (successfulIterations S N).card *
        (1 + Real.log γs / |Real.log γu|) +
      |Real.log (δmin / δ 0)| / |Real.log γu| := by
  have hstep (i : ℕ) (hi : i < N) (γ : ℝ) (hγ : 0 < γ)
      (h : δ (i + 1) ≤ γ * δ i) :
      Real.log (δ (i + 1)) - Real.log (δ i) ≤ Real.log γ := by
    have he := Real.log_le_log (hδ (i + 1) (by omega)) h
    rw [Real.log_mul hγ.ne' (hδ i (by omega)).ne'] at he
    linarith
  have htel := potential_change_le_on_trials (v := fun i => Real.log (δ i))
    (fun i hi hS => hstep i hi γs hγs (hs i hi hS))
    (fun i hi hT hS => hstep i hi γu hγu (hu i hi hT hS))
    (fun i hi hT => by rw [ha i hi hT])
  have hlog := Real.log_le_log hminpos hmin
  have hneg := Real.log_neg hγu hγu1
  have habs : |Real.log γu| = -Real.log γu := abs_of_neg hneg
  have hpos : 0 < |Real.log γu| := abs_pos.mpr hneg.ne
  have hratio : Real.log (δmin / δ 0) = Real.log δmin - Real.log (δ 0) :=
    Real.log_div hminpos.ne' (hδ 0 (Nat.zero_le _)).ne'
  have habsratio := neg_abs_le (Real.log (δmin / δ 0))
  have hcard : ((successfulIterations T N).card : ℝ) =
      (successfulIterations S N).card + (successfulIterations (T \ S) N).card := by
    exact_mod_cast card_trials_eq_add hST N
  apply (mul_le_mul_iff_of_pos_right hpos).mp
  rw [add_mul, div_mul_cancel₀ _ hpos.ne']
  have he : (successfulIterations S N).card *
      (1 + Real.log γs / |Real.log γu|) * |Real.log γu| =
      (successfulIterations S N).card * (|Real.log γu| + Real.log γs) := by field_simp
  rw [he, hcard]
  rw [habs] at *
  nlinarith

/-- An upper bound on a growing parameter bounds the number of its trial updates. -/
theorem iteration_bound_of_parameter_upper_on_trials {S T : Set ℕ} {σ : ℕ → ℝ}
    {γs γu σmax : ℝ} {N : ℕ} (hST : S ⊆ T) (hσ : ∀ i ≤ N, 0 < σ i)
    (hγs : 0 < γs) (hγs1 : γs < 1) (hγu : 1 < γu)
    (hmax : σ N ≤ σmax)
    (hs : ∀ i < N, i ∈ S → γs * σ i ≤ σ (i + 1))
    (hu : ∀ i < N, i ∈ T → i ∉ S → γu * σ i ≤ σ (i + 1))
    (ha : ∀ i < N, i ∉ T → σ (i + 1) = σ i) :
    ((successfulIterations T N).card : ℝ) ≤ (successfulIterations S N).card *
        (1 + |Real.log γs| / Real.log γu) +
      Real.log (σmax / σ 0) / Real.log γu := by
  have hstep (i : ℕ) (hi : i < N) (γ : ℝ) (hγ : 0 < γ)
      (h : γ * σ i ≤ σ (i + 1)) :
      Real.log γ ≤ Real.log (σ (i + 1)) - Real.log (σ i) := by
    have he := Real.log_le_log (mul_pos hγ (hσ i (by omega))) h
    rw [Real.log_mul hγ.ne' (hσ i (by omega)).ne'] at he
    linarith
  have htel := le_potential_change_on_trials (v := fun i => Real.log (σ i))
    (fun i hi hS => hstep i hi γs hγs (hs i hi hS))
    (fun i hi hT hS => hstep i hi γu (by linarith) (hu i hi hT hS))
    (fun i hi hT => by rw [ha i hi hT])
  have hlog := Real.log_le_log (hσ N le_rfl) hmax
  have hpos := Real.log_pos hγu
  have habs : |Real.log γs| = -Real.log γs := abs_of_neg (Real.log_neg hγs hγs1)
  have hratio : Real.log (σmax / σ 0) = Real.log σmax - Real.log (σ 0) :=
    Real.log_div (lt_of_lt_of_le (hσ N le_rfl) hmax).ne'
      (hσ 0 (Nat.zero_le _)).ne'
  have hcard : ((successfulIterations T N).card : ℝ) =
      (successfulIterations S N).card + (successfulIterations (T \ S) N).card := by
    exact_mod_cast card_trials_eq_add hST N
  apply (mul_le_mul_iff_of_pos_right hpos).mp
  rw [add_mul, div_mul_cancel₀ _ hpos.ne']
  have he : (successfulIterations S N).card *
      (1 + |Real.log γs| / Real.log γu) * Real.log γu =
      (successfulIterations S N).card * (Real.log γu + |Real.log γs|) := by field_simp
  rw [he, hcard, habs, hratio]
  nlinarith

end EvaluationComplexity
