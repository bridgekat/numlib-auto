import Numlib.Optimization.EvaluationComplexity.ParameterUpdates

/-!
# Cartis–Gould–Toint, Section 2.3: trust-region iteration counts

Lemma 2.3.1 uses only the radius-update component (2.3.7) of TR1. The hypothesis
below spells out that component, including its parameter ranges, through
`TrustRegionRadiusUpdates`; model construction and step selection play no role.
Counts use `N` updates, with indices `i < N`. Thus the source's inclusive set
`S_k` is represented by `successfulIterations ρ η₁ (k + 1)`.
-/

namespace CartisGouldToint

/-- The successful iterations (2.3.9) in a prefix of `N` updates. This corresponds
to the inclusive prefix (2.3.10) with the endpoint index `N - 1` when `N > 0`. -/
noncomputable def successfulIterations (ρ : ℕ → ℝ) (η₁ : ℝ) (N : ℕ) : Finset ℕ :=
  EvaluationComplexity.successfulIterations {i | η₁ ≤ ρ i} N

/-- An index belongs to the successful prefix exactly when it lies in the prefix
and its acceptance ratio is at least the threshold. -/
@[simp]
theorem mem_successfulIterations {ρ : ℕ → ℝ} {η₁ : ℝ} {N i : ℕ} :
    i ∈ successfulIterations ρ η₁ N ↔ i < N ∧ η₁ ≤ ρ i :=
  EvaluationComplexity.mem_successfulIterations

/-- **Lemma 2.3.1.** The update rules of TR1 and a positive lower bound on the
current radius bound the number of updates by the number of successful ones.
The half-open prefix corrects the inclusive-prefix indexing shorthand in the
source proof: `N = |S| + |U|` counts exactly the updates from `Δ₀` to `Δ_N`. -/
theorem lemma_2_3_1 {Δ ρ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ Δmin : ℝ} {N : ℕ}
    (h : EvaluationComplexity.TrustRegionRadiusUpdates Δ ρ η₁ η₂ γ₁ γ₂ γ₃ N)
    (hminpos : 0 < Δmin) (hmin : Δmin ≤ Δ N) :
    (N : ℝ) ≤ (successfulIterations ρ η₁ N).card *
        (1 + Real.log γ₃ / |Real.log γ₂|) +
      |Real.log (Δmin / Δ 0)| / |Real.log γ₂| :=
  EvaluationComplexity.iteration_bound_of_parameter_lower (S := {i | η₁ ≤ ρ i})
    (fun _ hi => h.pos hi) (by linarith [h.one_lt_gamma3])
    (h.gamma1_pos.trans_le h.gamma1_le_gamma2) h.gamma2_lt_one hmin hminpos
    (fun _ hi hs => h.successful_le hi hs)
    (fun _ hi hu => h.unsuccessful_le hi hu)

end CartisGouldToint
