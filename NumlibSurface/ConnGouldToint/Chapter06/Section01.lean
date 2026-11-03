import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.NormNum
import Numlib.Optimization.ModelBased.RatioTest

/-!
# The basic trust-region algorithm

[conn2000trust], Section 6.1. Algorithm 6.1.1 leaves the sufficient model decrease test
unspecified. The run is parameterized by that test and requires positive predicted decrease
at every step for which the ratio is evaluated.
-/

namespace ConnGouldToint.Chapter06

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The trust region (6.1.2) about the current iterate. -/
def trustRegion (p : Seminorm ℝ E) (x : E) (Δ : ℝ) : Set E :=
  {y | p (y - x) ≤ Δ}

@[simp]
theorem mem_trustRegion {p : Seminorm ℝ E} {x y : E} {Δ : ℝ} :
    y ∈ trustRegion p x Δ ↔ p (y - x) ≤ Δ :=
  Iff.rfl

/-- Parameters for BTR with the restrictions in (6.1.3). -/
structure BTRParams where
  η₁ : ℝ
  η₂ : ℝ
  γ₁ : ℝ
  γ₂ : ℝ
  eta₁_pos : 0 < η₁
  eta₁_le_eta₂ : η₁ ≤ η₂
  eta₂_lt_one : η₂ < 1
  gamma₁_pos : 0 < γ₁
  gamma₁_le_gamma₂ : γ₁ ≤ γ₂
  gamma₂_lt_one : γ₂ < 1

/-- The actual reduction divided by the model reduction, as in (6.1.4). -/
noncomputable def btrRatio (f m : E → ℝ) (x s : E) : ℝ :=
  Optimization.reductionRatio f x s (m x - m (x + s))

/-- The radius update (6.1.5), with no upper bound on expansion. -/
structure BTRRadiusUpdate (P : BTRParams) (ρ Δ Δ' : ℝ) : Prop where
  very_successful : P.η₂ ≤ ρ → Δ ≤ Δ'
  successful : P.η₁ ≤ ρ → ρ < P.η₂ → P.γ₂ * Δ ≤ Δ' ∧ Δ' ≤ Δ
  unsuccessful : ρ < P.η₁ → P.γ₁ * Δ ≤ Δ' ∧ Δ' ≤ P.γ₂ * Δ

/-- The update of the trust-region radius preserves positivity. -/
theorem BTRRadiusUpdate.pos {P : BTRParams} {ρ Δ Δ' : ℝ}
    (h : BTRRadiusUpdate P ρ Δ Δ') (hΔ : 0 < Δ) : 0 < Δ' := by
  by_cases h₂ : P.η₂ ≤ ρ
  · exact hΔ.trans_le (h.very_successful h₂)
  by_cases h₁ : P.η₁ ≤ ρ
  · exact (mul_pos (P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂) hΔ).trans_le
      (h.successful h₁ (lt_of_not_ge h₂)).1
  · exact (mul_pos P.gamma₁_pos hΔ).trans_le (h.unsuccessful (lt_of_not_ge h₁)).1

/-- The example parameter values from (6.1.6). -/
noncomputable def defaultBTRParams : BTRParams where
  η₁ := 0.01
  η₂ := 0.9
  γ₁ := 1 / 2
  γ₂ := 1 / 2
  eta₁_pos := by norm_num
  eta₁_le_eta₂ := by norm_num
  eta₂_lt_one := by norm_num
  gamma₁_pos := by norm_num
  gamma₁_le_gamma₂ := le_rfl
  gamma₂_lt_one := by norm_num

/-- The quadratic model (6.1.7), evaluated at a step from its center. -/
noncomputable def quadraticModel {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (c : ℝ) (g : F) (H : F →ₗ[ℝ] F) (s : F) : ℝ :=
  c + inner ℝ g s + (1 / 2) * inner ℝ s (H s)

/-- An infinite run of Algorithm 6.1.1. The predicate `sufficient` specifies the model
decrease requirement at each iteration. Its inputs are the index, model, iterate and step. -/
structure BTRRun (f : E → ℝ) (P : BTRParams)
    (sufficient : ℕ → (E → ℝ) → E → E → Prop) where
  x : ℕ → E
  s : ℕ → E
  Δ : ℕ → ℝ
  p : ℕ → Seminorm ℝ E
  norm_separates : ∀ k v, p k v = 0 → v = 0
  model : ℕ → E → ℝ
  delta_initial_pos : 0 < Δ 0
  feasible : ∀ k, x k + s k ∈ trustRegion (p k) (x k) (Δ k)
  sufficient_decrease : ∀ k, sufficient k (model k) (x k) (s k)
  predicted_pos : ∀ k, 0 < model k (x k) - model k (x k + s k)
  iterate_update : ∀ k, x (k + 1) =
    Optimization.acceptStep P.η₁ f (x k) (s k) (model k (x k) - model k (x k + s k))
  radius_update : ∀ k, BTRRadiusUpdate P (btrRatio f (model k) (x k) (s k)) (Δ k) (Δ (k + 1))

namespace BTRRun

variable {f : E → ℝ} {P : BTRParams} {sufficient : ℕ → (E → ℝ) → E → E → Prop}

/-- Successful iterations are those for which the reduction ratio is at least `η₁`. -/
def successful (run : BTRRun f P sufficient) : Set ℕ :=
  {k | P.η₁ ≤ btrRatio f (run.model k) (run.x k) (run.s k)}

/-- Very successful iterations are those for which the reduction ratio is at least `η₂`. -/
def verySuccessful (run : BTRRun f P sufficient) : Set ℕ :=
  {k | P.η₂ ≤ btrRatio f (run.model k) (run.x k) (run.s k)}

/-- Every very successful iteration is successful. -/
theorem verySuccessful_subset_successful (run : BTRRun f P sufficient) :
    run.verySuccessful ⊆ run.successful :=
  fun _ hk ↦ P.eta₁_le_eta₂.trans hk

/-- Every trust-region radius in the run is positive. -/
theorem delta_pos (run : BTRRun f P sufficient) (k : ℕ) : 0 < run.Δ k := by
  induction k with
  | zero => exact run.delta_initial_pos
  | succ k ih => exact (run.radius_update k).pos ih

/-- Lower bound used in Theorem 6.4.3. If radii at most `θ` force very successful
iterations, then every radius is at least `min (Δ 0) (γ₁ * θ)`. The minimum includes
the initial radius, which can be smaller than the constant displayed in the book's proof. -/
theorem delta_lower_bound (run : BTRRun f P sufficient) {θ : ℝ}
    (hforce : ∀ k, run.Δ k ≤ θ → k ∈ run.verySuccessful) (k : ℕ) :
    min (run.Δ 0) (P.γ₁ * θ) ≤ run.Δ k := by
  induction k with
  | zero => exact min_le_left _ _
  | succ k ih =>
    have h := run.radius_update k
    by_cases hρ : k ∈ run.verySuccessful
    · exact ih.trans (h.very_successful hρ)
    · have hθ : θ < run.Δ k := lt_of_not_ge (fun hk ↦ hρ (hforce k hk))
      have hmul := mul_le_mul_of_nonneg_left hθ.le P.gamma₁_pos.le
      have hstep : P.γ₁ * run.Δ k ≤ run.Δ (k + 1) := by
        by_cases h₁ : k ∈ run.successful
        · exact (mul_le_mul_of_nonneg_right P.gamma₁_le_gamma₂ (run.delta_pos k).le).trans
            (h.successful h₁ (lt_of_not_ge hρ)).1
        · exact (h.unsuccessful (lt_of_not_ge h₁)).1
      exact (min_le_right _ _).trans (hmul.trans hstep)

end BTRRun
end ConnGouldToint.Chapter06
