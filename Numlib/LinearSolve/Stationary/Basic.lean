import Numlib.Analysis.SpectralRadius
import Numlib.Analysis.NormedRing.Inverse
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Stationary (affine) iterations

`Stationary.step G f x = G x + f`. Convergence for all data iff `ρ(G) < 1` (Saad Thm 4.1 in a
complex Banach space for `⇒`, finite dimension for `⇐`; Kress Thm 4.1), the contraction case
`‖G‖ < 1` with a priori / a posteriori bounds (Kress Thm 3.48, Atkinson–Han §5.2.2), and the
error propagation `x_k - x* = G^k (x₀ - x*)`.
-/

open Filter Topology

namespace Stationary

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- One affine step `x ↦ G x + f`. -/
def step (G : E →L[𝕜] E) (f : E) (x : E) : E := G x + f

variable (G : E →L[𝕜] E) (f : E)

theorem step_iterate_sub {x' : E} (hfix : G x' + f = x') (x₀ : E) (k : ℕ) :
    (step G f)^[k] x₀ - x' = (G ^ k) (x₀ - x') := by
  sorry

/-- Fixed points of the step are solutions of `(1 - G) x = f`. -/
theorem step_fixed_iff (x : E) : step G f x = x ↔ (1 - G) x = f := by
  sorry

/-- Contraction case `‖G‖ < 1` (Kress Thm 3.48, Atkinson–Han §5.2.2). -/
theorem contractingWith (hG : ‖G‖ < 1) :
    ContractingWith ⟨‖G‖, norm_nonneg _⟩ (step G f) := by
  sorry

/-- A priori bound `‖x_k - x*‖ ≤ ‖G‖^k / (1 - ‖G‖) ‖x₁ - x₀‖` for `‖G‖ < 1`. -/
theorem norm_iterate_sub_le [CompleteSpace E] (hG : ‖G‖ < 1) {x' : E} (hfix : G x' + f = x')
    (x₀ : E) (k : ℕ) :
    ‖(step G f)^[k] x₀ - x'‖ ≤ ‖G‖ ^ k / (1 - ‖G‖) * ‖step G f x₀ - x₀‖ := by
  sorry

/-- A posteriori bound `‖x_k - x*‖ ≤ ‖G‖ / (1 - ‖G‖) ‖x_k - x_{k-1}‖`. -/
theorem norm_iterate_sub_le' [CompleteSpace E] (hG : ‖G‖ < 1) {x' : E} (hfix : G x' + f = x')
    (x₀ : E) (k : ℕ) :
    ‖(step G f)^[k + 1] x₀ - x'‖ ≤
      ‖G‖ / (1 - ‖G‖) * ‖(step G f)^[k + 1] x₀ - (step G f)^[k] x₀‖ := by
  sorry

section Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Saad Thm 4.1 (⇒), any complex Banach space: `ρ(G) < 1` gives convergence for every `f, x₀`
to the unique fixed point `(1 - G)⁻¹ f`. -/
theorem tendsto_of_spectralRadius_lt_one [CompleteSpace F] (G : F →L[ℂ] F)
    (hG : spectralRadius ℂ G < 1) (f x₀ : F) :
    Tendsto (fun k => (step G f)^[k] x₀) atTop (𝓝 (Ring.inverse (1 - G) f)) := by
  sorry

theorem isUnit_one_sub_of_spectralRadius_lt_one [CompleteSpace F] (G : F →L[ℂ] F)
    (hG : spectralRadius ℂ G < 1) : IsUnit (1 - G) := by
  sorry

/-- Saad Thm 4.1 (⇐), finite dimension: convergence of `G^k x₀ → 0` for all `x₀` forces
`ρ(G) < 1`. -/
theorem spectralRadius_lt_one_of_forall_tendsto [FiniteDimensional ℂ F] (G : F →L[ℂ] F)
    (h : ∀ x₀, Tendsto (fun k => (G ^ k) x₀) atTop (𝓝 0)) : spectralRadius ℂ G < 1 := by
  sorry

/-- Saad Thm 4.1 as an equivalence in finite dimension. -/
theorem forall_tendsto_iff_spectralRadius_lt_one [FiniteDimensional ℂ F] (G : F →L[ℂ] F) :
    (∀ f x₀, ∃ x, Tendsto (fun k => (step G f)^[k] x₀) atTop (𝓝 x)) ↔
      spectralRadius ℂ G < 1 := by
  sorry

/-- Geometric convergence rate: for every `r > ρ(G)`, `‖x_k - x*‖ ≤ C r^k ‖x₀ - x*‖`. -/
theorem exists_norm_iterate_sub_le [CompleteSpace F] (G : F →L[ℂ] F) {r : NNReal}
    (hr : spectralRadius ℂ G < r) (f : F) {x' : F} (hfix : G x' + f = x') :
    ∃ C : ℝ, ∀ x₀ k, ‖(step G f)^[k] x₀ - x'‖ ≤ C * (r : ℝ) ^ k * ‖x₀ - x'‖ := by
  sorry

end Complex

end Stationary
