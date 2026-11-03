import NumlibSurface.ConnGouldToint.Chapter13.Section01

/-! # The logarithmic barrier model -/

open Metric
open scoped BigOperators

namespace ConnGouldToint.Chapter13

variable {ι : Type*} [Fintype ι]

/-- The quadratic model (13.4.2), evaluated at the displacement `s`. -/
noncomputable def logBarrierModel (x s : ι → ℝ) (μ : ℝ) : ℝ :=
  logBarrier x μ - μ * (∑ i, (x i)⁻¹ * s i) +
    μ / 2 * (∑ i, ((x i) ^ 2)⁻¹ * (s i) ^ 2)

/-- The diagonal Hessian formula (13.4.8). -/
theorem logBarrier_hessian (μ : ℝ) {x : ι → ℝ} (hx : ∀ i, 0 < x i) (d e : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (fun y ↦ logBarrier y μ)) x d e =
      μ * ∑ i, ((x i) ^ 2)⁻¹ * d i * e i :=
  Optimization.fderiv_fderiv_logBarrier_apply μ hx d e

/-- The smoothness part AC.1c of Lemma 13.4.1. -/
theorem logBarrier_contDiffOn (μ : ℝ) :
    ContDiffOn ℝ 2 (fun x : ι → ℝ ↦ logBarrier x μ)
      (interior (Optimization.nonnegativeOrthant ι)) := by
  intro x hx
  have hpos : ∀ i, 0 < x i := by
    rw [Optimization.nonnegativeOrthant, interior_pi_set Set.finite_univ] at hx
    simpa only [Set.mem_pi, Set.mem_univ, true_implies, interior_Ici, Set.mem_Ioi] using hx
  exact (Optimization.contDiffAt_logBarrier μ hpos).contDiffWithinAt

/-- The Hessian-bound part AC.4c of Lemma 13.4.1. -/
theorem logBarrier_hessian_bounded (μ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ (1 : ℝ), ∀ x : ι → ℝ, (∀ i, 0 < x i) →
      ε ≤ infDist x (frontier (Optimization.nonnegativeOrthant ι)) →
      ‖fderiv ℝ (fderiv ℝ (fun y ↦ logBarrier y μ)) x‖ ≤ C := by
  refine ⟨max 1 (|μ| * Fintype.card ι * (ε ^ 2)⁻¹), le_max_left _ _, fun x hx hdist ↦ ?_⟩
  exact (Optimization.norm_fderiv_fderiv_logBarrier_le μ hε
    (fun i ↦ hdist.trans (Optimization.infDist_frontier_le_coordinate hx i))).trans
      (le_max_right _ _)

/-- The model (13.4.2) is the second-order Taylor model of the barrier. -/
theorem logBarrierModel_eq_taylor {x : ι → ℝ} (hx : ∀ i, 0 < x i) (s : ι → ℝ) (μ : ℝ) :
    logBarrierModel x s μ = logBarrier x μ + fderiv ℝ (fun y ↦ logBarrier y μ) x s +
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ (fun y ↦ logBarrier y μ)) x s s := by
  change _ = logBarrier x μ + fderiv ℝ (Optimization.logBarrier μ) x s + _
  rw [Optimization.fderiv_logBarrier_apply μ hx, logBarrier_hessian μ hx]
  simp only [logBarrierModel, pow_two, mul_assoc]
  ring

end ConnGouldToint.Chapter13
