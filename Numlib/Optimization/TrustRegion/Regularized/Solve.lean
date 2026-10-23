import Numlib.Optimization.TrustRegion.Regularized.Run
import Numlib.Optimization.TrustRegion.Regularized.Hessian
import Numlib.Optimization.Descent

/-!
# Existence of permitted regularized trust-region steps

Exact minimization of the actual continuous quadratic model on a compact ball
provides a permitted step. At interior minimizers the actual derivative vanishes
and the constant second derivative is positive semidefinite. A negative shifted
Hessian eigenvalue therefore forces the global minimizer onto the boundary.
-/

namespace RegularizedTrustRegion
open TaylorModel Set Metric SecondOrderTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The constant second derivative of the regularized quadratic model is
nonnegative on every diagonal direction at any actual local minimizer. -/
theorem model_curvature_nonneg {f : E → ℝ} {x s : E} {ε : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hm : IsLocalMin (model f x ε) s) (v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x v v + ε * ‖v‖ ^ 2 := by
  have hn := Descent.nonneg_apply_apply_of_isLocalMin hm
    (Filter.Eventually.of_forall (fun y =>
      (hasFDerivAt_model hf ε y).differentiableAt.hasFDerivAt))
    (hasFDerivAt_fderiv_model hf ε s) v
  change 0 ≤ fderiv ℝ (fderiv ℝ f) x v v + ε * inner ℝ v v at hn
  simpa only [real_inner_self_eq_norm_sq] using hn

variable [CompleteSpace E]

/-- A negative shifted actual Hessian eigenvalue excludes an interior model
minimizer, including at zero gradient. -/
theorem not_isLocalMin_of_negative_shift {f : E → ℝ} {x s u : E} {ε μ : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (he : IsLeastEigenpair f x μ u)
    (hneg : μ + ε < 0) : ¬IsLocalMin (model f x ε) s := by
  intro hm
  have hn := model_curvature_nonneg hf hm u
  have hcurv : fderiv ℝ (fderiv ℝ f) x u u = μ := by
    have ht := TaylorModel.tensor_curvature_of_eigenvector f x u he.unit he.eigenvector
    have hu : (![u, u] : Fin 2 → E) = (fun _ => u) := by
      ext i; fin_cases i <;> rfl
    simpa only [← hu, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] using ht
  rw [hcurv, he.unit] at hn
  linarith

/-- A nonzero actual gradient excludes a local minimum of the model at zero. -/
theorem not_isLocalMin_zero_of_gradient_ne {f : E → ℝ} {x : E} {ε : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : gradient f x ≠ 0) :
    ¬IsLocalMin (model f x ε) 0 := by
  intro hm
  have hd := hm.hasFDerivAt_eq_zero (hasFDerivAt_model hf ε 0)
  have hz : fderiv ℝ f x = 0 := by
    simpa only [quadraticDerivative, map_zero, add_zero, smul_zero] using hd
  apply hg
  have hh := congrArg (InnerProductSpace.toDual ℝ E).symm hz
  simpa only [← toDual_gradient, LinearIsometryEquiv.symm_apply_apply, map_zero] using hh

/-- Every nonterminal model has a feasible strict improvement which obeys the
actual interior stationarity test; negative shifted curvature forces a boundary
step. The condition of nonterminality is a nonzero gradient or a genuine negative
shifted Hessian eigenvalue, rather than an assumed existence of a trial step. -/
theorem exists_modelStep [ProperSpace E] {f : E → ℝ} {x u : E} {μ ε Δ θ : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hΔ : 0 < Δ) (hθ : 0 ≤ θ)
    (hactive : gradient f x ≠ 0 ∨ (IsLeastEigenpair f x μ u ∧ μ + ε < 0)) :
    ∃ s : E, ‖s‖ ≤ Δ ∧ model f x ε s < model f x ε 0 ∧
      (‖s‖ < Δ → ‖fderiv ℝ (model f x ε) s‖ ≤ θ / 2 * ‖s‖ ^ 2) ∧
      (IsLeastEigenpair f x μ u → μ + ε < 0 → ‖s‖ = Δ) := by
  have hc : Continuous (model f x ε) :=
    (continuous_eval f 2 x).add (continuous_const.mul (continuous_norm.pow 2))
  obtain ⟨s, hs, hm⟩ := (isCompact_closedBall (0 : E) Δ).exists_isMinOn
    (nonempty_closedBall.mpr hΔ.le) hc.continuousOn
  have hsn : ‖s‖ ≤ Δ := by simpa only [mem_closedBall, dist_zero_right] using hs
  have hzero : (0 : E) ∈ closedBall 0 Δ := by simpa using hΔ.le
  have hstrict : model f x ε s < model f x ε 0 := by
    have hle := hm hzero
    by_contra hbad
    have heq : model f x ε s = model f x ε 0 := le_antisymm hle (le_of_not_gt hbad)
    have hzmin : IsMinOn (model f x ε) (closedBall 0 Δ) 0 := by
      intro y hy
      rw [← heq]
      exact hm hy
    have hlocal := hzmin.isLocalMin (Metric.closedBall_mem_nhds_of_mem
      (show (0 : E) ∈ ball 0 Δ by simpa using hΔ))
    rcases hactive with hg | ⟨he, hn⟩
    · exact not_isLocalMin_zero_of_gradient_ne hf hg hlocal
    · exact not_isLocalMin_of_negative_shift hf he hn hlocal
  have hinterior : ‖s‖ < Δ → IsLocalMin (model f x ε) s := by
    intro hi
    exact hm.isLocalMin (Metric.closedBall_mem_nhds_of_mem (by simpa using hi))
  refine ⟨s, hsn, hstrict, ?_, ?_⟩
  · intro hi
    rw [(hinterior hi).fderiv_eq_zero, norm_zero]
    exact mul_nonneg (div_nonneg hθ (by norm_num)) (sq_nonneg _)
  · intro he hn
    by_contra hboundary
    exact not_isLocalMin_of_negative_shift hf he hn
      (hinterior (lt_of_le_of_ne hsn hboundary))

/-- Failure of the actual enabled stopping test guarantees that the compact
model minimization supplies a permitted step in either algorithm mode. -/
theorem exists_step_of_not_stopped [ProperSpace E] {f : E → ℝ} {x u : E}
    {μ ε ε₁ Δ θ : ℝ} {ε₂ : WithTop ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hΔ : 0 < Δ) (hθ : 0 ≤ θ) (hε₁ : 0 ≤ ε₁)
    (hmode : (ε₂ = ⊤ ∧ ε = Real.sqrt ε₁) ∨ (ε₂ = (ε : WithTop ℝ) ∧ ε ≤ 1))
    (he : ε₂ ≠ ⊤ → IsLeastEigenpair f x μ u) (hstop : ¬Stopped f x μ ε₁ ε₂) :
    ∃ s : E, ‖s‖ ≤ Δ ∧ model f x ε s < model f x ε 0 ∧
      (‖s‖ < Δ → ‖fderiv ℝ (model f x ε) s‖ ≤ θ / 2 * ‖s‖ ^ 2) ∧
      (IsLeastEigenpair f x μ u → μ + ε < 0 → ‖s‖ = Δ) := by
  apply exists_modelStep hf hΔ hθ
  by_cases hg : gradient f x ≠ 0
  · exact Or.inl hg
  · have hgrad : ‖gradient f x‖ ≤ ε₁ := by
      simpa only [not_not.mp hg, norm_zero] using hε₁
    rcases hmode with ⟨htop, _⟩ | ⟨hfinite, _⟩
    · exfalso
      apply hstop
      apply (stopped_iff _ _ _ _ _).mpr
      refine ⟨hgrad, fun e hh => ?_⟩
      rw [htop] at hh
      exact (WithTop.top_ne_coe hh).elim
    · have hnotop : ε₂ ≠ ⊤ := by simp [hfinite]
      refine Or.inr ⟨he hnotop, ?_⟩
      have hneg : μ < -ε := by
        by_contra hn
        apply hstop
        apply (stopped_iff _ _ _ _ _).mpr
        refine ⟨hgrad, ?_⟩
        intro e hh
        have heq : ε = e := WithTop.coe_injective (hfinite.symm.trans hh)
        simpa only [← heq] using le_of_not_gt hn
      linarith

end RegularizedTrustRegion
