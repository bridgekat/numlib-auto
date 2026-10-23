import Numlib.Optimization.Quadratic.Optimality.TrustRegion
import Numlib.Optimization.Quadratic.Regularization.Stopping
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Global quadratic optimality in a positive-definite metric

Riesz representation transports the original linear and quadratic terms to
the actual energy inner product. All shifted-pencil equations and quadratic
forms are preserved exactly.
-/

namespace QuadraticOptimality.Metric
open QuadraticRegularization.Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (M : E →L[ℝ] E) (hM : M.toLinearMap.IsSymmetricCoercive)

/-- Represent the actual original linear functional by its Riesz vector in the metric inner
product. -/
noncomputable def gradient (g : E) : WithEnergy M.toLinearMap hM :=
  (InnerProductSpace.toDual ℝ _).symm (linearTerm M hM g)

/-- Represent the actual original quadratic form by its bounded operator in the metric inner
product. -/
noncomputable def hessian (H : E →L[ℝ] E) :
    WithEnergy M.toLinearMap hM →L[ℝ] WithEnergy M.toLinearMap hM :=
  InnerProductSpace.continuousLinearMapOfBilin (quadraticTerm M hM H)

/-- The transported gradient represents the original linear term exactly. -/
theorem inner_gradient (g : E) (v : WithEnergy M.toLinearMap hM) :
    inner ℝ (gradient M hM g) v = inner ℝ g (toOriginal M hM v) :=
  InnerProductSpace.toDual_symm_apply

/-- The transported Hessian represents the original bilinear form exactly. -/
theorem inner_hessian (H : E →L[ℝ] E) (v w : WithEnergy M.toLinearMap hM) :
    inner ℝ (hessian M hM H v) w = 
      inner ℝ (H (toOriginal M hM v)) (toOriginal M hM w) :=
  InnerProductSpace.continuousLinearMapOfBilin_apply _ _ _

/-- A symmetric original Hessian stays symmetric in metric coordinates. -/
theorem hessian_symmetric {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric) :
    (hessian M hM H).toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (hessian M hM H v) w = inner ℝ v (hessian M hM H w)
  calc
    _ = inner ℝ (hessian M hM H w) v := by
      rw [inner_hessian, inner_hessian]
      exact (hH _ _).trans (real_inner_comm _ _)
    _ = _ := real_inner_comm _ _

/-- The metric-coordinate quadratic equals the original quadratic at the same vector. -/
theorem model_eq (H : E →L[ℝ] E) (g s : E) :
    model (hessian M hM H) (gradient M hM g) (WithEnergy.equiv M.toLinearMap hM s) = 
      inner ℝ g s + inner ℝ (H s) s / 2 := by
  rw [QuadraticOptimality.model_eq, inner_gradient, inner_hessian]
  rfl

/-- The shifted metric Hessian quadratic is exactly the original shifted pencil form. -/
theorem shifted_inner (H : E →L[ℝ] E) (τ : ℝ) (v w : E) :
    inner ℝ ((hessian M hM H + τ • ContinuousLinearMap.id ℝ (WithEnergy M.toLinearMap hM))
      (WithEnergy.equiv M.toLinearMap hM v)) (WithEnergy.equiv M.toLinearMap hM w) = 
      inner ℝ ((H + τ • M) v) w := by
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, inner_add_left,
    real_inner_smul_left, inner_hessian]
  rfl

/-- Metric radial stationarity is equivalent to the original shifted pencil linear-system
equation. -/
theorem solve_iff (H : E →L[ℝ] E) (g s : E) (τ : ℝ) :
    gradient M hM g + hessian M hM H (WithEnergy.equiv M.toLinearMap hM s) = 
      -τ • WithEnergy.equiv M.toLinearMap hM s ↔ (H + τ • M) s = -g := by
  constructor
  · intro hh
    apply ext_inner_right ℝ
    intro v
    have he := congrArg (fun z : WithEnergy M.toLinearMap hM =>
      inner ℝ z (WithEnergy.equiv M.toLinearMap hM v)) hh
    change inner ℝ ((H + τ • M) s) v = inner ℝ (-g) v
    simp only [inner_add_left, inner_neg_left, add_apply, smul_apply,
      real_inner_smul_left, inner_gradient, inner_hessian] at he ⊢
    change inner ℝ g v + inner ℝ (H s) v = -τ * inner ℝ (M s) v at he
    linarith
  · intro hh
    apply ext_inner_right ℝ
    intro v
    obtain ⟨w, rfl⟩ := (WithEnergy.equiv M.toLinearMap hM).surjective v
    have he := congrArg (fun z : E => inner ℝ z w) hh
    change inner ℝ (gradient M hM g + hessian M hM H
      (WithEnergy.equiv M.toLinearMap hM s)) (WithEnergy.equiv M.toLinearMap hM w) = _
    simp only [inner_add_left, inner_neg_left, add_apply, smul_apply,
      real_inner_smul_left, inner_gradient, inner_hessian] at he ⊢
    change inner ℝ g w + inner ℝ (H s) w = -τ * inner ℝ (M s) w
    linarith

include hM in
/-- The full trust-region global-minimum characterization holds for any symmetric coercive metric,
including singular shifted pencils and all feasible points. -/
theorem trust_region_iff {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric)
    (g s : E) {Δ : ℝ} (hΔ : 0 < Δ) (hs : energyNorm M.toLinearMap s ≤ Δ) :
    (∀ t : E, energyNorm M.toLinearMap t ≤ Δ →
      inner ℝ g s + inner ℝ (H s) s / 2 ≤ inner ℝ g t + inner ℝ (H t) t / 2) ↔
    ∃ τ : ℝ, 0 ≤ τ ∧ (H + τ • M) s = -g ∧
      (∀ v, 0 ≤ inner ℝ ((H + τ • M) v) v) ∧
      τ * (energyNorm M.toLinearMap s ^ 2 - Δ ^ 2) = 0 := by
  have hh := QuadraticOptimality.trust_region_iff (hessian_symmetric M hM hH)
    (gradient M hM g) (WithEnergy.equiv M.toLinearMap hM s) hΔ hs
  constructor
  · intro hm
    have hm' : ∀ t : WithEnergy M.toLinearMap hM, ‖t‖ ≤ Δ →
        model (hessian M hM H) (gradient M hM g) (WithEnergy.equiv M.toLinearMap hM s) ≤
          model (hessian M hM H) (gradient M hM g) t := by
      intro t ht
      obtain ⟨v, rfl⟩ := (WithEnergy.equiv M.toLinearMap hM).surjective t
      simpa only [model_eq] using hm v ht
    obtain ⟨τ, hτ, hsolve, hPSD, hcomp⟩ := hh.mp hm'
    refine ⟨τ, hτ, (solve_iff M hM H g s τ).mp hsolve, ?_, hcomp⟩
    intro v
    simpa only [shifted_inner] using hPSD (WithEnergy.equiv M.toLinearMap hM v)
  · rintro ⟨τ, hτ, hsolve, hPSD, hcomp⟩
    have hm := hh.mpr ⟨τ, hτ, (solve_iff M hM H g s τ).mpr hsolve, ?_, hcomp⟩
    · intro t ht
      simpa only [model_eq] using hm (WithEnergy.equiv M.toLinearMap hM t) ht
    · intro v
      obtain ⟨w, rfl⟩ := (WithEnergy.equiv M.toLinearMap hM).surjective v
      simpa only [shifted_inner] using hPSD w

include hM in
/-- Positive definiteness of the original shifted pencil implies uniqueness of the weighted
trust-region minimizer. -/
theorem unique_trust_region {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric)
    (g s : E) {τ Δ : ℝ} (hτ : 0 ≤ τ) (hsolve : (H + τ • M) s = -g)
    (hPD : ∀ v, v ≠ 0 → 0 < inner ℝ ((H + τ • M) v) v)
    (hcomp : τ * (energyNorm M.toLinearMap s ^ 2 - Δ ^ 2) = 0) :
    ∀ t : E, energyNorm M.toLinearMap t ≤ Δ →
      inner ℝ g t + inner ℝ (H t) t / 2 ≤ inner ℝ g s + inner ℝ (H s) s / 2 → t = s := by
  intro t ht hm
  have he := QuadraticOptimality.unique_trust_region (hessian_symmetric M hM hH)
    (gradient M hM g) (WithEnergy.equiv M.toLinearMap hM s) hτ
    ((solve_iff M hM H g s τ).mpr hsolve) (Δ := Δ) ?_ hcomp
    (WithEnergy.equiv M.toLinearMap hM t) ht (by simpa only [model_eq] using hm)
  · exact (WithEnergy.equiv M.toLinearMap hM).injective he
  · intro v hv
    obtain ⟨w, rfl⟩ := (WithEnergy.equiv M.toLinearMap hM).surjective v
    have hw : w ≠ 0 := by intro hh; subst w; exact hv rfl
    simpa only [shifted_inner] using hPD w hw

end QuadraticOptimality.Metric
