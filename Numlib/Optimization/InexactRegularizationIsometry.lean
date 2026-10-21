import Numlib.Optimization.InexactRegularizationBounds

/-!
# Isometric transport of supplied polynomial inspections

Linear isometries identify actual displacement balls and preserve polynomial values,
regularizers and every operational halving test. Thus scalar inspections can be used on
one-dimensional Euclidean space without replacing the true compact gap by an abstract oracle.
-/

noncomputable section
namespace Optimization.InexactRegularization
open InexactTaylorModels TaylorCriticality

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Replacing equal model data keeps every recorded direction of a radius search. -/
def RadiusSearch.congr {A A' : Coefficients E} {c c' σ δ v ε : ℝ} {p j N : ℕ}
    (s : RadiusSearch c A p j σ δ v ε N) (hc : c = c') (hA : A = A') :
    RadiusSearch c' A' p j σ δ v ε N where
  direction := s.direction
  witness := by simpa only [← hA] using s.witness
  failed := by simpa only [← hc, ← hA] using s.failed

/-- Replacing equal model data keeps every operational choice of a complete inspection. -/
def Inspection.congr {P : Parameters} {A A' : Coefficients E} {c c' σ : ℝ}
    {δ : ℕ → ℝ} (I : Inspection P c A σ δ) (hc : c = c') (hA : A = A') :
    Inspection P c' A' σ δ where
  order := I.order
  order_pos := I.order_pos
  order_le := I.order_le
  halvings := I.halvings
  search := fun j hj hjq hjo => (I.search j hj hjq hjo).congr hc hA
  earlier := by
    intro j hj hjq hjo
    simpa only [RadiusSearch.congr, ← hA] using I.earlier j hj hjq hjo
  failed := by intro hq; simpa only [RadiusSearch.congr, ← hA] using I.failed hq
  retained := by intro hq; simpa only [RadiusSearch.congr, ← hc, ← hA] using I.retained hq

/-- Equal-data replacement preserves all inspected radii exactly. -/
theorem Inspection.congr_radii {P : Parameters} {A A' : Coefficients E} {c c' σ : ℝ}
    {δ : ℕ → ℝ} (I : Inspection P c A σ δ) (hc : c = c') (hA : A = A') :
    (I.congr hc hA).radii = I.radii := rfl

/-- Pull a supplied tensor family back along a linear isometry equivalence. -/
def pullCoefficients (e : E ≃ₗᵢ[ℝ] F) (A : Coefficients F) : Coefficients E :=
  fun i => (A i).compContinuousLinearMap (fun _ => (e : E →L[ℝ] F))

/-- Isometric pullback preserves the norm of every tensor. -/
theorem norm_pullCoefficients (e : E ≃ₗᵢ[ℝ] F) (A : Coefficients F) (i : ℕ) :
    ‖pullCoefficients e A i‖ = ‖A i‖ :=
  ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv _ _

/-- Pulled tensor polynomials are the original polynomials in isometric coordinates. -/
theorem polynomial_pullCoefficients (e : E ≃ₗᵢ[ℝ] F) (A : Coefficients F)
    (c : ℝ) (j : ℕ) (d : E) :
    polynomial c (pullCoefficients e A) j d = polynomial c A j (e d) := by
  simp [polynomial, pullCoefficients]

/-- The actual Taylor decrement commutes with isometric pullback. -/
theorem decrement_pullCoefficients (e : E ≃ₗᵢ[ℝ] F) (A : Coefficients F)
    (j : ℕ) (d : E) :
    decrement (pullCoefficients e A) j d = decrement A j (e d) := by
  simp [decrement, pullCoefficients]

/-- The radial regularizer commutes with isometric pullback as well. -/
theorem regularizedPolynomial_pullCoefficients (e : E ≃ₗᵢ[ℝ] F) (A : Coefficients F)
    (c σ : ℝ) (p : ℕ) (d : E) :
    regularizedPolynomial c (pullCoefficients e A) p σ d =
      regularizedPolynomial c A p σ (e d) := by
  simp [regularizedPolynomial, polynomial_pullCoefficients]

/-- A genuine fraction witness transfers to the corresponding displacement ball. -/
theorem CoefficientWitness.pull [ProperSpace F] (e : E ≃ₗᵢ[ℝ] F)
    {A : Coefficients F} {j : ℕ} {δ v : ℝ} {d : F}
    (hw : CoefficientWitness A j δ v d) (hv : 0 ≤ v) :
    CoefficientWitness (pullCoefficients e A) j δ v (e.symm d) := by
  have hδ : 0 ≤ δ := (norm_nonneg d).trans hw.feasible
  have hg : gapOn (decrement (pullCoefficients e A) j) (Metric.closedBall 0 δ) ≤
      gapOn (decrement A j) (Metric.closedBall 0 δ) := by
    apply gapOn_le ⟨0, by simpa using hδ⟩
    intro x hx
    rw [decrement_pullCoefficients]
    exact le_gapOn (isCompact_closedBall (0 : F) δ) (continuous_decrement A j).continuousOn
      (by simpa only [Metric.mem_closedBall, dist_zero_right, e.norm_map] using hx)
  refine ⟨by simpa using hw.feasible, ?_⟩
  rw [decrement_pullCoefficients, e.apply_symm_apply]
  exact (mul_le_mul_of_nonneg_left hg hv).trans hw.fraction_le

/-- Every recorded halving, failure and witness of a radius search transports isometrically. -/
def RadiusSearch.pull [ProperSpace F] (e : E ≃ₗᵢ[ℝ] F)
    {A : Coefficients F} {c σ δ v ε : ℝ} {p j N : ℕ}
    (s : RadiusSearch c A p j σ δ v ε N) (hv : 0 ≤ v) :
    RadiusSearch c (pullCoefficients e A) p j σ δ v ε N where
  direction := fun k => e.symm (s.direction k)
  witness := fun k hk => (s.witness k hk).pull e hv
  failed := by
    intro k hk
    simpa only [decrement_pullCoefficients, regularizedPolynomial_pullCoefficients,
      e.apply_symm_apply] using s.failed k hk

/-- A full inspection, including the all-pass branch, transports to isometric coordinates. -/
def Inspection.pull [ProperSpace F] (e : E ≃ₗᵢ[ℝ] F)
    {P : Parameters} {A : Coefficients F} {c σ : ℝ} {δ : ℕ → ℝ}
    (I : Inspection P c A σ δ) : Inspection P c (pullCoefficients e A) σ δ where
  order := I.order
  order_pos := I.order_pos
  order_le := I.order_le
  halvings := I.halvings
  search := fun j hj hjq hjo => (I.search j hj hjq hjo).pull e P.fraction_pos.le
  earlier := by
    intro j hj hjq hjo
    simpa only [RadiusSearch.pull, decrement_pullCoefficients, e.apply_symm_apply]
      using I.earlier j hj hjq hjo
  failed := by
    intro hq
    simpa only [RadiusSearch.pull, decrement_pullCoefficients, e.apply_symm_apply]
      using I.failed hq
  retained := by
    intro hq
    simpa only [RadiusSearch.pull, regularizedPolynomial_pullCoefficients,
      e.apply_symm_apply] using I.retained hq

/-- Inspection transport preserves each inspected radius exactly. -/
theorem Inspection.pull_radii [ProperSpace F] (e : E ≃ₗᵢ[ℝ] F)
    {P : Parameters} {A : Coefficients F} {c σ : ℝ} {δ : ℕ → ℝ}
    (I : Inspection P c A σ δ) : (I.pull e).radii = I.radii := rfl

end Optimization.InexactRegularization
