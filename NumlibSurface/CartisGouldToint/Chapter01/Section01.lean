import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Optimization.Unconstrained.Optimality

/-!
# Cartis–Gould–Toint, Section 1.1: optimality conditions

The Lagrangian uses the source convention `f(x) − ⟪y,c(x)⟫`. Its derivative conditions
are expressed using the actual Fréchet derivatives and Euclidean inner products.
The source's strict second-order conditions (1.1.15),(1.1.18) require nonzero directions.
The converse in Theorem 1.1.2 requires a tangent-cone correction for general convex sets;
its original form is recorded as incorrect in the plan.
-/

namespace CartisGouldToint

/-- The Lagrangian with the minus multiplier convention of equation (1.1.1). -/
def lagrangian {E F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E → ℝ) (c : E → F) (x : E) (y : F) : ℝ := f x - inner ℝ y (c x)

/-- The Lagrangian agrees with the objective at a feasible point. -/
@[simp]
theorem lagrangian_of_feasible {E F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : E → ℝ} {c : E → F} {x : E} (y : F) (hx : c x = 0) :
    lagrangian f c x y = f x := by simp [lagrangian, hx]

/-- **Theorem 1.1.1 (unconstrained optimality conditions).** At a local minimum,
the first derivative vanishes; for a `C²` objective its Hessian is positive semidefinite;
for a `C³` objective its third derivative vanishes along the Hessian kernel. Conversely,
a stationary point with positive definite Hessian is a strict local minimum.
The Hessian is the actual second Fréchet derivative, viewed as a bilinear form. -/
theorem theorem_1_1_1 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} :
    (ContDiff ℝ 1 f → IsLocalMin f x → fderiv ℝ f x = 0) ∧
    (ContDiff ℝ 2 f → IsLocalMin f x →
      ∀ v, 0 ≤ fderiv ℝ (fderiv ℝ f) x v v) ∧
    (ContDiff ℝ 3 f → IsLocalMin f x →
      ∀ v, fderiv ℝ (fderiv ℝ f) x v = 0 →
        iteratedFDeriv ℝ 3 f x (fun _ => v) = 0) ∧
    (ContDiff ℝ 2 f → fderiv ℝ f x = 0 →
      (∀ v ≠ 0, 0 < fderiv ℝ (fderiv ℝ f) x v v) →
        ∃ δ > 0, ∀ y ∈ Metric.ball x δ, y ≠ x → f x < f y) := by
  refine ⟨fun _ hmin => hmin.fderiv_eq_zero, ?_, ?_, ?_⟩
  · exact fun hf hmin => Descent.hessian_nonneg_of_isLocalMin hmin hf
  · intro hf hmin v hv
    exact Descent.third_apply_eq_zero_of_isLocalMin hmin hf v (by simp [hv])
  · exact Descent.strict_local_min_of_pos_hessian

end CartisGouldToint
