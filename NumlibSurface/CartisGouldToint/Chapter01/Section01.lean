import Mathlib.Analysis.InnerProductSpace.Basic

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

end CartisGouldToint
