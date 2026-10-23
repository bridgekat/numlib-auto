import Numlib.Optimization.Constrained.Restriction
import NumlibSurface.CartisGouldToint.Chapter01.Section01
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Cartis–Gould–Toint, Section 7.1: equality constraints within a convex set

A feasible minimizer of the Lagrangian minimizes the objective over the feasible subset.
The conclusion is membership in the argmin, without an assertion of uniqueness.
The source assumes an ambient closed bounded nonempty convex set; neither its geometry
nor smoothness is needed for Theorem 7.1.1. The surface retains the closed subset and its
inclusion in an ambient set, while the backbone is the general order argument.
-/

namespace CartisGouldToint

/-- The feasible subset of `S` determined by the equality constraint `c = 0`. -/
def constrainedFeasibleSet {E F : Type*} [Zero F] (S : Set E) (c : E → F) : Set E :=
  {x ∈ S | c x = 0}

@[simp]
theorem mem_constrainedFeasibleSet {E F : Type*} [Zero F]
    {S : Set E} {c : E → F} {x : E} :
    x ∈ constrainedFeasibleSet S c ↔ x ∈ S ∧ c x = 0 := Iff.rfl

/-- **Theorem 7.1.1 (local sufficiency of the Lagrangian).** A feasible
minimizer of the Lagrangian on the closed subset `S` also minimizes the objective
over the feasible points in `S`. -/
theorem theorem_7_1_1 {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C S : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    {y : EuclideanSpace ℝ (Fin m)}
    (_hS : IsClosed S) (_hSC : S ⊆ C) (hx : x ∈ S) (hc : c x = 0)
    (hmin : IsMinOn (fun z => lagrangian f c z y) S x) :
    x ∈ constrainedFeasibleSet S c ∧ IsMinOn f (constrainedFeasibleSet S c) x := by
  refine ⟨⟨hx, hc⟩, ?_⟩
  exact Constrained.isMinOn_of_sub_comp_eq_zero (price := fun z => inner ℝ y z)
    (by simp) hc hmin

end CartisGouldToint
