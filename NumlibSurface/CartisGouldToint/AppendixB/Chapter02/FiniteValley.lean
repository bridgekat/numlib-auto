import NumlibSurface.CartisGouldToint.AppendixB.Chapter02.Profiles
import Numlib.Optimization.SteepestDescentValleyScalarBounds
import Numlib.Optimization.SteepestDescentValleyCounterexample

/-!
# Finite completion of the SDEX valley profiles

These are the actual finite scalar and Euclidean constructions underlying the valid parts
of Appendix B.2. The count is rounded up from the reciprocal squared tolerance; the source
cell formulas are used only through that finite count. A unit objective transition followed
by a constant tail supplies the required right completion. On the left the objective is
affine, as in equation (B.2.24), and the width and midpoint are frozen.

This corrected finite construction proves global C2 regularity, a uniform lower bound,
uniform scalar derivatives, and the prescribed actual nodal gradients and steps.
`FiniteValleySmooth` supplies uniform mixed and Hessian bounds and first local ray minima;
the parent `Chapter02` module identifies the full construction and states Lemmas B.2.2–B.2.6
with their finite range, integer count and explicit exterior completion. The global
line-minimization interpretation fails for the complete actual finite objective, as
demonstrated by the last theorem.
-/

noncomputable section
open Optimization.SteepestDescentValley

namespace CartisGouldToint.AppendixB.Chapter02

/-- Every tolerance in `(0,1]` has an actual finite Euclidean valley, with the rounded
cell count and genuine C2 smoothness across all scalar and moving strip seams. -/
theorem finite_valley_c2 (eps : ℝ) (hpos : 0 < eps) (hle : eps ≤ 1) :
    ContDiff ℝ 2 (euclideanObjective (roundedParameters eps hpos hle)) :=
  contDiff_euclideanObjective _

/-- The corrected finite completion has a uniform global lower bound, chosen before the
tolerance and independent of the number of cells. This is the bounded-below conclusion
for the actual completed function, rather than an assumed profile bound. -/
theorem finite_valley_uniform_lower_bound (eps : ℝ) (hpos : 0 < eps) (hle : eps ≤ 1)
    (p : EuclideanSpace ℝ (Fin 2)) :
    -22 / Real.sqrt 2 ≤ euclideanObjective (roundedParameters eps hpos hle) p :=
  euclideanObjective_lower _ _

/-- Width and midpoint have uniform actual first and second derivatives on the full line;
the objective profile has the fixed bound 200 for both orders. -/
theorem finite_valley_uniform_scalar_derivatives :
    ∃ C > 0, ∀ (P : Parameters) (j : ℕ), j = 1 ∨ j = 2 → ∀ t : ℝ,
      |iteratedDeriv j (scalarObjective P) t| ≤ 200 ∧
        |iteratedDeriv j (scalarWidth P) t| ≤ C ∧
          |iteratedDeriv j (scalarMidpoint P) t| ≤ C := by
  obtain ⟨C, hC, h⟩ := exists_width_midpoint_derivative_bound
  exact ⟨C, hC, fun P j hj t => ⟨scalarObjective_derivatives_bound P hj t, h P j hj t⟩⟩

/-- The actual nodal gradient has the prescribed Euclidean components and norm. -/
theorem finite_valley_nodal_gradient (P : Parameters) {k : ℕ} (hk : k ≤ P.count) :
    gradient (euclideanObjective P) (nodePoint P k) = nodeGradient P k ∧
      ‖gradient (euclideanObjective P) (nodePoint P k)‖ = cellLength P k :=
  ⟨gradient_euclideanObjective_node P hk, norm_gradient_euclideanObjective_node P hk⟩

/-- The prescribed successor is the actual negative-gradient step with parameter square root two. -/
theorem finite_valley_prescribed_step (P : Parameters) {k : ℕ} (hk : k < P.count) :
    nodePoint P (k + 1) = nodePoint P k - Real.sqrt 2 •
      gradient (euclideanObjective P) (nodePoint P k) := nodePoint_succ P hk

/-- The actual finite path first attains the gradient tolerance at its final node.
This count does not assert that the prescribed steps are global ray minimizers. -/
theorem finite_valley_first_tolerance (P : Parameters) :
    ‖gradient (euclideanObjective P) (nodePoint P P.count)‖ = P.eps ∧
      ∀ k < P.count, P.eps < ‖gradient (euclideanObjective P) (nodePoint P k)‖ :=
  ⟨terminal_gradient_norm P, fun _ hk => preceding_gradient_norm P hk⟩

/-- A complete actual valley with exact reciprocal-square count refutes the global
interpretation of the prescribed first step. The source's first-local-minimum clause
is proved separately in `FiniteValleySmooth`. -/
theorem finite_valley_not_global_exact :
    ¬ LineSearch.IsExact (euclideanObjective counterexampleParameters)
      (nodePoint counterexampleParameters 0)
      (-gradient (euclideanObjective counterexampleParameters)
        (nodePoint counterexampleParameters 0)) (Real.sqrt 2) :=
  counterexample_not_global_exact

end CartisGouldToint.AppendixB.Chapter02
