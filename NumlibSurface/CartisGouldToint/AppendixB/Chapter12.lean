import Numlib.Optimization.CubicQuadraticMinimum

/-!
# Appendix B to Chapter 12

A zero minimum of the source's cubic model implies a zero minimum of its quadratic
truncation. The zero constant terms make `IsMinOn` at the origin precisely the asserted
zero-minimum statements. The result includes radius zero.
-/

noncomputable section
open Metric Set Optimization
namespace CartisGouldToint.AppendixB.Chapter12

/-- Lemma B.12.1: a cubic model with minimum zero on the closed radius-`Δ` ball has
quadratic truncation with minimum zero on the same ball. A continuous linear operator
represents the matrix `H`, and a continuous trilinear form represents the cubic tensor.
The conclusion holds even without symmetry assumptions. -/
theorem lemma_B_12_1 {n : ℕ} (g : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) ℝ)
    {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hmin : IsMinOn (fun s => QuadraticSubproblem.quadratic g H s + T (fun _ => s) / 6)
      (closedBall 0 Δ) 0) :
    IsMinOn (QuadraticSubproblem.quadratic g H) (closedBall 0 Δ) 0 :=
  isMinOn_quadratic_of_cubic g H T hΔ hmin

end CartisGouldToint.AppendixB.Chapter12
