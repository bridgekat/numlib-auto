import NumlibSurface.CartisGouldToint.Chapter12.Section01
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Cartis–Gould–Toint, Appendix B to Chapter 12

Lemma B.12.1 reduces zero cubic model decrease to zero quadratic model decrease. Both the
explicit model statement and its formulation using the actual Taylor criticality measure
are provided. A matrix is represented by its continuous linear map; the model statement
holds even without symmetry. Radius zero is included.
-/

namespace CartisGouldToint

/-- **Lemma B.12.1, model formulation.** If the cubic model has minimum zero on the
centered ball, the quadratic model has minimum zero there too. Both models vanish at
zero, so the cubic hypothesis is expressed as nonnegativity of all its feasible values. -/
theorem lemma_B_12_1_models {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ s, ‖s‖ ≤ δ → 0 ≤ inner ℝ g s + inner ℝ s (H s) / 2 + T (fun _ => s) / 6) :
    ∃ s, ‖s‖ ≤ δ ∧ inner ℝ g s + inner ℝ s (H s) / 2 = 0 ∧
      ∀ d, ‖d‖ ≤ δ → 0 ≤ inner ℝ g d + inner ℝ d (H d) / 2 := by
  exact ⟨0, by simpa using hδ, by simp,
    TaylorModel.quadratic_nonneg_of_cubic_nonneg g H T h⟩

/-- **Lemma B.12.1.** Zero cubic Taylor criticality implies zero quadratic Taylor
criticality, with the criticality measures defined by genuine Taylor polynomials. -/
theorem lemma_B_12_1 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : highOrderCriticality f 3 x δ = 0) : highOrderCriticality f 2 x δ = 0 :=
  TaylorModel.criticality_two_eq_zero_of_three f x hδ h

end CartisGouldToint
