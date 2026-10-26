import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Optimization.Optimality.HighOrder

/-!
# Cartis–Gould–Toint, Appendix B: Appendix to Chapter 12

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], Appendix B, "Appendix to
Chapter 12": Lemma B.12.1, which justifies the use of the third-order measure `φ^δ_{f,3}` in
§12.1.3 (`φ^δ_{f,3}(x) = 0` implies `φ^δ_{f,2}(x) = 0`). The content is the backbone theorem
`Optimization.taylorMeasure_two_eq_zero_of_three`, stated for arbitrary Taylor data; here it is
specialized to the data `(g, H, T)` of the book on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, with the
book's `min` written as `sInf` of the values on the closed ball (the minimum is attained, by
compactness).

## Main results

* `lemma_B_12_1` — Lemma B.12.1.

## Deviations from the book

* The symmetry of `H` and the cubic symmetry of `T` assumed by the book are not needed: `H` is any
  linear map and `T` any continuous trilinear form.
* The radius `Δ` is arbitrary (for `Δ < 0` both minima are over the empty set and the statement is
  trivial with the convention `sInf ∅ = 0`).

The proofs of Theorems 12.1.7 and 12.2.6 that the book gives in this appendix belong to Chapter 12.
-/

open Set Metric
open scoped RealInnerProductSpace

namespace CartisGouldToint.AppendixB

variable {n : ℕ}

/-- The Taylor data `(g, H, T)` of Lemma B.12.1 as a formal multilinear series: `D₁[s] = ⟨g, s⟩`,
`D₂[s]² = ⟨s, H s⟩`, `D₃[s]³ = T[s]³`. -/
private noncomputable def lemmaB121Data (g : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) ℝ) :
    FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ
  | 1 => (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin n)) ℝ).symm (innerSL ℝ g)
  | 2 => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin n)) ℝ).symm
      (((continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin n)) ℝ).symm.toContinuousLinearEquiv
          : (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ] _).comp
        (((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))
          ℝ).flip H).comp (innerSL ℝ)))
  | 3 => T
  | _ => 0

/-- **Lemma B.12.1** of [cartis2022evaluation]: given a vector `g`, a matrix `H` and a trilinear
form `T` on `ℝⁿ`, let `ψ₂(s) = ⟨g, s⟩ + ½ ⟨s, H s⟩` and `ψ₃(s) = ψ₂(s) + (1/6) T[s]³`. If
`min_{‖s‖ ≤ Δ} ψ₃(s) = 0`, then `min_{‖s‖ ≤ Δ} ψ₂(s) = 0`. -/
theorem lemma_B_12_1 (g : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) ℝ) (Δ : ℝ)
    (h : sInf ((fun s => ⟪g, s⟫ + 1 / 2 * ⟪s, H s⟫ + 1 / 6 * T (fun _ => s)) ''
      closedBall 0 Δ) = 0) :
    sInf ((fun s => ⟪g, s⟫ + 1 / 2 * ⟪s, H s⟫) '' closedBall 0 Δ) = 0 := by
  rcases lt_or_ge Δ 0 with hΔ | hΔ
  · rw [closedBall_eq_empty.2 hΔ, image_empty, Real.sInf_empty]
  set D := lemmaB121Data g H T
  have h1 : ∀ s, (D 1 fun _ => s) = ⟪g, s⟫ := fun s => by
    simp [D, lemmaB121Data]
  have h2 : ∀ s, (D 2 fun _ => s) = ⟪s, H s⟫ := fun s => by
    simp [D, lemmaB121Data, Fin.tail]
  have h3 : ∀ s, (D 3 fun _ => s) = T fun _ => s := fun _ => rfl
  have key : ∀ (j : ℕ) (ψ : EuclideanSpace ℝ (Fin n) → ℝ), (∀ s, D.taylorDecrement j s = -ψ s) →
      sInf (ψ '' closedBall 0 Δ) = -Optimization.taylorMeasure D j Δ univ := by
    intro j ψ hψ
    rw [Optimization.taylorMeasure_eq_sSup, inter_univ, Real.sInf_def, neg_inj, ← image_neg_eq_neg,
      image_image]
    simp only [hψ]
  have e3 := key 3 (fun s => ⟪g, s⟫ + 1 / 2 * ⟪s, H s⟫ + 1 / 6 * T (fun _ => s)) fun s => by
    rw [D.taylorDecrement_three, h1, h2, h3]; ring
  have e2 := key 2 (fun s => ⟪g, s⟫ + 1 / 2 * ⟪s, H s⟫) fun s => by
    rw [D.taylorDecrement_two, h1, h2]; ring
  rw [e3, neg_eq_zero] at h
  rw [e2, Optimization.taylorMeasure_two_eq_zero_of_three D hΔ h, neg_zero]

end CartisGouldToint.AppendixB
