/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Optimization.Optimality.HighOrder

/-!
# Cartis, Gould and Toint, Appendix B: Appendix to Chapter 12

This module formalizes the part of Appendix B of [cartis2022evaluation] that belongs to Chapter 12:
Lemma B.12.1, which justifies the use of the third-order measure $\phi^\delta_{f,3}$ in §12.1.3.
Given $g \in \mathbb{R}^n$, a linear map $H$ and a trilinear form $T$, let $\psi_2(s) = \langle g,
s\rangle + \frac12 \langle s, Hs\rangle$ and $\psi_3(s) = \psi_2(s) + \frac16 T[s]^3$. The lemma
says that if the minimum of $\psi_3$ over the ball $\|s\| \le \Delta$ is $0$, then so is the minimum
of $\psi_2$; thus $\phi^\delta_{f,3}(x) = 0$ implies $\phi^\delta_{f,2}(x) = 0$. The content is the
backbone theorem `Optimization.taylorMeasure_two_eq_zero_of_three` for arbitrary Taylor data,
specialized here to the data $(g, H, T)$ of the book. The proofs of Theorems 12.1.7 and 12.2.6 that
the book gives in this appendix belong to Chapter 12.

## Main results

* Lemma B.12.1, `CartisGouldToint.AppendixB.lemma_B_12_1`: if
  $\min_{\|s\| \le \Delta} \psi_3(s) = 0$, then $\min_{\|s\| \le \Delta} \psi_2(s) = 0$.

## Implementation notes

* $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`. The book's minimum over the closed ball is written
  as `sInf` of the values on the ball; for $\Delta \ge 0$ the minimum is attained, by compactness.

## Deviations from the source

* **Generalization.** Lemma B.12.1 drops the symmetry hypotheses and admits arbitrary radii under
  the infimum convention. See `CartisGouldToint.AppendixB.lemma_B_12_1`.
* **Lemma B.12.1** (generalization). The book assumes that $H$ is symmetric and that $T$ is a
  symmetric trilinear form; neither is needed. See `CartisGouldToint.AppendixB.lemma_B_12_1`.
* **Lemma B.12.1** (generalization). The radius $\Delta$ is arbitrary. For $\Delta < 0$ both minima
  are over the empty set, and the statement holds trivially with the convention `sInf ∅ = 0`. See
  `CartisGouldToint.AppendixB.lemma_B_12_1`.
-/

open Set Metric
open scoped RealInnerProductSpace

namespace CartisGouldToint.AppendixB

variable {n : ℕ}

/-- The Taylor data $(g, H, T)$ of Lemma B.12.1 as a formal multilinear series: its terms of order
$1$, $2$ and $3$ are $s \mapsto \langle g, s\rangle$, $s \mapsto \langle s, Hs\rangle$ and $T$,
and the other terms are $0$. -/
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

/-- **Lemma B.12.1** of [cartis2022evaluation]. Let $g \in \mathbb{R}^n$, let
$H : \mathbb{R}^n \to \mathbb{R}^n$ be a continuous linear map, let $T$ be a continuous
trilinear form on $\mathbb{R}^n$, and let $\Delta \in \mathbb{R}$. Let
$$\psi_2(s) = \langle g, s\rangle + \tfrac12 \langle s, Hs\rangle \quad \text{and} \quad
  \psi_3(s) = \psi_2(s) + \tfrac16 T[s]^3.$$
If $\inf_{\|s\| \le \Delta} \psi_3(s) = 0$, then $\inf_{\|s\| \le \Delta} \psi_2(s) = 0$.

**Generalization.** The book assumes that $H$ is symmetric and that $T$ is symmetric. Neither
assumption is needed. The radius $\Delta$ is arbitrary: for $\Delta < 0$ both infima are over
the empty set and are $0$ by the convention `sInf ∅ = 0`.

For $\Delta \ge 0$ the infima are minima, since the closed ball is compact; they are the book's
minima. The infimum is `sInf` of the image of `Metric.closedBall 0 Δ`.

**Generalization.** The quadratic and cubic coefficient maps need no symmetry hypotheses. The result
uses infima, so even a negative radius is admitted with Lean's empty-set infimum convention.
-/
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
