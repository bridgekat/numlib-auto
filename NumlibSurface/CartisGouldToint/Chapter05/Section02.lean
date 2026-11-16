/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.MultivariateTaylor.LinearComp

/-!
# Cartis, Gould and Toint, Section 5.2: Partially separable problems

This module formalizes the partially separable functions of Section 5.2 of [cartis2022evaluation]. A
function $f : \mathbb{R}^n \to \mathbb{R}$ is partially separable if
$f(x) = \sum_{i=1}^m f_i(U_i x)$ for element functions $f_i : \mathbb{R}^{n_i} \to \mathbb{R}$ and
$n_i \times n$ matrices $U_i$ (5.2.1). The Taylor polynomial of such a function then splits in the
same way (5.2.2), so that a Taylor model of $f$ is a sum of Taylor models of the element functions.
The proof uses the Taylor polynomial of a function composed with a linear map from
`Numlib.Analysis.Calculus.MultivariateTaylor.LinearComp`. The section has no numbered results.

## Main definitions

* Equation (5.2.1), `CartisGouldToint.Chapter05.IsPartiallySeparable`: $f(x) = \sum_i f_i(U_i x)$
  for all $x$.

## Main results

* Equation (5.2.2), `CartisGouldToint.Chapter05.taylorPolynomial_partiallySeparable`:
  $T_{f,p}(x, s) = \sum_i T_{f_i,p}(U_i x, U_i s)$.

## Implementation notes

* The space $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`. The matrices $U_i$ are continuous linear
  maps from $\mathbb{R}^n$ to $\mathbb{R}^{n_i}$, and $T_{f,p}(x, s)$ is `taylorPolynomial f p x s`.

## Not formalized

* The remark that partially separable models can be used in trust-region and adaptive-regularization
  methods without a change of their complexity bounds. It is a statement about the inputs of those
  algorithms.
* The structured trust regions and the element-wise regularizations of the Notes.
-/

namespace CartisGouldToint.Chapter05

variable {n m : ℕ} {d : Fin m → ℕ}

/-- **Equation (5.2.1)** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$, let
$f_i : \mathbb{R}^{n_i} \to \mathbb{R}$ for $i = 1, \dots, m$, and let
$U_i : \mathbb{R}^n \to \mathbb{R}^{n_i}$ be linear maps. The function $f$ is **partially
separable** with the element functions $f_i$ and the maps $U_i$ if
$$f(x) = \sum_{i=1}^m f_i(U_i x) \quad \text{for all } x \in \mathbb{R}^n.$$

The book writes $U_i$ as an $n_i \times n$ matrix. Here $U_i$ is a continuous linear map, and
$n_i$ is `d i`. -/
def IsPartiallySeparable (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (fᵢ : (i : Fin m) → EuclideanSpace ℝ (Fin (d i)) → ℝ)
    (U : (i : Fin m) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (d i))) : Prop :=
  ∀ x, f x = ∑ i, fᵢ i (U i x)

/-- The function $f$ is partially separable with the element functions $f_i$ and the maps $U_i$ if
and only if $f(x) = \sum_i f_i(U_i x)$ for all $x \in \mathbb{R}^n$. -/
theorem isPartiallySeparable_iff {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {fᵢ : (i : Fin m) → EuclideanSpace ℝ (Fin (d i)) → ℝ}
    {U : (i : Fin m) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (d i))} :
    IsPartiallySeparable f fᵢ U ↔ ∀ x, f x = ∑ i, fᵢ i (U i x) :=
  Iff.rfl

/-- If $f$ is partially separable with the element functions $f_i$ and the maps $U_i$, then $f$ is
the function $x \mapsto \sum_i f_i(U_i x)$. -/
theorem IsPartiallySeparable.eq {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {fᵢ : (i : Fin m) → EuclideanSpace ℝ (Fin (d i)) → ℝ}
    {U : (i : Fin m) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (d i))}
    (h : IsPartiallySeparable f fᵢ U) : f = fun x => ∑ i, fᵢ i (U i x) :=
  funext h

/-- **Equation (5.2.2)** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$ be
partially separable with the element functions $f_i$ and the linear maps $U_i$, let
$p \in \mathbb{N}$ and $x \in \mathbb{R}^n$, and suppose that each $f_i$ is $p$ times
continuously differentiable at $U_i x$. Then for every $s \in \mathbb{R}^n$ the Taylor
polynomials of degree $p$ satisfy
$$T_{f,p}(x, s) = \sum_{i=1}^m T_{f_i,p}(U_i x, U_i s).$$

The Taylor polynomial $T_{f,p}(x, s)$ is `taylorPolynomial f p x s`. -/
theorem taylorPolynomial_partiallySeparable {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {fᵢ : (i : Fin m) → EuclideanSpace ℝ (Fin (d i)) → ℝ}
    {U : (i : Fin m) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (d i))}
    (h : IsPartiallySeparable f fᵢ U) {p : ℕ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ∀ i, ContDiffAt ℝ p (fᵢ i) (U i x)) (s : EuclideanSpace ℝ (Fin n)) :
    taylorPolynomial f p x s = ∑ i, taylorPolynomial (fᵢ i) p (U i x) (U i s) := by
  rw [h.eq]
  exact taylorPolynomial_finset_sum_comp_continuousLinearMap U (fun i _ => hf i) s

end CartisGouldToint.Chapter05
