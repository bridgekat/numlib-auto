import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.MultivariateTaylor.LinearComp

/-!
# Cartis–Gould–Toint §5.2: Partially separable problems

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §5.2. Functions are on
`ℝⁿ = EuclideanSpace ℝ (Fin n)`; the `n_i × n` matrices `U_i` are continuous linear maps
`ℝⁿ → ℝ^{n_i}`, and `T_{f,p}(x, s)` is `taylorPolynomial f p x s`.

## Main definitions and results

* `IsPartiallySeparable` — partial separability (5.2.1), `f(x) = ∑ᵢ fᵢ(Uᵢ x)`.
* `taylorPolynomial_partiallySeparable` — the decomposition (5.2.2) of the Taylor model,
  `T_{f,p}(x, s) = ∑ᵢ T_{fᵢ,p}(Uᵢ x, Uᵢ s)`.

The section has no numbered results. Its remark that partially separable models can be used in
trust-region and adaptive-regularization methods without changing their complexity bounds is a
statement about the inputs of those algorithms, and the structured trust regions and element-wise
regularizations of the Notes are not formalized.
-/

namespace CartisGouldToint.Chapter05

variable {n m : ℕ} {d : Fin m → ℕ}

/-- `f : ℝⁿ → ℝ` is **partially separable** ([cartis2022evaluation], (5.2.1)) with the element
functions `fᵢ : ℝ^{dᵢ} → ℝ` and the linear maps (`dᵢ × n` matrices) `Uᵢ : ℝⁿ → ℝ^{dᵢ}`,
`i = 1, …, m`, when `f(x) = ∑ᵢ fᵢ(Uᵢ x)` for all `x`. -/
def IsPartiallySeparable (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (fᵢ : (i : Fin m) → EuclideanSpace ℝ (Fin (d i)) → ℝ)
    (U : (i : Fin m) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (d i))) : Prop :=
  ∀ x, f x = ∑ i, fᵢ i (U i x)

theorem isPartiallySeparable_iff {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {fᵢ : (i : Fin m) → EuclideanSpace ℝ (Fin (d i)) → ℝ}
    {U : (i : Fin m) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (d i))} :
    IsPartiallySeparable f fᵢ U ↔ ∀ x, f x = ∑ i, fᵢ i (U i x) :=
  Iff.rfl

/-- A partially separable function is the sum of its element functions composed with the
linear maps. -/
theorem IsPartiallySeparable.eq {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {fᵢ : (i : Fin m) → EuclideanSpace ℝ (Fin (d i)) → ℝ}
    {U : (i : Fin m) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (d i))}
    (h : IsPartiallySeparable f fᵢ U) : f = fun x => ∑ i, fᵢ i (U i x) :=
  funext h

/-- **(5.2.2)** of [cartis2022evaluation]: the Taylor model of a partially separable function is
the sum of the Taylor models of its element functions,
`T_{f,p}(x, s) = ∑ᵢ T_{fᵢ,p}(Uᵢ x, Uᵢ s)`, provided every element function `fᵢ` is `p` times
continuously differentiable at `Uᵢ x`. -/
theorem taylorPolynomial_partiallySeparable {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {fᵢ : (i : Fin m) → EuclideanSpace ℝ (Fin (d i)) → ℝ}
    {U : (i : Fin m) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (d i))}
    (h : IsPartiallySeparable f fᵢ U) {p : ℕ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ∀ i, ContDiffAt ℝ p (fᵢ i) (U i x)) (s : EuclideanSpace ℝ (Fin n)) :
    taylorPolynomial f p x s = ∑ i, taylorPolynomial (fᵢ i) p (U i x) (U i s) := by
  rw [h.eq]
  exact taylorPolynomial_finset_sum_comp_continuousLinearMap U (fun i _ => hf i) s

end CartisGouldToint.Chapter05
