import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.LipschitzIteratedFDeriv

/-!
# Cartis–Gould–Toint §2.1: A requirement

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §2.1: the standing assumptions
of Part IA on the objective `f : ℝⁿ → ℝ` (with `ℝⁿ = EuclideanSpace ℝ (Fin n)`) of the
unconstrained problem (2.1.1).

## Main definitions

* `AssumptionBb f flow` — f.Bb: `f` is bounded below by `flow` on `ℝⁿ`.
* `AssumptionC1 f` — f.C1: `f` is continuously differentiable on `ℝⁿ`.
* `AssumptionGL f L` — f.gL: `f` is `C¹` and its gradient is `L`-Lipschitz (2.1.5), with
  `L = L_{f,1} ≥ 1` as in the book.

## Main results

* `AssumptionGL.iteratedFDerivLipschitzOn` — f.gL in the form used by the Taylor remainder
  bounds: the first derivative (as a multilinear map) is `L`-Lipschitz on `ℝⁿ`.
* `AssumptionGL.norm_iteratedFDeriv_two_le` — under f.gL the second derivative is bounded by
  `L` in operator norm (Theorem A.8.5, one direction).

The one-dimensional example showing that f.Bb and f.C1 alone admit no complexity bound is
discussion, not a numbered result, and is not formalized.
-/

open Set

namespace CartisGouldToint.Chapter02

variable {n : ℕ}

/-- **Assumption f.Bb** of [cartis2022evaluation] (§2.1): `f` is bounded below on `ℝⁿ` by the
constant `flow` (`f_low`), i.e. `f x ≥ flow` for all `x`. -/
def AssumptionBb (f : EuclideanSpace ℝ (Fin n) → ℝ) (flow : ℝ) : Prop :=
  ∀ x, flow ≤ f x

/-- **Assumption f.C1** of [cartis2022evaluation] (§2.1): `f` is continuously differentiable
on `ℝⁿ`. -/
def AssumptionC1 (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ContDiff ℝ 1 f

/-- **Assumption f.gL** of [cartis2022evaluation] (§2.1): `f` is continuously differentiable on
`ℝⁿ` and its gradient is Lipschitz continuous with constant `L = L_{f,1} ≥ 1`,
`‖∇f(x) - ∇f(y)‖ ≤ L ‖x - y‖` for all `x, y` (2.1.5). -/
structure AssumptionGL (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) : Prop where
  /-- `f` is continuously differentiable. -/
  contDiff : ContDiff ℝ 1 f
  /-- The Lipschitz constant satisfies `L_{f,1} ≥ 1`. -/
  one_le : 1 ≤ L
  /-- The gradient is `L`-Lipschitz (2.1.5). -/
  lipschitz : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖

/-- f.Bb unfolded: `f` is bounded below by `f_low` everywhere. -/
theorem assumptionBb_iff {f : EuclideanSpace ℝ (Fin n) → ℝ} {flow : ℝ} :
    AssumptionBb f flow ↔ ∀ x, flow ≤ f x :=
  Iff.rfl

/-- f.C1 unfolded: `f` is continuously differentiable. -/
theorem assumptionC1_iff {f : EuclideanSpace ℝ (Fin n) → ℝ} :
    AssumptionC1 f ↔ ContDiff ℝ 1 f :=
  Iff.rfl

/-- The gradient and the first derivative of a real function on `ℝⁿ` have the same
increments in norm. -/
theorem norm_fderiv_sub_fderiv (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ f x - fderiv ℝ f y‖ = ‖gradient f x - gradient f y‖ := by
  rw [gradient, gradient, ← map_sub, LinearIsometryEquiv.norm_map]

/-- The first iterated derivative and the first derivative have the same increments in
norm. -/
theorem norm_iteratedFDeriv_one_sub (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y‖ = ‖fderiv ℝ f x - fderiv ℝ f y‖ := by
  have e : ∀ z, iteratedFDeriv ℝ 1 f z =
      (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin n)) ℝ).symm (fderiv ℝ f z) := by
    intro z; ext m; simp
  rw [e, e, ← map_sub, LinearIsometryEquiv.norm_map]

namespace AssumptionGL

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}

/-- f.gL implies f.C1. -/
theorem assumptionC1 (h : AssumptionGL f L) : AssumptionC1 f :=
  h.contDiff

/-- A function satisfying f.gL is differentiable. -/
theorem differentiable (h : AssumptionGL f L) : Differentiable ℝ f :=
  h.contDiff.differentiable one_ne_zero

/-- The Lipschitz constant of f.gL is positive. -/
theorem pos (h : AssumptionGL f L) : 0 < L :=
  zero_lt_one.trans_le h.one_le

/-- The Lipschitz constant of f.gL is nonnegative. -/
theorem nonneg (h : AssumptionGL f L) : 0 ≤ L :=
  h.pos.le

/-- **Bridge to the backbone.** Under f.gL, `∇¹f` is `L`-Lipschitz on `ℝⁿ` as a multilinear map:
`IteratedFDerivLipschitzOn f 1 L univ`. -/
theorem iteratedFDerivLipschitzOn (h : AssumptionGL f L) :
    IteratedFDerivLipschitzOn f 1 L univ := by
  rw [iteratedFDerivLipschitzOn_iff]
  intro x _ y _
  rw [norm_iteratedFDeriv_one_sub, norm_fderiv_sub_fderiv]
  exact h.lipschitz x y

/-- Under f.gL, `‖∇²f(x)‖ ≤ L` for every `x` (operator norm; Theorem A.8.5 of
[cartis2022evaluation] with `p = 1`). No second-order smoothness is needed: where `∇f` is not
differentiable, `∇²f` is `0` by convention. -/
theorem norm_iteratedFDeriv_two_le (h : AssumptionGL f L) (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ 2 f x‖ ≤ L :=
  norm_iteratedFDeriv_succ_le_of_lipschitzOn isOpen_univ h.nonneg h.iteratedFDerivLipschitzOn
    (mem_univ x)

end AssumptionGL

/-- f.gL is `C¹` with an `L`-Lipschitz first derivative on `ℝⁿ` (the backbone predicate
`IteratedFDerivLipschitzOn f 1 L univ`) and `L ≥ 1`. -/
theorem assumptionGL_iff {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ} :
    AssumptionGL f L ↔ ContDiff ℝ 1 f ∧ 1 ≤ L ∧ IteratedFDerivLipschitzOn f 1 L univ := by
  refine ⟨fun h => ⟨h.contDiff, h.one_le, h.iteratedFDerivLipschitzOn⟩, fun ⟨h1, h2, h3⟩ =>
    ⟨h1, h2, fun x y => ?_⟩⟩
  rw [← norm_fderiv_sub_fderiv, ← norm_iteratedFDeriv_one_sub]
  exact iteratedFDerivLipschitzOn_iff.1 h3 x (mem_univ _) y (mem_univ _)

end CartisGouldToint.Chapter02
