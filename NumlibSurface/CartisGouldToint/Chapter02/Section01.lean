import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.AnchoredLipschitzDerivs

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
  `L = L_{f,1} ≥ 1` as in the book; it is the anchored smoothness assumption
  `LipschitzDerivsAnchored` of order `1` on the whole space, with `L ≥ 1`.

## Main results

* `AssumptionGL.lipschitz`, `AssumptionGL.of_lipschitz` — f.gL in the gradient form (2.1.5);
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
`‖∇f(x) - ∇f(y)‖ ≤ L ‖x - y‖` for all `x, y` (2.1.5). It is stated as the anchored smoothness
assumption of order `1` on the whole space (`C = A = ℝⁿ`) together with `L ≥ 1`; the gradient
form is `AssumptionGL.lipschitz` and `AssumptionGL.of_lipschitz`. -/
abbrev AssumptionGL (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) : Prop :=
  LipschitzDerivsAnchored f univ univ 1 1 (fun _ => L) ∧ 1 ≤ L

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

/-- Under f.gL, `f` is continuously differentiable. -/
theorem contDiff (h : AssumptionGL f L) : ContDiff ℝ 1 f :=
  h.1.contDiff

/-- The Lipschitz constant of f.gL satisfies `L_{f,1} ≥ 1`. -/
theorem one_le (h : AssumptionGL f L) : 1 ≤ L :=
  h.2

/-- **Bridge to the backbone.** Under f.gL, `∇¹f` is `L`-Lipschitz on `ℝⁿ` as a multilinear map:
`IteratedFDerivLipschitzOn f 1 L univ`. -/
theorem iteratedFDerivLipschitzOn (h : AssumptionGL f L) :
    IteratedFDerivLipschitzOn f 1 L univ :=
  (lipschitzDerivsAnchored_univ_top_iff.1 h.1).2

/-- f.gL from a `C¹` function whose first derivative is `L`-Lipschitz on `ℝⁿ`, `L ≥ 1`. -/
theorem of_iteratedFDerivLipschitzOn (hf : ContDiff ℝ 1 f) (hL1 : 1 ≤ L)
    (hL : IteratedFDerivLipschitzOn f 1 L univ) : AssumptionGL f L :=
  ⟨lipschitzDerivsAnchored_univ_top_iff.2 ⟨hf, hL⟩, hL1⟩

/-- The gradient is `L`-Lipschitz (2.1.5). -/
theorem lipschitz (h : AssumptionGL f L) (x y : EuclideanSpace ℝ (Fin n)) :
    ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖ := by
  rw [← norm_fderiv_sub_fderiv, ← norm_iteratedFDeriv_one_sub]
  exact iteratedFDerivLipschitzOn_iff.1 h.iteratedFDerivLipschitzOn x (mem_univ _) y (mem_univ _)

/-- f.gL in the gradient form (2.1.5): a `C¹` function with `L`-Lipschitz gradient, `L ≥ 1`. -/
theorem of_lipschitz (hf : ContDiff ℝ 1 f) (hL1 : 1 ≤ L)
    (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) : AssumptionGL f L := by
  refine of_iteratedFDerivLipschitzOn hf hL1 (iteratedFDerivLipschitzOn_iff.2 fun x _ y _ => ?_)
  rw [norm_iteratedFDeriv_one_sub, norm_fderiv_sub_fderiv]
  exact hL x y

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

/-- Under f.gL, `‖∇²f(x)‖ ≤ L` for every `x` (operator norm; Theorem A.8.5 of
[cartis2022evaluation] with `p = 1`). No second-order smoothness is needed: where `∇f` is not
differentiable, `∇²f` is `0` by convention. -/
theorem norm_iteratedFDeriv_two_le (h : AssumptionGL f L) (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ 2 f x‖ ≤ L :=
  norm_iteratedFDeriv_succ_le_of_lipschitzOn isOpen_univ h.nonneg h.iteratedFDerivLipschitzOn
    (mem_univ x)

end AssumptionGL

end CartisGouldToint.Chapter02
