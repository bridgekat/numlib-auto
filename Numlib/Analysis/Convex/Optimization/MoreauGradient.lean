import Numlib.Analysis.Convex.Duality.Ops
import Numlib.Analysis.Convex.Optimization.Prox
import Numlib.Analysis.Convex.Subgradient.LegendreType

/-!
# The gradient formulas of Moreau's theorem

For `f` closed proper convex on a finite-dimensional inner product space and `w z = ½‖z‖²`, the
Moreau envelope `f □ w` is finite everywhere and differentiable everywhere, with

`∇(f □ w) z = z - prox (z | f)`,  `∇(f* □ w) z = prox (z | f)`.

So the two halves of Moreau's splitting `z = prox (z | f) + prox (z | f*)` are the gradients of the
two envelopes. The splitting itself is in `Optimization/Prox.lean`; what is added here is that
`∂(f □ w) z` is a single point, and a convex function with a one-point subdifferential at `z` is
differentiable there.

## Main results

* `subgradient_infConv_quadFn` — `∂(f □ w) z = {prox (z | f*)}`.
* `hasGradientAt_infConv_quadFn`, `hasGradientAt_infConv_conj_quadFn`,
  `gradient_infConv_quadFn`, `gradient_infConv_conj_quadFn` — the gradient formulas
  (Theorem 31.5 in [^1]), in `HasGradientAt` form and in terms of Mathlib's `gradient`.
* `closedProperConvexFn_infConv_quadFn` — the Moreau envelope is finite everywhere, hence closed
  proper convex.
* `conj_infConv_quadFn` — `(f □ w)* = f* + w`, since conjugation turns `□` into `+` and `w* = w`.

## Implementation notes

No relative-interior or exactness hypothesis is needed: the conjugate of an infimal convolution is
used in its unconditional direction, and the constraint qualification for the subgradient sum rule
is supplied by `w` being finite and continuous.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §31.
-/

namespace ConvexAnalysis

open scoped Pointwise RealInnerProductSpace

section MoreauGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-! ### The Moreau envelope is closed proper convex -/

/-- The Moreau envelope is finite everywhere. -/
theorem dom_infConv_quadFn (hf : ClosedProperConvexFn f) :
    dom (infConv f (quadFn (innerₗ E))) = Set.univ :=
  Set.eq_univ_of_forall fun z => mem_dom.2 (lt_top_iff_ne_top.2 (infConv_quadFn_ne_top hf z))

/-- Finite everywhere and convex, hence closed. -/
theorem closedProperConvexFn_infConv_quadFn (hf : ClosedProperConvexFn f) :
    ClosedProperConvexFn (infConv f (quadFn (innerₗ E))) := by
  have hc : ConvexFn (infConv f (quadFn (innerₗ E))) := convexFn_infConv hf.convex convexFn_quadFn
  have hp : Proper (infConv f (quadFn (innerₗ E))) :=
    ⟨⟨0, mem_dom.2 (lt_top_iff_ne_top.2 (infConv_quadFn_ne_top hf 0))⟩,
      fun z => infConv_quadFn_ne_bot hf z⟩
  exact ⟨hc, closedFn_of_dom_eq_univ hc hp (dom_infConv_quadFn hf), hp⟩

omit [FiniteDimensional ℝ E] in
/-- The conjugate of a Moreau envelope: `(f □ w)* = f* + w`, since `w* = w`. -/
theorem conj_infConv_quadFn (f : E → EReal) :
    conj (innerₗ E) (infConv f (quadFn (innerₗ E))) = conj (innerₗ E) f + quadFn (innerₗ E) := by
  rw [conj_infConv]
  congr 1
  funext y
  exact conj_quadFn y

/-! ### The gradient formulas -/

/-- **The subdifferential of a Moreau envelope is a single point**: `∂(f □ w) z = {prox (z | f*)}`.
Conjugate inversion turns `y ∈ ∂(f □ w) z` into `z ∈ ∂(f* + w) y`, the sum rule splits that as
`∂f* y + {y}`, and what is left, `z - y ∈ ∂f* y`, characterises `prox (z | f*)`. -/
theorem subgradient_infConv_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    subgradient (innerₗ E) (infConv f (quadFn (innerₗ E))) z
      = {prox (innerₗ E) (conj (innerₗ E) f) z} := by
  have hg := closedProperConvexFn_infConv_quadFn hf
  have hcf := closedProperConvexFn_conj (B := innerₗ E) hf
  ext y
  rw [Set.mem_singleton_iff, ← mem_subgradient_conj_innerL_iff hg.convex hg.closed z y,
    conj_infConv_quadFn, (isExactSum_quadFn hcf).subgradient_add, subgradient_quadFn]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rw [Set.mem_singleton_iff] at hb
    rw [hb] at hab
    have hab' : a + y = z := hab
    refine ((prox_eq_iff hcf z y).2 ?_).symm
    have hza : z - y = a := by rw [← hab']; abel
    rw [hza]
    exact ha
  · intro hy
    exact ⟨z - y, (prox_eq_iff hcf z y).1 hy.symm, y, rfl, by change z - y + y = z; abel⟩

/-- The two proximal points add up to `z`, written here as a formula for the second. -/
theorem prox_conj_eq (hf : ClosedProperConvexFn f) (z : E) :
    prox (innerₗ E) (conj (innerₗ E) f) z = z - prox (innerₗ E) f z :=
  eq_sub_of_add_eq (by rw [add_comm]; exact prox_add_prox_conj hf z)

/-- `prox (z | f*) = ∇(f □ w) z`: the subdifferential is a single point, so the envelope is
differentiable there. -/
theorem hasGradientAt_infConv_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    HasGradientAt (infConv f (quadFn (innerₗ E)))
      (InnerProductSpace.toDual ℝ E (prox (innerₗ E) (conj (innerₗ E) f) z)) z :=
  hasGradientAt_toDual_of_subgradient_eq_singleton
    (closedProperConvexFn_infConv_quadFn hf).convex
    (closedProperConvexFn_infConv_quadFn hf).proper (subgradient_infConv_quadFn hf z)

/-- `prox (z | f) = ∇(f* □ w) z`. The previous statement applied to `f*`, using
`prox (z | f**) = z - prox (z | f*) = prox (z | f)`. -/
theorem hasGradientAt_infConv_conj_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    HasGradientAt (infConv (conj (innerₗ E) f) (quadFn (innerₗ E)))
      (InnerProductSpace.toDual ℝ E (prox (innerₗ E) f z)) z := by
  have hcf := closedProperConvexFn_conj (B := innerₗ E) hf
  have h := hasGradientAt_infConv_quadFn hcf z
  rwa [prox_conj_eq hcf z, prox_conj_eq hf z, sub_sub_cancel] at h

/-- `∇(f □ w) z = z - prox (z | f)`. -/
theorem gradient_infConv_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    gradient (fun u => (infConv f (quadFn (innerₗ E)) u).toReal) z = z - prox (innerₗ E) f z := by
  rw [(hasGradientAt_infConv_quadFn hf z).gradient_toReal_eq,
    LinearIsometryEquiv.symm_apply_apply, prox_conj_eq hf z]

/-- `∇(f* □ w) z = prox (z | f)`. -/
theorem gradient_infConv_conj_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    gradient (fun u => (infConv (conj (innerₗ E) f) (quadFn (innerₗ E)) u).toReal) z
      = prox (innerₗ E) f z := by
  rw [(hasGradientAt_infConv_conj_quadFn hf z).gradient_toReal_eq,
    LinearIsometryEquiv.symm_apply_apply]

/-- The Moreau envelope is differentiable everywhere. -/
theorem differentiableAtFn_infConv_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    DifferentiableAtFn (infConv f (quadFn (innerₗ E))) z :=
  ⟨_, hasGradientAt_infConv_quadFn hf z⟩

end MoreauGradient

end ConvexAnalysis
