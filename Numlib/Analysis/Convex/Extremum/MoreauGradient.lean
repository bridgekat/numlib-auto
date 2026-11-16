/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Ops
import Numlib.Analysis.Convex.Extremum.Prox
import Numlib.Analysis.Convex.Subdifferential.LegendreType

/-!
# The gradient formulas of Moreau's theorem

Let $E$ be a finite-dimensional real inner product space, let $w(z) = \tfrac12 \|z\|^2$, and let $f$
be a closed proper convex function on $E$ with conjugate $f^*$. Write
$\operatorname{prox}(z \mid f)$ for the proximal point of $z$ with respect to $f$: the unique point
that minimizes $x \mapsto f(x) + w(z - x)$. Then the Moreau envelope $f \mathbin{\square} w$ is
finite and differentiable everywhere, and
$$\nabla (f \mathbin{\square} w)(z) = z - \operatorname{prox}(z \mid f), \qquad \nabla (f^*
  \mathbin{\square} w)(z) = \operatorname{prox}(z \mid f).$$
So the two terms of Moreau's splitting $z = \operatorname{prox}(z \mid f) + \operatorname{prox}(z
\mid f^*)$ are the gradients of the two envelopes. These are the gradient formulas of Theorem 31.5
of [rockafellar1970convex], and the presentation follows §31 of that book.

The splitting itself is in `Numlib.Analysis.Convex.Extremum.Prox`. This module adds two facts: the
subdifferential $\partial (f \mathbin{\square} w)(z)$ is a single point, and a convex function whose
subdifferential at $z$ is a single point is differentiable at $z$.

## Main results

* `ConvexAnalysis.subdifferential_infConv_quadFn`: $\partial (f \mathbin{\square} w)(z) =
  \{\operatorname{prox}(z \mid f^*)\}$.
* `ConvexAnalysis.hasGradientAtFn_infConv_quadFn`,
  `ConvexAnalysis.hasGradientAtFn_infConv_convexConj_quadFn`: the envelopes $f \mathbin{\square} w$
  and $f^* \mathbin{\square} w$ have the gradients $\operatorname{prox}(z \mid f^*)$ and
  $\operatorname{prox}(z \mid f)$ at $z$, in the form `ConvexAnalysis.HasGradientAtFn`.
* `ConvexAnalysis.gradient_infConv_quadFn`, `ConvexAnalysis.gradient_infConv_convexConj_quadFn`: the
  same formulas for the Mathlib `gradient`, $\nabla (f \mathbin{\square} w)(z) = z -
  \operatorname{prox}(z \mid f)$ and $\nabla (f^* \mathbin{\square} w)(z) = \operatorname{prox}(z
  \mid f)$.
* `ConvexAnalysis.closedProperConvexFn_infConv_quadFn`: the Moreau envelope is finite everywhere,
  hence a closed proper convex function.
* `ConvexAnalysis.convexConj_infConv_quadFn`: $(f \mathbin{\square} w)^* = f^* + w$.

## Implementation notes

* No relative-interior or exactness hypothesis is needed. The formula for the conjugate of an
  infimal convolution is used only in the direction that holds without hypotheses. The constraint
  qualification for the subgradient sum rule comes from the fact that $w$ is finite and continuous.
-/

namespace ConvexAnalysis

open scoped Pointwise RealInnerProductSpace

section MoreauGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-! ### The Moreau envelope is closed proper convex -/

/-- Let $f$ be a closed proper convex function on a finite-dimensional real inner product space $E$.
Then the effective domain of the Moreau envelope $f \mathbin{\square} w$ is all of $E$. -/
theorem convexDom_infConv_quadFn (hf : ClosedProperConvexFn f) :
    convexDom (infConv f (quadFn (innerₗ E))) = Set.univ :=
  Set.eq_univ_of_forall fun z => mem_convexDom.2 (lt_top_iff_ne_top.2 (infConv_quadFn_ne_top hf z))

/-- Let $f$ be a closed proper convex function on a finite-dimensional real inner product space $E$,
and let $w(z) = \tfrac12 \|z\|^2$. Then the Moreau envelope $f \mathbin{\square} w$ is a closed
proper convex function.

The envelope is convex and finite everywhere (`ConvexAnalysis.convexDom_infConv_quadFn`), and a
convex function that is finite everywhere on a finite-dimensional space is closed. -/
theorem closedProperConvexFn_infConv_quadFn (hf : ClosedProperConvexFn f) :
    ClosedProperConvexFn (infConv f (quadFn (innerₗ E))) := by
  have hc : ConvexFn (infConv f (quadFn (innerₗ E))) := convexFn_infConv hf.convex convexFn_quadFn
  have hp : ProperConvex (infConv f (quadFn (innerₗ E))) :=
    ⟨⟨0, mem_convexDom.2 (lt_top_iff_ne_top.2 (infConv_quadFn_ne_top hf 0))⟩,
      fun z => infConv_quadFn_ne_bot hf z⟩
  exact ⟨hc, closedConvex_of_convexDom_eq_univ hc hp (convexDom_infConv_quadFn hf), hp⟩

omit [FiniteDimensional ℝ E] in
/-- Let $f$ be any function on a real inner product space $E$ with values in the extended reals, and
let $w(z) = \tfrac12 \|z\|^2$. Then the conjugate of the Moreau envelope is
$$(f \mathbin{\square} w)^* = f^* + w.$$

The conjugate of an infimal convolution is the sum of the conjugates, and $w^* = w$
(`ConvexAnalysis.convexConj_quadFn`). Conjugates are taken with respect to the inner product. -/
theorem convexConj_infConv_quadFn (f : E → EReal) :
    convexConj (innerₗ E) (infConv f (quadFn (innerₗ E))) = convexConj (innerₗ E) f
        + quadFn (innerₗ E) := by
  rw [convexConj_infConv]
  congr 1
  funext y
  exact convexConj_quadFn y

/-! ### The gradient formulas -/

/-- **The subdifferential of a Moreau envelope is a single point.** Let $f$ be a closed proper
convex function on a finite-dimensional real inner product space $E$, and let
$w(z) = \tfrac12 \|z\|^2$. Then for every $z \in E$,
$$\partial (f \mathbin{\square} w)(z) = \{\operatorname{prox}(z \mid f^*)\}.$$

Conjugate inversion turns $y \in \partial (f \mathbin{\square} w)(z)$ into
$z \in \partial (f^* + w)(y)$. The sum rule splits this subdifferential as
$\partial f^*(y) + \{y\}$, and the remaining condition $z - y \in \partial f^*(y)$ characterizes
$\operatorname{prox}(z \mid f^*)$. -/
theorem subdifferential_infConv_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    subdifferential (innerₗ E) (infConv f (quadFn (innerₗ E))) z
      = {prox (innerₗ E) (convexConj (innerₗ E) f) z} := by
  have hg := closedProperConvexFn_infConv_quadFn hf
  have hcf := closedProperConvexFn_convexConj (B := innerₗ E) hf
  ext y
  rw [Set.mem_singleton_iff, ← mem_subdifferential_convexConj_innerL_iff hg.convex hg.closed z y,
    convexConj_infConv_quadFn, (isExactSum_quadFn hcf).subdifferential_add, subdifferential_quadFn]
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

/-- Let $f$ be a closed proper convex function on a finite-dimensional real inner product space $E$.
Then $\operatorname{prox}(z \mid f^*) = z - \operatorname{prox}(z \mid f)$ for every $z \in E$:
the two proximal points add up to $z$. -/
theorem prox_convexConj_eq (hf : ClosedProperConvexFn f) (z : E) :
    prox (innerₗ E) (convexConj (innerₗ E) f) z = z - prox (innerₗ E) f z :=
  eq_sub_of_add_eq (by rw [add_comm]; exact prox_add_prox_convexConj hf z)

/-- Let $f$ be a closed proper convex function on a finite-dimensional real inner product space $E$,
and let $w(z) = \tfrac12 \|z\|^2$. Then for every $z \in E$, the Moreau envelope
$f \mathbin{\square} w$ is differentiable at $z$, with gradient
$$\nabla (f \mathbin{\square} w)(z) = \operatorname{prox}(z \mid f^*).$$

The subdifferential at $z$ is a single point (`ConvexAnalysis.subdifferential_infConv_quadFn`),
so the envelope is differentiable there. The gradient is stated as
`ConvexAnalysis.HasGradientAtFn` with the functional `InnerProductSpace.toDual ℝ E` applied to
$\operatorname{prox}(z \mid f^*)$. -/
theorem hasGradientAtFn_infConv_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    HasGradientAtFn (infConv f (quadFn (innerₗ E)))
      (InnerProductSpace.toDual ℝ E (prox (innerₗ E) (convexConj (innerₗ E) f) z)) z :=
  hasGradientAtFn_toDual_of_subdifferential_eq_singleton
    (closedProperConvexFn_infConv_quadFn hf).convex
    (closedProperConvexFn_infConv_quadFn hf).proper (subdifferential_infConv_quadFn hf z)

/-- Let $f$ be a closed proper convex function on a finite-dimensional real inner product space $E$,
and let $w(z) = \tfrac12 \|z\|^2$. Then for every $z \in E$, the Moreau envelope
$f^* \mathbin{\square} w$ of the conjugate is differentiable at $z$, with gradient
$$\nabla (f^* \mathbin{\square} w)(z) = \operatorname{prox}(z \mid f).$$

This is `ConvexAnalysis.hasGradientAtFn_infConv_quadFn` applied to $f^*$, together with
$\operatorname{prox}(z \mid f^{**}) = z - \operatorname{prox}(z \mid f^*) =
\operatorname{prox}(z \mid f)$. The gradient is stated as `ConvexAnalysis.HasGradientAtFn` with
the functional `InnerProductSpace.toDual ℝ E` applied to $\operatorname{prox}(z \mid f)$. -/
theorem hasGradientAtFn_infConv_convexConj_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    HasGradientAtFn (infConv (convexConj (innerₗ E) f) (quadFn (innerₗ E)))
      (InnerProductSpace.toDual ℝ E (prox (innerₗ E) f z)) z := by
  have hcf := closedProperConvexFn_convexConj (B := innerₗ E) hf
  have h := hasGradientAtFn_infConv_quadFn hcf z
  rwa [prox_convexConj_eq hcf z, prox_convexConj_eq hf z, sub_sub_cancel] at h

/-- Let $f$ be a closed proper convex function on a finite-dimensional real inner product space $E$,
and let $w(z) = \tfrac12 \|z\|^2$. Then for every $z \in E$,
$$\nabla (f \mathbin{\square} w)(z) = z - \operatorname{prox}(z \mid f).$$
This is the first gradient formula in Theorem 31.5 of [rockafellar1970convex].

The gradient is the Mathlib `gradient` of the real-valued function
$u \mapsto (f \mathbin{\square} w)(u)$, obtained by `EReal.toReal`; the envelope is finite
everywhere. -/
theorem gradient_infConv_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    gradient (fun u => (infConv f (quadFn (innerₗ E)) u).toReal) z = z - prox (innerₗ E) f z := by
  rw [(hasGradientAtFn_infConv_quadFn hf z).gradient_toReal_eq,
    LinearIsometryEquiv.symm_apply_apply, prox_convexConj_eq hf z]

/-- Let $f$ be a closed proper convex function on a finite-dimensional real inner product space $E$,
and let $w(z) = \tfrac12 \|z\|^2$. Then for every $z \in E$,
$$\nabla (f^* \mathbin{\square} w)(z) = \operatorname{prox}(z \mid f).$$
This is the second gradient formula in Theorem 31.5 of [rockafellar1970convex].

The gradient is the Mathlib `gradient` of the real-valued function
$u \mapsto (f^* \mathbin{\square} w)(u)$, obtained by `EReal.toReal`; the envelope is finite
everywhere. -/
theorem gradient_infConv_convexConj_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    gradient (fun u => (infConv (convexConj (innerₗ E) f) (quadFn (innerₗ E)) u).toReal) z
      = prox (innerₗ E) f z := by
  rw [(hasGradientAtFn_infConv_convexConj_quadFn hf z).gradient_toReal_eq,
    LinearIsometryEquiv.symm_apply_apply]

/-- Let $f$ be a closed proper convex function on a finite-dimensional real inner product space $E$.
Then the Moreau envelope $f \mathbin{\square} w$ is differentiable at every point of $E$. -/
theorem differentiableAtFn_infConv_quadFn (hf : ClosedProperConvexFn f) (z : E) :
    DifferentiableAtFn (infConv f (quadFn (innerₗ E))) z :=
  ⟨_, hasGradientAtFn_infConv_quadFn hf z⟩

end MoreauGradient

end ConvexAnalysis
