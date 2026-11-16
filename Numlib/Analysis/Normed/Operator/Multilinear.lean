/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Operator.Bilinear`, beside `ContinuousLinearMap.le_opNorm₂`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.RCLike.Basic

/-!
# Operator-norm estimates for curried multilinear maps

This file gives elementary bounds for continuous bilinear and trilinear maps on a real normed space
$X$ in curried form, as elements of $L(X, L(X, X))$ and $L(X, L(X, L(X, X)))$. This is the shape of
an iterated Fréchet derivative that is carried as a chain of `ContinuousLinearMap`s instead of as a
`ContinuousMultilinearMap`. The bounds control the remainder of a Taylor expansion whose
perturbation is known only to first order, as in the analysis of Runge–Kutta methods in
[quarteroni2000numerical], §11.8.

## Main results

* `ContinuousLinearMap.le_opNorm₃`: a curried trilinear map satisfies
  $\|Cxyz\| \le \|C\| \|x\| \|y\| \|z\|$.
* `norm_bilinear_diag_sub_le`: the diagonal $w \mapsto B w w$ of a bilinear map is Lipschitz on
  bounded sets, with the first-order cross terms kept explicitly.
* `norm_trilinear_diag_sub_le`: the diagonal $w \mapsto C w w w$ of a trilinear map is Lipschitz on
  bounded sets.
* `ContinuousLinearMap.norm_comp_le_of_norm_le_one`: composition with a map of norm at most $1$ on
  the left does not increase the operator norm.

## Implementation notes

* `ContinuousLinearMap.le_opNorm₃` is the three-argument companion of Mathlib's
  `ContinuousLinearMap.le_opNorm₂`.
* `ContinuousLinearMap.norm_comp_le_of_norm_le_one`, applied at each level of a curried tower,
  carries a bound on the derivatives of a map to the derivatives of its composition with a
  projection.
-/

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **The operator bound for a trilinear map.** Let $X$ be a real normed space and let
$C \in L(X, L(X, L(X, X)))$. Then for all $x, y, z \in X$, $$\|C x y z\| \le \|C\| \, \|x\| \,
\|y\| \, \|z\|.$$

This is the three-argument companion of `ContinuousLinearMap.le_opNorm₂`. -/
theorem ContinuousLinearMap.le_opNorm₃ (C : X →L[ℝ] X →L[ℝ] X →L[ℝ] X) (x y z : X) :
    ‖C x y z‖ ≤ ‖C‖ * ‖x‖ * ‖y‖ * ‖z‖ := by
  calc ‖C x y z‖ ≤ ‖C x y‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖C‖ * ‖x‖ * ‖y‖ * ‖z‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm₂ _ _ _

/-- **The diagonal of a bilinear map under a perturbation.** Let $X$ be a real normed space, let
$B \in L(X, L(X, X))$, and let $g, d, e \in X$. Then $$\|B(g + d)(g + d) - B g g - B e g - B g
e\| \le \|B\| \, \|d - e\| \, \|g\| + \|B\| \, \|g\| \, \|d - e\| + \|B\| \, \|d\|^2.$$

Here $e$ plays the role of a first approximation of the perturbation $d$. The difference on the
left is $B(d - e)g + Bg(d - e) + Bdd$. This bound controls the $h^3$ error of a Runge–Kutta
stage in [quarteroni2000numerical], §11.8. -/
theorem norm_bilinear_diag_sub_le (B : X →L[ℝ] X →L[ℝ] X) (g d e : X) :
    ‖B (g + d) (g + d) - B g g - B e g - B g e‖
      ≤ ‖B‖ * ‖d - e‖ * ‖g‖ + ‖B‖ * ‖g‖ * ‖d - e‖ + ‖B‖ * ‖d‖ * ‖d‖ := by
  have key : B (g + d) (g + d) - B g g - B e g - B g e
      = B (d - e) g + B g (d - e) + B d d := by
    simp only [map_add, map_sub, _root_.add_apply, _root_.sub_apply]
    abel
  rw [key]
  refine norm_add₃_le.trans ?_
  gcongr <;> exact ContinuousLinearMap.le_opNorm₂ _ _ _

/-- **The diagonal of a trilinear map is Lipschitz on bounded sets.** Let $X$ be a real normed
space, let $C \in L(X, L(X, L(X, X)))$, and let $x, y \in X$. Then $$\|Cxxx - Cyyy\| \le \|C\|
\, \|x - y\| \, \|x\|^2 + \|C\| \, \|y\| \, \|x - y\| \, \|x\| + \|C\| \, \|y\|^2 \, \|x -
y\|,$$ that is, $\|Cxxx - Cyyy\| \le \|C\| (\|x\|^2 + \|x\| \|y\| + \|y\|^2) \|x - y\|$.

The bound follows from the identity $Cxxx - Cyyy = C(x - y)xx + Cy(x - y)x + Cyy(x - y)$. It is
used in [quarteroni2000numerical], §11.8. -/
theorem norm_trilinear_diag_sub_le (C : X →L[ℝ] X →L[ℝ] X →L[ℝ] X) (x y : X) :
    ‖C x x x - C y y y‖
      ≤ ‖C‖ * ‖x - y‖ * ‖x‖ * ‖x‖ + ‖C‖ * ‖y‖ * ‖x - y‖ * ‖x‖
        + ‖C‖ * ‖y‖ * ‖y‖ * ‖x - y‖ := by
  have key : C x x x - C y y y = C (x - y) x x + C y (x - y) x + C y y (x - y) := by
    simp only [map_sub, _root_.sub_apply]
    abel
  rw [key]
  refine norm_add₃_le.trans ?_
  gcongr <;> exact ContinuousLinearMap.le_opNorm₃ _ _ _ _

/-- **Composition with a map of norm at most one does not increase the operator norm.** Let $E$,
$F$, $G$ be normed spaces over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $J : F \to G$ be a
bounded linear map with $\|J\| \le 1$, and let $L : E \to F$ be bounded linear. Then $$\|J \circ
L\| \le \|L\|.$$

Applied at each level of multilinearity, this carries a bound on the derivatives of a vector
field $f$ to the derivatives of the autonomized field $(1, f)$. -/
theorem ContinuousLinearMap.norm_comp_le_of_norm_le_one {𝕜 : Type*} [RCLike 𝕜]
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] (J : F →L[𝕜] G) (hJ : ‖J‖ ≤ 1)
    (L : E →L[𝕜] F) : ‖J.comp L‖ ≤ ‖L‖ := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc ‖J‖ * ‖L‖ ≤ 1 * ‖L‖ := by
        refine mul_le_mul_of_nonneg_right hJ (ContinuousLinearMap.opNorm_nonneg L)
    _ = ‖L‖ := one_mul _

