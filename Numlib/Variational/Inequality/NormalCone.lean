/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Continuity
import Numlib.Analysis.Convex.Duality.Continuity
import Numlib.Analysis.Convex.Duality.Pairing
import Numlib.Analysis.Convex.Extremum.Minimum
import Numlib.Analysis.Convex.Subdifferential.Calculus
import Numlib.Analysis.Convex.Subdifferential.Defs
import Numlib.Analysis.Convex.Subdifferential.Monotone
import Numlib.Variational.Inequality.Basic

/-!
# Variational inequalities in the language of convex analysis

This module translates the elliptic variational inequality of `Numlib.Variational.Inequality.Basic`,
$$u \in K, \qquad \langle f, v - u \rangle \le \langle Au, v - u \rangle + j(v) - j(u)
  \quad \text{for all } v \in K,$$
into the normal cones, subdifferentials and monotone relations of convex analysis. With $N_K(u)$ the
normal cone of $K$ at $u$, $\partial$ the subdifferential and $\delta_K$ the indicator function of
$K$, the inequality of the first kind ($j = 0$) is $f - Au \in N_K(u)$, and the general inequality
is $f - Au \in \partial(j + \delta_K)(u)$. In a Hilbert space, for $j$ convex and lower
semicontinuous, the subdifferential splits as $\partial(j + \delta_K)(u) = \partial j(u) + N_K(u)$.
The variational inequalities follow §11.3 of [han2009theoretical], and the sum rule follows §23 of
[rockafellar1970convex].

The module also shows that a strongly monotone operator has a monotone graph, and that the
first-order condition for a minimizer of a convex function $f$ over a convex set $K$,
$f'(u)(v - u) \ge 0$ for all $v \in K$, is $-f'(u) \in N_K(u)$. This is the sufficiency half of
Theorem 27.4 of [rockafellar1970convex].

## Main results

* `isVariationalInequalitySolution_zero_iff_sub_mem_normalCone`: the inequality of the first kind is
  $u \in K$ and $f - Au \in N_K(u)$.
* `isVariationalInequalitySolution_iff_sub_mem_subdifferential`: the variational inequality is
  $u \in K$ and $f - Au \in \partial(j + \delta_K)(u)$.
* `ConvexOn.isExactSum_coe_indicatorFn`: in a Hilbert space, a convex lower semicontinuous $j$ and
  $\delta_K$ satisfy the constraint qualification of the sum rule.
* `isVariationalInequalitySolution_iff_sub_mem_add_normalCone`: in a Hilbert space, for $j$ convex
  and lower semicontinuous, the variational inequality is $u \in K$ and
  $f - Au \in \partial j(u) + N_K(u)$.
* `IsStronglyMonotoneWith.isMonotoneRel_graph`: a strongly monotone operator with a nonnegative
  constant has a monotone graph.
* `isMinOn_iff_neg_mem_normalCone`, `isMinOn_iff_neg_toDual_symm_mem_normalCone`: a point minimizes
  a convex function over a convex set if and only if the negative derivative, or in a Hilbert space
  the negative gradient, lies in the normal cone.

## Implementation notes

* The variational inequality stays defined as an inequality. Its users work with it as an
  inequality, $A$ is a nonlinear operator and $j$ is real-valued, and a definition through
  `ConvexAnalysis.subdifferential` would bring a coercion to `EReal` into every proof of the
  Hilbert-space theory.
* The normal cone and the subdifferential are taken for the pairing `innerₗ V`, except in
  `isMinOn_iff_neg_mem_normalCone`, which uses the pairing of $V$ with its continuous dual. The
  indicator function $\delta_K$ is `ConvexAnalysis.indicatorFn K`.
* The split of the subdifferential is the sum rule `ConvexAnalysis.IsExactSum.subdifferential_add`
  under the continuity constraint qualification `ConvexAnalysis.IsExactSum.of_continuousAt`. The
  continuity of $j$ is `ConvexOn.continuous_of_lowerSemicontinuous`. The qualification needs a
  compatible pairing, which `ConvexAnalysis.instIsCompatiblePairingInner` supplies by the
  Fréchet–Riesz theorem.
* A real-valued convex function is read as a proper convex `EReal`-valued function by
  `ConvexOn.convexFn_coe` and `ConvexAnalysis.properConvex_coe`.
-/

open ConvexAnalysis
open scoped Pointwise

/-! ### The variational inequality as a normal-cone and a subgradient condition -/

section Inequality

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {A : V → V} {j : V → ℝ} {f : V} {K : Set V} {u : V}

/-- **The inequality of the first kind is a normal-cone condition.** Let $V$ be a real inner product
space, $A : V \to V$, $f \in V$ and $K \subseteq V$. Then $u$ solves the variational inequality
with $j = 0$ if and only if $u \in K$ and $f - Au$ lies in the normal cone of $K$ at $u$:
$$\langle v - u, f - Au \rangle \le 0 \quad \text{for all } v \in K.$$

There is no hypothesis on $A$, $K$ or $V$. The normal cone is `ConvexAnalysis.normalCone` for
the pairing `innerₗ V`. -/
theorem isVariationalInequalitySolution_zero_iff_sub_mem_normalCone :
    IsVariationalInequalitySolution A 0 f K u ↔ u ∈ K ∧ f - A u ∈ normalCone (innerₗ V) K u := by
  unfold IsVariationalInequalitySolution
  rw [mem_normalCone]
  refine and_congr_right fun _ => forall₂_congr fun v _ => ?_
  rw [Pi.zero_apply, Pi.zero_apply, sub_zero, add_zero, innerₗ_apply_apply,
    inner_sub_right (v - u) f (A u), sub_nonpos, real_inner_comm (v - u) f,
    real_inner_comm (v - u) (A u)]

/-- **The variational inequality is a subgradient condition.** Let $V$ be a real inner product
space, $A : V \to V$, $j : V \to \mathbb{R}$, $f \in V$ and $K \subseteq V$. Then $u$ solves the
variational inequality if and only if $u \in K$ and $f - Au$ is a subgradient at $u$ of
$j + \delta_K$, the function equal to $j$ on $K$ and to $+\infty$ outside $K$:
$$j(u) + \langle v - u, f - Au \rangle \le j(v) + \delta_K(v) \quad \text{for all } v \in V.$$

There is no hypothesis on $A$, $j$, $K$ or $V$. Outside $K$ the subgradient inequality holds
trivially, and on $K$ it is the variational inequality. The subdifferential is
`ConvexAnalysis.subdifferential` for the pairing `innerₗ V`, applied to the `EReal`-valued
function $j + \delta_K$. -/
theorem isVariationalInequalitySolution_iff_sub_mem_subdifferential :
    IsVariationalInequalitySolution A j f K u ↔
      u ∈ K ∧
        f - A u ∈ subdifferential (innerₗ V) (fun v => (j v : EReal) + indicatorFn K v) u := by
  unfold IsVariationalInequalitySolution
  refine and_congr_right fun hu => ?_
  simp only [mem_subdifferential, indicatorFn_of_mem hu, add_zero, innerₗ_apply_apply]
  constructor
  · intro h v
    by_cases hv : v ∈ K
    · rw [indicatorFn_of_mem hv, add_zero, ← EReal.coe_add, EReal.coe_le_coe_iff, inner_sub_right,
        real_inner_comm f (v - u), real_inner_comm (A u) (v - u)]
      linarith [h v hv]
    · rw [indicatorFn_of_notMem hv, EReal.coe_add_top]
      exact le_top
  · intro h v hv
    have hv' := h v
    rw [indicatorFn_of_mem hv, add_zero, ← EReal.coe_add, EReal.coe_le_coe_iff, inner_sub_right,
      real_inner_comm f (v - u), real_inner_comm (A u) (v - u)] at hv'
    linarith

/-- Let $V$ be a real Hilbert space, let $j : V \to \mathbb{R}$ be convex and lower semicontinuous,
and let $K \subseteq V$ be nonempty and convex. Then $j$ and the indicator function $\delta_K$
add exactly for the pairing `innerₗ V`: both are proper, and the conjugate of $j + \delta_K$ is
the infimal convolution of the conjugates, with the infimum attained. This is the constraint
qualification for the split $\partial(j + \delta_K) = \partial j + N_K$.

A convex lower semicontinuous real function on a Hilbert space is continuous, and this gives the
continuity constraint qualification `ConvexAnalysis.IsExactSum.of_continuousAt`. -/
theorem ConvexOn.isExactSum_coe_indicatorFn [CompleteSpace V] (hj : ConvexOn ℝ Set.univ j)
    (hlsc : LowerSemicontinuous j) (hK : Convex ℝ K) (hne : K.Nonempty) :
    IsExactSum (innerₗ V) (fun v => (j v : EReal)) (indicatorFn K) := by
  obtain ⟨x₀, hx₀⟩ := hne
  refine IsExactSum.of_continuousAt (ConvexOn.convexFn_coe hj) (properConvex_coe j)
    (convexFn_indicatorFn.2 hK) (properConvex_indicatorFn.2 ⟨x₀, hx₀⟩) (x₀ := x₀)
    (mem_convexDom.2 (EReal.coe_lt_top _)) (by rwa [convexDom_indicatorFn]) ?_
  exact (continuous_coe_real_ereal.comp (hj.continuous_of_lowerSemicontinuous hlsc)).continuousAt

/-- **The variational inequality with a split subdifferential.** Let $V$ be a real Hilbert space,
$A : V \to V$, $f \in V$, let $j : V \to \mathbb{R}$ be convex and lower semicontinuous, and let
$K \subseteq V$ be nonempty and convex. Then $u$ solves the variational inequality if and only
if $u \in K$ and
$$f - Au \in \partial j(u) + N_K(u),$$
that is, some subgradient $y$ of $j$ at $u$ has $f - Au - y$ normal to $K$ at $u$.

The inclusion $\partial j(u) + N_K(u) \subseteq \partial(j + \delta_K)(u)$ holds with no
hypothesis. The reverse inclusion is the sum rule
`ConvexAnalysis.IsExactSum.subdifferential_add` under the constraint qualification
`ConvexOn.isExactSum_coe_indicatorFn`, which uses the hypotheses on $j$, $K$ and $V$. -/
theorem isVariationalInequalitySolution_iff_sub_mem_add_normalCone [CompleteSpace V]
    (hj : ConvexOn ℝ Set.univ j) (hlsc : LowerSemicontinuous j) (hK : Convex ℝ K)
    (hne : K.Nonempty) :
    IsVariationalInequalitySolution A j f K u ↔
      u ∈ K ∧ f - A u ∈ subdifferential (innerₗ V) (fun v => (j v : EReal)) u +
        normalCone (innerₗ V) K u := by
  rw [isVariationalInequalitySolution_iff_sub_mem_subdifferential]
  refine and_congr_right fun hu => ?_
  rw [← subdifferential_indicatorFn (B := innerₗ V) hu,
    ← (ConvexOn.isExactSum_coe_indicatorFn hj hlsc hK hne).subdifferential_add u]
  rfl

/-- **A strongly monotone operator has a monotone graph.** Let $V$ be a real inner product space and
let $A : V \to V$ be strongly monotone with a constant $c \ge 0$. Then the graph
$\{(x, Ax) : x \in V\}$ of $A$ is a monotone relation:
$$\langle x - y, Ax - Ay \rangle \ge 0 \quad \text{for all } x, y \in V.$$

The conclusion is `ConvexAnalysis.IsMonotoneRel (innerₗ V)` of the graph `{p | p.2 = A p.1}`.
This is the single-valued case of the monotone relations on which the theory of the
subdifferential is built. -/
theorem IsStronglyMonotoneWith.isMonotoneRel_graph {c : ℝ} (hA : IsStronglyMonotoneWith ℝ A c)
    (hc : 0 ≤ c) : IsMonotoneRel (innerₗ V) {p : V × V | p.2 = A p.1} := by
  rintro ⟨x, x'⟩ (rfl : x' = A x) ⟨y, y'⟩ (rfl : y' = A y)
  have h := (isStronglyMonotoneWith_real_iff A c).1 hA x y
  dsimp only
  rw [innerₗ_apply_apply, real_inner_comm]
  exact (mul_nonneg hc (sq_nonneg _)).trans h

end Inequality

/-! ### The first-order condition of a constrained convex minimiser -/

section Gateaux

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : V → ℝ}
  {f' : V → V →L[ℝ] ℝ} {K : Set V} {u : V}

/-- **The first-order condition as a normal-cone condition.** Let $V$ be a real normed space, let
$K \subseteq V$ be convex, and let $f : V \to \mathbb{R}$ be convex on $K$. Assume that at every
point $w \in K$ the function $f$ has the directional derivative $f'(w)h$ in every direction $h$,
where $f'(w) \in V'$. Then $u \in K$ minimizes $f$ over $K$ if and only if $-f'(u)$ lies in the
normal cone of $K$ at $u$ for the pairing of $V$ with $V'$:
$$f'(u)(v - u) \ge 0 \quad \text{for all } v \in K.$$
This is the sufficiency half of Theorem 27.4 of [rockafellar1970convex].

The pairing is `(topDualPairing ℝ V).flip`. The proof reads
`isMinOn_iff_forall_lineDeriv_nonneg` as a membership in `ConvexAnalysis.normalCone`. -/
theorem isMinOn_iff_neg_mem_normalCone (hf : ConvexOn ℝ K f)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h) (hu : u ∈ K) :
    IsMinOn f K u ↔ -f' u ∈ normalCone (topDualPairing ℝ V).flip K u := by
  rw [isMinOn_iff_forall_lineDeriv_nonneg hf hG hu, mem_normalCone]
  refine forall₂_congr fun v _ => ?_
  simp only [LinearMap.flip_apply, topDualPairing_apply, neg_apply, neg_nonpos]

end Gateaux

section GateauxHilbert

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {f : V → ℝ} {f' : V → V →L[ℝ] ℝ} {K : Set V} {u : V}

/-- **The first-order condition as a normal-cone condition, in a Hilbert space.** Let $V$ be a real
Hilbert space, let $K \subseteq V$ be convex, and let $f : V \to \mathbb{R}$ be convex on $K$,
with directional derivatives $f'(w)h$, $f'(w) \in V'$, at every point $w \in K$ in every
direction $h$. Let $\nabla f(u) \in V$ be the Riesz representative of $f'(u)$. Then $u \in K$
minimizes $f$ over $K$ if and only if
$$-\nabla f(u) \in N_K(u), \quad \text{that is,} \quad \langle v - u, \nabla f(u) \rangle \ge 0
  \quad \text{for all } v \in K.$$

The gradient is `(InnerProductSpace.toDual ℝ V).symm (f' u)`, and the normal cone is taken for
the pairing `innerₗ V`. -/
theorem isMinOn_iff_neg_toDual_symm_mem_normalCone (hf : ConvexOn ℝ K f)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h) (hu : u ∈ K) :
    IsMinOn f K u ↔ -(InnerProductSpace.toDual ℝ V).symm (f' u) ∈ normalCone (innerₗ V) K u := by
  rw [isMinOn_iff_forall_lineDeriv_nonneg hf hG hu, mem_normalCone]
  refine forall₂_congr fun v _ => ?_
  rw [innerₗ_apply_apply, inner_neg_right, real_inner_comm, InnerProductSpace.toDual_symm_apply,
    neg_nonpos]

end GateauxHilbert
