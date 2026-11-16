/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Indicator
import Numlib.Analysis.Convex.Extremum.Minimum
import Numlib.Analysis.Convex.Extremum.Prox
import Numlib.Analysis.Convex.Subdifferential.Defs
import Numlib.Analysis.Normed.Module.BestApprox

/-!
# The metric projection onto a convex set as a proximal mapping

Let $V$ be a real inner product space and let $K \subseteq V$. A point $v$ is a **best
approximation** of $u$ from $K$ (`IsBestApprox K u v`, from
`Numlib.Analysis.Normed.Module.BestApprox`) if $v \in K$ and $\|u - v\| \le \|u - w\|$ for all
$w \in K$. This module connects this notion with convex analysis. For convex $K$, the point $v$ is
the projection of $u$ onto $K$ exactly when $u - v$ is normal to $K$ at $v$, that is,
$\langle w - v, u - v \rangle \le 0$ for all $w \in K$. This is the nearest-point problem, the first
application of Theorem 27.4 in [rockafellar1970convex], §27, and it is also Lemma 3.4.1 of
[han2009theoretical]. If moreover $K$ is nonempty and closed and $V$ is finite-dimensional, then $v$
is the projection of $u$ exactly when $v = \operatorname{prox}(u \mid \delta(\cdot \mid K))$, the
proximal point of $u$ for the indicator function of $K$. This is the remark after Theorem 31.5 in
[rockafellar1970convex], §31.

Neither notion includes the other. `IsBestApprox` is defined in every seminormed space of every
dimension, and `ConvexAnalysis.prox` is defined for every closed proper convex function. Both are
therefore kept, and this module translates between them.

## Main results

* `isBestApprox_iff_sub_mem_normalCone`: for convex $K$, $v$ is a best approximation of $u$ from $K$
  if and only if $v \in K$ and $u - v \in N_K(v)$.
* `isBestApprox_iff_prox_eq`: for $K$ nonempty, closed and convex in a finite-dimensional space, $v$
  is a best approximation of $u$ from $K$ if and only if $\operatorname{prox}(u \mid \delta(\cdot
  \mid K)) = v$.

## Implementation notes

* The normal cone is `ConvexAnalysis.normalCone (innerₗ V) K v`, taken for the pairing `innerₗ V`.
  The first result is `isBestApprox_iff_inner_le_zero` written as a membership in this cone.
* The second result combines `ConvexAnalysis.prox_eq_iff`, which says
  $\operatorname{prox}(u \mid f) = v$ if and only if $u - v \in \partial f(v)$, with the identity
  $\partial \delta(\cdot \mid K)(v) = N_K(v)$ at points $v \in K$.
* The projection theorem in Hilbert space, existence and uniqueness of the best approximation from a
  nonempty closed convex set, is Mathlib's `exists_norm_eq_iInf_of_complete_convex`. The
  finite-dimensional hypothesis of the second result comes from `ConvexAnalysis.prox`, whose proof
  of attainment is finite-dimensional, and not from the projection.
-/

open ConvexAnalysis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {K : Set V} {u v : V}

/-- **The projection onto a convex set is characterized by the normal cone.** Let $V$ be a real
inner product space, let $K \subseteq V$ be convex, and let $u, v \in V$. Then $v$ is a best
approximation of $u$ from $K$ if and only if $v \in K$ and $u - v$ is normal to $K$ at $v$, that
is,
$$\langle w - v, u - v \rangle \le 0 \quad \text{for every } w \in K.$$

The normal cone is `ConvexAnalysis.normalCone (innerₗ V) K v`. -/
theorem isBestApprox_iff_sub_mem_normalCone (hK : Convex ℝ K) :
    IsBestApprox K u v ↔ v ∈ K ∧ u - v ∈ normalCone (innerₗ V) K v := by
  constructor
  · intro h
    refine ⟨h.1, fun w hw => ?_⟩
    rw [innerₗ_apply_apply, real_inner_comm]
    exact (isBestApprox_iff_inner_le_zero hK h.1).1 h w hw
  · rintro ⟨hv, h⟩
    refine (isBestApprox_iff_inner_le_zero hK hv).2 fun w hw => ?_
    have hw' := h w hw
    rwa [innerₗ_apply_apply, real_inner_comm] at hw'

/-- **The metric projection is the proximal mapping of the indicator.** Let $V$ be a
finite-dimensional real inner product space, let $K \subseteq V$ be nonempty, closed and convex,
and let $u, v \in V$. Then $v$ is a best approximation of $u$ from $K$ if and only if
$$\operatorname{prox}(u \mid \delta(\cdot \mid K)) = v,$$
where $\delta(\cdot \mid K)$ is the indicator function of $K$, equal to $0$ on $K$ and $+\infty$
off $K$.

The proximal mapping is `ConvexAnalysis.prox (innerₗ V)`, and the indicator is
`ConvexAnalysis.indicatorFn K`. -/
theorem isBestApprox_iff_prox_eq [FiniteDimensional ℝ V] (hK : Convex ℝ K) (hKc : IsClosed K)
    (hne : K.Nonempty) :
    IsBestApprox K u v ↔ prox (innerₗ V) (indicatorFn K) u = v := by
  rw [prox_eq_iff (closedProperConvexFn_indicatorFn hK hKc hne),
    mem_subdifferential_indicatorFn_iff hne, isBestApprox_iff_sub_mem_normalCone hK]
