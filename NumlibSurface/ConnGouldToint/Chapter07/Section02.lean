/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Subproblem.TrustRegion

/-!
# Conn, Gould and Toint, Section 7.2: Characterization of the Euclidean model minimizer

This module formalizes the characterization of global minimizers of the trust-region subproblem in
Section 7.2 of [conn2000trust]. Let $E$ be a real inner product space, $g \in E$, and $H$ a bounded
symmetric operator on $E$. The model (7.2.1) is
$$q(s) = \langle g, s \rangle + \tfrac12 \langle s, H s \rangle.$$
A global minimizer $s$ of $q$ on the sphere $\|s\| = \Delta$ satisfies $(H + \mu I) s = -g$ for some
$\mu$ with $H + \mu I$ positive semidefinite (Theorem 7.2.1). A global minimizer on the ball
$\|s\| \le \Delta$ satisfies the same conditions with $\mu \ge 0$ and $\mu (\|s\| - \Delta) = 0$
(Corollary 7.2.2). In both cases the minimizer is unique if $H + \mu I$ is coercive. The proofs
specialize `Numlib.Optimization.Subproblem.TrustRegion`.

## Main definitions

* Equation (7.2.1), `ConnGouldToint.Chapter07.q`: the quadratic model $q(s) = \langle g, s \rangle +
  \frac12 \langle s, H s \rangle$.

## Main results

* Theorem 7.2.1, `ConnGouldToint.Chapter07.theorem_7_2_1`: a global minimizer on the sphere solves a
  shifted system with a positive semidefinite shifted Hessian.
* Corollary 7.2.2, `ConnGouldToint.Chapter07.corollary_7_2_2`: a global minimizer on the ball has a
  nonnegative complementary multiplier.

## Implementation notes

* Coercivity of $H + \mu I$, that is $\langle (H + \mu I) u, u \rangle \ge c \|u\|^2$ for some
  $c > 0$, is `LinearMap.IsCoercive`. In finite dimension it is equivalent to positive definiteness.

## Deviations from the source

* **Equation (7.2.1), Theorem 7.2.1 and Corollary 7.2.2** (generalization). The model and
  multiplier conditions apply to a bounded symmetric operator on a real inner-product space. The
  uniqueness clause uses coercivity, which agrees with positive definiteness in finite
  dimensions. See `ConnGouldToint.Chapter07.theorem_7_2_1` and
  `ConnGouldToint.Chapter07.corollary_7_2_2`.
* **Theorem 7.2.1** (reading). The radius is assumed positive. See
  `ConnGouldToint.Chapter07.theorem_7_2_1`.
* **Corollary 7.2.2** (reading). The radius is assumed positive. See
  `ConnGouldToint.Chapter07.corollary_7_2_2`.
-/

namespace ConnGouldToint.Chapter07

open Metric
open Subproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Equation (7.2.1)** of [conn2000trust]. For $g \in E$ and a bounded linear operator $H$ on $E$,
the **quadratic model** of the trust-region subproblem is
$$q(s) = \langle g, s \rangle + \tfrac12 \langle s, H s \rangle.$$

It is `Subproblem.quadModel g H`.

**Generalization.** The quadratic model acts on a real inner-product space with a bounded
operator. -/
noncomputable abbrev q (g : E) (H : E →L[ℝ] E) : E → ℝ := quadModel g H

/-- **Theorem 7.2.1** of [conn2000trust]. Let $E$ be a real inner product space, not necessarily
complete, $g \in E$, $H$ a bounded symmetric operator on $E$, and $\Delta > 0$. Let $s$ with
$\|s\| = \Delta$ be a global minimizer of $q$ on the sphere $\{u : \|u\| = \Delta\}$. Then there
is $\mu \in \mathbb{R}$ such that
$$(H + \mu I) s = -g \quad \text{and} \quad H + \mu I \text{ is positive semidefinite}.$$
If moreover $H + \mu I$ is coercive, then $s$ is the only global minimizer of $q$ on the sphere.

**Reading.** The statement assumes $\Delta > 0$. For $\Delta = 0$ the sphere is $\{0\}$, and the
shifted system $(H + \mu I) 0 = -g$ has no solution when $g \neq 0$.

Coercivity is `LinearMap.IsCoercive`, which is equivalent to positive definiteness in finite
dimension.

**Reading.** In the more general inner-product space, the uniqueness premise is coercivity. In
finite dimensions this is positive definiteness. -/
theorem theorem_7_2_1 {g : E} {H : E →L[ℝ] E} {Δ : ℝ} {s : E}
    (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hΔ : 0 < Δ)
    (hs : ‖s‖ = Δ) (hmin : IsMinOn (q g H) (sphere 0 Δ) s) :
    ∃ μ : ℝ, (H + μ • (1 : E →L[ℝ] E)) s = -g ∧
      ((H + μ • (1 : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E).IsPositive ∧
      (((H + μ • (1 : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E).IsCoercive →
        ∀ u : E, ‖u‖ = Δ → IsMinOn (q g H) (sphere 0 Δ) u → u = s) :=
  exists_shift_of_isMinOn_sphere hH hΔ hs hmin

/-- **Corollary 7.2.2** of [conn2000trust]. Let $E$ be a real inner product space, not necessarily
complete, $g \in E$, $H$ a bounded symmetric operator on $E$, and $\Delta > 0$. Let $s$ with
$\|s\| \le \Delta$ be a global minimizer of $q$ on the ball $\{u : \|u\| \le \Delta\}$. Then
there is $\mu \ge 0$ such that
$$(H + \mu I) s = -g, \qquad H + \mu I \text{ is positive semidefinite}, \qquad \mu (\|s\| -
  \Delta) = 0.$$
If moreover $H + \mu I$ is coercive, then $s$ is the only global minimizer of $q$ on the ball.

**Reading.** The statement assumes $\Delta > 0$. For $\Delta = 0$ the only feasible point is
$0$, and the shifted system has no solution when $g \neq 0$.

The conditions on $\mu$ are `Subproblem.IsTrustRegionMultiplier g H Δ s μ`.

**Reading.** Coercivity supplies uniqueness on the ball, as in the sphere version. -/
theorem corollary_7_2_2 {g : E} {H : E →L[ℝ] E} {Δ : ℝ} {s : E}
    (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hΔ : 0 < Δ)
    (hs : ‖s‖ ≤ Δ) (hmin : IsMinOn (q g H) (closedBall 0 Δ) s) :
    ∃ μ, IsTrustRegionMultiplier g H Δ s μ ∧
      (((H + μ • (1 : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E).IsCoercive →
        ∀ u : E, ‖u‖ ≤ Δ → IsMinOn (q g H) (closedBall 0 Δ) u → u = s) := by
  obtain ⟨μ, hμ⟩ := (isMinOn_closedBall_iff hH hΔ hs).mp hmin
  exact ⟨μ, hμ, fun hc _ hu hmin' => eq_of_isMinOn_closedBall_of_posDef hH hμ hs hc hu hmin'⟩

end ConnGouldToint.Chapter07
