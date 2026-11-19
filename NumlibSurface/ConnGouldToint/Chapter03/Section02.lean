/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Numlib.Analysis.Convex.LinearInequalities
import Numlib.Analysis.Convex.Subdifferential.Calculus
import Numlib.Optimization.Constrained.SecondOrder
import Numlib.Optimization.Descent
import Numlib.Optimization.Optimality.Clarke
import Numlib.Optimization.Optimality.ConvexSet
import Numlib.Optimization.Optimality.Unconstrained

/-!
# Conn, Gould and Toint, Section 3.2: Optimality conditions

This module formalizes the optimality conditions of Section 3.2 of [conn2000trust]. For
unconstrained problems, a local minimizer of a smooth $f$ has $\nabla f(x) = 0$ and a positive
semidefinite Hessian, and a stationary point with positive definite Hessian is an isolated strict
local minimizer (Theorems 3.2.1–3.2.3). For the problem
$$\min f(x) \quad \text{subject to} \quad h_i(x) = 0, \ g_j(x) \le 0,$$
the first- and second-order Karush–Kuhn–Tucker conditions hold under the constraint qualifications
AO.1 and AO.2, which follow from linear independence of the active constraint gradients (Theorems
3.2.4–3.2.6). A strict local minimizer that satisfies the second-order sufficient conditions with
strict complementarity persists, with its multipliers and active set, along a smooth branch under
perturbations of the data (Theorem 3.2.7). The section also proves the continuity of parametric
minimum values (Theorem 3.2.8), the optimality conditions on a closed convex set and the normal cone
of a set defined by inequalities (Theorems 3.2.9–3.2.11), and nonsmooth conditions with Clarke
subgradients for composite problems $f + h \circ c$ (Theorems 3.2.12–3.2.15).

The proofs specialize the backbone modules `Numlib.Optimization.Optimality.Unconstrained`,
`Numlib.Optimization.Constrained.SecondOrder`, `Numlib.Optimization.Optimality.ConvexSet`,
`Numlib.Optimization.Optimality.Clarke`, `Numlib.Analysis.Convex.LinearInequalities` and
`Numlib.Analysis.Convex.Subdifferential.Calculus`, and Mathlib's implicit function theorem.

## Main definitions

* Assumption AF.1, `ConnGouldToint.Chapter03.AF1`: $f$ is twice continuously differentiable.
* Assumption AO.1, `ConnGouldToint.Chapter03.AO1`: every direction that satisfies the linearized
  constraints is tangent to the feasible set.
* Assumption AO.2, `ConnGouldToint.Chapter03.AO2`: every critical direction is tangent to the set
  where the strongly active constraints stay active.
* Assumption AC.2, `ConnGouldToint.Chapter03.AC2`: the feasible set is nonempty, closed and convex.
* Assumption AC.7, `ConnGouldToint.Chapter03.AC7`: the feasible set is
  $\{x : c_i(x) \ge 0 \text{ for all } i\}$.
* Assumption AO.1 for inequalities, `ConnGouldToint.Chapter03.ActiveLinearizedConeMatches`: the
  tangent cone equals the cone of the linearized active inequalities.
* Theorem 3.2.7, `ConnGouldToint.Chapter03.activeKKTLinearization`: the block operator
  $(d, w) \mapsto (Hd + A^* w, Ad)$ of the active KKT equations.
* Theorem 3.2.7, `ConnGouldToint.Chapter03.ActiveDual`: the space of equality and active-inequality
  multipliers.

## Main results

* Theorem 3.2.1, `ConnGouldToint.Chapter03.theorem_3_2_1`: the derivative vanishes at an
  unconstrained local minimizer.
* Theorem 3.2.2, `ConnGouldToint.Chapter03.theorem_3_2_2`: at an unconstrained local minimizer the
  Hessian is also positive semidefinite.
* Theorem 3.2.3, `ConnGouldToint.Chapter03.theorem_3_2_3`: a stationary point with positive definite
  Hessian is an isolated strict local minimizer.
* Theorem 3.2.4, `ConnGouldToint.Chapter03.theorem_3_2_4`: the first-order KKT conditions under
  AO.1.
* Section 3.2.2, `ConnGouldToint.Chapter03.ao1_ao2_of_isRegularPointIneq`: linear independence of
  the active constraint derivatives implies AO.1 and AO.2.
* Theorem 3.2.5, `ConnGouldToint.Chapter03.theorem_3_2_5_of_constraint_qualifications` and
  `ConnGouldToint.Chapter03.theorem_3_2_5`: the second-order necessary conditions under AO.1 and
  AO.2, and under linear independence.
* Theorem 3.2.6, `ConnGouldToint.Chapter03.theorem_3_2_6`: the second-order sufficient conditions
  for a strict local minimizer.
* Theorem 3.2.7, `ConnGouldToint.Chapter03.theorem_3_2_7`: the strict local minimizer and its
  multipliers continue along a $C^1$ branch with the same active set.
* Theorem 3.2.7, `ConnGouldToint.Chapter03.theorem_3_2_7_strict_minimizer_branch`: the same
  conclusion from an explicitly given smooth active KKT residual.
* Theorem 3.2.7, `ConnGouldToint.Chapter03.theorem_3_2_7_activeKKT_invertible`,
  `ConnGouldToint.Chapter03.theorem_3_2_7_activeKKT_conditions_open`,
  `ConnGouldToint.Chapter03.theorem_3_2_7_implicit_branch` and
  `ConnGouldToint.Chapter03.theorem_3_2_7_joint_smooth_data`: the steps of the proof.
* Theorems 3.2.7 and 15.2.2, `ConnGouldToint.Chapter03.active_kkt_stationary_iff`: stationarity in
  terms of the active Jacobian is equivalent to the KKT stationarity condition with zero multipliers
  for the inactive constraints.
* Theorems 3.2.7 and 15.2.2, `ConnGouldToint.Chapter03.continuous_active_multiplier_recovery`: if
  the active Jacobian is surjective at a base point, a function that is continuous at that point
  gives the only possible multiplier vector at every nearby point.
* Theorems 3.2.7 and 15.2.2, `ConnGouldToint.Chapter03.active_surjective_licq`: a surjective active
  Jacobian gives linear independence of the active constraint derivatives.
* Theorem 3.2.8, `ConnGouldToint.Chapter03.theorem_3_2_8`: the minimum value is continuous and the
  minimizers form an upper hemicontinuous correspondence.
* Theorem 3.2.8, `ConnGouldToint.Chapter03.theorem_3_2_8_counterexample` and
  `ConnGouldToint.Chapter03.theorem_3_2_8_noncompact_value_counterexample`: the minimizers need not
  be lower hemicontinuous, and without compactness the value need not be continuous.
* Theorem 3.2.9, `ConnGouldToint.Chapter03.theorem_3_2_9`: first-order criticality on a closed
  convex set means that $-\nabla f(x)$ is a normal vector.
* Theorem 3.2.10, `ConnGouldToint.Chapter03.theorem_3_2_10_normalCone`: the normal cone is generated
  by the negative active constraint gradients.
* Theorem 3.2.10, `ConnGouldToint.Chapter03.isClosed_normalCone_graph`,
  `ConnGouldToint.Chapter03.continuous_normal_selection_on_active_face` and
  `ConnGouldToint.Chapter03.theorem_3_2_10_face_continuity`: the continuity of the normal and
  tangent cones on a fixed active face.
* Theorem 3.2.11, `ConnGouldToint.Chapter03.theorem_3_2_11_of_normalCone_sum` and
  `ConnGouldToint.Chapter03.theorem_3_2_11`: multipliers for a smooth problem over a base set $C$,
  under a normal-cone sum rule.
* Theorem 3.2.11, `ConnGouldToint.Chapter03.theorem_3_2_11_tangent_counterexample`: linearization of
  the tangent cone alone does not give multipliers.
* Theorem 3.2.12, `ConnGouldToint.Chapter03.theorem_3_2_12`: at a local minimizer of a locally
  Lipschitz function, $0$ is a Clarke subgradient.
* Corollary 3.2.13, `ConnGouldToint.Chapter03.corollary_3_2_13`: the first-order conditions for a
  composite $f + h \circ c$.
* Corollary 3.2.13, `ConnGouldToint.Chapter03.clarke_composite_equality_counterexample`: the Clarke
  derivative of a composite can be smaller than the linearized bound.
* Theorem 3.2.14, `ConnGouldToint.Chapter03.theorem_3_2_14`: second-order sufficient conditions for
  a composite.
* Theorem 3.2.15, `ConnGouldToint.Chapter03.theorem_3_2_15_clarke` and
  `ConnGouldToint.Chapter03.theorem_3_2_15`: KKT conditions for a composite problem with a composite
  constraint.
* Theorem 3.2.15, `ConnGouldToint.Chapter03.theorem_3_2_15_boundary_counterexample`: a convex outer
  function on a proper domain can fail to have a subgradient at a minimizer.

## Conventions

* The derivative $f'(x)$ is `fderiv ℝ f x`.
* The gradient $\nabla f(x)$ is `gradient f x`. The derivative is zero exactly when the gradient is
  zero. At a point where $f$ is not differentiable, Lean sets both to zero.
* The Hessian form $\langle d, \nabla^2 f(x) d \rangle$ is `iteratedFDeriv ℝ 2 f x (fun _ => d)`.
* Theorem 3.2.4 writes the inequality constraints as $c_i(x) \ge 0$, as the source does. Theorems
  3.2.5–3.2.7 and 3.2.11 write them as $g_j(x) \le 0$, the negated constraints of the source, with
  the Lagrangian $f + \sum_i \lambda_i h_i + \sum_j \mu_j g_j$ and $\mu \ge 0$. The feasible set is
  `Constrained.feasible h g`.
* The tangent cone $T_C(x)$ is Mathlib's `posTangentConeAt C x`, and the normal cone $N_C(x)$ is
  `normalCone (innerₗ V) C x`, the set of $g$ with $\langle g, y - x \rangle \le 0$ for all
  $y \in C$.
* The Clarke directional derivative $f^\circ(x; d)$ and the Clarke subdifferential
  $\partial^\circ f(x)$ are `Optimization.clarkeDerivative` and `Optimization.clarkeSubgradient`.

## Deviations from the source

* **Generalization.** Assumption AF.1 and Theorems 3.2.1–3.2.2 extend to general real normed spaces.
  See `ConnGouldToint.Chapter03.theorem_3_2_1`, `ConnGouldToint.Chapter03.AF1`,
  `ConnGouldToint.Chapter03.theorem_3_2_2`.
* **Generalization.** Theorem 3.2.9 derives normal-cone membership directly from the tangent
  directional tests. See `ConnGouldToint.Chapter03.theorem_3_2_9`.
* **Explicit tangent qualification.** Theorem 3.2.10 gives the normal-cone formula with the active
  tangent linearization as an explicit hypothesis. See
  `ConnGouldToint.Chapter03.ActiveLinearizedConeMatches`,
  `ConnGouldToint.Chapter03.theorem_3_2_10_normalCone`.
* **Continuity formulation.** Theorem 3.2.10 makes fixed-active-set, bounded-section hemicontinuity
  and normal selection explicit. See `ConnGouldToint.Chapter03.isClosed_normalCone_graph`,
  `ConnGouldToint.Chapter03.continuous_normal_selection_on_active_face`,
  `ConnGouldToint.Chapter03.theorem_3_2_10_face_continuity`.
* **Generalization.** Theorem 3.2.12 extends Clarke stationarity to complete real Hilbert spaces.
  See `ConnGouldToint.Chapter03.theorem_3_2_12`.
* **Correction.** Corollary 3.2.13 uses a Clarke chain-rule bound, with a counterexample to the
  printed equality. See `ConnGouldToint.Chapter03.corollary_3_2_13`,
  `ConnGouldToint.Chapter03.clarke_composite_equality_counterexample`.
* **Generalization.** Theorem 3.2.4 exposes the tangent qualification and uses local
  differentiability. See `ConnGouldToint.Chapter03.theorem_3_2_4`.
* **Local smoothness and qualification variants.** Theorems 3.2.5–3.2.6 need only local smoothness,
  with both tangent-qualified and regular-point necessity statements. See
  `ConnGouldToint.Chapter03.theorem_3_2_5_of_constraint_qualifications`,
  `ConnGouldToint.Chapter03.theorem_3_2_5`, `ConnGouldToint.Chapter03.theorem_3_2_6`.
* **Generalization.** Theorem 3.2.7 allows parameter-dependent inequalities and gives local
  uniqueness among all local minimizers. See
  `ConnGouldToint.Chapter03.theorem_3_2_7_strict_minimizer_branch`,
  `ConnGouldToint.Chapter03.theorem_3_2_7`.
* **Correction and generalization.** Theorem 3.2.8 gives continuous values and upper hemicontinuous
  minimizers under compactness, with counterexamples to the stronger printed claims. See
  `ConnGouldToint.Chapter03.theorem_3_2_8`, `ConnGouldToint.Chapter03.theorem_3_2_8_counterexample`,
  `ConnGouldToint.Chapter03.theorem_3_2_8_noncompact_value_counterexample`.
* **Correction and generalization.** Theorem 3.2.14 uses affine minorants and establishes strict
  local minimality on the domain. See `ConnGouldToint.Chapter03.theorem_3_2_14`.
* **Correction.** Theorem 3.2.11 adds a normal-cone sum hypothesis and includes a counterexample to
  relying on the tangent condition alone. See
  `ConnGouldToint.Chapter03.theorem_3_2_11_of_normalCone_sum`,
  `ConnGouldToint.Chapter03.theorem_3_2_11`,
  `ConnGouldToint.Chapter03.theorem_3_2_11_tangent_counterexample`.
* **Correction and Clarke variant.** Theorem 3.2.15 uses local Lipschitz and active descent
  assumptions. Its counterexample shows that convexity on an arbitrary outer domain is insufficient.
  See `ConnGouldToint.Chapter03.theorem_3_2_15_boundary_counterexample`,
  `ConnGouldToint.Chapter03.theorem_3_2_15_clarke`, `ConnGouldToint.Chapter03.theorem_3_2_15`.
* **Assumption AF.1 and Theorems 3.2.1–3.2.2** (generalization). The objective can be on any real
  normed space. See `ConnGouldToint.Chapter03.AF1`, `ConnGouldToint.Chapter03.theorem_3_2_1` and
  `ConnGouldToint.Chapter03.theorem_3_2_2`.
* **Theorem 3.2.4** (generalization). The objective needs only differentiability at the candidate
  minimizer, and the tangent inclusion supplies the needed constraint data. See
  `ConnGouldToint.Chapter03.theorem_3_2_4`.
* **Theorems 3.2.5–3.2.6** (generalization). Second-order smoothness is local to the candidate
  minimizer. See `ConnGouldToint.Chapter03.theorem_3_2_5_of_constraint_qualifications`,
  `ConnGouldToint.Chapter03.theorem_3_2_5` and `ConnGouldToint.Chapter03.theorem_3_2_6`.
* **Theorem 3.2.7** (generalization). The inequality constraints can depend on the parameter,
  and the minimizer is unique among all local minimizers in a neighbourhood. See
  `ConnGouldToint.Chapter03.theorem_3_2_7`.
* **Theorem 3.2.8** (correction). The statement assumes nonempty compact feasible sets and gives
  continuity of the minimum value and upper hemicontinuity of the minimizers. The minimizers need
  not be lower hemicontinuous, and without compactness the value need not be continuous. See
  `ConnGouldToint.Chapter03.theorem_3_2_8`, `ConnGouldToint.Chapter03.theorem_3_2_8_counterexample`
  and `ConnGouldToint.Chapter03.theorem_3_2_8_noncompact_value_counterexample`.
* **Theorem 3.2.8** (generalization). The feasible sets and objective may be nonconvex, and
  the variables and parameters may lie in arbitrary topological spaces. See
  `ConnGouldToint.Chapter03.theorem_3_2_8`.
* **Theorem 3.2.9** (generalization). The tangent-cone inequality gives normal-cone membership
  without a constraint qualification or continuous differentiability on the feasible set. See
  `ConnGouldToint.Chapter03.theorem_3_2_9`.
* **Theorem 3.2.10** (reading). The continuity of the normal and tangent cones is stated on a face
  with a fixed active set, as upper and lower hemicontinuity of their bounded sections. See
  `ConnGouldToint.Chapter03.theorem_3_2_10_face_continuity`.
* **Theorem 3.2.10, normal-cone formula** (generalization). The active tangent linearization
  suffices without global smoothness of the constraint functions. See
  `ConnGouldToint.Chapter03.theorem_3_2_10_normalCone`.
* **Theorem 3.2.11** (correction). The multiplier conclusion needs a normal-cone sum rule at the
  minimizer; linearization of the tangent cone alone does not suffice. See
  `ConnGouldToint.Chapter03.theorem_3_2_11_of_normalCone_sum` and
  `ConnGouldToint.Chapter03.theorem_3_2_11_tangent_counterexample`.
* **Theorem 3.2.12** (generalization). The Clarke first-order condition holds in any real Hilbert
  space. See `ConnGouldToint.Chapter03.theorem_3_2_12`.
* **Corollary 3.2.13** (correction). The first-order condition uses the bound
  $f'(x) d + h^\circ(c(x); c'(x) d)$. It is not equal to the Clarke derivative of the composite in
  general. See `ConnGouldToint.Chapter03.corollary_3_2_13` and
  `ConnGouldToint.Chapter03.clarke_composite_equality_counterexample`.
* **Theorem 3.2.14** (correction). The result gives strict local optimality on the domain.
  Isolation among local minimizers can fail on a domain with isolated points accumulating
  at the minimizer. See `ConnGouldToint.Chapter03.theorem_3_2_14`.
* **Theorem 3.2.14** (generalization). Affine minorants touching at $c(x)$ suffice for the
  second-order argument, so $h$ can be arbitrary. See `ConnGouldToint.Chapter03.theorem_3_2_14`.
* **Theorem 3.2.15** (correction). The outer functions are locally Lipschitz, and an active
  constraint needs a strict Clarke descent direction. The printed conditions on the domains of the
  outer functions are not sufficient. See `ConnGouldToint.Chapter03.theorem_3_2_15` and
  `ConnGouldToint.Chapter03.theorem_3_2_15_boundary_counterexample`.
-/

open Set Filter Topology ConvexAnalysis
open scoped RealInnerProductSpace NNReal

namespace ConnGouldToint.Chapter03

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Theorem 3.2.1** of [conn2000trust]. Let $E$ be a real normed space, and let
$f : E \to \mathbb{R}$ be continuously differentiable. If $x$ is a local minimizer of $f$, then
$f'(x) = 0$.

**Generalization.** The book works on $\mathbb{R}^n$. The first-order condition holds in any
real normed space by considering directional derivatives along lines.

**Generalization.** The unconstrained necessary conditions and smoothness assumption use Fréchet
derivatives on real normed spaces.
-/
theorem theorem_3_2_1 {f : E → ℝ} (hf : ContDiff ℝ 1 f) {x : E} (hx : IsLocalMin f x) :
    fderiv ℝ f x = 0 :=
  hx.hasFDerivAt_eq_zero (hf.differentiable (by norm_num) x).hasFDerivAt

/-- **Assumption AF.1** of [conn2000trust]. The objective function $f : E \to \mathbb{R}$ is twice
continuously differentiable on $E$.

**Generalization.** The book uses $E = \mathbb{R}^n$. The smoothness condition applies to an
arbitrary real normed space.

**Generalization.** The unconstrained necessary conditions and smoothness assumption use Fréchet
derivatives on real normed spaces.
-/
abbrev AF1 (f : E → ℝ) : Prop := ContDiff ℝ 2 f

/-- **Theorem 3.2.2** of [conn2000trust]. Let $E$ be a real normed space, and let
$f : E \to \mathbb{R}$ satisfy AF.1. If $x$ is a local minimizer of $f$, then $f'(x) = 0$ and
$$\langle s, \nabla^2 f(x) s \rangle \ge 0 \quad \text{for all } s \in E.$$

**Generalization.** The book works on $\mathbb{R}^n$. Nonnegativity of the second variation
holds in any real normed space because its evaluation on $s$ comes from a real function
along the line through $x$ in direction $s$.

**Generalization.** The unconstrained necessary conditions and smoothness assumption use Fréchet
derivatives on real normed spaces.
-/
theorem theorem_3_2_2 {f : E → ℝ} (hf : AF1 f) {x : E} (hx : IsLocalMin f x) :
    fderiv ℝ f x = 0 ∧ ∀ s : E, 0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => s) :=
  ⟨theorem_3_2_1 (hf.of_le (by norm_num)) hx,
    IsLocalMin.iteratedFDeriv_two_apply_self_nonneg hx hf.contDiffAt⟩

/-- **Theorem 3.2.3** of [conn2000trust]. Let $E$ be a finite-dimensional real normed space, and let
$f : E \to \mathbb{R}$ satisfy AF.1. If $f'(x) = 0$ and $\langle s, \nabla^2 f(x) s \rangle > 0$
for all $s \neq 0$, then $x$ is a strict local minimizer of $f$, and $x$ has a neighbourhood
that contains no other local minimizer of $f$. -/
theorem theorem_3_2_3 [FiniteDimensional ℝ E] {f : E → ℝ} (hf : AF1 f)
    {x : E} (hx : fderiv ℝ f x = 0)
    (hpos : ∀ s : E, s ≠ 0 → 0 < iteratedFDeriv ℝ 2 f x (fun _ => s)) :
    Optimization.IsStrictLocalMin f x ∧ ∀ᶠ y in 𝓝 x, IsLocalMin f y → y = x := by
  refine ⟨Optimization.isStrictLocalMin_of_fderiv_eq_zero_of_posDef hf.contDiffAt hx hpos, ?_⟩
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact Eventually.of_forall fun y _ => Subsingleton.elim y x
  let H := iteratedFDeriv ℝ 2 f
  let c := minCurvature (H x)
  obtain ⟨v, hv, hvc⟩ := exists_eq_minCurvature (H x)
  have hc : 0 < c := by
    rw [show c = H x (fun _ => v) from hvc.symm]
    exact hpos v (by rintro rfl; simp at hv)
  have hH : Continuous H := hf.continuous_iteratedFDeriv'
  have hclose : ∀ᶠ z in 𝓝 x, dist (H z) (H x) < c :=
    hH.continuousAt (Metric.ball_mem_nhds (H x) hc)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hclose
  have hcurv (z : E) (hz : dist z x < r) : 0 < minCurvature (H z) := by
    have h := abs_minCurvature_sub_le (A := H z) (B := H x)
    have h' := hball (y := z) hz
    rw [dist_eq_norm] at h'
    linarith [neg_abs_le (minCurvature (H z) - minCurvature (H x))]
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy hymin
  by_contra hyx
  let d := y - x
  let g : ℝ → ℝ := fun t => fderiv ℝ f (x + t • d) d
  have hd : ∀ t : ℝ, HasDerivAt g (fderiv ℝ (fderiv ℝ f) (x + t • d) d d) t := by
    intro t
    have hseg : HasDerivAt (fun u : ℝ => x + u • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have hF : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
    have h := hF.differentiable (by norm_num) (x + t • d)
    simpa [g] using (h.hasFDerivAt.comp_hasDerivAt t hseg).clm_apply (hasDerivAt_const t d)
  obtain ⟨t, ht, he⟩ := exists_deriv_eq_slope g (by norm_num : (0 : ℝ) < 1)
    (fun u _ => (hd u).continuousAt.continuousWithinAt)
    (fun u _ => (hd u).differentiableAt.differentiableWithinAt)
  have hnear : dist (x + t • d) x < r := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le]
    have hy' : ‖d‖ < r := by simpa [Metric.mem_ball, dist_eq_norm, d] using hy
    exact (mul_le_of_le_one_left (norm_nonneg d) ht.2.le).trans_lt hy'
  have hdpos : 0 < ‖d‖ ^ 2 := pow_pos (norm_pos_iff.2 (sub_ne_zero.2 hyx)) _
  have hdiag : 0 < H (x + t • d) (fun _ => d) :=
    (mul_pos (hcurv _ hnear) hdpos).trans_le (minCurvature_mul_norm_sq_le _ _)
  have hstat := theorem_3_2_1 (hf.of_le (by norm_num)) hymin
  have hy' : x + d = y := by dsimp [d]; abel
  rw [(hd t).deriv] at he
  simp only [g, one_smul, zero_smul, add_zero, hy', hstat, hx,
    zero_apply, sub_zero, zero_div] at he
  exact hdiag.ne' (by simpa [H, iteratedFDeriv_two_apply] using he)

section ConvexNonsmooth

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Assumption AC.2** of [conn2000trust]. The feasible set $C$ is nonempty, closed and convex. -/
def AC2 (C : Set V) : Prop := C.Nonempty ∧ IsClosed C ∧ Convex ℝ C

/-- **Theorem 3.2.9** of [conn2000trust]. Let $V$ be a real Hilbert space, let $C \subseteq V$
satisfy AC.2, let $f : V \to \mathbb{R}$, and let $x \in C$. If
$$f'(x) d \ge 0 \quad \text{for all } d \in T_C(x),$$
then $-\nabla f(x) \in N_C(x)$.

**Generalization.** The source assumes continuous differentiability and the first-order constraint
qualification AO.1. Here the tangent-cone inequality directly implies normal-cone membership,
since for each $z \in C$ the vector $z - x$ is tangent at $x$. The derivative in the statement
is Mathlib's `fderiv`, which is zero where the derivative does not exist.

**Generalization.** The conclusion is phrased via normal-cone membership and directly assumes the
tangent directional inequality. The source assumes differentiability throughout the feasible set.
-/
theorem theorem_3_2_9 [CompleteSpace V] {C : Set V} (hC : AC2 C) {f : V → ℝ} {x : V} (hx : x ∈ C)
    (hcrit : ∀ d ∈ posTangentConeAt C x, 0 ≤ fderiv ℝ f x d) :
    -gradient f x ∈ normalCone (innerₗ V) C x := by
  rw [mem_normalCone]
  intro z hz
  have htan := sub_mem_posTangentConeAt_of_segment_subset (hC.2.2.segment_subset hx hz)
  simpa [innerₗ_apply_apply] using hcrit (z - x) htan

/-- **Assumption AC.7** of [conn2000trust]. For finitely many functions $c_i : V \to \mathbb{R}$,
the feasible set is
$$C = \{x : c_i(x) \ge 0 \text{ for all } i\}.$$
-/
def AC7 {ι : Type*} [Fintype ι] (C : Set V) (c : ι → V → ℝ) : Prop :=
  C = {x | ∀ i, 0 ≤ c i x}

/-- **Assumption AO.1** of [conn2000trust], for inequality constraints. For $C \subseteq V$,
functions $c_i : V \to \mathbb{R}$ and $x \in V$, the **active linearization qualification**
holds at $x$ if a direction $d$ is tangent to $C$ at $x$ exactly when it satisfies the
linearized active constraints:
$$d \in T_C(x) \iff c_i'(x) d \ge 0 \text{ for every } i \text{ with } c_i(x) = 0.$$

**Reading.** For the cone formula the feasible tangent cone is assumed to match the linearized
active cone. This supplies the needed constraint qualification without global differentiability.
-/
def ActiveLinearizedConeMatches {ι : Type*} (C : Set V) (c : ι → V → ℝ) (x : V) : Prop :=
  ∀ d : V, d ∈ posTangentConeAt C x ↔ ∀ i, c i x = 0 → 0 ≤ fderiv ℝ (c i) x d

/-- **Theorem 3.2.10** of [conn2000trust], the normal-cone formula. Let $V$ be a finite-dimensional
real inner product space, let $C$ satisfy AC.2 and AC.7 with finitely many $c_i$, and let $x$ be
feasible. If the active linearization qualification holds at $x$, then $g \in N_C(x)$ if and
only if
$$g = \sum_{i : c_i(x) = 0} a_i \, (-\nabla c_i(x)) \quad \text{for some } a_i \ge 0.$$

**Generalization.** The book assumes AC.1, global twice-continuous differentiability of the
constraints. The normal-cone formula needs the active tangent linearization at $x$ alone.
The constraint gradients come from Mathlib's totalized derivative.

**Reading.** For the cone formula the feasible tangent cone is assumed to match the linearized
active cone. This supplies the needed constraint qualification without global differentiability.
-/
theorem theorem_3_2_10_normalCone [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {C : Set V} {c : ι → V → ℝ} (hC : AC2 C) (hset : AC7 C c)
    {x : V} (hx : ∀ i, 0 ≤ c i x) (hQ : ActiveLinearizedConeMatches C c x) (g : V) :
    g ∈ normalCone (innerₗ V) C x ↔
      ∃ a : {i // c i x = 0} → ℝ, (∀ i, 0 ≤ a i) ∧
        ∑ i, a i • (-gradient (c i) x) = g := by
  classical
  let b (i : {i // c i x = 0}) := -gradient (c i) x
  rw [← ConvexAnalysis.farkas (B := innerₗ V) b g]
  have hxC : x ∈ C := by rw [hset]; exact hx
  have hlin (d : V) :
      (∀ i, innerₗ V d (b i) ≤ 0) ↔ d ∈ posTangentConeAt C x := by
    rw [hQ d]
    simp [b, innerₗ_apply_apply]
  constructor
  · intro hn d hd
    have hmax : IsMaxOn (fun y : V => ⟪g, y⟫) C x := by
      intro y hy
      have h := hn y hy
      simp only [innerₗ_apply_apply, inner_sub_left, sub_nonpos] at h
      change ⟪g, y⟫ ≤ ⟪g, x⟫
      simpa only [real_inner_comm g] using h
    have hder : HasFDerivAt (fun y : V => ⟪g, y⟫) (innerSL ℝ g) x :=
      (innerSL ℝ g).hasFDerivAt
    have hg := hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos hder.hasFDerivWithinAt ((hlin d).1 hd)
    simpa [innerₗ_apply_apply, real_inner_comm] using hg
  · intro hp z hz
    have hz' := sub_mem_posTangentConeAt_of_segment_subset (hC.2.2.segment_subset hxC hz)
    exact hp (z - x) ((hlin _).2 hz')

/-- **Theorem 3.2.10** of [conn2000trust], closed graph of the normal cone. For every
$C \subseteq V$, the set of pairs $(x, g)$ with $g \in N_C(x)$ is closed in $V \times V$.

This is the outer-limit part of the continuity of the normal cone.

**Reading.** The cone graph is closed. Inner continuity uses a selection on feasible points with the
same active set and qualifying linearization. The hemicontinuity statement concerns positive-radius
bounded sections of the cones.
-/
theorem isClosed_normalCone_graph (C : Set V) :
    IsClosed {p : V × V | p.2 ∈ normalCone (innerₗ V) C p.1} := by
  have he : {p : V × V | p.2 ∈ normalCone (innerₗ V) C p.1} =
      ⋂ z : C, {p : V × V | ⟪(z : V) - p.1, p.2⟫ ≤ 0} := by
    ext p
    simp [mem_normalCone, innerₗ_apply_apply, inner_sub_left]
  rw [he]
  exact isClosed_iInter fun z =>
    isClosed_le ((continuous_const.sub continuous_fst).inner continuous_snd) continuous_const

/-- **Theorem 3.2.10** of [conn2000trust], inner continuity of the normal cone. Let $V$, $C$ and
$c_i$ be as in `ConnGouldToint.Chapter03.theorem_3_2_10_normalCone`, with each $c_i$
continuously differentiable. Let $x$ be feasible, let the active linearization qualification
hold at $x$, and let $g \in N_C(x)$. Then there is a continuous $G : V \to V$ with $G(x) = g$
and $G(z) \in N_C(z)$ for every feasible $z$ that has the same active constraints as $x$ and at
which the active linearization qualification holds.

The map $G$ keeps the coefficients of $g$ in the active gradients fixed.

**Reading.** The cone graph is closed. Inner continuity uses a selection on feasible points with the
same active set and qualifying linearization. The hemicontinuity statement concerns positive-radius
bounded sections of the cones.
-/
theorem continuous_normal_selection_on_active_face [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {C : Set V} {c : ι → V → ℝ} (hC : AC2 C) (hset : AC7 C c)
    (hc : ∀ i, ContDiff ℝ 1 (c i)) {x : V} (hx : ∀ i, 0 ≤ c i x)
    (hQ : ActiveLinearizedConeMatches C c x) {g : V} (hg : g ∈ normalCone (innerₗ V) C x) :
    ∃ G : V → V, Continuous G ∧ G x = g ∧
      ∀ z, (∀ i, 0 ≤ c i z) → (∀ i, c i z = 0 ↔ c i x = 0) →
        ActiveLinearizedConeMatches C c z → G z ∈ normalCone (innerₗ V) C z := by
  classical
  obtain ⟨a, ha, hax⟩ := (theorem_3_2_10_normalCone hC hset hx hQ g).1 hg
  let G (z : V) := ∑ i : {i // c i x = 0}, a i • (-gradient (c i) z)
  have hcont (i : ι) : Continuous (gradient (c i)) :=
    (InnerProductSpace.toDual ℝ V).symm.continuous.comp ((hc i).continuous_fderiv one_ne_zero)
  refine ⟨G, continuous_finsetSum _ fun i _ => (hcont i).neg.const_smul (a i), hax, ?_⟩
  intro z hz hface hzQ
  apply (theorem_3_2_10_normalCone hC hset hz hzQ (G z)).2
  let e : {i // c i x = 0} ≃ {i // c i z = 0} :=
    Equiv.subtypeEquivRight fun i => (hface i).symm
  refine ⟨fun i => a (e.symm i), fun i => ha (e.symm i), ?_⟩
  rw [← Equiv.sum_comp e]
  simp [G, e]

private theorem upperHemicontinuous_inter_compact {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {F : X → Set Y} {K : Set Y} (hK : IsCompact K)
    (hF : IsClosed {p : X × Y | p.2 ∈ F p.1}) :
    UpperHemicontinuous (fun x ↦ F x ∩ K) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply upperHemicontinuous_iff_forall_isOpen.mpr
  intro x U hU hx
  let D : Set (X × K) := {p | (p.2 : Y) ∈ F p.1 ∧ (p.2 : Y) ∈ Uᶜ}
  have hD : IsClosed D := (hF.preimage
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).inter
    (hU.isClosed_compl.preimage (continuous_subtype_val.comp continuous_snd))
  have hclosed := (isClosedMap_fst_of_compactSpace (X := X) (Y := K)) D hD
  have hx' : x ∈ (Prod.fst '' D)ᶜ := by
    rintro ⟨⟨y, v⟩, hv, rfl⟩
    exact hv.2 (hx ⟨hv.1, v.property⟩)
  filter_upwards [hclosed.isOpen_compl.mem_nhds hx'] with y hy
  intro v hv
  by_contra hvU
  exact hy ⟨(y, ⟨v, hv.2⟩), ⟨hv.1, hvU⟩, rfl⟩

private theorem lowerHemicontinuous_inter_closedBall_of_smul
    {X : Type*} [TopologicalSpace X] {F : X → Set V}
    (hF : LowerHemicontinuous F)
    (hsmul : ∀ x (a : ℝ), 0 ≤ a → ∀ d ∈ F x, a • d ∈ F x)
    {R : ℝ} (hR : 0 < R) :
    LowerHemicontinuous (fun x ↦ F x ∩ Metric.closedBall 0 R) := by
  apply lowerHemicontinuous_iff.mpr
  intro x
  apply lowerHemicontinuousAt_iff.mpr
  intro U hU hhit
  obtain ⟨d, ⟨hdF, hdB⟩, hdU⟩ := hhit
  have hlim : Tendsto (fun a : ℝ ↦ a • d) (𝓝[<] (1 : ℝ)) (𝓝 d) := by
    have ht : Tendsto (fun a : ℝ ↦ a) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    simpa using ht.smul (tendsto_const_nhds (x := d))
  obtain ⟨a, haU, ha⟩ := ((hlim.eventually (hU.mem_nhds hdU)).and
    (Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1))).exists
  have had : a • d ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ha.1.le]
    have hdR : ‖d‖ ≤ R := by simpa [Metric.mem_closedBall] using hdB
    exact (mul_le_mul_of_nonneg_left hdR ha.1.le).trans_lt
      (by simpa using mul_lt_mul_of_pos_right ha.2 hR)
  have hhit' : (F x ∩ (U ∩ Metric.ball 0 R)).Nonempty :=
    ⟨a • d, hsmul x a ha.1.le d hdF, haU, had⟩
  filter_upwards [(lowerHemicontinuousAt_iff.mp (lowerHemicontinuous_iff.mp hF x))
    (U ∩ Metric.ball 0 R) (hU.inter Metric.isOpen_ball) hhit'] with y hy
  obtain ⟨z, hz, hzU, hzR⟩ := hy
  exact ⟨z, ⟨hz, Metric.ball_subset_closedBall hzR⟩, hzU⟩

/-- **Theorem 3.2.10** of [conn2000trust], continuity on a fixed active face. Let $V$, $C$ and $c_i$
be as in `ConnGouldToint.Chapter03.theorem_3_2_10_normalCone`, with each $c_i$ continuously
differentiable. Let $x_0 \in V$ and $R > 0$, and let $S$ be the set of feasible $z$ that have
the same active constraints as $x_0$ and at which the active linearization qualification holds.
On $S$, the correspondences
$$z \mapsto N_C(z) \cap \bar{B}(0, R) \quad \text{and} \quad z \mapsto T_C(z) \cap \bar{B}(0,
  R)$$
are both upper and lower hemicontinuous.

**Reading.** The source states that the normal and tangent cones are continuous. Here the
continuity is stated on a face with a fixed active set and for the sections of the cones by
closed balls, which gives the usual local convergence of closed cones.

**Reading.** The cone graph is closed. Inner continuity uses a selection on feasible points with the
same active set and qualifying linearization. The hemicontinuity statement concerns positive-radius
bounded sections of the cones.
-/
theorem theorem_3_2_10_face_continuity [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {C : Set V} {c : ι → V → ℝ} (hC : AC2 C) (hset : AC7 C c)
    (hc : ∀ i, ContDiff ℝ 1 (c i)) (x₀ : V) {R : ℝ} (hR : 0 < R) :
    let S := {z : V | (∀ i, 0 ≤ c i z) ∧ (∀ i, c i z = 0 ↔ c i x₀ = 0) ∧
      ActiveLinearizedConeMatches C c z}
    let N := fun z : S ↦ normalCone (innerₗ V) C (z : V) ∩ Metric.closedBall 0 R
    let T := fun z : S ↦ posTangentConeAt C (z : V) ∩ Metric.closedBall 0 R
    UpperHemicontinuous N ∧ LowerHemicontinuous N ∧ UpperHemicontinuous T ∧
      LowerHemicontinuous T := by
  classical
  intro S N T
  let N₀ (z : S) := normalCone (innerₗ V) C (z : V)
  let T₀ (z : S) := posTangentConeAt C (z : V)
  have hmemC (z : S) : (z : V) ∈ C := by
    rw [hset]
    exact z.property.1
  have hnclosed : IsClosed {p : S × V | p.2 ∈ N₀ p.1} :=
    (isClosed_normalCone_graph C).preimage
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have htclosed : IsClosed {p : S × V | p.2 ∈ T₀ p.1} := by
    have heq : {p : S × V | p.2 ∈ T₀ p.1} =
        ⋂ i : {i // c i x₀ = 0}, {p : S × V | 0 ≤ fderiv ℝ (c i) (p.1 : V) p.2} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, T₀]
      rw [p.1.property.2.2 p.2]
      constructor
      · exact fun h i ↦ h i ((p.1.property.2.1 i).mpr i.property)
      · exact fun h i hi ↦ h ⟨i, (p.1.property.2.1 i).mp hi⟩
    rw [heq]
    apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const
      ((((hc i).continuous_fderiv one_ne_zero).comp
        (continuous_subtype_val.comp continuous_fst)).clm_apply continuous_snd)
  have hNlow : LowerHemicontinuous N₀ := by
    apply lowerHemicontinuous_iff.mpr
    intro x
    apply lowerHemicontinuousAt_iff.mpr
    intro U hU hmeet
    obtain ⟨g, hg, hgU⟩ := hmeet
    obtain ⟨G, hG, hGx, hGN⟩ :=
      continuous_normal_selection_on_active_face hC hset hc x.property.1 x.property.2.2 hg
    have hcont : Continuous (fun z : S ↦ G (z : V)) := hG.comp continuous_subtype_val
    have hGmem : ∀ z : S, G z ∈ N₀ z := fun z ↦
      hGN z z.property.1 (fun i ↦ (z.property.2.1 i).trans (x.property.2.1 i).symm)
        z.property.2.2
    have hu : (G (x : V)) ∈ U := hGx.symm ▸ hgU
    filter_upwards [(hcont.tendsto x).eventually (hU.mem_nhds hu)] with z hz
    exact ⟨G z, hGmem z, hz⟩
  have hTlow : LowerHemicontinuous T₀ := by
    apply lowerHemicontinuous_iff.mpr
    intro x
    apply lowerHemicontinuousAt_iff.mpr
    intro U hU hmeet
    obtain ⟨d, hd, hdU⟩ := hmeet
    obtain ⟨α, l, hl, a, w, hw₀, hwC, hlim⟩ := exists_fun_of_mem_tangentConeAt hd
    let : l.NeBot := hl
    obtain ⟨j, hjC, hjU⟩ := (hwC.and (hlim.eventually (hU.mem_nhds hdU))).exists
    let y : V := (x : V) + w j
    let G (z : S) : V := (a j : ℝ) • (y - (z : V))
    have hG : Continuous G := (continuous_const.sub continuous_subtype_val).const_smul _
    have hGx : G x ∈ U := by
      simpa [G, y, NNReal.smul_def] using hjU
    have hGmem (z : S) : G z ∈ T₀ z := by
      have htan := sub_mem_posTangentConeAt_of_segment_subset
        (hC.2.2.segment_subset (hmemC z) hjC)
      apply (z.property.2.2 _).mpr
      intro i hi
      rw [show G z = (a j : ℝ) • (y - (z : V)) from rfl, map_smul, smul_eq_mul]
      exact mul_nonneg (a j).coe_nonneg ((z.property.2.2 _).mp htan i hi)
    filter_upwards [(hG.tendsto x).eventually (hU.mem_nhds hGx)] with z hz
    exact ⟨G z, hGmem z, hz⟩
  let : ProperSpace V := FiniteDimensional.proper_real V
  refine ⟨upperHemicontinuous_inter_compact (isCompact_closedBall _ _) hnclosed,
    lowerHemicontinuous_inter_closedBall_of_smul hNlow ?_ hR,
    upperHemicontinuous_inter_compact (isCompact_closedBall _ _) htclosed,
    lowerHemicontinuous_inter_closedBall_of_smul hTlow ?_ hR⟩
  · intro z a ha d hd y hy
    rw [map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos ha (hd y hy)
  · intro z a ha d hd
    apply (z.property.2.2 _).mpr
    intro i hi
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg ha ((z.property.2.2 _).mp hd i hi)

/-- **Theorem 3.2.12** of [conn2000trust]. Let $V$ be a real Hilbert space, let
$f : V \to \mathbb{R}$ be Lipschitz continuous on a neighbourhood of $x$, and let $x$ be a local
minimizer of $f$. Then $0 \in \partial^\circ f(x)$, $f^\circ(x; d) \ge 0$ for all $d$, and
$f^\circ(x; \cdot)$ is the support function of $\partial^\circ f(x)$.

**Generalization.** The book states the result on $\mathbb{R}^n$. The directional argument and
the Clarke support property hold in an arbitrary real Hilbert space.

The support property is `Optimization.HasClarkeSupport`.

**Generalization.** The Clarke condition and nonnegative directional derivatives hold in a complete
real Hilbert space. The result also states the support representation.
-/
theorem theorem_3_2_12 [CompleteSpace V] {f : V → ℝ} {x : V} (hmin : IsLocalMin f x)
    {U : Set V} {L : ℝ≥0} (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) :
    0 ∈ Optimization.clarkeSubgradient f x ∧
      (∀ d, 0 ≤ Optimization.clarkeDerivative f x d) ∧ Optimization.HasClarkeSupport f x := by
  have hd (d : V) : 0 ≤ Optimization.clarkeDerivative f x d := by
    apply Optimization.le_clarkeDerivative_of_eventually_base_quotient_ge hU hL
    have ht : Tendsto (fun t : ℝ => x + t • d) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
      have ht₀ : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_right nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds (x := x)).add
        (ht₀.smul (tendsto_const_nhds (x := d)))
    filter_upwards [ht.eventually hmin, self_mem_nhdsWithin] with t ht htpos
    exact div_nonneg (sub_nonneg.2 ht) htpos.le
  refine ⟨?_, hd, Optimization.hasClarkeSupport_of_lipschitzOnWith hU hL⟩
  intro d
  simpa using hd d

private theorem composite_linearized_clarke_nonneg
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {f : V → ℝ} {c : V → W} {h : W → ℝ} {x : V}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    (hmin : IsLocalMin (fun z => f z + h (c z)) x)
    {U : Set W} {L : ℝ≥0} (hU : U ∈ 𝓝 (c x)) (hL : LipschitzOnWith L h U) (d : V) :
    0 ≤ fderiv ℝ f x d + Optimization.clarkeDerivative h (c x) (fderiv ℝ c x d) := by
  let g (t : ℝ) := x + t • d
  let v := fderiv ℝ c x d
  let F := fderiv ℝ f x d
  have hg : HasDerivAt g d 0 := by
    simpa [g] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have htg : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    simpa [g] using hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hg0 : g 0 = x := by simp [g]
  have htf : Tendsto (fun t : ℝ => (f (g t) - f x) / t) (𝓝[>] 0) (𝓝 F) := by
    have hf' : HasFDerivAt f (fderiv ℝ f x) (g 0) := by simpa only [hg0] using hf.hasFDerivAt
    have hd := (hf'.comp_hasDerivAt (0 : ℝ) hg).tendsto_slope_zero_right
    simpa [Function.comp_def, g, F, smul_eq_mul, div_eq_mul_inv, mul_comm] using hd
  have htc : Tendsto (fun t : ℝ => t⁻¹ • (c (g t) - c x)) (𝓝[>] 0) (𝓝 v) := by
    have hc' : HasFDerivAt c (fderiv ℝ c x) (g 0) := by simpa only [hg0] using hc.hasFDerivAt
    have hd := (hc'.comp_hasDerivAt (0 : ℝ) hg).tendsto_slope_zero_right
    simpa [Function.comp_def, g, v] using hd
  have hte : Tendsto (fun t : ℝ => (L : ℝ) * ‖t⁻¹ • (c (g t) - c x) - v‖)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ((htc.sub (tendsto_const_nhds (x := v))).norm.const_mul (L : ℝ))
  have htm : Tendsto (fun t : ℝ => c x + t • v) (𝓝[>] 0) (𝓝 (c x)) := by
    have ht₀ : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds (x := c x)).add
      (ht₀.smul (tendsto_const_nhds (x := v)))
  change 0 ≤ F + Optimization.clarkeDerivative h (c x) v
  by_contra! hneg
  let ε := -(F + Optimization.clarkeDerivative h (c x) v) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hlow : -F - ε ≤ Optimization.clarkeDerivative h (c x) v := by
    apply Optimization.le_clarkeDerivative_of_eventually_base_quotient_ge hU hL
    filter_upwards [htg.eventually hmin, htf.eventually_lt_const (by linarith : F < F + ε / 2),
      hte.eventually_lt_const (half_pos hε), (hc.continuousAt.tendsto.comp htg).eventually hU,
      htm.eventually hU, self_mem_nhdsWithin] with t hm hft het hct hmt ht
    change 0 < t at ht
    have hnorm : ‖t⁻¹ • (c (g t) - c x) - v‖ = ‖c (g t) - (c x + t • v)‖ / t := by
      have heq : t⁻¹ • (c (g t) - c x) - v = t⁻¹ • (c (g t) - (c x + t • v)) := by
        rw [show c (g t) - (c x + t • v) = (c (g t) - c x) - t • v by abel]
        simp only [smul_sub, inv_smul_smul₀ ht.ne']
      rw [heq, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), div_eq_mul_inv, mul_comm]
    have hLip := hL.dist_le_mul _ hct _ hmt
    rw [Real.dist_eq, dist_eq_norm] at hLip
    have herr : (h (c (g t)) - h (c x + t • v)) / t ≤
        (L : ℝ) * ‖t⁻¹ • (c (g t) - c x) - v‖ := by
      rw [hnorm, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right ((le_abs_self _).trans hLip) ht.le
    have hq : 0 ≤ (f (g t) - f x) / t + (h (c (g t)) - h (c x)) / t := by
      change f x + h (c x) ≤ f (g t) + h (c (g t)) at hm
      rw [← add_div]
      exact div_nonneg (by linarith) ht.le
    have hs : (h (c (g t)) - h (c x)) / t =
        (h (c (g t)) - h (c x + t • v)) / t + (h (c x + t • v) - h (c x)) / t := by ring
    rw [hs] at hq
    linarith
  dsimp [ε] at hlow
  linarith

/-- **Corollary 3.2.13** of [conn2000trust]. Let $V$ be a real Hilbert space and $W$ a
finite-dimensional real inner product space. Let $f : V \to \mathbb{R}$ and $c : V \to W$ be
differentiable at $x$, let $h : W \to \mathbb{R}$ be Lipschitz continuous on a neighbourhood of
$c(x)$, and let $x$ be a local minimizer of $f + h \circ c$. Then

* there is $y \in \partial^\circ h(c(x))$ with $\nabla f(x) + c'(x)^* y = 0$, and
* $f'(x) d + h^\circ(c(x); c'(x) d) \ge 0$ for every $d \in V$.

**Correction.** The source identifies $f'(x) d + h^\circ(c(x); c'(x) d)$ with the Clarke
directional derivative of the composite $f + h \circ c$. This identity fails in general; see
`ConnGouldToint.Chapter03.clarke_composite_equality_counterexample`. The statement uses the
linearized bound, which is the support function of the set of $\nabla f(x) + c'(x)^* y$.

**Correction.** The Clarke derivative of the composite is bounded above by the chain-rule
expression. The stationarity conclusion uses that upper bound. A Lipschitz example shows that the
printed derivative equality can fail.
-/
theorem corollary_3_2_13 [CompleteSpace V]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {f : V → ℝ} {c : V → W} {h : W → ℝ} {x : V}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    (hmin : IsLocalMin (fun z => f z + h (c z)) x)
    {U : Set W} {L : ℝ≥0} (hU : U ∈ 𝓝 (c x)) (hL : LipschitzOnWith L h U) :
    (∃ y ∈ Optimization.clarkeSubgradient h (c x),
      gradient f x + (fderiv ℝ c x).adjoint y = 0) ∧
      ∀ d, 0 ≤ fderiv ℝ f x d + Optimization.clarkeDerivative h (c x) (fderiv ℝ c x d) := by
  let K := Optimization.clarkeSubgradient h (c x)
  let J := (fderiv ℝ c x).adjoint
  let P := (fun y => gradient f x + J y) '' K
  have hK := Optimization.isCompact_clarkeSubgradient hU hL
  have hP : IsClosed P := (hK.image (continuous_const.add J.continuous)).isClosed
  have hcP : Convex ℝ P := by
    intro a ha b hb s t hs ht hst
    obtain ⟨u, hu, rfl⟩ := ha
    obtain ⟨v, hv, rfl⟩ := hb
    refine ⟨s • u + t • v, Optimization.convex_clarkeSubgradient h (c x) hu hv hs ht hst, ?_⟩
    simp only [map_add, map_smul, smul_add]
    have he : gradient f x = s • gradient f x + t • gradient f x := by
      rw [← add_smul, hst, one_smul]
    conv_lhs => rw [he]
    abel
  have hsupp := Optimization.hasClarkeSupport_of_lipschitzOnWith hU hL
  have hzero : (0 : V) ∈ P := by
    rw [← hP.closure_eq, ← hcP.convexHull_eq]
    apply (mem_closure_convexHull_iff_le_supportFn (B := innerₗ V) P 0).2
    intro d
    let v := fderiv ℝ c x d
    have hcont : Continuous (fun z : W => ⟪z, v⟫) := continuous_id.inner continuous_const
    obtain ⟨y, hy, hymax⟩ := hK.exists_isMaxOn hsupp.nonempty hcont.continuousOn
    have houter : Optimization.clarkeDerivative h (c x) v ≤ ⟪y, v⟫ := by
      have hle := (supportFn_le_coe_iff (B := innerₗ W) (s := K) (y := v)).2
        (fun z hz => hymax hz)
      rw [hsupp v] at hle
      exact EReal.coe_le_coe_iff.1 hle
    have hdir := composite_linearized_clarke_nonneg hf hc hmin hU hL d
    have hpair : 0 ≤ ⟪gradient f x + J y, d⟫ := by
      rw [inner_add_left, inner_gradient_left, ContinuousLinearMap.adjoint_inner_left]
      exact hdir.trans (add_le_add_right houter _)
    have hmem : gradient f x + J y ∈ P := ⟨y, hy, rfl⟩
    have hcoe : ((0 : ℝ) : EReal) ≤ ((⟪gradient f x + J y, d⟫ : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.2 hpair
    simpa only [innerₗ_apply_apply, inner_zero_left] using
      hcoe.trans (le_supportFn (B := innerₗ V) hmem d)
  exact ⟨hzero, composite_linearized_clarke_nonneg hf hc hmin hU hL⟩

/-- **Corollary 3.2.13** of [conn2000trust], counterexample to equality. There are
$h : \mathbb{R}^2 \to \mathbb{R}$, Lipschitz with constant $4$, and $d \in \mathbb{R}^2$ such
that the function $t \mapsto h(td)$ has Clarke derivative $0$ at $0$ in the direction $1$, while
$h^\circ(0; d) \ge 2$.

With the linear map $c(t) = td$, the Clarke derivative of $h \circ c$ is smaller than
$h^\circ(c(0); c'(0) 1)$, although the restriction is constant and the embedding is linear.

**Correction.** The Clarke derivative of the composite is bounded above by the chain-rule
expression. The stationarity conclusion uses that upper bound. A Lipschitz example shows that the
printed derivative equality can fail.
-/
theorem clarke_composite_equality_counterexample :
    ∃ (h : EuclideanSpace ℝ (Fin 2) → ℝ) (d : EuclideanSpace ℝ (Fin 2)),
      LipschitzWith 4 h ∧
      Optimization.clarkeDerivative (fun t : ℝ => h (t • d)) 0 1 = 0 ∧
      2 ≤ Optimization.clarkeDerivative h 0 d := by
  let h (p : EuclideanSpace ℝ (Fin 2)) := |p 0 + p 1| - |p 0 - p 1|
  let d : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]
  let e : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0, 1]
  have hL : LipschitzWith 4 h := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    have hb (i : Fin 2) : |p i - q i| ≤ dist p q := by
      simpa [dist_eq_norm, Real.norm_eq_abs] using PiLp.norm_apply_le (p - q) i
    have hplus : |(p 0 + p 1) - (q 0 + q 1)| ≤ 2 * dist p q := by
      rw [show (p 0 + p 1) - (q 0 + q 1) = (p 0 - q 0) + (p 1 - q 1) by ring]
      linarith [abs_add_le (p 0 - q 0) (p 1 - q 1), hb 0, hb 1]
    have hminus : |(p 0 - p 1) - (q 0 - q 1)| ≤ 2 * dist p q := by
      rw [show (p 0 - p 1) - (q 0 - q 1) = (p 0 - q 0) - (p 1 - q 1) by ring]
      linarith [abs_sub (p 0 - q 0) (p 1 - q 1), hb 0, hb 1]
    rw [Real.dist_eq]
    change |h p - h q| ≤ 4 * dist p q
    rw [show h p - h q =
      (|p 0 + p 1| - |q 0 + q 1|) - (|p 0 - p 1| - |q 0 - q 1|) by dsimp [h]; ring]
    exact (abs_sub _ _).trans (by
      linarith [(abs_abs_sub_abs_le_abs_sub (p 0 + p 1) (q 0 + q 1)).trans hplus,
        (abs_abs_sub_abs_le_abs_sub (p 0 - p 1) (q 0 - q 1)).trans hminus])
  refine ⟨h, d, hL, ?_, ?_⟩
  · have hz : (fun t : ℝ => h (t • d)) = fun _ => 0 := by
      funext t
      simp [h, d, PiLp.smul_apply]
    rw [hz]
    exact Optimization.clarkeDerivative_const 0 0 1
  · have ht₀ : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    have hy : Tendsto (fun t : ℝ => (2 * t) • e) (𝓝[>] 0) (𝓝 0) := by
      simpa using (ht₀.const_mul 2).smul (tendsto_const_nhds (x := e))
    apply Optimization.le_clarkeDerivative_of_eventually_path_quotient_ge
      (U := Set.univ) univ_mem hL.lipschitzOnWith hy
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    have h1 : h ((2 * t) • e + t • d) = 2 * t := by
      simp only [Fin.isValue, PiLp.add_apply, PiLp.smul_apply, Matrix.cons_val_zero,
        smul_eq_mul, mul_zero, mul_one, zero_add, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        add_zero, h, e, d]
      rw [abs_of_nonneg (by linarith : 0 ≤ t + 2 * t),
        abs_of_nonpos (by linarith : t - 2 * t ≤ 0)]
      ring
    have h2 : h ((2 * t) • e) = 0 := by simp [h, e, PiLp.smul_apply]
    rw [h1, h2, sub_zero]
    exact (le_div_iff₀ ht).2 le_rfl

end ConvexNonsmooth


/-- **Theorem 3.2.4** of [conn2000trust]. Let $E$ be a finite-dimensional real normed space, let
$f : E \to \mathbb{R}$ be differentiable at $x$, and let $x$ be a local minimizer of $f$ on the
set $F = \{y : c_i(y) = 0 \ (i \in \mathcal{E}), \ c_i(y) \ge 0 \ (i \in \mathcal{I})\}$ with
finite index sets. Suppose that every $d$ with $c_i'(x) d = 0$ for $i \in \mathcal{E}$ and
$c_i'(x) d \ge 0$ for active $i \in \mathcal{I}$ lies in $T_F(x)$. Then there are multipliers
$y_i$ with
$$f'(x) = \sum_{i \in \mathcal{E}} y_i c_i'(x) + \sum_{i \in \mathcal{I}} y_i c_i'(x),$$
$c_i(x) = 0$ for $i \in \mathcal{E}$, and $c_i(x) \ge 0$, $y_i \ge 0$ and $c_i(x) y_i = 0$ for
$i \in \mathcal{I}$.

**Generalization.** The book assumes that $f$ and the constraints are continuously
differentiable. The argument needs differentiability of $f$ at $x$ and the inclusion of the
linearized directions in the tangent cone. The constraint derivatives in that inclusion are
Mathlib's `fderiv`.

The qualification is the tangent inclusion form of AO.1. The constraints are written
$c_i \ge 0$, as in the source, so the inequality multipliers are nonnegative with this sign of
the stationarity condition. In the Lean statement the equality constraints are `ce` with
multipliers `l`, and the inequality constraints are `ci` with multipliers `μ`.

**Generalization.** The objective only needs a derivative at the candidate, with the necessary
linearized-to-feasible tangent inclusion as an explicit premise.
-/
theorem theorem_3_2_4 [FiniteDimensional ℝ E] {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : E → ℝ} {ce : ι → E → ℝ} {ci : κ → E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x)
    (hx : x ∈ Constrained.feasible ce (fun i y ↦ -ci i y))
    (hQ : ∀ d : E, (∀ i, fderiv ℝ (ce i) x d = 0) →
      (∀ i, ci i x = 0 → 0 ≤ fderiv ℝ (ci i) x d) →
      d ∈ posTangentConeAt (Constrained.feasible ce (fun i y ↦ -ci i y)) x)
    (hmin : IsLocalMinOn f (Constrained.feasible ce (fun i y ↦ -ci i y)) x) :
    ∃ (l : ι → ℝ) (μ : κ → ℝ),
      fderiv ℝ f x = (∑ i, l i • fderiv ℝ (ce i) x) + ∑ i, μ i • fderiv ℝ (ci i) x ∧
      (∀ i, ce i x = 0) ∧ (∀ i, 0 ≤ ci i x ∧ 0 ≤ μ i ∧ ci i x * μ i = 0) := by
  obtain ⟨l, μ, h⟩ := Constrained.exists_kkt_of_linearized_feasible_directions
    (f' := fderiv ℝ f) (h' := fun i ↦ fderiv ℝ (ce i)) (g' := fun i y ↦ -fderiv ℝ (ci i) y)
    hx fun d hd₁ hd₂ ↦ hmin.hasFDerivWithinAt_nonneg hf.hasFDerivAt.hasFDerivWithinAt
      (hQ d hd₁ fun i hi ↦ by simpa using hd₂ i (by simp [Constrained.activeSet, hi]))
  refine ⟨-l, μ, ?_, h.feasible_eq, fun i ↦ ⟨by simpa using h.feasible_ineq i, h.nonneg i, ?_⟩⟩
  · have hs := h.stationary
    simp only [smul_neg, Finset.sum_neg_distrib] at hs
    simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
    apply sub_eq_zero.mp
    calc
      _ = fderiv ℝ f x + (∑ i, l i • fderiv ℝ (ce i) x) -
          ∑ i, μ i • fderiv ℝ (ci i) x := by abel
      _ = 0 := by simpa [sub_eq_add_neg] using hs
  · have hp := h.complementary i
    simpa [mul_comm] using hp

section SmoothSecondOrder

open Constrained

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [FiniteDimensional ℝ E]


omit [Fintype ι] [Fintype κ] [FiniteDimensional ℝ E] in
/-- **Assumption AO.1** of [conn2000trust]. For constraints $h_i(x) = 0$ and $g_j(x) \le 0$ with
feasible set $F$, the **first-order constraint qualification** holds at $x$ if every direction
that satisfies the linearized constraints is tangent to $F$: if $h_i'(x) d = 0$ for all $i$ and
$g_j'(x) d \le 0$ for all active $j$, then $d \in T_F(x)$. -/
def AO1 (h : ι → E → ℝ) (g : κ → E → ℝ) (x : E) : Prop :=
  ∀ d : E, (∀ i, fderiv ℝ (h i) x d = 0) →
    (∀ j ∈ activeSet g x, fderiv ℝ (g j) x d ≤ 0) → d ∈ posTangentConeAt (feasible h g) x

omit [Fintype ι] [Fintype κ] [FiniteDimensional ℝ E] in
/-- **Assumption AO.2** of [conn2000trust]. For constraints $h_i(x) = 0$ and $g_j(x) \le 0$, the
**second-order constraint qualification** holds at $x$ if for every multiplier vector
$\mu \ge 0$ with $\mu_j > 0$ only for active $j$, every direction in the critical cone
$\mathcal{C}(x, \mu)$ is tangent at $x$ to the set
$$F_\mu = \{y \in F : g_j(y) = 0 \text{ whenever } \mu_j > 0\}.$$

The critical cone `Constrained.criticalCone` consists of the $d$ with $h_i'(x) d = 0$ for all
$i$, $g_j'(x) d = 0$ for active $j$ with $\mu_j > 0$, and $g_j'(x) d \le 0$ for active $j$ with
$\mu_j = 0$. The multipliers $\mu$ specify which constraints are strongly active. -/
def AO2 (h : ι → E → ℝ) (g : κ → E → ℝ) (x : E) : Prop :=
  ∀ μ : κ → ℝ, (∀ j, 0 ≤ μ j) → (∀ j, 0 < μ j → j ∈ activeSet g x) →
    criticalCone (fun i ↦ fderiv ℝ (h i)) g (fun j ↦ fderiv ℝ (g j)) x μ ⊆
      posTangentConeAt (stronglyActiveFeasible h g μ) x

omit [Fintype ι] [Fintype κ] in
/-- **Section 3.2.2** of [conn2000trust]. Let $E$ be a finite-dimensional real normed space, let
$h_i$ and $g_j$ be strictly differentiable at $x$, and let $x$ be a regular point: $x$ is
feasible and the derivatives $h_i'(x)$ and $g_j'(x)$ for active $j$ are linearly independent.
Then AO.1 and AO.2 hold at $x$. -/
theorem ao1_ao2_of_isRegularPointIneq [Finite ι] [Finite κ]
    {h : ι → E → ℝ} {g : κ → E → ℝ} {x : E}
    (hreg : IsRegularPointIneq h (fun i ↦ fderiv ℝ (h i)) g (fun j ↦ fderiv ℝ (g j)) x)
    (hh : ∀ i, HasStrictFDerivAt (h i) (fderiv ℝ (h i) x) x)
    (hg : ∀ j, HasStrictFDerivAt (g j) (fderiv ℝ (g j) x) x) :
    AO1 h g x ∧ AO2 h g x := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  exact ⟨fun _ ↦ mem_posTangentConeAt_of_isRegularPointIneq hreg hh hg,
    fun _ ↦ criticalCone_subset_tangent_stronglyActiveFeasible_of_isRegularPointIneq hreg hh hg⟩

/-- **Theorem 3.2.5** of [conn2000trust], under AO.1 and AO.2. Let $E$ be a finite-dimensional real
normed space, let $f$, $h_i$ and $g_j$ be twice continuously differentiable at a feasible point
$x$, let AO.1 and AO.2 hold at $x$, and let $x$ be a local minimizer of $f$ on the feasible set.
Then there are multipliers $\lambda$ and $\mu$ such that $(x, \lambda, \mu)$ is a KKT point and
$$\langle d, \nabla^2 \mathcal{L}(x) d \rangle \ge 0 \quad \text{for all } d \in \mathcal{C}(x,
  \mu),$$
where $\mathcal{L} = f + \sum_i \lambda_i h_i + \sum_j \mu_j g_j$.

**Generalization.** The book assumes that the objective and constraints are twice
continuously differentiable everywhere. The conclusion requires this smoothness only at $x$.

The inequalities are written $g_j \le 0$. The KKT conditions are `Constrained.IsKKTPoint`:
feasibility, stationarity $f'(x) + \sum_i \lambda_i h_i'(x) + \sum_j \mu_j g_j'(x) = 0$,
$\mu \ge 0$ and $\mu_j g_j(x) = 0$.

**Reading.** Twice continuous differentiability is local to the candidate. The necessary condition
is given with explicit tangent qualifications and in a variant using regularity of the active
constraints.
-/
theorem theorem_3_2_5_of_constraint_qualifications
    {f : E → ℝ} {h : ι → E → ℝ} {g : κ → E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hh : ∀ i, ContDiffAt ℝ 2 (h i) x)
    (hg : ∀ j, ContDiffAt ℝ 2 (g j) x)
    (hx : x ∈ feasible h g) (hQ₁ : AO1 h g x) (hQ₂ : AO2 h g x)
    (hmin : IsLocalMinOn f (feasible h g) x) :
    ∃ (l : ι → ℝ) (μ : κ → ℝ),
      IsKKTPoint (fderiv ℝ f) h (fun i ↦ fderiv ℝ (h i)) g (fun j ↦ fderiv ℝ (g j)) x l μ ∧
      ∀ d ∈ criticalCone (fun i ↦ fderiv ℝ (h i)) g (fun j ↦ fderiv ℝ (g j)) x μ,
        0 ≤ iteratedFDeriv ℝ 2 (kktLagrangian f h g l μ) x (fun _ ↦ d) := by
  have hfd := (hf.differentiableAt (by norm_num)).hasFDerivAt
  obtain ⟨l, μ, hkkt⟩ := exists_kkt_of_linearized_feasible_directions hx
    (fun d hd₁ hd₂ ↦ hmin.hasFDerivWithinAt_nonneg hfd.hasFDerivWithinAt (hQ₁ d hd₁ hd₂))
  have hact (j : κ) (hj : 0 < μ j) : j ∈ activeSet g x :=
    mem_activeSet.mpr ((mul_eq_zero.mp (hkkt.complementary j)).resolve_left hj.ne')
  exact ⟨l, μ, hkkt, secondOrder_necessary_of_isKKTPoint_of_tangent hkkt hmin hf hh hg hfd
    (fun i ↦ ((hh i).differentiableAt (by norm_num)).hasFDerivAt)
    (fun j ↦ ((hg j).differentiableAt (by norm_num)).hasFDerivAt) (hQ₂ μ hkkt.nonneg hact)⟩

/-- **Theorem 3.2.5** of [conn2000trust]. Let $E$ be a finite-dimensional real normed space, let
$f$, $h_i$ and $g_j$ be twice continuously differentiable at $x$, let $x$ be a regular point
(feasible, with linearly independent $h_i'(x)$ and active $g_j'(x)$), and let $x$ be a local
minimizer of $f$ on the feasible set. Then there are multipliers $\lambda$ and $\mu$ such that
$(x, \lambda, \mu)$ is a KKT point and
$$\langle d, \nabla^2 \mathcal{L}(x) d \rangle \ge 0 \quad \text{for all } d \in \mathcal{C}(x,
  \mu).$$

**Generalization.** The book assumes twice-continuous differentiability everywhere. The
statement uses only the smoothness at $x$. Linear independence gives the constraint
qualifications for this formulation.

The inequalities are written $g_j \le 0$, the negated constraints of the source, so the
inequality part of the Lagrangian is added. Linear independence supplies AO.1 and AO.2 by
`ConnGouldToint.Chapter03.ao1_ao2_of_isRegularPointIneq`.

**Reading.** Twice continuous differentiability is local to the candidate. The necessary condition
is given with explicit tangent qualifications and in a variant using regularity of the active
constraints.
-/
theorem theorem_3_2_5 {f : E → ℝ} {h : ι → E → ℝ} {g : κ → E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hh : ∀ i, ContDiffAt ℝ 2 (h i) x)
    (hg : ∀ j, ContDiffAt ℝ 2 (g j) x)
    (hreg : IsRegularPointIneq h (fun i ↦ fderiv ℝ (h i)) g (fun j ↦ fderiv ℝ (g j)) x)
    (hmin : IsLocalMinOn f (feasible h g) x) :
    ∃ (l : ι → ℝ) (μ : κ → ℝ),
      IsKKTPoint (fderiv ℝ f) h (fun i ↦ fderiv ℝ (h i)) g (fun j ↦ fderiv ℝ (g j)) x l μ ∧
      ∀ d ∈ criticalCone (fun i ↦ fderiv ℝ (h i)) g (fun j ↦ fderiv ℝ (g j)) x μ,
        0 ≤ iteratedFDeriv ℝ 2 (kktLagrangian f h g l μ) x (fun _ ↦ d) :=
  secondOrder_necessary_ineq hreg hmin hf hh hg
    (fun i ↦ ((hh i).differentiableAt (by norm_num)).hasFDerivAt)
    (fun j ↦ ((hg j).differentiableAt (by norm_num)).hasFDerivAt)

/-- **Theorem 3.2.6** of [conn2000trust]. Let $E$ be a finite-dimensional real normed space, let
$f$, $h_i$ and $g_j$ be twice continuously differentiable at $x$, and let $(x, \lambda, \mu)$ be
a KKT point. If
$$\langle d, \nabla^2 \mathcal{L}(x) d \rangle > 0 \quad \text{for all nonzero } d \in
  \mathcal{C}(x, \mu),$$
then $x$ is a strict local minimizer of $f$ on the feasible set.

**Generalization.** The book assumes twice-continuous differentiability everywhere; the
second-order sufficient condition uses this smoothness at $x$.

**Reading.** Twice continuous differentiability is local to the candidate. The necessary condition
is given with explicit tangent qualifications and in a variant using regularity of the active
constraints.
-/
theorem theorem_3_2_6 {f : E → ℝ} {h : ι → E → ℝ} {g : κ → E → ℝ} {x : E}
    {l : ι → ℝ} {μ : κ → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hh : ∀ i, ContDiffAt ℝ 2 (h i) x)
    (hg : ∀ j, ContDiffAt ℝ 2 (g j) x)
    (hkkt : IsKKTPoint (fderiv ℝ f) h (fun i ↦ fderiv ℝ (h i)) g (fun j ↦ fderiv ℝ (g j)) x l μ)
    (hpos : ∀ d ∈ criticalCone (fun i ↦ fderiv ℝ (h i)) g (fun j ↦ fderiv ℝ (g j)) x μ,
      d ≠ 0 → 0 < iteratedFDeriv ℝ 2 (kktLagrangian f h g l μ) x (fun _ ↦ d)) :
    Optimization.IsStrictLocalMinOn f (feasible h g) x :=
  isStrictLocalMinOn_of_secondOrder_sufficient hkkt hf hh hg
    (hf.differentiableAt (by norm_num)).hasFDerivAt
    (fun i ↦ ((hh i).differentiableAt (by norm_num)).hasFDerivAt)
    (fun j ↦ ((hg j).differentiableAt (by norm_num)).hasFDerivAt) hpos

end SmoothSecondOrder

section ActiveKKTSensitivity

variable {V Y P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

open ContinuousLinearMap

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Y] in
/-- **Theorem 3.2.7** of [conn2000trust], the linearized active KKT equations. For bounded linear
maps $A : V \to Y$ and $H : V \to V$ between real Hilbert spaces, the **active KKT block** is
the operator
$$(d, w) \mapsto (Hd + A^* w, \ Ad)$$
on $V \times Y$.

The multipliers enter the Lagrangian with the positive sign. A change of the sign of the
multipliers gives the convention of the source. -/
noncomputable def activeKKTLinearization (A : V →L[ℝ] Y) (H : V →L[ℝ] V) :
    (V × Y) →L[ℝ] (V × Y) :=
  (H.comp (fst ℝ V Y) + A.adjoint.comp (snd ℝ V Y)).prod (A.comp (fst ℝ V Y))

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Y] in
/-- **Theorem 3.2.7** of [conn2000trust]. The active KKT block maps $(d, w)$ to $(Hd + A^* w, Ad)$.
-/
@[simp] theorem activeKKTLinearization_apply (A : V →L[ℝ] Y) (H : V →L[ℝ] V)
    (z : V × Y) : activeKKTLinearization A H z = (H z.1 + A.adjoint z.2, A z.1) := rfl

/-- **Theorem 3.2.7** of [conn2000trust], invertibility. Let $V$ and $Y$ be finite-dimensional real
inner product spaces, let $A : V \to Y$ be surjective, and let $\langle Hd, d \rangle > 0$ for
every nonzero $d$ with $Ad = 0$. Then the active KKT block of $A$ and $H$ is invertible. -/
theorem theorem_3_2_7_activeKKT_invertible {A : V →L[ℝ] Y} {H : V →L[ℝ] V}
    (hA : Function.Surjective A) (hH : ∀ d : V, A d = 0 → d ≠ 0 → 0 < ⟪H d, d⟫) :
    (activeKKTLinearization A H).IsInvertible := by
  let B := activeKKTLinearization A H
  have hinj : Function.Injective B := (injective_iff_map_eq_zero B).mpr fun z hz ↦ by
    have h₁ : H z.1 + A.adjoint z.2 = 0 := congrArg Prod.fst hz
    have h₂ : A z.1 = 0 := congrArg Prod.snd hz
    have hv : z.1 = 0 := by
      by_contra hne
      have heq := congrArg (fun v : V ↦ ⟪v, z.1⟫) h₁
      simp only [inner_add_left, ContinuousLinearMap.adjoint_inner_left, h₂, inner_zero_right,
        add_zero, inner_zero_left] at heq
      exact (hH z.1 h₂ hne).ne' heq
    have hμ : A.adjoint z.2 = 0 := by simpa [hv] using h₁
    obtain ⟨v, hv'⟩ := hA z.2
    have hμ' : ⟪z.2, z.2⟫ = 0 := by
      calc
        _ = ⟪A.adjoint z.2, v⟫ := by rw [ContinuousLinearMap.adjoint_inner_left, hv']
        _ = 0 := by rw [hμ, inner_zero_left]
    exact Prod.ext hv (inner_self_eq_zero.mp hμ')
  have hsurj : Function.Surjective B := LinearMap.surjective_of_injective
    (f := B.toLinearMap) hinj
  exact ⟨ContinuousLinearEquiv.ofBijective B (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj), ContinuousLinearEquiv.coe_ofBijective ..⟩

/-- **Theorem 3.2.7** of [conn2000trust], openness. For finite-dimensional real inner product spaces
$V$ and $Y$, the set of pairs $(A, H)$ of linear maps such that $A : V \to Y$ is surjective and
$\langle Hd, d \rangle > 0$ for every nonzero $d$ with $Ad = 0$ is open.

The proof uses the compactness of the unit sphere to handle the varying kernel of $A$. -/
theorem theorem_3_2_7_activeKKT_conditions_open :
    IsOpen {p : (V →L[ℝ] Y) × (V →L[ℝ] V) | Function.Surjective p.1 ∧
      ∀ d : V, p.1 d = 0 → d ≠ 0 → 0 < ⟪p.2 d, d⟫} := by
  let X := (V →L[ℝ] Y) × (V →L[ℝ] V)
  let K := Metric.sphere (0 : V) 1
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let D : Set (X × K) := {q | q.1.1 (q.2 : V) = 0 ∧ ⟪q.1.2 (q.2 : V), (q.2 : V)⟫ ≤ 0}
  have hval : Continuous (fun q : X × K ↦ (q.2 : V)) :=
    continuous_subtype_val.comp continuous_snd
  have hAz : Continuous (fun q : X × K ↦ q.1.1 (q.2 : V)) :=
    (continuous_fst.comp continuous_fst).clm_apply hval
  have hHz : Continuous (fun q : X × K ↦ ⟪q.1.2 (q.2 : V), (q.2 : V)⟫) :=
    ((continuous_snd.comp continuous_fst).clm_apply hval).inner hval
  have hD : IsClosed D := (isClosed_eq hAz (continuous_const (y := (0 : Y)))).inter
    (isClosed_le hHz (continuous_const (y := (0 : ℝ))))
  have hbad := (isClosedMap_fst_of_compactSpace (X := X) (Y := K)) D hD
  have hB : Continuous (fun p : X ↦ activeKKTLinearization p.1 p.2) := by
    let i : V →L[ℝ] V × Y := inl ℝ V Y
    let j : Y →L[ℝ] V × Y := inr ℝ V Y
    let u : V × Y →L[ℝ] V := fst ℝ V Y
    let v : V × Y →L[ℝ] Y := snd ℝ V Y
    have heq : (fun p : X ↦ activeKKTLinearization p.1 p.2) =
        fun p ↦ i.comp (p.2.comp u) + i.comp (p.1.adjoint.comp v) + j.comp (p.1.comp u) := by
      funext p
      ext w <;> simp [i, j, u, v]
    rw [heq]
    exact ((continuous_const.clm_comp (continuous_snd.clm_comp continuous_const)).add
      (continuous_const.clm_comp
        ((ContinuousLinearMap.adjoint.continuous.comp continuous_fst).clm_comp
          continuous_const))).add
      (continuous_const.clm_comp (continuous_fst.clm_comp continuous_const))
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hp' : p ∈ (Prod.fst '' D)ᶜ := by
    rintro ⟨⟨q, d⟩, hd, rfl⟩
    have hnorm : ‖(d : V)‖ = 1 := mem_sphere_zero_iff_norm.mp d.property
    have hdne : (d : V) ≠ 0 := by intro hz; simp [hz] at hnorm
    exact (not_le_of_gt (hp.2 d hd.1 hdne)) hd.2
  have hinv := theorem_3_2_7_activeKKT_invertible hp.1 hp.2
  filter_upwards [hbad.isOpen_compl.mem_nhds hp',
    (hB.tendsto p).eventually hinv.eventually_nhds] with q hq hqB
  refine ⟨?_, ?_⟩
  · intro b
    obtain ⟨e, he⟩ := hqB
    obtain ⟨z, hz⟩ := e.surjective (0, b)
    refine ⟨z.1, ?_⟩
    have hb := congrArg Prod.snd hz
    change ((e : (V × Y) →L[ℝ] V × Y) z).2 = b at hb
    rwa [he, activeKKTLinearization_apply] at hb
  · intro d hd hdne
    by_contra! hnon
    let a := ‖d‖⁻¹
    have ha : 0 < a := inv_pos.mpr (norm_pos_iff.mpr hdne)
    let v : K := ⟨a • d, mem_sphere_zero_iff_norm.mpr (by
      rw [norm_smul, Real.norm_of_nonneg ha.le]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hdne))⟩
    apply hq
    refine ⟨(q, v), ⟨?_, ?_⟩, rfl⟩
    · change q.1 (a • d) = 0
      rw [map_smul, hd, smul_zero]
    · change ⟪q.2 (a • d), a • d⟫ ≤ 0
      rw [map_smul, real_inner_smul_left, real_inner_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos ha.le (mul_nonpos_of_nonneg_of_nonpos ha.le hnon)

/-- **Theorem 3.2.7** of [conn2000trust], the implicit branch. Let $P$ be a real Banach space and
$V$, $Y$ finite-dimensional real inner product spaces. Let
$F : P \times (V \times Y) \to V \times Y$ be continuously differentiable at $(p_0, z_0)$ with
$F(p_0, z_0) = 0$, and let its partial derivative in $z$ at $(p_0, z_0)$ be the active KKT block
of $A$ and $H$, where $A$ is surjective and $\langle Hd, d \rangle > 0$ for nonzero $d$ with
$Ad = 0$. Then there are a map $z : P \to V \times Y$, continuously differentiable at $p_0$ with
$z(p_0) = z_0$, an open set $U \ni p_0$ on which $z$ is continuous, and an open set $W \ni z_0$
such that for every $p \in U$, $z(p) \in W$ and the only zero of $F(p, \cdot)$ in $W$ is $z(p)$.

The function $F$ is the residual of the KKT equations with a fixed active set. -/
theorem theorem_3_2_7_implicit_branch {F : P × (V × Y) → V × Y}
    {p₀ : P} {z₀ : V × Y} {A : V →L[ℝ] Y} {H : V →L[ℝ] V}
    (hF : ContDiffAt ℝ 1 F (p₀, z₀)) (hzero : F (p₀, z₀) = 0)
    (hB : (fderiv ℝ F (p₀, z₀)).comp (inr ℝ P (V × Y)) = activeKKTLinearization A H)
    (hA : Function.Surjective A) (hH : ∀ d : V, A d = 0 → d ≠ 0 → 0 < ⟪H d, d⟫) :
    ∃ z : P → V × Y, ContDiffAt ℝ 1 z p₀ ∧ z p₀ = z₀ ∧
      ∃ U : Set P, IsOpen U ∧ p₀ ∈ U ∧ ContinuousOn z U ∧
        ∃ W : Set (V × Y), IsOpen W ∧ z₀ ∈ W ∧
          ∀ p ∈ U, z p ∈ W ∧ ∀ w ∈ W, F (p, w) = 0 ↔ w = z p := by
  have hi : ((fderiv ℝ F (p₀, z₀)).comp (inr ℝ P (V × Y))).IsInvertible :=
    hB ▸ theorem_3_2_7_activeKKT_invertible hA hH
  let z := hF.implicitFunction one_ne_zero hi
  have hz : z p₀ = z₀ := hF.implicitFunction_apply_self one_ne_zero hi
  have hzd : ContDiffAt ℝ 1 z p₀ := hF.contDiffAt_implicitFunction one_ne_zero hi
  have hu : {v | F v = 0 ↔ z v.1 = v.2} ∈ 𝓝 p₀ ×ˢ 𝓝 z₀ := by
    rw [← nhds_prod_eq]
    change ∀ᶠ v in 𝓝 (p₀, z₀), F v = 0 ↔ z v.1 = v.2
    simpa [z, hzero] using hF.eventually_apply_eq_iff_implicitFunction one_ne_zero hi
  obtain ⟨U₀, hU₀, W₀, hW₀, hsub⟩ := Filter.mem_prod_iff.mp hu
  obtain ⟨U, hUU, hU, hp⟩ := mem_nhds_iff.mp hU₀
  obtain ⟨W, hWW, hW, hw⟩ := mem_nhds_iff.mp hW₀
  have hzW : z ⁻¹' W ∈ 𝓝 p₀ := hzd.continuousAt (hW.mem_nhds (hz.symm ▸ hw))
  obtain ⟨U', hU'W, hU', hp'⟩ := mem_nhds_iff.mp hzW
  have hreg : {p | ContDiffAt ℝ 1 z p} ∈ 𝓝 p₀ := hzd.eventually (by norm_num)
  obtain ⟨U'', hU''reg, hU'', hp''⟩ := mem_nhds_iff.mp hreg
  refine ⟨z, hzd, hz, U ∩ (U' ∩ U''), hU.inter (hU'.inter hU''),
    ⟨hp, hp', hp''⟩, ?_, W, hW, hw, ?_⟩
  · intro p hpU
    have hpreg : ContDiffAt ℝ 1 z p := hU''reg hpU.2.2
    exact hpreg.continuousAt.continuousWithinAt
  · intro p hpU
    refine ⟨hU'W hpU.2.1, fun w hwW ↦ ?_⟩
    have he := hsub (show (p, w) ∈ U₀ ×ˢ W₀ from ⟨hUU hpU.1, hWW hwW⟩)
    exact he.trans eq_comm

end ActiveKKTSensitivity

section MixedKKTSensitivity

open Constrained ContinuousLinearMap

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

/-- **Theorem 3.2.7** of [conn2000trust], multiplier space. The multipliers of the equality
constraints indexed by $\iota$ and of the active inequality constraints indexed by $\kappa$ form
the Euclidean space $\mathbb{R}^{\iota \sqcup \kappa}$. -/
abbrev ActiveDual (ι κ : Type*) [Fintype ι] [Fintype κ] :=
  EuclideanSpace ℝ (ι ⊕ κ)

omit [FiniteDimensional ℝ V] in
/-- **Theorems 3.2.7 and 15.2.2** of [conn2000trust], active stationarity. Let $V$ be a real Hilbert
space, and let the inequality constraints $g_j$ be indexed by $\kappa \sqcup \nu$, with $\kappa$
the active ones. Let $A : V \to \mathbb{R}^{\iota \sqcup \kappa}$ have the rows $h_i'(x)$ and
$g_j'(x)$ for $j \in \kappa$. Then for every multiplier vector $m = (\lambda, \mu_\kappa)$,
$$\nabla f(x) + A^* m = 0 \iff f'(x) + \sum_i \lambda_i h_i'(x) + \sum_{j \in \kappa \sqcup \nu}
  \mu_j g_j'(x) = 0,$$
where $\mu_j = 0$ for $j \in \nu$. -/
theorem active_kkt_stationary_iff {f : V → ℝ} {h : ι → V → ℝ}
    {g : κ ⊕ ν → V → ℝ} {x : V}
    {A : V →L[ℝ] ActiveDual ι κ} {mult : ActiveDual ι κ}
    (hA : ∀ d i, A d i = Sum.elim (fun i ↦ fderiv ℝ (h i) x d)
      (fun j ↦ fderiv ℝ (g (.inl j)) x d) i) :
    gradient f x + A.adjoint mult = 0 ↔
      fderiv ℝ f x + ∑ i, mult (.inl i) • fderiv ℝ (h i) x +
        ∑ j : κ ⊕ ν, (Sum.elim (fun k ↦ mult (.inr k)) (fun _ ↦ 0) j) • fderiv ℝ (g j) x = 0 := by
  let L := fderiv ℝ f x + ∑ i, mult (.inl i) • fderiv ℝ (h i) x +
    ∑ j : κ ⊕ ν, (Sum.elim (fun k ↦ mult (.inr k)) (fun _ ↦ 0) j) • fderiv ℝ (g j) x
  have he (d : V) : ⟪gradient f x + A.adjoint mult, d⟫ = L d := by
    simp only [L, inner_add_left, inner_gradient_left, adjoint_inner_left,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hA, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, add_apply, sum_apply, smul_apply, smul_eq_mul,
      zero_mul, Finset.sum_const_zero, add_zero]
    simp only [mul_comm, add_assoc]
  constructor
  · intro hs
    ext d
    rw [← he d, hs, inner_zero_left, zero_apply]
  · intro hs
    apply ext_inner_right ℝ
    intro d
    rw [he, show L = 0 from hs, zero_apply, inner_zero_left]

omit [FiniteDimensional ℝ V] in
/-- **Theorems 3.2.7 and 15.2.2** of [conn2000trust], continuous multiplier recovery. Let $V$ be a
real Hilbert space and $Q$ a topological space. Let $A : Q \to L(V, \mathbb{R}^{\iota \sqcup
\kappa})$ and $G : Q \to V$ be continuous at $q_0$, let $A(q_0)$ be surjective, and let
$G(q_0) + A(q_0)^* m_0 = 0$. Then there is $m : Q \to \mathbb{R}^{\iota \sqcup \kappa}$,
continuous at $q_0$ with $m(q_0) = m_0$, such that for all $q$ near $q_0$ the map $A(q)$ is
surjective and every $b$ with $G(q) + A(q)^* b = 0$ equals $m(q)$.

The conclusion is a uniqueness statement: $m(q)$ is the only possible solution, but it is not
asserted to solve $G(q) + A(q)^* b = 0$. -/
theorem continuous_active_multiplier_recovery
    {Q : Type*} [TopologicalSpace Q] {q₀ : Q}
    {A : Q → V →L[ℝ] ActiveDual ι κ} {G : Q → V} {m₀ : ActiveDual ι κ}
    (hA : ContinuousAt A q₀) (hG : ContinuousAt G q₀) (honto : Function.Surjective (A q₀))
    (hbase : G q₀ + (A q₀).adjoint m₀ = 0) :
    ∃ m : Q → ActiveDual ι κ, ContinuousAt m q₀ ∧ m q₀ = m₀ ∧
      ∀ᶠ q in 𝓝 q₀, Function.Surjective (A q) ∧
        ∀ b : ActiveDual ι κ, G q + (A q).adjoint b = 0 → b = m q := by
  let B (q : Q) := (A q).comp (A q).adjoint
  have hB : ContinuousAt B q₀ :=
    hA.clm_comp (ContinuousLinearMap.adjoint.continuous.continuousAt.comp hA)
  have hadj : Function.Injective (A q₀).adjoint := by
    intro a b hab
    apply ext_inner_right ℝ
    intro v
    obtain ⟨d, rfl⟩ := honto v
    rw [← adjoint_inner_left, hab, adjoint_inner_left]
  have hinj : Function.Injective (B q₀) :=
    (ContinuousLinearMap.self_comp_adjoint_injective_iff (A q₀)).mpr hadj
  have hsurj : Function.Surjective (B q₀) :=
    LinearMap.surjective_of_injective (f := (B q₀).toLinearMap) hinj
  let e := ContinuousLinearEquiv.ofBijective (B q₀) (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj)
  have he : (e : ActiveDual ι κ →L[ℝ] ActiveDual ι κ) = B q₀ :=
    ContinuousLinearEquiv.coe_ofBijective ..
  have hi : (B q₀).IsInvertible := ⟨e, he⟩
  let m (q : Q) := (B q).inverse (-(A q (G q)))
  have hinv : ContinuousAt (ContinuousLinearMap.inverse (R := ℝ)) (B q₀) := by
    rw [← ringInverse_eq_inverse, ← he]
    exact NormedRing.inverse_continuousAt ((ContinuousLinearEquiv.unitsEquiv ℝ _).symm e)
  have hm : ContinuousAt m q₀ :=
    (hinv.comp hB).clm_apply ((hA.clm_apply hG).neg)
  have hrec (q : Q) (hq : (B q).IsInvertible) (b : ActiveDual ι κ)
      (hb : G q + (A q).adjoint b = 0) : b = m q := by
    have hb' : (A q).adjoint b = -G q := eq_neg_of_add_eq_zero_right hb
    have hlin : B q b = -(A q (G q)) := by simp [B, hb', map_neg]
    obtain ⟨E, hE⟩ := hq
    change b = (B q).inverse (-(A q (G q)))
    rw [← hlin, ← hE, inverse_equiv]
    exact (E.symm_apply_apply b).symm
  refine ⟨m, hm, (hrec q₀ hi m₀ hbase).symm, ?_⟩
  filter_upwards [hB.tendsto.eventually hi.eventually_nhds] with q hq
  refine ⟨?_, hrec q hq⟩
  intro b
  obtain ⟨E, hE⟩ := hq
  obtain ⟨v, hv⟩ := E.surjective b
  have heval := congrArg (fun T : ActiveDual ι κ →L[ℝ] ActiveDual ι κ ↦ T v) hE
  exact ⟨(A q).adjoint v, by simpa [B] using heval.symm.trans hv⟩

omit [CompleteSpace V] [FiniteDimensional ℝ V] [Fintype ν] in
/-- **Theorems 3.2.7 and 15.2.2** of [conn2000trust], LICQ from the active Jacobian. Let the
inequality constraints $g_j$ be indexed by $\kappa \sqcup \nu$, let $x$ be feasible with
$g_j(x) < 0$ for $j \in \nu$, and let $A$ have the rows $h_i'(x)$ and $g_j'(x)$ for
$j \in \kappa$. If $A$ is surjective, then $x$ is a regular point: the derivatives $h_i'(x)$ and
$g_j'(x)$ for active $j$ are linearly independent. -/
theorem active_surjective_licq {h : ι → V → ℝ} {g : κ ⊕ ν → V → ℝ}
    {x : V} {A : V →L[ℝ] ActiveDual ι κ}
    (hA : ∀ d i, A d i = Sum.elim (fun i ↦ fderiv ℝ (h i) x d)
      (fun j ↦ fderiv ℝ (g (.inl j)) x d) i)
    (honto : Function.Surjective A) (hneg : ∀ j : ν, g (.inr j) x < 0)
    (hx : x ∈ feasible h g) :
    IsRegularPointIneq h (fun i ↦ fderiv ℝ (h i)) g (fun j ↦ fderiv ℝ (g j)) x := by
  classical
  let row : ι ⊕ κ → V →L[ℝ] ℝ :=
    Sum.elim (fun i ↦ fderiv ℝ (h i) x) (fun j ↦ fderiv ℝ (g (.inl j)) x)
  have hrow (d : V) (i : ι ⊕ κ) : row i d = A d i := by
    rw [hA]
    cases i <;> rfl
  have hli : LinearIndependent ℝ row := Fintype.linearIndependent_iff.mpr fun a ha i ↦ by
    obtain ⟨d, hd⟩ := honto (WithLp.toLp 2 (Pi.single i 1))
    have h := congrArg (fun L : V →L[ℝ] ℝ ↦ L d) ha
    simp only [sum_apply, smul_apply, smul_eq_mul, zero_apply, hrow, hd, PiLp.toLp_apply] at h
    simpa [Pi.single_apply, Finset.sum_ite_eq', eq_comm] using h
  have hl (j : activeSet g x) : ∃ k : κ, (j : κ ⊕ ν) = .inl k := by
    rcases j with ⟨j, hj⟩
    cases j with
    | inl k => exact ⟨k, rfl⟩
    | inr k => exact ((hneg k).ne (mem_activeSet.mp hj)).elim
  let jmap (j : activeSet g x) := (hl j).choose
  have hjmap (j : activeSet g x) : (j : κ ⊕ ν) = .inl (jmap j) := (hl j).choose_spec
  have hjinj : Function.Injective jmap := by
    intro i j hij
    apply Subtype.ext
    rw [hjmap i, hjmap j, hij]
  let emb : ι ⊕ activeSet g x → ι ⊕ κ := Sum.map id jmap
  have hemb : Function.Injective emb := by
    rintro (i | i) (j | j) hij
    · exact congrArg Sum.inl (Sum.inl.inj hij)
    · cases hij
    · cases hij
    · exact congrArg Sum.inr (hjinj (Sum.inr.inj hij))
  refine ⟨hx.1, hx.2, ?_⟩
  convert hli.comp emb hemb using 1
  funext i
  cases i with
  | inl i => rfl
  | inr j =>
    change fderiv ℝ (g (j : κ ⊕ ν)) x = fderiv ℝ (g (.inl (jmap j))) x
    rw [hjmap]

/-- **Theorem 3.2.7** of [conn2000trust], strict-minimizer continuation from an explicit residual.
Let $P$ be a real Banach space and $V$ a finite-dimensional real inner product space, and let
$f(p, \cdot)$, $h_i(p, \cdot)$ and $g_j(p, \cdot)$ be twice continuously differentiable for each
parameter $p$. The inequality constraints are indexed by $\kappa \sqcup \nu$: those in $\kappa$
are active at the base point and those in $\nu$ are inactive. Let $z_0 = (x_0, m_0)$ with
$m_0 = (\lambda_0, \mu_0)$, and let

* $F(p, (x, m)) = (\nabla_x f(p, x) + A(p, x)^* m, \ (h(p, x), g_\kappa(p, x)))$ be continuously
  differentiable at $(p_0, z_0)$ with $F(p_0, z_0) = 0$, where $A(p, x)$ has the rows
  $h_i'(p, x)$ and $g_j'(p, x)$ for $j \in \kappa$,
* $H(p, z)$ satisfy $\langle H(p, z) d, d \rangle = \langle d, \nabla^2_{xx} \mathcal{L}(p, z) d
  \rangle$, and the partial derivative of $F$ in $z$ at $(p_0, z_0)$ be the active KKT block of
  $A(p_0, x_0)$ and $H(p_0, z_0)$,
* $A(p_0, x_0)$ be surjective and $\langle H(p_0, z_0) d, d \rangle > 0$ for nonzero $d$ with
  $A(p_0, x_0) d = 0$,
* $A$, $H$ and $g_\nu$ be continuous at the base, with $g_j(p_0, x_0) < 0$ for $j \in \nu$ and
  strict complementarity $\mu_{0,j} > 0$ for $j \in \kappa$.

Then there are a map $z(p) = (x(p), m(p))$, continuously differentiable at $p_0$ with
$z(p_0) = z_0$, and an open set $X \ni x_0$ such that for all $p$ near $p_0$: $x(p) \in X$; the
active constraints at $x(p)$ are exactly those in $\kappa$; strict complementarity, surjectivity
of $A(p, x(p))$ and positivity of $H$ on its kernel persist; $(x(p), m(p))$ is a KKT point with
$\mu_j = 0$ for $j \in \nu$; $x(p)$ is a strict local minimizer; its KKT multipliers are unique;
and $x(p)$ is the only feasible local minimizer in $X$.

The smooth residual and its block derivative are hypotheses here.
`ConnGouldToint.Chapter03.theorem_3_2_7_joint_smooth_data` constructs them from jointly smooth
data.

**Generalization.** Inequalities may depend on the parameter. The parameter branch is differentiable
at the base, preserves the active set, and the full theorem gives uniqueness among nearby local
minimizers and uniqueness of the multipliers.
-/
theorem theorem_3_2_7_strict_minimizer_branch
    {f : P → V → ℝ} {h : ι → P → V → ℝ} {g : κ ⊕ ν → P → V → ℝ}
    {F : P × (V × ActiveDual ι κ) → V × ActiveDual ι κ}
    {A : P → V → V →L[ℝ] ActiveDual ι κ} {H : P → V × ActiveDual ι κ → V →L[ℝ] V}
    {p₀ : P} {z₀ : V × ActiveDual ι κ}
    (hF : ContDiffAt ℝ 1 F (p₀, z₀)) (hzero : F (p₀, z₀) = 0)
    (hB : (fderiv ℝ F (p₀, z₀)).comp (inr ℝ P (V × ActiveDual ι κ)) =
      activeKKTLinearization (A p₀ z₀.1) (H p₀ z₀))
    (hA₀ : Function.Surjective (A p₀ z₀.1))
    (hH₀ : ∀ d : V, A p₀ z₀.1 d = 0 → d ≠ 0 → 0 < ⟪H p₀ z₀ d, d⟫)
    (hAcont : ContinuousAt (fun w : P × (V × ActiveDual ι κ) ↦ A w.1 w.2.1) (p₀, z₀))
    (hHcont : ContinuousAt (fun w : P × (V × ActiveDual ι κ) ↦ H w.1 w.2) (p₀, z₀))
    (hgcont : ∀ j : ν, ContinuousAt (fun w : P × (V × ActiveDual ι κ) ↦
      g (.inr j) w.1 w.2.1) (p₀, z₀))
    (hstrict : ∀ j : κ, 0 < z₀.2 (.inr j)) (hinactive : ∀ j : ν, g (.inr j) p₀ z₀.1 < 0)
    (hf : ∀ p x, ContDiffAt ℝ 2 (f p) x)
    (hh : ∀ p x i, ContDiffAt ℝ 2 (h i p) x)
    (hg : ∀ p x j, ContDiffAt ℝ 2 (g j p) x)
    (hF₁ : ∀ p z, (F (p, z)).1 = gradient (f p) z.1 + (A p z.1).adjoint z.2)
    (hF₂ : ∀ p z i, (F (p, z)).2 i = Sum.elim (fun i ↦ h i p z.1)
      (fun j ↦ g (.inl j) p z.1) i)
    (hA : ∀ p x d i, A p x d i = Sum.elim (fun i ↦ fderiv ℝ (h i p) x d)
      (fun j ↦ fderiv ℝ (g (.inl j) p) x d) i)
    (hH : ∀ p z d, ⟪H p z d, d⟫ =
      iteratedFDeriv ℝ 2 (kktLagrangian (f p) (fun i ↦ h i p) (fun j ↦ g j p)
        (fun i ↦ z.2 (.inl i)) (Sum.elim (fun j ↦ z.2 (.inr j)) (fun _ ↦ 0))) z.1
        (fun _ ↦ d)) :
    ∃ z : P → V × ActiveDual ι κ, ContDiffAt ℝ 1 z p₀ ∧ z p₀ = z₀ ∧
      ∃ X : Set V, IsOpen X ∧ z₀.1 ∈ X ∧ ∀ᶠ p in 𝓝 p₀,
        (z p).1 ∈ X ∧
        (∀ j : κ ⊕ ν, g j p (z p).1 = 0 ↔ ∃ i : κ, j = .inl i) ∧
        (∀ j : κ, 0 < (z p).2 (.inr j)) ∧
        Function.Surjective (A p (z p).1) ∧
        (∀ d : V, A p (z p).1 d = 0 → d ≠ 0 → 0 < ⟪H p (z p) d, d⟫) ∧
        IsKKTPoint (fderiv ℝ (f p)) (fun i ↦ h i p) (fun i ↦ fderiv ℝ (h i p))
          (fun j ↦ g j p) (fun j ↦ fderiv ℝ (g j p)) (z p).1 (fun i ↦ (z p).2 (.inl i))
          (Sum.elim (fun j ↦ (z p).2 (.inr j)) (fun _ ↦ 0)) ∧
        Optimization.IsStrictLocalMinOn (f p) (feasible (fun i ↦ h i p) (fun j ↦ g j p)) (z p).1 ∧
        (∀ l μ, IsKKTPoint (fderiv ℝ (f p)) (fun i ↦ h i p) (fun i ↦ fderiv ℝ (h i p))
          (fun j ↦ g j p) (fun j ↦ fderiv ℝ (g j p)) (z p).1 l μ →
          l = (fun i ↦ (z p).2 (.inl i)) ∧
          μ = Sum.elim (fun j ↦ (z p).2 (.inr j)) (fun _ ↦ 0)) ∧
        ∀ w ∈ X, w ∈ feasible (fun i ↦ h i p) (fun j ↦ g j p) →
          IsLocalMinOn (f p) (feasible (fun i ↦ h i p) (fun j ↦ g j p)) w → w = (z p).1 := by
  obtain ⟨z, hz, hz₀, U, hU, hpU, -, W, hW, hzW, hbranch⟩ :=
    theorem_3_2_7_implicit_branch hF hzero hB hA₀ hH₀
  have hpair : Tendsto (fun p ↦ (p, z p)) (𝓝 p₀) (𝓝 (p₀, z₀)) := by
    rw [← hz₀]
    exact tendsto_id.prodMk_nhds hz.continuousAt.tendsto
  have hreg : ∀ᶠ p in 𝓝 p₀, Function.Surjective (A p (z p).1) ∧
      ∀ d : V, A p (z p).1 d = 0 → d ≠ 0 → 0 < ⟪H p (z p) d, d⟫ :=
    ((hAcont.prodMk hHcont).tendsto.comp hpair).eventually
      (theorem_3_2_7_activeKKT_conditions_open.mem_nhds ⟨hA₀, hH₀⟩)
  have hpos : ∀ᶠ p in 𝓝 p₀, ∀ j : κ, 0 < (z p).2 (.inr j) := by
    apply eventually_all.mpr
    intro j
    let proj : ActiveDual ι κ →L[ℝ] ℝ := PiLp.proj _ _ (.inr j)
    have hcont : Continuous (fun w : V × ActiveDual ι κ ↦ w.2 (.inr j)) :=
      proj.continuous.comp continuous_snd
    exact ((hcont.tendsto _).comp hz.continuousAt.tendsto).eventually
      (Ioi_mem_nhds (show 0 < (z p₀).2 (.inr j) by rw [hz₀]; exact hstrict j))
  have hneg : ∀ᶠ p in 𝓝 p₀, ∀ j : ν, g (.inr j) p (z p).1 < 0 :=
    eventually_all.mpr fun j ↦
      ((hgcont j).tendsto.comp hpair).eventually (Iio_mem_nhds (hinactive j))
  let q₀ : P × V := (p₀, z₀.1)
  let lift (q : P × V) := (q.1, (q.2, z₀.2))
  have hlift : ContinuousAt lift q₀ :=
    continuous_fst.continuousAt.prodMk (continuous_snd.continuousAt.prodMk continuousAt_const)
  have hlift₀ : lift q₀ = (p₀, z₀) := rfl
  have hA' : ContinuousAt (fun q : P × V ↦ A q.1 q.2) q₀ := by
    exact (hlift₀.symm ▸ hAcont).comp hlift
  have hG' : ContinuousAt (fun q : P × V ↦ gradient (f q.1) q.2) q₀ := by
    have hf₁ : ContinuousAt (fun q : P × V ↦ (F (lift q)).1) q₀ :=
      continuous_fst.continuousAt.comp ((hlift₀.symm ▸ hF.continuousAt).comp hlift)
    have hadd : ContinuousAt (fun q : P × V ↦ (A q.1 q.2).adjoint z₀.2) q₀ :=
      (ContinuousLinearMap.adjoint.continuous.continuousAt.comp hA').clm_apply continuousAt_const
    convert hf₁.sub hadd using 1
    funext q
    change gradient (f q.1) q.2 = (F (q.1, (q.2, z₀.2))).1 - (A q.1 q.2).adjoint z₀.2
    rw [hF₁, add_sub_cancel_right]
  have hbase : gradient (f p₀) z₀.1 + (A p₀ z₀.1).adjoint z₀.2 = 0 := by
    simpa [hF₁] using congrArg Prod.fst hzero
  obtain ⟨m, hm, hm₀, hmrec⟩ := continuous_active_multiplier_recovery hA' hG' hA₀ hbase
  have hnearW : ∀ᶠ q : P × V in 𝓝 q₀, (q.2, m q) ∈ W := by
    apply (continuous_snd.continuousAt.prodMk hm).tendsto.eventually
    apply hW.mem_nhds
    change (z₀.1, m q₀) ∈ W
    rwa [hm₀]
  have hnearpos : ∀ᶠ q : P × V in 𝓝 q₀, ∀ j : κ, 0 < m q (.inr j) := by
    apply eventually_all.mpr
    intro j
    let proj : ActiveDual ι κ →L[ℝ] ℝ := PiLp.proj _ _ (.inr j)
    apply (proj.continuous.continuousAt.comp hm).tendsto.eventually
    apply Ioi_mem_nhds
    change 0 < m q₀ (.inr j)
    rw [hm₀]
    exact hstrict j
  have hnearneg : ∀ᶠ q : P × V in 𝓝 q₀, ∀ j : ν, g (.inr j) q.1 q.2 < 0 := by
    apply eventually_all.mpr
    intro j
    exact ((hlift₀.symm ▸ hgcont j).comp hlift).tendsto.eventually (Iio_mem_nhds (hinactive j))
  have hnear := hnearW.and (hnearpos.and (hnearneg.and hmrec))
  change ∀ᶠ q in 𝓝 (p₀, z₀.1), _ at hnear
  rw [nhds_prod_eq] at hnear
  obtain ⟨U', hU', X₀, hX₀, hrectangle⟩ := Filter.mem_prod_iff.mp hnear
  obtain ⟨X, hXX₀, hX, hxX⟩ := mem_nhds_iff.mp hX₀
  have hx : ∀ᶠ p in 𝓝 p₀, (z p).1 ∈ X := by
    apply (continuous_fst.continuousAt.comp hz.continuousAt).tendsto.eventually
    change ∀ᶠ y in 𝓝 (z p₀).1, y ∈ X
    rw [hz₀]
    exact hX.mem_nhds hxX
  refine ⟨z, hz, hz₀, X, hX, hxX, ?_⟩
  filter_upwards [hU.mem_nhds hpU, hreg, hpos, hneg, hU', hx] with p hp hpreg hppos hpneg hp' hpx
  have hFz : F (p, z p) = 0 := ((hbranch p hp).2 _ (hbranch p hp).1).mpr rfl
  have he (i : ι) : h i p (z p).1 = 0 := by
    simpa [hF₂] using congrArg (fun w : V × ActiveDual ι κ ↦ w.2 (.inl i)) hFz
  have hi (j : κ) : g (.inl j) p (z p).1 = 0 := by
    simpa [hF₂] using congrArg (fun w : V × ActiveDual ι κ ↦ w.2 (.inr j)) hFz
  have hstat : gradient (f p) (z p).1 + (A p (z p).1).adjoint (z p).2 = 0 := by
    simpa [hF₁] using congrArg Prod.fst hFz
  let μ : κ ⊕ ν → ℝ := Sum.elim (fun j ↦ (z p).2 (.inr j)) (fun _ ↦ 0)
  have hkkt : IsKKTPoint (fderiv ℝ (f p)) (fun i ↦ h i p) (fun i ↦ fderiv ℝ (h i p))
      (fun j ↦ g j p) (fun j ↦ fderiv ℝ (g j p)) (z p).1 (fun i ↦ (z p).2 (.inl i)) μ := by
    refine ⟨he, ?_, (active_kkt_stationary_iff (hA p _)).mp hstat, ?_, ?_⟩
    · intro j
      cases j with
      | inl j => exact (hi j).le
      | inr j => exact (hpneg j).le
    · intro j
      cases j with
      | inl j => exact (hppos j).le
      | inr j => exact le_rfl
    · intro j
      cases j with
      | inl j => rw [hi, mul_zero]
      | inr j => exact zero_mul _
  refine ⟨hpx, ?_, hppos, hpreg.1, hpreg.2, hkkt,
    theorem_3_2_6 (hf p _) (hh p _) (hg p _) hkkt ?_, ?_, ?_⟩
  · intro j
    cases j with
    | inl j => simp [hi]
    | inr j => simp [(hpneg j).ne]
  · intro d hd hdne
    have hker : A p (z p).1 d = 0 := by
      ext i
      rw [hA]
      cases i with
      | inl i => exact hd.1 i
      | inr j => exact hd.2.1 (.inl j) (hi j) (hppos j)
    rw [← hH]
    exact hpreg.2 d hker hdne
  · intro l' μ' hkkt'
    have hin (j : ν) : μ' (.inr j) = 0 :=
      (mul_eq_zero.mp (hkkt'.complementary (.inr j))).resolve_right (hpneg j).ne
    let mult' : ActiveDual ι κ := WithLp.toLp 2 (Sum.elim l' (fun j ↦ μ' (.inl j)))
    have hμ' : Sum.elim (fun j ↦ mult' (.inr j)) (fun _ ↦ 0) = μ' := by
      funext j
      cases j with
      | inl j => rfl
      | inr j => exact (hin j).symm
    have hstat' : gradient (f p) (z p).1 + (A p (z p).1).adjoint mult' = 0 := by
      apply (active_kkt_stationary_iff (f := f p) (h := fun i ↦ h i p)
        (g := fun j ↦ g j p) (hA p _)).mpr
      rw [hμ']
      exact hkkt'.stationary
    have heq : (A p (z p).1).adjoint mult' = (A p (z p).1).adjoint (z p).2 :=
      add_left_cancel (hstat'.trans hstat.symm)
    have hmult : mult' = (z p).2 := by
      apply ext_inner_right ℝ
      intro y
      obtain ⟨d, rfl⟩ := hpreg.1 y
      rw [← adjoint_inner_left, heq, adjoint_inner_left]
    constructor
    · exact funext fun i ↦ congrArg (fun mult : ActiveDual ι κ ↦ mult (.inl i)) hmult
    · rw [← hμ', hmult]
  · intro w hw hwfeas hwmin
    have hnearw := hrectangle (show (p, w) ∈ U' ×ˢ X₀ from ⟨hp', hXX₀ hw⟩)
    obtain ⟨hwW, hwpos, hwneg, hwonto, hwrec⟩ := hnearw
    have hlicq := active_surjective_licq (h := fun i ↦ h i p) (g := fun j ↦ g j p)
      (hA p w) hwonto hwneg hwfeas
    obtain ⟨l', μ', hkkt'⟩ := exists_kkt_of_isLocalMinOn hlicq hwmin
      ((hf p w).differentiableAt (by norm_num)).hasFDerivAt
      (fun i ↦ (hh p w i).hasStrictFDerivAt (by norm_num))
      (fun j ↦ (hg p w j).hasStrictFDerivAt (by norm_num))
    have hout (j : ν) : μ' (.inr j) = 0 :=
      (mul_eq_zero.mp (hkkt'.complementary (.inr j))).resolve_right (hwneg j).ne
    let mult' : ActiveDual ι κ := WithLp.toLp 2 (Sum.elim l' (fun j ↦ μ' (.inl j)))
    have hμ' : Sum.elim (fun j ↦ mult' (.inr j)) (fun _ ↦ 0) = μ' := by
      funext j
      cases j with
      | inl j => rfl
      | inr j => exact (hout j).symm
    have hstationary : gradient (f p) w + (A p w).adjoint mult' = 0 := by
      apply (active_kkt_stationary_iff (f := f p) (h := fun i ↦ h i p)
        (g := fun j ↦ g j p) (hA p w)).mpr
      rw [hμ']
      exact hkkt'.stationary
    have hmult : mult' = m (p, w) := hwrec mult' hstationary
    have hactive (j : κ) : g (.inl j) p w = 0 := by
      have hμpos : 0 < μ' (.inl j) := by
        change 0 < mult' (.inr j)
        rw [hmult]
        exact hwpos j
      exact (mul_eq_zero.mp (hkkt'.complementary (.inl j))).resolve_left hμpos.ne'
    have hFzero : F (p, (w, m (p, w))) = 0 := by
      apply Prod.ext
      · rw [hF₁, ← hmult]
        exact hstationary
      · ext i
        rw [hF₂]
        cases i with
        | inl i => exact hkkt'.feasible_eq i
        | inr j => exact hactive j
    exact congrArg Prod.fst (((hbranch p hp).2 _ hwW).mp hFzero)


omit [FiniteDimensional ℝ V] [CompleteSpace P] in
/-- **Theorem 3.2.7** of [conn2000trust], smooth data. Let $P$ be a real normed space and $V$ a real
Hilbert space, and let $f$, $h_i$ and $g_j$ be twice continuously differentiable jointly in
$(p, x)$. Then there are the active KKT residual $F$, the active Jacobian $A$ and the Hessian
operator $H$ of `ConnGouldToint.Chapter03.theorem_3_2_7_strict_minimizer_branch`, with $F$
continuously differentiable, $A$ and $H$ continuous, and the partial derivative of $F$ in $z$
equal to the active KKT block of $A$ and $H$ at every point. -/
theorem theorem_3_2_7_joint_smooth_data
    {f : P → V → ℝ} {h : ι → P → V → ℝ} {g : κ ⊕ ν → P → V → ℝ}
    (hf : ContDiff ℝ 2 (Function.uncurry f))
    (hh : ∀ i, ContDiff ℝ 2 (Function.uncurry (h i)))
    (hg : ∀ j, ContDiff ℝ 2 (Function.uncurry (g j))) :
    ∃ (F : P × (V × ActiveDual ι κ) → V × ActiveDual ι κ)
      (A : P → V → V →L[ℝ] ActiveDual ι κ)
      (H : P → V × ActiveDual ι κ → V →L[ℝ] V),
      ContDiff ℝ 1 F ∧
      Continuous (fun w : P × (V × ActiveDual ι κ) ↦ A w.1 w.2.1) ∧
      Continuous (Function.uncurry H) ∧
      (∀ p z, (fderiv ℝ F (p, z)).comp (inr ℝ P (V × ActiveDual ι κ)) =
        activeKKTLinearization (A p z.1) (H p z)) ∧
      (∀ p z, (F (p, z)).1 = gradient (f p) z.1 + (A p z.1).adjoint z.2) ∧
      (∀ p z i, (F (p, z)).2 i = Sum.elim (fun i ↦ h i p z.1)
        (fun j ↦ g (.inl j) p z.1) i) ∧
      (∀ p x d i, A p x d i = Sum.elim (fun i ↦ fderiv ℝ (h i p) x d)
        (fun j ↦ fderiv ℝ (g (.inl j) p) x d) i) ∧
      ∀ p z d, ⟪H p z d, d⟫ =
        iteratedFDeriv ℝ 2 (kktLagrangian (f p) (fun i ↦ h i p) (fun j ↦ g j p)
          (fun i ↦ z.2 (.inl i)) (Sum.elim (fun j ↦ z.2 (.inr j)) (fun _ ↦ 0))) z.1
          (fun _ ↦ d) := by
  let C (p : P) (x : V) : ActiveDual ι κ :=
    WithLp.toLp 2 (Sum.elim (fun i ↦ h i p x) (fun j ↦ g (.inl j) p x))
  have hC : ContDiff ℝ 2 (Function.uncurry C) := contDiff_piLp' 2 fun i ↦ by
    cases i with
    | inl i => exact hh i
    | inr j => exact hg (.inl j)
  let A (p : P) (x : V) := fderiv ℝ (C p) x
  have hA : ContDiff ℝ 1 (Function.uncurry A) :=
    (hC.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)).fderiv
      (g := Prod.snd) contDiff_snd (by norm_num)
  let Q := P × ActiveDual ι κ
  let L (q : Q) := kktLagrangian (f q.1) (fun i ↦ h i q.1) (fun j ↦ g j q.1)
    (fun i ↦ q.2 (.inl i)) (Sum.elim (fun j ↦ q.2 (.inr j)) (fun _ ↦ 0))
  let coord (i : ι ⊕ κ) : ActiveDual ι κ →L[ℝ] ℝ :=
    PiLp.proj 2 (fun _ : ι ⊕ κ ↦ ℝ) i
  have hL : ContDiff ℝ 2 (Function.uncurry L) := by
    have hpr : ContDiff ℝ 2 (fun w : Q × V ↦ (w.1.1, w.2)) :=
      (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd
    change ContDiff ℝ 2 (fun w : Q × V ↦ L w.1 w.2)
    simp only [L, kktLagrangian_apply]
    apply ((hf.comp hpr).add ?_).add ?_
    · exact ContDiff.sum fun i _ ↦
        ((coord (.inl i)).contDiff.comp (contDiff_snd.comp contDiff_fst)).mul
          ((hh i).comp hpr)
    · refine ContDiff.sum fun j _ ↦ ?_
      cases j with
      | inl j =>
        exact ((coord (.inr j)).contDiff.comp (contDiff_snd.comp contDiff_fst)).mul
          ((hg (.inl j)).comp hpr)
      | inr j => exact contDiff_const.mul ((hg (.inr j)).comp hpr)
  let G (q : Q) (x : V) := gradient (L q) x
  have hG : ContDiff ℝ 1 (Function.uncurry G) :=
    (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.contDiff.comp
      ((hL.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)).fderiv
        (g := Prod.snd) contDiff_snd (by norm_num))
  let H (p : P) (z : V × ActiveDual ι κ) := fderiv ℝ (G (p, z.2)) z.1
  have hswap : ContDiff ℝ 1 (fun w : P × (V × ActiveDual ι κ) ↦ ((w.1, w.2.2), w.2.1)) :=
    (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)).prodMk
      (contDiff_fst.comp contDiff_snd)
  let F (w : P × (V × ActiveDual ι κ)) := (G (w.1, w.2.2) w.2.1, C w.1 w.2.1)
  have hF : ContDiff ℝ 1 F := (hG.comp hswap).prodMk
    ((hC.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp
      (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)))
  have hrow (p : P) (x d : V) (i : ι ⊕ κ) :
      A p x d i = Sum.elim (fun i ↦ fderiv ℝ (h i p) x d)
        (fun j ↦ fderiv ℝ (g (.inl j) p) x d) i := by
    have hc : DifferentiableAt ℝ (C p) x :=
      ((hC.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)) x
    let proj : ActiveDual ι κ →L[ℝ] ℝ := PiLp.proj 2 (fun _ : ι ⊕ κ ↦ ℝ) i
    have hp := (proj.hasFDerivAt.comp x hc.hasFDerivAt).fderiv
    have he := congrArg (fun T : V →L[ℝ] ℝ ↦ T d) hp
    cases i <;> exact he.symm
  have hstation (p : P) (z : V × ActiveDual ι κ) :
      (F (p, z)).1 = gradient (f p) z.1 + (A p z.1).adjoint z.2 := by
    have diff {u : P → V → ℝ} (hu : ContDiff ℝ 2 (Function.uncurry u)) :
        DifferentiableAt ℝ (u p) z.1 :=
      (hu.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num) _
    apply ext_inner_right ℝ
    intro d
    change ⟪gradient (L (p, z.2)) z.1, d⟫ = _
    rw [inner_gradient_left, (hasFDerivAt_kktLagrangian (diff hf).hasFDerivAt
      (fun i ↦ (diff (hh i)).hasFDerivAt) (fun j ↦ (diff (hg j)).hasFDerivAt)).fderiv]
    simp only [inner_add_left, inner_gradient_left, adjoint_inner_left,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hrow, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, add_apply, sum_apply, smul_apply, smul_eq_mul,
      zero_mul, Finset.sum_const_zero, add_zero]
    simp only [mul_comm, add_assoc]
  have hHp : ContDiff ℝ 0 (fun w : Q × V ↦ fderiv ℝ (G w.1) w.2) :=
    (hG.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)).fderiv
      (g := Prod.snd) contDiff_snd (by norm_num)
  refine ⟨F, A, H, hF,
    (hA.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))).continuous,
    (hHp.comp (hswap.of_le zero_le)).continuous, ?_, hstation, fun _ _ _ ↦ rfl, hrow, ?_⟩
  · intro p z
    let D := (fderiv ℝ F (p, z)).comp (inr ℝ P (V × ActiveDual ι κ))
    have hDF : HasFDerivAt F (fderiv ℝ F (p, z)) (p, z) :=
      (hF.differentiable one_ne_zero _).hasFDerivAt
    have hd₁ : HasFDerivAt (fun x : V ↦ F (p, (x, z.2)))
        (D.comp (inl ℝ V (ActiveDual ι κ))) z.1 := by
      have he : HasFDerivAt (fun x : V ↦ (p, (x, z.2)))
          ((0 : V →L[ℝ] P).prod ((ContinuousLinearMap.id ℝ V).prod 0)) z.1 :=
        (hasFDerivAt_const p z.1).prodMk
          ((hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1))
      convert hDF.comp z.1 he using 1
      · rfl
      · apply ContinuousLinearMap.ext
        intro d
        simp [D]
    have hd₂ : HasFDerivAt (fun m : ActiveDual ι κ ↦ F (p, (z.1, m)))
        (D.comp (inr ℝ V (ActiveDual ι κ))) z.2 := by
      have he : HasFDerivAt (fun m : ActiveDual ι κ ↦ (p, (z.1, m)))
          ((0 : ActiveDual ι κ →L[ℝ] P).prod
            (ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℝ (ActiveDual ι κ)))) z.2 :=
        (hasFDerivAt_const p z.2).prodMk
          ((hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2))
      convert hDF.comp z.2 he using 1
      · rfl
      · apply ContinuousLinearMap.ext
        intro d
        simp [D]
    have hGdiff : DifferentiableAt ℝ (G (p, z.2)) z.1 :=
      ((hG.comp (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero) z.1
    have hCdiff : DifferentiableAt ℝ (C p) z.1 :=
      ((hC.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)) z.1
    have hd₁' : HasFDerivAt (fun x : V ↦ F (p, (x, z.2)))
        ((H p z).prod (A p z.1)) z.1 :=
      hGdiff.hasFDerivAt.prodMk hCdiff.hasFDerivAt
    have hd₂' : HasFDerivAt (fun m : ActiveDual ι κ ↦ F (p, (z.1, m)))
        (((A p z.1).adjoint).prod 0) z.2 := by
      have hlin := ((hasFDerivAt_const (gradient (f p) z.1) z.2).add
        (A p z.1).adjoint.hasFDerivAt).prodMk (hasFDerivAt_const (C p z.1) z.2)
      rw [zero_add] at hlin
      convert hlin using 1
      funext m
      exact Prod.ext (hstation p (z.1, m)) rfl
    have he₁ := hd₁.unique hd₁'
    have he₂ := hd₂.unique hd₂'
    apply ContinuousLinearMap.ext
    intro v
    change D v = _
    calc
      D v = D (v.1, 0) + D (0, v.2) := by rw [← map_add]; simp
      _ = _ := by
        simpa using congrArg₂ (· + ·)
          (congrArg (fun T : V →L[ℝ] (V × ActiveDual ι κ) ↦ T v.1) he₁)
          (congrArg (fun T : ActiveDual ι κ →L[ℝ] (V × ActiveDual ι κ) ↦ T v.2) he₂)
  · intro p z d
    let q : Q := (p, z.2)
    let e := (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv
    have hd : DifferentiableAt ℝ (fderiv ℝ (L q)) z.1 :=
      (((hL.comp (contDiff_const.prodMk contDiff_id)).fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable one_ne_zero) _
    have he := (e.hasFDerivAt.comp z.1 hd.hasFDerivAt).fderiv
    change ⟪fderiv ℝ (G q) z.1 d, d⟫ = iteratedFDeriv ℝ 2 (L q) z.1 (fun _ ↦ d)
    rw [show fderiv ℝ (G q) z.1 = e.toContinuousLinearMap.comp
      (fderiv ℝ (fderiv ℝ (L q)) z.1) from he, comp_apply, iteratedFDeriv_two_apply]
    exact InnerProductSpace.toDual_symm_apply

/-- **Theorem 3.2.7** of [conn2000trust]. Let $P$ be a real Banach space and $V$ a
finite-dimensional real inner product space, and let $f$, $h_i$ and $g_j$ be twice continuously
differentiable jointly in the parameter $p$ and the variable $x$. The inequality constraints are
indexed by $\kappa \sqcup \nu$. Let $z_0 = (x_0, (\lambda_0, \mu_0))$, and suppose that at $p_0$

* $(x_0, \lambda_0, \mu)$ is a KKT point, where $\mu_j = \mu_{0,j} > 0$ for $j \in \kappa$ and
  $\mu_j = 0$ for $j \in \nu$,
* $g_j(p_0, x_0) < 0$ for $j \in \nu$,
* the rows $h_i'(p_0, x_0)$ and $g_j'(p_0, x_0)$ for $j \in \kappa$ map $V$ onto
  $\mathbb{R}^{\iota \sqcup \kappa}$, and
* $\langle d, \nabla^2_{xx} \mathcal{L}(p_0, z_0) d \rangle > 0$ for every nonzero $d$ in the
  kernel of these rows.

Then there are a map $z(p) = (x(p), (\lambda(p), \mu(p)))$, continuously differentiable at $p_0$
with $z(p_0) = z_0$, and an open set $X \ni x_0$ such that for all $p$ near $p_0$: $x(p) \in X$;
the active constraints at $x(p)$ are exactly those in $\kappa$; strict complementarity, the rank
condition and the positivity of the Lagrangian Hessian on the kernel persist; $x(p)$ is a KKT
point with these multipliers; $x(p)$ is a strict local minimizer; its KKT multipliers are
unique; and $x(p)$ is the only feasible local minimizer in $X$.

**Generalization.** The displayed problem (3.2.15) has parameter-independent inequality
constraints, and the theorem states uniqueness among strict local minimizers. The statement
allows parameter-dependent inequalities and gives uniqueness among all nearby local minimizers.
It also gives differentiability at $p_0$, as in the variant mentioned in the source notes.

The active Jacobian is described by its rows. The proof applies
`ConnGouldToint.Chapter03.theorem_3_2_7_strict_minimizer_branch` to the data of
`ConnGouldToint.Chapter03.theorem_3_2_7_joint_smooth_data`.

**Generalization.** Inequalities may depend on the parameter. The parameter branch is differentiable
at the base, preserves the active set, and the full theorem gives uniqueness among nearby local
minimizers and uniqueness of the multipliers.
-/
theorem theorem_3_2_7
    {f : P → V → ℝ} {h : ι → P → V → ℝ} {g : κ ⊕ ν → P → V → ℝ}
    {p₀ : P} {z₀ : V × ActiveDual ι κ}
    (hf : ContDiff ℝ 2 (Function.uncurry f))
    (hh : ∀ i, ContDiff ℝ 2 (Function.uncurry (h i)))
    (hg : ∀ j, ContDiff ℝ 2 (Function.uncurry (g j)))
    (hkkt : IsKKTPoint (fderiv ℝ (f p₀)) (fun i ↦ h i p₀) (fun i ↦ fderiv ℝ (h i p₀))
      (fun j ↦ g j p₀) (fun j ↦ fderiv ℝ (g j p₀)) z₀.1 (fun i ↦ z₀.2 (.inl i))
      (Sum.elim (fun j ↦ z₀.2 (.inr j)) (fun _ ↦ 0)))
    (hstrict : ∀ j : κ, 0 < z₀.2 (.inr j))
    (hinactive : ∀ j : ν, g (.inr j) p₀ z₀.1 < 0)
    (hRank : ∀ b : ActiveDual ι κ, ∃ d : V, ∀ i,
      Sum.elim (fun i ↦ fderiv ℝ (h i p₀) z₀.1 d)
        (fun j ↦ fderiv ℝ (g (.inl j) p₀) z₀.1 d) i = b i)
    (hpos : ∀ d : V, (∀ i, fderiv ℝ (h i p₀) z₀.1 d = 0) →
      (∀ j : κ, fderiv ℝ (g (.inl j) p₀) z₀.1 d = 0) → d ≠ 0 →
      0 < iteratedFDeriv ℝ 2 (kktLagrangian (f p₀) (fun i ↦ h i p₀) (fun j ↦ g j p₀)
        (fun i ↦ z₀.2 (.inl i)) (Sum.elim (fun j ↦ z₀.2 (.inr j)) (fun _ ↦ 0))) z₀.1
        (fun _ ↦ d)) :
    ∃ z : P → V × ActiveDual ι κ, ContDiffAt ℝ 1 z p₀ ∧ z p₀ = z₀ ∧
      ∃ X : Set V, IsOpen X ∧ z₀.1 ∈ X ∧ ∀ᶠ p in 𝓝 p₀,
        (z p).1 ∈ X ∧
        (∀ j : κ ⊕ ν, g j p (z p).1 = 0 ↔ ∃ i : κ, j = .inl i) ∧
        (∀ j : κ, 0 < (z p).2 (.inr j)) ∧
        (∀ b : ActiveDual ι κ, ∃ d : V, ∀ i,
          Sum.elim (fun i ↦ fderiv ℝ (h i p) (z p).1 d)
            (fun j ↦ fderiv ℝ (g (.inl j) p) (z p).1 d) i = b i) ∧
        (∀ d : V, (∀ i, fderiv ℝ (h i p) (z p).1 d = 0) →
          (∀ j : κ, fderiv ℝ (g (.inl j) p) (z p).1 d = 0) → d ≠ 0 →
          0 < iteratedFDeriv ℝ 2 (kktLagrangian (f p) (fun i ↦ h i p) (fun j ↦ g j p)
            (fun i ↦ (z p).2 (.inl i)) (Sum.elim (fun j ↦ (z p).2 (.inr j)) (fun _ ↦ 0)))
            (z p).1 (fun _ ↦ d)) ∧
        IsKKTPoint (fderiv ℝ (f p)) (fun i ↦ h i p) (fun i ↦ fderiv ℝ (h i p))
          (fun j ↦ g j p) (fun j ↦ fderiv ℝ (g j p)) (z p).1 (fun i ↦ (z p).2 (.inl i))
          (Sum.elim (fun j ↦ (z p).2 (.inr j)) (fun _ ↦ 0)) ∧
        Optimization.IsStrictLocalMinOn (f p) (feasible (fun i ↦ h i p) (fun j ↦ g j p)) (z p).1 ∧
        (∀ l μ, IsKKTPoint (fderiv ℝ (f p)) (fun i ↦ h i p) (fun i ↦ fderiv ℝ (h i p))
          (fun j ↦ g j p) (fun j ↦ fderiv ℝ (g j p)) (z p).1 l μ →
          l = (fun i ↦ (z p).2 (.inl i)) ∧
          μ = Sum.elim (fun j ↦ (z p).2 (.inr j)) (fun _ ↦ 0)) ∧
        ∀ w ∈ X, w ∈ feasible (fun i ↦ h i p) (fun j ↦ g j p) →
          IsLocalMinOn (f p) (feasible (fun i ↦ h i p) (fun j ↦ g j p)) w → w = (z p).1 := by
  obtain ⟨F, A, H, hF, hAcont, hHcont, hB, hstat, hfeas, hrow, hH⟩ :=
    theorem_3_2_7_joint_smooth_data hf hh hg
  have hzero : F (p₀, z₀) = 0 := by
    apply Prod.ext
    · rw [hstat]
      exact (active_kkt_stationary_iff (hrow p₀ z₀.1)).mpr hkkt.stationary
    · ext i
      rw [hfeas]
      cases i with
      | inl i => exact hkkt.feasible_eq i
      | inr j => exact (mul_eq_zero.mp (hkkt.complementary (.inl j))).resolve_left (hstrict j).ne'
  have hA₀ : Function.Surjective (A p₀ z₀.1) := by
    intro b
    obtain ⟨d, hd⟩ := hRank b
    exact ⟨d, by ext i; rw [hrow]; exact hd i⟩
  have hH₀ (d : V) (hd : A p₀ z₀.1 d = 0) (hne : d ≠ 0) : 0 < ⟪H p₀ z₀ d, d⟫ := by
    rw [hH]
    apply hpos d _ _ hne
    · intro i
      simpa only [hrow, Sum.elim_inl, PiLp.zero_apply] using
        congrArg (fun m : ActiveDual ι κ ↦ m (.inl i)) hd
    · intro j
      simpa only [hrow, Sum.elim_inr, PiLp.zero_apply] using
        congrArg (fun m : ActiveDual ι κ ↦ m (.inr j)) hd
  have slice {u : P → V → ℝ} (hu : ContDiff ℝ 2 (Function.uncurry u)) (p : P) (x : V) :
      ContDiffAt ℝ 2 (u p) x :=
    (hu.comp (contDiff_const.prodMk contDiff_id)).contDiffAt
  have inactiveCont (j : ν) :
      ContinuousAt (fun w : P × (V × ActiveDual ι κ) ↦ g (.inr j) w.1 w.2.1) (p₀, z₀) :=
    ((hg (.inr j)).continuous.comp (continuous_fst.prodMk
      (continuous_fst.comp continuous_snd))).continuousAt
  obtain ⟨z, hz, hz₀, X, hX, hx₀, hzX⟩ := theorem_3_2_7_strict_minimizer_branch
    hF.contDiffAt hzero (hB p₀ z₀) hA₀ hH₀ hAcont.continuousAt hHcont.continuousAt
    inactiveCont hstrict hinactive (slice hf) (fun p x i ↦ slice (hh i) p x)
    (fun p x j ↦ slice (hg j) p x) hstat hfeas hrow hH
  refine ⟨z, hz, hz₀, X, hX, hx₀, hzX.mono fun p ⟨hmem, hact, hstr, hsurj, hpd, hrest⟩ ↦
    ⟨hmem, hact, hstr, ?_, ?_, hrest⟩⟩
  · intro b
    obtain ⟨d, hd⟩ := hsurj b
    exact ⟨d, fun i ↦ (hrow p (z p).1 d i).symm.trans
      (congrArg (fun m : ActiveDual ι κ ↦ m i) hd)⟩
  · intro d hd₁ hd₂ hne
    rw [← hH]
    apply hpd d _ hne
    ext i
    rw [hrow]
    cases i with
    | inl i => exact hd₁ i
    | inr j => exact hd₂ j

end MixedKKTSensitivity

section ParametricMinimum

variable {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]

private theorem eventually_feasible_prod_subset {C : P → Set X} {p : P}
    (hC : IsCompact (C p)) (hU : UpperHemicontinuousAt C p)
    {S : Set (X × P)} (hS : IsOpen S) (hmem : ∀ x ∈ C p, (x, p) ∈ S) :
    ∀ᶠ q in 𝓝 p, ∀ x ∈ C q, (x, q) ∈ S := by
  have hprod : S ∈ (𝓝ˢ (C p)) ×ˢ 𝓝 p := hC.mem_nhdsSet_prod_of_forall fun x hx ↦ by
    rw [← nhds_prod_eq]
    exact hS.mem_nhds (hmem x hx)
  obtain ⟨U, hUn, V, hV, hsub⟩ := Filter.mem_prod_iff.mp hprod
  obtain ⟨U', hU'o, hCU', hU'U⟩ := mem_nhdsSet_iff_exists.mp hUn
  filter_upwards [hU.forall_isOpen U' hU'o hCU', hV] with q hq hqV
  exact fun x hx ↦ hsub ⟨hU'U (hq hx), hqV⟩

/-- **Theorem 3.2.8** of [conn2000trust]. Let $X$ and $P$ be topological spaces, let $C : P \to 2^X$
be upper and lower hemicontinuous with nonempty compact values, and let
$f : X \times P \to \mathbb{R}$ be continuous. Let
$$v(p) = \min_{x \in C(p)} f(x, p), \qquad S(p) = \{x \in C(p) : f(x, p) = v(p)\}.$$
Then $v$ is continuous, $S$ is upper hemicontinuous, and $S(p)$ is nonempty for every $p$.

**Correction.** The statement assumes nonempty compact feasible sets, and it asserts upper
hemicontinuity of $S$ only. The minimizers need not be lower hemicontinuous, even for a linear
objective on a fixed compact convex set
(`ConnGouldToint.Chapter03.theorem_3_2_8_counterexample`), and without compactness $v$ need not
be continuous (`ConnGouldToint.Chapter03.theorem_3_2_8_noncompact_value_counterexample`).

**Generalization.** The book assumes convex feasible sets, a convex objective in the decision
variable, and Euclidean spaces. Compactness and hemicontinuity suffice for the comparison of
minimum values in arbitrary topological spaces.

The value $v(p)$ is `sInf` of the image of $C(p)$.

**Correction.** Compact nonempty continuous feasible values yield a continuous optimum, attained
minimizers and upper hemicontinuity even without convexity. The examples show failure of lower
hemicontinuity of minimizers and failure of value continuity without compactness.
-/
theorem theorem_3_2_8 {C : P → Set X} {f : X × P → ℝ}
    (hC : ∀ p, IsCompact (C p)) (hne : ∀ p, (C p).Nonempty)
    (hupper : UpperHemicontinuous C) (hlower : LowerHemicontinuous C) (hf : Continuous f) :
    let value := fun p ↦ sInf ((fun x ↦ f (x, p)) '' C p)
    let sol := fun p ↦ {x ∈ C p | f (x, p) = value p}
    Continuous value ∧ UpperHemicontinuous sol ∧ ∀ p, (sol p).Nonempty := by
  let value (p : P) := sInf ((fun x ↦ f (x, p)) '' C p)
  let sol (p : P) := {x ∈ C p | f (x, p) = value p}
  have hmin (p : P) : ∃ x ∈ C p, f (x, p) = value p ∧ ∀ y ∈ C p, f (x, p) ≤ f (y, p) := by
    obtain ⟨x, hx, hm⟩ := (hC p).exists_isMinOn (hne p)
      (hf.comp (continuous_id.prodMk continuous_const)).continuousOn
    refine ⟨x, hx, ?_, fun y hy ↦ hm hy⟩
    exact (show IsLeast ((fun y ↦ f (y, p)) '' C p) (f (x, p)) from
      ⟨mem_image_of_mem _ hx, by rintro _ ⟨y, hy, rfl⟩; exact hm hy⟩).csInf_eq.symm
  have hle (p : P) (x : X) (hx : x ∈ C p) : value p ≤ f (x, p) := by
    obtain ⟨z, -, hz, h⟩ := hmin p
    rw [← hz]
    exact h x hx
  have hvalue : Continuous value := by
    rw [continuous_iff_continuousAt]
    intro p
    apply tendsto_order.mpr
    constructor
    · intro b hb
      have h := eventually_feasible_prod_subset (hC p) (upperHemicontinuous_iff.mp hupper p)
        (S := {z | b < f z}) (isOpen_lt continuous_const hf)
        (fun x hx ↦ hb.trans_le (hle p x hx))
      filter_upwards [h] with q hq
      obtain ⟨x, hx, hv, -⟩ := hmin q
      exact hv ▸ hq x hx
    · intro b hb
      obtain ⟨x, hx, hv, -⟩ := hmin p
      have hp : (x, p) ∈ {z | f z < b} := by
        change f (x, p) < b
        rwa [hv]
      have hopen : IsOpen {z | f z < b} := isOpen_lt hf continuous_const
      have hprod : {z | f z < b} ∈ 𝓝 x ×ˢ 𝓝 p := by
        rw [← nhds_prod_eq]
        exact hopen.mem_nhds hp
      obtain ⟨U, hU, V, hV, hsub⟩ := Filter.mem_prod_iff.mp hprod
      obtain ⟨W, hWU, hW, hxW⟩ := mem_nhds_iff.mp hU
      have hhit : {q | (C q ∩ W).Nonempty} ∈ 𝓝 p :=
        ((lowerHemicontinuous_iff_isOpen_inter_nonempty.mp hlower) W hW).mem_nhds
          ⟨x, hx, hxW⟩
      filter_upwards [hhit, hV] with q hq hqV
      obtain ⟨y, hy, hyW⟩ := hq
      exact (hle q y hy).trans_lt (hsub ⟨hWU hyW, hqV⟩)
  refine ⟨hvalue, upperHemicontinuous_iff_forall_isOpen.mpr ?_, ?_⟩
  · intro p U hU hp
    have hopen : IsOpen {z : X × P | z.1 ∈ U ∨ value z.2 < f z} :=
      (hU.preimage continuous_fst).union (isOpen_lt (hvalue.comp continuous_snd) hf)
    have hmem (x : X) (hx : x ∈ C p) : (x, p) ∈ {z : X × P | z.1 ∈ U ∨ value z.2 < f z} := by
      by_cases he : f (x, p) = value p
      · exact Or.inl (hp ⟨hx, he⟩)
      · exact Or.inr (lt_of_le_of_ne (hle p x hx) (Ne.symm he))
    filter_upwards [eventually_feasible_prod_subset (hC p)
      (upperHemicontinuous_iff.mp hupper p) hopen hmem] with q hq
    intro x hx
    exact (hq x hx.1).resolve_right (by rw [hx.2]; exact lt_irrefl _)
  · intro p
    obtain ⟨x, hx, hv, -⟩ := hmin p
    exact ⟨x, hx, hv⟩

end ParametricMinimum

/-- **Theorem 3.2.8** of [conn2000trust], counterexample to lower hemicontinuity. The correspondence
$$p \mapsto \operatorname*{argmin}_{x \in [0, 1]} px$$
on $\mathbb{R}$ is not lower hemicontinuous.

The failure is at $p = 0$, where every point of $[0, 1]$ is a minimizer. The feasible set is
fixed, and the objective is jointly continuous and linear in $x$.

**Correction.** Compact nonempty continuous feasible values yield a continuous optimum, attained
minimizers and upper hemicontinuity even without convexity. The examples show failure of lower
hemicontinuity of minimizers and failure of value continuity without compactness.
-/
theorem theorem_3_2_8_counterexample :
    ¬ LowerHemicontinuous (fun p : ℝ ↦
      {x ∈ Icc (0 : ℝ) 1 | IsMinOn (fun y ↦ p * y) (Icc (0 : ℝ) 1) x}) := by
  intro h
  have hopen := lowerHemicontinuous_iff_isOpen_inter_nonempty.mp h (Ioi (1 / 2 : ℝ)) isOpen_Ioi
  have hmem : (0 : ℝ) ∈ {p : ℝ | ({x ∈ Icc (0 : ℝ) 1 |
      IsMinOn (fun y ↦ p * y) (Icc (0 : ℝ) 1) x} ∩ Ioi (1 / 2 : ℝ)).Nonempty} := by
    refine ⟨1, ⟨⟨by norm_num, le_rfl⟩, ?_⟩, by norm_num⟩
    intro y _
    simp
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
  have hεball : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  obtain ⟨x, ⟨hx, hxmin⟩, hxopen⟩ := hsub hεball
  have hle : (ε / 2) * x ≤ (ε / 2) * 0 := hxmin (show 0 ∈ Icc (0 : ℝ) 1 by norm_num)
  have hpos : 0 < (ε / 2) * x :=
    mul_pos (half_pos hε) (by linarith [show (1 / 2 : ℝ) < x from hxopen])
  linarith


private theorem strictLocalMinOn_of_minorant [FiniteDimensional ℝ E]
    {F L : E → ℝ} {S : Set E} {x : E} (hL : ContDiffAt ℝ 2 L x)
    (hstat : fderiv ℝ L x = 0) (hminor : ∀ y ∈ S, L y - L x ≤ F y - F x)
    (hpos : ∀ d ∈ posTangentConeAt {y ∈ S | F y ≤ F x} x, d ≠ 0 →
      0 < iteratedFDeriv ℝ 2 L x (fun _ ↦ d)) :
    Optimization.IsStrictLocalMinOn F S x := by
  have hm := Optimization.isStrictLocalMinOn_of_posTangentCone hL
    (C := {y ∈ S | F y ≤ F x})
    (Eventually.of_forall fun y ↦ by simp [hstat]) (fun d hd hn _ ↦ hpos d hd hn)
  rw [Optimization.isStrictLocalMinOn_iff_eventually] at hm ⊢
  filter_upwards [hm] with y hy hyS hyx
  by_contra! hbad
  exact (not_lt_of_ge (by linarith [hminor y hyS, hbad])) (hy ⟨hyS, hbad⟩ hyx)

/-- **Theorem 3.2.14** of [conn2000trust]. Let $E$ be a finite-dimensional real normed space and $W$
a real inner product space. Let $f : E \to \mathbb{R}$ and $c : E \to W$ be twice continuously
differentiable at $x \in S$, let $c$ map $S$ into $C \subseteq W$, and let
$h : W \to \mathbb{R}$. Let
$$K = \{g \in W : h(c(x)) + \langle z - c(x), g \rangle \le h(z) \text{ for all } z \in C\}$$
be the subgradients of $h$ at $c(x)$ relative to $C$, and let
$L_g(y) = f(y) + \langle c(y), g \rangle$. Let $g^* \in K$ with $L_{g^*}'(x) = 0$, and suppose
that
$$\langle d, \nabla^2 L_{g^*}(x) d \rangle > 0$$
for every $d$ with $\|d\| = 1$ and $L_g'(x) d \le 0$ for all $g \in K$. Then $x$ is a strict
local minimizer of $f + h \circ c$ on $S$.

**Correction.** The book also asserts isolation among local minimizers. On the domain
$S = \{0\} \cup \{1/j : j \in \mathbb{N},\ j \ge 1\}$, take $f(y) = y^2$ and $h = c = 0$ with
$C = \mathbb{R}$. The conditions hold at $0$. Every point $1/j$ is a local minimizer on $S$, so
the isolation claim fails for this domain. The statement gives strict local optimality on $S$.

**Generalization.** The source assumes convexity of $h$. The argument only uses the affine
minorants touching at $c(x)$, which the statement collects in $K$ for any $h$.

Because $g^*$ gives zero first variation, the zero support condition in (3.2.24) is equivalent
to the condition that every first variation $L_g'(x) d$ with $g \in K$ is nonpositive.

**Correction.** The result uses supporting affine minorants of the outer function on its domain. It
concludes strict local minimality on the stated feasible domain. An arbitrary domain can have
accumulating isolated points, so isolation among local minimizers is omitted.
-/
theorem theorem_3_2_14 [FiniteDimensional ℝ E]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {f : E → ℝ} {c : E → W} {h : W → ℝ} {S : Set E} {C : Set W} {x : E}
    (hx : x ∈ S) (hcS : MapsTo c S C) (hf : ContDiffAt ℝ 2 f x) (hc : ContDiffAt ℝ 2 c x) :
    let K := {g : W | ∀ z ∈ C, h (c x) + ⟪z - c x, g⟫ ≤ h z}
    let L := fun (g : W) (y : E) ↦ f y + ⟪c y, g⟫
    ∀ gStar ∈ K, fderiv ℝ (L gStar) x = 0 →
      (∀ d : E, ‖d‖ = 1 → (∀ g ∈ K, fderiv ℝ (L g) x d ≤ 0) →
        0 < iteratedFDeriv ℝ 2 (L gStar) x (fun _ ↦ d)) →
      x ∈ S ∧ Optimization.IsStrictLocalMinOn (fun y ↦ f y + h (c y)) S x := by
  dsimp only
  intro gStar hgStar hstat hpos
  let F (y : E) := f y + h (c y)
  let L (g : W) (y : E) := f y + ⟪c y, g⟫
  let K := {g : W | ∀ z ∈ C, h (c x) + ⟪z - c x, g⟫ ≤ h z}
  have hL (g : W) : ContDiffAt ℝ 2 (L g) x := hf.add (hc.inner ℝ contDiffAt_const)
  have hminor (g : W) (hg : g ∈ K) (y : E) (hy : y ∈ S) : L g y - L g x ≤ F y - F x := by
    have hp := hg (c y) (hcS hy)
    rw [inner_sub_left] at hp
    dsimp [L, F]
    linarith
  refine ⟨hx, strictLocalMinOn_of_minorant (F := F) (L := L gStar) (hL gStar) hstat
    (hminor gStar hgStar) ?_⟩
  intro d hd hd₀
  have hdir (g : W) (hg : g ∈ K) : fderiv ℝ (L g) x d ≤ 0 := by
    have hm : IsMaxOn (L g) {y ∈ S | F y ≤ F x} x := by
      intro y hy
      change y ∈ S ∧ F y ≤ F x at hy
      change L g y ≤ L g x
      linarith [hminor g hg y hy.1, hy.2]
    exact hm.isLocalMaxOn.hasFDerivWithinAt_nonpos
      ((hL g).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt hd
  let a : ℝ := ‖d‖⁻¹
  have ha : 0 < a := inv_pos.mpr (norm_pos_iff.mpr hd₀)
  have hunit : ‖a • d‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg ha.le]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hd₀)
  have hp := hpos (a • d) hunit (fun g hg ↦ by
    rw [map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos ha.le (hdir g hg))
  let H := iteratedFDeriv ℝ 2 (L gStar) x
  have hscale : H (fun _ ↦ a • d) = a ^ 2 * H (fun _ ↦ d) := by
    change H.toMultilinearMap (fun _ ↦ a • d) = _
    rw [H.toMultilinearMap.map_smul_univ (fun _ ↦ a) (fun _ ↦ d)]
    simp
  change 0 < H (fun _ ↦ a • d) at hp
  rw [hscale] at hp
  exact pos_of_mul_pos_right hp (sq_nonneg a)


section SmoothNormalMultipliers

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [FiniteDimensional ℝ V]

open Constrained
open scoped Pointwise

/-- **Theorem 3.2.11** of [conn2000trust], under a normal-cone sum rule. Let $V$ be a
finite-dimensional real inner product space, let $C \subseteq V$, and let
$F = \{y : h_i(y) = 0, \ g_j(y) \le 0\}$ with $x \in F$. Let $f$ be differentiable at $x$, and
let $x$ be a local minimizer of $f$ on $C \cap F$. Let
$$Q = \{z : h_i'(x)(z - x) = 0 \text{ for all } i, \ g_j'(x)(z - x) \le 0 \text{ for active }
  j\}.$$
Suppose that $z - x \in T_{C \cap F}(x)$ for every $z \in C \cap Q$, and that
$N_{C \cap Q}(x) = N_C(x) + N_Q(x)$. Then there are multipliers $\lambda$ and $\mu$ with
$h_i(x) = 0$, $g_j(x) \le 0$, $\mu_j \ge 0$, $\mu_j g_j(x) = 0$ and
$$-\nabla f(x) - \sum_i \lambda_i \nabla h_i(x) - \sum_j \mu_j \nabla g_j(x) \in N_C(x).$$

**Correction.** The source derives the multipliers from the linearization of the tangent cone
alone. The normal-cone sum rule at the minimizer is also needed; see
`ConnGouldToint.Chapter03.theorem_3_2_11_tangent_counterexample`.

The inequalities are written $g_j \le 0$.

**Correction.** A normal-cone sum rule is required in addition to the local tangent inclusion. One
variant derives the rule from exactness of the indicator sum. The counterexample has the tangent
equality but no required multiplier.
-/
theorem theorem_3_2_11_of_normalCone_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    {C : Set V} {f : V → ℝ} {h : ι → V → ℝ} {g : κ → V → ℝ} {x : V}
    (hx : x ∈ feasible h g) (hf : DifferentiableAt ℝ f x)
    (hmin : IsLocalMinOn f (C ∩ feasible h g) x) :
    let Q := {z : V | (∀ i, fderiv ℝ (h i) x (z - x) = 0) ∧
      ∀ j ∈ activeSet g x, fderiv ℝ (g j) x (z - x) ≤ 0}
    (∀ z ∈ C ∩ Q, z - x ∈ posTangentConeAt (C ∩ feasible h g) x) →
    normalCone (innerₗ V) (C ∩ Q) x = normalCone (innerₗ V) C x + normalCone (innerₗ V) Q x →
    ∃ (l : ι → ℝ) (μ : κ → ℝ), (∀ i, h i x = 0) ∧
      (∀ j, g j x ≤ 0 ∧ 0 ≤ μ j ∧ μ j * g j x = 0) ∧
      -gradient f x - (∑ i, l i • gradient (h i) x) - (∑ j, μ j • gradient (g j) x) ∈
        normalCone (innerₗ V) C x := by
  classical
  intro Q hQ hsum
  have hn : -gradient f x ∈ normalCone (innerₗ V) (C ∩ Q) x := by
    intro z hz
    have hp := hmin.hasFDerivWithinAt_nonneg hf.hasFDerivAt.hasFDerivWithinAt (hQ z hz)
    simpa [innerₗ_apply_apply] using hp
  rw [hsum] at hn
  obtain ⟨n, hn, w, hw, hnw⟩ := hn
  let A : (ι ⊕ ι) ⊕ activeSet g x → V :=
    Sum.elim (Sum.elim (fun i ↦ gradient (h i) x) (fun i ↦ -gradient (h i) x))
      (fun j ↦ gradient (g j) x)
  have hlin : ∀ d : V, (∀ i, innerₗ V d (A i) ≤ 0) → innerₗ V d w ≤ 0 := by
    intro d hd
    have hh (i : ι) : fderiv ℝ (h i) x d = 0 := by
      refine le_antisymm ?_ ?_
      · simpa [A, innerₗ_apply_apply] using hd (.inl (.inl i))
      · simpa [A, innerₗ_apply_apply] using hd (.inl (.inr i))
    have hg (j : κ) (hj : j ∈ activeSet g x) : fderiv ℝ (g j) x d ≤ 0 := by
      simpa [A, innerₗ_apply_apply] using hd (.inr ⟨j, hj⟩)
    have hz : x + d ∈ Q := by simpa [Q] using And.intro hh hg
    simpa using hw (x + d) hz
  obtain ⟨a, ha, hwa⟩ := (ConvexAnalysis.farkas (B := innerₗ V) A w).mp hlin
  let l (i : ι) := a (.inl (.inl i)) - a (.inl (.inr i))
  let μ := Function.extend (Subtype.val : activeSet g x → κ) (fun j ↦ a (.inr j)) 0
  have hμactive (j : κ) (hj : j ∈ activeSet g x) : μ j = a (.inr ⟨j, hj⟩) :=
    Subtype.val_injective.extend_apply _ _ ⟨j, hj⟩
  have hμinactive (j : κ) (hj : j ∉ activeSet g x) : μ j = 0 :=
    Function.extend_apply' _ _ _ (by rintro ⟨⟨j', hj'⟩, rfl⟩; exact hj hj')
  have hw' : (∑ i, l i • gradient (h i) x) + (∑ j, μ j • gradient (g j) x) = w := by
    rw [show (∑ j, μ j • gradient (g j) x) = ∑ j : activeSet g x,
      a (.inr j) • gradient (g j) x from sum_extend_activeSet_smul _ _]
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hwa
    simp only [l, sub_eq_add_neg, add_smul, neg_smul, Finset.sum_add_distrib,
      Finset.sum_neg_distrib]
    simpa [A, smul_neg, Finset.sum_neg_distrib] using hwa
  refine ⟨l, μ, hx.1, fun j ↦ ⟨hx.2 j, ?_, ?_⟩, ?_⟩
  · by_cases hj : j ∈ activeSet g x
    · rw [hμactive j hj]
      exact ha _
    · rw [hμinactive j hj]
  · by_cases hj : j ∈ activeSet g x
    · rw [mem_activeSet.mp hj, mul_zero]
    · rw [hμinactive j hj, zero_mul]
  · have heq : -gradient f x - (∑ i, l i • gradient (h i) x) -
        (∑ j, μ j • gradient (g j) x) = n := by
      rw [← sub_add_eq_sub_sub, hw', ← hnw]
      exact add_sub_cancel_right n w
    simpa only [heq] using hn

/-- **Theorem 3.2.11** of [conn2000trust]. Let $V$, $C$, $F$, $f$, $x$ and $Q$ be as in
`ConnGouldToint.Chapter03.theorem_3_2_11_of_normalCone_sum`, with $x \in C$. Suppose that
$z - x \in T_{C \cap F}(x)$ for every $z \in C \cap Q$, and that the indicator functions of $C$
and $Q$ satisfy the exact sum rule. Then there are multipliers $\lambda$ and $\mu$ with
$h_i(x) = 0$, $g_j(x) \le 0$, $\mu_j \ge 0$, $\mu_j g_j(x) = 0$ and
$$-\nabla f(x) - \sum_i \lambda_i \nabla h_i(x) - \sum_j \mu_j \nabla g_j(x) \in N_C(x).$$

**Correction.** As in `ConnGouldToint.Chapter03.theorem_3_2_11_of_normalCone_sum`, the
linearization of the tangent cone alone does not give the multipliers.

The exact sum rule is `ConvexAnalysis.IsExactSum` for the indicator functions; it gives the
normal-cone sum rule.

**Correction.** A normal-cone sum rule is required in addition to the local tangent inclusion. One
variant derives the rule from exactness of the indicator sum. The counterexample has the tangent
equality but no required multiplier.
-/
theorem theorem_3_2_11 {ι κ : Type*} [Fintype ι] [Fintype κ]
    {C : Set V} {f : V → ℝ} {h : ι → V → ℝ} {g : κ → V → ℝ} {x : V}
    (hxC : x ∈ C) (hx : x ∈ feasible h g) (hf : DifferentiableAt ℝ f x)
    (hmin : IsLocalMinOn f (C ∩ feasible h g) x) :
    let Q := {z : V | (∀ i, fderiv ℝ (h i) x (z - x) = 0) ∧
      ∀ j ∈ activeSet g x, fderiv ℝ (g j) x (z - x) ≤ 0}
    (∀ z ∈ C ∩ Q, z - x ∈ posTangentConeAt (C ∩ feasible h g) x) →
    IsExactSum (innerₗ V) (indicatorFn C) (indicatorFn Q) →
    ∃ (l : ι → ℝ) (μ : κ → ℝ), (∀ i, h i x = 0) ∧
      (∀ j, g j x ≤ 0 ∧ 0 ≤ μ j ∧ μ j * g j x = 0) ∧
      -gradient f x - (∑ i, l i • gradient (h i) x) - (∑ j, μ j • gradient (g j) x) ∈
        normalCone (innerₗ V) C x := by
  intro Q hQ hsum
  exact theorem_3_2_11_of_normalCone_sum hx hf hmin hQ
    (hsum.normalCone_inter hxC (by simp [Q]))

end SmoothNormalMultipliers

/-- **Theorem 3.2.11** of [conn2000trust], counterexample. In $\mathbb{R}^3$ with coordinates
$w_0, w_1, w_2$, let
$$C = \{w : w_2 \ge 0, \ w_1 + 2t w_0 + t^2 w_2 \ge 0 \text{ for all } t \in \mathbb{R}\},$$
a closed convex cone, let $h(w) = w_1$, $Q = \{w : w_1 = 0\}$ and $f(w) = w_0$. Then $0 \in C$,
$f$ and $h$ are continuously differentiable, $h(0) = 0$, $0$ minimizes $f$ on $C \cap Q$, $Q$ is
the kernel of $h'(0)$, and the tangent cone is exactly linearized:
$T_{C \cap Q}(0) = T_C(0) \cap Q$. But there is no $\lambda \in \mathbb{R}$ with
$$-\nabla f(0) - \lambda \nabla h(0) \in N_C(0).$$

The set $C \cap Q$ is the nonnegative $w_2$-axis.

**Correction.** A normal-cone sum rule is required in addition to the local tangent inclusion. One
variant derives the rule from exactness of the indicator sum. The counterexample has the tangent
equality but no required multiplier.
-/
theorem theorem_3_2_11_tangent_counterexample :
    let W := EuclideanSpace ℝ (Fin 3)
    let C : Set W := {w | 0 ≤ w 2 ∧ ∀ t : ℝ, 0 ≤ w 1 + 2 * t * w 0 + t ^ 2 * w 2}
    let Q : Set W := {w | w 1 = 0}
    let f : W → ℝ := fun w ↦ w 0
    let h : W → ℝ := fun w ↦ w 1
    IsClosed C ∧ Convex ℝ C ∧ (0 : W) ∈ C ∧
      ContDiff ℝ 1 f ∧ ContDiff ℝ 1 h ∧ h 0 = 0 ∧ IsMinOn f (C ∩ Q) 0 ∧
      Q = {d | fderiv ℝ h 0 d = 0} ∧
      posTangentConeAt (C ∩ Q) (0 : W) = posTangentConeAt C 0 ∩ Q ∧
      ¬ ∃ l : ℝ, -gradient f 0 - l • gradient h 0 ∈ normalCone (innerₗ W) C 0 := by
  intro W C Q f h
  let b (i : Fin 3) : W →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i
  let L (t : ℝ) := b 1 + (2 * t) • b 0 + t ^ 2 • b 2
  have hCeq : C = {w : W | 0 ≤ b 2 w} ∩ ⋂ t : ℝ, {w : W | 0 ≤ L t w} := by
    ext w
    simp [C, L, smul_eq_mul]
    rfl
  have hclosed : IsClosed C := by
    rw [hCeq]
    exact (isClosed_le continuous_const (b 2).continuous).inter
      (isClosed_iInter fun t ↦ isClosed_le continuous_const (L t).continuous)
  have hconv : Convex ℝ C := by
    rw [hCeq]
    exact (convex_halfSpace_ge (b 2).toLinearMap.isLinear 0).inter
      (convex_iInter fun t ↦ convex_halfSpace_ge (L t).toLinearMap.isLinear 0)
  have h₀ : (0 : W) ∈ C := by simp [C, PiLp.zero_apply]
  have hscale (a : ℝ) (ha : 0 ≤ a) {w : W} (hw : w ∈ C) : a • w ∈ C := by
    rw [hCeq] at hw ⊢
    refine ⟨?_, ?_⟩
    · simpa using mul_nonneg ha hw.1
    · apply Set.mem_iInter.mpr
      intro t
      have ht : 0 ≤ L t w := (Set.mem_iInter.mp hw.2) t
      simpa using mul_nonneg ha ht
  have htan : posTangentConeAt C (0 : W) = C := by
    ext d
    constructor
    · intro hd
      obtain ⟨I, F, hF, a, w, _, hw, hlim⟩ := exists_fun_of_mem_tangentConeAt hd
      let : F.NeBot := hF
      apply hclosed.mem_of_tendsto hlim
      filter_upwards [hw] with n hn
      exact hscale (a n : ℝ) (a n).coe_nonneg (by simpa using hn)
    · intro hd
      simpa using sub_mem_posTangentConeAt_of_segment_subset (hconv.segment_subset h₀ hd)
  have hQ0 : (0 : W) ∈ Q := by simp [Q, PiLp.zero_apply]
  have hQconv : Convex ℝ Q :=
    convex_hyperplane (b 1).toLinearMap.isLinear 0
  have heq : posTangentConeAt (C ∩ Q) (0 : W) = posTangentConeAt C 0 ∩ Q := by
    rw [htan]
    ext d
    constructor
    · intro hd
      refine ⟨htan ▸ tangentConeAt_mono inter_subset_left hd, ?_⟩
      have hzero : IsLocalMinOn h (C ∩ Q) (0 : W) :=
        (show IsMinOn h (C ∩ Q) (0 : W) from fun z hz ↦ by
          change (0 : W) 1 ≤ z 1
          rw [PiLp.zero_apply, show z 1 = 0 from hz.2]).isLocalMinOn
      have hnonneg := hzero.hasFDerivWithinAt_nonneg (b 1).hasFDerivAt.hasFDerivWithinAt hd
      have hmax : IsLocalMaxOn h (C ∩ Q) (0 : W) :=
        (show IsMaxOn h (C ∩ Q) (0 : W) from fun z hz ↦ by
          change z 1 ≤ (0 : W) 1
          rw [PiLp.zero_apply, show z 1 = 0 from hz.2]).isLocalMaxOn
      exact le_antisymm (hmax.hasFDerivWithinAt_nonpos
        (b 1).hasFDerivAt.hasFDerivWithinAt hd) hnonneg
    · intro hd
      simpa using sub_mem_posTangentConeAt_of_segment_subset
        ((hconv.inter hQconv).segment_subset ⟨h₀, hQ0⟩ hd)
  have hx0 (w : W) (hw : w ∈ C ∩ Q) : w 0 = 0 := by
    have hm : IsLocalMin (fun t : ℝ ↦ 2 * t * w 0 + t ^ 2 * w 2) 0 := by
      apply IsMinOn.isLocalMin (s := Set.univ) ?_ univ_mem
      intro t _
      have ht := hw.1.2 t
      rw [show w 1 = 0 from hw.2, zero_add] at ht
      simpa using ht
    have hd : HasDerivAt (fun t : ℝ ↦ 2 * t * w 0 + t ^ 2 * w 2) (2 * w 0) 0 := by
      convert (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (w 0)).add
        (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (w 2)) using 1
      · rfl
      · norm_num [id]
    linarith [hm.hasDerivAt_eq_zero hd]
  refine ⟨hclosed, hconv, h₀, (b 0).contDiff, (b 1).contDiff, hQ0,
    fun w hw ↦ by simp [f, PiLp.zero_apply, hx0 w hw], ?_, heq, ?_⟩
  · rw [show fderiv ℝ h 0 = b 1 from (b 1).hasFDerivAt.fderiv]
    rfl
  · rintro ⟨l, hl⟩
    let w (t : ℝ) : W := WithLp.toLp 2 ![t, t ^ 2, 1]
    have hw (t : ℝ) : w t ∈ C := by
      refine ⟨by simp [w], fun a ↦ ?_⟩
      change 0 ≤ t ^ 2 + 2 * a * t + a ^ 2 * 1
      nlinarith [sq_nonneg (t + a)]
    have hp (t : ℝ) : -t - l * t ^ 2 ≤ 0 := by
      have ht := hl (w t) (hw t)
      simp only [innerₗ_apply_apply, sub_zero, inner_sub_right, inner_neg_right,
        real_inner_smul_right, inner_gradient_right, conj_trivial] at ht
      rw [show fderiv ℝ f 0 = b 0 from (b 0).hasFDerivAt.fderiv,
        show fderiv ℝ h 0 = b 1 from (b 1).hasFDerivAt.fderiv] at ht
      exact ht
    have hm : IsLocalMax (fun t : ℝ ↦ -t - l * t ^ 2) 0 := by
      apply IsMaxOn.isLocalMax (s := Set.univ) ?_ univ_mem
      intro t _
      simpa using hp t
    have hd : HasDerivAt (fun t : ℝ ↦ -t - l * t ^ 2) (-1) 0 := by
      convert (hasDerivAt_id (0 : ℝ)).neg.sub (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul l) using 1
      · rfl
      · norm_num [id]
    have hc := hm.hasDerivAt_eq_zero hd
    norm_num at hc



/-- **Theorem 3.2.8** of [conn2000trust], counterexample without compactness. The function
$$p \mapsto \inf_{x \in \mathbb{R}} (px - 1)^2$$
is not continuous.

Its value is $0$ for $p \neq 0$ and $1$ for $p = 0$. The feasible set $\mathbb{R}$ is fixed but
not compact.

**Correction.** Compact nonempty continuous feasible values yield a continuous optimum, attained
minimizers and upper hemicontinuity even without convexity. The examples show failure of lower
hemicontinuity of minimizers and failure of value continuity without compactness.
-/
theorem theorem_3_2_8_noncompact_value_counterexample :
    ¬ Continuous (fun p : ℝ ↦ sInf (Set.range (fun x : ℝ ↦ (p * x - 1) ^ 2))) := by
  let v (p : ℝ) := sInf (Set.range (fun x : ℝ ↦ (p * x - 1) ^ 2))
  have hv₀ : v 0 = 1 := by simp [v]
  have hv (p : ℝ) (hp : p ≠ 0) : v p = 0 := by
    apply IsLeast.csInf_eq
    refine ⟨⟨p⁻¹, by simp [hp]⟩, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact sq_nonneg _
  intro hc
  have hnear := (hc.continuousAt (x := (0 : ℝ))).eventually
    (Metric.ball_mem_nhds (v 0) (show (0 : ℝ) < 1 / 2 by norm_num))
  change ∀ᶠ p in 𝓝 (0 : ℝ), v p ∈ Metric.ball (v 0) (1 / 2) at hnear
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hb : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  have hcontra := hsub hb
  norm_num [hv₀, hv (ε / 2) (half_pos hε).ne', Metric.mem_ball, Real.dist_eq] at hcontra


/-- **Theorem 3.2.15** of [conn2000trust], counterexample on the boundary of the outer domain. Let
$h(z) = -\sqrt{z}$, $c(x) = x^4$, $f(x) = 2x^2$, $t \equiv -1$ and $r \equiv 0$ on $\mathbb{R}$.
Then $h$ is convex on $[0, \infty)$, $t$ is convex, $c$ maps $\mathbb{R}$ into $[0, \infty)$,
$f$, $c$ and $r$ are continuously differentiable, the constraint $t(r(x)) \le 0$ is strictly
inactive, and $0$ is a local minimizer of $f + h \circ c$, which is $x \mapsto x^2$. But $h$ has
no subgradient at $c(0) = 0$ relative to $[0, \infty)$: there is no $a$ with
$h(0) + za \le h(z)$ for all $z \ge 0$.

The outer function must therefore be regular at the composite point.

**Correction.** Local Lipschitz control supplies outer subgradients and an active constraint needs a
strict linearized Clarke descent direction. The convex theorem uses globally defined outer
functions. A boundary example shows convexity on the printed arbitrary domain alone can leave the
outer subdifferential empty.
-/
theorem theorem_3_2_15_boundary_counterexample :
    let h := fun z : ℝ ↦ -Real.sqrt z
    let c := fun x : ℝ ↦ x ^ 4
    let f := fun x : ℝ ↦ 2 * x ^ 2
    let t := fun _ : ℝ ↦ (-1 : ℝ)
    let r := fun _ : ℝ ↦ (0 : ℝ)
    ConvexOn ℝ (Ici 0) h ∧ ConvexOn ℝ univ t ∧ MapsTo c univ (Ici 0) ∧
    ContDiff ℝ 1 f ∧ ContDiff ℝ 1 c ∧ ContDiff ℝ 1 r ∧ t (r 0) < 0 ∧
    IsLocalMinOn (fun x ↦ f x + h (c x)) {x | t (r x) ≤ 0} 0 ∧
    ¬ ∃ a : ℝ, ∀ z ≥ 0, h (c 0) + (z - c 0) * a ≤ h z := by
  dsimp only
  refine ⟨Real.strictConcaveOn_sqrt.concaveOn.neg, convexOn_const _ convex_univ,
    fun x _ ↦ (by positivity : 0 ≤ x ^ 4), contDiff_const.mul (contDiff_id.pow 2),
    contDiff_id.pow 4, contDiff_const, by norm_num, ?_, ?_⟩
  · apply IsMinOn.isLocalMinOn
    intro x _
    have hsq : Real.sqrt (x ^ 4) = x ^ 2 := by
      rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg x)]
    change 2 * (0 : ℝ) ^ 2 + -Real.sqrt (0 ^ 4) ≤ 2 * x ^ 2 + -Real.sqrt (x ^ 4)
    rw [hsq]
    norm_num
    nlinarith [sq_nonneg x]
  · rintro ⟨a, ha⟩
    let ε : ℝ := (|a| + 2)⁻¹
    have hε : 0 < ε := inv_pos.mpr (by positivity)
    have heq : (|a| + 2) * ε = 1 := mul_inv_cancel₀ (by positivity)
    have h := ha (ε ^ 2) (sq_nonneg ε)
    simp only [zero_pow (by decide : (4 : ℕ) ≠ 0), Real.sqrt_zero, neg_zero, sub_zero, zero_add,
      Real.sqrt_sq hε.le] at h
    have h' : ε * a ≤ -1 := by
      apply (mul_le_mul_iff_right₀ hε).mp
      calc
        ε * (ε * a) = ε ^ 2 * a := by ring
        _ ≤ -ε := h
        _ = ε * -1 := by ring
    have hl := mul_le_mul_of_nonneg_right (neg_abs_le a) hε.le
    nlinarith [hl]


section CompositeKKT

variable {V W Z : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]

open Optimization

omit [CompleteSpace V] [FiniteDimensional ℝ W] in
private theorem eventually_composite_ray_quotient_lt
    {f : V → ℝ} {c : V → W} {h : W → ℝ} {x d : V} {b : ℝ}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    {U : Set W} {K : ℝ≥0} (hU : U ∈ 𝓝 (c x)) (hK : LipschitzOnWith K h U)
    (hb : fderiv ℝ f x d + clarkeDerivative h (c x) (fderiv ℝ c x d) < b) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ((f (x + s • d) + h (c (x + s • d))) - (f x + h (c x))) / s < b := by
  let p (s : ℝ) := x + s • d
  let v := fderiv ℝ c x d
  let A := fderiv ℝ f x d
  let B := clarkeDerivative h (c x) v
  let ε := (b - (A + B)) / 3
  have hε : 0 < ε := by dsimp [ε, A, B, v]; linarith
  have hp : HasDerivAt p d 0 := by
    simpa [p] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have hp₀ : p 0 = x := by simp [p]
  have hpn : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    rw [← hp₀]
    exact hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hfn : Tendsto (fun s : ℝ ↦ (f (p s) - f x) / s) (𝓝[>] 0) (𝓝 A) := by
    have h : HasFDerivAt f (fderiv ℝ f x) (p 0) := hp₀ ▸ hf.hasFDerivAt
    simpa [hp₀, Function.comp_def, A, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (h.comp_hasDerivAt 0 hp).tendsto_slope_zero_right
  have hcn : Tendsto (fun s : ℝ ↦ s⁻¹ • (c (p s) - c x)) (𝓝[>] 0) (𝓝 v) := by
    have h : HasFDerivAt c (fderiv ℝ c x) (p 0) := hp₀ ▸ hc.hasFDerivAt
    simpa [hp₀, Function.comp_def, v] using (h.comp_hasDerivAt 0 hp).tendsto_slope_zero_right
  have he : Tendsto (fun s : ℝ ↦ (K : ℝ) * ‖s⁻¹ • (c (p s) - c x) - v‖)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ((hcn.sub (tendsto_const_nhds (x := v))).norm.const_mul (K : ℝ))
  have hlin : Tendsto (fun s : ℝ ↦ c x + s • v) (𝓝[>] (0 : ℝ)) (𝓝 (c x)) := by
    have ht : Tendsto (fun s : ℝ ↦ s) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds (x := c x)).add (ht.smul (tendsto_const_nhds (x := v)))
  have hbase := eventually_base_quotient_lt_of_clarkeDerivative_lt hU hK
    (show B < B + ε by linarith)
  filter_upwards [hfn.eventually_lt_const (show A < A + ε by linarith),
    he.eventually_lt_const hε, hbase, (hc.continuousAt.tendsto.comp hpn).eventually hU,
    hlin.eventually hU, self_mem_nhdsWithin] with s hsF hsE hsH hsC hsL hs
  change 0 < s at hs
  have hnorm : ‖s⁻¹ • (c (p s) - c x) - v‖ = ‖c (p s) - (c x + s • v)‖ / s := by
    have heq : s⁻¹ • (c (p s) - c x) - v = s⁻¹ • (c (p s) - (c x + s • v)) := by
      rw [show c (p s) - (c x + s • v) = (c (p s) - c x) - s • v by abel]
      simp only [smul_sub, inv_smul_smul₀ hs.ne']
    rw [heq, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), div_eq_mul_inv, mul_comm]
  have hLip := hK.dist_le_mul _ hsC _ hsL
  rw [Real.dist_eq, dist_eq_norm] at hLip
  have herror : (h (c (p s)) - h (c x + s • v)) / s ≤
      (K : ℝ) * ‖s⁻¹ • (c (p s) - c x) - v‖ := by
    rw [hnorm, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right ((le_abs_self _).trans hLip) hs.le
  change ((f (p s) + h (c (p s))) - (f x + h (c x))) / s < b
  have hsplit : ((f (p s) + h (c (p s))) - (f x + h (c x))) / s =
      (f (p s) - f x) / s + (h (c (p s)) - h (c x + s • v)) / s +
        (h (c x + s • v) - h (c x)) / s := by ring
  rw [hsplit]
  dsimp only [ε] at hsF hsE hsH
  linarith

omit [CompleteSpace V] in
private theorem isCompact_convexJoin_real {P Q : Set V} (hP : IsCompact P) (hQ : IsCompact Q) :
    IsCompact (convexJoin ℝ P Q) := by
  let T (z : ℝ × V × V) := z.1 • z.2.1 + (1 - z.1) • z.2.2
  have hT : Continuous T := (continuous_fst.smul (continuous_fst.comp continuous_snd)).add
    ((continuous_const.sub continuous_fst).smul (continuous_snd.comp continuous_snd))
  have heq : convexJoin ℝ P Q = T '' (Icc (0 : ℝ) 1 ×ˢ (P ×ˢ Q)) := by
    ext z
    rw [mem_convexJoin]
    constructor
    · rintro ⟨p, hp, q, hq, a, b, ha, hb, hab, rfl⟩
      exact ⟨(a, p, q), ⟨⟨ha, by linarith⟩, hp, hq⟩, by
        change a • p + (1 - a) • q = a • p + b • q
        rw [show 1 - a = b by linarith]⟩
    · rintro ⟨⟨a, p, q⟩, ⟨ha, hp, hq⟩, rfl⟩
      exact ⟨p, hp, q, hq, a, 1 - a, ha.1, sub_nonneg.mpr ha.2, by ring, rfl⟩
  rw [heq]
  exact (isCompact_Icc.prod (hP.prod hQ)).image hT

/-- **Theorem 3.2.15** of [conn2000trust], Clarke form. Let $V$ be a real Hilbert space and $W$, $Z$
finite-dimensional real inner product spaces. Let $f : V \to \mathbb{R}$, $c : V \to W$ and
$r : V \to Z$ be differentiable at $x$, and let $h : W \to \mathbb{R}$ and
$t : Z \to \mathbb{R}$ be Lipschitz continuous on neighbourhoods of $c(x)$ and $r(x)$. Let
$t(r(x)) \le 0$; if $t(r(x)) = 0$, let there be a direction $d$ with
$t^\circ(r(x); r'(x) d) < 0$. If $x$ is a local minimizer of $f + h \circ c$ on
$\{z : t(r(z)) \le 0\}$, then there are $y \in \partial^\circ h(c(x))$,
$u \in \partial^\circ t(r(x))$ and $\mu \ge 0$ with $t(r(x)) \mu = 0$ and
$$\nabla f(x) + c'(x)^* y + \mu \, r'(x)^* u = 0.$$

**Correction.** The outer functions are locally Lipschitz, and an active constraint needs a
strict Clarke descent direction through $r$. The printed conditions on the domains of the outer
functions do not suffice; see `ConnGouldToint.Chapter03.theorem_3_2_15_boundary_counterexample`.

The multipliers use Clarke subgradients, so the result also applies to nonconvex outer
functions.

**Correction.** Local Lipschitz control supplies outer subgradients and an active constraint needs a
strict linearized Clarke descent direction. The convex theorem uses globally defined outer
functions. A boundary example shows convexity on the printed arbitrary domain alone can leave the
outer subdifferential empty.
-/
theorem theorem_3_2_15_clarke {f : V → ℝ} {c : V → W} {r : V → Z} {h : W → ℝ}
    {t : Z → ℝ} {x : V} (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    (hr : DifferentiableAt ℝ r x) {U : Set W} {T : Set Z} {K M : ℝ≥0}
    (hU : U ∈ 𝓝 (c x)) (hK : LipschitzOnWith K h U)
    (hT : T ∈ 𝓝 (r x)) (hM : LipschitzOnWith M t T)
    (hfeas : t (r x) ≤ 0)
    (hQ : t (r x) = 0 → ∃ d, clarkeDerivative t (r x) (fderiv ℝ r x d) < 0)
    (hmin : IsLocalMinOn (fun z ↦ f z + h (c z)) {z | t (r z) ≤ 0} x) :
    ∃ y ∈ clarkeSubgradient h (c x), ∃ u ∈ clarkeSubgradient t (r x), ∃ μ : ℝ,
      0 ≤ μ ∧ t (r x) * μ = 0 ∧
      gradient f x + (fderiv ℝ c x).adjoint y + μ • (fderiv ℝ r x).adjoint u = 0 := by
  let H := clarkeSubgradient h (c x)
  let J := clarkeSubgradient t (r x)
  let A := (fderiv ℝ c x).adjoint
  let B := (fderiv ℝ r x).adjoint
  have hsH := hasClarkeSupport_of_lipschitzOnWith hU hK
  have hsJ := hasClarkeSupport_of_lipschitzOnWith hT hM
  rcases hfeas.lt_or_eq with hinact | hact
  · have hct : ContinuousAt (fun z ↦ t (r z)) x :=
      (hM.continuousOn.continuousAt hT).comp hr.continuousAt
    have hnear : ∀ᶠ z in 𝓝 x, z ∈ {z | t (r z) ≤ 0} :=
      (hct.tendsto.eventually (Iio_mem_nhds hinact)).mono fun _ hz ↦ le_of_lt hz
    have hm : IsLocalMin (fun z ↦ f z + h (c z)) x := by
      change ∀ᶠ z in 𝓝[{z | t (r z) ≤ 0}] x,
        f x + h (c x) ≤ f z + h (c z) at hmin
      rw [eventually_nhdsWithin_iff] at hmin
      filter_upwards [hmin, hnear] with z hz hz'
      exact hz hz'
    obtain ⟨y, hy, hzero⟩ := (corollary_3_2_13 hf hc hm hU hK).1
    obtain ⟨u, hu⟩ := hsJ.nonempty
    exact ⟨y, hy, u, hu, 0, le_rfl, by simp, by simpa using hzero⟩
  · let P := (fun y ↦ gradient f x + A y) '' H
    let Q := B '' J
    have hP : IsCompact P := (isCompact_clarkeSubgradient hU hK).image
      (continuous_const.add A.continuous)
    have hQ' : IsCompact Q := (isCompact_clarkeSubgradient hT hM).image B.continuous
    have hPc : Convex ℝ P := by
      intro p hp q hq a b ha hb hab
      obtain ⟨y, hy, rfl⟩ := hp
      obtain ⟨z, hz, rfl⟩ := hq
      refine ⟨a • y + b • z, convex_clarkeSubgradient h (c x) hy hz ha hb hab, ?_⟩
      simp only [map_add, map_smul, smul_add]
      have he : gradient f x = a • gradient f x + b • gradient f x := by
        rw [← add_smul, hab, one_smul]
      conv_lhs => rw [he]
      abel
    have hQc : Convex ℝ Q := (convex_clarkeSubgradient t (r x)).linear_image B.toLinearMap
    have hjoin : convexHull ℝ (P ∪ Q) = convexJoin ℝ P Q :=
      hPc.convexHull_union hQc (hsH.nonempty.image _) (hsJ.nonempty.image _)
    have hmem : (0 : V) ∈ convexJoin ℝ P Q := by
      rw [← (isCompact_convexJoin_real hP hQ').isClosed.closure_eq, ← hjoin]
      apply (mem_closure_convexHull_iff_le_supportFn (B := innerₗ V) (P ∪ Q) 0).mpr
      intro d
      simp only [innerₗ_apply_apply, inner_zero_left]
      by_contra! hneg
      have hdot (v : V) (hv : v ∈ P ∪ Q) : ⟪v, d⟫ < 0 := by
        have he : ((⟪v, d⟫ : ℝ) : EReal) < 0 :=
          (le_supportFn (B := innerₗ V) hv d).trans_lt hneg
        exact EReal.coe_lt_coe_iff.mp (by simpa using he)
      have hmax :
          fderiv ℝ f x d + clarkeDerivative h (c x) (fderiv ℝ c x d) < 0 := by
        obtain ⟨y, hy, hymax⟩ := (isCompact_clarkeSubgradient hU hK).exists_isMaxOn
          hsH.nonempty (continuous_id.inner continuous_const :
            Continuous (fun z : W ↦ ⟪z, fderiv ℝ c x d⟫)).continuousOn
        have hle := (supportFn_le_coe_iff (B := innerₗ W) (s := H)
          (y := fderiv ℝ c x d)).2 (fun z hz ↦ hymax hz)
        rw [hsH] at hle
        have hv := hdot (gradient f x + A y) (Or.inl ⟨y, hy, rfl⟩)
        rw [inner_add_left, inner_gradient_left, ContinuousLinearMap.adjoint_inner_left] at hv
        exact (add_le_add_right (EReal.coe_le_coe_iff.mp hle) _).trans_lt hv
      have hmaxT : clarkeDerivative t (r x) (fderiv ℝ r x d) < 0 := by
        obtain ⟨u, hu, humax⟩ := (isCompact_clarkeSubgradient hT hM).exists_isMaxOn
          hsJ.nonempty (continuous_id.inner continuous_const :
            Continuous (fun z : Z ↦ ⟪z, fderiv ℝ r x d⟫)).continuousOn
        have hle := (supportFn_le_coe_iff (B := innerₗ Z) (s := J)
          (y := fderiv ℝ r x d)).2 (fun z hz ↦ humax hz)
        rw [hsJ] at hle
        have hv := hdot (B u) (Or.inr ⟨u, hu, rfl⟩)
        rw [ContinuousLinearMap.adjoint_inner_left] at hv
        exact (EReal.coe_le_coe_iff.mp hle).trans_lt hv
      have hbad := eventually_composite_ray_quotient_lt hf hc hU hK hmax
      have hfeas' := eventually_composite_ray_quotient_lt
        (f := fun _ : V ↦ (0 : ℝ)) (d := d) (differentiableAt_const 0) hr hT hM
        (b := 0) (by simpa using hmaxT)
      have hray : Tendsto (fun s : ℝ ↦ x + s • d) (𝓝[>] (0 : ℝ))
          (𝓝[{z | t (r z) ≤ 0}] x) := by
        apply tendsto_nhdsWithin_iff.mpr
        constructor
        · have ht : Tendsto (fun s : ℝ ↦ s) (𝓝[>] 0) (𝓝 0) :=
            tendsto_id.mono_right nhdsWithin_le_nhds
          simpa using (tendsto_const_nhds (x := x)).add (ht.smul (tendsto_const_nhds (x := d)))
        · filter_upwards [hfeas', self_mem_nhdsWithin] with s hfs hs
          change 0 < s at hs
          simpa only [zero_add, hact, sub_zero, zero_mul] using
            ((div_lt_iff₀ hs).mp hfs).le
      obtain ⟨s, hsbad, hsm, hs⟩ :=
        (hbad.and ((hray.eventually hmin).and self_mem_nhdsWithin)).exists
      exact (not_lt_of_ge (sub_nonneg.mpr hsm)) ((div_lt_iff₀ hs).mp hsbad |>.trans_eq (zero_mul _))
    obtain ⟨p, ⟨y, hy, rfl⟩, q, ⟨u, hu, rfl⟩, a, b, ha, hb, hab, hzero⟩ :=
      mem_convexJoin.mp hmem
    have hap : 0 < a := by
      by_contra! han
      have ha0 : a = 0 := le_antisymm han ha
      have hb1 : b = 1 := by linarith
      have hq0 : B u = 0 := by simpa [ha0, hb1] using hzero
      obtain ⟨d, hd⟩ := hQ hact
      have hu' := hu (fderiv ℝ r x d)
      rw [← ContinuousLinearMap.adjoint_inner_left, hq0, inner_zero_left] at hu'
      linarith
    refine ⟨y, hy, u, hu, b / a, div_nonneg hb hap.le, by rw [hact, zero_mul], ?_⟩
    have hscaled := congrArg (fun z : V ↦ a⁻¹ • z) hzero
    simpa [smul_add, smul_smul, inv_mul_cancel₀ hap.ne', div_eq_mul_inv, mul_comm a⁻¹ b] using
      hscaled

/-- **Theorem 3.2.15** of [conn2000trust]. Let $V$ be a real Hilbert space and $W$, $Z$
finite-dimensional real inner product spaces. Let $f : V \to \mathbb{R}$, $c : V \to W$ and
$r : V \to Z$ be differentiable at $x$, and let $h : W \to \mathbb{R}$ and
$t : Z \to \mathbb{R}$ be convex and continuous on the whole space and Lipschitz continuous on
neighbourhoods of $c(x)$ and $r(x)$. Let $t(r(x)) \le 0$; if $t(r(x)) = 0$, let there be a
direction $d$ with $t^\circ(r(x); r'(x) d) < 0$. If $x$ is a local minimizer of $f + h \circ c$
on $\{z : t(r(z)) \le 0\}$, then there are convex subgradients $y \in \partial h(c(x))$ and
$u \in \partial t(r(x))$ and $\mu \ge 0$ with $t(r(x)) \mu = 0$ and
$$\nabla f(x) + c'(x)^* y + \mu \, r'(x)^* u = 0.$$

**Correction.** The outer functions are convex on their full spaces and locally Lipschitz at the
image points, and an active constraint needs a strict Clarke descent direction through $r$. The
printed conditions on the domains of the outer functions do not suffice; see
`ConnGouldToint.Chapter03.theorem_3_2_15_boundary_counterexample`.

**Correction.** Local Lipschitz control supplies outer subgradients and an active constraint needs a
strict linearized Clarke descent direction. The convex theorem uses globally defined outer
functions. A boundary example shows convexity on the printed arbitrary domain alone can leave the
outer subdifferential empty.
-/
theorem theorem_3_2_15 {f : V → ℝ} {c : V → W} {r : V → Z} {h : W → ℝ}
    {t : Z → ℝ} {x : V} (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    (hr : DifferentiableAt ℝ r x) (hh : ConvexOn ℝ univ h) (ht : ConvexOn ℝ univ t)
    (hch : Continuous h) (hct : Continuous t) {U : Set W} {T : Set Z} {K M : ℝ≥0}
    (hU : U ∈ 𝓝 (c x)) (hK : LipschitzOnWith K h U)
    (hT : T ∈ 𝓝 (r x)) (hM : LipschitzOnWith M t T)
    (hfeas : t (r x) ≤ 0)
    (hQ : t (r x) = 0 → ∃ d, clarkeDerivative t (r x) (fderiv ℝ r x d) < 0)
    (hmin : IsLocalMinOn (fun z ↦ f z + h (c z)) {z | t (r z) ≤ 0} x) :
    ∃ y ∈ subdifferential (innerₗ W) (fun w ↦ (h w : EReal)) (c x),
      ∃ u ∈ subdifferential (innerₗ Z) (fun z ↦ (t z : EReal)) (r x), ∃ μ : ℝ,
        0 ≤ μ ∧ t (r x) * μ = 0 ∧
        gradient f x + (fderiv ℝ c x).adjoint y + μ • (fderiv ℝ r x).adjoint u = 0 := by
  obtain ⟨y, hy, u, hu, μ, hμ, hcomp, hstat⟩ :=
    theorem_3_2_15_clarke hf hc hr hU hK hT hM hfeas hQ hmin
  exact ⟨y, clarkeSubgradient_subset_subdifferential hh hch hU hK hy,
    u, clarkeSubgradient_subset_subdifferential ht hct hT hM hu, μ, hμ, hcomp, hstat⟩

end CompositeKKT

end ConnGouldToint.Chapter03
