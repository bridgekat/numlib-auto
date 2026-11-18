/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import NumlibSurface.ConnGouldToint.Chapter13.Section03
import NumlibSurface.ConnGouldToint.Chapter13.Section01
import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Conn, Gould and Toint, Section 13.4: The logarithmic barrier model

This module formalizes Section 13.4 of [conn2000trust]: the primal logarithmic barrier method for
the bound constraints $x \ge 0$ in $\mathbb{R}^n$. For an objective $f$ and a barrier parameter
$\mu > 0$, the barrier objective is $f(x) + b_\mu(x)$ with $b_\mu(x) = -\mu \sum_i \log x_i$. The
barrier model (13.4.2) is the second-order Taylor model of $b_\mu$, and Lemma 13.4.1 checks the
barrier and model assumptions for it. Each inner minimization stops at a point that passes the
second-order tests (13.4.3)–(13.4.5) with tolerances $\varepsilon^D$ and $\varepsilon^E$. As $\mu$,
$\varepsilon^D$ and $\varepsilon^E$ tend to zero, these tests give first-order and weak second-order
criticality in the limit (Theorem 13.4.3 and Corollary 13.4.4).

The module also proves the inner convergence that Theorem 13.4.2 needs, under hypotheses stronger
than the printed ones, and two counterexamples: a run of the inner algorithms that never stops under
the printed hypotheses of Theorem 13.4.2, and a bounded-below version of the example after Corollary
13.4.4, whose limit point fails strong second-order criticality. The proofs build on
`NumlibSurface.ConnGouldToint.Chapter13.Section02`,
`NumlibSurface.ConnGouldToint.Chapter13.Section03` and the basic trust-region analysis of Chapter 6.

## Main definitions

* Equation (13.4.2), `ConnGouldToint.Chapter13.logBarrierModel`: the quadratic model of the
  logarithmic barrier at a displacement $s$.
* Equations (13.4.3)–(13.4.5), `ConnGouldToint.Chapter13.BarrierSecondOrderStop`: the positivity,
  dual residual and Hessian stopping tests.
* Definitions before Theorem 13.4.3, `ConnGouldToint.Chapter13.AsymptoticallyActive` and
  `ConnGouldToint.Chapter13.ConsistentlyActive`: a coordinate tends to zero, and every coordinate
  either tends to zero or stays away from zero.
* Equation (13.4.13), `ConnGouldToint.Chapter13.logBarrierCounterObjective`: the quadratic example
  in dimension four, with the Hessian (13.4.14) `ConnGouldToint.Chapter13.logBarrierCounterHessian`.
* Algorithm 13.4.1, `ConnGouldToint.Chapter13.PrimalLogBarrierOuterRun`: the primal log-barrier
  method, with finite inner minimizations `ConnGouldToint.Chapter13.PrimalLogBarrierInnerPrefix` by
  Algorithm 13.2.1 or Algorithm 13.3.1.

## Main results

* Equation (13.4.8), `ConnGouldToint.Chapter13.logBarrier_hessian`: the Hessian of $b_\mu$ is
  diagonal with entries $\mu / x_i^2$.
* Lemma 13.4.1, `ConnGouldToint.Chapter13.logBarrier_contDiffOn`,
  `ConnGouldToint.Chapter13.logBarrier_hessian_bounded`,
  `ConnGouldToint.Chapter13.logBarrierModel_contDiff`,
  `ConnGouldToint.Chapter13.logBarrierModel_zero`,
  `ConnGouldToint.Chapter13.logBarrierModel_fderiv_center`,
  `ConnGouldToint.Chapter13.logBarrierModel_hessian_bounded` and
  `ConnGouldToint.Chapter13.logBarrierModel_fderiv_fderiv`: the logarithmic barrier and its model
  satisfy AC.1c, AC.4c, AM.1, AM.2, AM.3, AM.4h, AM.5c and AC.6b.
* Theorem 13.4.2, `ConnGouldToint.Chapter13.theorem_13_4_2_of_inner_limits`: the inner limits imply
  that the stopping tests hold at infinitely many inner iterates.
* Theorem 13.4.2, `ConnGouldToint.Chapter13.theorem_13_4_2_inner_of_extension`: the first- and
  second-order inner limits for Algorithm 13.3.1 under a uniform clearance, a smooth extension of
  the objective and uniform model estimates.
* Theorem 13.4.2, `ConnGouldToint.Chapter13.theorem_13_4_2_unbounded_primal_inner_run`: under the
  printed hypotheses, a run of Algorithm 13.2.1 never passes the stopping tests.
* Theorem 13.4.3, `ConnGouldToint.Chapter13.theorem_13_4_3`: points that pass the stopping tests
  with vanishing parameter and tolerances have nonnegative limiting gradients, zero limiting
  gradients on inactive coordinates, and nonnegative limiting curvature on inactive directions.
* Corollary 13.4.4, `ConnGouldToint.Chapter13.corollary_13_4_4`: a limit of such points is
  first-order critical and weakly second-order critical.
* Example after Corollary 13.4.4,
  `ConnGouldToint.Chapter13.logBarrierCounterRegularized_convergent_stops`: exact stopping points
  converge to a point with negative curvature in a feasible direction.

## Implementation notes

* Vectors are functions `ι → ℝ` on a finite index type `ι`, with the sup norm of Mathlib. Algorithm
  13.4.1 and its inner runs work in `EuclideanSpace ℝ ι`, so that the trust region and the distance
  to the boundary are Euclidean. The map `ConnGouldToint.Chapter13.barrierEuclideanCoordinates`
  converts between the two.
* The Hessian test (13.4.5) is written as a quadratic-form inequality in the Euclidean norm, and
  $\partial_i f(x)$ is the directional derivative
  `ConnGouldToint.Chapter13.barrierCoordinateGradient`.
* The lower limits in Theorem 13.4.3 are written in eventual form: each negative tolerance $-\eta$
  is eventually a lower bound.

## Deviations from the source

* **Algorithm 13.4.1** (generalization). An inner minimization may stop at index zero when its
  starting point already passes the stopping tests. See
  `ConnGouldToint.Chapter13.PrimalLogBarrierOuterRun`.
* **Theorem 13.4.2** (correction). The printed hypotheses do not give finite stopping. For the
  bilinear objective $x_1 x_2$, a run of Algorithm 13.2.1, and also of Algorithm 13.3.1, with exact
  logarithmic Taylor models is unbounded, has ratios at least $2$, and fails the gradient test at
  every iterate. The inner limits are proved under a uniform clearance, a smooth extension of the
  objective that agrees with it at the iterates and trials, and uniform model estimates. See
  `ConnGouldToint.Chapter13.theorem_13_4_2_unbounded_primal_inner_run`,
  `ConnGouldToint.Chapter13.theorem_13_4_2_unbounded_constrained_primal_inner_run` and
  `ConnGouldToint.Chapter13.theorem_13_4_2_inner_of_extension`.
* **Example after Corollary 13.4.4** (correction). The quadratic (13.4.13) is unbounded below on the
  orthant, so it does not meet the lower-boundedness requirement. A smooth cutoff gives a
  bounded-below objective with the same stopping points and the same limit. See
  `ConnGouldToint.Chapter13.logBarrierCounterRegularized_example`.
-/

open Filter Metric
open scoped Topology
open scoped BigOperators

namespace ConnGouldToint.Chapter13

variable {ι : Type*} [Fintype ι]

/-- **Equation (13.4.2)** of [conn2000trust]. For $x > 0$, a displacement $s$ and a barrier
parameter $\mu$, the **logarithmic barrier model** is
$$m^b(x, s) = -\mu \sum_i \log x_i - \mu \sum_i \frac{s_i}{x_i} + \frac{\mu}{2} \sum_i
  \frac{s_i^2}{x_i^2}.$$
-/
noncomputable def logBarrierModel (x s : ι → ℝ) (μ : ℝ) : ℝ :=
  logBarrier x μ - μ * (∑ i, (x i)⁻¹ * s i) +
    μ / 2 * (∑ i, ((x i) ^ 2)⁻¹ * (s i) ^ 2)

/-- **Equation (13.4.8)** of [conn2000trust]. Let $\mu \in \mathbb{R}$ and $x > 0$. The Hessian of
the logarithmic barrier $b_\mu(y) = -\mu \sum_i \log y_i$ at $x$ is diagonal:
$$\nabla^2 b_\mu(x)[d, e] = \mu \sum_i \frac{d_i e_i}{x_i^2} \quad \text{for all } d, e.$$
-/
theorem logBarrier_hessian (μ : ℝ) {x : ι → ℝ} (hx : ∀ i, 0 < x i) (d e : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (fun y ↦ logBarrier y μ)) x d e =
      μ * ∑ i, ((x i) ^ 2)⁻¹ * d i * e i :=
  Optimization.fderiv_fderiv_logBarrier_apply μ hx d e

/-- **Lemma 13.4.1** of [conn2000trust], AC.1c. For every $\mu \in \mathbb{R}$, the logarithmic
barrier $b_\mu$ is twice continuously differentiable on the interior of the nonnegative orthant. -/
theorem logBarrier_contDiffOn (μ : ℝ) :
    ContDiffOn ℝ 2 (fun x : ι → ℝ ↦ logBarrier x μ)
      (interior (Optimization.nonnegativeOrthant ι)) := by
  intro x hx
  have hpos : ∀ i, 0 < x i := by
    rw [Optimization.nonnegativeOrthant, interior_pi_set Set.finite_univ] at hx
    simpa only [Set.mem_pi, Set.mem_univ, true_implies, interior_Ici, Set.mem_Ioi] using hx
  exact (Optimization.contDiffAt_logBarrier μ hpos).contDiffWithinAt

/-- **Lemma 13.4.1** of [conn2000trust], AC.4c. Let $\mu \in \mathbb{R}$ and $\varepsilon > 0$.
There is $C \ge 1$ such that $\|\nabla^2 b_\mu(x)\| \le C$ for every $x > 0$ whose distance to
the boundary of the nonnegative orthant is at least $\varepsilon$.

The distance and the operator norm are those of the sup norm on `ι → ℝ`. -/
theorem logBarrier_hessian_bounded (μ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ (1 : ℝ), ∀ x : ι → ℝ, (∀ i, 0 < x i) →
      ε ≤ infDist x (frontier (Optimization.nonnegativeOrthant ι)) →
      ‖fderiv ℝ (fderiv ℝ (fun y ↦ logBarrier y μ)) x‖ ≤ C := by
  refine ⟨max 1 (|μ| * Fintype.card ι * (ε ^ 2)⁻¹), le_max_left _ _, fun x hx hdist ↦ ?_⟩
  exact (Optimization.norm_fderiv_fderiv_logBarrier_le μ hε
    (fun i ↦ hdist.trans (Optimization.infDist_frontier_le_coordinate hx i))).trans
      (le_max_right _ _)

/-- The barrier model (13.4.2) of [conn2000trust] is the second-order Taylor model of the barrier:
for $x > 0$, every $s$ and every $\mu$,
$$m^b(x, s) = b_\mu(x) + D b_\mu(x) s + \frac12 \nabla^2 b_\mu(x)[s, s].$$
-/
theorem logBarrierModel_eq_taylor {x : ι → ℝ} (hx : ∀ i, 0 < x i) (s : ι → ℝ) (μ : ℝ) :
    logBarrierModel x s μ = logBarrier x μ + fderiv ℝ (fun y ↦ logBarrier y μ) x s +
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ (fun y ↦ logBarrier y μ)) x s s := by
  change _ = logBarrier x μ + fderiv ℝ (Optimization.logBarrier μ) x s + _
  rw [Optimization.fderiv_logBarrier_apply μ hx, logBarrier_hessian μ hx]
  simp only [logBarrierModel, pow_two, mul_assoc]
  ring


/-- Let $E$ be a real normed space, $a \in \mathbb{R}$, $g$ a continuous linear functional on $E$
and $H$ a continuous symmetric bilinear form on $E$. The quadratic
$d \mapsto a + g(d) + \frac12 H(d, d)$ has the derivative $g + H(s, \cdot)$ at every $s$. -/
theorem barrierQuadratic_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ}
    {g : E →L[ℝ] ℝ} {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hs : ∀ d e, H d e = H e d) (s : E) :
    HasFDerivAt (fun d ↦ a + g d + (1 / 2 : ℝ) * H d d) (g + H s) s := by
  have hquad₀ := H.hasFDerivAt.clm_apply (hasFDerivAt_id s)
  have heq : (H s).comp (ContinuousLinearMap.id ℝ E) + H.flip s = (2 : ℝ) • H s := by
    ext d
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply,
      smul_apply, smul_eq_mul, hs d s]
    ring
  simp only [id_eq] at hquad₀
  rw [heq] at hquad₀
  have hquad : HasFDerivAt (fun d : E ↦ H d d) ((2 : ℝ) • H s) s := by
    exact hquad₀
  have hmodel₀ := (g.hasFDerivAt.const_add a).add
    (hquad.const_smul (1 / 2 : ℝ))
  have heq' : (g + (1 / 2 : ℝ) • ((2 : ℝ) • H s)) = g + H s := by
    rw [smul_smul]
    norm_num
  rw [heq'] at hmodel₀
  exact hmodel₀

private theorem logBarrierModel_fderiv {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    (μ : ℝ) (s : ι → ℝ) :
    fderiv ℝ (logBarrierModel x · μ) s =
      fderiv ℝ (Optimization.logBarrier μ) x +
        fderiv ℝ (fderiv ℝ (Optimization.logBarrier μ)) x s := by
  let g := fderiv ℝ (Optimization.logBarrier μ) x
  let H := fderiv ℝ (fderiv ℝ (Optimization.logBarrier μ)) x
  have hs : ∀ d e, H d e = H e d := by
    intro d e
    rw [show H d e = μ * ∑ i, ((x i) ^ 2)⁻¹ * d i * e i from logBarrier_hessian μ hx d e,
      show H e d = μ * ∑ i, ((x i) ^ 2)⁻¹ * e i * d i from logBarrier_hessian μ hx e d]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hm : (logBarrierModel x · μ) = fun d ↦ logBarrier x μ + g d + (1 / 2 : ℝ) * H d d := by
    funext d
    exact logBarrierModel_eq_taylor hx d μ
  rw [hm]
  exact (barrierQuadratic_hasFDerivAt hs s).fderiv

/-- **Lemma 13.4.1** of [conn2000trust], AM.3. For $x > 0$ and every $\mu$, the derivative of the
barrier model $s \mapsto m^b(x, s)$ at $s = 0$ is the derivative $D b_\mu(x)$ of the barrier. -/
theorem logBarrierModel_fderiv_center {x : ι → ℝ} (hx : ∀ i, 0 < x i) (μ : ℝ) :
    fderiv ℝ (logBarrierModel x · μ) 0 = fderiv ℝ (Optimization.logBarrier μ) x := by
  rw [logBarrierModel_fderiv hx, map_zero, add_zero]

/-- **Lemma 13.4.1** of [conn2000trust], AM.5c and AC.6b. For $x > 0$, every $\mu$ and every $s$,
the Hessian of the barrier model $s \mapsto m^b(x, s)$ at $s$ is $\nabla^2 b_\mu(x)$.

The model Hessian is constant and equal to the barrier Hessian at the center. So the barrier
part of AM.5c is exact, and AC.6b holds with zero Hessian variation. -/
theorem logBarrierModel_fderiv_fderiv {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    (μ : ℝ) (s : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (logBarrierModel x · μ)) s =
      fderiv ℝ (fderiv ℝ (Optimization.logBarrier μ)) x := by
  rw [show fderiv ℝ (logBarrierModel x · μ) = fun t ↦
      fderiv ℝ (Optimization.logBarrier μ) x +
        fderiv ℝ (fderiv ℝ (Optimization.logBarrier μ)) x t from
      funext (logBarrierModel_fderiv hx μ)]
  exact ((fderiv ℝ (fderiv ℝ (Optimization.logBarrier μ)) x).hasFDerivAt.const_add _).fderiv

/-- **Lemma 13.4.1** of [conn2000trust], AM.1. For $x > 0$ and every $\mu$, the barrier model
$s \mapsto m^b(x, s)$ is twice continuously differentiable. -/
theorem logBarrierModel_contDiff {x : ι → ℝ} (hx : ∀ i, 0 < x i) (μ : ℝ) :
    ContDiff ℝ 2 (logBarrierModel x · μ) := by
  simp only [logBarrierModel_eq_taylor hx]
  fun_prop

/-- **Lemma 13.4.1** of [conn2000trust], AM.2. The barrier model interpolates the barrier at its
center: $m^b(x, 0) = b_\mu(x)$ for all $x$ and $\mu$. -/
@[simp] theorem logBarrierModel_zero (x : ι → ℝ) (μ : ℝ) :
    logBarrierModel x 0 μ = logBarrier x μ := by
  simp [logBarrierModel]

/-- **Lemma 13.4.1** of [conn2000trust], AM.4h. Let $\mu \in \mathbb{R}$ and $\varepsilon > 0$.
There is $C \ge 1$ such that $\|\nabla^2_s m^b(x, s)\| \le C$ for every $s$ and every $x > 0$
whose distance to the boundary of the nonnegative orthant is at least $\varepsilon$. -/
theorem logBarrierModel_hessian_bounded (μ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ (1 : ℝ), ∀ x : ι → ℝ, (∀ i, 0 < x i) →
      ε ≤ infDist x (frontier (Optimization.nonnegativeOrthant ι)) →
      ∀ s : ι → ℝ, ‖fderiv ℝ (fderiv ℝ (logBarrierModel x · μ)) s‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := logBarrier_hessian_bounded (ι := ι) μ hε
  exact ⟨C, hC, fun x hx hdist s ↦ by
    rw [logBarrierModel_fderiv_fderiv hx]
    exact hb x hx hdist⟩

/-! ### Stopping tests and the outer limits -/

section Outer

variable [DecidableEq ι]

/-- The partial derivative $\partial_i f(x) = D f(x) e_i$ of $f : \mathbb{R}^n \to \mathbb{R}$,
where $e_i$ is the $i$-th unit vector.

It is the directional Fréchet derivative, and it is $0$ when $f$ is not differentiable at $x$. -/
noncomputable def barrierCoordinateGradient (f : (ι → ℝ) → ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- **Equations (13.4.3)–(13.4.5)** of [conn2000trust]. A point $x \in \mathbb{R}^n$ passes the
**second-order stopping tests** for the objective $f$, the barrier parameter $\mu$ and the
tolerances $\varepsilon^D$, $\varepsilon^E$ if $x > 0$,
$$\sum_i \left(\partial_i f(x) - \frac{\mu}{x_i}\right)^2 \le (\varepsilon^D)^2, \qquad \nabla^2
  f(x)[d, d] + \mu \sum_i \frac{d_i^2}{x_i^2} \ge -\varepsilon^E \|d\|^2 \text{ for all } d,$$
where $\|d\|$ is the Euclidean norm.

The Hessian test (13.4.5) is written as a quadratic-form inequality instead of a bound on the
least eigenvalue. -/
def BarrierSecondOrderStop (f : (ι → ℝ) → ℝ) (x : ι → ℝ) (μ εD εE : ℝ) : Prop :=
  (∀ i, 0 < x i) ∧
  (∑ i, (barrierCoordinateGradient f x i - μ / x i) ^ 2) ≤ εD ^ 2 ∧
  ∀ d : ι → ℝ, -εE * (∑ i, (d i) ^ 2) ≤
    fderiv ℝ (fderiv ℝ f) x d d + μ * ∑ i, ((x i) ^ 2)⁻¹ * d i * d i

/-- The residual in (13.4.3) of [conn2000trust] is the gradient of the barrier objective. If $f$ is
differentiable at $x > 0$, then for every $\mu$ and $i$,
$$\partial_i (f + b_\mu)(x) = \partial_i f(x) - \frac{\mu}{x_i}.$$
-/
theorem barrierCoordinateGradient_logBarrierObjective {f : (ι → ℝ) → ℝ} {x : ι → ℝ}
    (hf : DifferentiableAt ℝ f x) (hx : ∀ i, 0 < x i) (μ : ℝ) (i : ι) :
    barrierCoordinateGradient (fun y ↦ logBarrierObjective f y μ) x i =
      barrierCoordinateGradient f x i - μ / x i := by
  have hb := (Optimization.contDiffAt_logBarrier (n := 1) μ hx).differentiableAt (by simp)
  have hd := (hf.hasFDerivAt.add hb.hasFDerivAt).fderiv
  change fderiv ℝ (f + Optimization.logBarrier μ) x (Pi.single i 1) =
    barrierCoordinateGradient f x i - μ / x i
  rw [hd, add_apply, Optimization.fderiv_logBarrier_apply μ hx, barrierCoordinateGradient]
  have hsum : (∑ j, (x j)⁻¹ * (Pi.single i (1 : ℝ) : ι → ℝ) j) = (x i)⁻¹ := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  rw [hsum, div_eq_mul_inv]
  ring

omit [DecidableEq ι] in
/-- The quadratic form in (13.4.4) of [conn2000trust] is that of the Hessian of the barrier
objective. If $f$ is twice continuously differentiable and $x > 0$, then for every $\mu$ and
$d$,
$$\nabla^2 (f + b_\mu)(x)[d, d] = \nabla^2 f(x)[d, d] + \mu \sum_i \frac{d_i^2}{x_i^2}.$$
-/
theorem logBarrierObjective_hessian_apply {f : (ι → ℝ) → ℝ} {x : ι → ℝ}
    (hf : ContDiff ℝ 2 f) (hx : ∀ i, 0 < x i) (μ : ℝ) (d : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (fun y ↦ logBarrierObjective f y μ)) x d d =
      fderiv ℝ (fderiv ℝ f) x d d + μ * ∑ i, ((x i) ^ 2)⁻¹ * d i * d i := by
  let b := Optimization.logBarrier (ι := ι) μ
  have hpos : ∀ᶠ y in 𝓝 x, ∀ i, 0 < y i :=
    eventually_all.mpr fun i ↦ (continuous_apply i).continuousAt.eventually (lt_mem_nhds (hx i))
  have he : fderiv ℝ (fun y ↦ logBarrierObjective f y μ) =ᶠ[𝓝 x]
      fun y ↦ fderiv ℝ f y + fderiv ℝ b y := by
    filter_upwards [hpos] with y hy
    have hb := (Optimization.contDiffAt_logBarrier (n := 1) μ hy).differentiableAt (by simp)
    exact ((hf.differentiable (by norm_num) y).hasFDerivAt.add hb.hasFDerivAt).fderiv
  have hf' := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by simp) x
  have hb' := ((Optimization.contDiffAt_logBarrier (n := 2) μ hx).fderiv_right (m := 1)
    (by norm_num)).differentiableAt (by simp)
  rw [he.fderiv_eq]
  change (fderiv ℝ ((fderiv ℝ f + fderiv ℝ (Optimization.logBarrier μ)) :
    (ι → ℝ) → ((ι → ℝ) →L[ℝ] ℝ)) x) d d = _
  rw [(hf'.hasFDerivAt.add hb'.hasFDerivAt).fderiv, add_apply, add_apply]
  change _ + fderiv ℝ (fderiv ℝ (fun y ↦ logBarrier y μ)) x d d = _
  rw [logBarrier_hessian μ hx]

/-- The finite stopping implication in Theorem 13.4.2 of [conn2000trust]. Let
$f : \mathbb{R}^n \to \mathbb{R}$, $\mu \in \mathbb{R}$, $\varepsilon^D > 0$ and
$\varepsilon^E > 0$, and let $(x_j)$ be positive vectors with
$$\sum_i \left(\partial_i f(x_j) - \frac{\mu}{x_{j,i}}\right)^2 \to 0.$$
Let $(\lambda_j)$ be real numbers with $\limsup_j \lambda_j \ge 0$ that are cobounded from
below, and with $\lambda_j \|d\|^2 \le \nabla^2 f(x_j)[d, d] + \mu \sum_i d_i^2 / x_{j,i}^2$ for
all $j$ and $d$. Then infinitely many $x_j$ pass the stopping tests (13.4.3)–(13.4.5).

The inner analysis supplies the convergence of the squared residual and the nonnegative upper
limit of the curvature. The second gives arbitrarily late indices that pass the Hessian test.
Coboundedness from below is `Filter.IsCoboundedUnder (· ≤ ·)`, which makes the upper limit
meaningful. -/
theorem theorem_13_4_2_of_inner_limits {f : (ι → ℝ) → ℝ} {x : ℕ → ι → ℝ}
    {μ εD εE : ℝ} (hD : 0 < εD) (hE : 0 < εE)
    (hx : ∀ j i, 0 < x j i)
    (hgrad : Tendsto (fun j ↦ ∑ i, (barrierCoordinateGradient f (x j) i - μ / x j i) ^ 2)
      atTop (𝓝 0))
    {lamMin : ℕ → ℝ} (hbelow : atTop.IsCoboundedUnder (· ≤ ·) lamMin)
    (hlimsup : 0 ≤ limsup lamMin atTop)
    (hmin : ∀ j (d : ι → ℝ), lamMin j * (∑ i, (d i) ^ 2) ≤
      fderiv ℝ (fderiv ℝ f) (x j) d d + μ * ∑ i, ((x j i) ^ 2)⁻¹ * d i * d i) :
    ∃ᶠ j in atTop, BarrierSecondOrderStop f (x j) μ εD εE := by
  have hfreq := frequently_lt_of_lt_limsup hbelow ((neg_lt_zero.mpr hE).trans_le hlimsup)
  refine (hfreq.and_eventually (hgrad.eventually (gt_mem_nhds (sq_pos_of_pos hD)))).mono ?_
  intro j hj
  exact ⟨hx j, hj.2.le, fun d ↦
    (mul_le_mul_of_nonneg_right hj.1.le (Finset.sum_nonneg fun i _ ↦ sq_nonneg (d i))).trans
      (hmin j d)⟩

/-! ### Inner convergence of Algorithm 13.3.1 -/

section InnerConvergence

open Chapter06 Set
open Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The reduction of Section 13.3 of [conn2000trust] to basic trust-region convergence. Let $F$ be a
function that agrees with the barrier objective $\varphi$ at every iterate $x_j$ and every trial
point $x_j + s_j$ of a run of Algorithm 13.3.1. Then the run is a run of the basic trust-region
algorithm (Algorithm 6.1.1) for $F$, with the norm of $E$ and no extra decrease condition.

Each step of Algorithm 13.3.1 already passes the fraction-to-boundary test, so the guarded ratio
equals the ordinary ratio of $F$. The result is `ConnGouldToint.Chapter06.BTRRun`. -/
noncomputable def SecondPrimalBarrierInnerRun.toBTRRun
    {P : BTRParams} {C : Set E} {σ : ℝ} {φ F : E → ℝ}
    (r : SecondPrimalBarrierInnerRun P C σ φ)
    (hx : ∀ j, F (r.x j) = φ (r.x j))
    (hs : ∀ j, F (r.x j + r.s j) = φ (r.x j + r.s j)) :
    BTRRun F P (fun _ _ _ _ ↦ True) where
  x := r.x
  s := r.s
  Δ := r.Δ
  p := fun _ ↦ normSeminorm ℝ E
  norm_separates := fun _ _ h ↦ norm_eq_zero.mp h
  model := r.model
  delta_initial_pos := r.initial_radius_pos
  feasible := fun j ↦ by simpa [trustRegion] using r.step_feasible j
  sufficient_decrease := fun _ ↦ trivial
  predicted_pos := r.predicted_pos
  iterate_update := by
    intro j
    classical
    rw [r.iterate_update, primalBarrierRatio, ite_eq_left (r.trial_admissible j)]
    simp only [Optimization.acceptStep, btrRatio, Optimization.reductionRatio, hx, hs]
    split_ifs with h
    · exact ite_eq_left h
    · exact ite_eq_right h
  radius_update := by
    intro j
    have h := r.radius_update j
    rw [primalBarrierRatio, ite_eq_left (r.trial_admissible j)] at h
    simpa only [btrRatio, Optimization.reductionRatio, hx, hs] using h

private theorem barrier_fraction_mul_min_le {q a b c : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : q * a ≤ c) :
    q * min a b ≤ min a (min b c) :=
  le_min ((mul_le_mul_of_nonneg_left (min_le_left _ _) hq).trans
    (mul_le_of_le_one_left ha hq1))
    (le_min ((mul_le_mul_of_nonneg_left (min_le_right _ _) hq).trans
      (mul_le_of_le_one_left hb hq1)) ((mul_le_mul_of_nonneg_left (min_le_left _ _) hq).trans hc))

private theorem sq_min_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (min a b) ^ 2 = min (a ^ 2) (b ^ 2) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left ((sq_le_sq₀ ha hb).mpr h)]
  · rw [min_eq_right h, min_eq_right ((sq_le_sq₀ hb ha).mpr h)]

private theorem abs_sub_min_zero_le (a b : ℝ) : |min 0 a - min 0 b| ≤ |a - b| := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [min_eq_right ha, min_eq_right hb]
  · rw [min_eq_right ha, min_eq_left hb, sub_zero, abs_of_nonpos ha,
      abs_of_nonpos (sub_nonpos.mpr (ha.trans hb))]
    linarith
  · rw [min_eq_left ha, min_eq_right hb, abs_of_nonneg (sub_nonneg.mpr hb),
      abs_of_nonneg (sub_nonneg.mpr (hb.trans ha))]
    linarith
  · simp [min_eq_left ha, min_eq_left hb]

/-- The first- and second-order inner limits used in Theorem 13.4.2 of [conn2000trust] for Algorithm
13.3.1. Let $E$ be a nontrivial real Hilbert space, and consider a run of Algorithm 13.3.1 for
the barrier objective $\varphi$ with fraction $\sigma$, iterates $x_j$, steps $s_j$, radii
$\Delta_j$, models $m_j$, gradients $g_j$, curvature bounds $\beta_j$ and least-curvature
measures $\tau_j$. Let $F : E \to \mathbb{R}$ agree with $\varphi$ at all iterates and trial
points, be twice continuously differentiable and bounded below, with $\|\nabla^2 F\| \le L$. Let
$D, G, T > 0$. Assume for all $j$:
* $D \le (1 - \sigma) \operatorname{dist}(x_j, \partial C)$;
* $1 \le \beta_j \le K$, $\|g_j\| \le G$, $|\tau_j| \le T$ and
  $\tau_j = \min\{0, \lambda(\nabla^2 m_j(x_j))\}$;
* $F(x_j) = m_j(x_j)$, $D F(x_j) = D m_j(x_j)$ and $|F(x_j + s_j) - m_j(x_j + s_j)| \le K
  \Delta_j^2$;
* $m_j$ and $D m_j$ are differentiable on the segment $[x_j, x_j + s_j]$.

Assume further that for every $\varepsilon > 0$ there is $\delta > 0$ such that, for every $j$
with $\Delta_j \le \delta$ and every $y \in [x_j, x_j + s_j]$,
$$\|\nabla^2 F(y) - \nabla^2 F(x_j)\| + \|\nabla^2 m_j(y) - \nabla^2 m_j(x_j)\| \le
  \varepsilon,$$
and that AM.5 holds for $F$, the models and the iterates. Then $\|D F(x_j)\| \to 0$, and for
every $\varepsilon > 0$ there are infinitely many $j$ with
$\lambda(\nabla^2 F(x_j)) > -\varepsilon$.

Here $\lambda(H)$ is the infimum of $H[u, u]$ over unit vectors $u$,
`ConnGouldToint.Chapter06.leastUnitCurvature`, and AM.5 is
`ConnGouldToint.Chapter06.ModelHessianAgreement`. The fixed clearance and the uniform bounds on
the first- and second-order measures remove the caps of (13.3.2) at the cost of fixed factors. -/
theorem theorem_13_4_2_inner_of_extension [Nontrivial E]
    {P : BTRParams} {C : Set E} {σ : ℝ} {φ F : E → ℝ}
    (r : SecondPrimalBarrierInnerRun P C σ φ)
    (hx : ∀ j, F (r.x j) = φ (r.x j))
    (hs : ∀ j, F (r.x j + r.s j) = φ (r.x j + r.s j))
    (hf : ContDiff ℝ 2 F) (hlower : BddBelow (range F))
    {K L D G T : ℝ} (hD : 0 < D) (hG : 0 < G) (hT : 0 < T)
    (hclear : ∀ j, D ≤ (1 - σ) * infDist (r.x j) (frontier C))
    (hH : ∀ y, ‖fderiv ℝ (fderiv ℝ F) y‖ ≤ L)
    (hβ₁ : ∀ j, 1 ≤ r.β j) (hβK : ∀ j, r.β j ≤ K)
    (hGbd : ∀ j, ‖r.g j‖ ≤ G)
    (hτbd : ∀ j, |r.τ j| ≤ T)
    (hτ : ∀ j, r.τ j = min 0
      (leastUnitCurvature (fderiv ℝ (fderiv ℝ (r.model j)) (r.x j))))
    (hval : ∀ j, F (r.x j) = r.model j (r.x j))
    (hgrad : ∀ j, fderiv ℝ F (r.x j) = fderiv ℝ (r.model j) (r.x j))
    (herr : ∀ j, |F (r.x j + r.s j) - r.model j (r.x j + r.s j)| ≤ K * (r.Δ j) ^ 2)
    (hm : ∀ j y, y ∈ segment ℝ (r.x j) (r.x j + r.s j) →
      DifferentiableAt ℝ (r.model j) y)
    (hDm : ∀ j y, y ∈ segment ℝ (r.x j) (r.x j + r.s j) →
      DifferentiableAt ℝ (fderiv ℝ (r.model j)) y)
    (hvar : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ j, r.Δ j ≤ δ →
      ∀ y ∈ segment ℝ (r.x j) (r.x j + r.s j),
        ‖fderiv ℝ (fderiv ℝ F) y - fderiv ℝ (fderiv ℝ F) (r.x j)‖ +
        ‖fderiv ℝ (fderiv ℝ (r.model j)) y -
          fderiv ℝ (fderiv ℝ (r.model j)) (r.x j)‖ ≤ ε)
    (hagree : ModelHessianAgreement F r.model r.x) :
    Tendsto (fun j ↦ ‖fderiv ℝ F (r.x j)‖) atTop (𝓝 0) ∧
    ∀ ε > (0 : ℝ), ∃ᶠ j in atTop,
      -ε < leastUnitCurvature (fderiv ℝ (fderiv ℝ F) (r.x j)) := by
  let run := r.toBTRRun hx hs
  have hΔ (j : ℕ) : 0 < r.Δ j := run.delta_pos j
  have hβ (j : ℕ) := zero_lt_one.trans_le (hβ₁ j)
  have hg (j : ℕ) : r.g j = gradient F (r.x j) := by
    rw [r.gradient_model]
    unfold gradient
    rw [hgrad]
  let q := min 1 (D / G)
  have hq : 0 < q := lt_min zero_lt_one (div_pos hD hG)
  have hq1 : q ≤ 1 := min_le_left _ _
  let κ := min (1 / 2) (r.κ * q)
  have hκ : κ ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_min (by norm_num) (mul_pos r.decrease_constant hq),
      (min_le_left _ _).trans_lt (by norm_num)⟩
  have hdec (j : ℕ) : HasSufficientModelDecrease (r.model j) (r.x j) (r.s j)
      (gradient F (r.x j)) (r.β j) (r.Δ j) κ := by
    rw [← hg]
    refine ⟨hκ, ?_⟩
    have hGq : q * (‖r.g j‖ / r.β j) ≤ (1 - σ) * infDist (r.x j) (frontier C) := calc
      _ ≤ q * ‖r.g j‖ := mul_le_mul_of_nonneg_left (div_le_self (norm_nonneg _) (hβ₁ j)) hq.le
      _ ≤ q * G := mul_le_mul_of_nonneg_left (hGbd j) hq.le
      _ ≤ D := (le_div_iff₀ hG).mp (min_le_right _ _)
      _ ≤ _ := hclear j
    have hcap := barrier_fraction_mul_min_le hq.le hq1
      (div_nonneg (norm_nonneg _) (hβ j).le) (hΔ j).le hGq
    have hmain :=
      mul_le_mul_of_nonneg_left hcap (mul_nonneg r.decrease_constant.le (norm_nonneg (r.g j)))
    have hm : r.κ * (‖r.g j‖ * min (‖r.g j‖ / r.β j)
        (constrainedBarrierRadius (r.Δ j) σ (infDist (r.x j) (frontier C)))) ≤
        r.model j (r.x j) - r.model j (r.x j + r.s j) :=
      (mul_le_mul_of_nonneg_left (le_max_left _ _) r.decrease_constant.le).trans
        (r.sufficient_decrease j)
    calc
      _ ≤ (r.κ * q) * ‖r.g j‖ * min (‖r.g j‖ / r.β j) (r.Δ j) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _))
          (le_min (div_nonneg (norm_nonneg _) (hβ j).le) (hΔ j).le)
      _ = (r.κ * ‖r.g j‖) * (q * min (‖r.g j‖ / r.β j) (r.Δ j)) := by ring
      _ ≤ _ := by
        exact hmain.trans (by simpa only [constrainedBarrierRadius, mul_assoc] using hm)
  have hgradlim := theorem_6_4_6 run r.β hβ hβK hval hdec herr hlower hf hH
    (show (0 : ℝ) ≤ 1 by norm_num) (fun _ _ ↦ by simp [run, SecondPrimalBarrierInnerRun.toBTRRun])
  have hcrit : Tendsto (fun j ↦ ‖fderiv ℝ F (r.x j)‖) atTop (𝓝 0) := by
    simpa only [run, SecondPrimalBarrierInnerRun.toBTRRun, gradient, LinearIsometryEquiv.norm_map]
      using hgradlim
  have hsmall : smallRadiusModelAgreement run :=
    smallRadiusModelAgreement_of_hessians run hf hm hDm hval hgrad hcrit hagree
      zero_lt_one (fun j ↦ by
        change ‖r.s j‖ ≤ 1 * r.Δ j
        rw [one_mul]
        exact r.step_feasible j) hvar
  refine ⟨hcrit, ?_⟩
  let curv (j : ℕ) := min 0 (leastUnitCurvature (fderiv ℝ (fderiv ℝ F) (r.x j)))
  have ha : Tendsto (fun j ↦ |curv j - r.τ j|) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ ↦ abs_nonneg _) (fun j ↦ ?_) (hagree hcrit)
    rw [hτ]
    exact (abs_sub_min_zero_le _ _).trans
      (abs_sub_leastUnitCurvature_le _ _)
  let q₂ := min 1 (D ^ 2 / T ^ 2)
  have hq₂ : 0 < q₂ := lt_min zero_lt_one (div_pos (sq_pos_of_pos hD) (sq_pos_of_pos hT))
  have hsecond (j : ℕ) : HasNegativeCurvatureDecrease (r.model j) (r.x j) (r.s j)
      (r.τ j) (r.Δ j) (r.κ * q₂) := by
    refine ⟨mul_pos r.decrease_constant hq₂, fun hneg ↦ ?_⟩
    let b := (1 - σ) * infDist (r.x j) (frontier C)
    have hb : 0 < b := hD.trans_le (hclear j)
    have hTq : q₂ * (r.τ j) ^ 2 ≤ b ^ 2 := calc
      _ ≤ q₂ * T ^ 2 := mul_le_mul_of_nonneg_left
        (by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hT.le).mpr (hτbd j)) hq₂.le
      _ ≤ D ^ 2 := (le_div_iff₀ (sq_pos_of_pos hT)).mp (min_le_right _ _)
      _ ≤ _ := (sq_le_sq₀ hD.le hb.le).mpr (hclear j)
    have hcap := barrier_fraction_mul_min_le hq₂.le (min_le_left _ _)
      (sq_nonneg (r.τ j)) (sq_nonneg (r.Δ j)) hTq
    rw [← sq_min_of_nonneg (a := r.Δ j) (hΔ j).le hb.le] at hcap
    have hh := mul_le_mul_of_nonneg_left hcap
      (mul_nonneg r.decrease_constant.le (neg_nonneg.mpr hneg.le))
    have hm : r.κ * (-r.τ j * min ((r.τ j) ^ 2)
        (constrainedBarrierRadius (r.Δ j) σ (infDist (r.x j) (frontier C)) ^ 2)) ≤
        r.model j (r.x j) - r.model j (r.x j + r.s j) :=
      (mul_le_mul_of_nonneg_left (le_max_right _ _) r.decrease_constant.le).trans
        (r.sufficient_decrease j)
    rw [abs_of_neg hneg]
    calc
      _ = (r.κ * -r.τ j) * (q₂ * min ((r.τ j) ^ 2) ((r.Δ j) ^ 2)) := by ring
      _ ≤ _ := hh.trans (by simpa only [constrainedBarrierRadius, mul_assoc, b] using hm)
  intro ε hε
  exact
    (theorem_6_6_4 run (mul_pos r.decrease_constant hq₂) hval hlower hsmall ha hsecond ε hε).mono
    (fun j hj ↦ hj.trans_le (min_le_right _ _))

omit [CompleteSpace E] in
private theorem leastUnitCurvature_mul_norm_sq_le [Nontrivial E]
    (H : E →L[ℝ] E →L[ℝ] ℝ) (v : E) :
    leastUnitCurvature H * ‖v‖ ^ 2 ≤ H v v := by
  by_cases hv : v = 0
  · simp [hv]
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u : sphere (0 : E) 1 :=
    ⟨‖v‖⁻¹ • v, mem_sphere_zero_iff_norm.mpr (by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hvn.le), inv_mul_cancel₀ hvn.ne'])⟩
  have hlower : BddBelow (range (fun u : sphere (0 : E) 1 ↦ H u u)) := by
    refine ⟨-‖H‖, ?_⟩
    rintro _ ⟨w, rfl⟩
    have hw : ‖(w : E)‖ = 1 := norm_eq_of_mem_sphere w
    have h₁ := (H w).le_opNorm (w : E)
    have h₂ := H.le_opNorm (w : E)
    simp only [hw, mul_one, Real.norm_eq_abs] at h₁ h₂
    linarith [(abs_le.mp (h₁.trans h₂)).1]
  have hq := ciInf_le hlower u
  have hh := mul_le_mul_of_nonneg_right hq (sq_nonneg ‖v‖)
  change leastUnitCurvature H * ‖v‖ ^ 2 ≤ H (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) * ‖v‖ ^ 2 at hh
  simp only [map_smul, smul_apply, smul_eq_mul] at hh
  have heq : (‖v‖⁻¹ * (‖v‖⁻¹ * H v v)) * ‖v‖ ^ 2 = H v v := by field_simp
  simpa only [heq] using hh

end InnerConvergence

/-! ### Stopping in Euclidean coordinates -/

section EuclideanStopping

open Chapter06 Set

variable [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
private theorem barrier_euclidean_norm_sq (d : ι → ℝ) :
    ‖(WithLp.toLp 2 d : EuclideanSpace ℝ ι)‖ ^ 2 = ∑ i, (d i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
  · simp only [Real.norm_eq_abs, sq_abs]
  · exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The identity map from `ι → ℝ` with the sup norm to `EuclideanSpace ℝ ι`, as a continuous linear
map. It gives the Euclidean coordinates in (13.4.3)–(13.4.5) of [conn2000trust]. -/
noncomputable def barrierEuclideanCoordinates : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.toContinuousLinearMap

omit [DecidableEq ι] [Nonempty ι] in
private theorem barrier_composed_hessian {F : EuclideanSpace ℝ ι → ℝ}
    (hf : ContDiff ℝ 2 F) (x d : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (F ∘ barrierEuclideanCoordinates)) x d d =
      fderiv ℝ (fderiv ℝ F) (barrierEuclideanCoordinates x)
        (barrierEuclideanCoordinates d) (barrierEuclideanCoordinates d) := by
  let T : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι := barrierEuclideanCoordinates
  let A : (EuclideanSpace ℝ ι →L[ℝ] ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (ι → ℝ) (EuclideanSpace ℝ ι) ℝ).flip T
  have he : fderiv ℝ (F ∘ T) = fun y ↦ A (fderiv ℝ F (T y)) := by
    funext y
    exact (((hf.differentiable (by norm_num) (T y)).hasFDerivAt).comp y T.hasFDerivAt).fderiv
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) (T x)
  have hd := A.hasFDerivAt.comp x (hdf.hasFDerivAt.comp x T.hasFDerivAt)
  change HasFDerivAt (fun y ↦ A (fderiv ℝ F (T y))) _ x at hd
  change fderiv ℝ (fderiv ℝ (F ∘ T)) x d d = _
  rw [he, hd.fderiv]
  rfl

/-- Coordinate transfer for Theorem 13.4.2 of [conn2000trust]. Let
$f : \mathbb{R}^n \to \mathbb{R}$, let $F$ be a function on the Euclidean space $\mathbb{R}^n$,
let $\mu \in \mathbb{R}$, $\varepsilon^D > 0$ and $\varepsilon^E > 0$, and let $(x_j)$ be
positive vectors. Assume that for all $j$, $i$ and $d$,
$$\partial_i f(x_j) - \frac{\mu}{x_{j,i}} = D F(x_j) e_i, \qquad \nabla^2 f(x_j)[d, d] + \mu
  \sum_i \frac{d_i^2}{x_{j,i}^2} = \nabla^2 F(x_j)[d, d].$$
If $\|D F(x_j)\| \to 0$ and, for every $\varepsilon > 0$, infinitely many $j$ have
$\lambda(\nabla^2 F(x_j)) > -\varepsilon$, then infinitely many $x_j$ pass the stopping tests
(13.4.3)–(13.4.5).

The two identities are the transformation of the gradient and the Hessian under the Euclidean
coordinate map at the positive iterates. -/
theorem theorem_13_4_2_of_extension {f : (ι → ℝ) → ℝ} {F : EuclideanSpace ℝ ι → ℝ}
    {x : ℕ → EuclideanSpace ℝ ι} {μ εD εE : ℝ} (hD : 0 < εD) (hE : 0 < εE)
    (hx : ∀ j i, 0 < (x j).ofLp i)
    (hDmap : ∀ j i,
      barrierCoordinateGradient f (x j).ofLp i - μ / (x j).ofLp i =
        fderiv ℝ F (x j) (WithLp.toLp 2 (Pi.single i 1)))
    (hHmap : ∀ j (d : ι → ℝ),
      fderiv ℝ (fderiv ℝ f) (x j).ofLp d d + μ * ∑ i, (((x j).ofLp i) ^ 2)⁻¹ * d i * d i =
        fderiv ℝ (fderiv ℝ F) (x j) (WithLp.toLp 2 d) (WithLp.toLp 2 d))
    (hgrad : Tendsto (fun j ↦ ‖fderiv ℝ F (x j)‖) atTop (𝓝 0))
    (hcurv : ∀ ε > (0 : ℝ), ∃ᶠ j in atTop,
      -ε < leastUnitCurvature (fderiv ℝ (fderiv ℝ F) (x j))) :
    ∃ᶠ j in atTop, BarrierSecondOrderStop f (x j).ofLp μ εD εE := by
  have hDlim : Tendsto (fun j ↦
      ∑ i, (barrierCoordinateGradient f (x j).ofLp i - μ / (x j).ofLp i) ^ 2) atTop (𝓝 0) := by
    rw [← Finset.sum_const_zero (s := (Finset.univ : Finset ι))]
    apply tendsto_finsetSum Finset.univ
    intro i _
    let v : EuclideanSpace ℝ ι := WithLp.toLp 2 (Pi.single i 1)
    have hterm : Tendsto (fun j ↦
        barrierCoordinateGradient f (x j).ofLp i - μ / (x j).ofLp i) atTop (𝓝 0) :=
      squeeze_zero_norm' (a := fun j ↦ ‖fderiv ℝ F (x j)‖ * ‖v‖)
        (Eventually.of_forall fun j ↦ by rw [hDmap]; exact (fderiv ℝ F (x j)).le_opNorm v)
        (by simpa using hgrad.mul_const ‖v‖)
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using hterm.pow 2
  refine ((hcurv εE hE).and_eventually
    (hDlim.eventually (gt_mem_nhds (sq_pos_of_pos hD)))).mono ?_
  intro j hj
  refine ⟨hx j, hj.2.le, fun d ↦ ?_⟩
  rw [hHmap, ← barrier_euclidean_norm_sq]
  exact (mul_le_mul_of_nonneg_right hj.1.le (sq_nonneg _)).trans
    (leastUnitCurvature_mul_norm_sq_le _ _)

/-- Coordinate transfer for Theorem 13.4.2 of [conn2000trust] under local agreement with a smooth
extension. Let $f : \mathbb{R}^n \to \mathbb{R}$ and $F$ on the Euclidean space $\mathbb{R}^n$
be twice continuously differentiable, let $\mu \in \mathbb{R}$, $\varepsilon^D > 0$ and
$\varepsilon^E > 0$, and let $(x_j)$ be positive vectors. Assume that $F$ agrees with the
barrier objective $f + b_\mu$ in a neighborhood of each $x_j$. If $\|D F(x_j)\| \to 0$ and, for
every $\varepsilon > 0$, infinitely many $j$ have $\lambda(\nabla^2 F(x_j)) > -\varepsilon$,
then infinitely many $x_j$ pass the stopping tests (13.4.3)–(13.4.5).

Local agreement gives the two derivative identities of
`ConnGouldToint.Chapter13.theorem_13_4_2_of_extension`. -/
theorem theorem_13_4_2_of_local_extension {f : (ι → ℝ) → ℝ} {F : EuclideanSpace ℝ ι → ℝ}
    {x : ℕ → EuclideanSpace ℝ ι} {μ εD εE : ℝ} (hD : 0 < εD) (hE : 0 < εE)
    (hf : ContDiff ℝ 2 f) (hF : ContDiff ℝ 2 F) (hx : ∀ j i, 0 < (x j).ofLp i)
    (hlocal : ∀ j, (F ∘ barrierEuclideanCoordinates) =ᶠ[𝓝 (x j).ofLp]
      fun y ↦ logBarrierObjective f y μ)
    (hgrad : Tendsto (fun j ↦ ‖fderiv ℝ F (x j)‖) atTop (𝓝 0))
    (hcurv : ∀ ε > (0 : ℝ), ∃ᶠ j in atTop,
      -ε < leastUnitCurvature (fderiv ℝ (fderiv ℝ F) (x j))) :
    ∃ᶠ j in atTop, BarrierSecondOrderStop f (x j).ofLp μ εD εE := by
  have hTx (j : ℕ) : barrierEuclideanCoordinates (x j).ofLp = x j :=
    WithLp.toLp_ofLp 2 (x j)
  refine theorem_13_4_2_of_extension hD hE hx ?_ ?_ hgrad hcurv
  · intro j i
    rw [← barrierCoordinateGradient_logBarrierObjective
      (hf.differentiable (by norm_num) _) (hx j)]
    unfold barrierCoordinateGradient
    rw [← (hlocal j).fderiv_eq]
    have hh := ((hF.differentiable (by norm_num) _).hasFDerivAt.comp
      (x j).ofLp barrierEuclideanCoordinates.hasFDerivAt).fderiv
    rw [hh, ContinuousLinearMap.comp_apply, hTx]
    rfl
  · intro j d
    rw [← logBarrierObjective_hessian_apply hf (hx j), ← (hlocal j).fderiv.fderiv_eq,
      barrier_composed_hessian hF, hTx]
    rfl

omit [DecidableEq ι] in
/-- The corrected uniform boundary clearance for the inner runs of Theorem 13.4.2 of
[conn2000trust]. Let $n \ge 1$, $0 < \mu < \nu$, and let $f : \mathbb{R}^n \to \mathbb{R}$ be
twice continuously differentiable with $f \ge L$ and $\|\nabla^2 f\| \le H$ on $\mathbb{R}^n$.
Assume that $f(y) - \nu \sum_i \log y_i \ge A$ for all positive $y$. Then for every run of
Algorithm 13.2.1 on the Euclidean nonnegative orthant with the barrier objective $f + b_\mu$,
there is $\varepsilon \in (0, 1)$ such that every iterate has Euclidean distance at least
$\varepsilon$ from the boundary of the orthant.

The hypotheses are a global lower bound on the objective, AF.3 and AW.2 at the larger parameter
$\nu$. -/
theorem PrimalBarrierInnerRun.euclidean_clearance_of_global_lower
    {P : BTRParams} {f : (ι → ℝ) → ℝ} {σ μ ν L A H : ℝ}
    (r : PrimalBarrierInnerRun P
      ((WithLp.ofLp : EuclideanSpace ℝ ι → (ι → ℝ)) ⁻¹' Optimization.nonnegativeOrthant ι)
      σ (fun x ↦ logBarrierObjective f x.ofLp μ))
    (hμ : 0 < μ) (hν : μ < ν) (hf : ContDiff ℝ 2 f)
    (hlower : ∀ y, L ≤ f y) (hH : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (hbar : ∀ y : ι → ℝ, (∀ i, 0 < y i) → A ≤ logBarrierObjective f y ν) :
    ∃ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ j,
      ε ≤ infDist (r.x j) (frontier
        ((WithLp.ofLp : EuclideanSpace ℝ ι → (ι → ℝ)) ⁻¹' Optimization.nonnegativeOrthant ι)) := by
  let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).toHomeomorph
  let O := Optimization.nonnegativeOrthant ι
  let C := T ⁻¹' O
  have hCfront : T ⁻¹' frontier O = frontier C := T.preimage_frontier O
  have hxp (j : ℕ) (i : ι) : 0 < (r.x j).ofLp i := by
    have hh : r.x j ∈ interior C := r.interior_iterate j
    rw [← T.preimage_interior O] at hh
    have hh' : (r.x j).ofLp ∈ interior O := hh
    change (r.x j).ofLp ∈ interior (Set.univ.pi (fun _ : ι ↦ Ici (0 : ℝ))) at hh'
    rw [interior_pi_set Set.finite_univ] at hh'
    exact
      (by simpa only [Set.mem_pi, Set.mem_univ, true_implies, interior_Ici, Set.mem_Ioi] using hh' :
      ∀ i, 0 < (r.x j).ofLp i) i
  obtain ⟨ε, hε, hbound⟩ := logBarrier_sublevel_separation_of_global_lower
    hμ hν hf hlower hH hbar hxp (fun j ↦ r.objective_antitone (Nat.zero_le j))
  have hzero : (0 : EuclideanSpace ℝ ι) ∈ frontier C := by
    rw [← hCfront]
    apply Optimization.mem_frontier_nonnegativeOrthant.mpr
    exact ⟨fun _ ↦ le_rfl, Classical.arbitrary ι, rfl⟩
  refine ⟨ε, hε, fun j ↦ (le_infDist ⟨0, hzero⟩).mpr ?_⟩
  intro y hy
  have hy' : y.ofLp ∈ frontier O := by
    rw [← hCfront] at hy
    exact hy
  obtain ⟨_, i, hi⟩ := Optimization.mem_frontier_nonnegativeOrthant.mp hy'
  have hxi := (hbound j).trans (Optimization.infDist_frontier_le_coordinate (hxp j) i)
  have hnorm : |(r.x j - y).ofLp i| ≤ ‖r.x j - y‖ := by
    rw [EuclideanSpace.norm_eq]
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
    exact Finset.single_le_sum (fun k _ ↦ sq_nonneg ‖(r.x j - y).ofLp k‖) (Finset.mem_univ i)
  rw [WithLp.ofLp_sub, Pi.sub_apply, hi, sub_zero, abs_of_pos (hxp j i)] at hnorm
  exact hxi.trans (by simpa only [dist_eq_norm] using hnorm)

end EuclideanStopping


/-- A coordinate $i$ is **asymptotically active** for a family $(x_k)$ along a filter if
$x_{k,i} \to 0$. This is the definition before Theorem 13.4.3 of [conn2000trust]. -/
def AsymptoticallyActive {α : Type*} (l : Filter α) (x : α → ι → ℝ) (i : ι) : Prop :=
  Tendsto (fun k ↦ x k i) l (𝓝 0)

/-- A family $(x_k)$ is **consistently active** along a filter if each coordinate $i$ is either
asymptotically active or eventually satisfies $x_{k,i} \ge \delta$ for some $\delta > 0$. This
is the definition before Theorem 13.4.3 of [conn2000trust]. -/
def ConsistentlyActive {α : Type*} (l : Filter α) (x : α → ι → ℝ) : Prop :=
  ∀ i, AsymptoticallyActive l x i ∨ ∃ δ > 0, ∀ᶠ k in l, δ ≤ x k i

private theorem barrier_coordinate_residual_le {f : (ι → ℝ) → ℝ}
    {x : ι → ℝ} {μ εD εE : ℝ} (hs : BarrierSecondOrderStop f x μ εD εE)
    (hε : 0 ≤ εD) (i : ι) :
    |barrierCoordinateGradient f x i - μ / x i| ≤ εD := by
  apply (sq_le_sq₀ (abs_nonneg _) hε).mp
  rw [sq_abs]
  exact (Finset.single_le_sum (fun j _ ↦ sq_nonneg
    (barrierCoordinateGradient f x j - μ / x j)) (Finset.mem_univ i)).trans hs.2.1

private theorem barrier_ratio_tendsto_zero {α : Type*} {l : Filter α} {μ v : α → ℝ}
    (hμ : Tendsto μ l (𝓝 0)) (hμpos : ∀ k, 0 ≤ μ k)
    {δ : ℝ} (hδ : 0 < δ) (hv : ∀ᶠ k in l, δ ≤ v k) :
    Tendsto (fun k ↦ μ k / v k) l (𝓝 0) := by
  apply squeeze_zero' (g := fun k ↦ μ k / δ)
  · filter_upwards [hv] with k hk
    exact div_nonneg (hμpos k) (hδ.le.trans hk)
  · filter_upwards [hv] with k hk
    exact div_le_div_of_nonneg_left (hμpos k) hδ hk
  · simpa using hμ.div_const δ

omit [DecidableEq ι] in
private theorem barrier_hessian_correction_tendsto_zero {α : Type*} {l : Filter α}
    {x : α → ι → ℝ} {μ : α → ℝ} (hμ : Tendsto μ l (𝓝 0)) (hμpos : ∀ k, 0 ≤ μ k)
    (d : ι → ℝ) (hfree : ∀ i, d i ≠ 0 → ∃ δ > 0, ∀ᶠ k in l, δ ≤ x k i) :
    Tendsto (fun k ↦ μ k * ∑ i, ((x k i) ^ 2)⁻¹ * d i * d i) l (𝓝 0) := by
  simp only [Finset.mul_sum]
  rw [← Finset.sum_const_zero (s := (Finset.univ : Finset ι))]
  apply tendsto_finsetSum Finset.univ
  intro i _
  by_cases hi : d i = 0
  · simpa [hi] using (tendsto_const_nhds : Tendsto (fun _ : α ↦ (0 : ℝ)) l (𝓝 0))
  obtain ⟨δ, hδ, hxi⟩ := hfree i hi
  have hr : Tendsto (fun k ↦ μ k / (x k i) ^ 2) l (𝓝 0) :=
    barrier_ratio_tendsto_zero hμ hμpos (sq_pos_of_pos hδ)
      (hxi.mono fun k hk ↦ (sq_le_sq₀ hδ.le (hδ.le.trans hk)).mpr hk)
  simpa only [div_eq_mul_inv, mul_assoc, zero_mul] using (hr.mul_const (d i)).mul_const (d i)

/-- **Theorem 13.4.3** of [conn2000trust]. Let $f : \mathbb{R}^n \to \mathbb{R}$, and let
$x_k \in \mathbb{R}^n$ and numbers $\mu_k \ge 0$, $\varepsilon^D_k \ge 0$ and $\varepsilon^E_k$
be indexed by $k$ in a set with a filter $l$. Assume that $\mu_k$, $\varepsilon^D_k$ and
$\varepsilon^E_k$ tend to $0$ along $l$ and that each $x_k$ passes the stopping tests
(13.4.3)–(13.4.5) with $\mu_k$, $\varepsilon^D_k$ and $\varepsilon^E_k$. Then:
* for every $i$ and every $\eta > 0$, eventually $\partial_i f(x_k) \ge -\eta$;
* for every $i$ such that eventually $x_{k,i} \ge \delta$ for some $\delta > 0$,
  $\partial_i f(x_k) \to 0$;
* for every $d$ whose nonzero coordinates $i$ all satisfy eventually $x_{k,i} \ge \delta$ for
  some $\delta > 0$, and every $\eta > 0$, eventually $\nabla^2 f(x_k)[d, d] \ge -\eta$.

The lower-limit inequalities (13.4.9)–(13.4.11) are written in eventual form: each negative
tolerance $-\eta$ is eventually a lower bound. This also covers sequences whose lower limit is
$+\infty$. -/
theorem theorem_13_4_3 {α : Type*} {l : Filter α} {f : (ι → ℝ) → ℝ}
    {x : α → ι → ℝ} {μ εD εE : α → ℝ}
    (hμ : Tendsto μ l (𝓝 0)) (hμpos : ∀ k, 0 ≤ μ k)
    (hD : Tendsto εD l (𝓝 0)) (hDpos : ∀ k, 0 ≤ εD k)
    (hE : Tendsto εE l (𝓝 0))
    (hstop : ∀ k, BarrierSecondOrderStop f (x k) (μ k) (εD k) (εE k)) :
    (∀ i η, 0 < η → ∀ᶠ k in l, -η ≤ barrierCoordinateGradient f (x k) i) ∧
    (∀ i, (∃ δ > 0, ∀ᶠ k in l, δ ≤ x k i) →
      Tendsto (fun k ↦ barrierCoordinateGradient f (x k) i) l (𝓝 0)) ∧
    ∀ d : ι → ℝ, (∀ i, d i ≠ 0 → ∃ δ > 0, ∀ᶠ k in l, δ ≤ x k i) →
      ∀ η, 0 < η → ∀ᶠ k in l, -η ≤ fderiv ℝ (fderiv ℝ f) (x k) d d := by
  have herr (k : α) (i : ι) :=
    barrier_coordinate_residual_le (hstop k) (hDpos k) i
  refine ⟨?_, ?_, ?_⟩
  · intro i η hη
    filter_upwards [hD.eventually (gt_mem_nhds hη)] with k hk
    have hh := (abs_le.mp (herr k i)).1
    have hp := div_nonneg (hμpos k) ((hstop k).1 i).le
    linarith
  · intro i ⟨δ, hδ, hxi⟩
    have hr := barrier_ratio_tendsto_zero hμ hμpos hδ hxi
    have he : Tendsto (fun k ↦ barrierCoordinateGradient f (x k) i - μ k / x k i) l (𝓝 0) :=
      squeeze_zero_norm' (Eventually.of_forall fun k ↦ by simpa [Real.norm_eq_abs] using herr k i)
        hD
    simpa only [sub_add_cancel, zero_add] using he.add hr
  · intro d hd η hη
    have hc := barrier_hessian_correction_tendsto_zero hμ hμpos d hd
    have he := hE.mul_const (∑ i, (d i) ^ 2)
    have hec : Tendsto
        (fun k ↦ εE k * (∑ i, (d i) ^ 2) + μ k * ∑ i, ((x k i) ^ 2)⁻¹ * d i * d i)
        l (𝓝 0) := by
      simpa only [zero_mul, zero_add] using he.add hc
    filter_upwards [hec.eventually (gt_mem_nhds hη)] with k hk
    linarith [(hstop k).2.2 d]

/-- **Theorem 13.4.3** of [conn2000trust], (13.4.10)–(13.4.11) for a consistently active family. Let
$f$, $x_k$, $\mu_k$, $\varepsilon^D_k$, $\varepsilon^E_k$ and $l$ be as in
`ConnGouldToint.Chapter13.theorem_13_4_3`, and assume moreover that $(x_k)$ is consistently
active along $l$. Then $\partial_i f(x_k) \to 0$ for every coordinate $i$ that is not
asymptotically active, and for every $d$ with $d_i = 0$ on the asymptotically active coordinates
and every $\eta > 0$, eventually $\nabla^2 f(x_k)[d, d] \ge -\eta$.

All coordinates outside the asymptotically active set are eventually separated from the
boundary. -/
theorem theorem_13_4_3_consistentlyActive {α : Type*} {l : Filter α}
    {f : (ι → ℝ) → ℝ} {x : α → ι → ℝ} (ha : ConsistentlyActive l x)
    {μ εD εE : α → ℝ} (hμ : Tendsto μ l (𝓝 0)) (hμpos : ∀ k, 0 ≤ μ k)
    (hD : Tendsto εD l (𝓝 0)) (hDpos : ∀ k, 0 ≤ εD k)
    (hE : Tendsto εE l (𝓝 0))
    (hstop : ∀ k, BarrierSecondOrderStop f (x k) (μ k) (εD k) (εE k)) :
    (∀ i, ¬ AsymptoticallyActive l x i →
      Tendsto (fun k ↦ barrierCoordinateGradient f (x k) i) l (𝓝 0)) ∧
    ∀ d : ι → ℝ, (∀ i, AsymptoticallyActive l x i → d i = 0) →
      ∀ η, 0 < η → ∀ᶠ k in l, -η ≤ fderiv ℝ (fderiv ℝ f) (x k) d d := by
  obtain ⟨_, hg, hH⟩ := theorem_13_4_3 hμ hμpos hD hDpos hE hstop
  refine ⟨fun i hi ↦ hg i ((ha i).resolve_left hi), ?_⟩
  exact fun d hd ↦ hH d fun i hi ↦ (ha i).resolve_left fun h ↦ hi (hd i h)

/-- **Corollary 13.4.4** of [conn2000trust]. Let $l$ be a nontrivial filter, let
$f : \mathbb{R}^n \to \mathbb{R}$ be twice continuously differentiable, and let $x_k \to x^*$
along $l$. Let $\mu_k \ge 0$, $\varepsilon^D_k \ge 0$ and $\varepsilon^E_k$ tend to $0$ along
$l$, and assume that each $x_k$ passes the stopping tests (13.4.3)–(13.4.5) with $\mu_k$,
$\varepsilon^D_k$ and $\varepsilon^E_k$. Then $x^* \ge 0$, and for every $i$,
$\partial_i f(x^*) \ge 0$, with $\partial_i f(x^*) = 0$ if $x^*_i > 0$. Moreover,
$\nabla^2 f(x^*)[d, d] \ge 0$ for every $d$ with $d_i = 0$ whenever $x^*_i = 0$.

This is weak second-order criticality of the limit point: the Hessian is tested on the nullspace
of all active bounds. -/
theorem corollary_13_4_4 {α : Type*} {l : Filter α} [l.NeBot]
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    {x : α → ι → ℝ} {xstar : ι → ℝ} (hx : Tendsto x l (𝓝 xstar))
    {μ εD εE : α → ℝ} (hμ : Tendsto μ l (𝓝 0)) (hμpos : ∀ k, 0 ≤ μ k)
    (hD : Tendsto εD l (𝓝 0)) (hDpos : ∀ k, 0 ≤ εD k) (hE : Tendsto εE l (𝓝 0))
    (hstop : ∀ k, BarrierSecondOrderStop f (x k) (μ k) (εD k) (εE k)) :
    (∀ i, 0 ≤ xstar i) ∧
    (∀ i, 0 ≤ barrierCoordinateGradient f xstar i ∧
      (0 < xstar i → barrierCoordinateGradient f xstar i = 0)) ∧
    ∀ d : ι → ℝ, (∀ i, xstar i = 0 → d i = 0) → 0 ≤ fderiv ℝ (fderiv ℝ f) xstar d d := by
  have hxi (i : ι) : Tendsto (fun k ↦ x k i) l (𝓝 (xstar i)) :=
    ((continuous_apply i).tendsto xstar).comp hx
  have hfeas (i : ι) : 0 ≤ xstar i :=
    ge_of_tendsto (hxi i) (Eventually.of_forall fun k ↦ ((hstop k).1 i).le)
  have haway (i : ι) (hi : 0 < xstar i) : ∃ δ > 0, ∀ᶠ k in l, δ ≤ x k i :=
    ⟨xstar i / 2, half_pos hi, ((hxi i).eventually (lt_mem_nhds (half_lt_self hi))).mono
      fun _ h ↦ h.le⟩
  obtain ⟨hg₀, hg, hH⟩ := theorem_13_4_3 hμ hμpos hD hDpos hE hstop
  have hlimit_nonneg {u : α → ℝ} {a : ℝ} (hu : Tendsto u l (𝓝 a))
      (hb : ∀ η > 0, ∀ᶠ k in l, -η ≤ u k) : 0 ≤ a := by
    by_contra! hn
    have := ge_of_tendsto hu (hb (-a / 2) (by linarith))
    linarith
  refine ⟨hfeas, ?_, ?_⟩
  · intro i
    have hc : Continuous (fun y ↦ barrierCoordinateGradient f y i) :=
      (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have ht := (hc.tendsto xstar).comp hx
    exact ⟨hlimit_nonneg ht (hg₀ i), fun hi ↦ tendsto_nhds_unique ht (hg i (haway i hi))⟩
  · intro d hd
    have hf' := hf.fderiv_right (m := 1) (by norm_num)
    have hc : Continuous (fun y ↦ fderiv ℝ (fderiv ℝ f) y d d) :=
      ((hf'.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
    exact hlimit_nonneg ((hc.tendsto xstar).comp hx)
      (hH d fun i hi ↦ haway i (lt_of_le_of_ne (hfeas i) (fun hz ↦ hi (hd i hz.symm))))

end Outer


/-! ### Algorithm 13.4.1 -/

section PrimalOuterRun

open Chapter06 Set

/-- The closed nonnegative orthant of the Euclidean space $\mathbb{R}^n$. Its interior, the set of
positive vectors, is the domain of the logarithmic barrier in Algorithm 13.4.1 of
[conn2000trust]. -/
def logBarrierEuclideanDomain (ι : Type*) [Fintype ι] : Set (EuclideanSpace ℝ ι) :=
  WithLp.ofLp ⁻¹' Optimization.nonnegativeOrthant ι

private theorem mem_interior_logBarrierEuclideanDomain (x : EuclideanSpace ℝ ι) :
    x ∈ interior (logBarrierEuclideanDomain ι) ↔ ∀ i, 0 < x.ofLp i := by
  let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).toHomeomorph
  change x ∈ interior (T ⁻¹' Optimization.nonnegativeOrthant ι) ↔ _
  rw [← T.preimage_interior]
  change x.ofLp ∈ interior (Set.univ.pi (fun _ : ι ↦ Ici (0 : ℝ))) ↔ _
  rw [interior_pi_set Set.finite_univ]
  simp only [Set.mem_pi, Set.mem_univ, true_implies, interior_Ici, Set.mem_Ioi]

/-- The two step rules in Algorithm 13.4.1 of [conn2000trust]: the inner minimization uses either
Algorithm 13.2.1 or Algorithm 13.3.1. -/
inductive PrimalBarrierStepRule
  /-- Algorithm 13.2.1: compute the trial, and reject it if it fails the fraction-to-boundary test.
  -/
  | rejectOutside
  /-- Algorithm 13.3.1: impose the fraction-to-boundary test in the step calculation. -/
  | constrainTrial

/-- A finite primal log-barrier inner minimization in Algorithm 13.4.1 of [conn2000trust]. For an
objective $f$, a fraction $\sigma \in (0, 1)$, a barrier parameter $\mu$, inner iterates $x_j$
in the Euclidean space $\mathbb{R}^n$ and a terminal index $J$, it is a finite trace
(`ConnGouldToint.Chapter13.PrimalBarrierInnerPrefix`) on the nonnegative orthant for the barrier
objective $f + b_\mu$, together with a step rule and objective models $m^f_j$, such that for
every $j < J$:
* on the ball $\|v - x_j\| \le \Delta_j$, the model is $m_j(v) = m^f_j(v) + m^b(x_j, v - x_j)$,
  with the exact barrier model (13.4.2);
* $m^f_j$ and $D m^f_j$ are differentiable on this ball, $m^f_j(x_j) = f(x_j)$ and
  $D m^f_j(x_j) = D f(x_j)$;
* with $g = \nabla m_j(x_j)$, $\beta = 1 + \sup\{\|\nabla^2 m_j(v)\| : \|v - x_j\| \le
  \Delta_j\}$ and $\tau = \min\{0, \lambda(\nabla^2 m_j(x_j))\}$, the step satisfies AA.1 and
  AA.2 under the rule of Algorithm 13.2.1, and passes the fraction-to-boundary test and the
  decrease test (13.3.2) under the rule of Algorithm 13.3.1.

Moreover, the Hessians $\nabla^2 m^f_j$ are bounded on the positive points of the balls,
uniformly in $j < J$, and the decrease constant $\kappa$ lies in $(0, 1)$. The rule of Algorithm
13.2.1 uses the uncapped decrease and the guarded ratio; the rule of Algorithm 13.3.1 uses the
feasible capped decrease. -/
structure PrimalLogBarrierInnerPrefix (P : BTRParams) (f : (ι → ℝ) → ℝ)
    (σ μ : ℝ) (x : ℕ → EuclideanSpace ℝ ι) (J : ℕ)
    extends PrimalBarrierInnerPrefix P (logBarrierEuclideanDomain ι) σ
      (fun v ↦ logBarrierObjective f v.ofLp μ) x J where
  /-- The step rule, Algorithm 13.2.1 or Algorithm 13.3.1. -/
  rule : PrimalBarrierStepRule
  /-- The fraction $\sigma$ of the fraction-to-boundary test lies in $(0, 1)$. -/
  fraction : σ ∈ Ioo (0 : ℝ) 1
  /-- The objective models $m^f_j$. -/
  objectiveModel : ℕ → EuclideanSpace ℝ ι → ℝ
  /-- On the trust region of each inner iteration, the model is the objective model plus the exact
  barrier model (13.4.2) at the center. -/
  model_split : ∀ j < J, ∀ v ∈ closedBall (x j) (Δ j),
    model j v = objectiveModel j v + logBarrierModel (x j).ofLp (v - x j).ofLp μ
  /-- Each objective model and its derivative are differentiable on the trust region. -/
  objective_model_twice_diff : ∀ j < J,
    DifferentiableOn ℝ (objectiveModel j) (closedBall (x j) (Δ j)) ∧
    DifferentiableOn ℝ (fderiv ℝ (objectiveModel j)) (closedBall (x j) (Δ j))
  /-- Each objective model agrees with $f$ at the center. -/
  objective_model_value : ∀ j < J, objectiveModel j (x j) = f (x j).ofLp
  /-- Each objective model has the derivative of $f$ at the center. -/
  objective_model_derivative : ∀ j < J, fderiv ℝ (objectiveModel j) (x j) =
    fderiv ℝ (fun v : EuclideanSpace ℝ ι ↦ f v.ofLp) (x j)
  /-- The Hessians of the objective models are bounded on the positive points of the trust regions,
  uniformly in the inner iteration. -/
  objective_model_hessian_bound : ∃ K : ℝ, ∀ j < J, ∀ v ∈ closedBall (x j) (Δ j),
    v ∈ interior (logBarrierEuclideanDomain ι) → ‖fderiv ℝ (fderiv ℝ (objectiveModel j)) v‖ ≤ K
  /-- The decrease constant $\kappa$ of the step rules. -/
  κ : ℝ
  /-- The decrease constant $\kappa$ lies in $(0, 1)$. -/
  decrease_constant : κ ∈ Ioo (0 : ℝ) 1
  /-- Each step satisfies the decrease conditions of its step rule: AA.1 and AA.2 for Algorithm
  13.2.1, or the fraction-to-boundary test and (13.3.2) for Algorithm 13.3.1. -/
  step_rule : ∀ j < J,
    let g := gradient (model j) (x j)
    let β := 1 + sSup ((fun v ↦ ‖fderiv ℝ (fderiv ℝ (model j)) v‖) '' closedBall (x j) (Δ j))
    let τ := min 0 (leastUnitCurvature (fderiv ℝ (fderiv ℝ (model j)) (x j)))
    match rule with
    | .rejectOutside =>
      HasSufficientModelDecrease (model j) (x j) (s j) g β (Δ j) κ ∧
      HasNegativeCurvatureDecrease (model j) (x j) (s j) τ (Δ j) κ
    | .constrainTrial =>
      BarrierAdmissibleTrial (logBarrierEuclideanDomain ι) σ (x j) (x j + s j) ∧
      HasConstrainedBarrierDecrease (model j) (x j) (s j) g β (Δ j) σ
        (infDist (x j) (frontier (logBarrierEuclideanDomain ι))) τ κ

variable [DecidableEq ι]

/-- **Algorithm 13.4.1** of [conn2000trust]. Let $f : \mathbb{R}^n \to \mathbb{R}$. A **run of the
primal log-barrier method** consists of outer iterates $x_k$ in the Euclidean space
$\mathbb{R}^n$, barrier parameters $\mu_k$, fractions $\sigma_k$, forcing functions
$\varepsilon^D$ and $\varepsilon^E$, and finite inner minimizations with iterates $x_{k,j}$ and
terminal indices $J_k$, such that:
* $x_0 > 0$, $\mu_k > 0$ and $\mu_k \to 0$;
* $\varepsilon^D(\mu) > 0$ and $\varepsilon^E(\mu) > 0$ for $\mu > 0$, and both tend to $0$ as
  $\mu \to 0^+$;
* for each $k$, the inner iterates form a finite inner minimization
  (`ConnGouldToint.Chapter13.PrimalLogBarrierInnerPrefix`) with $\sigma_k$, $\mu_k$ and $J_k$,
  which starts at $x_{k,0} = x_k$ and ends at $x_{k+1} = x_{k,J_k}$;
* $x_{k+1}$ passes the stopping tests (13.4.3)–(13.4.5) with $\mu_k$, $\varepsilon^D(\mu_k)$ and
  $\varepsilon^E(\mu_k)$, and no $x_{k,j}$ with $j < J_k$ passes them.

**Generalization.** The terminal index $J_k$ may be zero: an inner minimization stops at once if
its starting point passes the stopping tests.

Each inner minimization starts at the current outer iterate and stops at the first point that
passes the tests. -/
structure PrimalLogBarrierOuterRun (P : BTRParams) (f : (ι → ℝ) → ℝ) where
  /-- The outer iterates $x_k$. -/
  x : ℕ → EuclideanSpace ℝ ι
  /-- The barrier parameters $\mu_k$. -/
  μ : ℕ → ℝ
  /-- The fractions $\sigma_k$ of the fraction-to-boundary tests. -/
  σ : ℕ → ℝ
  /-- The forcing function $\varepsilon^D$ of the dual residual test. -/
  εD : ℝ → ℝ
  /-- The forcing function $\varepsilon^E$ of the Hessian test. -/
  εE : ℝ → ℝ
  /-- The inner iterates $x_{k,j}$ of the $k$-th inner minimization. -/
  inner : ℕ → ℕ → EuclideanSpace ℝ ι
  /-- The terminal index $J_k$ of the $k$-th inner minimization. -/
  stopIndex : ℕ → ℕ
  /-- The initial outer iterate is positive. -/
  initial_positive : ∀ i, 0 < (x 0).ofLp i
  /-- The barrier parameters are positive. -/
  parameter_pos : ∀ k, 0 < μ k
  /-- The barrier parameters tend to $0$. -/
  parameter_limit : Tendsto μ atTop (𝓝 0)
  /-- The forcing functions are positive at every positive barrier parameter. -/
  forcing_pos : ∀ μ > 0, 0 < εD μ ∧ 0 < εE μ
  /-- The forcing functions tend to $0$ as the barrier parameter tends to $0$ from above. -/
  forcing_limit : Tendsto εD (𝓝[>] 0) (𝓝 0) ∧ Tendsto εE (𝓝[>] 0) (𝓝 0)
  /-- Each inner minimization is a finite primal log-barrier inner minimization with the fraction
  $\sigma_k$ and the parameter $\mu_k$. -/
  inner_trace : ∀ k, PrimalLogBarrierInnerPrefix P f (σ k) (μ k) (inner k) (stopIndex k)
  /-- Each inner minimization starts at the current outer iterate. -/
  start_inner : ∀ k, inner k 0 = x k
  /-- The next outer iterate is the last inner iterate. -/
  finish_inner : ∀ k, x (k + 1) = inner k (stopIndex k)
  /-- The next outer iterate passes the stopping tests (13.4.3)–(13.4.5). -/
  stopping_test : ∀ k, BarrierSecondOrderStop f (x (k + 1)).ofLp (μ k) (εD (μ k)) (εE (μ k))
  /-- No earlier inner iterate passes the stopping tests. -/
  first_stop : ∀ k j, j < stopIndex k →
    ¬ BarrierSecondOrderStop f (inner k j).ofLp (μ k) (εD (μ k)) (εE (μ k))

/-- **Algorithm 13.4.1** of [conn2000trust] as an instance of Algorithm 13.1.1. A run of the primal
log-barrier method is a run of the generic barrier method
`ConnGouldToint.Chapter13.BarrierOuterRun` on the nonnegative orthant, where each inner
minimization is a finite trust-region solve of the log-barrier objective with parameter $\mu_k$
by Algorithm 13.2.1 or Algorithm 13.3.1. -/
def PrimalLogBarrierOuterRun.toBarrierOuterRun {P : BTRParams} {f : (ι → ℝ) → ℝ}
    (r : PrimalLogBarrierOuterRun P f) :
    BarrierOuterRun (logBarrierEuclideanDomain ι)
      (fun v μ ↦ logBarrierObjective f v.ofLp μ)
      (fun μ φ x J ↦ φ = (fun v ↦ logBarrierObjective f v.ofLp μ) ∧
        ∃ σ, Nonempty (PrimalLogBarrierInnerPrefix P f σ μ x J)) where
  x := r.x
  μ := r.μ
  inner := r.inner
  stopIndex := r.stopIndex
  initial_interior := interior_subset_intrinsicInterior (𝕜 := ℝ)
    ((mem_interior_logBarrierEuclideanDomain _).mpr r.initial_positive)
  parameter_pos := r.parameter_pos
  parameter_limit := r.parameter_limit
  inner_start_interior := fun k ↦ interior_subset_intrinsicInterior (𝕜 := ℝ)
    (r.inner_trace k).initial_interior
  inner_solved := fun k ↦ ⟨rfl, r.σ k, ⟨r.inner_trace k⟩⟩
  inner_finish_interior := fun k ↦ interior_subset_intrinsicInterior (𝕜 := ℝ)
    ((r.inner_trace k).toPrimalBarrierInnerPrefix.interior_iterate le_rfl)
  outer_update := r.finish_inner

private theorem PrimalLogBarrierOuterRun.forcing_tendsto {P : BTRParams}
    {f : (ι → ℝ) → ℝ} (r : PrimalLogBarrierOuterRun P f) :
    Tendsto (fun k ↦ r.εD (r.μ k)) atTop (𝓝 0) ∧
      Tendsto (fun k ↦ r.εE (r.μ k)) atTop (𝓝 0) := by
  have hμ : Tendsto r.μ atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨r.parameter_limit, Eventually.of_forall r.parameter_pos⟩
  exact ⟨r.forcing_limit.1.comp hμ, r.forcing_limit.2.comp hμ⟩

/-- **Theorem 13.4.3** of [conn2000trust] for the completed iterations of Algorithm 13.4.1. For a
run of the primal log-barrier method, the iterates $x_{k+1}$ satisfy the three conclusions of
`ConnGouldToint.Chapter13.theorem_13_4_3` along $k \to \infty$.

The shifted sequence $x_{k+1}$ uses the barrier parameter $\mu_k$ that produced each completed
iterate. -/
theorem PrimalLogBarrierOuterRun.convergence {P : BTRParams} {f : (ι → ℝ) → ℝ}
    (r : PrimalLogBarrierOuterRun P f) :
    (∀ i η, 0 < η → ∀ᶠ k in atTop, -η ≤ barrierCoordinateGradient f (r.x (k + 1)).ofLp i) ∧
    (∀ i, (∃ δ > 0, ∀ᶠ k in atTop, δ ≤ (r.x (k + 1)).ofLp i) →
      Tendsto (fun k ↦ barrierCoordinateGradient f (r.x (k + 1)).ofLp i) atTop (𝓝 0)) ∧
    ∀ d : ι → ℝ, (∀ i, d i ≠ 0 → ∃ δ > 0, ∀ᶠ k in atTop, δ ≤ (r.x (k + 1)).ofLp i) →
      ∀ η, 0 < η → ∀ᶠ k in atTop, -η ≤ fderiv ℝ (fderiv ℝ f) (r.x (k + 1)).ofLp d d := by
  exact theorem_13_4_3 r.parameter_limit (fun k ↦ (r.parameter_pos k).le)
    r.forcing_tendsto.1 (fun k ↦ (r.forcing_pos _ (r.parameter_pos k)).1.le)
    r.forcing_tendsto.2 r.stopping_test

/-- **Corollary 13.4.4** of [conn2000trust] for completed runs of Algorithm 13.4.1. Let $f$ be twice
continuously differentiable, and consider a run of the primal log-barrier method for $f$. If
$j_k \to \infty$ and $x_{j_k + 1} \to x^*$, then $x^* \ge 0$, $\partial_i f(x^*) \ge 0$ for all
$i$ with equality when $x^*_i > 0$, and $\nabla^2 f(x^*)[d, d] \ge 0$ for every $d$ with
$d_i = 0$ whenever $x^*_i = 0$.

The Hessian inequality is on the nullspace of all active bounds. -/
theorem PrimalLogBarrierOuterRun.weakSecondOrder_limit {P : BTRParams}
    {f : (ι → ℝ) → ℝ} (r : PrimalLogBarrierOuterRun P f) (hf : ContDiff ℝ 2 f)
    {j : ℕ → ℕ} (hj : Tendsto j atTop atTop) {xstar : ι → ℝ}
    (hx : Tendsto (fun k ↦ (r.x (j k + 1)).ofLp) atTop (𝓝 xstar)) :
    (∀ i, 0 ≤ xstar i) ∧
    (∀ i, 0 ≤ barrierCoordinateGradient f xstar i ∧
      (0 < xstar i → barrierCoordinateGradient f xstar i = 0)) ∧
    ∀ d : ι → ℝ, (∀ i, xstar i = 0 → d i = 0) → 0 ≤ fderiv ℝ (fderiv ℝ f) xstar d d := by
  exact corollary_13_4_4 hf hx (r.parameter_limit.comp hj) (fun k ↦ (r.parameter_pos (j k)).le)
    (r.forcing_tendsto.1.comp hj) (fun k ↦ (r.forcing_pos _ (r.parameter_pos (j k))).1.le)
    (r.forcing_tendsto.2.comp hj) (fun k ↦ r.stopping_test (j k))

end PrimalOuterRun

/-! ### A counterexample to strong second-order criticality -/

section StrongCounterexample

private noncomputable def logBarrierCounterVector : Fin 4 → ℝ :=
  fun i ↦ if i = 0 then -3 else 1

private noncomputable def logBarrierCounterLinear : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  ∑ i, logBarrierCounterVector i • ContinuousLinearMap.proj i

/-- **Equation (13.4.14)** of [conn2000trust] in dimension four. With $v = (-3, 1, 1, 1)$, the
symmetric bilinear form on $\mathbb{R}^4$ is
$$H(x, d) = \sum_i x_i d_i - \frac18 (v \cdot x)(v \cdot d).$$
-/
noncomputable def logBarrierCounterHessian :
    (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) →L[ℝ] ℝ :=
  (∑ i, (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj i)) -
    (1 / 8 : ℝ) • logBarrierCounterLinear.smulRight logBarrierCounterLinear

private theorem logBarrierCounterHessian_apply (x d : Fin 4 → ℝ) :
    logBarrierCounterHessian x d =
      (∑ i, x i * d i) - (1 / 8 : ℝ) *
        (∑ i, logBarrierCounterVector i * x i) * (∑ i, logBarrierCounterVector i * d i) := by
  simp only [logBarrierCounterHessian, logBarrierCounterLinear, sub_apply, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

private theorem logBarrierCounterHessian_symm (x d : Fin 4 → ℝ) :
    logBarrierCounterHessian x d = logBarrierCounterHessian d x := by
  rw [logBarrierCounterHessian_apply, logBarrierCounterHessian_apply]
  simp only [mul_comm (x _) (d _)]
  ring

/-- **Equation (13.4.13)** of [conn2000trust]. The quadratic example $q(x) = \frac12 H(x, x)$ on
$\mathbb{R}^4$, with $H$ the bilinear form (13.4.14).

It is not regularized, and it is unbounded below on the nonnegative orthant. -/
noncomputable def logBarrierCounterObjective (x : Fin 4 → ℝ) : ℝ :=
  (1 / 2 : ℝ) * logBarrierCounterHessian x x

private theorem logBarrierCounterObjective_fderiv (x : Fin 4 → ℝ) :
    fderiv ℝ logBarrierCounterObjective x = logBarrierCounterHessian x := by
  have h := barrierQuadratic_hasFDerivAt (a := 0) (g := 0) logBarrierCounterHessian_symm x
  change fderiv ℝ (fun d ↦ (1 / 2 : ℝ) * logBarrierCounterHessian d d) x = _
  simpa only [zero_apply, zero_add] using h.fderiv

private theorem logBarrierCounterObjective_hessian (x : Fin 4 → ℝ) :
    fderiv ℝ (fderiv ℝ logBarrierCounterObjective) x = logBarrierCounterHessian := by
  rw [funext logBarrierCounterObjective_fderiv]
  exact logBarrierCounterHessian.hasFDerivAt.fderiv

/-- **Equations (13.4.18)–(13.4.19)** of [conn2000trust] and the example after Corollary 13.4.4. For
every $r > 0$, the point $(r, r, r, r)$ passes the stopping tests (13.4.3)–(13.4.5) for the
quadratic (13.4.13) with $\mu = r^2$ and $\varepsilon^D = \varepsilon^E = 0$. Nevertheless,
$\nabla^2 q(0)[e_1, e_1] < 0$ for the feasible direction $e_1$.

The points $(r, r, r, r)$ are exact stationary points of the barrier objective. The example
concerns the stopping tests themselves, and its quadratic is unbounded below on the orthant. In
Lean $e_1$ is `Pi.single 0 1`. -/
theorem logBarrierCounterObjective_stops_and_negative_direction :
    (∀ r > 0, BarrierSecondOrderStop logBarrierCounterObjective (fun _ ↦ r) (r ^ 2) 0 0) ∧
    fderiv ℝ (fderiv ℝ logBarrierCounterObjective) 0 (Pi.single 0 1) (Pi.single 0 1) < 0 := by
  have hz : ∑ i, logBarrierCounterVector i = 0 := by
    norm_num [Fin.sum_univ_four, logBarrierCounterVector, Pi.single_apply]
  have hz2 : ∑ i, (logBarrierCounterVector i) ^ 2 = 12 := by
    norm_num [Fin.sum_univ_four, logBarrierCounterVector, Pi.single_apply]
  constructor
  · intro r hr
    refine ⟨fun _ ↦ hr, ?_, ?_⟩
    · have hg (i : Fin 4) :
          barrierCoordinateGradient logBarrierCounterObjective (fun _ ↦ r) i = r := by
        rw [barrierCoordinateGradient, logBarrierCounterObjective_fderiv,
          logBarrierCounterHessian_apply, ← Finset.sum_mul]
        simp only [hz, zero_mul, mul_zero, sub_zero]
        simp [Pi.single_apply]
      simp [hg, pow_two, mul_div_cancel_right₀ r hr.ne']
    · intro d
      rw [logBarrierCounterObjective_hessian, logBarrierCounterHessian_apply]
      have hsum : r ^ 2 * (∑ i, (r ^ 2)⁻¹ * d i * d i) = ∑ i, d i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [show r ^ 2 * ((r ^ 2)⁻¹ * d i * d i) =
          (r ^ 2 * (r ^ 2)⁻¹) * d i * d i by ring, mul_inv_cancel₀ (pow_ne_zero _ hr.ne')]
        ring
      change -(0 : ℝ) * (∑ i, d i ^ 2) ≤ _
      rw [hsum]
      have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ logBarrierCounterVector d
      rw [hz2] at hc
      have hd : 0 ≤ ∑ i, (d i) ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg (d i)
      simp_rw [← pow_two] at *
      nlinarith
  · rw [logBarrierCounterObjective_hessian, logBarrierCounterHessian_apply]
    norm_num [Fin.sum_univ_four, logBarrierCounterVector, Pi.single_apply]

private def logBarrierCounterBump : ContDiffBump (0 : Fin 4 → ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

private noncomputable def logBarrierCounterOuter (x : Fin 4 → ℝ) : ℝ := ∑ i, (x i) ^ 2

/-- A bounded-below version of the example after Corollary 13.4.4 of [conn2000trust]. With a smooth
bump function $\psi$ on $\mathbb{R}^4$ that equals $1$ on the closed ball of radius $1$ about
$0$ and vanishes outside the ball of radius $2$,
$$\tilde q(x) = \psi(x) q(x) + (1 - \psi(x)) \|x\|_2^2,$$
where $q$ is the quadratic (13.4.13) and $\|x\|_2^2 = \sum_i x_i^2$.

It agrees with (13.4.13) near the origin and with a positive quadratic outside a ball. The balls
are those of the sup norm. -/
noncomputable def logBarrierCounterRegularized (x : Fin 4 → ℝ) : ℝ :=
  logBarrierCounterBump x * logBarrierCounterObjective x +
    (1 - logBarrierCounterBump x) * logBarrierCounterOuter x

private theorem logBarrierCounterRegularized_inner {x : Fin 4 → ℝ}
    (hx : x ∈ ball (0 : Fin 4 → ℝ) 1) :
    logBarrierCounterRegularized =ᶠ[𝓝 x] logBarrierCounterObjective := by
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  have hb : logBarrierCounterBump y = 1 :=
    logBarrierCounterBump.one_of_mem_closedBall (ball_subset_closedBall hy)
  simp [logBarrierCounterRegularized, hb]

private theorem logBarrierCounterRegularized_outer {x : Fin 4 → ℝ}
    (hx : x ∉ closedBall (0 : Fin 4 → ℝ) 2) :
    logBarrierCounterRegularized =ᶠ[𝓝 x] logBarrierCounterOuter := by
  filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hx] with y hy
  have hb : logBarrierCounterBump y = 0 :=
    logBarrierCounterBump.zero_of_le_dist (le_of_not_ge hy)
  simp [logBarrierCounterRegularized, hb]

private noncomputable def logBarrierCounterOuterHessian :
    (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) →L[ℝ] ℝ :=
  (2 : ℝ) • ∑ i, (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj i)

private theorem logBarrierCounterOuterHessian_apply (x d : Fin 4 → ℝ) :
    logBarrierCounterOuterHessian x d = 2 * ∑ i, x i * d i := by
  simp only [logBarrierCounterOuterHessian, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

private theorem logBarrierCounterOuter_hessian (x : Fin 4 → ℝ) :
    fderiv ℝ (fderiv ℝ logBarrierCounterOuter) x = logBarrierCounterOuterHessian := by
  have hs (v w : Fin 4 → ℝ) :
      logBarrierCounterOuterHessian v w = logBarrierCounterOuterHessian w v := by
    simp only [logBarrierCounterOuterHessian_apply, mul_comm (v _) (w _)]
  have he : logBarrierCounterOuter = fun v ↦
      (0 : ℝ) + (0 : (Fin 4 → ℝ) →L[ℝ] ℝ) v + (1 / 2 : ℝ) * logBarrierCounterOuterHessian v v := by
    funext v
    rw [logBarrierCounterOuterHessian_apply]
    simp only [zero_apply, zero_add, logBarrierCounterOuter, pow_two]
    ring
  have hd (v : Fin 4 → ℝ) :
      fderiv ℝ logBarrierCounterOuter v = logBarrierCounterOuterHessian v := by
    rw [he]
    simpa only [zero_add] using (barrierQuadratic_hasFDerivAt (a := 0) (g := 0) hs v).fderiv
  rw [funext hd]
  exact logBarrierCounterOuterHessian.hasFDerivAt.fderiv

/-- The bounded-below repair of the example after Corollary 13.4.4 of [conn2000trust]. The function
$\tilde q$ of `ConnGouldToint.Chapter13.logBarrierCounterRegularized` is twice continuously
differentiable, has a bounded Hessian and is bounded below. For every $\mu > 0$ its barrier
objective $\tilde q + b_\mu$ is bounded below on the positive orthant. For every $r \in (0, 1)$
the point $(r, r, r, r)$ passes the stopping tests (13.4.3)–(13.4.5) with $\mu = r^2$ and zero
tolerances. Finally $\nabla \tilde q(0) = 0$ and $\nabla^2 \tilde q(0)[e_1, e_1] < 0$.

The exact inner stopping points converge to $0$, which fails strong second-order criticality. -/
theorem logBarrierCounterRegularized_example :
    ContDiff ℝ 2 logBarrierCounterRegularized ∧
    (∃ M : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ logBarrierCounterRegularized) x‖ ≤ M) ∧
    (∃ m : ℝ, ∀ x, m ≤ logBarrierCounterRegularized x) ∧
    (∀ μ > 0, ∃ m : ℝ, ∀ x : Fin 4 → ℝ, (∀ i, 0 < x i) →
      m ≤ logBarrierObjective logBarrierCounterRegularized x μ) ∧
    (∀ r ∈ Set.Ioo (0 : ℝ) 1,
      BarrierSecondOrderStop logBarrierCounterRegularized (fun _ ↦ r) (r ^ 2) 0 0) ∧
    barrierCoordinateGradient logBarrierCounterRegularized 0 = 0 ∧
    fderiv ℝ (fderiv ℝ logBarrierCounterRegularized) 0 (Pi.single 0 1) (Pi.single 0 1) < 0 := by
  have hχ : ContDiff ℝ 2 logBarrierCounterBump := logBarrierCounterBump.contDiff
  have hf : ContDiff ℝ 2 logBarrierCounterObjective := by
    unfold logBarrierCounterObjective
    fun_prop
  have hout : ContDiff ℝ 2 logBarrierCounterOuter := by
    unfold logBarrierCounterOuter
    fun_prop
  have hF : ContDiff ℝ 2 logBarrierCounterRegularized :=
    (hχ.mul hf).add ((contDiff_const.sub hχ).mul hout)
  have hH := (hF.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  let K := closedBall (0 : Fin 4 → ℝ) 2
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨M, hM⟩ := (hK.image hH.norm).bddAbove
  obtain ⟨m, hm⟩ := (hK.image hF.continuous).bddBelow
  refine ⟨hF, ⟨max M ‖logBarrierCounterOuterHessian‖, ?_⟩, ⟨min m 0, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ K
    · exact (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    · rw [(logBarrierCounterRegularized_outer hx).fderiv.fderiv_eq,
        logBarrierCounterOuter_hessian]
      exact le_max_right _ _
  · intro x
    by_cases hx : x ∈ K
    · exact (min_le_left _ _).trans (hm ⟨x, hx, rfl⟩)
    · rw [(logBarrierCounterRegularized_outer hx).eq_of_nhds]
      exact (min_le_right _ _).trans (Finset.sum_nonneg fun i _ ↦ sq_nonneg (x i))
  · intro μ hμ
    refine ⟨min (m - 8 * μ) (-(μ ^ 2)), fun x hx ↦ ?_⟩
    by_cases hxK : x ∈ K
    · apply (min_le_left _ _).trans
      have hcoord (i : Fin 4) : x i ≤ 2 := by
        have hdist := (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 2)).mp hxK i
        simpa [Real.dist_eq, abs_of_pos (hx i)] using hdist
      have hsum : (∑ i, Real.log (x i)) ≤ 8 := by
        calc
          _ ≤ ∑ _i : Fin 4, (2 : ℝ) := Finset.sum_le_sum fun i _ ↦
            (Real.log_le_self (hx i).le).trans (hcoord i)
          _ = 8 := by norm_num
      have hlow := hm ⟨x, hxK, rfl⟩
      change m - 8 * μ ≤ logBarrierCounterRegularized x + (-μ) * ∑ i, Real.log (x i)
      rw [neg_mul]
      linarith [mul_le_mul_of_nonneg_left hsum hμ.le]
    · apply (min_le_right _ _).trans
      change -(μ ^ 2) ≤ logBarrierCounterRegularized x + (-μ) * ∑ i, Real.log (x i)
      rw [neg_mul]
      rw [(logBarrierCounterRegularized_outer hxK).eq_of_nhds]
      simp only [logBarrierCounterOuter, Finset.mul_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
      calc
        _ = ∑ _i : Fin 4, -(μ ^ 2 / 4) := by norm_num; ring
        _ ≤ _ := Finset.sum_le_sum fun i _ ↦ by
          have hlog := mul_le_mul_of_nonneg_left (Real.log_le_self (hx i).le) hμ.le
          nlinarith [sq_nonneg (x i - μ / 2)]
  · intro r hr
    have hx : (fun _ : Fin 4 ↦ r) ∈ ball (0 : Fin 4 → ℝ) 1 := by
      apply (dist_pi_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
      intro i
      simpa [Real.dist_eq, abs_of_pos hr.1] using hr.2
    have he := logBarrierCounterRegularized_inner hx
    obtain ⟨hs, _⟩ := logBarrierCounterObjective_stops_and_negative_direction
    simpa only [BarrierSecondOrderStop, barrierCoordinateGradient, he.fderiv_eq,
      he.fderiv.fderiv_eq] using hs r hr.1
  · funext i
    have he := logBarrierCounterRegularized_inner (mem_ball_self (by norm_num : (0 : ℝ) < 1))
    simp [barrierCoordinateGradient, he.fderiv_eq, logBarrierCounterObjective_fderiv]
  · have he := logBarrierCounterRegularized_inner (mem_ball_self (by norm_num : (0 : ℝ) < 1))
    rw [he.fderiv.fderiv_eq]
    exact logBarrierCounterObjective_stops_and_negative_direction.2

/-- A counterexample to strong second-order criticality of limit points after Corollary 13.4.4 of
[conn2000trust]. There are positive barrier parameters $\mu_k \to 0$ and points $x_k \to 0$ in
$\mathbb{R}^4$ such that each $x_k$ passes the stopping tests (13.4.3)–(13.4.5) for $\tilde q$
with $\mu_k$ and zero tolerances, $\nabla \tilde q(0) = 0$, and there is $d \ge 0$ with
$\nabla^2 \tilde q(0)[d, d] < 0$.

Here $\tilde q$ is the bounded-below repair
`ConnGouldToint.Chapter13.logBarrierCounterRegularized`, so a vanishing barrier sequence can
converge to a limit with negative curvature in a feasible direction. -/
theorem logBarrierCounterRegularized_convergent_stops :
    ∃ (x : ℕ → Fin 4 → ℝ) (μ : ℕ → ℝ),
      (∀ k, 0 < μ k) ∧ Tendsto μ atTop (𝓝 0) ∧ Tendsto x atTop (𝓝 0) ∧
      (∀ k, BarrierSecondOrderStop logBarrierCounterRegularized (x k) (μ k) 0 0) ∧
      barrierCoordinateGradient logBarrierCounterRegularized 0 = 0 ∧
      ∃ d : Fin 4 → ℝ, (∀ i, 0 ≤ d i) ∧
        fderiv ℝ (fderiv ℝ logBarrierCounterRegularized) 0 d d < 0 := by
  let r (k : ℕ) : ℝ := 1 / ((k : ℝ) + 2)
  have hr (k : ℕ) : r k ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨by dsimp [r]; positivity, ?_⟩
    dsimp [r]
    exact (div_lt_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have hlim : Tendsto r atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    simpa [r, Function.comp_def, Nat.cast_add, add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using h
  obtain ⟨_, _, _, _, hstop, hgrad, hneg⟩ := logBarrierCounterRegularized_example
  refine ⟨fun k _ ↦ r k, fun k ↦ r k ^ 2, fun k ↦ sq_pos_of_pos (hr k).1,
    by simpa using hlim.pow 2, tendsto_pi_nhds.mpr fun _ ↦ hlim,
    fun k ↦ hstop _ (hr k), hgrad, Pi.single 0 1, ?_, hneg⟩
  intro i
  by_cases hi : i = 0 <;> simp [hi]

end StrongCounterexample

/-! ### A counterexample to finite stopping in Theorem 13.4.2 -/

section PrimalEscape

open Set

private noncomputable def escapeGap (p : ℝ) : ℝ := p - Real.log p

private theorem escapeGap_drop {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    u ^ 2 / 8 ≤ escapeGap (1 + u) - escapeGap (1 + u / 2) := by
  let f (p : ℝ) := escapeGap p - (u / 4) * p
  have ha : 1 + u / 2 ≤ 1 + u := by linarith
  have hD (p : ℝ) (hp : 0 < p) :
      HasDerivAt f (1 - p⁻¹ - u / 4) p := by
    have hd := ((hasDerivAt_id p).sub (Real.hasDerivAt_log hp.ne')).sub
      ((hasDerivAt_id p).const_mul (u / 4))
    change HasDerivAt f (1 - p⁻¹ - u / 4 * 1) p at hd
    simpa only [mul_one] using hd
  have hm : MonotoneOn f (Icc (1 + u / 2) (1 + u)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun p hp ↦ (hD p (by linarith [hp.1])).continuousAt.continuousWithinAt
    · intro p hp
      have hp' := interior_subset hp
      exact (hD p (by linarith [hp'.1])).differentiableAt.differentiableWithinAt
    · intro p hp
      have hp' := interior_subset hp
      have hpos : 0 < p := by linarith [hp'.1]
      rw [(hD p hpos).deriv]
      have hinv : p⁻¹ ≤ 1 - u / 4 := by
        rw [← one_div]
        apply (div_le_iff₀ hpos).mpr
        have hmul := mul_le_mul_of_nonneg_right hp'.2 hu.le
        nlinarith [hp'.1, hmul, mul_nonneg hu.le (sub_nonneg.mpr hu1)]
      linarith
  have hh := hm ⟨le_rfl, ha⟩ ⟨ha, le_rfl⟩ ha
  unfold f at hh
  nlinarith

private noncomputable def escapeY (u : ℝ) : ℝ := u + u ^ 2

private noncomputable def escapeQ (u : ℝ) : ℝ := -(2 + 3 * u) / (4 * (1 + u))

private noncomputable def escapeA (u : ℝ) : ℝ :=
  -2 * (u * (1 + escapeQ u) + (1 + u) * escapeQ u + (escapeQ u) ^ 2 / 2 + u ^ 2 / 16)

/-- Two-coordinate run data for the counterexample to Theorem 13.4.2 of [conn2000trust] for
Algorithm 13.2.1. For a parameter $u$, the iterate is $(x, y) = (1/u, u + u^2)$, the trial point
is $(x', y') = (2/u, u/2 + u^2/4)$, and the barrier parameter is $1$. Write
$\psi(p) = p - \log p$, so that the barrier objective $xy - \log x - \log y$ equals $\psi(xy)$
and $xy = 1 + u$ at the iterate. With $Q(u) = -(2 + 3u) / (4(1 + u))$ and $A(u) = -2\left(u(1 +
Q) + (1 + u) Q + Q^2/2 + u^2/16\right)$, the total model in the displacement $(s, t)$ is
$$\psi(1 + u) + u^2 s + \frac{t}{1 + u} + \frac12 \left(A(u) u^2 s^2 + 2 s t +
  \frac{t^2}{y^2}\right).$$
The structure records that the trial is admissible and that this model, its decrease, its
curvature and the actual decrease have the stated properties.

The true objective is $xy$, the barrier model is the exact logarithmic Taylor quadratic, and the
objective model adds a centered quadratic $a s^2 / 2$ to the bilinear objective. The decrease
tests use a curvature bound and the least quadratic curvature. -/
structure PrimalBarrierEscapeTrial (u : ℝ) : Prop where
  /-- The parameter is positive. -/
  parameter_pos : 0 < u
  /-- The parameter is at most $1/2$. -/
  parameter_le_half : u ≤ 1 / 2
  /-- The trial point is positive, passes the fraction-to-boundary test
  $\min\{x', y'\} \ge \frac14 \min\{x, y\}$, and lies in the trust region of radius $2x$. -/
  trial_inside :
    let x := 1 / u
    let y := escapeY u
    let x' := 2 * x
    let y' := escapeY (u / 2)
    0 < x' ∧ 0 < y' ∧ (1 / 4 : ℝ) * min x y ≤ min x' y' ∧
      (x' - x) ^ 2 + (y' - y) ^ 2 ≤ (2 * x) ^ 2
  /-- The total model is the objective model $(x + s)(y + t) + a s^2 / 2$, with
  $a = (A(u) - 1) u^2$, plus the logarithmic Taylor model at $(x, y)$. -/
  model_matches :
    let x := 1 / u
    let y := escapeY u
    let a := (escapeA u - 1) * u ^ 2
    let g₁ := u ^ 2
    let g₂ := 1 / (1 + u)
    ∀ s t : ℝ,
      ((x + s) * (y + t) + a * s ^ 2 / 2 +
        (-Real.log x - Real.log y - s / x - t / y +
          (s ^ 2 / x ^ 2 + t ^ 2 / y ^ 2) / 2)) =
      escapeGap (1 + u) + g₁ * s + g₂ * t +
        ((escapeA u * u ^ 2) * s ^ 2 + 2 * s * t + t ^ 2 / y ^ 2) / 2
  /-- The Hessian coefficient of the objective model is bounded: $|(A(u) - 1) u^2| \le 9$. -/
  objective_model_bound : |(escapeA u - 1) * u ^ 2| ≤ 9
  /-- The predicted decrease of the trial is $u^2 / 16$. -/
  predicted_decrease :
    let x := 1 / u
    let y := escapeY u
    let s := x
    let t := escapeY (u / 2) - y
    show Prop from -(u ^ 2 * s + (1 / (1 + u)) * t +
      ((escapeA u * u ^ 2) * s ^ 2 + 2 * s * t + t ^ 2 / y ^ 2) / 2) = u ^ 2 / 16
  /-- The predicted decrease satisfies AA.1 and AA.2 with the constant $1/32768$, the model gradient
  norm $\sqrt{u^4 + (1 + u)^{-2}}$ and the radius $2/u$, for every curvature bound
  $\beta \ge 1/y^2$ and every curvature measure $\tau \ge -12 u^2$. -/
  sufficient_decrease :
    let g := Real.sqrt ((u ^ 2) ^ 2 + (1 / (1 + u)) ^ 2)
    let y := escapeY u
    ∀ β τ : ℝ, 1 / y ^ 2 ≤ β → -(12 * u ^ 2) ≤ τ →
      (1 / 32768 : ℝ) * max (g * min (g / β) (2 / u))
        (-τ * min (τ ^ 2) ((2 / u) ^ 2)) ≤ u ^ 2 / 16
  /-- The model curvature is at least $-12 u^2$: the model Hessian form is bounded below by
  $-12 u^2 (s^2 + t^2)$. -/
  curvature_lower :
    let y := escapeY u
    ∀ s t : ℝ, -(12 * u ^ 2) * (s ^ 2 + t ^ 2) ≤
      (escapeA u * u ^ 2) * s ^ 2 + 2 * s * t + t ^ 2 / y ^ 2
  /-- The actual decrease is at least $u^2 / 8$: $\psi(1 + u) - \psi(1 + u/2) \ge u^2 / 8$. -/
  actual_decrease : u ^ 2 / 8 ≤ escapeGap (1 + u) - escapeGap (1 + u / 2)
  /-- The second component $1/(1 + u)$ of the model gradient exceeds the stopping tolerance $1/4$.
  -/
  fails_gradient_stop : 1 / 4 < 1 / (1 + u)

private theorem escapeQ_bounds {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1 / 2) :
    -1 ≤ escapeQ u ∧ escapeQ u ≤ 0 := by
  have hpos : 0 < 4 * (1 + u) := by positivity
  unfold escapeQ
  exact ⟨(le_div_iff₀ hpos).mpr (by linarith), div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le⟩

private theorem escapeA_bound {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1 / 2) :
    |escapeA u| ≤ 8 := by
  obtain ⟨hq₁, hq₂⟩ := escapeQ_bounds hu hu1
  have hq3 : (escapeQ u) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq₂) (show 0 ≤ 1 + escapeQ u by linarith)]
  unfold escapeA
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg hu.le (show 0 ≤ 1 + escapeQ u by linarith),
    mul_nonneg hu.le (neg_nonneg.mpr hq₂), mul_nonneg hu.le (sub_nonneg.mpr hu1),
    sq_nonneg (escapeQ u), sq_nonneg u]

private theorem escape_trial {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1 / 2) :
    PrimalBarrierEscapeTrial u := by
  have hu0 := hu.ne'
  have hp : 0 < 1 + u := by positivity
  have hy : 0 < escapeY u := by unfold escapeY; positivity
  have hy' : 0 < escapeY (u / 2) := by unfold escapeY; positivity
  have hY : escapeY u = u * (1 + u) := by unfold escapeY; ring
  have hQ : escapeY (u / 2) - escapeY u = escapeY u * escapeQ u := by
    rw [hY, escapeQ]
    unfold escapeY
    field_simp [hp.ne']
    ring
  have hA := abs_le.mp (escapeA_bound hu hu1)
  refine ⟨hu, hu1, ?_, ?_, ?_, ?_, ?_, ?_, escapeGap_drop hu (by linarith), ?_⟩
  · dsimp only
    refine ⟨by positivity, hy', ?_, ?_⟩
    · apply le_min
      · exact ((mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)).trans
          (by nlinarith [div_pos zero_lt_one hu]))
      · exact ((mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)).trans
          (by unfold escapeY; nlinarith))
    · have hyub : escapeY u ≤ 1 := by
        unfold escapeY; nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu1)]
      have hyt : escapeY (u / 2) ≤ escapeY u := by
        unfold escapeY
        nlinarith
      have hxs : (1 : ℝ) ≤ 1 / u := (le_div_iff₀ hu).mpr (by linarith)
      have ht1 : |escapeY (u / 2) - escapeY u| ≤ 1 := by
        rw [abs_of_nonpos (sub_nonpos.mpr hyt)]
        linarith
      have ht2 := (sq_le_sq₀ (abs_nonneg _) (zero_le_one : (0 : ℝ) ≤ 1)).mpr ht1
      rw [sq_abs] at ht2
      have hx2 := (sq_le_sq₀ zero_le_one (zero_le_one.trans hxs)).mpr hxs
      nlinarith
  · dsimp only
    intro s t
    have hxy : (1 / u) * escapeY u = 1 + u := by rw [hY]; field_simp [hu0]
    have hlog := Real.log_mul (show (1 / u : ℝ) ≠ 0 by positivity) hy.ne'
    rw [hxy] at hlog
    unfold escapeGap
    rw [hlog]
    rw [hY]
    field_simp [hu0, hp.ne']
    ring
  · have hh : |escapeA u - 1| ≤ 9 := by
      apply abs_le.mpr
      constructor <;> linarith [hA.1, hA.2]
    rw [abs_mul, abs_of_nonneg (sq_nonneg u)]
    exact (mul_le_mul_of_nonneg_right hh (sq_nonneg u)).trans
      (by nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu1)])
  · dsimp only
    rw [hQ, hY, escapeA]
    field_simp [hu0, hp.ne']
    ring
  · dsimp only
    intro β τ hβ hτ
    have hβp := (show 0 < 1 / escapeY u ^ 2 by positivity).trans_le hβ
    have hYb : escapeY u ≤ 2 * u := by
      unfold escapeY
      nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu1)]
    have hβinv : β⁻¹ ≤ 4 * u ^ 2 := calc
      _ ≤ (1 / escapeY u ^ 2)⁻¹ := inv_anti₀ (by positivity) hβ
      _ = escapeY u ^ 2 := by simp
      _ ≤ _ := by
        have h := (sq_le_sq₀ hy.le (by positivity : 0 ≤ 2 * u)).mpr hYb
        nlinarith
    let g := Real.sqrt ((u ^ 2) ^ 2 + (1 / (1 + u)) ^ 2)
    have hg : 0 ≤ g := Real.sqrt_nonneg _
    have hg2 : g ^ 2 ≤ 2 := by
      dsimp only [g]
      rw [Real.sq_sqrt (by positivity)]
      have hu2 : u ^ 2 ≤ 1 := by nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu1)]
      have hi : 1 / (1 + u) ≤ 1 := (div_le_one hp).mpr (by linarith)
      have h₁ := (sq_le_sq₀ (sq_nonneg u) zero_le_one).mpr hu2
      have h₂ := (sq_le_sq₀ (by positivity : 0 ≤ 1 / (1 + u)) zero_le_one).mpr hi
      linarith
    have hfirst : g * min (g / β) (2 / u) ≤ 8 * u ^ 2 := calc
      _ ≤ g * (g / β) := mul_le_mul_of_nonneg_left (min_le_left _ _) hg
      _ = g ^ 2 * β⁻¹ := by rw [div_eq_mul_inv]; ring
      _ ≤ _ := by
        have h := mul_le_mul hg2 hβinv (inv_nonneg.mpr hβp.le) (by norm_num : (0 : ℝ) ≤ 2)
        nlinarith
    have hsecond : -τ * min (τ ^ 2) ((2 / u) ^ 2) ≤ 1728 * u ^ 2 := by
      by_cases ht : 0 ≤ τ
      · exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht)
          (le_min (sq_nonneg _) (sq_nonneg _))).trans (by positivity)
      · have hneg : 0 ≤ -τ := by linarith
        have ha : -τ ≤ 12 * u ^ 2 := by linarith
        have h₁ := mul_le_mul_of_nonneg_left (min_le_left (τ ^ 2) ((2 / u) ^ 2)) hneg
        have h₂ : (-τ) ^ 3 ≤ (12 * u ^ 2) ^ 3 := pow_le_pow_left₀ hneg ha 3
        have hu2 : u ^ 2 ≤ 1 := by nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu1)]
        have hu4 : (u ^ 2) ^ 2 ≤ 1 := by
          simpa using (sq_le_sq₀ (sq_nonneg u) zero_le_one).mpr hu2
        have h₃ := mul_le_mul_of_nonneg_right hu4 (sq_nonneg u)
        exact h₁.trans (by nlinarith [h₂, h₃])
    change (1 / 32768 : ℝ) * max (g * min (g / β) (2 / u)) _ ≤ _
    have hmax : max (g * min (g / β) (2 / u)) (-τ * min (τ ^ 2) ((2 / u) ^ 2)) ≤ 1728 * u ^ 2 :=
      max_le (hfirst.trans (by nlinarith [sq_nonneg u])) hsecond
    nlinarith [hmax, sq_nonneg u]
  · dsimp only
    intro s t
    have h₁ : -8 * u ^ 2 ≤ escapeA u * u ^ 2 :=
      mul_le_mul_of_nonneg_right hA.1 (sq_nonneg u)
    have hYb : escapeY u ≤ 2 * u := by
      unfold escapeY
      nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu1)]
    have h₂ : escapeY u ^ 2 ≤ 4 * u ^ 2 := by
      have h := (sq_le_sq₀ hy.le (by positivity : 0 ≤ 2 * u)).mpr hYb
      nlinarith
    have hsq : 0 ≤ (escapeY u * s + t / escapeY u) ^ 2 := sq_nonneg _
    have hcross : -(escapeY u ^ 2) * s ^ 2 ≤ 2 * s * t + t ^ 2 / escapeY u ^ 2 := by
      have he : (escapeY u * s + t / escapeY u) ^ 2 =
          escapeY u ^ 2 * s ^ 2 + 2 * s * t + t ^ 2 / escapeY u ^ 2 := by
        field_simp [hy.ne']
        ring
      rw [he] at hsq
      linarith
    have h₃ := mul_le_mul_of_nonneg_right h₁ (sq_nonneg s)
    have h₄ := mul_le_mul_of_nonneg_right h₂ (sq_nonneg s)
    nlinarith [mul_nonneg (sq_nonneg u) (sq_nonneg t)]
  · apply (lt_div_iff₀ hp).mpr
    linarith

/-- The printed hypotheses of Theorem 13.4.2 of [conn2000trust] permit an unbounded sequence of
accepted trials. There is a sequence $u_j \to 0$ with $u_{j+1} = u_j / 2$ such that each $u_j$
gives the trial data of `ConnGouldToint.Chapter13.PrimalBarrierEscapeTrial`, the ratio of the
actual decrease $\psi(1 + u_j) - \psi(1 + u_{j+1})$ to the predicted decrease $u_j^2 / 16$ is at
least $2$, and for every $\mu > 0$ the barrier objective $xy - \mu(\log x + \log y)$ is bounded
below on the positive quadrant.

The iterates are $(1/u_j, u_j + u_j^2)$, and the proof takes $u_j = 2^{-(j+1)}$. The radius
doubles, the objective models have a uniform Hessian bound, and the second component of the
barrier gradient stays above the stopping tolerance. -/
theorem theorem_13_4_2_unbounded_run_counterexample :
    ∃ u : ℕ → ℝ,
      Tendsto u atTop (𝓝 0) ∧
      (∀ j, u (j + 1) = u j / 2) ∧
      (∀ j, PrimalBarrierEscapeTrial (u j)) ∧
      (∀ j, 2 ≤ (escapeGap (1 + u j) - escapeGap (1 + u (j + 1))) / (u j ^ 2 / 16)) ∧
      (∀ μ > 0, ∃ A : ℝ, ∀ x y : ℝ, 0 < x → 0 < y →
        A ≤ x * y - μ * (Real.log x + Real.log y)) := by
  let u (j : ℕ) := (1 / 2 : ℝ) ^ (j + 1)
  have hu (j : ℕ) : 0 < u j := by dsimp [u]; positivity
  have hu1 (j : ℕ) : u j ≤ 1 / 2 := by
    simp only [u, pow_succ]
    exact mul_le_of_le_one_left (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))
  have hup (j : ℕ) : u (j + 1) = u j / 2 := by
    simp only [u, pow_succ]
    ring
  refine ⟨u, ?_, hup, fun j ↦ escape_trial (hu j) (hu1 j), ?_, ?_⟩
  · simpa only [u, pow_succ, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2 : ℝ)
  · intro j
    rw [hup]
    exact (le_div_iff₀ (by positivity)).mpr (by
      linarith [escapeGap_drop (hu j) (show u j ≤ 1 by linarith [hu1 j])])
  · intro μ hμ
    refine ⟨μ - μ * Real.log μ, fun x y hx hy ↦ ?_⟩
    rw [← Real.log_mul hx.ne' hy.ne']
    have hp := mul_pos hx hy
    have hl := Real.log_le_sub_one_of_pos (div_pos hp hμ)
    rw [Real.log_div hp.ne' hμ.ne'] at hl
    have hm := mul_le_mul_of_nonneg_left hl hμ.le
    simp only [mul_sub, mul_div_cancel₀ _ hμ.ne', mul_one] at hm
    linarith

private abbrev EscapeSpace := EuclideanSpace ℝ (Fin 2)

private noncomputable def escapePoint (u : ℝ) : EscapeSpace :=
  WithLp.toLp 2 ![1 / u, escapeY u]

private def escapeOrthant : Set EscapeSpace :=
  WithLp.ofLp ⁻¹' Optimization.nonnegativeOrthant (Fin 2)

private noncomputable def escapeObjective (p : EscapeSpace) : ℝ :=
  escapeGap (p.ofLp 0 * p.ofLp 1)

private noncomputable def escapeModel (u : ℝ) (p : EscapeSpace) : ℝ :=
  let s := p.ofLp 0 - 1 / u
  let t := p.ofLp 1 - escapeY u
  escapeGap (1 + u) + u ^ 2 * s + (1 / (1 + u)) * t +
    ((escapeA u * u ^ 2) * s ^ 2 + 2 * s * t + t ^ 2 / (escapeY u) ^ 2) / 2

private theorem escapeOrthant_interior {p : EscapeSpace}
    (hp : ∀ i, 0 < p.ofLp i) : p ∈ interior escapeOrthant := by
  let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).toHomeomorph
  change p ∈ interior (T ⁻¹' Optimization.nonnegativeOrthant (Fin 2))
  rw [← T.preimage_interior]
  change p.ofLp ∈ interior (Set.univ.pi (fun _ : Fin 2 ↦ Ici (0 : ℝ)))
  rw [interior_pi_set Set.finite_univ]
  simpa only [Set.mem_pi, Set.mem_univ, true_implies, interior_Ici, Set.mem_Ioi] using hp

private theorem escape_norm_sq (v : EscapeSpace) :
    ‖v‖ ^ 2 = (v.ofLp 0) ^ 2 + (v.ofLp 1) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
  · simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  · exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

private theorem escape_coord_abs_le_norm (v : EscapeSpace) (i : Fin 2) :
    |v.ofLp i| ≤ ‖v‖ := by
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs, escape_norm_sq]
  fin_cases i
  · change (v.ofLp 0) ^ 2 ≤ (v.ofLp 0) ^ 2 + (v.ofLp 1) ^ 2
    linarith [sq_nonneg (v.ofLp 1)]
  · change (v.ofLp 1) ^ 2 ≤ (v.ofLp 0) ^ 2 + (v.ofLp 1) ^ 2
    linarith [sq_nonneg (v.ofLp 0)]

private theorem escapeOrthant_boundary_dist {p : EscapeSpace} (hp : ∀ i, 0 < p.ofLp i) :
    infDist p (frontier escapeOrthant) = min (p.ofLp 0) (p.ofLp 1) := by
  let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).toHomeomorph
  have hfront : frontier escapeOrthant =
      T ⁻¹' frontier (Optimization.nonnegativeOrthant (Fin 2)) := (T.preimage_frontier _).symm
  have hz : (0 : EscapeSpace) ∈ frontier escapeOrthant := by
    rw [hfront]
    exact Optimization.mem_frontier_nonnegativeOrthant.mpr ⟨fun _ ↦ le_rfl, 0, rfl⟩
  apply le_antisymm
  · by_cases h : p.ofLp 0 ≤ p.ofLp 1
    · let z : EscapeSpace := WithLp.toLp 2 ![0, p.ofLp 1]
      have hz' : z ∈ frontier escapeOrthant := by
        rw [hfront]
        apply Optimization.mem_frontier_nonnegativeOrthant.mpr
        refine ⟨?_, 0, rfl⟩
        intro i
        fin_cases i
        · exact le_rfl
        · exact (hp 1).le
      have hdist : dist p z ≤ p.ofLp 0 := by
        rw [dist_eq_norm]
        apply (sq_le_sq₀ (norm_nonneg _) (hp 0).le).mp
        rw [escape_norm_sq]
        change (p.ofLp 0 - 0) ^ 2 + (p.ofLp 1 - p.ofLp 1) ^ 2 ≤ _
        ring_nf
        exact le_rfl
      exact (infDist_le_dist_of_mem hz').trans (hdist.trans_eq (min_eq_left h).symm)
    · let z : EscapeSpace := WithLp.toLp 2 ![p.ofLp 0, 0]
      have hz' : z ∈ frontier escapeOrthant := by
        rw [hfront]
        apply Optimization.mem_frontier_nonnegativeOrthant.mpr
        refine ⟨?_, 1, rfl⟩
        intro i
        fin_cases i
        · exact (hp 0).le
        · exact le_rfl
      have hdist : dist p z ≤ p.ofLp 1 := by
        rw [dist_eq_norm]
        apply (sq_le_sq₀ (norm_nonneg _) (hp 1).le).mp
        rw [escape_norm_sq]
        change (p.ofLp 0 - p.ofLp 0) ^ 2 + (p.ofLp 1 - 0) ^ 2 ≤ _
        ring_nf
        exact le_rfl
      exact (infDist_le_dist_of_mem hz').trans (hdist.trans_eq (min_eq_right (le_of_not_ge h)).symm)
  · apply (le_infDist ⟨0, hz⟩).mpr
    intro z hz'
    rw [hfront] at hz'
    obtain ⟨_, i, hi⟩ := Optimization.mem_frontier_nonnegativeOrthant.mp hz'
    have hi' : z.ofLp i = 0 := hi
    have hnorm := escape_coord_abs_le_norm (p - z) i
    rw [WithLp.ofLp_sub, Pi.sub_apply, hi', sub_zero, abs_of_pos (hp i)] at hnorm
    rw [dist_eq_norm]
    fin_cases i
    · exact (min_le_left _ _).trans hnorm
    · exact (min_le_right _ _).trans hnorm

private theorem escapePoint_positive {u : ℝ} (hu : 0 < u) :
    ∀ i, 0 < (escapePoint u).ofLp i := by
  intro i
  fin_cases i
  · change 0 < 1 / u
    positivity
  · change 0 < escapeY u
    unfold escapeY
    positivity

private theorem escapeObjective_at_point {u : ℝ} (hu : 0 < u) :
    escapeObjective (escapePoint u) = escapeGap (1 + u) := by
  change escapeGap ((1 / u) * escapeY u) = _
  congr 1
  unfold escapeY
  field_simp [hu.ne']

private theorem escapeModel_predicted {u : ℝ} (h : PrimalBarrierEscapeTrial u) :
    escapeModel u (escapePoint u) - escapeModel u (escapePoint (u / 2)) = u ^ 2 / 16 := by
  have he : 1 / (u / 2) - 1 / u = 1 / u := by
    field_simp [h.parameter_pos.ne']
    ring
  have hcenter : escapeModel u (escapePoint u) = escapeGap (1 + u) := by
    simp [escapeModel, escapePoint]
  rw [hcenter]
  change escapeGap (1 + u) -
    (escapeGap (1 + u) + u ^ 2 * (1 / (u / 2) - 1 / u) +
      1 / (1 + u) * (escapeY (u / 2) - escapeY u) +
      ((escapeA u * u ^ 2) * (1 / (u / 2) - 1 / u) ^ 2 +
        2 * (1 / (u / 2) - 1 / u) * (escapeY (u / 2) - escapeY u) +
        (escapeY (u / 2) - escapeY u) ^ 2 / (escapeY u) ^ 2) / 2) = _
  rw [he]
  have hp := h.predicted_decrease
  dsimp only at hp
  linarith

private def escapeL (i : Fin 2) : EscapeSpace →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).toContinuousLinearMap

private noncomputable def escapeG (u : ℝ) : EscapeSpace →L[ℝ] ℝ :=
  (u ^ 2) • escapeL 0 + (1 / (1 + u)) • escapeL 1

private noncomputable def escapeH (u : ℝ) : EscapeSpace →L[ℝ] EscapeSpace →L[ℝ] ℝ :=
  (escapeA u * u ^ 2) • (escapeL 0).smulRight (escapeL 0) +
    (escapeL 0).smulRight (escapeL 1) + (escapeL 1).smulRight (escapeL 0) +
    (1 / (escapeY u) ^ 2) • (escapeL 1).smulRight (escapeL 1)

private theorem escapeH_apply (u : ℝ) (v w : EscapeSpace) :
    escapeH u v w = (escapeA u * u ^ 2) * v.ofLp 0 * w.ofLp 0 +
      v.ofLp 0 * w.ofLp 1 + v.ofLp 1 * w.ofLp 0 +
      (1 / (escapeY u) ^ 2) * v.ofLp 1 * w.ofLp 1 := by
  simp [escapeH, escapeL, mul_assoc]

private theorem escapeModel_fderiv (u : ℝ) (p : EscapeSpace) :
    fderiv ℝ (escapeModel u) p = escapeG u + escapeH u (p - escapePoint u) := by
  let m (d : EscapeSpace) := escapeGap (1 + u) + escapeG u d + (1 / 2 : ℝ) * escapeH u d d
  have he : escapeModel u = fun p ↦ m (p - escapePoint u) := by
    funext v
    unfold m
    rw [escapeH_apply]
    have hL (i : Fin 2) (p : EscapeSpace) : escapeL i p = p.ofLp i := rfl
    simp only [escapeModel, escapeG, add_apply, smul_apply, smul_eq_mul, hL,
      WithLp.ofLp_sub, Pi.sub_apply]
    have hx0 : (escapePoint u).ofLp 0 = 1 / u := rfl
    have hx1 : (escapePoint u).ofLp 1 = escapeY u := rfl
    simp only [hx0, hx1]
    ring
  have hs (v w : EscapeSpace) : escapeH u v w = escapeH u w v := by
    simp only [escapeH_apply]
    ring
  rw [he]
  have hd := (barrierQuadratic_hasFDerivAt (a := escapeGap (1 + u)) (g := escapeG u) hs
    (p - escapePoint u)).comp p ((hasFDerivAt_id p).sub_const (escapePoint u))
  change HasFDerivAt (fun v ↦ m (v - escapePoint u)) _ p at hd
  rw [hd.fderiv, ContinuousLinearMap.comp_id]

private theorem escapeModel_hessian (u : ℝ) (p : EscapeSpace) :
    fderiv ℝ (fderiv ℝ (escapeModel u)) p = escapeH u := by
  rw [funext (escapeModel_fderiv u)]
  have hd := ((escapeH u).hasFDerivAt (x := p - escapePoint u)).comp p
    ((hasFDerivAt_id p).sub_const (escapePoint u))
  have hd' := (hd.const_add (escapeG u)).fderiv
  change fderiv ℝ (fun v ↦ escapeG u + escapeH u (v - escapePoint u)) p = _ at hd'
  simpa only [ContinuousLinearMap.comp_id] using hd'

private theorem escapeModel_gradient_norm (u : ℝ) :
    ‖gradient (escapeModel u) (escapePoint u)‖ =
      Real.sqrt ((u ^ 2) ^ 2 + (1 / (1 + u)) ^ 2) := by
  let g : EscapeSpace := WithLp.toLp 2 ![u ^ 2, 1 / (1 + u)]
  have hg : gradient (escapeModel u) (escapePoint u) = g := by
    apply (InnerProductSpace.toDual ℝ EscapeSpace).injective
    ext d
    change inner ℝ (gradient (escapeModel u) (escapePoint u)) d = inner ℝ g d
    rw [inner_gradient_left, escapeModel_fderiv, sub_self, map_zero, add_zero,
      EuclideanSpace.inner_eq_star_dotProduct]
    simp [escapeG, escapeL, g, dotProduct, Fin.sum_univ_two]
    ring
  rw [hg, EuclideanSpace.norm_eq]
  simp [g, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- AA.1 and AA.2 for the Euclidean quadratic model of the counterexample to Theorem 13.4.2 of
[conn2000trust]. For trial data with parameter $u$, let $x = (1/u, u + u^2)$, let
$s = (2/u, u/2 + u^2/4) - x$, let $H$ be the model Hessian at $x$, $\beta = 1 + \|H\|$ and
$\tau = \min\{0, \lambda(H)\}$. Then $s$ satisfies the sufficient decrease condition AA.1 with
the model gradient, $\beta$, the radius $2/u$ and the constant $1/32768$, and the
negative-curvature decrease condition AA.2 with $\tau$, the same radius and the same constant. -/
theorem escapeModel_adequate_decrease {u : ℝ} (h : PrimalBarrierEscapeTrial u) :
    let x := escapePoint u
    let s := escapePoint (u / 2) - x
    let H := fderiv ℝ (fderiv ℝ (escapeModel u)) x
    let β := 1 + ‖H‖
    let τ := min 0 (Chapter06.leastUnitCurvature H)
    Chapter06.HasSufficientModelDecrease (escapeModel u) x s
      (gradient (escapeModel u) x) β (2 / u) (1 / 32768) ∧
    Chapter06.HasNegativeCurvatureDecrease (escapeModel u) x s τ (2 / u) (1 / 32768) := by
  dsimp only
  rw [escapeModel_hessian]
  let e : EscapeSpace := WithLp.toLp 2 ![0, 1]
  have he : ‖e‖ = 1 := by simp [e, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hYe : 1 / (escapeY u) ^ 2 ≤ ‖escapeH u‖ := by
    have h₁ := ((escapeH u) e).le_opNorm e
    have h₂ := (escapeH u).le_opNorm e
    rw [he, mul_one] at h₁ h₂
    have hq : escapeH u e e = 1 / (escapeY u) ^ 2 := by simp [e, escapeH_apply]
    rw [hq, Real.norm_of_nonneg (by positivity)] at h₁
    exact h₁.trans h₂
  have hβ : 1 / (escapeY u) ^ 2 ≤ 1 + ‖escapeH u‖ := hYe.trans (by linarith)
  have ht : -(12 * u ^ 2) ≤ min 0 (Chapter06.leastUnitCurvature (escapeH u)) := by
    let : Nonempty (sphere (0 : EscapeSpace) 1) :=
      ⟨⟨e, mem_sphere_zero_iff_norm.mpr he⟩⟩
    apply le_min (by nlinarith [sq_nonneg u])
    apply le_ciInf
    intro v
    have hb := h.curvature_lower ((v : EscapeSpace).ofLp 0) ((v : EscapeSpace).ofLp 1)
    rw [← escape_norm_sq, norm_eq_of_mem_sphere v, one_pow, mul_one] at hb
    rw [escapeH_apply]
    convert hb using 1
    ring
  have hdec := h.sufficient_decrease _ _ hβ ht
  have hpred : escapeModel u (escapePoint u) -
      escapeModel u (escapePoint u + (escapePoint (u / 2) - escapePoint u)) = u ^ 2 / 16 := by
    rw [show escapePoint u + (escapePoint (u / 2) - escapePoint u) = escapePoint (u / 2) by abel]
    exact escapeModel_predicted h
  constructor
  · refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    rw [hpred, mul_assoc, escapeModel_gradient_norm]
    exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)).trans hdec
  · refine ⟨by norm_num, fun ht ↦ ?_⟩
    rw [hpred, abs_of_neg ht, mul_assoc]
    exact (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)).trans hdec

private noncomputable def escapeFModel (u a : ℝ) (p : EscapeSpace) : ℝ :=
  barrierBilinearObjective p.ofLp + a * (p.ofLp 0 - 1 / u) ^ 2 / 2

private noncomputable def escapeFCross : EscapeSpace →L[ℝ] EscapeSpace →L[ℝ] ℝ :=
  (escapeL 0).smulRight (escapeL 1) + (escapeL 1).smulRight (escapeL 0)

private noncomputable def escapeFDiagonal : EscapeSpace →L[ℝ] EscapeSpace →L[ℝ] ℝ :=
  (escapeL 0).smulRight (escapeL 0)

private noncomputable def escapeFH (a : ℝ) : EscapeSpace →L[ℝ] EscapeSpace →L[ℝ] ℝ :=
  escapeFCross + a • escapeFDiagonal

private noncomputable def escapeFG (u : ℝ) : EscapeSpace →L[ℝ] ℝ :=
  escapeY u • escapeL 0 + (1 / u) • escapeL 1

private theorem escapeFModel_fderiv (u a : ℝ) (p : EscapeSpace) :
    fderiv ℝ (escapeFModel u a) p = escapeFG u + escapeFH a (p - escapePoint u) := by
  let m (s : EscapeSpace) := (1 / u) * escapeY u + escapeFG u s +
    (1 / 2 : ℝ) * escapeFH a s s
  have he : escapeFModel u a = fun p ↦ m (p - escapePoint u) := by
    funext v
    have hx0 : (escapePoint u).ofLp 0 = 1 / u := rfl
    have hx1 : (escapePoint u).ofLp 1 = escapeY u := rfl
    simp [m, escapeFModel, barrierBilinearObjective, escapeFG, escapeFH, escapeFCross,
      escapeFDiagonal, escapeL, hx0, hx1]
    ring
  have hs (v w : EscapeSpace) : escapeFH a v w = escapeFH a w v := by
    simp [escapeFH, escapeFCross, escapeFDiagonal, escapeL]
    ring
  rw [he]
  have hd := (barrierQuadratic_hasFDerivAt (a := (1 / u) * escapeY u) (g := escapeFG u) hs
    (p - escapePoint u)).comp p ((hasFDerivAt_id p).sub_const (escapePoint u))
  change HasFDerivAt (fun v ↦ m (v - escapePoint u)) _ p at hd
  rw [hd.fderiv, ContinuousLinearMap.comp_id]

private theorem escapeFModel_hessian (u a : ℝ) (p : EscapeSpace) :
    fderiv ℝ (fderiv ℝ (escapeFModel u a)) p = escapeFH a := by
  rw [funext (escapeFModel_fderiv u a)]
  have hd := ((escapeFH a).hasFDerivAt (x := p - escapePoint u)).comp p
    ((hasFDerivAt_id p).sub_const (escapePoint u))
  have hd' := (hd.const_add (escapeFG u)).fderiv
  change fderiv ℝ (fun v ↦ escapeFG u + escapeFH a (v - escapePoint u)) p = _ at hd'
  simpa only [ContinuousLinearMap.comp_id] using hd'

/-- AM.1–AM.4i and AM.6 for the counterexample models of Theorem 13.4.2 of [conn2000trust]. There is
$B$ such that for every parameter $u$ with trial data there is a twice continuously
differentiable objective model $m^f$ with $m^f(x) = x_1 x_2$ and $D m^f(x) = D(x_1 x_2)$ at the
iterate $x = (1/u, u + u^2)$, with $\|\nabla^2 m^f\| \le B$ everywhere and constant Hessian,
such that the total model has constant Hessian and equals $m^f$ plus the logarithmic Taylor
model (13.4.2) at $x$ with barrier parameter $1$. -/
theorem escapeModel_source_models :
    ∃ B : ℝ, ∀ u, PrimalBarrierEscapeTrial u → ∃ mf : EscapeSpace → ℝ,
      ContDiff ℝ 2 mf ∧
      mf (escapePoint u) = barrierBilinearObjective (escapePoint u).ofLp ∧
      fderiv ℝ mf (escapePoint u) =
        fderiv ℝ (fun p : EscapeSpace ↦ barrierBilinearObjective p.ofLp) (escapePoint u) ∧
      (∀ p, ‖fderiv ℝ (fderiv ℝ mf) p‖ ≤ B) ∧
      (∀ p q, fderiv ℝ (fderiv ℝ mf) p = fderiv ℝ (fderiv ℝ mf) q) ∧
      (∀ p q, fderiv ℝ (fderiv ℝ (escapeModel u)) p =
        fderiv ℝ (fderiv ℝ (escapeModel u)) q) ∧
      ∀ p, escapeModel u p = mf p +
        logBarrierModel (escapePoint u).ofLp (p - escapePoint u).ofLp 1 := by
  refine ⟨‖escapeFCross‖ + 9 * ‖escapeFDiagonal‖, fun u h ↦ ?_⟩
  let a := (escapeA u - 1) * u ^ 2
  have hx0 : (escapePoint u).ofLp 0 = 1 / u := rfl
  have hx1 : (escapePoint u).ofLp 1 = escapeY u := rfl
  refine ⟨escapeFModel u a, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold escapeFModel barrierBilinearObjective
    have h₀ : ContDiff ℝ 2 (escapeL 0) := (escapeL 0).contDiff
    have h₁ : ContDiff ℝ 2 (escapeL 1) := (escapeL 1).contDiff
    have hc : ContDiff ℝ 2 (fun p : EscapeSpace ↦ a * ((escapeL 0) p - 1 / u) ^ 2 / 2) :=
      (contDiff_const.mul ((h₀.sub contDiff_const).pow 2)).div_const 2
    exact (h₀.mul h₁).add hc
  · simp [escapeFModel, hx0]
  · have hf : (fun p : EscapeSpace ↦ barrierBilinearObjective p.ofLp) = escapeFModel u 0 := by
      funext p
      simp [escapeFModel]
    rw [hf, escapeFModel_fderiv, escapeFModel_fderiv, sub_self, map_zero, map_zero]
  · intro p
    rw [escapeFModel_hessian, escapeFH]
    have ha : |a| ≤ 9 := h.objective_model_bound
    have hd : ‖a • escapeFDiagonal‖ ≤ |a| * ‖escapeFDiagonal‖ := by
      simpa only [Real.norm_eq_abs] using ContinuousLinearMap.opNorm_smul_le a escapeFDiagonal
    calc
      ‖escapeFCross + a • escapeFDiagonal‖ ≤ ‖escapeFCross‖ + ‖a • escapeFDiagonal‖ :=
        norm_add_le escapeFCross (a • escapeFDiagonal)
      _ ≤ ‖escapeFCross‖ + 9 * ‖escapeFDiagonal‖ :=
        add_le_add le_rfl (hd.trans (mul_le_mul_of_nonneg_right ha (norm_nonneg escapeFDiagonal)))
  · intro p q
    rw [escapeFModel_hessian, escapeFModel_hessian]
  · intro p q
    rw [escapeModel_hessian, escapeModel_hessian]
  · intro p
    have hh := h.model_matches (p.ofLp 0 - 1 / u) (p.ofLp 1 - escapeY u)
    dsimp only at hh
    have h0 : 1 / u + (p.ofLp 0 - 1 / u) = p.ofLp 0 := by ring
    have h1 : escapeY u + (p.ofLp 1 - escapeY u) = p.ofLp 1 := by ring
    rw [h0, h1] at hh
    unfold escapeModel escapeFModel barrierBilinearObjective logBarrierModel
    simp only [hx0, hx1, WithLp.ofLp_sub, Pi.sub_apply, Fin.sum_univ_two, logBarrier,
      Optimization.logBarrier, one_mul]
    simp only [div_eq_mul_inv, ← inv_pow] at hh ⊢
    linear_combination -hh

private theorem escapePoint_no_first_order_stop {u εE : ℝ} (h : PrimalBarrierEscapeTrial u) :
    ¬ BarrierSecondOrderStop barrierBilinearObjective (escapePoint u).ofLp 1 (1 / 4) εE := by
  intro hstop
  let y := (escapePoint u).ofLp
  have hg : barrierCoordinateGradient barrierBilinearObjective y 1 - 1 / y 1 = 1 / (1 + u) := by
    unfold barrierCoordinateGradient
    rw [barrierBilinearObjective_fderiv_apply]
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide),
      mul_zero, mul_one, add_zero]
    change 1 / u - 1 / escapeY u = _
    unfold escapeY
    field_simp [h.parameter_pos.ne', show 1 + u ≠ 0 by linarith [h.parameter_pos]]
    ring
  have hsum := Finset.single_le_sum (s := Finset.univ)
    (fun i _ ↦ sq_nonneg (barrierCoordinateGradient barrierBilinearObjective y i - 1 / y i))
    (Finset.mem_univ (1 : Fin 2))
  have hs := hsum.trans hstop.2.1
  rw [hg] at hs
  exact (not_lt_of_ge ((sq_le_sq₀
    (div_nonneg zero_le_one (by linarith [h.parameter_pos])) (by norm_num)).mp hs))
    h.fails_gradient_stop

/-- The counterexample to the printed primal finite stopping in Theorem 13.4.2 of [conn2000trust].
Consider Algorithm 13.2.1 with the parameters (6.1.6), $\eta_1 = 0.01$, $\eta_2 = 0.9$ and
$\gamma_1 = \gamma_2 = 1/2$, the Euclidean nonnegative quadrant of $\mathbb{R}^2$, the fraction
$\sigma = 1/4$ and the barrier objective $\psi(x_1 x_2) = x_1 x_2 - \log(x_1 x_2)$. There is a
run such that:
* on the interior, the barrier objective is $x_1 x_2 - \log x_1 - \log x_2$, the log-barrier
  objective of the bilinear objective with $\mu = 1$;
* the bilinear objective is twice continuously differentiable with bounded Hessian, and its
  log-barrier objective is bounded below on the positive quadrant for every $\mu > 0$;
* no iterate passes the stopping tests with $\mu = 1$, $\varepsilon^D = 1/4$ and any
  $\varepsilon^E$, and the model gradients $\nabla m_j(x_j)$ do not tend to $0$;
* each step satisfies AA.1 and AA.2 with $\beta = 1 + \|\nabla^2 m_j(x_j)\|$,
  $\tau = \min\{0, \lambda(\nabla^2 m_j(x_j))\}$ and the constant $1/32768$;
* there is $u_j \to 0$ with trial data such that $x_j = (1/u_j, u_j + u_j^2)$,
  $\Delta_j = 2/u_j$, $m_j$ is the model of `ConnGouldToint.Chapter13.PrimalBarrierEscapeTrial`,
  and every guarded ratio is at least $2$.

The ratios are computed from the true logarithmic barrier and the certified model, so every
trial is very successful. -/
theorem theorem_13_4_2_unbounded_primal_inner_run :
    ∃ r : PrimalBarrierInnerRun Chapter06.defaultBTRParams escapeOrthant (1 / 4) escapeObjective,
      (∀ p ∈ interior escapeOrthant,
        escapeObjective p = logBarrierObjective barrierBilinearObjective p.ofLp 1) ∧
      ContDiff ℝ 2 barrierBilinearObjective ∧
      (∃ H, ∀ p, ‖fderiv ℝ (fderiv ℝ barrierBilinearObjective) p‖ ≤ H) ∧
      (∀ μ > 0, ∃ A : ℝ, ∀ p : Fin 2 → ℝ, (∀ i, 0 < p i) →
        A ≤ logBarrierObjective barrierBilinearObjective p μ) ∧
      (∀ j εE, ¬ BarrierSecondOrderStop barrierBilinearObjective (r.x j).ofLp 1 (1 / 4) εE) ∧
      (¬ Tendsto (fun j ↦ ‖gradient (r.model j) (r.x j)‖) atTop (𝓝 0)) ∧
      (∀ j,
        let H := fderiv ℝ (fderiv ℝ (r.model j)) (r.x j)
        let β := 1 + ‖H‖
        let τ := min 0 (Chapter06.leastUnitCurvature H)
        Chapter06.HasSufficientModelDecrease (r.model j) (r.x j) (r.s j)
          (gradient (r.model j) (r.x j)) β (r.Δ j) (1 / 32768) ∧
        Chapter06.HasNegativeCurvatureDecrease (r.model j) (r.x j) (r.s j) τ (r.Δ j) (1 / 32768)) ∧
      ∃ u : ℕ → ℝ, Tendsto u atTop (𝓝 0) ∧ (∀ j, PrimalBarrierEscapeTrial (u j)) ∧
        (∀ j, r.x j = escapePoint (u j) ∧ r.Δ j = 2 / u j ∧ r.model j = escapeModel (u j)) ∧
        (∀ j, 2 ≤ primalBarrierRatio escapeOrthant (1 / 4) escapeObjective
          (r.model j) (r.x j) (r.s j)) := by
  obtain ⟨u, hu, hup, htrial, hratio, hAW⟩ := theorem_13_4_2_unbounded_run_counterexample
  let x (j : ℕ) := escapePoint (u j)
  let s (j : ℕ) := x (j + 1) - x j
  let Δ (j : ℕ) := 2 / u j
  let m (j : ℕ) := escapeModel (u j)
  have hxpos (j : ℕ) : ∀ i, 0 < (x j).ofLp i := escapePoint_positive (htrial j).parameter_pos
  have hstep (j : ℕ) : x j + s j = x (j + 1) := by dsimp [s]; abel
  have hdouble (j : ℕ) : (1 : ℝ) / u (j + 1) = 2 * (1 / u j) := by
    rw [hup]
    field_simp [(htrial j).parameter_pos.ne']
  have ha (j : ℕ) : BarrierAdmissibleTrial escapeOrthant (1 / 4) (x j) (x j + s j) := by
    rw [hstep]
    refine ⟨escapeOrthant_interior (hxpos _), ?_⟩
    rw [escapeOrthant_boundary_dist (hxpos _), escapeOrthant_boundary_dist (hxpos _)]
    change (1 / 4 : ℝ) * min (1 / u j) (escapeY (u j)) ≤
      min (1 / u (j + 1)) (escapeY (u (j + 1)))
    rw [hdouble, hup]
    exact (htrial j).trial_inside.2.2.1
  have hp (j : ℕ) : m j (x j) - m j (x j + s j) = u j ^ 2 / 16 := by
    rw [hstep]
    change escapeModel (u j) (escapePoint (u j)) -
      escapeModel (u j) (escapePoint (u (j + 1))) = _
    rw [hup]
    exact escapeModel_predicted (htrial j)
  have hr (j : ℕ) :
      2 ≤ primalBarrierRatio escapeOrthant (1 / 4) escapeObjective (m j) (x j) (s j) := by
    rw [primalBarrierRatio, ite_eq_left (ha j), Chapter06.btrRatio, Optimization.reductionRatio,
      hp j,
      hstep, escapeObjective_at_point (htrial j).parameter_pos,
      escapeObjective_at_point (htrial (j + 1)).parameter_pos]
    exact hratio j
  have hη (j : ℕ) : Chapter06.defaultBTRParams.η₂ ≤
      primalBarrierRatio escapeOrthant (1 / 4) escapeObjective (m j) (x j) (s j) :=
    (Chapter06.defaultBTRParams.eta₂_lt_one.le.trans (by norm_num)).trans (hr j)
  let r : PrimalBarrierInnerRun Chapter06.defaultBTRParams escapeOrthant (1 / 4) escapeObjective :=
    { x := x
      s := s
      Δ := Δ
      model := m
      initial_interior := escapeOrthant_interior (hxpos 0)
      initial_radius_pos := div_pos (by norm_num) (htrial 0).parameter_pos
      step_feasible := fun j ↦ by
        apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (by norm_num) (htrial j).parameter_pos.le)).mp
        rw [escape_norm_sq]
        change (1 / u (j + 1) - 1 / u j) ^ 2 +
          (escapeY (u (j + 1)) - escapeY (u j)) ^ 2 ≤ (2 / u j) ^ 2
        rw [hdouble, hup]
        have h := (htrial j).trial_inside.2.2.2
        convert h using 1
        ring
      predicted_pos := fun j ↦ by rw [hp]; positivity [(htrial j).parameter_pos]
      iterate_update := fun j ↦ by
        rw [ite_eq_left (Chapter06.defaultBTRParams.eta₁_le_eta₂.trans (hη j)), hstep]
      radius_update := fun j ↦
        ⟨fun _ ↦ by
          have h : Δ (j + 1) = 2 * Δ j := by
            dsimp [Δ]
            rw [hup]
            field_simp [(htrial j).parameter_pos.ne']
          rw [h]
          linarith [div_pos (show (0 : ℝ) < 2 by norm_num) (htrial j).parameter_pos]
        , fun _ h ↦ (h.not_ge (hη j)).elim
        , fun h ↦ (h.not_ge (Chapter06.defaultBTRParams.eta₁_le_eta₂.trans (hη j))).elim⟩ }
  obtain ⟨hf, hH⟩ := barrierBilinearObjective_smooth_bounded_hessian
  have hbar : ∀ μ > 0, ∃ A : ℝ, ∀ p : Fin 2 → ℝ, (∀ i, 0 < p i) →
      A ≤ logBarrierObjective barrierBilinearObjective p μ := by
    intro μ hμ
    obtain ⟨A, hA⟩ := hAW μ hμ
    refine ⟨A, fun p hp ↦ ?_⟩
    change A ≤ p 0 * p 1 + (-μ) * (∑ i, Real.log (p i))
    rw [Fin.sum_univ_two]
    linarith [hA (p 0) (p 1) (hp 0) (hp 1)]
  have hnograd : ¬ Tendsto (fun j ↦ ‖gradient (r.model j) (r.x j)‖) atTop (𝓝 0) := by
    intro ht
    obtain ⟨j, hj⟩ := (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).exists
    change ‖gradient (escapeModel (u j)) (escapePoint (u j))‖ < (1 / 4 : ℝ) at hj
    rw [escapeModel_gradient_norm] at hj
    have hpos : 0 ≤ 1 / (1 + u j) := by
      have := (htrial j).parameter_pos
      positivity
    have hle : 1 / (1 + u j) ≤ Real.sqrt (((u j) ^ 2) ^ 2 + (1 / (1 + u j)) ^ 2) := by
      calc
        _ = Real.sqrt ((1 / (1 + u j)) ^ 2) := (Real.sqrt_sq hpos).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by linarith [sq_nonneg ((u j) ^ 2)])
    exact hj.not_ge ((htrial j).fails_gradient_stop.le.trans hle)
  have had (j : ℕ) :
      let H := fderiv ℝ (fderiv ℝ (r.model j)) (r.x j)
      Chapter06.HasSufficientModelDecrease (r.model j) (r.x j) (r.s j)
        (gradient (r.model j) (r.x j)) (1 + ‖H‖) (r.Δ j) (1 / 32768) ∧
      Chapter06.HasNegativeCurvatureDecrease (r.model j) (r.x j) (r.s j)
        (min 0 (Chapter06.leastUnitCurvature H)) (r.Δ j) (1 / 32768) := by
    have hh : s j = escapePoint (u j / 2) - escapePoint (u j) := by
      change escapePoint (u (j + 1)) - escapePoint (u j) = _
      rw [hup]
    change Chapter06.HasSufficientModelDecrease _ _ (s j) _ _ _ _ ∧
      Chapter06.HasNegativeCurvatureDecrease _ _ (s j) _ _ _
    rw [hh]
    exact escapeModel_adequate_decrease (htrial j)
  refine ⟨r, ?_, hf, hH, hbar, fun j _ ↦ escapePoint_no_first_order_stop (htrial j),
    hnograd, had, u, hu, htrial, fun _ ↦ ⟨rfl, rfl, rfl⟩, hr⟩
  intro p hp
  have hp' : p.ofLp ∈ interior (Optimization.nonnegativeOrthant (Fin 2)) := by
    let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).toHomeomorph
    change p ∈ interior (T ⁻¹' Optimization.nonnegativeOrthant (Fin 2)) at hp
    rw [← T.preimage_interior] at hp
    exact hp
  change p.ofLp ∈ interior (Set.univ.pi (fun _ : Fin 2 ↦ Ici (0 : ℝ))) at hp'
  rw [interior_pi_set Set.finite_univ] at hp'
  have hpos : ∀ i, 0 < p.ofLp i := by
    simpa only [Set.mem_pi, Set.mem_univ, true_implies, interior_Ici, Set.mem_Ioi] using hp'
  change p.ofLp 0 * p.ofLp 1 - Real.log (p.ofLp 0 * p.ofLp 1) =
    p.ofLp 0 * p.ofLp 1 + (-1 : ℝ) * ∑ i, Real.log (p.ofLp i)
  rw [Fin.sum_univ_two, Real.log_mul (hpos 0).ne' (hpos 1).ne']
  ring

/-- The counterexample to Theorem 13.4.2 of [conn2000trust] for Algorithm 13.3.1. With the same data
as `ConnGouldToint.Chapter13.theorem_13_4_2_unbounded_primal_inner_run`, there is a run of
Algorithm 13.3.1 such that the barrier objective, the bilinear objective and its log-barrier
objectives are as there, and:
* there is $B$ such that each objective model $m^f_j$ is twice continuously differentiable,
  agrees with $x_1 x_2$ in value and derivative at $x_j$, and has constant Hessian of norm at
  most $B$, and each barrier model is the logarithmic Taylor model (13.4.2) at $x_j$ with
  $\mu = 1$;
* no iterate passes the stopping tests with $\mu = 1$, $\varepsilon^D = 1/4$ and any
  $\varepsilon^E$, and the model gradients $g_j$ do not tend to $0$;
* every guarded ratio is at least $2$, and $x_j = (1/u_j, u_j + u_j^2)$ for a positive sequence
  $u_j \to 0$.

The trials already pass the fraction-to-boundary test, and the capped decrease benchmarks can
only be smaller. AM.5c holds because the model gradients stay away from zero. -/
theorem theorem_13_4_2_unbounded_constrained_primal_inner_run :
    ∃ r : SecondPrimalBarrierInnerRun Chapter06.defaultBTRParams escapeOrthant
        (1 / 4) escapeObjective,
      (∀ p ∈ interior escapeOrthant,
        escapeObjective p = logBarrierObjective barrierBilinearObjective p.ofLp 1) ∧
      ContDiff ℝ 2 barrierBilinearObjective ∧
      (∃ H, ∀ p, ‖fderiv ℝ (fderiv ℝ barrierBilinearObjective) p‖ ≤ H) ∧
      (∀ μ > 0, ∃ A : ℝ, ∀ p : Fin 2 → ℝ, (∀ i, 0 < p i) →
        A ≤ logBarrierObjective barrierBilinearObjective p μ) ∧
      (∃ B, ∀ j, ContDiff ℝ 2 (r.objectiveModel j) ∧
        r.objectiveModel j (r.x j) = barrierBilinearObjective (r.x j).ofLp ∧
        fderiv ℝ (r.objectiveModel j) (r.x j) =
          fderiv ℝ (fun p : EscapeSpace ↦ barrierBilinearObjective p.ofLp) (r.x j) ∧
        (∀ p, ‖fderiv ℝ (fderiv ℝ (r.objectiveModel j)) p‖ ≤ B) ∧
        (∀ p q, fderiv ℝ (fderiv ℝ (r.objectiveModel j)) p =
          fderiv ℝ (fderiv ℝ (r.objectiveModel j)) q) ∧
        ∀ p, r.barrierModel j p = logBarrierModel (r.x j).ofLp (p - r.x j).ofLp 1) ∧
      (∀ j εE, ¬ BarrierSecondOrderStop barrierBilinearObjective (r.x j).ofLp 1 (1 / 4) εE) ∧
      (¬ Tendsto (fun j ↦ ‖r.g j‖) atTop (𝓝 0)) ∧
      (∀ j, 2 ≤ primalBarrierRatio escapeOrthant (1 / 4) escapeObjective
        (r.model j) (r.x j) (r.s j)) ∧
      ∃ u : ℕ → ℝ, Tendsto u atTop (𝓝 0) ∧ (∀ j, 0 < u j) ∧
        ∀ j, r.x j = escapePoint (u j) := by
  classical
  obtain ⟨r, hφ, hf, hH, hAW, hstop, hgrad, hdec, u, hu, htrial, hrun, hratio⟩ :=
    theorem_13_4_2_unbounded_primal_inner_run
  obtain ⟨B, hB⟩ := escapeModel_source_models
  choose mf hmf using fun j ↦ hB (u j) (htrial j)
  let H j := fderiv ℝ (fderiv ℝ (r.model j)) (r.x j)
  let b j := 1 + ‖H j‖
  let t j := min 0 (Chapter06.leastUnitCurvature (H j))
  have hconst (j : ℕ) (p : EscapeSpace) :
      fderiv ℝ (fderiv ℝ (r.model j)) p = H j := by
    dsimp only [H]
    rw [(hrun j).2.2]
    exact (hmf j).2.2.2.2.2.1 _ _
  have htrial_adm (j : ℕ) :
      BarrierAdmissibleTrial escapeOrthant (1 / 4) (r.x j) (r.x j + r.s j) := by
    by_contra hn
    have h := hratio j
    rw [primalBarrierRatio, ite_eq_right hn] at h
    norm_num at h
  let R : SecondPrimalBarrierInnerRun Chapter06.defaultBTRParams escapeOrthant
      (1 / 4) escapeObjective := {
    toPrimalBarrierInnerRun := r
    fraction := by norm_num
    objectiveModel := mf
    barrierModel := fun j p ↦ logBarrierModel (r.x j).ofLp (p - r.x j).ofLp 1
    model_split := fun j ↦ by
      funext p
      rw [(hrun j).1, (hrun j).2.2]
      exact (hmf j).2.2.2.2.2.2 p
    g := fun j ↦ gradient (r.model j) (r.x j)
    β := b
    τ := t
    κ := 1 / 32768
    decrease_constant := by norm_num
    gradient_model := fun _ ↦ rfl
    curvature_model := fun j ↦ by
      have hball : r.x j ∈ closedBall (r.x j) (r.Δ j) :=
        mem_closedBall_self ((norm_nonneg (r.s j)).trans (r.step_feasible j))
      have he : (fun p ↦ ‖fderiv ℝ (fderiv ℝ (r.model j)) p‖) ''
          closedBall (r.x j) (r.Δ j) = {‖H j‖} := by
        ext z
        constructor
        · rintro ⟨p, _, rfl⟩
          simp [hconst j p]
        · rintro hz
          obtain rfl := Set.mem_singleton_iff.mp hz
          exact ⟨r.x j, hball, rfl⟩
      simp [b, he]
    nonpositive_least_curvature := fun j ↦ by
      have he : Set.range (fun p : Metric.sphere (0 : EscapeSpace) 1 ↦ H j p p) =
          (fun p ↦ H j p p) '' Metric.sphere (0 : EscapeSpace) 1 := by
        ext z
        exact ⟨fun ⟨p, h⟩ ↦ ⟨p, p.property, h⟩, fun ⟨p, hp, h⟩ ↦ ⟨⟨p, hp⟩, h⟩⟩
      rw [show t j = min 0 (sInf (Set.range
        (fun p : Metric.sphere (0 : EscapeSpace) 1 ↦ H j p p))) from rfl, he]
    trial_admissible := htrial_adm
    sufficient_decrease := fun j ↦ by
      let δ := constrainedBarrierRadius (r.Δ j) (1 / 4)
        (infDist (r.x j) (frontier escapeOrthant))
      have hδ : 0 ≤ δ := le_min ((norm_nonneg (r.s j)).trans (r.step_feasible j))
        (mul_nonneg (by norm_num) infDist_nonneg)
      have hle : δ ≤ r.Δ j := min_le_left _ _
      have ht : t j ≤ 0 := min_le_left _ _
      obtain ⟨hfirst, hsecond⟩ := hdec j
      unfold HasConstrainedBarrierDecrease
      rw [mul_max_of_nonneg _ _ (by norm_num)]
      apply max_le
      · rw [← mul_assoc]
        exact (mul_le_mul_of_nonneg_left (min_le_min le_rfl hle) (by positivity)).trans hfirst.2
      · rcases ht.lt_or_eq with ht' | ht'
        · rw [← mul_assoc]
          have hh := hsecond.2 ht'
          rw [abs_of_neg ht'] at hh
          exact (mul_le_mul_of_nonneg_left (min_le_min le_rfl
            (pow_le_pow_left₀ hδ hle 2)) (mul_nonneg (by norm_num) (neg_nonneg.mpr ht))).trans hh
        · simpa only [ht', neg_zero, zero_mul, mul_zero] using (r.predicted_pos j).le }
  refine ⟨R, hφ, hf, hH, hAW, ⟨B, fun j ↦ ?_⟩, hstop, hgrad, hratio,
    u, hu, fun j ↦ (htrial j).parameter_pos, fun j ↦ (hrun j).1⟩
  rw [show R.x j = r.x j from rfl, (hrun j).1]
  refine ⟨(hmf j).1, (hmf j).2.1, (hmf j).2.2.1, (hmf j).2.2.2.1,
    (hmf j).2.2.2.2.1, fun p ↦ ?_⟩
  change logBarrierModel (r.x j).ofLp (p - r.x j).ofLp 1 = _
  rw [(hrun j).1]

end PrimalEscape

end ConnGouldToint.Chapter13
