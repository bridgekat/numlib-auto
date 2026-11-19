/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import NumlibSurface.ConnGouldToint.Chapter13.Section03
import NumlibSurface.ConnGouldToint.Chapter13.Section04

/-!
# Conn, Gould and Toint, Section 13.6: Primal-dual barrier methods

This module formalizes the primal-dual barrier methods of Section 13.6 of [conn2000trust] for the
bound constraints $x \ge 0$ in $\mathbb{R}^n$. Besides the primal iterate $x > 0$, the method keeps
dual variables $z > 0$ that estimate the barrier multipliers $\mu / x_i$. The barrier model (13.6.3)
replaces the primal curvature $\mu / x_i^2$ by $z_i / x_i$:
$$m^b(x, z, s) = -\mu \sum_i \log x_i - \mu \sum_i \frac{s_i}{x_i} + \frac12 \sum_i \frac{z_i}{x_i}
  s_i^2.$$
Lemma 13.6.1 checks the model assumptions for this model. The inner algorithm, Algorithm 13.6.1,
stops at a point that passes the primal-dual tests (13.6.5)–(13.6.8), and Algorithm 13.6.2 drives
the barrier parameter to zero. Theorem 13.6.3 gives first-order and weak second-order criticality in
the limit, and Theorem 13.6.4 studies the safeguarded dual update (13.6.17)–(13.6.19), which keeps
the duals bounded (AA.7) and consistent with $\mu / x$ (AA.8).

The finite stopping of Theorem 13.6.2 and the dual consistency of Theorem 13.6.4 are proved under
corrected hypotheses, and scalar counterexamples show why the printed hypotheses do not suffice. The
proofs build on `NumlibSurface.ConnGouldToint.Chapter13.Section03` and
`NumlibSurface.ConnGouldToint.Chapter13.Section04`.

## Main definitions

* Equation (13.6.3), `ConnGouldToint.Chapter13.primalDualBarrierModel`: the primal-dual barrier
  model with the corrected positive quadratic term.
* Equations (13.6.5)–(13.6.8), `ConnGouldToint.Chapter13.PrimalDualBarrierStop`: the positivity,
  dual residual, complementarity and Hessian stopping tests.
* Algorithm 13.6.1, `ConnGouldToint.Chapter13.PrimalDualBarrierInnerRun`: a run of the primal-dual
  inner algorithm for a fixed barrier parameter.
* Algorithm 13.6.2, `ConnGouldToint.Chapter13.PrimalDualBarrierOuterRun`: the primal-dual barrier
  method.
* Equation (13.6.16), `ConnGouldToint.Chapter13.primalDualPredictedMultiplier`: one coordinate of
  the predicted multiplier.
* Equations (13.6.17)–(13.6.19), `ConnGouldToint.Chapter13.primalDualSafeguard`: the projection of
  the predicted multiplier onto the safeguard interval.

## Main results

* Lemma 13.6.1, `ConnGouldToint.Chapter13.primalDualBarrierModel_center`,
  `ConnGouldToint.Chapter13.primalDualBarrierModel_hessian`,
  `ConnGouldToint.Chapter13.primalDualBarrierModel_hessian_bounded` and
  `ConnGouldToint.Chapter13.primalDualBarrierModel_hessian_consistent`: the model satisfies
  AM.1–AM.3, AC.6b, AM.4h and AM.5c.
* Theorem 13.6.2, `ConnGouldToint.Chapter13.PrimalDualBarrierInnerRun.frequently_stop_of_extension`:
  a bounded run of Algorithm 13.6.1 with a smooth extension of the objective, uniform model
  estimates and AA.8 passes the stopping tests infinitely often.
* Theorem 13.6.2, `ConnGouldToint.Chapter13.theorem_13_6_2_unbounded_run_counterexample`: without
  bounded primal coordinates, a run never passes the complementarity test.
* Theorem 13.6.3, `ConnGouldToint.Chapter13.theorem_13_6_3`: points that pass the primal-dual
  stopping tests with vanishing parameter and tolerances have nonnegative limiting gradients, zero
  limiting gradients on inactive coordinates, and nonnegative limiting curvature on inactive
  directions.
* Theorem 13.6.4, `ConnGouldToint.Chapter13.theorem_13_6_4`: the safeguarded duals stay positive and
  bounded (AA.7).
* Theorem 13.6.4, `ConnGouldToint.Chapter13.theorem_13_6_4_aa8_of_frequently_successful` and
  `ConnGouldToint.Chapter13.theorem_13_6_4_aa8_of_reset_rejected`: AA.8 holds with infinitely many
  successful iterations, or with the reset of the dual after a rejection.
* Theorem 13.6.4, `ConnGouldToint.Chapter13.theorem_13_6_4_all_rejected_counterexample`: AA.8 fails
  for a bounded run whose trials are all rejected.

## Implementation notes

* Vectors are functions `ι → ℝ` on a finite index type `ι`. The inner runs work in
  `EuclideanSpace ℝ ι`, so that the trust region and the distance to the boundary are Euclidean.
* In the stopping tests the complementarity matrix is diagonal, so its operator norm is the largest
  coordinate residual $|x_i z_i - \mu|$. The least-eigenvalue test is written as a bound on all
  quadratic forms.
* The dual update (13.6.17)–(13.6.19) is not part of
  `ConnGouldToint.Chapter13.PrimalDualBarrierInnerRun`; the theorems that need it take it as a
  hypothesis.
* The lower limits in Theorem 13.6.3 are written in eventual form: each negative tolerance $-\eta$
  is eventually a lower bound.

## Deviations from the source

* **Correction.** The primal-dual model uses the positive quadratic term needed to recover the
  Taylor model with exact multipliers. See `ConnGouldToint.Chapter13.primalDualBarrierModel`,
  `ConnGouldToint.Chapter13.primalDualBarrierModel_eq_primal`,
  `ConnGouldToint.Chapter13.primalDualBarrierModel_printed_sign_counterexample`.
* **Reading.** The model Hessian bounds and consistency use explicit clearance and dual estimates
  with the corrected sign. See `ConnGouldToint.Chapter13.primalDualBarrierDiagonal`,
  `ConnGouldToint.Chapter13.primalDualBarrierDiagonal_apply`,
  `ConnGouldToint.Chapter13.primalDualBarrierModel_center`,
  `ConnGouldToint.Chapter13.primalDualBarrierModel_hessian`,
  `ConnGouldToint.Chapter13.primalDualBarrierModel_hessian_bounded`,
  `ConnGouldToint.Chapter13.primalDualBarrierModel_hessian_consistent`.
* **Representation.** The primal-dual tests use a squared gradient residual, componentwise diagonal
  complementarity and a quadratic-form bound. See `ConnGouldToint.Chapter13.PrimalDualBarrierStop`.
* **Correction.** The primal-dual runs add strict trial feasibility; a scalar example passes the
  printed unsigned-distance test from outside. See
  `ConnGouldToint.Chapter13.primalDual_distance_test_infeasible_counterexample`,
  `ConnGouldToint.Chapter13.PrimalDualBarrierInnerRun`,
  `ConnGouldToint.Chapter13.PrimalDualBarrierOuterRun`,
  `ConnGouldToint.Chapter13.PrimalDualBarrierInnerRun.Successful`.
* **Correction.** The stopping transfer requires bounded primal coordinates; the scalar run exhibits
  failure when they are unbounded. See `ConnGouldToint.Chapter13.theorem_13_6_2_of_inner_limits`,
  `ConnGouldToint.Chapter13.theorem_13_6_2_of_primal_stopping`,
  `ConnGouldToint.Chapter13.PrimalDualBarrierInnerRun.frequently_stop_of_extension_limits`,
  `ConnGouldToint.Chapter13.PrimalDualBarrierInnerRun.frequently_stop_of_extension`,
  `ConnGouldToint.Chapter13.primalDual_complementarity_unbounded_counterexample`,
  `ConnGouldToint.Chapter13.theorem_13_6_2_unbounded_run_counterexample`.
* **Generalization.** The outer convergence conclusions depend on residual stopping tests along a
  filter, and apply to completed runs. See `ConnGouldToint.Chapter13.theorem_13_6_3`,
  `ConnGouldToint.Chapter13.theorem_13_6_3_consistentlyActive`,
  `ConnGouldToint.Chapter13.PrimalDualBarrierOuterRun.convergence`.
* **Representation.** The multiplier safeguards are scalar clamping formulas used coordinatewise
  with positive denominators. See `ConnGouldToint.Chapter13.primalDualPredictedMultiplier`,
  `ConnGouldToint.Chapter13.primalDualSafeguard`.
* **Correction.** The AA.8 variants require late successes or reset the dual on rejection. A bounded
  all-rejected run disproves the printed inference. See `ConnGouldToint.Chapter13.theorem_13_6_4`,
  `ConnGouldToint.Chapter13.theorem_13_6_4_aa8_of_frequently_successful`,
  `ConnGouldToint.Chapter13.theorem_13_6_4_aa8_of_reset_rejected`,
  `ConnGouldToint.Chapter13.PrimalDualBarrierInnerRun.dual_consistent_of_reset_rejected`,
  `ConnGouldToint.Chapter13.primalDual_safeguard_stalled_counterexample`,
  `ConnGouldToint.Chapter13.theorem_13_6_4_all_rejected_counterexample`.
* **Equation (13.6.3)** (correction). The printed quadratic term of the barrier model has a negative
  sign; the model uses the positive sign. See
  `ConnGouldToint.Chapter13.primalDualBarrierModel_printed_sign_counterexample`.
* **Algorithm 13.6.1, Step 2** (correction). The printed distance test also admits infeasible
  points; the trial must also be strictly feasible. See
  `ConnGouldToint.Chapter13.primalDual_distance_test_infeasible_counterexample`.
* **Theorem 13.6.2** (correction). Finite stopping needs bounded primal coordinates. A scalar
  all-successful run with unbounded primal coordinates never passes the complementarity test. See
  `ConnGouldToint.Chapter13.theorem_13_6_2_unbounded_run_counterexample` and
  `ConnGouldToint.Chapter13.PrimalDualBarrierInnerRun.frequently_stop_of_extension`.
* **Theorem 13.6.4** (correction). AA.8 needs infinitely many successful iterations; a bounded run
  with all trials rejected violates it. Resetting the dual to $\mu / x$ after a rejection gives AA.8
  when the accepted displacements tend to zero. See
  `ConnGouldToint.Chapter13.theorem_13_6_4_aa8_of_frequently_successful`,
  `ConnGouldToint.Chapter13.theorem_13_6_4_all_rejected_counterexample` and
  `ConnGouldToint.Chapter13.theorem_13_6_4_aa8_of_reset_rejected`.
-/

open Filter Set
open scoped Topology

namespace ConnGouldToint.Chapter13

variable {ι : Type*} [Fintype ι]

/-- **Equation (13.6.3)** of [conn2000trust]. For a primal point $x > 0$, a dual point $z$, a
displacement $s$ and a barrier parameter $\mu$, the **primal-dual barrier model** is
$$m^b(x, z, s) = -\mu \sum_i \log x_i - \mu \sum_i \frac{s_i}{x_i} + \frac12 \sum_i
  \frac{z_i}{x_i} s_i^2.$$

**Correction.** The source prints the quadratic term with a negative sign. The model uses the
positive sign, as in Section 13.6.2 and in the elimination of the dual Newton step. With the
printed sign the model differs from the primal Taylor model even for the exact dual values; see
`ConnGouldToint.Chapter13.primalDualBarrierModel_printed_sign_counterexample`.

**Correction.** The linear term is the derivative of the logarithmic barrier and the diagonal
quadratic term has positive sign. With exact dual values this produces the Taylor model, which the
printed negative quadratic sign fails to recover.
-/
noncomputable def primalDualBarrierModel (x z s : ι → ℝ) (μ : ℝ) : ℝ :=
  logBarrier x μ - μ * (∑ i, (x i)⁻¹ * s i) +
    (1 / 2 : ℝ) * ∑ i, (z i / x i) * (s i) ^ 2

/-- With the exact dual values $z_i = \mu / x_i$, the primal-dual barrier model (13.6.3) of
[conn2000trust] is the primal Taylor model (13.4.2): $m^b(x, \mu / x, s) = m^b(x, s)$ for all
$x$, $s$ and $\mu$.

**Correction.** The linear term is the derivative of the logarithmic barrier and the diagonal
quadratic term has positive sign. With exact dual values this produces the Taylor model, which the
printed negative quadratic sign fails to recover.
-/
theorem primalDualBarrierModel_eq_primal (x s : ι → ℝ) (μ : ℝ) :
    primalDualBarrierModel x (fun i ↦ μ / x i) s μ = logBarrierModel x s μ := by
  unfold primalDualBarrierModel logBarrierModel
  simp only [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by
    simp only [div_eq_mul_inv, ← inv_pow]
    ring

/-- A counterexample to the printed sign in (13.6.3) of [conn2000trust]. In one dimension, at
$x = z = \mu = s = 1$, the primal Taylor model (13.4.2) differs from the value
$-\log 1 - 1 - \frac12$ of the model with the printed negative quadratic term:
$$m^b(1, 1) \ne -\log 1 - 1 - \tfrac12.$$

The exact dual value is $z = \mu / x = 1$ here, so the printed model differs from the primal
Taylor model even for the exact dual value.

**Correction.** The linear term is the derivative of the logarithmic barrier and the diagonal
quadratic term has positive sign. With exact dual values this produces the Taylor model, which the
printed negative quadratic sign fails to recover.
-/
theorem primalDualBarrierModel_printed_sign_counterexample :
    logBarrierModel (ι := Unit) (fun _ ↦ 1) (fun _ ↦ 1) 1 ≠
      logBarrier (ι := Unit) (fun _ ↦ 1) 1 - 1 - 1 / 2 := by
  norm_num [logBarrierModel]
  linarith

private noncomputable def barrierCoordinateBilinear (i : ι) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj i)

/-- The **diagonal bilinear form** of a vector $a \in \mathbb{R}^n$ is
$(d, e) \mapsto \sum_i a_i d_i e_i$, as a continuous bilinear form on $\mathbb{R}^n$.

**Reading.** The model identities use the corrected sign. The boundedness and consistency lemmas
take an explicit positive primal-coordinate lower bound, with AA.7 or the multiplier consistency
along a filter as appropriate.
-/
noncomputable def primalDualBarrierDiagonal (a : ι → ℝ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, a i • barrierCoordinateBilinear i

/-- The diagonal bilinear form of $a$ takes the value $\sum_i a_i d_i e_i$ at $(d, e)$.

**Reading.** The model identities use the corrected sign. The boundedness and consistency lemmas
take an explicit positive primal-coordinate lower bound, with AA.7 or the multiplier consistency
along a filter as appropriate.
-/
theorem primalDualBarrierDiagonal_apply (a d e : ι → ℝ) :
    primalDualBarrierDiagonal a d e = ∑ i, a i * d i * e i := by
  simp [primalDualBarrierDiagonal, barrierCoordinateBilinear, mul_assoc]

private theorem norm_primalDualBarrierDiagonal_le (a : ι → ℝ) :
    ‖primalDualBarrierDiagonal a‖ ≤ ∑ i, |a i| *
      ‖barrierCoordinateBilinear i‖ := by
  unfold primalDualBarrierDiagonal
  refine (norm_sum_le Finset.univ (fun i ↦ a i • barrierCoordinateBilinear i)).trans ?_
  apply Finset.sum_le_sum
  intro i _
  simpa only [Real.norm_eq_abs] using
    ContinuousLinearMap.opNorm_smul_le (a i) (barrierCoordinateBilinear i)

private theorem primalDualBarrierModel_eq_quadratic {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    (z : ι → ℝ) (μ : ℝ) (s : ι → ℝ) :
    primalDualBarrierModel x z s μ =
      logBarrier x μ + fderiv ℝ (Optimization.logBarrier μ) x s +
        (1 / 2 : ℝ) * primalDualBarrierDiagonal (fun i ↦ z i / x i) s s := by
  rw [Optimization.fderiv_logBarrier_apply μ hx, primalDualBarrierDiagonal_apply]
  simp only [primalDualBarrierModel, pow_two, mul_assoc]
  ring

private theorem primalDualBarrierModel_fderiv {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    (z : ι → ℝ) (μ : ℝ) (s : ι → ℝ) :
    fderiv ℝ (fun d ↦ primalDualBarrierModel x z d μ) s =
      fderiv ℝ (Optimization.logBarrier μ) x + primalDualBarrierDiagonal (fun i ↦ z i / x i) s := by
  simp only [primalDualBarrierModel_eq_quadratic hx]
  apply (barrierQuadratic_hasFDerivAt ?_ s).fderiv
  intro d e
  simp only [primalDualBarrierDiagonal_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **Lemma 13.6.1** of [conn2000trust], AM.1–AM.3. For $x > 0$, every $z$ and every $\mu$, the
primal-dual barrier model $s \mapsto m^b(x, z, s)$ is twice continuously differentiable,
$m^b(x, z, 0) = b_\mu(x)$, and its derivative at $s = 0$ is the derivative $D b_\mu(x)$ of the
barrier $b_\mu(x) = -\mu \sum_i \log x_i$.

**Reading.** The model identities use the corrected sign. The boundedness and consistency lemmas
take an explicit positive primal-coordinate lower bound, with AA.7 or the multiplier consistency
along a filter as appropriate.
-/
theorem primalDualBarrierModel_center {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    (z : ι → ℝ) (μ : ℝ) :
    ContDiff ℝ 2 (fun s ↦ primalDualBarrierModel x z s μ) ∧
    primalDualBarrierModel x z 0 μ = logBarrier x μ ∧
    fderiv ℝ (fun s ↦ primalDualBarrierModel x z s μ) 0 =
      fderiv ℝ (Optimization.logBarrier μ) x := by
  refine ⟨?_, by simp [primalDualBarrierModel], ?_⟩
  · simp only [primalDualBarrierModel_eq_quadratic hx]
    fun_prop
  · rw [primalDualBarrierModel_fderiv hx, map_zero, add_zero]

/-- **Lemma 13.6.1** of [conn2000trust], AC.6b. For $x > 0$, every $z$, $\mu$ and $s$, the Hessian
of $s \mapsto m^b(x, z, s)$ at $s$ is the diagonal bilinear form of $(z_i / x_i)_i$.

The Hessian does not depend on the displacement, so AC.6b holds with zero variation.

**Reading.** The model identities use the corrected sign. The boundedness and consistency lemmas
take an explicit positive primal-coordinate lower bound, with AA.7 or the multiplier consistency
along a filter as appropriate.
-/
theorem primalDualBarrierModel_hessian {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    (z : ι → ℝ) (μ : ℝ) (s : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (fun d ↦ primalDualBarrierModel x z d μ)) s =
      primalDualBarrierDiagonal (fun i ↦ z i / x i) := by
  rw [funext (primalDualBarrierModel_fderiv hx z μ)]
  exact ((primalDualBarrierDiagonal _).hasFDerivAt.const_add _).fderiv

/-- **Lemma 13.6.1** of [conn2000trust], AM.4h. Let $\varepsilon > 0$, $K > 0$ and
$\mu \in \mathbb{R}$. There is $C \ge 1$ such that $\|\nabla^2_s m^b(x, z, s)\| \le C$ for all
$x$, $z$ and $s$ with $x_i \ge \varepsilon$ and $0 \le z_i \le K \max\{x_i^{-1}, 1\}$ for all
$i$.

The layer $x_i \ge \varepsilon$ is bounded away from the boundary, and the bound on the duals is
AA.7.

**Reading.** The model identities use the corrected sign. The boundedness and consistency lemmas
take an explicit positive primal-coordinate lower bound, with AA.7 or the multiplier consistency
along a filter as appropriate.
-/
theorem primalDualBarrierModel_hessian_bounded {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (μ : ℝ) :
    ∃ C ≥ (1 : ℝ), ∀ x z s : ι → ℝ, (∀ i, ε ≤ x i) →
      (∀ i, 0 ≤ z i ∧ z i ≤ K * max (x i)⁻¹ 1) →
      ‖fderiv ℝ (fderiv ℝ (fun d ↦ primalDualBarrierModel x z d μ)) s‖ ≤ C := by
  let B := K * max ε⁻¹ 1 / ε
  let C := ∑ i : ι, B * ‖barrierCoordinateBilinear i‖
  refine ⟨max 1 C, le_max_left _ _, fun x z s hx hz ↦ ?_⟩
  rw [primalDualBarrierModel_hessian (fun i ↦ hε.trans_le (hx i))]
  refine (norm_primalDualBarrierDiagonal_le _).trans (le_trans ?_ (le_max_right 1 C))
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg (barrierCoordinateBilinear i))
  rw [abs_of_nonneg (div_nonneg (hz i).1 (hε.le.trans (hx i)))]
  calc
    z i / x i ≤ z i / ε := div_le_div_of_nonneg_left (hz i).1 hε (hx i)
    _ ≤ B := by
      apply div_le_div_of_nonneg_right _ hε.le
      exact (hz i).2.trans (mul_le_mul_of_nonneg_left
        (max_le_max (inv_anti₀ hε (hx i)) le_rfl) hK.le)

/-- **Lemma 13.6.1** of [conn2000trust], AM.5c. Let $l$ be a filter, $\varepsilon > 0$ and
$\mu \in \mathbb{R}$, and let $x_j$, $z_j$ and $s_j$ be vectors with $x_{j,i} \ge \varepsilon$
for all $j$ and $i$. If $z_{j,i} - \mu / x_{j,i} \to 0$ along $l$ for every $i$ (AA.8), then
$$\|\nabla^2_s m^b(x_j, z_j, s_j) - \nabla^2 b_\mu(x_j)\| \to 0.$$

On a uniformly positive primal layer, AA.8 makes the Hessian of the barrier model asymptotically
exact.

**Reading.** The model identities use the corrected sign. The boundedness and consistency lemmas
take an explicit positive primal-coordinate lower bound, with AA.7 or the multiplier consistency
along a filter as appropriate.
-/
theorem primalDualBarrierModel_hessian_consistent {α : Type*} {l : Filter α}
    {x z s : α → ι → ℝ} {ε μ : ℝ} (hε : 0 < ε) (hx : ∀ j i, ε ≤ x j i)
    (hdual : ∀ i, Tendsto (fun j ↦ z j i - μ / x j i) l (𝓝 0)) :
    Tendsto (fun j ↦
      ‖fderiv ℝ (fderiv ℝ (fun d ↦ primalDualBarrierModel (x j) (z j) d μ)) (s j) -
      fderiv ℝ (fderiv ℝ (Optimization.logBarrier μ)) (x j)‖) l (𝓝 0) := by
  have heq (j : α) :
      fderiv ℝ (fderiv ℝ (fun d ↦ primalDualBarrierModel (x j) (z j) d μ)) (s j) -
        fderiv ℝ (fderiv ℝ (Optimization.logBarrier μ)) (x j) =
      primalDualBarrierDiagonal (fun i ↦ (z j i - μ / x j i) / x j i) := by
    rw [primalDualBarrierModel_hessian (fun i ↦ hε.trans_le (hx j i))]
    ext d e
    simp only [sub_apply, primalDualBarrierDiagonal_apply,
      Optimization.fderiv_fderiv_logBarrier_apply μ (fun i ↦ hε.trans_le (hx j i)),
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by
      simp only [div_eq_mul_inv, ← inv_pow]
      ring
  simp only [heq]
  refine squeeze_zero
    (fun j ↦ norm_nonneg (primalDualBarrierDiagonal (fun i ↦ (z j i - μ / x j i) / x j i)))
    (fun j ↦ norm_primalDualBarrierDiagonal_le (fun i ↦ (z j i - μ / x j i) / x j i)) ?_
  rw [← Finset.sum_const_zero (s := (Finset.univ : Finset ι))]
  apply tendsto_finsetSum Finset.univ
  intro i _
  have ht : Tendsto (fun j ↦ |(z j i - μ / x j i) / x j i|) l (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ abs_nonneg _)
      (g := fun j ↦ |z j i - μ / x j i| / ε)
    · intro j
      rw [abs_div, abs_of_pos (hε.trans_le (hx j i))]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hε (hx j i)
    · simpa using (continuous_abs.continuousAt.tendsto.comp (hdual i)).div_const ε
  simpa only [zero_mul] using ht.mul_const
    ‖barrierCoordinateBilinear i‖

variable [DecidableEq ι]

/-! ### Stopping tests and Algorithms 13.6.1 and 13.6.2 -/

/-- **Equations (13.6.5)–(13.6.8)** of [conn2000trust]. A primal-dual pair $(x, z)$ passes the
**primal-dual stopping tests** for the objective $f$, the barrier parameter $\mu$ and the
tolerances $\varepsilon^D$, $\varepsilon^C$, $\varepsilon^E$ if $x > 0$, $z > 0$, and
$$\sum_i (\partial_i f(x) - z_i)^2 \le (\varepsilon^D)^2, \qquad |x_i z_i - \mu| \le
  \varepsilon^C \text{ for all } i,$$
$$\nabla^2 f(x)[d, d] + \sum_i \frac{z_i}{x_i} d_i^2 \ge -\varepsilon^E \|d\|^2 \text{ for all }
  d,$$
where $\|d\|$ is the Euclidean norm.

The complementarity matrix is diagonal, so its operator norm is the largest coordinate residual.
The least-eigenvalue test is written as a bound on all quadratic forms.

**Reading.** The gradient test uses a squared Euclidean norm, the diagonal complementarity operator
norm is tested coordinatewise, and the eigenvalue test is expressed as a homogeneous curvature
bound.
-/
def PrimalDualBarrierStop (f : (ι → ℝ) → ℝ) (x z : ι → ℝ) (μ εD εC εE : ℝ) : Prop :=
  (∀ i, 0 < x i) ∧ (∀ i, 0 < z i) ∧
  (∑ i, (barrierCoordinateGradient f x i - z i) ^ 2) ≤ εD ^ 2 ∧
  (∀ i, |x i * z i - μ| ≤ εC) ∧
  ∀ d : ι → ℝ, -εE * (∑ i, (d i) ^ 2) ≤
    fderiv ℝ (fderiv ℝ f) x d d + ∑ i, (z i / x i) * d i * d i

/-- A counterexample to the printed distance test in Step 2 of Algorithm 13.6.1 of [conn2000trust].
There are $x > 0$ and $y < 0$ with $|y - x| \le 2$ and
$$\tfrac12 \operatorname{dist}(x, \partial [0, \infty)) \le \operatorname{dist}(y, \partial [0,
  \infty)).$$

The test with fraction $\frac12$ admits the infeasible point $y$. The proof takes $x = 1$ and
$y = -1$.

**Correction.** The primal trial must be strictly feasible in addition to having sufficient unsigned
distance from the boundary. A scalar exterior trial can pass the printed distance test. The
execution is specified through run relations using the corrected model and explicitly guarded
acceptance.
-/
theorem primalDual_distance_test_infeasible_counterexample :
    ∃ x y : ℝ, x ∈ interior (Ici (0 : ℝ)) ∧ y ∈ Metric.closedBall x 2 ∧
      (1 / 2 : ℝ) * Metric.infDist x (frontier (Ici (0 : ℝ))) ≤
        Metric.infDist y (frontier (Ici (0 : ℝ))) ∧ y ∉ Ici (0 : ℝ) := by
  refine ⟨1, -1, ?_⟩
  norm_num [interior_Ici, Metric.mem_closedBall, frontier_Ici, Metric.infDist_singleton,
    Real.dist_eq]

private def euclideanOrthant : Set (EuclideanSpace ℝ ι) :=
  WithLp.ofLp ⁻¹' Optimization.nonnegativeOrthant ι

/-- **Algorithm 13.6.1** of [conn2000trust]. Let $f : \mathbb{R}^n \to \mathbb{R}$,
$\sigma \in \mathbb{R}$ and $\mu > 0$. A **run of the primal-dual inner algorithm** is a run of
Algorithm 13.3.1 (`ConnGouldToint.Chapter13.SecondPrimalBarrierInnerRun`) on the nonnegative
orthant of the Euclidean space $\mathbb{R}^n$ for the barrier objective $f + b_\mu$, together
with dual points $z_j > 0$, such that for all $j$:
* the barrier model is the primal-dual model (13.6.3), $m^b_j(y) = m^b(x_j, z_j, y - x_j)$;
* the objective model $m^f_j$ and its derivative are differentiable on the ball
  $\|y - x_j\| \le \Delta_j$, with $m^f_j(x_j) = f(x_j)$ and $D m^f_j(x_j) = D f(x_j)$;
* the Hessians $\nabla^2 m^f_j$ are bounded on the positive points of these balls, uniformly in
  $j$.

**Correction.** Step 1 uses the positive quadratic sign of the corrected model (13.6.3). Step 2
keeps the trial strictly feasible: every trial passes the interior and fraction-to-boundary test
of Algorithm 13.3.1, which the printed distance test alone does not ensure.

The dual update is not part of the run.

**Correction.** The primal trial must be strictly feasible in addition to having sufficient unsigned
distance from the boundary. A scalar exterior trial can pass the printed distance test. The
execution is specified through run relations using the corrected model and explicitly guarded
acceptance.
-/
structure PrimalDualBarrierInnerRun (P : Chapter06.BTRParams) (f : (ι → ℝ) → ℝ) (σ μ : ℝ)
    extends SecondPrimalBarrierInnerRun P (euclideanOrthant (ι := ι)) σ
      (fun x ↦ logBarrierObjective f x.ofLp μ) where
  /-- The barrier parameter $\mu$ is positive. -/
  barrier_parameter_pos : 0 < μ
  /-- The dual points $z_j$. -/
  z : ℕ → ι → ℝ
  /-- The dual points are positive. -/
  dual_pos : ∀ j i, 0 < z j i
  /-- The barrier model is the primal-dual model (13.6.3) at $(x_j, z_j)$. -/
  barrier_model : ∀ j y, barrierModel j y =
    primalDualBarrierModel (x j).ofLp (z j) (y - x j).ofLp μ
  /-- Each objective model and its derivative are differentiable on the trust region. -/
  objective_model_twice_diff : ∀ j,
    DifferentiableOn ℝ (objectiveModel j) (Metric.closedBall (x j) (Δ j)) ∧
    DifferentiableOn ℝ (fderiv ℝ (objectiveModel j)) (Metric.closedBall (x j) (Δ j))
  /-- Each objective model agrees with $f$ at the center. -/
  objective_model_value : ∀ j, objectiveModel j (x j) = f (x j).ofLp
  /-- Each objective model has the derivative of $f$ at the center. -/
  objective_model_derivative : ∀ j, fderiv ℝ (objectiveModel j) (x j) =
    fderiv ℝ (fun y : EuclideanSpace ℝ ι ↦ f y.ofLp) (x j)
  /-- The Hessians of the objective models are bounded on the positive points of the trust regions,
  uniformly in $j$. -/
  objective_model_hessian_bound : ∃ K : ℝ, ∀ j y,
    y ∈ Metric.closedBall (x j) (Δ j) → y ∈ interior (euclideanOrthant (ι := ι)) →
      ‖fderiv ℝ (fderiv ℝ (objectiveModel j)) y‖ ≤ K

/-- **Algorithm 13.6.2** of [conn2000trust]. Let $f : \mathbb{R}^n \to \mathbb{R}$. A **run of the
primal-dual barrier method** consists of outer iterates $(x_k, z_k)$, barrier parameters
$\mu_k$, fractions $\sigma_k$, forcing functions $\varepsilon^D$, $\varepsilon^C$,
$\varepsilon^E$, runs of Algorithm 13.6.1 and stopping indices $J_k$, such that:
* $x_0 > 0$, $z_0 > 0$ and $\mu_k \to 0$;
* $\varepsilon^D(\mu)$, $\varepsilon^C(\mu)$ and $\varepsilon^E(\mu)$ are positive for $\mu > 0$
  and tend to $0$ as $\mu \to 0^+$;
* the $k$-th inner run, with $\sigma_k$ and $\mu_k$, starts at $(x_k, z_k)$ and reaches
  $(x_{k+1}, z_{k+1})$ at the index $J_k$;
* $(x_{k+1}, z_{k+1})$ passes the stopping tests (13.6.5)–(13.6.8) with $\mu_k$,
  $\varepsilon^D(\mu_k)$, $\varepsilon^C(\mu_k)$ and $\varepsilon^E(\mu_k)$, and no earlier
  inner iterate passes them.

The barrier parameters are positive because each inner run requires it. The method joins the
fixed-parameter inner runs at their first stopping indices.

**Correction.** The primal trial must be strictly feasible in addition to having sufficient unsigned
distance from the boundary. A scalar exterior trial can pass the printed distance test. The
execution is specified through run relations using the corrected model and explicitly guarded
acceptance.
-/
structure PrimalDualBarrierOuterRun (P : Chapter06.BTRParams) (f : (ι → ℝ) → ℝ) where
  /-- The primal outer iterates $x_k$. -/
  x : ℕ → ι → ℝ
  /-- The dual outer iterates $z_k$. -/
  z : ℕ → ι → ℝ
  /-- The barrier parameters $\mu_k$. -/
  μ : ℕ → ℝ
  /-- The fractions $\sigma_k$ of the fraction-to-boundary tests. -/
  σ : ℕ → ℝ
  /-- The forcing function $\varepsilon^D$ of the dual residual test. -/
  εD : ℝ → ℝ
  /-- The forcing function $\varepsilon^C$ of the complementarity test. -/
  εC : ℝ → ℝ
  /-- The forcing function $\varepsilon^E$ of the Hessian test. -/
  εE : ℝ → ℝ
  /-- The initial primal iterate is positive. -/
  initial_primal_pos : ∀ i, 0 < x 0 i
  /-- The initial dual iterate is positive. -/
  initial_dual_pos : ∀ i, 0 < z 0 i
  /-- The forcing functions are positive at every positive barrier parameter. -/
  forcing_pos : ∀ μ > 0, 0 < εD μ ∧ 0 < εC μ ∧ 0 < εE μ
  /-- The forcing functions tend to $0$ as the barrier parameter tends to $0$ from above. -/
  forcing_limit : Tendsto εD (𝓝[>] 0) (𝓝 0) ∧ Tendsto εC (𝓝[>] 0) (𝓝 0) ∧
    Tendsto εE (𝓝[>] 0) (𝓝 0)
  /-- The barrier parameters tend to $0$. -/
  parameter_limit : Tendsto μ atTop (𝓝 0)
  /-- The inner runs of Algorithm 13.6.1, the $k$-th with the fraction $\sigma_k$ and the parameter
  $\mu_k$. -/
  inner : ∀ k, PrimalDualBarrierInnerRun P f (σ k) (μ k)
  /-- The stopping indices $J_k$ of the inner runs. -/
  stopIndex : ℕ → ℕ
  /-- The $k$-th inner run starts at $(x_k, z_k)$. -/
  start_inner : ∀ k, ((inner k).x 0).ofLp = x k ∧ (inner k).z 0 = z k
  /-- The $k$-th inner run reaches $(x_{k+1}, z_{k+1})$ at its stopping index. -/
  finish_inner : ∀ k, ((inner k).x (stopIndex k)).ofLp = x (k + 1) ∧
    (inner k).z (stopIndex k) = z (k + 1)
  /-- The next outer iterate passes the stopping tests (13.6.5)–(13.6.8). -/
  stopping_test : ∀ k, PrimalDualBarrierStop f (x (k + 1)) (z (k + 1)) (μ k)
    (εD (μ k)) (εC (μ k)) (εE (μ k))
  /-- No earlier inner iterate passes the stopping tests. -/
  first_stop : ∀ k j, j < stopIndex k →
    ¬ PrimalDualBarrierStop f ((inner k).x j).ofLp ((inner k).z j) (μ k)
      (εD (μ k)) (εC (μ k)) (εE (μ k))

/-- Finite stopping in Theorem 13.6.2 of [conn2000trust] from the inner limits. Let
$f : \mathbb{R}^n \to \mathbb{R}$, $\mu \in \mathbb{R}$, $\varepsilon^D, \varepsilon^C,
\varepsilon^E, M > 0$, and let $x_j > 0$ and $z_j > 0$ with $x_{j,i} \le M$ for all $j$ and $i$.
Assume that for every $i$
$$\partial_i f(x_j) - \frac{\mu}{x_{j,i}} \to 0 \qquad \text{and} \qquad z_{j,i} -
  \frac{\mu}{x_{j,i}} \to 0.$$
Let $(\lambda_j)$ be real numbers that are cobounded from below with $\limsup_j \lambda_j \ge 0$
and $\lambda_j \|d\|^2 \le \nabla^2 f(x_j)[d, d] + \sum_i (z_{j,i} / x_{j,i}) d_i^2$ for all $j$
and $d$. Then infinitely many $(x_j, z_j)$ pass the stopping tests (13.6.5)–(13.6.8).

The upper bound $M$ on the primal coordinates is needed to pass from AA.8 to the unscaled
complementarity test. The curvature bound is that of the primal-dual model used in the stopping
test.

**Correction.** The finite stopping transfer requires an upper bound on primal coordinates to turn
small additive multiplier error into small product error. The extension version also supplies the
clearance and model hypotheses for primal inner convergence. A scalar unbounded run with AA.8 and
frequent success can fail the complementarity test indefinitely.
-/
theorem theorem_13_6_2_of_inner_limits {f : (ι → ℝ) → ℝ} {x z : ℕ → ι → ℝ}
    {μ εD εC εE M : ℝ} (hD : 0 < εD) (hC : 0 < εC) (hE : 0 < εE) (hM : 0 < M)
    (hx : ∀ j i, 0 < x j i) (hz : ∀ j i, 0 < z j i) (hxM : ∀ j i, x j i ≤ M)
    (hgrad : ∀ i, Tendsto (fun j ↦ barrierCoordinateGradient f (x j) i - μ / x j i)
      atTop (𝓝 0))
    (hdual : ∀ i, Tendsto (fun j ↦ z j i - μ / x j i) atTop (𝓝 0))
    {lamMin : ℕ → ℝ} (hbelow : atTop.IsCoboundedUnder (· ≤ ·) lamMin)
    (hlimsup : 0 ≤ limsup lamMin atTop)
    (hmin : ∀ j (d : ι → ℝ), lamMin j * (∑ i, (d i) ^ 2) ≤
      fderiv ℝ (fderiv ℝ f) (x j) d d + ∑ i, (z j i / x j i) * d i * d i) :
    ∃ᶠ j in atTop, PrimalDualBarrierStop f (x j) (z j) μ εD εC εE := by
  have hgs : Tendsto (fun j ↦ ∑ i, (barrierCoordinateGradient f (x j) i - z j i) ^ 2)
      atTop (𝓝 0) := by
    rw [← Finset.sum_const_zero (s := (Finset.univ : Finset ι))]
    apply tendsto_finsetSum Finset.univ
    intro i _
    simpa only [sub_sub_sub_cancel_right, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      ((hgrad i).sub (hdual i)).pow 2
  have hcomp : ∀ᶠ j in atTop, ∀ i, |x j i * z j i - μ| ≤ εC := by
    apply eventually_all.mpr
    intro i
    have hsmall := (continuous_abs.continuousAt.tendsto.comp (hdual i)).eventually
      (gt_mem_nhds (show |(0 : ℝ)| < εC / M by simpa using div_pos hC hM))
    filter_upwards [hsmall] with j hj
    change |z j i - μ / x j i| < εC / M at hj
    have heq : x j i * z j i - μ = x j i * (z j i - μ / x j i) := by
      field_simp [(hx j i).ne']
    rw [heq, abs_mul, abs_of_pos (hx j i)]
    exact (mul_le_mul (hxM j i) hj.le (abs_nonneg _) hM.le).trans_eq
      (mul_div_cancel₀ _ hM.ne')
  have hfreq := frequently_lt_of_lt_limsup hbelow ((neg_lt_zero.mpr hE).trans_le hlimsup)
  refine (hfreq.and_eventually
    ((hgs.eventually (gt_mem_nhds (sq_pos_of_pos hD))).and hcomp)).mono ?_
  intro j hj
  exact ⟨hx j, hz j, hj.2.1.le, hj.2.2, fun d ↦
    (mul_le_mul_of_nonneg_right hj.1.le (Finset.sum_nonneg fun i _ ↦ sq_nonneg (d i))).trans
      (hmin j d)⟩

/-- Primal stopping implies primal-dual stopping in Theorem 13.6.2 of [conn2000trust]. Let
$\varepsilon^D, \varepsilon^C, \varepsilon^E, \delta, M > 0$ and $\mu \in \mathbb{R}$, and let
$x_j$ and $z_j > 0$ with $\delta \le x_{j,i} \le M$ for all $j$ and $i$. Assume AA.8,
$z_{j,i} - \mu / x_{j,i} \to 0$ for every $i$. If infinitely many $x_j$ pass the primal stopping
tests (13.4.3)–(13.4.5) with $\mu$, $\varepsilon^D / 2$ and $\varepsilon^E / 2$, then infinitely
many $(x_j, z_j)$ pass the primal-dual stopping tests (13.6.5)–(13.6.8) with $\mu$,
$\varepsilon^D$, $\varepsilon^C$ and $\varepsilon^E$.

The lower primal bound transfers the Hessian test of the true barrier to the primal-dual
Hessian. The upper bound transfers dual consistency to unscaled complementarity.

**Correction.** The finite stopping transfer requires an upper bound on primal coordinates to turn
small additive multiplier error into small product error. The extension version also supplies the
clearance and model hypotheses for primal inner convergence. A scalar unbounded run with AA.8 and
frequent success can fail the complementarity test indefinitely.
-/
theorem theorem_13_6_2_of_primal_stopping {f : (ι → ℝ) → ℝ} {x z : ℕ → ι → ℝ}
    {μ εD εC εE δ M : ℝ} (hD : 0 < εD) (hC : 0 < εC) (hE : 0 < εE)
    (hδ : 0 < δ) (hM : 0 < M) (hxδ : ∀ j i, δ ≤ x j i) (hxM : ∀ j i, x j i ≤ M)
    (hz : ∀ j i, 0 < z j i)
    (hdual : ∀ i, Tendsto (fun j ↦ z j i - μ / x j i) atTop (𝓝 0))
    (hfreq : ∃ᶠ j in atTop, BarrierSecondOrderStop f (x j) μ (εD / 2) (εE / 2)) :
    ∃ᶠ j in atTop, PrimalDualBarrierStop f (x j) (z j) μ εD εC εE := by
  let e (j : ℕ) (i : ι) := z j i - μ / x j i
  have hsum : Tendsto (fun j ↦ ∑ i, (e j i) ^ 2) atTop (𝓝 0) := by
    rw [← Finset.sum_const_zero (s := (Finset.univ : Finset ι))]
    apply tendsto_finsetSum Finset.univ
    intro i _
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using (hdual i).pow 2
  have hsmall {a : ℝ} (ha : 0 < a) : ∀ᶠ j in atTop, ∀ i, |e j i| ≤ a := by
    apply eventually_all.mpr
    intro i
    have h := (continuous_abs.continuousAt.tendsto.comp (hdual i)).eventually
      (gt_mem_nhds (show |(0 : ℝ)| < a by simpa using ha))
    exact h.mono fun j hj ↦ hj.le
  have hδE : 0 < δ * (εE / 2) := mul_pos hδ (half_pos hE)
  refine (hfreq.and_eventually
    ((hsum.eventually (gt_mem_nhds (sq_pos_of_pos (half_pos hD)))).and
      ((hsmall (div_pos hC hM)).and (hsmall hδE)))).mono ?_
  intro j hj
  obtain ⟨hp, hsumj, hCj, hEj⟩ := hj
  refine ⟨hp.1, hz j, ?_, ?_, ?_⟩
  · let a (i : ι) := barrierCoordinateGradient f (x j) i - μ / x j i
    have hsumle : (∑ i, (barrierCoordinateGradient f (x j) i - z j i) ^ 2) ≤
        ∑ i, (2 * (a i) ^ 2 + 2 * (e j i) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      dsimp [a, e]
      nlinarith [sq_nonneg (barrierCoordinateGradient f (x j) i - μ / x j i + (z j i - μ / x j i))]
    refine hsumle.trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    linarith [hp.2.1]
  · intro i
    have heq : x j i * z j i - μ = x j i * e j i := by
      unfold e
      field_simp [(hp.1 i).ne']
    rw [heq, abs_mul, abs_of_pos (hp.1 i)]
    exact (mul_le_mul (hxM j i) (hCj i) (abs_nonneg _) hM.le).trans_eq
      (mul_div_cancel₀ _ hM.ne')
  · intro d
    have hd (i : ι) : -(εE / 2) ≤ z j i / x j i - μ * ((x j i) ^ 2)⁻¹ := by
      have heq : z j i / x j i - μ * ((x j i) ^ 2)⁻¹ = e j i / x j i := by
        unfold e
        field_simp [(hp.1 i).ne']
      rw [heq]
      apply (le_div_iff₀ (hp.1 i)).mpr
      have hh := (abs_le.mp (hEj i)).1
      have hmul := mul_le_mul_of_nonpos_left (hxδ j i) (show -(εE / 2) ≤ 0 by linarith)
      linarith
    have hcorr := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
      mul_le_mul_of_nonneg_right (hd i) (sq_nonneg (d i)))
    rw [← Finset.mul_sum] at hcorr
    simp_rw [sub_mul, Finset.sum_sub_distrib] at hcorr
    have hh := hp.2.2 d
    rw [Finset.mul_sum (s := Finset.univ) (a := μ)] at hh
    simp only [pow_two, ← mul_assoc] at hcorr hh ⊢
    linarith only [hcorr, hh]

/-- A counterexample for AA.8 without bounded primal iterates in Theorem 13.6.2 of [conn2000trust].
There are real sequences $x_j \ge 1$ and $z_j > 0$ with $z_j - 1/x_j \to 0$ and
$x_j z_j - 1 = 1$ for all $j$.

So AA.8 alone does not make the unscaled complementarity residual tend to zero, even with
positive primal and dual coordinates and a uniform lower bound on the primal coordinates.

**Correction.** The finite stopping transfer requires an upper bound on primal coordinates to turn
small additive multiplier error into small product error. The extension version also supplies the
clearance and model hypotheses for primal inner convergence. A scalar unbounded run with AA.8 and
frequent success can fail the complementarity test indefinitely.
-/
theorem primalDual_complementarity_unbounded_counterexample :
    ∃ x z : ℕ → ℝ, (∀ j, 1 ≤ x j ∧ 0 < z j) ∧
      Tendsto (fun j ↦ z j - 1 / x j) atTop (𝓝 0) ∧
      (∀ j, x j * z j - 1 = 1) := by
  let x (j : ℕ) := (j : ℝ) + 1
  refine ⟨x, fun j ↦ 2 / x j, fun j ↦ ⟨by simp [x], by dsimp [x]; positivity⟩, ?_, ?_⟩
  · have h (j : ℕ) : 2 / x j - 1 / x j = 1 / x j := by rw [← sub_div]; norm_num
    simpa only [h, x] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · intro j
    change x j * (2 / x j) - 1 = 1
    rw [mul_div_cancel₀ _ (show x j ≠ 0 by dsimp [x]; positivity)]
    norm_num

private theorem dual_coordinate_tendsto_zero {α : Type*} {l : Filter α}
    {x z : α → ℝ} (hz : ∀ k, 0 ≤ z k)
    (hp : Tendsto (fun k ↦ x k * z k) l (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) (hx : ∀ᶠ k in l, δ ≤ x k) :
    Tendsto z l (𝓝 0) := by
  apply squeeze_zero' (g := fun k ↦ (x k * z k) / δ) (Eventually.of_forall hz)
  · filter_upwards [hx] with k hk
    exact (le_div_iff₀ hδ).mpr (by
      rw [mul_comm (z k) δ]
      exact mul_le_mul_of_nonneg_right hk (hz k))
  · simpa using hp.div_const δ

/-- **Theorem 13.6.3** of [conn2000trust]. Let $f : \mathbb{R}^n \to \mathbb{R}$, and let
$x_k, z_k \in \mathbb{R}^n$ and numbers $\mu_k$, $\varepsilon^D_k \ge 0$, $\varepsilon^C_k$ and
$\varepsilon^E_k$ be indexed by $k$ in a set with a filter $l$. Assume that $\mu_k$,
$\varepsilon^D_k$, $\varepsilon^C_k$ and $\varepsilon^E_k$ tend to $0$ along $l$ and that each
$(x_k, z_k)$ passes the stopping tests (13.6.5)–(13.6.8) with $\mu_k$, $\varepsilon^D_k$,
$\varepsilon^C_k$ and $\varepsilon^E_k$. Then:
* for every $i$ and every $\eta > 0$, eventually $\partial_i f(x_k) \ge -\eta$;
* for every $i$ such that eventually $x_{k,i} \ge \delta$ for some $\delta > 0$,
  $\partial_i f(x_k) \to 0$;
* for every $d$ whose nonzero coordinates $i$ all satisfy eventually $x_{k,i} \ge \delta$ for
  some $\delta > 0$, and every $\eta > 0$, eventually $\nabla^2 f(x_k)[d, d] \ge -\eta$.

The lower limits are written as eventual inequalities for every positive tolerance.

**Generalization.** The outer limits are derived from the stopping tests along a filter rather than
all of the algorithm convergence assumptions. The completed run specializes the ordered sequence
case.
-/
theorem theorem_13_6_3 {α : Type*} {l : Filter α} {f : (ι → ℝ) → ℝ}
    {x z : α → ι → ℝ} {μ εD εC εE : α → ℝ}
    (hμ : Tendsto μ l (𝓝 0)) (hD : Tendsto εD l (𝓝 0)) (hDpos : ∀ k, 0 ≤ εD k)
    (hC : Tendsto εC l (𝓝 0)) (hE : Tendsto εE l (𝓝 0))
    (hstop : ∀ k, PrimalDualBarrierStop f (x k) (z k) (μ k) (εD k) (εC k) (εE k)) :
    (∀ i η, 0 < η → ∀ᶠ k in l, -η ≤ barrierCoordinateGradient f (x k) i) ∧
    (∀ i, (∃ δ > 0, ∀ᶠ k in l, δ ≤ x k i) →
      Tendsto (fun k ↦ barrierCoordinateGradient f (x k) i) l (𝓝 0)) ∧
    ∀ d : ι → ℝ, (∀ i, d i ≠ 0 → ∃ δ > 0, ∀ᶠ k in l, δ ≤ x k i) →
      ∀ η, 0 < η → ∀ᶠ k in l, -η ≤ fderiv ℝ (fderiv ℝ f) (x k) d d := by
  have hres (k : α) (i : ι) : |barrierCoordinateGradient f (x k) i - z k i| ≤ εD k := by
    apply (sq_le_sq₀ (abs_nonneg _) (hDpos k)).mp
    rw [sq_abs]
    exact (Finset.single_le_sum (fun j _ ↦ sq_nonneg
      (barrierCoordinateGradient f (x k) j - z k j)) (Finset.mem_univ i)).trans (hstop k).2.2.1
  have hprod (i : ι) : Tendsto (fun k ↦ x k i * z k i) l (𝓝 0) := by
    have he : Tendsto (fun k ↦ x k i * z k i - μ k) l (𝓝 0) :=
      squeeze_zero_norm' (Eventually.of_forall fun k ↦ by
        simpa [Real.norm_eq_abs] using (hstop k).2.2.2.1 i) hC
    simpa only [sub_add_cancel, add_zero] using he.add hμ
  have hdual (i : ι) {δ : ℝ} (hδ : 0 < δ) (hxi : ∀ᶠ k in l, δ ≤ x k i) :
      Tendsto (fun k ↦ z k i) l (𝓝 0) :=
    dual_coordinate_tendsto_zero (fun k ↦ ((hstop k).2.1 i).le) (hprod i) hδ hxi
  refine ⟨?_, ?_, ?_⟩
  · intro i η hη
    filter_upwards [hD.eventually (gt_mem_nhds hη)] with k hk
    linarith [(abs_le.mp (hres k i)).1, (hstop k).2.1 i]
  · intro i ⟨δ, hδ, hxi⟩
    have he : Tendsto (fun k ↦ barrierCoordinateGradient f (x k) i - z k i) l (𝓝 0) :=
      squeeze_zero_norm'
        (Eventually.of_forall fun k ↦ by simpa [Real.norm_eq_abs] using hres k i) hD
    simpa only [sub_add_cancel, add_zero] using he.add (hdual i hδ hxi)
  · intro d hd η hη
    have hc : Tendsto (fun k ↦ ∑ i, (z k i / x k i) * d i * d i) l (𝓝 0) := by
      rw [← Finset.sum_const_zero (s := (Finset.univ : Finset ι))]
      apply tendsto_finsetSum Finset.univ
      intro i _
      by_cases hi : d i = 0
      · simpa [hi] using (tendsto_const_nhds : Tendsto (fun _ : α ↦ (0 : ℝ)) l (𝓝 0))
      obtain ⟨δ, hδ, hxi⟩ := hd i hi
      have hr : Tendsto (fun k ↦ z k i / x k i) l (𝓝 0) := by
        apply squeeze_zero' (g := fun k ↦ z k i / δ)
        · exact Eventually.of_forall fun k ↦ div_nonneg ((hstop k).2.1 i).le ((hstop k).1 i).le
        · filter_upwards [hxi] with k hk
          exact div_le_div_of_nonneg_left ((hstop k).2.1 i).le hδ hk
        · simpa using (hdual i hδ hxi).div_const δ
      simpa only [zero_mul] using (hr.mul_const (d i)).mul_const (d i)
    have he := hE.mul_const (∑ i, (d i) ^ 2)
    have hec : Tendsto
        (fun k ↦ εE k * (∑ i, (d i) ^ 2) + ∑ i, (z k i / x k i) * d i * d i) l (𝓝 0) := by
      simpa only [zero_mul, zero_add] using he.add hc
    filter_upwards [hec.eventually (gt_mem_nhds hη)] with k hk
    linarith [(hstop k).2.2.2.2 d]

/-- **Theorem 13.6.3** of [conn2000trust] for a consistently active family. Let $f$, $x_k$, $z_k$,
the parameters and $l$ be as in `ConnGouldToint.Chapter13.theorem_13_6_3`, and assume moreover
that $(x_k)$ is consistently active along $l$. Then $\partial_i f(x_k) \to 0$ for every
coordinate $i$ that is not asymptotically active, and for every $d$ with $d_i = 0$ on the
asymptotically active coordinates and every $\eta > 0$, eventually
$\nabla^2 f(x_k)[d, d] \ge -\eta$.

The free coordinates are exactly those to which the vanishing-gradient and second-order
conclusions apply.

**Generalization.** The outer limits are derived from the stopping tests along a filter rather than
all of the algorithm convergence assumptions. The completed run specializes the ordered sequence
case.
-/
theorem theorem_13_6_3_consistentlyActive {α : Type*} {l : Filter α} {f : (ι → ℝ) → ℝ}
    {x z : α → ι → ℝ} (ha : ConsistentlyActive l x) {μ εD εC εE : α → ℝ}
    (hμ : Tendsto μ l (𝓝 0)) (hD : Tendsto εD l (𝓝 0)) (hDpos : ∀ k, 0 ≤ εD k)
    (hC : Tendsto εC l (𝓝 0)) (hE : Tendsto εE l (𝓝 0))
    (hstop : ∀ k, PrimalDualBarrierStop f (x k) (z k) (μ k) (εD k) (εC k) (εE k)) :
    (∀ i, ¬ AsymptoticallyActive l x i →
      Tendsto (fun k ↦ barrierCoordinateGradient f (x k) i) l (𝓝 0)) ∧
    ∀ d : ι → ℝ, (∀ i, AsymptoticallyActive l x i → d i = 0) →
      ∀ η, 0 < η → ∀ᶠ k in l, -η ≤ fderiv ℝ (fderiv ℝ f) (x k) d d := by
  obtain ⟨_, hg, hH⟩ := theorem_13_6_3 hμ hD hDpos hC hE hstop
  refine ⟨fun i hi ↦ hg i ((ha i).resolve_left hi), ?_⟩
  exact fun d hd ↦ hH d fun i hi ↦ (ha i).resolve_left fun h ↦ hi (hd i h)

/-- **Theorem 13.6.3** of [conn2000trust] for the completed outer iterations of Algorithm 13.6.2.
For a run of the primal-dual barrier method, the primal iterates $x_{k+1}$ satisfy the three
conclusions of `ConnGouldToint.Chapter13.theorem_13_6_3` along $k \to \infty$.

**Generalization.** The outer limits are derived from the stopping tests along a filter rather than
all of the algorithm convergence assumptions. The completed run specializes the ordered sequence
case.
-/
theorem PrimalDualBarrierOuterRun.convergence {P : Chapter06.BTRParams} {f : (ι → ℝ) → ℝ}
    (r : PrimalDualBarrierOuterRun P f) :
    (∀ i η, 0 < η → ∀ᶠ k in atTop, -η ≤ barrierCoordinateGradient f (r.x (k + 1)) i) ∧
    (∀ i, (∃ δ > 0, ∀ᶠ k in atTop, δ ≤ r.x (k + 1) i) →
      Tendsto (fun k ↦ barrierCoordinateGradient f (r.x (k + 1)) i) atTop (𝓝 0)) ∧
    ∀ d : ι → ℝ, (∀ i, d i ≠ 0 → ∃ δ > 0, ∀ᶠ k in atTop, δ ≤ r.x (k + 1) i) →
      ∀ η, 0 < η → ∀ᶠ k in atTop, -η ≤ fderiv ℝ (fderiv ℝ f) (r.x (k + 1)) d d := by
  have hμpos (k : ℕ) := (r.inner k).barrier_parameter_pos
  have hμ : Tendsto r.μ atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨r.parameter_limit, Eventually.of_forall hμpos⟩
  exact theorem_13_6_3 r.parameter_limit (r.forcing_limit.1.comp hμ)
    (fun k ↦ (r.forcing_pos _ (hμpos k)).1.le) (r.forcing_limit.2.1.comp hμ)
    (r.forcing_limit.2.2.comp hμ) r.stopping_test

/-! ### The dual safeguard -/

/-- **Equation (13.6.16)** of [conn2000trust], one coordinate. For a barrier parameter $\mu$, a
primal coordinate $x$, a dual coordinate $z$ and a step $s$, the **predicted multiplier** is
$$\frac{\mu}{x} - \frac{z}{x} s.$$

**Reading.** The projection and interval endpoints are written as scalar minimum and maximum
operations, applied independently to each coordinate. The formula is total via division by zero;
feasibility proofs require positive primal coordinates and parameter.
-/
noncomputable def primalDualPredictedMultiplier (μ x z s : ℝ) : ℝ := μ / x - z / x * s

private noncomputable def dualSafeguardLower (l μ y z : ℝ) : ℝ := l * min 1 (min z (μ / y))

private noncomputable def dualSafeguardUpper (u μ y z : ℝ) : ℝ :=
  max u (max z (max (u / μ) (u * (μ / y))))

/-- **Equations (13.6.17)–(13.6.19)** of [conn2000trust] on a successful iteration. For constants
$l$ and $u$, a barrier parameter $\mu$, a primal coordinate $x$, its new value $y$, a dual
coordinate $z$ and a step $s$, the **safeguarded multiplier** is the projection of the predicted
multiplier (13.6.16) onto the interval $[L, U]$:
$$\max\left\{L, \min\left\{U, \frac{\mu}{x} - \frac{z}{x} s\right\}\right\}, \qquad L = l
  \min\left\{1, z, \frac{\mu}{y}\right\}, \quad U = \max\left\{u, z, \frac{u}{\mu}, \frac{u
  \mu}{y}\right\}.$$

An unsuccessful iteration keeps the old multiplier.

**Reading.** The projection and interval endpoints are written as scalar minimum and maximum
operations, applied independently to each coordinate. The formula is total via division by zero;
feasibility proofs require positive primal coordinates and parameter.
-/
noncomputable def primalDualSafeguard (l u μ x y z s : ℝ) : ℝ :=
  max (dualSafeguardLower l μ y z)
    (min (dualSafeguardUpper u μ y z) (primalDualPredictedMultiplier μ x z s))

private theorem safeguard_bounds {l u μ y z : ℝ} (hl : 0 < l) (hl' : l < 1) (hu : 1 < u)
    (hμ : 0 < μ) (hy : 0 < y) (hz : 0 < z) :
    0 < dualSafeguardLower l μ y z ∧
      dualSafeguardLower l μ y z ≤ μ / y ∧ μ / y ≤ dualSafeguardUpper u μ y z := by
  have h : 0 < μ / y := div_pos hμ hy
  have hmin : min 1 (min z (μ / y)) ≤ μ / y :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨mul_pos hl (lt_min zero_lt_one (lt_min hz h)), ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hmin hl.le).trans
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hl'.le) h.le])
  · exact (show μ / y ≤ u * (μ / y) by nlinarith [mul_nonneg (sub_nonneg.mpr hu.le) h.le]).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

/-- **Theorem 13.6.4** of [conn2000trust], positivity and AA.7. Let $0 < l < 1 < u$, $\mu > 0$ and
$\varepsilon > 0$, and let $x_j$, $z_j$ and $s_j$ be real sequences with $x_j \ge \varepsilon$
for all $j$ and $z_0 > 0$. Assume that $z_{j+1}$ is the safeguarded multiplier
(13.6.17)–(13.6.19) for $x_j$, $x_{j+1}$, $z_j$ and $s_j$ on the successful iterations, and
$z_{j+1} = z_j$ on the others. Then for all $j$,
$$0 < z_j \le \max\left\{u, z_0, \frac{u}{\mu}, \frac{u \mu}{\varepsilon}\right\}.$$

The layer $x_j \ge \varepsilon$ is (13.6.21). The theorem gives the explicit uniform bound from
the proof of the source.

**Correction.** Positivity and a uniform bound use a positive primal lower bound. For the printed
update the AA.8 limit also needs infinitely many successes when displacements vanish. A reset to the
exact dual after a rejected trial yields consistency under vanishing accepted displacements, and the
all-rejected example shows failure without either condition.
-/
theorem theorem_13_6_4 {x z s : ℕ → ℝ} {success : ℕ → Prop} [DecidablePred success]
    {l u μ ε : ℝ} (hl : 0 < l) (hl' : l < 1) (hu : 1 < u) (hμ : 0 < μ)
    (hε : 0 < ε) (hx : ∀ j, ε ≤ x j) (hz : 0 < z 0)
    (hupdate : ∀ j, z (j + 1) = if success j then
      primalDualSafeguard l u μ (x j) (x (j + 1)) (z j) (s j) else z j) :
    ∀ j, 0 < z j ∧ z j ≤ max u (max (z 0) (max (u / μ) (u * (μ / ε)))) := by
  let B := max u (max (z 0) (max (u / μ) (u * (μ / ε))))
  have hzB : z 0 ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  intro j
  induction j with
  | zero => exact ⟨hz, hzB⟩
  | succ j ih =>
    by_cases hs : success j
    · rw [hupdate, ite_eq_left hs]
      obtain ⟨hlo, hle, hhi⟩ :=
        safeguard_bounds hl hl' hu hμ (hε.trans_le (hx (j + 1))) ih.1
      refine ⟨hlo.trans_le (le_max_left _ _), max_le (hle.trans (hhi.trans ?_))
        ((min_le_left _ _).trans ?_)⟩ <;>
        exact max_le (le_max_left _ _) (max_le ih.2 (max_le
          ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
          ((mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left hμ.le hε (hx (j + 1))) (zero_lt_one.trans hu).le).trans
              ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))))
    · rwa [hupdate, ite_eq_right hs]

private theorem dualSafeguard_error_le {l u μ ε B x y z s : ℝ}
    (hl : 0 < l) (hl' : l < 1) (hu : 1 < u) (hμ : 0 < μ) (hε : 0 < ε)
    (hx : ε ≤ x) (hy : ε ≤ y) (hz : 0 < z) (hzB : z ≤ B) (hyx : y = x + s) :
    |primalDualSafeguard l u μ x y z s - μ / y| ≤ (μ / (ε * ε) + B / ε) * |s| := by
  obtain ⟨_, hlow, hhigh⟩ := safeguard_bounds hl hl' hu hμ (hε.trans_le hy) hz
  have hx' := hε.trans_le hx
  have hy' := hε.trans_le hy
  let p := primalDualPredictedMultiplier μ x z s
  have hclip : |primalDualSafeguard l u μ x y z s - μ / y| ≤ |p - μ / y| := by
    apply abs_le.mpr
    have hab := abs_le.mp (le_refl |p - μ / y|)
    unfold primalDualSafeguard
    change -|p - μ / y| ≤ max _ (min _ p) - μ / y ∧
      max _ (min _ p) - μ / y ≤ |p - μ / y|
    constructor
    · apply le_sub_iff_add_le.mpr
      exact (le_min (by linarith [abs_nonneg (p - μ / y)]) (by linarith [hab.1])).trans
        (le_max_right _ _)
    · apply sub_le_iff_le_add.mpr
      exact max_le (by linarith [abs_nonneg (p - μ / y)])
        ((min_le_right _ _).trans (by linarith [hab.2]))
  refine hclip.trans ?_
  have heq : p - μ / y = (μ / (x * y) - z / x) * s := by
    unfold p primalDualPredictedMultiplier
    field_simp [hx'.ne', hy'.ne']
    rw [hyx]
    ring
  rw [heq, abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg s)
  exact (abs_sub _ _).trans (add_le_add
    (by rw [abs_of_pos (div_pos hμ (mul_pos hx' hy'))]
        exact div_le_div_of_nonneg_left hμ.le (mul_pos hε hε) (mul_le_mul hx hy hε.le hx'.le))
    (by rw [abs_of_pos (div_pos hz hx')]
        exact (div_le_div_of_nonneg_right hzB hx'.le).trans
          (div_le_div_of_nonneg_left (hz.le.trans hzB) hε hx)))

/-- **Theorem 13.6.4** of [conn2000trust], AA.8 with infinitely many successful iterations. Let
$0 < l < 1 < u$, $\mu > 0$, $\varepsilon > 0$, and let $x_j \ge \varepsilon$, $z_j$ and $s_j$ be
real sequences with $z_0 > 0$ and $s_j \to 0$. Assume that $x_{j+1} = x_j + s_j$ and $z_{j+1}$
is the safeguarded multiplier (13.6.17)–(13.6.19) on the successful iterations, and
$x_{j+1} = x_j$ and $z_{j+1} = z_j$ on the others. If infinitely many iterations are successful,
then $z_j - \mu / x_j \to 0$.

**Correction.** The statement assumes infinitely many successful iterations. Without them AA.8
can fail; see `ConnGouldToint.Chapter13.theorem_13_6_4_all_rejected_counterexample`.

The projection cannot increase the error relative to the exact multiplier $\mu / x_{j+1}$,
because the projection interval contains it. So the predictor need not lie eventually strictly
inside the interval.

**Correction.** Positivity and a uniform bound use a positive primal lower bound. For the printed
update the AA.8 limit also needs infinitely many successes when displacements vanish. A reset to the
exact dual after a rejected trial yields consistency under vanishing accepted displacements, and the
all-rejected example shows failure without either condition.
-/
theorem theorem_13_6_4_aa8_of_frequently_successful
    {x z s : ℕ → ℝ} {success : ℕ → Prop} [DecidablePred success]
    {l u μ ε : ℝ} (hl : 0 < l) (hl' : l < 1) (hu : 1 < u) (hμ : 0 < μ)
    (hε : 0 < ε) (hx : ∀ j, ε ≤ x j) (hz : 0 < z 0)
    (hprimal : ∀ j, x (j + 1) = if success j then x j + s j else x j)
    (hupdate : ∀ j, z (j + 1) = if success j then
      primalDualSafeguard l u μ (x j) (x (j + 1)) (z j) (s j) else z j)
    (hs : Tendsto s atTop (𝓝 0)) (hfreq : ∃ᶠ j in atTop, success j) :
    Tendsto (fun j ↦ z j - μ / x j) atTop (𝓝 0) := by
  let B := max u (max (z 0) (max (u / μ) (u * (μ / ε))))
  have hb := theorem_13_6_4 hl hl' hu hμ hε hx hz hupdate
  have hs0 : Tendsto (fun j ↦ (μ / (ε * ε) + B / ε) * |s j|) atTop (𝓝 0) := by
    simpa using ((continuous_abs.continuousAt.tendsto.comp hs).const_mul
      (μ / (ε * ε) + B / ε))
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hs0.eventually (gt_mem_nhds hδ))
  obtain ⟨J, hJ, hsucc⟩ := (frequently_atTop.mp hfreq) N
  have hlate (j : ℕ) (hj : N ≤ j) (ha : success j) :
      dist (z (j + 1) - μ / x (j + 1)) 0 < δ := by
    rw [Real.dist_eq, sub_zero, hupdate, ite_eq_left ha]
    exact (dualSafeguard_error_le hl hl' hu hμ hε (hx j) (hx (j + 1))
      (hb j).1 (hb j).2 (by rw [hprimal, ite_eq_left ha])).trans_lt (hN j hj)
  refine ⟨J + 1, fun n hn ↦ ?_⟩
  induction n, hn using Nat.le_induction with
  | base => exact hlate J hJ hsucc
  | succ j hj ih =>
    by_cases ha : success j
    · exact hlate j (hJ.trans (Nat.le_succ J |>.trans hj)) ha
    · rwa [hprimal, hupdate, ite_eq_right ha, ite_eq_right ha]

/-- **Theorem 13.6.4** of [conn2000trust] with the corrected safeguard update. Let $0 < l < 1 < u$,
$\mu > 0$, $\varepsilon > 0$, and let $x_j \ge \varepsilon$, $z_j$ and $s_j$ be real sequences
with $z_0 > 0$ and $x_{j+1} - x_j \to 0$. Assume that $x_{j+1} = x_j + s_j$ and $z_{j+1}$ is the
safeguarded multiplier (13.6.17)–(13.6.19) on the successful iterations, and $x_{j+1} = x_j$ and
$z_{j+1} = \mu / x_{j+1}$ on the others. Then for all $j$
$$0 < z_j \le \max\left\{u, z_0, \frac{u}{\mu}, \frac{u \mu}{\varepsilon}\right\},$$
and $z_j - \mu / x_j \to 0$.

**Correction.** After a rejection, the dual coordinate is reset to the exact barrier multiplier
instead of being kept. This is the ordinary projection with zero effective step, so positivity,
AA.7 and AA.8 hold without infinitely many successful trials.

**Correction.** Positivity and a uniform bound use a positive primal lower bound. For the printed
update the AA.8 limit also needs infinitely many successes when displacements vanish. A reset to the
exact dual after a rejected trial yields consistency under vanishing accepted displacements, and the
all-rejected example shows failure without either condition.
-/
theorem theorem_13_6_4_aa8_of_reset_rejected
    {x z s : ℕ → ℝ} {success : ℕ → Prop} [DecidablePred success]
    {l u μ ε : ℝ} (hl : 0 < l) (hl' : l < 1) (hu : 1 < u) (hμ : 0 < μ)
    (hε : 0 < ε) (hx : ∀ j, ε ≤ x j) (hz : 0 < z 0)
    (hprimal : ∀ j, x (j + 1) = if success j then x j + s j else x j)
    (hupdate : ∀ j, z (j + 1) = if success j then
      primalDualSafeguard l u μ (x j) (x (j + 1)) (z j) (s j) else μ / x (j + 1))
    (hs : Tendsto (fun j ↦ x (j + 1) - x j) atTop (𝓝 0)) :
    (∀ j, 0 < z j ∧ z j ≤ max u (max (z 0) (max (u / μ) (u * (μ / ε))))) ∧
    Tendsto (fun j ↦ z j - μ / x j) atTop (𝓝 0) := by
  have hp (j : ℕ) : 0 < x j := hε.trans_le (hx j)
  have hzpos (j : ℕ) : 0 < z j := by
    induction j with
    | zero => exact hz
    | succ j ih =>
      rw [hupdate]
      split_ifs
      · exact (safeguard_bounds hl hl' hu hμ (hp (j + 1)) ih).1.trans_le (le_max_left _ _)
      · exact div_pos hμ (hp (j + 1))
  let t (j : ℕ) := if success j then s j else 0
  have ht : Tendsto t atTop (𝓝 0) := by
    have he (j : ℕ) : x (j + 1) - x j = t j := by
      rw [hprimal]
      unfold t
      split_ifs <;> ring
    simpa only [he] using hs
  have hpr (j : ℕ) : x (j + 1) = if True then x j + t j else x j := by
    simp only [ite_true]
    rw [hprimal]
    unfold t
    split_ifs <;> simp
  have hdu (j : ℕ) : z (j + 1) =
      if True then primalDualSafeguard l u μ (x j) (x (j + 1)) (z j) (t j) else z j := by
    simp only [ite_true]
    by_cases hj : success j
    · simp [hupdate j, t, hj]
    · have hxe : x (j + 1) = x j := by rw [hprimal, ite_eq_right hj]
      rw [hupdate, ite_eq_right hj]
      obtain ⟨_, hlo, hhi⟩ := safeguard_bounds hl hl' hu hμ (hp j) (hzpos j)
      simp only [t, ite_eq_right hj, hxe, primalDualSafeguard, primalDualPredictedMultiplier,
        mul_zero, sub_zero, min_eq_right hhi, max_eq_right hlo]
  exact ⟨theorem_13_6_4 (success := fun _ ↦ True) hl hl' hu hμ hε hx hz hdu,
    theorem_13_6_4_aa8_of_frequently_successful (success := fun _ ↦ True)
      hl hl' hu hμ hε hx hz hpr hdu ht (frequently_atTop.mpr fun N ↦ ⟨N, le_rfl, trivial⟩)⟩

/-- An iteration $j$ of a run of Algorithm 13.6.1 of [conn2000trust] is **successful** if its
guarded ratio, computed with the actual primal-dual model, is at least $\eta_1$.

**Correction.** The primal trial must be strictly feasible in addition to having sufficient unsigned
distance from the boundary. A scalar exterior trial can pass the printed distance test. The
execution is specified through run relations using the corrected model and explicitly guarded
acceptance.
-/
def PrimalDualBarrierInnerRun.Successful {P : Chapter06.BTRParams} {f : (ι → ℝ) → ℝ} {σ μ : ℝ}
    (r : PrimalDualBarrierInnerRun P f σ μ) (j : ℕ) : Prop :=
  P.η₁ ≤ primalBarrierRatio (euclideanOrthant (ι := ι)) σ
    (fun x ↦ logBarrierObjective f x.ofLp μ) (r.model j) (r.x j) (r.s j)

omit [DecidableEq ι] in
/-- Coordinatewise AA.8 for a run of Algorithm 13.6.1 of [conn2000trust] with the corrected
safeguard. Let $0 < l < 1 < u$ and $\delta > 0$, and consider a run with barrier parameter
$\mu$, primal iterates $x_j$ and duals $z_j$ such that $x_{j,i} \ge \delta$ for all $j$ and $i$,
and $x_{j+1} - x_j \to 0$. Assume that on each successful iteration $z_{j+1,i}$ is the
safeguarded multiplier (13.6.17)–(13.6.19) for $x_{j,i}$, $x_{j+1,i}$, $z_{j,i}$ and $s_{j,i}$,
and that on each unsuccessful iteration $z_{j+1,i} = \mu / x_{j+1,i}$. Then
$z_{j,i} - \mu / x_{j,i} \to 0$ for every $i$.

**Correction.** Positivity and a uniform bound use a positive primal lower bound. For the printed
update the AA.8 limit also needs infinitely many successes when displacements vanish. A reset to the
exact dual after a rejected trial yields consistency under vanishing accepted displacements, and the
all-rejected example shows failure without either condition.
-/
theorem PrimalDualBarrierInnerRun.dual_consistent_of_reset_rejected
    {P : Chapter06.BTRParams} {f : (ι → ℝ) → ℝ} {σ μ : ℝ}
    (r : PrimalDualBarrierInnerRun P f σ μ) {l u δ : ℝ}
    (hl : 0 < l) (hl' : l < 1) (hu : 1 < u)
    (hδ : 0 < δ) (hx : ∀ j i, δ ≤ (r.x j).ofLp i)
    (hstep : Tendsto (fun j ↦ r.x (j + 1) - r.x j) atTop (𝓝 0))
    (haccept : ∀ j i, r.Successful j → r.z (j + 1) i =
      primalDualSafeguard l u μ ((r.x j).ofLp i) ((r.x (j + 1)).ofLp i) (r.z j i) ((r.s j).ofLp i))
    (hreject : ∀ j i, ¬r.Successful j → r.z (j + 1) i = μ / (r.x (j + 1)).ofLp i) :
    ∀ i, Tendsto (fun j ↦ r.z j i - μ / (r.x j).ofLp i) atTop (𝓝 0) := by
  classical
  intro i
  have hpr (j : ℕ) : (r.x (j + 1)).ofLp i =
      if r.Successful j then (r.x j).ofLp i + (r.s j).ofLp i else (r.x j).ofLp i := by
    rw [r.iterate_update]
    unfold PrimalDualBarrierInnerRun.Successful
    split_ifs <;> rfl
  let T := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)
  have hc : Continuous (fun x : EuclideanSpace ℝ ι ↦ x.ofLp i) :=
    (continuous_apply i).comp T.continuous
  have hs : Tendsto (fun j ↦ (r.x (j + 1)).ofLp i - (r.x j).ofLp i) atTop (𝓝 0) := by
    have hh := hc.continuousAt.tendsto.comp hstep
    change Tendsto (fun j ↦ (r.x (j + 1) - r.x j).ofLp i) atTop
      (𝓝 ((0 : EuclideanSpace ℝ ι).ofLp i)) at hh
    simpa only [WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_zero, Pi.zero_apply] using hh
  exact (theorem_13_6_4_aa8_of_reset_rejected (success := r.Successful) hl hl' hu
    r.barrier_parameter_pos hδ (fun j ↦ hx j i) (r.dual_pos 0 i) hpr
    (fun j ↦ by
      by_cases h : r.Successful j
      · rw [ite_eq_left h]
        exact haccept j i h
      · rw [ite_eq_right h]
        exact hreject j i h) hs).2

/-- **Theorem 13.6.2** of [conn2000trust], corrected, from the inner limits of an extension. Let
$n \ge 1$, $\varepsilon^D, \varepsilon^C, \varepsilon^E, \delta, M > 0$, let
$f : \mathbb{R}^n \to \mathbb{R}$ and $F$ on the Euclidean space $\mathbb{R}^n$ be twice
continuously differentiable, and consider a run of Algorithm 13.6.1 with barrier parameter
$\mu$, primal iterates $x_j$ and duals $z_j$ such that $\delta \le x_{j,i} \le M$ for all $j$
and $i$. Assume that $F$ agrees with the barrier objective $f + b_\mu$ near each $x_j$, that
$\|D F(x_j)\| \to 0$, that for every $\varepsilon > 0$ infinitely many $j$ have
$\lambda(\nabla^2 F(x_j)) > -\varepsilon$, and that $\|D F(x_j)\| \to 0$ implies AA.8,
$z_{j,i} - \mu / x_{j,i} \to 0$ for all $i$. Then infinitely many $(x_j, z_j)$ pass the stopping
tests (13.6.5)–(13.6.8).

Here $\lambda(H)$ is `ConnGouldToint.Chapter06.leastUnitCurvature`. The derivative and curvature
limits can come from the run's own acceptance ratios through
`ConnGouldToint.Chapter13.theorem_13_4_2_inner_of_extension`, applied to its run of Algorithm
13.3.1. AA.8 then transfers both limits to the dual stopping tests.

**Correction.** The finite stopping transfer requires an upper bound on primal coordinates to turn
small additive multiplier error into small product error. The extension version also supplies the
clearance and model hypotheses for primal inner convergence. A scalar unbounded run with AA.8 and
frequent success can fail the complementarity test indefinitely.
-/
theorem PrimalDualBarrierInnerRun.frequently_stop_of_extension_limits [Nonempty ι]
    {P : Chapter06.BTRParams} {f : (ι → ℝ) → ℝ} {σ μ : ℝ}
    (r : PrimalDualBarrierInnerRun P f σ μ) {F : EuclideanSpace ℝ ι → ℝ}
    {εD εC εE δ M : ℝ} (hD : 0 < εD) (hC : 0 < εC) (hE : 0 < εE)
    (hf : ContDiff ℝ 2 f) (hF : ContDiff ℝ 2 F)
    (hδ : 0 < δ) (hM : 0 < M)
    (hxδ : ∀ j i, δ ≤ (r.x j).ofLp i) (hxM : ∀ j i, (r.x j).ofLp i ≤ M)
    (hlocal : ∀ j, (F ∘ barrierEuclideanCoordinates) =ᶠ[𝓝 (r.x j).ofLp]
      fun y ↦ logBarrierObjective f y μ)
    (hgrad : Tendsto (fun j ↦ ‖fderiv ℝ F (r.x j)‖) atTop (𝓝 0))
    (hcurv : ∀ ε > (0 : ℝ), ∃ᶠ j in atTop, -ε <
      Chapter06.leastUnitCurvature (fderiv ℝ (fderiv ℝ F) (r.x j)))
    (hAA8 : Tendsto (fun j ↦ ‖fderiv ℝ F (r.x j)‖) atTop (𝓝 0) →
      ∀ i, Tendsto (fun j ↦ r.z j i - μ / (r.x j).ofLp i) atTop (𝓝 0)) :
    ∃ᶠ j in atTop, PrimalDualBarrierStop f (r.x j).ofLp (r.z j) μ εD εC εE := by
  have hprimal := theorem_13_4_2_of_local_extension (half_pos hD) (half_pos hE)
    hf hF (fun j i ↦ hδ.trans_le (hxδ j i)) hlocal hgrad hcurv
  exact theorem_13_6_2_of_primal_stopping hD hC hE hδ hM hxδ hxM r.dual_pos
    (hAA8 hgrad) hprimal

/-- **Theorem 13.6.2** of [conn2000trust], corrected inner convergence for Algorithm 13.6.1. Let
$n \ge 1$ and $\varepsilon^D, \varepsilon^C, \varepsilon^E, \delta, M > 0$. Consider a run of
Algorithm 13.6.1 with barrier parameter $\mu$, fraction $\sigma$, primal iterates $x_j$, duals
$z_j$, steps $s_j$, radii $\Delta_j$, models $m_j$, gradients $g_j$, curvature bounds $\beta_j$
and least-curvature measures $\tau_j$, with $\delta \le x_{j,i} \le M$ for all $j$ and $i$. Let
$f$ and $F$ be twice continuously differentiable, with $F$ bounded below on the Euclidean space
$\mathbb{R}^n$, $\|\nabla^2 F\| \le L$, $F = f + b_\mu$ near each $x_j$, and
$F(x_j + s_j) = (f + b_\mu)(x_j + s_j)$. Let $D, G, T > 0$, and assume for all $j$:
* $D \le (1 - \sigma) \operatorname{dist}(x_j, \partial \mathbb{R}^n_+)$;
* $1 \le \beta_j \le K$, $\|g_j\| \le G$, $|\tau_j| \le T$ and
  $\tau_j = \min\{0, \lambda(\nabla^2 m_j(x_j))\}$;
* $F(x_j) = m_j(x_j)$, $D F(x_j) = D m_j(x_j)$ and $|F(x_j + s_j) - m_j(x_j + s_j)| \le K
  \Delta_j^2$;
* $m_j$ and $D m_j$ are differentiable on the segment $[x_j, x_j + s_j]$.

Assume further the uniform Hessian variation on short segments of
`ConnGouldToint.Chapter13.theorem_13_4_2_inner_of_extension`, AM.5 for $F$, and that
$\|g_j\| \to 0$ implies AA.8, $z_{j,i} - \mu / x_{j,i} \to 0$ for all $i$. Then infinitely many
$(x_j, z_j)$ pass the stopping tests (13.6.5)–(13.6.8).

**Correction.** The theorem assumes bounded primal coordinates, a smooth extension that
preserves the actual acceptance ratios, uniform model estimates and AA.8. Under the printed
hypotheses the inner algorithm need not stop; see
`ConnGouldToint.Chapter13.theorem_13_6_2_unbounded_run_counterexample`.

The extension lets the capped trust-region convergence proof use the actual primal-dual ratios.
The bounded primal layer and AA.8 transfer its two limits to all three primal-dual stopping
inequalities.

**Correction.** The finite stopping transfer requires an upper bound on primal coordinates to turn
small additive multiplier error into small product error. The extension version also supplies the
clearance and model hypotheses for primal inner convergence. A scalar unbounded run with AA.8 and
frequent success can fail the complementarity test indefinitely.
-/
theorem PrimalDualBarrierInnerRun.frequently_stop_of_extension [Nonempty ι]
    {P : Chapter06.BTRParams} {f : (ι → ℝ) → ℝ} {σ μ : ℝ}
    (r : PrimalDualBarrierInnerRun P f σ μ) {F : EuclideanSpace ℝ ι → ℝ}
    {εD εC εE δ M K L D G T : ℝ}
    (hD : 0 < εD) (hC : 0 < εC) (hE : 0 < εE)
    (hf : ContDiff ℝ 2 f) (hF : ContDiff ℝ 2 F) (hlower : BddBelow (range F))
    (hδ : 0 < δ) (hM : 0 < M)
    (hxδ : ∀ j i, δ ≤ (r.x j).ofLp i) (hxM : ∀ j i, (r.x j).ofLp i ≤ M)
    (hlocal : ∀ j, (F ∘ barrierEuclideanCoordinates) =ᶠ[𝓝 (r.x j).ofLp]
      fun y ↦ logBarrierObjective f y μ)
    (htrial : ∀ j, F (r.x j + r.s j) = logBarrierObjective f (r.x j + r.s j).ofLp μ)
    (hDp : 0 < D) (hG : 0 < G) (hT : 0 < T)
    (hclear : ∀ j, D ≤ (1 - σ) * Metric.infDist (r.x j) (frontier (euclideanOrthant (ι := ι))))
    (hH : ∀ y, ‖fderiv ℝ (fderiv ℝ F) y‖ ≤ L)
    (hβ₁ : ∀ j, 1 ≤ r.β j) (hβK : ∀ j, r.β j ≤ K)
    (hGbd : ∀ j, ‖r.g j‖ ≤ G) (hτbd : ∀ j, |r.τ j| ≤ T)
    (hτ : ∀ j, r.τ j = min 0
      (Chapter06.leastUnitCurvature (fderiv ℝ (fderiv ℝ (r.model j)) (r.x j))))
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
    (hagree : Chapter06.ModelHessianAgreement F r.model r.x)
    (hAA8 : Tendsto (fun j ↦ ‖r.g j‖) atTop (𝓝 0) →
      ∀ i, Tendsto (fun j ↦ r.z j i - μ / (r.x j).ofLp i) atTop (𝓝 0)) :
    ∃ᶠ j in atTop, PrimalDualBarrierStop f (r.x j).ofLp (r.z j) μ εD εC εE := by
  have hx (j : ℕ) : F (r.x j) = logBarrierObjective f (r.x j).ofLp μ := by
    have hh := (hlocal j).eq_of_nhds
    change F (WithLp.toLp 2 (r.x j).ofLp) = _ at hh
    rwa [WithLp.toLp_ofLp] at hh
  obtain ⟨hg, hc⟩ := theorem_13_4_2_inner_of_extension r.toSecondPrimalBarrierInnerRun hx htrial
    hF hlower hDp hG hT hclear hH hβ₁ hβK hGbd hτbd hτ hval hgrad herr hm hDm hvar hagree
  apply r.frequently_stop_of_extension_limits hD hC hE hf hF hδ hM hxδ hxM hlocal hg hc
  intro h
  apply hAA8
  have he (j : ℕ) : ‖r.g j‖ = ‖fderiv ℝ F (r.x j)‖ := by
    rw [r.gradient_model]
    unfold gradient
    rw [LinearIsometryEquiv.norm_map, hgrad]
  simpa only [he] using h

/-- A counterexample for the safeguard of Theorem 13.6.4 of [conn2000trust] when all later steps are
rejected. There are real sequences $x_j \ge 1$, $z_j > 0$ and $s_j \to 0$ with $x_{j+1} = x_j$
and $z_{j+1} = z_j$ for all $j$, such that $z_j - 1/x_j$ does not tend to $0$.

Holding both iterates on a rejected step cannot transfer a limit over the successful indices to
the full sequence.

**Correction.** Positivity and a uniform bound use a positive primal lower bound. For the printed
update the AA.8 limit also needs infinitely many successes when displacements vanish. A reset to the
exact dual after a rejected trial yields consistency under vanishing accepted displacements, and the
all-rejected example shows failure without either condition.
-/
theorem primalDual_safeguard_stalled_counterexample :
    ∃ x z s : ℕ → ℝ, (∀ j, 1 ≤ x j ∧ 0 < z j) ∧ Tendsto s atTop (𝓝 0) ∧
      (∀ j, x (j + 1) = x j ∧ z (j + 1) = z j) ∧
      ¬ Tendsto (fun j ↦ z j - 1 / x j) atTop (𝓝 0) := by
  refine ⟨fun _ ↦ 1, fun _ ↦ 2, fun _ ↦ 0, by norm_num, tendsto_const_nhds, by simp, ?_⟩
  intro h
  have h' : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 0) := by
    convert h using 1
    norm_num
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h')

/-! ### A run that never stops in Theorem 13.6.2 -/

section EscapeExample

open Metric

private def escapeBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

private noncomputable def escapeTail (x : ℝ) : ℝ := Real.log x + x⁻¹

/-- A globally smooth objective on $\mathbb{R}$ that equals $\log x + 1/x$ for $|x| \ge 2$. It is
$(1 - \psi(x))(\log x + 1/x)$, where $\psi$ is a smooth bump function equal to $1$ on $[-1, 1]$
and to $0$ outside $(-2, 2)$. -/
noncomputable def primalDualEscapeObjective (x : ℝ) : ℝ := (1 - escapeBump x) * escapeTail x

private theorem escape_eq_zero {x : ℝ} (hx : |x| < 1) :
    primalDualEscapeObjective =ᶠ[𝓝 x] fun _ ↦ 0 := by
  have hx' : x ∈ ball (0 : ℝ) 1 := by simpa [Real.dist_eq] using hx
  filter_upwards [isOpen_ball.mem_nhds hx'] with y hy
  simp [primalDualEscapeObjective, escapeBump.one_of_mem_closedBall (ball_subset_closedBall hy)]

private theorem escape_eq_tail {x : ℝ} (hx : 2 < |x|) :
    primalDualEscapeObjective =ᶠ[𝓝 x] escapeTail := by
  have hx' : x ∈ (closedBall (0 : ℝ) 2)ᶜ := by simpa [Real.dist_eq] using hx.not_ge
  filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hx'] with y hy
  have hby : escapeBump y = 0 :=
    escapeBump.zero_of_le_dist (le_of_not_ge (show y ∉ closedBall (0 : ℝ) 2 from hy))
  simp [primalDualEscapeObjective, hby]

private theorem escape_contDiff : ContDiff ℝ 2 primalDualEscapeObjective := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    exact contDiffAt_const.congr_of_eventuallyEq (escape_eq_zero (x := 0) (by norm_num))
  have ht : ContDiffAt ℝ 2 escapeTail x :=
    (contDiffAt_id.log hx).add (contDiffAt_id.inv hx)
  exact (contDiffAt_const.sub (escapeBump.contDiff (n := 2)).contDiffAt).mul ht

private theorem escapeTail_deriv {x : ℝ} (hx : x ≠ 0) :
    deriv escapeTail x = x⁻¹ - (x ^ 2)⁻¹ := by
  have h := (Real.hasDerivAt_log hx).add ((hasDerivAt_id x).inv hx)
  have he := h.deriv
  change deriv escapeTail x = _ at he
  simpa [div_eq_mul_inv, sub_eq_add_neg] using he

private theorem escapeTail_deriv_deriv {x : ℝ} (hx : x ≠ 0) :
    deriv (deriv escapeTail) x = -(x ^ 2)⁻¹ + 2 * (x ^ 3)⁻¹ := by
  have he : deriv escapeTail =ᶠ[𝓝 x] fun y ↦ y⁻¹ - (y ^ 2)⁻¹ := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact escapeTail_deriv hy
  rw [he.deriv_eq]
  have h := ((hasDerivAt_id x).inv hx).sub (((hasDerivAt_id x).pow 2).inv (pow_ne_zero _ hx))
  have hh := h.deriv
  change deriv (fun y : ℝ ↦ y⁻¹ - (y ^ 2)⁻¹) x = _ at hh
  rw [hh]
  simp only [id_eq, Pi.pow_apply]
  field_simp [hx]
  ring

private theorem escape_deriv {x : ℝ} (hx : 2 < |x|) :
    deriv primalDualEscapeObjective x = x⁻¹ - (x ^ 2)⁻¹ := by
  rw [(escape_eq_tail hx).deriv_eq, escapeTail_deriv]
  exact abs_pos.mp (zero_lt_two.trans hx)

private theorem escape_deriv_deriv {x : ℝ} (hx : 2 < |x|) :
    deriv (deriv primalDualEscapeObjective) x = -(x ^ 2)⁻¹ + 2 * (x ^ 3)⁻¹ := by
  have he : deriv primalDualEscapeObjective =ᶠ[𝓝 x] deriv escapeTail := by
    filter_upwards [continuous_abs.continuousAt.eventually (lt_mem_nhds hx)] with y hy
    exact (escape_eq_tail hy).deriv_eq
  rw [he.deriv_eq]
  exact escapeTail_deriv_deriv (abs_pos.mp (zero_lt_two.trans hx))

private theorem escape_hessian_bounded :
    ∃ B : ℝ, ∀ x, |deriv (deriv primalDualEscapeObjective) x| ≤ B := by
  have hcont : Continuous (deriv (deriv primalDualEscapeObjective)) :=
    ((escape_contDiff.deriv' (n := 1)).deriv' (n := 0)).continuous
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℝ) 2).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B 3, fun x ↦ ?_⟩
  by_cases hx : |x| ≤ 2
  · exact (by simpa [Real.norm_eq_abs] using hB x (show x ∈ closedBall (0 : ℝ) 2 by
        simpa [Real.dist_eq] using hx) : _ ≤ B).trans (le_max_left _ _)
  · have hp : 2 < |x| := lt_of_not_ge hx
    rw [escape_deriv_deriv hp]
    have habs : |-(x ^ 2)⁻¹ + 2 * (x ^ 3)⁻¹| ≤ |-(x ^ 2)⁻¹| + |2 * (x ^ 3)⁻¹| := by
      simpa only [Real.norm_eq_abs] using norm_add_le (-(x ^ 2)⁻¹) (2 * (x ^ 3)⁻¹)
    have hsum : |-(x ^ 2)⁻¹| + |2 * (x ^ 3)⁻¹| ≤ 3 := by
      simp only [abs_neg, abs_inv, abs_pow, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      have h1 : (|x| ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
      have h2 : (|x| ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
      linarith
    exact habs.trans (hsum.trans (le_max_right B 3))

private theorem escape_barrier_bounded :
    BddBelow ((fun x : ℝ ↦ primalDualEscapeObjective x - Real.log x) '' Ioi 0) := by
  let φ := fun x : ℝ ↦ primalDualEscapeObjective x - Real.log x
  have hc : ContinuousOn φ (Icc (1 / 2 : ℝ) 3) :=
    escape_contDiff.continuous.continuousOn.sub (fun x hx ↦
      (Real.continuousAt_log (show x ≠ 0 from ne_of_gt (by linarith [hx.1]))).continuousWithinAt)
  obtain ⟨B, hB⟩ := isCompact_Icc.bddBelow_image hc
  refine ⟨min B 0, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx0 : 0 < x := hx
  by_cases h1 : x < 1 / 2
  · have he := (escape_eq_zero (x := x) (by rw [abs_of_pos hx0]; linarith)).eq_of_nhds
    change min B 0 ≤ primalDualEscapeObjective x - Real.log x
    rw [he]
    exact (min_le_right _ _).trans (by linarith [Real.log_nonpos hx0.le (by linarith : x ≤ 1)])
  by_cases h3 : x ≤ 3
  · exact (min_le_left _ _).trans (hB ⟨x, ⟨le_of_not_gt h1, h3⟩, rfl⟩)
  · have he := (escape_eq_tail (x := x) (by rw [abs_of_pos hx0]; linarith)).eq_of_nhds
    change min B 0 ≤ primalDualEscapeObjective x - Real.log x
    rw [he, escapeTail, add_sub_cancel_left]
    exact (min_le_right _ _).trans (inv_nonneg.mpr hx0.le)

private theorem escape_barrier_uniform_lower_bound :
    ∃ B : ℝ, ∀ μ ∈ Ioc (0 : ℝ) 1, ∀ x > 0,
      B ≤ primalDualEscapeObjective x - μ * Real.log x := by
  obtain ⟨B, hB⟩ := escape_barrier_bounded
  obtain ⟨A, hA⟩ := (isCompact_Icc (α := ℝ) (a := 0) (b := 1)).bddBelow_image
    escape_contDiff.continuous.continuousOn
  refine ⟨min A B, fun μ hμ x hx ↦ ?_⟩
  by_cases hx1 : 1 ≤ x
  · have hh := hB ⟨x, hx, rfl⟩
    change B ≤ primalDualEscapeObjective x - Real.log x at hh
    exact (min_le_right _ _).trans (hh.trans (by
      have hm := mul_le_of_le_one_left (Real.log_nonneg hx1) hμ.2
      linarith))
  · have hh := hA ⟨x, ⟨hx.le, le_of_not_ge hx1⟩, rfl⟩
    exact (min_le_left _ _).trans (hh.trans (by
      have hm := mul_nonpos_of_nonneg_of_nonpos hμ.1.le (Real.log_nonpos hx.le (le_of_not_ge hx1))
      linarith))

/-- A one-dimensional all-successful run of Algorithm 13.6.1 of [conn2000trust] with barrier
parameter $\mu = 1$, fixed unit radius, unit steps and fraction $\frac12$. For an objective $f$
and sequences $x_j$ and $z_j$, write $g_j = f'(x_j) - 1/x_j$ and $h_j = f''(x_j) + z_j / x_j$.
The structure asserts that for all $j$: $x_j > 0$, $z_j > 0$, $x_{j+1} = x_j + 1$,
$x_{j+1} \ge \frac12 x_j$, $h_j \ge 0$,
$$\tfrac18 |g_j| \min\left\{\frac{|g_j|}{1 + |h_j|}, 1\right\} \le -g_j - \frac{h_j}{2},$$
and $0 < -g_j - h_j / 2 \le (f(x_j) - \log x_j) - (f(x_{j+1}) - \log x_{j+1})$.

The objective model is the exact quadratic Taylor model of $f$ at each iterate, and the model
curvature $h_j$ includes the corrected positive dual term $z_j / x_j$. The predicted decrease of
the unit step is $-g_j - h_j / 2$. -/
structure ScalarPrimalDualEscapeRun (f : ℝ → ℝ) (x z : ℕ → ℝ) : Prop where
  /-- The primal iterates are positive. -/
  primal_pos : ∀ j, 0 < x j
  /-- The dual iterates are positive. -/
  dual_pos : ∀ j, 0 < z j
  /-- Every step is the unit step $x_{j+1} = x_j + 1$. -/
  update : ∀ j, x (j + 1) = x j + 1
  /-- Every trial passes the fraction-to-boundary test with fraction $\frac12$. -/
  fractional_clearance : ∀ j, (1 / 2 : ℝ) * x j ≤ x (j + 1)
  /-- The model curvature $f''(x_j) + z_j / x_j$ is nonnegative. -/
  positive_curvature : ∀ j, 0 ≤ deriv (deriv f) (x j) + z j / x j
  /-- The predicted decrease of the unit step satisfies the decrease test with constant $\frac18$
  and unit radius. -/
  decrease : ∀ j,
    let g := deriv f (x j) - (x j)⁻¹
    let h := deriv (deriv f) (x j) + z j / x j
    (1 / 8 : ℝ) * (|g| * min (|g| / (1 + |h|)) 1) ≤ -g - h / 2
  /-- The predicted decrease is positive and at most the actual decrease of the barrier objective,
  so the ratio is at least $1$. -/
  very_successful : ∀ j,
    let g := deriv f (x j) - (x j)⁻¹
    let h := deriv (deriv f) (x j) + z j / x j
    0 < -g - h / 2 ∧ -g - h / 2 ≤
      (f (x j) - Real.log (x j)) - (f (x (j + 1)) - Real.log (x (j + 1)))

/-- A counterexample to the printed finite stopping in Theorem 13.6.2 of [conn2000trust]. Let $f$ be
the objective `ConnGouldToint.Chapter13.primalDualEscapeObjective`. Then $f$ is twice
continuously differentiable with bounded $f''$, the barrier objectives $f(x) - \mu \log x$ are
bounded below on $(0, \infty)$ uniformly in $\mu \in (0, 1]$, and there are sequences $x_j$ and
$z_j$ forming a one-dimensional all-successful run
(`ConnGouldToint.Chapter13.ScalarPrimalDualEscapeRun`) such that:
* $x_j \to \infty$;
* $z_j \le 2 \max\{x_j^{-1}, 1\}$ (AA.7);
* $f'(x_j) - 1/x_j \to 0$ and $z_j - 1/x_j \to 0$ (AA.8);
* $|x_j z_j - 1| > \frac12$ for all $j$.

The exact Taylor objective models satisfy the center matching and curvature conditions, and
every ratio is at least $1$. The unit complementarity error prevents finite stopping with
tolerance $\frac12$.

**Correction.** The finite stopping transfer requires an upper bound on primal coordinates to turn
small additive multiplier error into small product error. The extension version also supplies the
clearance and model hypotheses for primal inner convergence. A scalar unbounded run with AA.8 and
frequent success can fail the complementarity test indefinitely.
-/
theorem theorem_13_6_2_unbounded_run_counterexample :
    ∃ x z : ℕ → ℝ,
      ContDiff ℝ 2 primalDualEscapeObjective ∧
      (∃ B : ℝ, ∀ x, |deriv (deriv primalDualEscapeObjective) x| ≤ B) ∧
      (∃ B : ℝ, ∀ μ ∈ Ioc (0 : ℝ) 1, ∀ x > 0,
        B ≤ primalDualEscapeObjective x - μ * Real.log x) ∧
      ScalarPrimalDualEscapeRun primalDualEscapeObjective x z ∧
      Tendsto x atTop atTop ∧
      (∀ j, z j ≤ 2 * max (x j)⁻¹ 1) ∧
      Tendsto (fun j ↦ deriv primalDualEscapeObjective (x j) - (x j)⁻¹) atTop (𝓝 0) ∧
      Tendsto (fun j ↦ z j - (x j)⁻¹) atTop (𝓝 0) ∧
      (∀ j, ¬ |x j * z j - 1| ≤ (1 / 2 : ℝ)) := by
  let x (j : ℕ) := (j : ℝ) + 3
  let z (j : ℕ) := 2 / x j
  have hx (j : ℕ) : 3 ≤ x j := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) j]
  have hxp (j : ℕ) : 0 < x j := by linarith [hx j]
  have hx2 (j : ℕ) : 2 < |x j| := by rw [abs_of_pos (hxp j)]; linarith [hx j]
  have hxadd (j : ℕ) : x (j + 1) = x j + 1 := by simp [x, Nat.cast_add]; ring
  have hz (j : ℕ) : 0 < z j := div_pos zero_lt_two (hxp j)
  have hg (j : ℕ) : deriv primalDualEscapeObjective (x j) - (x j)⁻¹ = -((x j) ^ 2)⁻¹ := by
    rw [escape_deriv (hx2 j)]
    ring
  have hh (j : ℕ) : deriv (deriv primalDualEscapeObjective) (x j) + z j / x j =
      ((x j) ^ 2)⁻¹ + 2 * ((x j) ^ 3)⁻¹ := by
    rw [escape_deriv_deriv (hx2 j)]
    unfold z
    field_simp [(hxp j).ne']
    ring
  have hphi (j : ℕ) : primalDualEscapeObjective (x j) - Real.log (x j) = (x j)⁻¹ := by
    rw [(escape_eq_tail (hx2 j)).eq_of_nhds, escapeTail, add_sub_cancel_left]
  refine ⟨x, z, escape_contDiff, escape_hessian_bounded, escape_barrier_uniform_lower_bound,
    ⟨hxp, hz, hxadd, ?_, ?_, ?_, ?_⟩,
    tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hxadd]
    linarith [hx j]
  · intro j
    rw [hh]
    positivity
  · intro j
    dsimp only
    rw [hg, hh, abs_neg, abs_of_nonneg (by positivity : 0 ≤ ((x j) ^ 2)⁻¹)]
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (min_le_right _ _)
      (by positivity)) (by norm_num)).trans
    have hp := hxp j
    field_simp [hp.ne']
    nlinarith [hx j]
  · intro j
    dsimp only
    rw [hg, hh, hphi j, hphi (j + 1), hxadd]
    have hp := hxp j
    have hpa : 0 < x j + 1 := by positivity
    constructor
    · field_simp [hp.ne']
      nlinarith [hx j]
    · field_simp [hp.ne', hpa.ne']
      nlinarith [hx j, sq_nonneg (x j)]
  · intro j
    unfold z
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) zero_lt_two.le
  · have ht : Tendsto (fun j ↦ (x j)⁻¹) atTop (𝓝 0) := by
      have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 2)
      simpa [x, Function.comp_def, Nat.cast_add, add_assoc, one_div,
        show (2 : ℝ) + 1 = 3 by norm_num] using ht
    simpa only [hg, ← inv_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), neg_zero] using (ht.pow 2).neg
  · have ht : Tendsto (fun j ↦ (x j)⁻¹) atTop (𝓝 0) := by
      have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 2)
      simpa [x, Function.comp_def, Nat.cast_add, add_assoc, one_div,
        show (2 : ℝ) + 1 = 3 by norm_num] using ht
    have he (j : ℕ) : z j - (x j)⁻¹ = (x j)⁻¹ := by unfold z; rw [div_eq_mul_inv]; ring
    simpa only [he] using ht
  · intro j
    unfold z
    rw [mul_div_cancel₀ _ (hxp j).ne']
    norm_num

end EscapeExample

/-! ### A run with all trials rejected in Theorem 13.6.4 -/

section RejectionExample

open Metric Chapter06

private noncomputable def stalledBump : ContDiffBump (1 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

private noncomputable def stalledLocal (x : ℝ) : ℝ := Real.log x + (x - 1) ^ 2 / 4

/-- A smooth objective on $\mathbb{R}$ whose barrier objective $f(x) - \log x$ equals
$(x - 1)^2 / 4$ near $1$. It is $\psi(x)(\log x + (x - 1)^2 / 4) + (1 - \psi(x)) x^2$, where
$\psi$ is a smooth bump function equal to $1$ on $[3/4, 5/4]$ and to $0$ outside $(1/2, 3/2)$.

Outside $(1/2, 3/2)$ it is the positive quadratic $x^2$. -/
noncomputable def primalDualStalledObjective (x : ℝ) : ℝ :=
  stalledBump x * stalledLocal x + (1 - stalledBump x) * x ^ 2

private theorem stalled_eq_local {x : ℝ} (hx : x ∈ ball (1 : ℝ) (1 / 4)) :
    primalDualStalledObjective =ᶠ[𝓝 x] stalledLocal := by
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  simp [primalDualStalledObjective, stalledBump.one_of_mem_closedBall (ball_subset_closedBall hy)]

private theorem stalled_eq_outer {x : ℝ} (hx : x ∉ closedBall (1 : ℝ) (1 / 2)) :
    primalDualStalledObjective =ᶠ[𝓝 x] (fun y : ℝ ↦ y ^ 2) := by
  filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hx] with y hy
  have hb : stalledBump y = 0 :=
    stalledBump.zero_of_le_dist (le_of_not_ge (show y ∉ closedBall (1 : ℝ) (1 / 2) from hy))
  simp [primalDualStalledObjective, hb]

private theorem stalled_contDiff : ContDiff ℝ 2 primalDualStalledObjective := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have h := (contDiffAt_id (𝕜 := ℝ) (n := 2) (x := (0 : ℝ))).pow 2
    exact h.congr_of_eventuallyEq (stalled_eq_outer (by norm_num [mem_closedBall, Real.dist_eq]))
  have hlocal : ContDiffAt ℝ 2 stalledLocal x := by
    unfold stalledLocal
    exact (contDiffAt_id.log hx).add (((contDiffAt_id.sub contDiffAt_const).pow 2).div_const 4)
  have hb : ContDiffAt ℝ 2 stalledBump x := stalledBump.contDiff.contDiffAt
  exact (hb.mul hlocal).add ((contDiffAt_const.sub hb).mul (contDiffAt_id.pow 2))

private theorem stalledLocal_deriv {x : ℝ} (hx : x ≠ 0) :
    deriv stalledLocal x = x⁻¹ + (x - 1) / 2 := by
  have h := (Real.hasDerivAt_log hx).add ((((hasDerivAt_id x).sub_const 1).pow 2).div_const 4)
  have he := h.deriv
  change deriv stalledLocal x = _ at he
  rw [he]
  simp only [id_eq, Nat.cast_ofNat, show (2 - 1 : ℕ) = 1 by decide, pow_one, mul_one]
  ring

private theorem stalled_center_derivatives :
    deriv primalDualStalledObjective 1 = 1 ∧
    deriv (deriv primalDualStalledObjective) 1 = -(1 / 2 : ℝ) := by
  have h1 : (1 : ℝ) ∈ ball 1 (1 / 4) := mem_ball_self (by norm_num)
  constructor
  · rw [(stalled_eq_local h1).deriv_eq, stalledLocal_deriv (by norm_num)]
    norm_num
  have he : deriv primalDualStalledObjective =ᶠ[𝓝 (1 : ℝ)] fun x ↦ x⁻¹ + (x - 1) / 2 := by
    filter_upwards [isOpen_ball.mem_nhds h1, isOpen_ne.mem_nhds (one_ne_zero : (1 : ℝ) ≠ 0)]
      with y hy hy0
    rw [(stalled_eq_local hy).deriv_eq, stalledLocal_deriv hy0]
  rw [he.deriv_eq]
  have hd := ((hasDerivAt_id (1 : ℝ)).inv (by norm_num : (1 : ℝ) ≠ 0)).add
    (((hasDerivAt_id (1 : ℝ)).sub_const 1).div_const 2)
  have hh := hd.deriv
  change deriv (fun x : ℝ ↦ x⁻¹ + (x - 1) / 2) 1 = _ at hh
  rw [hh]
  norm_num

private theorem stalled_hessian_bounded :
    ∃ B : ℝ, ∀ x, |deriv (deriv primalDualStalledObjective) x| ≤ B := by
  have hc : Continuous (deriv (deriv primalDualStalledObjective)) :=
    ((stalled_contDiff.deriv' (n := 1)).deriv' (n := 0)).continuous
  obtain ⟨B, hB⟩ :=
    (isCompact_closedBall (1 : ℝ) (1 / 2)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B 2, fun x ↦ ?_⟩
  by_cases hx : x ∈ closedBall (1 : ℝ) (1 / 2)
  · exact (by simpa only [Real.norm_eq_abs] using hB x hx : _ ≤ B).trans (le_max_left _ _)
  · have he : deriv primalDualStalledObjective =ᶠ[𝓝 x] deriv (fun y : ℝ ↦ y ^ 2) := by
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hx] with y hy
      exact (stalled_eq_outer hy).deriv_eq
    rw [he.deriv_eq]
    have hd (y : ℝ) : deriv (fun y : ℝ ↦ y ^ 2) y = 2 * y := by simp
    have h := (hasDerivAt_id x |>.const_mul (2 : ℝ)).deriv
    change deriv (fun y : ℝ ↦ 2 * y) x = _ at h
    rw [funext hd, h]
    simp

private theorem stalled_barrier_bounded (μ : ℝ) (hμ : 0 < μ) :
    BddBelow ((fun x : ℝ ↦ primalDualStalledObjective x - μ * Real.log x) '' Ioi 0) := by
  obtain ⟨A, hA⟩ := (isCompact_closedBall (1 : ℝ) (1 / 2)).bddBelow_image
    stalled_contDiff.continuous.continuousOn
  refine ⟨min (A - 2 * μ) (-(μ ^ 2 / 4)), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hp : 0 < x := hx
  have hl := Real.log_le_self hp.le
  by_cases hb : x ∈ closedBall (1 : ℝ) (1 / 2)
  · have hxb : x ≤ 2 := by
      have h := abs_le.mp
        (show |x - 1| ≤ (1 / 2 : ℝ) by simpa [mem_closedBall, Real.dist_eq] using hb)
      linarith [h.2]
    have ha : A ≤ primalDualStalledObjective x := hA ⟨x, hb, rfl⟩
    exact (min_le_left _ _).trans (by linarith [mul_le_mul_of_nonneg_left (hl.trans hxb) hμ.le])
  · change min (A - 2 * μ) (-(μ ^ 2 / 4)) ≤ primalDualStalledObjective x - μ * Real.log x
    rw [(stalled_eq_outer hb).eq_of_nhds]
    exact (min_le_right _ _).trans (by
      nlinarith [mul_le_mul_of_nonneg_left hl hμ.le, sq_nonneg (x - μ / 2)])

/-- A one-dimensional rejected trial of Algorithm 13.6.1 of [conn2000trust] with barrier parameter
$1$, fraction $\frac12$ and the exact Taylor objective model. For parameters $P$, an objective
$f$, a primal point $x$, a dual point $z$, a step $s$, a radius $\Delta$, and the next values
$x'$, $z'$ and $\Delta'$, write $g = f'(x) - 1/x$, $h = f''(x) + z/x$, $\tau = \min\{0, h\}$,
$\hat\Delta = \min\{\Delta, x/2\}$ and $p = -(g s + h s^2 / 2)$. The structure asserts that
$x > 0$, $z > 0$, $x + s > 0$, $|s| \le \Delta$, $x + s \ge \frac12 x$,
$$\tfrac14 \max\left\{|g| \min\left\{\frac{|g|}{1 + |h|}, \hat\Delta\right\}, -\tau
  \min\{\tau^2, \hat\Delta^2\}\right\} \le p, \qquad p > 0,$$
that the ratio $((f(x) - \log x) - (f(x + s) - \log(x + s))) / p$ is less than $\eta_1$, that
$x' = x$ and $z' = z$, and that $\gamma_1 \Delta \le \Delta' \le \gamma_2 \Delta$.

The safeguarded dual branch (13.6.19) keeps the old multiplier after the rejection. -/
structure ScalarPrimalDualRejectedTrial (P : BTRParams) (f : ℝ → ℝ)
    (x z s Δ x' z' Δ' : ℝ) : Prop where
  /-- The primal point is positive. -/
  primal_pos : 0 < x
  /-- The dual point is positive. -/
  dual_pos : 0 < z
  /-- The trial point is positive. -/
  trial_pos : 0 < x + s
  /-- The step lies in the trust region. -/
  step_bound : |s| ≤ Δ
  /-- The trial passes the fraction-to-boundary test with fraction $\frac12$. -/
  fractional_clearance : (1 / 2 : ℝ) * x ≤ x + s
  /-- The predicted decrease satisfies the decrease test (13.3.2) with constant $\frac14$. -/
  model_decrease :
    let g := deriv f x - x⁻¹
    let h := deriv (deriv f) x + z / x
    let τ := min 0 h
    (1 / 4 : ℝ) * max (|g| * min (|g| / (1 + |h|)) (min Δ ((1 / 2 : ℝ) * x)))
      (-τ * min (τ ^ 2) ((min Δ ((1 / 2 : ℝ) * x)) ^ 2)) ≤ -(g * s + h * s ^ 2 / 2)
  /-- The predicted decrease is positive. -/
  predicted_pos :
    let g := deriv f x - x⁻¹
    let h := deriv (deriv f) x + z / x
    0 < -(g * s + h * s ^ 2 / 2)
  /-- The ratio is below $\eta_1$, so the trial is rejected. -/
  ratio_reject :
    let g := deriv f x - x⁻¹
    let h := deriv (deriv f) x + z / x
    ((f x - Real.log x) - (f (x + s) - Real.log (x + s))) /
      (-(g * s + h * s ^ 2 / 2)) < P.η₁
  /-- The primal and dual points are kept. -/
  retain : x' = x ∧ z' = z
  /-- The radius shrinks as for an unsuccessful iteration of (6.1.5). -/
  radius_update : P.γ₁ * Δ ≤ Δ' ∧ Δ' ≤ P.γ₂ * Δ

/-- A counterexample to AA.8 in the printed Theorem 13.6.4 of [conn2000trust]. Let $f$ be the
objective `ConnGouldToint.Chapter13.primalDualStalledObjective`. Then $f$ is twice continuously
differentiable with bounded $f''$, and for every $\mu > 0$ the barrier objective
$f(x) - \mu \log x$ is bounded below on $(0, \infty)$. There are radii $\Delta_j > 0$ with
$\Delta_j \to 0$ such that, for every $j$, the step $s = \Delta_j$ from $x = 1$ with dual
$z = \frac14$ is a rejected trial (`ConnGouldToint.Chapter13.ScalarPrimalDualRejectedTrial`) for
the parameters (6.1.6), which keeps $x = 1$ and $z = \frac14$ and gives the next radius
$\Delta_{j+1}$. Moreover $f'(1) - 1 = 0$, while $z - \mu / x = \frac14 - 1$ does not tend to
$0$.

All trials of this bounded run are rejected, the model gradients are zero and the steps tend to
zero. The safeguard keeps the dual coordinate at $\frac14$, so the AA.8 conclusion of Theorem
13.6.4 fails.

**Correction.** Positivity and a uniform bound use a positive primal lower bound. For the printed
update the AA.8 limit also needs infinitely many successes when displacements vanish. A reset to the
exact dual after a rejected trial yields consistency under vanishing accepted displacements, and the
all-rejected example shows failure without either condition.
-/
theorem theorem_13_6_4_all_rejected_counterexample :
    ∃ Δ : ℕ → ℝ,
      ContDiff ℝ 2 primalDualStalledObjective ∧
      (∃ B : ℝ, ∀ x, |deriv (deriv primalDualStalledObjective) x| ≤ B) ∧
      (∀ μ > 0, BddBelow ((fun x ↦ primalDualStalledObjective x - μ * Real.log x) '' Ioi 0)) ∧
      (∀ j, 0 < Δ j ∧
        ScalarPrimalDualRejectedTrial defaultBTRParams primalDualStalledObjective
          1 (1 / 4) (Δ j) (Δ j) 1 (1 / 4) (Δ (j + 1))) ∧
      deriv primalDualStalledObjective 1 - (1 : ℝ)⁻¹ = 0 ∧ Tendsto Δ atTop (𝓝 0) ∧
      ¬ Tendsto (fun _ : ℕ ↦ (1 / 4 : ℝ) - 1 / 1) atTop (𝓝 0) := by
  let Δ (j : ℕ) := (1 / 2 : ℝ) ^ j * (1 / 8)
  have hΔ (j : ℕ) : 0 < Δ j := by dsimp [Δ]; positivity
  have hbound (j : ℕ) : Δ j ≤ 1 / 8 := by
    dsimp only [Δ]
    exact mul_le_of_le_one_left (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))
  have hφ (s : ℝ) (hs : |s| < 1 / 4) :
      primalDualStalledObjective (1 + s) - Real.log (1 + s) = s ^ 2 / 4 := by
    have hh : 1 + s ∈ ball (1 : ℝ) (1 / 4) := by
      simpa [mem_ball, Real.dist_eq, add_comm] using hs
    rw [(stalled_eq_local hh).eq_of_nhds, stalledLocal]
    ring
  have hg : deriv primalDualStalledObjective 1 - (1 : ℝ)⁻¹ = 0 := by
    rw [stalled_center_derivatives.1]
    norm_num
  have hh : deriv (deriv primalDualStalledObjective) 1 + (1 / 4 : ℝ) / 1 = -(1 / 4 : ℝ) := by
    rw [stalled_center_derivatives.2]
    norm_num
  refine ⟨Δ, stalled_contDiff, stalled_hessian_bounded, stalled_barrier_bounded, ?_, hg, ?_, ?_⟩
  · intro j
    have hp := hΔ j
    have hb := hbound j
    refine ⟨hp, ⟨by norm_num, by norm_num, by linarith, ?_, by linarith, ?_, ?_, ?_,
      ⟨rfl, rfl⟩, ?_⟩⟩
    · rw [abs_of_pos hp]
    · dsimp only
      rw [hg, hh]
      norm_num
      have hmin : min (Δ j) (1 / 2) = Δ j := min_eq_left (by linarith)
      have hs : (Δ j) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
        (sq_le_sq₀ hp.le (by norm_num)).mpr (by linarith)
      rw [hmin]
      simp only [min_eq_right (show (Δ j) ^ 2 ≤ (1 / 16 : ℝ) by nlinarith)] at *
      simp only [max_eq_right (by positivity : (0 : ℝ) ≤ (1 / 4) * (Δ j) ^ 2)]
      nlinarith [sq_nonneg (Δ j)]
    · dsimp only
      rw [hg, hh]
      nlinarith [sq_pos_of_pos hp]
    · dsimp only
      rw [hg, hh, hφ (Δ j) (by rw [abs_of_pos hp]; linarith)]
      have hzero := hφ 0 (by norm_num)
      simp only [add_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div] at hzero
      rw [hzero]
      have hη : 0 < defaultBTRParams.η₁ := defaultBTRParams.eta₁_pos
      apply lt_of_le_of_lt (div_nonpos_of_nonpos_of_nonneg ?_ ?_) hη
      · nlinarith [sq_nonneg (Δ j)]
      · nlinarith [sq_nonneg (Δ j)]
    · have he : Δ (j + 1) = (1 / 2 : ℝ) * Δ j := by
        simp only [Δ, pow_succ]
        ring
      rw [he]
      exact ⟨le_rfl, le_rfl⟩
  · simpa only [Δ, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 8 : ℝ)
  · intro h
    have he := tendsto_nhds_unique
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ (1 / 4 : ℝ) - 1 / 1) atTop (𝓝 ((1 / 4 : ℝ) - 1 / 1))) h
    norm_num at he

end RejectionExample

end ConnGouldToint.Chapter13
