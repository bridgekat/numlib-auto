/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Nonlinear.ScalarNewton
import Numlib.Optimization.Subproblem.Bracketing
import Numlib.Optimization.Subproblem.SecularIteration
import Numlib.Optimization.Subproblem.Multiplier

/-!
# Conn, Gould and Toint, Section 7.3: The Moré–Sorensen secular equation

This module formalizes the Moré–Sorensen method for the Euclidean trust-region subproblem in Section
7.3 of [conn2000trust]. Let $E$ be a finite-dimensional real inner product space, $g \in E$, and $H$
a symmetric operator on $E$ with least eigenvalue $\lambda_1$ and greatest eigenvalue $\lambda_n$.
For $\lambda > -\lambda_1$ the shifted step $s(\lambda) = -(H + \lambda I)^{-1} g$ (7.3.1) is
defined, and a boundary solution of the subproblem has a multiplier $\lambda$ with
$\|s(\lambda)\| = \Delta$. The method solves the secular equation
$$\phi(\lambda) = \frac{1}{\|s(\lambda)\|} - \frac{1}{\Delta} = 0 \qquad (7.3.6)$$
by Newton's method. For $g \neq 0$, $\phi$ is increasing and concave on $(-\lambda_1, \infty)$
(Lemma 7.3.1), so Newton iterates from a point with $\phi < 0$ increase monotonically and converge
quadratically to the root (Lemma 7.3.2), and a Newton step from a point with $\phi > 0$ does not
overshoot the optimal multiplier (Lemma 7.3.3). Algorithm 7.3.4 safeguards the Newton iteration with
a bracket $[\lambda^L, \lambda^U]$ and a factorization test, and stops when the step is acceptable
(7.3.19) in the sense of Lemmas 7.3.5 and 7.3.6. The proofs specialize
`Numlib.Optimization.Subproblem.SecularIteration`, `Numlib.Optimization.Subproblem.Bracketing` and
`Numlib.Optimization.Subproblem.Multiplier`.

Theorem 7.3.4 states the convergence of Algorithm 7.3.4. Its phases are formalized separately:
interior stopping, the zero-gradient case, the easy case, where the safeguarded iteration enters the
Newton interval and then converges quadratically, and the hard case, where the multipliers converge
to the pole $-\lambda_1$ and boundary corrections along directions of vanishing shifted curvature
give minimizing model values. `ConnGouldToint.Chapter07.theorem_7_3_4_nonzero_gradient` combines the
multiplier alternatives for a nonzero gradient.

## Main definitions

* Equation (7.3.1), `ConnGouldToint.Chapter07.shiftedStep`: the step
  $s(\lambda) = -(H + \lambda I)^{-1} g$.
* Equation (7.3.6), `ConnGouldToint.Chapter07.phi`: the secular function $\phi(\lambda) = 1 /
  \|s(\lambda)\| - 1 / \Delta$.
* Equation (7.3.11), `ConnGouldToint.Chapter07.moreSorensenNewtonStep`: the Newton step
  $\lambda - \phi(\lambda) / \phi'(\lambda)$.
* Equation (7.3.14), `ConnGouldToint.Chapter07.moreSorensenTrial`: the safeguarded trial multiplier
  $\max\{\sqrt{\lambda^L \lambda^U}, \lambda^L + \theta (\lambda^U - \lambda^L)\}$.
* Equation (7.3.19), `ConnGouldToint.Chapter07.IsAcceptableModelStep`: an acceptable approximation
  to the model minimizer.
* Algorithm 7.3.4, `ConnGouldToint.Chapter07.moreSorensenSafeguardedStepBy`,
  `ConnGouldToint.Chapter07.moreSorensenSafeguardedStep` and
  `ConnGouldToint.Chapter07.moreSorensenSafeguardedIterates`: the safeguarded multiplier update and
  its orbit.
* Algorithm 7.3.4, Step 3b(iii), `ConnGouldToint.Chapter07.moreSorensenBoundaryCoefficient`: a fixed
  root of the boundary equation for a unit correction direction.

## Main results

* Equation (7.3.6), `ConnGouldToint.Chapter07.phi_eq_inv_norm_sub_inv`: $\phi(\lambda) = 1 /
  \|s(\lambda)\| - 1 / \Delta$.
* Lemma 7.3.1, `ConnGouldToint.Chapter07.lemma_7_3_1`: $\phi$ is strictly increasing and concave on
  $(-\lambda_1, \infty)$, with the derivatives (7.3.7)–(7.3.9).
* Algorithm 7.3.1, `ConnGouldToint.Chapter07.algorithm_7_3_1_step`: the Newton step from a Cholesky
  factor and one triangular solve.
* Lemma 7.3.2, `ConnGouldToint.Chapter07.lemma_7_3_2`: Newton iterates from a point with $\phi < 0$
  increase to the root, with linear and quadratic error bounds.
* Lemma 7.3.2, `ConnGouldToint.Chapter07.existsUnique_secular_root_of_phi_neg` and
  `ConnGouldToint.Chapter07.moreSorensenNewtonStep_eq_root_of_eigenvector`: existence of the root,
  and exact arrival when $g$ is an eigenvector.
* Lemma 7.3.3, `ConnGouldToint.Chapter07.lemma_7_3_3`: a Newton step from a point with $\phi > 0$
  does not exceed the optimal multiplier.
* Theorem 7.3.4, `ConnGouldToint.Chapter07.theorem_7_3_4_nonzero_gradient`: for a nonzero gradient,
  the method either stops at an unshifted solve, converges quadratically to the multiplier in the
  easy case, or converges to the pole in the hard case.
* Theorem 7.3.4, phase results: `ConnGouldToint.Chapter07.moreSorensen_bracketing_enters_newton`,
  `ConnGouldToint.Chapter07.moreSorensen_bracketing_tendsto`,
  `ConnGouldToint.Chapter07.moreSorensen_easy_newton_convergence`,
  `ConnGouldToint.Chapter07.moreSorensen_easy_bracket_then_newton`,
  `ConnGouldToint.Chapter07.moreSorensen_easy_safeguarded_run`,
  `ConnGouldToint.Chapter07.moreSorensen_interior_solution`,
  `ConnGouldToint.Chapter07.moreSorensen_zero_gradient_solution`,
  `ConnGouldToint.Chapter07.moreSorensen_zero_gradient_run`,
  `ConnGouldToint.Chapter07.moreSorensen_hard_model_convergence`,
  `ConnGouldToint.Chapter07.moreSorensen_hard_bracketing_subsequence`,
  `ConnGouldToint.Chapter07.moreSorensen_hard_safeguarded_run`,
  `ConnGouldToint.Chapter07.moreSorensen_hard_safeguarded_corrections` and
  `ConnGouldToint.Chapter07.moreSorensen_hard_bracket_then_exact_correction` treat interior
  stopping, the zero-gradient case, the easy case and the hard case separately.
* Algorithm 7.3.4, `ConnGouldToint.Chapter07.moreSorensenSafeguardedStep_of_positive_phi`,
  `ConnGouldToint.Chapter07.moreSorensenSafeguardedStep_zero_gradient`,
  `ConnGouldToint.Chapter07.moreSorensen_nonzero_bracket_run` and
  `ConnGouldToint.Chapter07.moreSorensen_interior_solution_of_unshifted_solve`: single updates from
  a positive secular value or a zero gradient, the safeguarded run before the Newton interval, and
  interior stopping for a positive semidefinite Hessian.
* Equation (7.3.16), `ConnGouldToint.Chapter07.moreSorensen_exact_leftmost_curvature_tendsto` and
  `ConnGouldToint.Chapter07.moreSorensen_hard_correction_curvature_tendsto`: vanishing shifted
  curvature of the hard-case corrections.
* Equation (7.3.18), `ConnGouldToint.Chapter07.multiplier_bounds_of_boundary`: $\|g\| / \Delta -
  \lambda_n \le \lambda \le \|g\| / \Delta - \lambda_1$ for a boundary solution.
* Lemma 7.3.5, `ConnGouldToint.Chapter07.lemma_7_3_5`: a shifted step with norm near $\Delta$ has
  model value at most $(1 - \kappa)^2$ times the minimum.
* Lemma 7.3.6, `ConnGouldToint.Chapter07.lemma_7_3_6`: a boundary correction with small shifted
  curvature has model value at most $(1 - \kappa)$ times the minimum.
* Algorithm 7.3.5, `ConnGouldToint.Chapter07.acceptable_of_easy_stopping_rule` and
  `ConnGouldToint.Chapter07.acceptable_of_hard_stopping_rule`: the two stopping rules give
  acceptable steps.
* Algorithm 7.3.4, Step 3b(iii), `ConnGouldToint.Chapter07.norm_add_boundaryCorrection` and
  `ConnGouldToint.Chapter07.moreSorensen_boundary_correction_tie`: the fixed root reaches the
  boundary, and the two roots can tie in model value.

## Conventions

* The least eigenvalue $\lambda_1$ is `Subproblem.leftmost hH`, the greatest $\lambda_n$ is
  `Subproblem.rightmost hH`, and $\lambda_s = \max\{0, -\lambda_1\}$ is
  `Subproblem.shiftThreshold hH`. The point $-\lambda_1$ is called the pole.
* The step $s(\lambda)$ is defined with `Ring.inverse`, so it is $0$ when $H + \lambda I$ is
  singular. The model is $q(s) = \langle g, s \rangle + \frac12 \langle s, H s \rangle$,
  `Subproblem.quadModel g H`.
* An optimal multiplier $\lambda_*$ for a global minimizer $s_*$ of $q$ on the ball is
  `Subproblem.IsTrustRegionMultiplier g H Δ s_* λ_*`. The interval $(-\lambda_1, \lambda_*]$ is the
  Newton interval.
* The safeguarded iteration is a bracketing run `Subproblem.IsBracketRun` with pole $-\lambda_1$ and
  target $\lambda_*$.

## Implementation notes

* The update of Algorithm 7.3.4 takes the lower estimate of Steps 3c–d as an input
  $b \le -\lambda_1$, which a successful or partial factorization supplies. Its computation is in
  `NumlibSurface.ConnGouldToint.Chapter07.Section03Cholesky`.
* In the hard case the multipliers converge, but a single vector limit of the corrected steps needs
  additional control of the correction directions or a unique minimizer.

## Deviations from the source

* **Lemma 7.3.2** (correction). The secular values of the Newton iterates are nonpositive, not
  negative, because Newton's method can reach the root exactly. See
  `ConnGouldToint.Chapter07.lemma_7_3_2`.
* **Prose following Lemmas 7.3.5 and 7.3.6** (correction). The acceptance coefficient of the model
  value is an upper bound on the chosen coefficient, so the printed comparisons are reversed. See
  `ConnGouldToint.Chapter07.IsAcceptableModelStep.weaken`.
* **Theorem 7.3.4, hard case** (correction). Vector convergence of the corrected steps is proved for
  a fixed unit leftmost eigenvector and a fixed root of the boundary equation. For general
  correction directions, the model values converge and every limit point is a minimizer. See
  `ConnGouldToint.Chapter07.moreSorensen_hard_bracket_then_exact_correction`.
* **Algorithm 7.3.4, Step 3b(iii)** (reading). The two roots of the boundary equation can give the
  same model value, so the rule needs a tie convention. See
  `ConnGouldToint.Chapter07.moreSorensen_boundary_correction_tie`.
-/

namespace ConnGouldToint.Chapter07

open Subproblem Set Filter Topology
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {g : E} {H : E →L[ℝ] E}
  {hH : (H : E →ₗ[ℝ] E).IsSymmetric}

/-- **Equation (7.3.1)** of [conn2000trust]. For $g \in E$ and $\lambda \in \mathbb{R}$, the
**shifted step** is $s(\lambda) = -(H + \lambda I)^{-1} g$.

It is `Subproblem.step g H λ`, defined with `Ring.inverse`, so it is $0$ when $H + \lambda I$ is
singular. -/
noncomputable abbrev shiftedStep (g : E) (H : E →L[ℝ] E) : ℝ → E := step g H

/-- **Equation (7.3.6)** of [conn2000trust]. The **secular function** of Moré and Sorensen is
$$\phi(\lambda) = \|s(\lambda)\|^{-1} - \Delta^{-1}.$$

It is `Subproblem.trSecular g H Δ (-1/2)`, the transformed secular function
$\pi(\lambda)^\beta - \Delta^{2\beta}$ with $\pi(\lambda) = \|s(\lambda)\|^2$ and
$\beta = -1/2$. -/
noncomputable abbrev phi (g : E) (H : E →L[ℝ] E) (Δ : ℝ) : ℝ → ℝ :=
  trSecular g H Δ (-1 / 2)

private theorem sq_rpow_neg_half (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (x ^ 2) ^ (-(k : ℝ) / 2) = (x ^ k)⁻¹ := by
  rw [← Real.rpow_two, ← Real.rpow_mul hx,
    show (2 : ℝ) * (-(k : ℝ) / 2) = -(k : ℝ) by ring, Real.rpow_neg hx, Real.rpow_natCast]

omit [FiniteDimensional ℝ E] in
/-- **Equation (7.3.6)** of [conn2000trust]. For all $\Delta, \lambda \in \mathbb{R}$,
$$\phi(\lambda) = \frac{1}{\|s(\lambda)\|} - \frac{1}{\Delta},$$
with the convention $1/0 = 0$. -/
theorem phi_eq_inv_norm_sub_inv (g : E) (H : E →L[ℝ] E) (Δ lam : ℝ) :
    phi g H Δ lam = 1 / ‖shiftedStep g H lam‖ - 1 / Δ := by
  have h : secular g H lam ^ (-1 / 2 : ℝ) = ‖step g H lam‖⁻¹ := by
    simpa [secular] using sq_rpow_neg_half ‖step g H lam‖ (norm_nonneg _) 1
  rw [phi, trSecular, h, show (2 : ℝ) * (-1 / 2) = -1 by norm_num, Real.rpow_neg_one]
  simp only [shiftedStep, one_div]

/-- **Lemma 7.3.1** of [conn2000trust]. Let $g \neq 0$ and $\Delta \in \mathbb{R}$. Then $\phi$ is
strictly increasing and concave on $(-\lambda_1, \infty)$. Moreover, for every
$\lambda > -\lambda_1$, with $s = s(\lambda)$ and $d = -(H + \lambda I)^{-1} s$, the step has
derivative $s'(\lambda) = d$, and
$$\phi'(\lambda) = -\frac{\langle s, d \rangle}{\|s\|^3}, \qquad \phi''(\lambda) = \frac{3
  (\langle s, d \rangle^2 - \|s\|^2 \|d\|^2)}{\|s\|^5},$$
which are (7.3.7)–(7.3.9). -/
theorem lemma_7_3_1 (hg : g ≠ 0) (Δ : ℝ) :
    StrictMonoOn (phi g H Δ) (Ioi (-leftmost hH)) ∧
    ConcaveOn ℝ (Ioi (-leftmost hH)) (phi g H Δ) ∧
    ∀ lam : ℝ, -leftmost hH < lam →
      let s := shiftedStep g H lam
      let d := -(Ring.inverse (H + lam • 1)) s
      HasDerivAt (shiftedStep g H) d lam ∧
        deriv (phi g H Δ) lam = -⟪s, d⟫ / ‖s‖ ^ 3 ∧
        iteratedDeriv 2 (phi g H Δ) lam =
          3 * (⟪s, d⟫ ^ 2 - ‖s‖ ^ 2 * ‖d‖ ^ 2) / ‖s‖ ^ 5 := by
  obtain ⟨hcv, hm, -⟩ := trSecular_shape (hH := hH) hg Δ (β := -1 / 2) (by norm_num)
  refine ⟨hm, hcv, fun lam hlam => ?_⟩
  let s := step g H lam
  let d := stepDeriv g H 1 lam
  have hstep (x : ℝ) : stepDeriv g H 0 x = step g H x := stepDeriv_zero x
  have hD : HasDerivAt (shiftedStep g H) d lam := by
    rw [← show stepDeriv g H 0 = shiftedStep g H from funext hstep]
    exact hasDerivAt_stepDeriv (g := g) hlam 0
  have hd : -(Ring.inverse (H + lam • 1)) s = d := by
    simp [d, s, stepDeriv, step, pow_two]
  change HasDerivAt (shiftedStep g H) (-(Ring.inverse (H + lam • 1)) s) lam ∧ _
  rw [hd]
  refine ⟨hD, ?_⟩
  change deriv (phi g H Δ) lam = -⟪s, d⟫ / ‖s‖ ^ 3 ∧
    iteratedDeriv 2 (phi g H Δ) lam =
      3 * (⟪s, d⟫ ^ 2 - ‖s‖ ^ 2 * ‖d‖ ^ 2) / ‖s‖ ^ 5
  have hπ1 : deriv (secular g H) lam = 2 * ⟪s, d⟫ := by
    simpa [s, d, iteratedDeriv_one, secularCoeff_zero, hstep] using
      (iteratedDeriv_secular (g := g) hlam 0).1
  have hπ2 : iteratedDeriv 2 (secular g H) lam = 6 * ‖d‖ ^ 2 := by
    have hc : secularCoeff 1 = 6 := by norm_num [secularCoeff, Nat.factorial_succ]
    simpa [hc, d] using (iteratedDeriv_secular (g := g) hlam 0).2
  have hpow3 : secular g H lam ^ ((-1 / 2 : ℝ) - 1) = (‖s‖ ^ 3)⁻¹ := by
    simpa [s, secular, show (-1 / 2 : ℝ) - 1 = -3 / 2 by norm_num] using
      sq_rpow_neg_half ‖s‖ (norm_nonneg _) 3
  have hpow5 : secular g H lam ^ ((-1 / 2 : ℝ) - 2) = (‖s‖ ^ 5)⁻¹ := by
    simpa [s, secular, show (-1 / 2 : ℝ) - 2 = -5 / 2 by norm_num] using
      sq_rpow_neg_half ‖s‖ (norm_nonneg _) 5
  constructor
  · rw [(hasDerivAt_trSecular hg hlam Δ (-1 / 2)).deriv, hπ1, hpow3]
    ring
  · have heq : iteratedDeriv 2 (phi g H Δ) lam =
        iteratedDeriv 2 (fun t => secular g H t ^ (-1 / 2 : ℝ)) lam := by
      simp only [iteratedDeriv_succ, iteratedDeriv_zero]
      congr 1
      funext x
      exact deriv_sub_const _
    rw [heq, iteratedDeriv_two_secular_rpow hg hlam, hπ1, hπ2, hpow3, hpow5]
    have hs : ‖s‖ ≠ 0 := by
      intro hz
      have hp := secular_pos (hH := hH) hg hlam
      change 0 < ‖s‖ ^ 2 at hp
      simp [hz] at hp
    field_simp
    ring

/-- **Equation (7.3.11)** of [conn2000trust]. The **Newton step** for the secular equation
$\phi(\lambda) = 0$ is
$$\lambda \mapsto \lambda - \frac{\phi(\lambda)}{\phi'(\lambda)}.$$

It is `Newton.scalarStep` for $\phi$ and its derivative; the quotient is $0$ where
$\phi'(\lambda) = 0$. -/
noncomputable abbrev moreSorensenNewtonStep (g : E) (H : E →L[ℝ] E) (Δ : ℝ) : ℝ → ℝ :=
  Newton.scalarStep (phi g H Δ) (deriv (phi g H Δ))

/-- **Algorithm 7.3.1** of [conn2000trust]. Let $g \neq 0$, $\Delta > 0$ and $\lambda > -\lambda_1$.
Let $L$ be an injective operator with $L L^* = H + \lambda I$ (a nonsingular Cholesky factor),
and let $L w = s(\lambda)$. Then the Newton step (7.3.11) is
$$\lambda + \frac{\|s(\lambda)\| - \Delta}{\Delta} \cdot \frac{\|s(\lambda)\|^2}{\|w\|^2}.$$

So one triangular solve gives the Newton step without the full derivative of $s(\lambda)$. -/
theorem algorithm_7_3_1_step (hg : g ≠ 0) {Δ lam : ℝ} (hΔ : 0 < Δ)
    (hlam : -leftmost hH < lam) (L : E →L[ℝ] E) (hL : Function.Injective L)
    (hfac : L.comp L.adjoint = H + lam • 1) {w : E}
    (hw : L w = shiftedStep g H lam) :
    moreSorensenNewtonStep g H Δ lam =
      lam + ((‖shiftedStep g H lam‖ - Δ) / Δ) * (‖shiftedStep g H lam‖ ^ 2 / ‖w‖ ^ 2) := by
  let s := shiftedStep g H lam
  let z := (Ring.inverse (H + lam • 1)) s
  have hsol : L (L.adjoint z) = s := by
    rw [← ContinuousLinearMap.comp_apply, hfac]
    exact add_smul_inverse_apply hlam s
  have hz : L.adjoint z = w := hL (hsol.trans hw.symm)
  have hinner : ⟪s, z⟫ = ‖w‖ ^ 2 := by
    rw [← show L w = s from hw, ← ContinuousLinearMap.adjoint_inner_right, hz,
      real_inner_self_eq_norm_sq]
  have hder := ((lemma_7_3_1 (hH := hH) hg Δ).2.2 lam hlam).2.1
  change deriv (phi g H Δ) lam = -⟪s, -z⟫ / ‖s‖ ^ 3 at hder
  rw [inner_neg_right, neg_neg, hinner] at hder
  have hs₀ : s ≠ 0 := by
    intro hs
    have hp := secular_pos (hH := hH) hg hlam
    change 0 < ‖s‖ ^ 2 at hp
    simp [hs] at hp
  have hw₀ : w ≠ 0 := fun h => hs₀ (by simpa [h] using hw.symm)
  rw [moreSorensenNewtonStep, Newton.scalarStep, phi_eq_inv_norm_sub_inv, hder]
  change lam - (1 / ‖s‖ - 1 / Δ) / (‖w‖ ^ 2 / ‖s‖ ^ 3) =
    lam + ((‖s‖ - Δ) / Δ) * (‖s‖ ^ 2 / ‖w‖ ^ 2)
  field_simp [norm_ne_zero_iff.mpr hs₀, norm_ne_zero_iff.mpr hw₀, hΔ.ne']
  ring

omit [FiniteDimensional ℝ E] in
private theorem phi_root {Δ r : ℝ} (hΔ : 0 < Δ) (hroot : secular g H r = Δ ^ 2) :
    phi g H Δ r = 0 := by
  rw [phi, trSecular, hroot, ← Real.rpow_two, ← Real.rpow_mul hΔ.le, sub_self]

private theorem moreSorensenNewtonStep_eq (hg : g ≠ 0) {Δ x : ℝ} (hΔ : 0 < Δ)
    (hx : -leftmost hH < x) :
    moreSorensenNewtonStep g H Δ x = x + trNewtonCorrection g H Δ x := by
  rw [moreSorensenNewtonStep, Newton.scalarStep, trNewtonCorrection_eq hg hx hΔ, sub_eq_add_neg,
    neg_div]

/-- **Lemma 7.3.2** of [conn2000trust], existence of the root. Let $g \neq 0$, $\Delta > 0$, and
$x > -\lambda_1$ with $\phi(x) < 0$. Then there is a unique $r > -\lambda_1$ with
$\|s(r)\|^2 = \Delta^2$. -/
theorem existsUnique_secular_root_of_phi_neg (hg : g ≠ 0) {Δ x : ℝ} (hΔ : 0 < Δ)
    (hx : -leftmost hH < x) (hbelow : phi g H Δ x < 0) :
    ∃! r, -leftmost hH < r ∧ secular g H r = Δ ^ 2 := by
  have hspos : 0 < ‖step g H x‖ := by
    have hp := secular_pos (hH := hH) hg hx
    rw [secular] at hp
    exact norm_pos_iff.2 fun h => by simp [h] at hp
  have hs : Δ < ‖step g H x‖ := by
    by_contra! hn
    rw [phi_eq_inv_norm_sub_inv] at hbelow
    have h := one_div_le_one_div_of_le hspos hn
    linarith only [hbelow, h]
  have hπx : Δ ^ 2 < secular g H x :=
    (pow_lt_pow_iff_left₀ hΔ.le hspos.le two_ne_zero).mpr hs
  obtain ⟨-, hπc, hπa, -, hπ0, -⟩ := secular_shape (hH := hH) hg 1
  obtain ⟨b, hxb, hb⟩ := ((eventually_ge_atTop x).and
    (hπ0.eventually (gt_mem_nhds (pow_pos hΔ 2)))).exists
  obtain ⟨r, hmem, hr⟩ := intermediate_value_Icc' hxb
    (hπc.mono fun _ hy => hx.trans_le hy.1) ⟨hb.le, hπx.le⟩
  have hrd := hx.trans_le hmem.1
  exact ⟨r, ⟨hrd, hr⟩, fun y hy => hπa.injOn hy.1 hrd (hy.2.trans hr.symm)⟩

/-- **Lemma 7.3.2** of [conn2000trust], exact arrival. Let $g \neq 0$ be an eigenvector of $H$,
$\Delta > 0$, and $r > -\lambda_1$ with $\|s(r)\|^2 = \Delta^2$. Then $\phi$ is affine on
$(-\lambda_1, \infty)$, and for every $x > -\lambda_1$ the Newton step from $x$ is exactly $r$. -/
theorem moreSorensenNewtonStep_eq_root_of_eigenvector (hg : g ≠ 0)
    (heig : ∃ c : ℝ, H g = c • g) {Δ r x : ℝ} (hΔ : 0 < Δ)
    (hr : -leftmost hH < r) (hroot : secular g H r = Δ ^ 2)
    (hx : -leftmost hH < x) :
    moreSorensenNewtonStep g H Δ x = r := by
  have hxr : x + (r - x) = r := by ring
  have ht := (secular_rpow_tangent (hH := hH) hg hx (δ := r - x) (by rwa [hxr])
    (-1 / 2)).2.2.2.2 rfl heig
  rw [hxr] at ht
  have hderiv : deriv (phi g H Δ) x = deriv (fun t => secular g H t ^ (-1 / 2 : ℝ)) x :=
    deriv_sub_const _
  have hlin : phi g H Δ r = phi g H Δ x + deriv (phi g H Δ) x * (r - x) := by
    rw [hderiv]
    unfold phi trSecular
    linarith only [ht]
  rw [phi_root hΔ hroot] at hlin
  have hd := (trSecular_shape (hH := hH) hg Δ (β := -1 / 2) (by norm_num)).2.2 x hx
  change x - phi g H Δ x / deriv (phi g H Δ) x = r
  field_simp [ne_of_gt hd]
  linarith only [hlin]

/-- **Lemma 7.3.2** of [conn2000trust]. Let $g \neq 0$, $\Delta > 0$, and let $r > -\lambda_1$ be
the root, $\|s(r)\|^2 = \Delta^2$. Let $\lambda_0 > -\lambda_1$ with $\phi(\lambda_0) < 0$, let
$\lambda_k$ be the Newton iterates (7.3.11) from $\lambda_0$, and let
$\gamma = 1 - \phi'(r) / \phi'(\lambda_0)$. Then:

* $\lambda_k > -\lambda_1$ and $\phi(\lambda_k) \le 0$ for all $k$;
* the sequence $(\lambda_k)$ is nondecreasing;
* $0 \le \gamma < 1$ and $r - \lambda_{k+1} \le \gamma (r - \lambda_k)$ for all $k$;
* $\lambda_k \to r$ with order $2$.

**Correction.** The source states $\phi(\lambda_k) < 0$ for the later iterates. When $\phi$ is
affine, one Newton step reaches the root exactly, and the secular value is $0$ at every later
iterate. See `ConnGouldToint.Chapter07.moreSorensenNewtonStep_eq_root_of_eigenvector`.

Convergence with order $2$ is `ConvergesWithOrder`: $\lambda_k \to r$ and
$|\lambda_{k+1} - r| \le C |\lambda_k - r|^2$ for some $C > 0$ and all large $k$. -/
theorem lemma_7_3_2 (hg : g ≠ 0) {Δ r x₀ : ℝ} (hΔ : 0 < Δ)
    (hr : -leftmost hH < r) (hroot : secular g H r = Δ ^ 2)
    (hx₀ : -leftmost hH < x₀) (hbelow : phi g H Δ x₀ < 0) :
    let x := fun k : ℕ => (moreSorensenNewtonStep g H Δ)^[k] x₀
    let γ := 1 - deriv (phi g H Δ) r / deriv (phi g H Δ) x₀
    (∀ k, -leftmost hH < x k ∧ phi g H Δ (x k) ≤ 0) ∧
      Monotone x ∧ γ ∈ Ico 0 1 ∧ (∀ k, r - x (k + 1) ≤ γ * (r - x k)) ∧
      ConvergesWithOrder x r 2 := by
  let N := moreSorensenNewtonStep g H Δ
  let x := fun k : ℕ => N^[k] x₀
  obtain ⟨-, hm, hd⟩ := trSecular_shape (hH := hH) hg Δ (β := -1 / 2) (by norm_num)
  have hr₀ := phi_root hΔ hroot
  have hxr : x₀ ≤ r := by
    by_contra! hn
    exact hbelow.not_gt (hr₀ ▸ hm hr hx₀ hn)
  have hupdate (k : ℕ) : x (k + 1) = moreSorensenNewtonStep g H Δ (x k) :=
    Function.iterate_succ_apply' N k x₀
  have hmem (k : ℕ) : x k ∈ Ioc (-leftmost hH) r := by
    induction k with
    | zero => exact ⟨hx₀, hxr⟩
    | succ k ih =>
      have hstep := trNewtonCorrection_mem hΔ hr hroot ih.1
      rw [hupdate, moreSorensenNewtonStep_eq hg hΔ ih.1]
      exact ⟨ih.1.trans_le (hstep.2 ih.2), hstep.1⟩
  have hstep (k : ℕ) :
      x k + trNewtonCorrection g H Δ (x k) ≤ x (k + 1) ∧ x (k + 1) ≤ r :=
    ⟨by rw [hupdate, moreSorensenNewtonStep_eq hg hΔ (hmem k).1], (hmem _).2⟩
  obtain ⟨hmono, htend, hγ, hlinear, -⟩ :=
    tendsto_of_trNewtonCorrection_le hΔ hr hroot (hmem 0) hstep
  refine ⟨fun k => ⟨(hmem k).1, hr₀ ▸ hm.monotoneOn (hmem k).1 hr (hmem k).2⟩,
    hmono, hγ, hlinear, htend, ?_⟩
  have hsmooth : ContDiffOn ℝ 2 (phi g H Δ) (Ioi (-leftmost hH)) :=
    (contDiffOn_secular_rpow (hH := hH) hg _).sub contDiffOn_const
  obtain ⟨ε, hε, hlocal⟩ := Newton.hasIterationOrder_scalarStep_two hr₀
    (hsmooth.contDiffAt (isOpen_Ioi.mem_nhds hr)) (hd r hr).ne'
  obtain ⟨j, hj⟩ := eventually_atTop.mp (htend.eventually (Metric.ball_mem_nhds r hε))
  obtain ⟨-, C, hC, hbound⟩ := hlocal (x j) (hj j le_rfl)
  obtain ⟨l, hl⟩ := eventually_atTop.mp hbound
  refine ⟨C, hC, eventually_atTop.mpr ⟨l + j, fun k hk => ?_⟩⟩
  have he := hl (k - j) (by omega)
  change ‖N^[k - j + 1] (N^[j] x₀) - r‖ ≤ C * ‖N^[k - j] (N^[j] x₀) - r‖ ^ (2 : ℝ) at he
  rwa [← Function.iterate_add_apply, ← Function.iterate_add_apply,
    show k - j + 1 + j = k + 1 by omega, show k - j + j = k by omega] at he

/-- **Lemma 7.3.3** of [conn2000trust]. Let $g \neq 0$ and $\Delta > 0$, and let $\lambda_*$ be an
optimal multiplier for a global minimizer $s_*$ with $\|s_*\| \le \Delta$. Let
$\lambda > -\lambda_1$ with $\phi(\lambda) > 0$, and let $\lambda^+$ be the Newton step from
$\lambda$. Then $\lambda^+ < \lambda$, $\lambda^+ \le \lambda_*$, and either
$$\lambda^+ > -\lambda_1 \text{ and } \phi(\lambda^+) \le 0, \qquad \text{or} \qquad \lambda^+
  \le -\lambda_1.$$

The optimal multiplier may be the pole $-\lambda_1$, or $0$ at an interior solution. -/
theorem lemma_7_3_3 (hg : g ≠ 0) {Δ r x : ℝ} (hΔ : 0 < Δ)
    {sM : E} (hsM : ‖sM‖ ≤ Δ) (hmul : IsTrustRegionMultiplier g H Δ sM r)
    (hx : -leftmost hH < x) (hpos : 0 < phi g H Δ x) :
    let x' := moreSorensenNewtonStep g H Δ x
    x' < x ∧ x' ≤ r ∧ ((-leftmost hH < x' ∧ phi g H Δ x' ≤ 0) ∨ x' ≤ -leftmost hH) := by
  let y := moreSorensenNewtonStep g H Δ x
  have hr : -leftmost hH ≤ r := neg_leftmost_le_shiftThreshold.trans
    (shiftThreshold_le_of_isPositive (hH := hH) hmul.nonneg hmul.isPositive)
  have hd := (trSecular_shape (hH := hH) hg Δ (β := -1 / 2) (by norm_num)).2.2 x hx
  have hyx : y < x := sub_lt_self _ (div_pos hpos hd)
  refine ⟨hyx, ?_⟩
  rcases lt_or_ge (-leftmost hH) y with hy | hy
  · have hxy : x + (y - x) = y := by ring
    have htan := (secular_rpow_tangent (hH := hH) hg hx (δ := y - x) (by rwa [hxy])
      (-1 / 2)).2.2.1 (by norm_num)
    rw [hxy] at htan
    have hderiv : deriv (phi g H Δ) x = deriv (fun t => secular g H t ^ (-1 / 2 : ℝ)) x :=
      deriv_sub_const _
    have hphi : phi g H Δ y ≤ 0 := by
      have ht : phi g H Δ y ≤ phi g H Δ x + deriv (phi g H Δ) x * (y - x) := by
        rw [hderiv]
        unfold phi trSecular
        linarith only [htan]
      have hz : phi g H Δ x + deriv (phi g H Δ) x * (y - x) = 0 := by
        dsimp [y, moreSorensenNewtonStep, Newton.scalarStep]
        field_simp [ne_of_gt hd]
        ring
      exact ht.trans_eq hz
    refine ⟨?_, Or.inl ⟨hy, hphi⟩⟩
    by_contra! hy'
    have hsq := (secular_lt_norm_sq_of_shifted (hH := hH) hg hr hmul.shifted hy').trans_le
      (pow_le_pow_left₀ (norm_nonneg _) hsM 2)
    have hnorm : ‖step g H y‖ < Δ := by
      rw [secular] at hsq
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hΔ.le two_ne_zero).mp hsq
    have hnpos : 0 < ‖step g H y‖ := by
      have hp := secular_pos (hH := hH) hg hy
      rw [secular] at hp
      exact norm_pos_iff.2 fun h => by simp [h] at hp
    have hgt : 0 < phi g H Δ y := by
      rw [phi_eq_inv_norm_sub_inv]
      exact sub_pos.mpr (one_div_lt_one_div_of_lt hnpos hnorm)
    exact hphi.not_gt hgt
  · exact ⟨hy.trans hr, Or.inr hy⟩

omit [FiniteDimensional ℝ E] in
private theorem quadModel_eq_of_shifted_comparison (hH' : (H : E →ₗ[ℝ] E).IsSymmetric)
    {μ : ℝ} {s : E} (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) (u : E) :
    quadModel g H u =
      (1 / 2) * (⟪u - s, (H + μ • (1 : E →L[ℝ] E)) (u - s)⟫ -
        ⟪s, (H + μ • (1 : E →L[ℝ] E)) s⟫ - μ * ‖u‖ ^ 2) := by
  have hd := quadModel_sub_eq_of_shifted hH' hs u
  rw [quadModel_eq_of_shifted hs, inner_eq_of_shifted hs] at hd
  linarith

private theorem quadModel_lower_bound_of_shifted {μ Δ : ℝ} {s u : E}
    (hμ : 0 ≤ μ) (hlam : -leftmost hH < μ)
    (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) (hu : ‖u‖ ≤ Δ) :
    -(1 / 2) * (⟪s, (H + μ • (1 : E →L[ℝ] E)) s⟫ + μ * Δ ^ 2) ≤ quadModel g H u := by
  have hp := isPositive_add_smul_of_le (hH := hH) hlam.le
  have hquad := ContinuousLinearMap.inner_apply_nonneg_of_isPositive hp (u - s)
  have hnorm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg u) hu 2) hμ
  rw [quadModel_eq_of_shifted_comparison hH hs]
  nlinarith only [hquad, hnorm]

/-- **Equation (7.3.19)** of [conn2000trust]. A step $s$ is an **acceptable approximation** to the
model minimizer $s_M$ with coefficients $\kappa_{\mathrm{opt}}$ and $\kappa_{\mathrm{tr}}$ if
$$q(s) \le \kappa_{\mathrm{opt}} \, q(s_M) \quad \text{and} \quad \|s\| \le \kappa_{\mathrm{tr}}
  \Delta.$$
-/
def IsAcceptableModelStep (g : E) (H : E →L[ℝ] E) (Δ κopt κtr : ℝ) (s sM : E) : Prop :=
  quadModel g H s ≤ κopt * quadModel g H sM ∧ ‖s‖ ≤ κtr * Δ

omit [FiniteDimensional ℝ E] in
/-- **Prose following Lemmas 7.3.5 and 7.3.6** of [conn2000trust]. Let $\Delta \ge 0$ and
$q(s_M) \le 0$. If $s$ is acceptable with coefficients $\kappa_{\mathrm{opt}}$ and
$\kappa_{\mathrm{tr}}$, and $\kappa_{\mathrm{opt}}' \le \kappa_{\mathrm{opt}}$ and
$\kappa_{\mathrm{tr}} \le \kappa_{\mathrm{tr}}'$, then $s$ is acceptable with coefficients
$\kappa_{\mathrm{opt}}'$ and $\kappa_{\mathrm{tr}}'$.

**Correction.** Since the reference value $q(s_M)$ is nonpositive, a smaller coefficient
$\kappa_{\mathrm{opt}}$ gives a weaker test. The comparisons of the coefficients in the prose of
the source must therefore be reversed: the stopping rules give acceptance for every
$\kappa_{\mathrm{opt}}$ at most the computed bound. -/
theorem IsAcceptableModelStep.weaken {Δ κopt κtr κopt' κtr' : ℝ} {s sM : E}
    (h : IsAcceptableModelStep g H Δ κopt κtr s sM) (hΔ : 0 ≤ Δ)
    (hval : quadModel g H sM ≤ 0) (hopt : κopt' ≤ κopt) (htr : κtr ≤ κtr') :
    IsAcceptableModelStep g H Δ κopt' κtr' s sM :=
  ⟨h.1.trans (mul_le_mul_of_nonpos_right hopt hval),
    h.2.trans (mul_le_mul_of_nonneg_right htr hΔ)⟩

/-- **Lemma 7.3.5** of [conn2000trust]. Let $\mu \ge 0$ with $\mu > -\lambda_1$, $\Delta > 0$ and
$0 < \kappa < 1$. If $\bigl|\|s(\mu)\| - \Delta\bigr| \le \kappa \Delta$, then for every $u$
with $\|u\| \le \Delta$,
$$q(s(\mu)) \le (1 - \kappa)^2 q(u).$$
-/
theorem lemma_7_3_5 {μ Δ κ : ℝ} (hμ : 0 ≤ μ) (hlam : -leftmost hH < μ)
    (hΔ : 0 < Δ) (hκ : κ ∈ Ioo 0 1) {u : E} (hu : ‖u‖ ≤ Δ)
    (hnear : |‖shiftedStep g H μ‖ - Δ| ≤ κ * Δ) :
    quadModel g H (shiftedStep g H μ) ≤ (1 - κ) ^ 2 * quadModel g H u := by
  let s := shiftedStep g H μ
  let A := H + μ • (1 : E →L[ℝ] E)
  have hs : A s = -g := (step_spec (g := g) hlam).1
  have hlower := quadModel_lower_bound_of_shifted (hH := hH) hμ hlam hs hu
  have hpos := ContinuousLinearMap.inner_apply_nonneg_of_isPositive
    (isPositive_add_smul_of_le (hH := hH) hlam.le) s
  have hlen : (1 - κ) * Δ ≤ ‖s‖ := by
    dsimp [s]
    nlinarith only [(abs_le.mp hnear).1]
  have hκ' : 0 ≤ 1 - κ := sub_nonneg.mpr hκ.2.le
  have hscale : (1 - κ) ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ hκ' (show 1 - κ ≤ 1 by linarith [hκ.1]) 2
  have hnorm := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (mul_nonneg hκ' hΔ.le) hlen 2) hμ
  have hcurv := mul_le_mul_of_nonneg_right hscale hpos
  calc
    quadModel g H s ≤ (1 - κ) ^ 2 * (-(1 / 2) * (⟪s, A s⟫ + μ * Δ ^ 2)) := by
      rw [quadModel_eq_of_shifted_comparison hH hs]
      simp only [sub_self, map_zero, inner_zero_left, zero_sub]
      change μ * ((1 - κ) * Δ) ^ 2 ≤ μ * ‖s‖ ^ 2 at hnorm
      change (1 - κ) ^ 2 * ⟪s, A s⟫ ≤ 1 * ⟪s, A s⟫ at hcurv
      nlinarith only [hnorm, hcurv]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower (sq_nonneg _)

/-- **Lemma 7.3.6** of [conn2000trust]. Let $\mu \ge 0$ with $\mu > -\lambda_1$ and
$0 < \kappa < 1$. Let $v$ satisfy $\|s(\mu) + v\| = \Delta$ and
$$\langle v, (H + \mu I) v \rangle \le \kappa \bigl(\langle s(\mu), (H + \mu I) s(\mu) \rangle +
  \mu \Delta^2\bigr).$$
Then for every $u$ with $\|u\| \le \Delta$,
$$q(s(\mu) + v) \le (1 - \kappa) q(u).$$
-/
theorem lemma_7_3_6 {μ Δ κ : ℝ} (hμ : 0 ≤ μ) (hlam : -leftmost hH < μ)
    (hκ : κ ∈ Ioo 0 1) {u v : E} (hu : ‖u‖ ≤ Δ)
    (hboundary : ‖shiftedStep g H μ + v‖ = Δ)
    (hdir : ⟪v, (H + μ • (1 : E →L[ℝ] E)) v⟫ ≤ κ *
      (⟪shiftedStep g H μ, (H + μ • (1 : E →L[ℝ] E)) (shiftedStep g H μ)⟫ + μ * Δ ^ 2)) :
    quadModel g H (shiftedStep g H μ + v) ≤ (1 - κ) * quadModel g H u := by
  let s := shiftedStep g H μ
  let A := H + μ • (1 : E →L[ℝ] E)
  have hs : A s = -g := (step_spec (g := g) hlam).1
  have hlower := quadModel_lower_bound_of_shifted (hH := hH) hμ hlam hs hu
  calc
    quadModel g H (s + v) ≤ (1 - κ) * (-(1 / 2) * (⟪s, A s⟫ + μ * Δ ^ 2)) := by
      rw [quadModel_eq_of_shifted_comparison hH hs, add_sub_cancel_left]
      change ‖s + v‖ = Δ at hboundary
      rw [hboundary]
      change ⟪v, A v⟫ ≤ κ * (⟪s, A s⟫ + μ * Δ ^ 2) at hdir
      change (1 / 2) * (⟪v, A v⟫ - ⟪s, A s⟫ - μ * Δ ^ 2) ≤ _
      nlinarith only [hdir]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower (sub_nonneg.mpr hκ.2.le)

omit [FiniteDimensional ℝ E] in
private theorem quadModel_nonpos_of_isMinOn {Δ : ℝ} (hΔ : 0 ≤ Δ) {sM : E}
    (hmin : IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) sM) :
    quadModel g H sM ≤ 0 := by
  simpa using hmin (show (0 : E) ∈ Metric.closedBall 0 Δ by simpa using hΔ)

/-- **Algorithm 7.3.5** of [conn2000trust], Step 1. Let $\mu \ge 0$ with $\mu > -\lambda_1$,
$\Delta > 0$, $0 < \kappa < 1$, and let $s_M$ be a global minimizer of $q$ on the ball of radius
$\Delta$. If $\bigl|\|s(\mu)\| - \Delta\bigr| \le \kappa \Delta$,
$\kappa_{\mathrm{opt}} \le (1 - \kappa)^2$ and $1 + \kappa \le \kappa_{\mathrm{tr}}$, then
$s(\mu)$ is an acceptable approximation (7.3.19) to $s_M$ with coefficients
$\kappa_{\mathrm{opt}}$ and $\kappa_{\mathrm{tr}}$. -/
theorem acceptable_of_easy_stopping_rule {μ Δ κ κopt κtr : ℝ} (hμ : 0 ≤ μ)
    (hlam : -leftmost hH < μ) (hΔ : 0 < Δ) (hκ : κ ∈ Ioo 0 1)
    {sM : E} (hsM : ‖sM‖ ≤ Δ)
    (hmin : IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) sM)
    (hnear : |‖shiftedStep g H μ‖ - Δ| ≤ κ * Δ)
    (hopt : κopt ≤ (1 - κ) ^ 2) (htr : 1 + κ ≤ κtr) :
    IsAcceptableModelStep g H Δ κopt κtr (shiftedStep g H μ) sM := by
  have h : IsAcceptableModelStep g H Δ ((1 - κ) ^ 2) (1 + κ) (shiftedStep g H μ) sM :=
    ⟨lemma_7_3_5 hμ hlam hΔ hκ hsM hnear, by nlinarith only [(abs_le.mp hnear).2]⟩
  exact h.weaken hΔ.le (quadModel_nonpos_of_isMinOn hΔ.le hmin) hopt htr

/-- **Algorithm 7.3.5** of [conn2000trust], hard-case test. Let $\mu \ge 0$ with $\mu > -\lambda_1$,
$0 < \kappa < 1$, and let $s_M$ be a global minimizer of $q$ on the ball of radius $\Delta$. Let
$v$ satisfy $\|s(\mu) + v\| = \Delta$ and
$$\langle v, (H + \mu I) v \rangle \le \kappa \bigl(\langle s(\mu), (H + \mu I) s(\mu) \rangle +
  \mu \Delta^2\bigr).$$
If $\kappa_{\mathrm{opt}} \le 1 - \kappa$ and $1 \le \kappa_{\mathrm{tr}}$, then $s(\mu) + v$ is
an acceptable approximation (7.3.19) to $s_M$ with coefficients $\kappa_{\mathrm{opt}}$ and
$\kappa_{\mathrm{tr}}$. -/
theorem acceptable_of_hard_stopping_rule {μ Δ κ κopt κtr : ℝ} (hμ : 0 ≤ μ)
    (hlam : -leftmost hH < μ) (hκ : κ ∈ Ioo 0 1) {sM v : E} (hsM : ‖sM‖ ≤ Δ)
    (hmin : IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) sM)
    (hboundary : ‖shiftedStep g H μ + v‖ = Δ)
    (hdir : ⟪v, (H + μ • (1 : E →L[ℝ] E)) v⟫ ≤ κ *
      (⟪shiftedStep g H μ, (H + μ • (1 : E →L[ℝ] E)) (shiftedStep g H μ)⟫ + μ * Δ ^ 2))
    (hopt : κopt ≤ 1 - κ) (htr : 1 ≤ κtr) :
    IsAcceptableModelStep g H Δ κopt κtr (shiftedStep g H μ + v) sM := by
  have hΔ := (norm_nonneg sM).trans hsM
  have h : IsAcceptableModelStep g H Δ (1 - κ) 1 (shiftedStep g H μ + v) sM :=
    ⟨lemma_7_3_6 hμ hlam hκ hsM hboundary hdir, by simp [hboundary]⟩
  exact h.weaken hΔ (quadModel_nonpos_of_isMinOn hΔ hmin) hopt htr

/-- **Equation (7.3.14)** of [conn2000trust]. For $\theta \in \mathbb{R}$ and a bracket
$[\lambda^L, \lambda^U]$, the **safeguarded trial multiplier** is
$$\max\bigl\{\sqrt{\lambda^L \lambda^U}, \; \lambda^L + \theta (\lambda^U - \lambda^L)\bigr\}.$$

It is `Subproblem.bracketEstimate 1 θ`. -/
noncomputable abbrev moreSorensenTrial (θ lo hi : ℝ) : ℝ := bracketEstimate 1 θ lo hi

/-- **Algorithm 7.3.4** of [conn2000trust], multiplier update with a factorization test. Let $P$ be
a test of positive definiteness of $H + \lambda I$, and let $(\lambda^L, \lambda^U, \lambda)$ be
the current lower end, upper end and trial multiplier, with a lower estimate $b$ of the pole.
The update returns a new triple as follows, where $T(l, u)$ is the trial multiplier (7.3.14) and
$\lambda^N$ is the Newton step (7.3.11) from $\lambda$:

* If $\lambda$ fails the test: $\lambda^{L\prime} = \max\{\lambda^L, \lambda, b\}$, and the
  result is $(\lambda^{L\prime}, \lambda^U, T(\lambda^{L\prime}, \lambda^U))$.
* If $\lambda$ passes the test and $g = 0$: with $\lambda^{L\prime} = \max\{\lambda^L, b\}$, the
  result is $(\lambda^{L\prime}, \lambda, T(\lambda^{L\prime}, \lambda))$.
* If $\lambda$ passes the test, $g \neq 0$ and $\phi(\lambda) \le 0$: the result is
  $(\max\{\lambda^L, \lambda\}, \lambda^U, \lambda^N)$.
* If $\lambda$ passes the test, $g \neq 0$ and $\phi(\lambda) > 0$: with
  $\lambda^{L\prime} = \max\{\lambda^L, b\}$, the result is
  $(\lambda^{L\prime}, \lambda, \lambda^N)$ if $\lambda^N$ passes the test, and otherwise
  $(\lambda^{L\prime\prime}, \lambda, T(\lambda^{L\prime\prime}, \lambda))$ with
  $\lambda^{L\prime\prime} = \max\{\lambda^{L\prime}, \lambda^N\}$.

The estimate $b$ is supplied by the successful or partial factorization. A zero gradient skips
the Newton formula, because both solves give $0$. -/
noncomputable def moreSorensenSafeguardedStepBy (g : E) (H : E →L[ℝ] E)
    (positive : ℝ → Prop) [DecidablePred positive] (Δ θ lo hi x b : ℝ) : ℝ × ℝ × ℝ :=
  if positive x then
    if ‖g‖ = 0 then
      let lo' := max lo b
      (lo', x, moreSorensenTrial θ lo' x)
    else
      let x' := moreSorensenNewtonStep g H Δ x
      if 0 < phi g H Δ x then
        let lo' := max lo b
        if positive x' then (lo', x, x')
        else
          let lo'' := max lo' x'
          (lo'', x, moreSorensenTrial θ lo'' x)
      else (max lo x, hi, x')
  else
    let lo' := max (max lo x) b
    (lo', hi, moreSorensenTrial θ lo' hi)

/-- **Algorithm 7.3.4** of [conn2000trust], multiplier update with the pole. This is the update
`ConnGouldToint.Chapter07.moreSorensenSafeguardedStepBy` with the factorization test
$\lambda > \lambda_{\mathrm{pole}}$, which is exact for $\lambda_{\mathrm{pole}} = -\lambda_1$. -/
noncomputable def moreSorensenSafeguardedStep (g : E) (H : E →L[ℝ] E)
    (pole Δ θ lo hi x b : ℝ) : ℝ × ℝ × ℝ :=
  moreSorensenSafeguardedStepBy g H (pole < ·) Δ θ lo hi x b

/-- **Algorithm 7.3.4** of [conn2000trust], the multiplier orbit before the stopping tests. Starting
from a triple $(\lambda^L_0, \lambda^U_0, \lambda_0)$, each state is obtained from the previous
one by `ConnGouldToint.Chapter07.moreSorensenSafeguardedStep`, with the lower estimate $b_k$
given as a function of the index $k$ and the current state.

The state is the lower end, the upper end and the trial multiplier. -/
noncomputable def moreSorensenSafeguardedIterates (g : E) (H : E →L[ℝ] E)
    (pole Δ θ : ℝ) (estimate : ℕ → (ℝ × ℝ × ℝ) → ℝ)
    (initial : ℝ × ℝ × ℝ) : ℕ → ℝ × ℝ × ℝ
  | 0 => initial
  | k + 1 =>
    let state := moreSorensenSafeguardedIterates g H pole Δ θ estimate initial k
    moreSorensenSafeguardedStep g H pole Δ θ state.1 state.2.1 state.2.2 (estimate k state)

/-- **Algorithm 7.3.4** of [conn2000trust], Steps 5a–b. Let $g \neq 0$, $\Delta > 0$, and let $r$ be
an optimal multiplier for a global minimizer $s_M$ with $\|s_M\| \le \Delta$. Let
$\lambda > -\lambda_1$ with $\phi(\lambda) > 0$, and let $b \le r$,
$0 \le \lambda^L \le r \le \lambda$ and $\theta \in [0, 1]$. Let $(\lambda^{L\prime},
\lambda^{U\prime}, \lambda')$ be the result of the update with the pole $-\lambda_1$, and let
$\lambda^N$ be the Newton step from $\lambda$. Then $\lambda^{L\prime} \le r$,
$\lambda^{U\prime} = \lambda$, and either
$$\lambda' = \lambda^N, \quad \lambda^N > -\lambda_1, \quad \phi(\lambda^N) \le 0, \quad
  \lambda^N \le r,$$
so the update enters the Newton interval, or $\lambda^N \le -\lambda_1$,
$\lambda^N \le \lambda^{L\prime}$ and $\lambda' \in [\lambda^{L\prime}, \lambda^{U\prime}]$, so
the failed candidate raises the lower end. -/
theorem moreSorensenSafeguardedStep_of_positive_phi (hg : g ≠ 0)
    {Δ θ lo hi x b r : ℝ} (hΔ : 0 < Δ)
    {sM : E} (hsM : ‖sM‖ ≤ Δ) (hmul : IsTrustRegionMultiplier g H Δ sM r)
    (hx : -leftmost hH < x) (hpos : 0 < phi g H Δ x) (hb : b ≤ r)
    (hlo : 0 ≤ lo) (hlr : lo ≤ r) (hrx : r ≤ x) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    let s := moreSorensenSafeguardedStep g H (-leftmost hH) Δ θ lo hi x b
    let x' := moreSorensenNewtonStep g H Δ x
    s.1 ≤ r ∧ s.2.1 = x ∧
      ((s.2.2 = x' ∧ -leftmost hH < x' ∧ phi g H Δ x' ≤ 0 ∧ x' ≤ r) ∨
        (x' ≤ -leftmost hH ∧ x' ≤ s.1 ∧ s.2.2 ∈ Icc s.1 s.2.1)) := by
  have hN := lemma_7_3_3 hg hΔ hsM hmul hx hpos
  dsimp only at hN ⊢
  rcases hN.2.2 with hgood | hbad
  · simp only [moreSorensenSafeguardedStep, moreSorensenSafeguardedStepBy, ite_eq_left hx,
      ite_eq_right (norm_ne_zero_iff.mpr hg), ite_eq_left hpos, ite_eq_left hgood.1]
    exact ⟨max_le hlr hb, trivial, Or.inl ⟨trivial, hgood.1, hgood.2, hN.2.1⟩⟩
  · simp only [moreSorensenSafeguardedStep, moreSorensenSafeguardedStepBy, ite_eq_left hx,
      ite_eq_right (norm_ne_zero_iff.mpr hg), ite_eq_left hpos, ite_eq_right (not_lt.mpr hbad)]
    have hnew := max_le (max_le hlr hb) hN.2.1
    exact ⟨hnew, trivial, Or.inr ⟨hbad, le_max_right _ _,
      bracketEstimate_mem_Icc (hlo.trans ((le_max_left _ _).trans (le_max_left _ _)))
        (hnew.trans hrx) (by simp) hθ⟩⟩

omit [FiniteDimensional ℝ E] in
/-- **Algorithm 7.3.4** of [conn2000trust], Steps 2, 3b and 5, zero gradient. If $g = 0$ and
$\lambda > \lambda_{\mathrm{pole}}$, then the update returns
$$\bigl(\max\{\lambda^L, b\}, \; \lambda, \; T(\max\{\lambda^L, b\}, \lambda)\bigr),$$
so it lowers the upper end to $\lambda$ and takes a bracket trial instead of a Newton step. -/
theorem moreSorensenSafeguardedStep_zero_gradient {pole Δ θ lo hi x b : ℝ}
    (hx : pole < x) :
    moreSorensenSafeguardedStep (0 : E) H pole Δ θ lo hi x b =
      (max lo b, x, moreSorensenTrial θ (max lo b) x) := by
  simp [moreSorensenSafeguardedStep, moreSorensenSafeguardedStepBy, hx]

private theorem isBracketRun_of_safeguarded_updates {pole r θ : ℝ}
    {lo hi x b e : ℕ → ℝ}
    (hθ : θ ∈ Ioo 0 1) (hlo : 0 ≤ lo 0) (hlr : lo 0 ≤ r) (hrh : r ≤ hi 0)
    (hx0 : x 0 ∈ Icc (lo 0) (hi 0)) (hpr : pole ≤ r)
    (hb : ∀ k, b k ≤ pole) (he : ∀ k, r < x k → e k ≤ pole)
    (hnever : ∀ k, x k ∉ Ioc pole r)
    (hleft : ∀ k, x k ≤ pole →
      lo (k + 1) = max (max (lo k) (x k)) (b k) ∧ hi (k + 1) = hi k ∧
      x (k + 1) = moreSorensenTrial θ (max (max (lo k) (x k)) (b k)) (hi k))
    (hright : ∀ k, r < x k →
      lo (k + 1) = max (lo k) (e k) ∧ hi (k + 1) = x k ∧
      x (k + 1) = moreSorensenTrial θ (max (lo k) (e k)) (x k)) :
    IsBracketRun pole r θ θ lo hi x := by
  have hθ' : θ ∈ Icc (0 : ℝ) 1 := ⟨hθ.1.le, hθ.2.le⟩
  have hinv (k : ℕ) :
      0 ≤ lo k ∧ lo k ≤ r ∧ r ≤ hi k ∧ x k ∈ Icc (lo k) (hi k) := by
    induction k with
    | zero => exact ⟨hlo, hlr, hrh, hx0⟩
    | succ k ih =>
      rcases le_or_gt (x k) pole with hx | hx
      · obtain ⟨hl, hu, ht⟩ := hleft k hx
        rw [hl, hu, ht]
        have h0 : 0 ≤ max (max (lo k) (x k)) (b k) :=
          ih.1.trans ((le_max_left _ _).trans (le_max_left _ _))
        have hp := max_le (max_le ih.2.1 (hx.trans hpr)) ((hb k).trans hpr)
        exact ⟨h0, hp, ih.2.2.1,
          bracketEstimate_mem_Icc h0 (hp.trans ih.2.2.1) (by simp) hθ'⟩
      · have hxr : r < x k := lt_of_not_ge fun hr => hnever k ⟨hx, hr⟩
        obtain ⟨hl, hu, ht⟩ := hright k hxr
        rw [hl, hu, ht]
        have h0 := ih.1.trans (le_max_left _ (e k))
        have hp := max_le ih.2.1 ((he k hxr).trans hpr)
        exact ⟨h0, hp, hxr.le, bracketEstimate_mem_Icc h0 (hp.trans hxr.le) (by simp) hθ'⟩
  refine ⟨hlo, hlr, hrh, ?_, ?_, ?_⟩
  · exact fun k hk => (hnever k hk).elim
  · intro k hx
    obtain ⟨hl, hu, ht⟩ := hleft k hx
    exact ⟨hu, Or.inr ⟨b k, hb k, hl⟩, θ, ⟨le_rfl, le_rfl⟩, 1, by simp,
      by rw [hl, hu, ht]⟩
  · intro k hx
    obtain ⟨hl, hu, ht⟩ := hright k hx
    refine ⟨hu.trans (min_eq_right (hinv k).2.2.2.2).symm, Or.inr ⟨e k, he k hx, hl⟩,
      θ, ⟨le_rfl, le_rfl⟩, θ, ⟨le_rfl, le_rfl⟩, le_rfl, 1, by simp, 1, by simp, le_rfl, ?_⟩
    rw [hl, hu, ht]
    exact ⟨le_rfl, le_rfl⟩

omit [FiniteDimensional ℝ E] in
/-- **Theorem 7.3.4** of [conn2000trust], multiplier convergence for zero gradient. Let
$\theta \in (0, 1)$ and $0 \le \lambda^L_0 \le \lambda_{\mathrm{pole}} \le \lambda^U_0$, with
$\lambda_0 \in [\lambda^L_0, \lambda^U_0]$ and lower estimates
$b_k \le \lambda_{\mathrm{pole}}$. If the triples $(\lambda^L_k, \lambda^U_k, \lambda_k)$ follow
the update with $g = 0$, then they form a bracketing run with pole and target
$\lambda_{\mathrm{pole}}$, and $\lambda_k \to \lambda_{\mathrm{pole}}$.

Certified pivot or curvature estimates may raise the lower end without changing the limit. -/
theorem moreSorensen_zero_gradient_run {pole Δ θ : ℝ} {lo hi x b : ℕ → ℝ}
    (hθ : θ ∈ Ioo 0 1) (hlo : 0 ≤ lo 0) (hlp : lo 0 ≤ pole) (hph : pole ≤ hi 0)
    (hx0 : x 0 ∈ Icc (lo 0) (hi 0)) (hb : ∀ k, b k ≤ pole)
    (hrec : ∀ k, (lo (k + 1), hi (k + 1), x (k + 1)) =
      moreSorensenSafeguardedStep (0 : E) H pole Δ θ (lo k) (hi k) (x k) (b k)) :
    IsBracketRun pole pole θ θ lo hi x ∧ Tendsto x atTop (𝓝 pole) := by
  have hleft (k : ℕ) (hx : x k ≤ pole) :
      lo (k + 1) = max (max (lo k) (x k)) (b k) ∧ hi (k + 1) = hi k ∧
      x (k + 1) = moreSorensenTrial θ (max (max (lo k) (x k)) (b k)) (hi k) := by
    simpa only [moreSorensenSafeguardedStep, moreSorensenSafeguardedStepBy,
      ite_eq_right (not_lt.mpr hx), Prod.mk.injEq] using hrec k
  have hright (k : ℕ) (hx : pole < x k) :
      lo (k + 1) = max (lo k) (b k) ∧ hi (k + 1) = x k ∧
      x (k + 1) = moreSorensenTrial θ (max (lo k) (b k)) (x k) := by
    simpa only [moreSorensenSafeguardedStep_zero_gradient hx, Prod.mk.injEq] using hrec k
  have hnever (k : ℕ) : x k ∉ Ioc pole pole := fun hk => hk.1.not_ge hk.2
  have hrun := isBracketRun_of_safeguarded_updates hθ hlo hlp hph hx0 le_rfl hb
    (fun k _ => hb k) hnever hleft hright
  exact ⟨hrun, (hrun.tendsto_bracket_of_never_mem le_rfl hθ.1 hθ.2 hnever).2.2⟩

/-- **Algorithm 7.3.4** of [conn2000trust], safeguarding before the Newton interval for a nonzero
gradient. Let $g \neq 0$, $\Delta > 0$, $\theta \in (0, 1)$, and let $r$ be an optimal
multiplier for a global minimizer $s_M$ with $\|s_M\| \le \Delta$. Let
$0 \le \lambda^L_0 \le r \le \lambda^U_0$, $\lambda_0 \in [\lambda^L_0, \lambda^U_0]$, and
$b_k \le -\lambda_1$ for all $k$. Suppose that $\phi(y) > 0$ for all $y > r$, that no
$\lambda_k$ lies in $(-\lambda_1, r]$, and that the triples follow the update with the pole
$-\lambda_1$. Then the triples form a bracketing run with pole $-\lambda_1$ and target $r$, and
for every $k$ with $\lambda_k > r$ the Newton step from $\lambda_k$ is at most $-\lambda_1$.

So each trial with a successful factorization also rejects its Newton candidate. -/
theorem moreSorensen_nonzero_bracket_run (hg : g ≠ 0)
    {Δ r θ : ℝ} {sM : E} {lo hi x b : ℕ → ℝ} (hΔ : 0 < Δ) (hθ : θ ∈ Ioo 0 1)
    (hsM : ‖sM‖ ≤ Δ) (hmul : IsTrustRegionMultiplier g H Δ sM r)
    (hlo : 0 ≤ lo 0) (hlr : lo 0 ≤ r) (hrh : r ≤ hi 0) (hx0 : x 0 ∈ Icc (lo 0) (hi 0))
    (hb : ∀ k, b k ≤ -leftmost hH)
    (hpos : ∀ y, r < y → 0 < phi g H Δ y)
    (hnever : ∀ k, x k ∉ Ioc (-leftmost hH) r)
    (hrec : ∀ k, (lo (k + 1), hi (k + 1), x (k + 1)) =
      moreSorensenSafeguardedStep g H (-leftmost hH) Δ θ (lo k) (hi k) (x k) (b k)) :
    IsBracketRun (-leftmost hH) r θ θ lo hi x ∧
      ∀ k, r < x k → moreSorensenNewtonStep g H Δ (x k) ≤ -leftmost hH := by
  have hpr : -leftmost hH ≤ r := neg_leftmost_le_shiftThreshold.trans
    (shiftThreshold_le_of_isPositive (hH := hH) hmul.nonneg hmul.isPositive)
  have hleft (k : ℕ) (hx : x k ≤ -leftmost hH) :
      lo (k + 1) = max (max (lo k) (x k)) (b k) ∧ hi (k + 1) = hi k ∧
      x (k + 1) = moreSorensenTrial θ (max (max (lo k) (x k)) (b k)) (hi k) := by
    simpa only [moreSorensenSafeguardedStep, moreSorensenSafeguardedStepBy,
      ite_eq_right (not_lt.mpr hx), Prod.mk.injEq] using hrec k
  let N := moreSorensenNewtonStep g H Δ
  have hfail (k : ℕ) (hx : r < x k) : N (x k) ≤ -leftmost hH := by
    by_contra! hsuccess
    have hx' := hpr.trans_lt hx
    have hc := (lemma_7_3_3 hg hΔ hsM hmul hx' (hpos _ hx)).2.1
    have hn : x (k + 1) = N (x k) := by
      have he := congrArg (fun t : ℝ × ℝ × ℝ => t.2.2) (hrec k)
      simpa only [N, moreSorensenSafeguardedStep, moreSorensenSafeguardedStepBy, ite_eq_left hx',
        ite_eq_right (norm_ne_zero_iff.mpr hg), ite_eq_left (hpos _ hx), ite_eq_left hsuccess]
        using he
    exact hnever (k + 1) ⟨hn ▸ hsuccess, hn ▸ hc⟩
  have hright (k : ℕ) (hx : r < x k) :
      lo (k + 1) = max (lo k) (max (b k) (N (x k))) ∧ hi (k + 1) = x k ∧
      x (k + 1) = moreSorensenTrial θ (max (lo k) (max (b k) (N (x k)))) (x k) := by
    simpa only [N, moreSorensenSafeguardedStep, moreSorensenSafeguardedStepBy,
      ite_eq_left (hpr.trans_lt hx), ite_eq_right (norm_ne_zero_iff.mpr hg),
      ite_eq_left (hpos _ hx), ite_eq_right (not_lt.mpr (hfail k hx)), Prod.mk.injEq, max_assoc]
      using hrec k
  exact ⟨isBracketRun_of_safeguarded_updates hθ hlo hlr hrh hx0 hpr hb
    (fun k hk => max_le (hb k) (hfail k hk)) hnever hleft hright, hfail⟩

/-- **Equation (7.3.18)** of [conn2000trust]. Let $\Delta > 0$ and $\mu \ge -\lambda_1$, and let $s$
satisfy $(H + \mu I) s = -g$ and $\|s\| = \Delta$. Then
$$\frac{\|g\|}{\Delta} - \lambda_n \le \mu \le \frac{\|g\|}{\Delta} - \lambda_1.$$
-/
theorem multiplier_bounds_of_boundary {μ Δ : ℝ} {s : E} (hΔ : 0 < Δ)
    (hμ : -leftmost hH ≤ μ)
    (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) (hn : ‖s‖ = Δ) :
    ‖g‖ / Δ - rightmost hH ≤ μ ∧ μ ≤ ‖g‖ / Δ - leftmost hH := by
  obtain ⟨hl, hu⟩ := norm_add_smul_apply_bounds (hH := hH) hμ s
  rw [hs, norm_neg, hn] at hl hu
  exact ⟨sub_le_iff_le_add.mpr ((div_le_iff₀ hΔ).2 hu),
    le_sub_iff_add_le.mpr ((le_div_iff₀ hΔ).2 hl)⟩

/-- **Theorem 7.3.4** of [conn2000trust], finite entry into the Newton interval. Let
$\theta \in (0, 1)$ and $r > \lambda_s$, where $\lambda_s = \max\{0, -\lambda_1\}$. If
$(\lambda^L_k, \lambda^U_k, \lambda_k)$ is a bracketing run with pole $\lambda_s$ and target
$r$, and $\lambda^L_0 < r$, then $\lambda_k \in (\lambda_s, r]$ for some $k$. -/
theorem moreSorensen_bracketing_enters_newton {r θ : ℝ} {lo hi lam : ℕ → ℝ}
    (hrun : IsBracketRun (shiftThreshold hH) r θ θ lo hi lam)
    (hr : shiftThreshold hH < r) (hlo : lo 0 < r) (hθ : θ ∈ Ioo 0 1) :
    ∃ k, lam k ∈ Ioc (shiftThreshold hH) r := by
  obtain ⟨k, -, hk⟩ := hrun.exists_mem hr hlo hθ.1 hθ.2
  exact ⟨k, hk⟩

/-- **Theorem 7.3.4** of [conn2000trust], multiplier convergence when safeguarding continues. Let
$\theta \in (0, 1)$ and $r \ge \lambda_s$. If $(\lambda^L_k, \lambda^U_k, \lambda_k)$ is a
bracketing run with pole $\lambda_s$ and target $r$, and no $\lambda_k$ lies in
$(\lambda_s, r]$, then $\lambda_k \to r$. -/
theorem moreSorensen_bracketing_tendsto {r θ : ℝ} {lo hi lam : ℕ → ℝ}
    (hrun : IsBracketRun (shiftThreshold hH) r θ θ lo hi lam)
    (hr : shiftThreshold hH ≤ r) (hθ : θ ∈ Ioo 0 1)
    (hnever : ∀ k, lam k ∉ Ioc (shiftThreshold hH) r) :
    Tendsto lam atTop (𝓝 r) :=
  (hrun.tendsto_bracket_of_never_mem hr hθ.1 hθ.2 hnever).2.2

/-- **Theorem 7.3.4** of [conn2000trust], the easy-case Newton phase. Let $g \neq 0$, $\Delta > 0$,
and let $r \ge 0$ with $r > -\lambda_1$ and $\|s(r)\|^2 = \Delta^2$. Let
$\lambda_0 > -\lambda_1$ with $\phi(\lambda_0) < 0$, and let $\lambda_k$ be the Newton iterates
from $\lambda_0$. Then $\lambda_k \to r$ with order $2$, $s(\lambda_k) \to s(r)$, and $s(r)$ is
a global minimizer of $q$ on the ball of radius $\Delta$, with $\|s(r)\| \le \Delta$. -/
theorem moreSorensen_easy_newton_convergence (hg : g ≠ 0) {Δ r x₀ : ℝ}
    (hΔ : 0 < Δ) (hr : -leftmost hH < r) (hr₀ : 0 ≤ r)
    (hroot : secular g H r = Δ ^ 2) (hx₀ : -leftmost hH < x₀) (hbelow : phi g H Δ x₀ < 0) :
    let x := fun k : ℕ => (moreSorensenNewtonStep g H Δ)^[k] x₀
    let sM := shiftedStep g H r
    ConvergesWithOrder x r 2 ∧ Tendsto (fun k => shiftedStep g H (x k)) atTop (𝓝 sM) ∧
      ‖sM‖ ≤ Δ ∧ IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) sM := by
  have hconv := (lemma_7_3_2 hg hΔ hr hroot hx₀ hbelow).2.2.2.2
  have hfun : stepDeriv g H 0 = shiftedStep g H := funext stepDeriv_zero
  have hcont : ContinuousAt (shiftedStep g H) r := by
    rw [← hfun]
    exact (hasDerivAt_stepDeriv (g := g) hr 0).continuousAt
  have hnorm : ‖shiftedStep g H r‖ = Δ := by
    change ‖shiftedStep g H r‖ ^ 2 = Δ ^ 2 at hroot
    nlinarith [norm_nonneg (shiftedStep g H r)]
  have hmul : IsTrustRegionMultiplier g H Δ (shiftedStep g H r) r :=
    ⟨hr₀, (step_spec hr).1, isPositive_add_smul_of_le hr.le, by simp [hnorm]⟩
  exact ⟨hconv, hcont.tendsto.comp hconv.tendsto, hnorm.le, hmul.isMinOn hH⟩

/-- **Theorem 7.3.4** of [conn2000trust], the safeguarded easy phase. Let $g \neq 0$, $\Delta > 0$,
$\theta \in (0, 1)$, and $r > \lambda_s$ with $\|s(r)\|^2 = \Delta^2$. Let
$(\lambda^L_k, \lambda^U_k, \lambda_k)$ be a bracketing run with pole $\lambda_s$ and target
$r$, with $\lambda^L_0 < r$. Then there is $k$ such that either $\lambda_k = r$, or the Newton
iterates from $\lambda_k$ converge to $r$ with order $2$ and their steps converge to $s(r)$. -/
theorem moreSorensen_easy_bracket_then_newton (hg : g ≠ 0) {Δ r θ : ℝ}
    {lo hi lam : ℕ → ℝ} (hΔ : 0 < Δ) (hr : shiftThreshold hH < r)
    (hroot : secular g H r = Δ ^ 2) (hlo : lo 0 < r) (hθ : θ ∈ Ioo 0 1)
    (hrun : IsBracketRun (shiftThreshold hH) r θ θ lo hi lam) :
    ∃ k, lam k = r ∨
      let x := fun j : ℕ => (moreSorensenNewtonStep g H Δ)^[j] (lam k)
      ConvergesWithOrder x r 2 ∧
        Tendsto (fun j => shiftedStep g H (x j)) atTop (𝓝 (shiftedStep g H r)) := by
  obtain ⟨k, hk⟩ := moreSorensen_bracketing_enters_newton hrun hr hlo hθ
  have ha : -leftmost hH < r := neg_leftmost_le_shiftThreshold.trans_lt hr
  refine ⟨k, ?_⟩
  rcases hk.2.lt_or_eq with hkr | hkr
  · have hx : -leftmost hH < lam k := neg_leftmost_le_shiftThreshold.trans_lt hk.1
    have hm := (trSecular_shape (hH := hH) hg Δ (β := -1 / 2) (by norm_num)).2.1
    have hbelow : phi g H Δ (lam k) < 0 := phi_root hΔ hroot ▸ hm hx ha hkr
    have h := moreSorensen_easy_newton_convergence hg hΔ ha
      (shiftThreshold_nonneg.trans hr.le) hroot hx hbelow
    exact Or.inr ⟨h.1, h.2.1⟩
  · exact Or.inl hkr

/-- **Theorem 7.3.4** of [conn2000trust], the actual recurrence in the easy case. Let $g \neq 0$,
$\Delta > 0$, $\theta \in (0, 1)$, and $r > -\lambda_1$ with $\|s(r)\|^2 = \Delta^2$. Let
$0 \le \lambda^L_0 \le r \le \lambda^U_0$, $\lambda_0 \in [\lambda^L_0, \lambda^U_0]$, and
$b_k \le -\lambda_1$ for all $k$, and let the triples follow the update with the pole
$-\lambda_1$. Then:

* $\lambda_k \to r$ with order $2$, and $s(\lambda_k) \to s(r)$;
* $s(r)$ is a global minimizer of $q$ on the ball of radius $\Delta$;
* there is $k$ with $\lambda_k \in (-\lambda_1, r]$, from which on the trial multipliers are the
  Newton iterates from $\lambda_k$.

So the recurrence enters the Newton interval in finite time, and its tail may reach $r$ exactly. -/
theorem moreSorensen_easy_safeguarded_run (hg : g ≠ 0)
    {Δ r θ : ℝ} {lo hi x b : ℕ → ℝ} (hΔ : 0 < Δ) (hθ : θ ∈ Ioo 0 1)
    (hr : -leftmost hH < r) (hroot : secular g H r = Δ ^ 2)
    (hlo : 0 ≤ lo 0) (hlr : lo 0 ≤ r) (hrh : r ≤ hi 0) (hx0 : x 0 ∈ Icc (lo 0) (hi 0))
    (hb : ∀ k, b k ≤ -leftmost hH)
    (hrec : ∀ k, (lo (k + 1), hi (k + 1), x (k + 1)) =
      moreSorensenSafeguardedStep g H (-leftmost hH) Δ θ (lo k) (hi k) (x k) (b k)) :
    ConvergesWithOrder x r 2 ∧
      Tendsto (fun k => shiftedStep g H (x k)) atTop (𝓝 (shiftedStep g H r)) ∧
      IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) (shiftedStep g H r) ∧
      ∃ k, x k ∈ Ioc (-leftmost hH) r ∧
        ∀ j, x (j + k) = (moreSorensenNewtonStep g H Δ)^[j] (x k) := by
  have hr₀ := hlo.trans hlr
  have hnorm : ‖shiftedStep g H r‖ = Δ := by
    change ‖shiftedStep g H r‖ ^ 2 = Δ ^ 2 at hroot
    nlinarith [norm_nonneg (shiftedStep g H r)]
  have hmul : IsTrustRegionMultiplier g H Δ (shiftedStep g H r) r :=
    ⟨hr₀, (step_spec hr).1, isPositive_add_smul_of_le hr.le, by simp [hnorm]⟩
  have hφ := phi_root hΔ hroot
  have hmono := (trSecular_shape (hH := hH) hg Δ (β := -1 / 2) (by norm_num)).2.1
  have hpos (y : ℝ) (hy : r < y) : 0 < phi g H Δ y := hφ ▸ hmono hr (hr.trans hy) hy
  let N := moreSorensenNewtonStep g H Δ
  have hfix : N r = r := by simp [N, moreSorensenNewtonStep, Newton.scalarStep, hφ]
  have hentry : ∃ k, x k ∈ Ioc (-leftmost hH) r := by
    by_contra! hnever
    obtain ⟨hrun, hfail⟩ := moreSorensen_nonzero_bracket_run hg hΔ hθ hnorm.le hmul hlo hlr
      hrh hx0 hb hpos hnever hrec
    have hxlim := (hrun.tendsto_bracket_of_never_mem hr.le hθ.1 hθ.2 hnever).2.2
    have hsmooth : ContDiffOn ℝ 2 (phi g H Δ) (Ioi (-leftmost hH)) :=
      (contDiffOn_secular_rpow (hH := hH) hg _).sub contDiffOn_const
    have hdiff := hsmooth.contDiffAt (isOpen_Ioi.mem_nhds hr)
    have hd := (trSecular_shape (hH := hH) hg Δ (β := -1 / 2) (by norm_num)).2.2 r hr
    have hcder : ContinuousAt (deriv (phi g H Δ)) r :=
      (hdiff.of_le (by norm_num)).continuousAt_deriv
    have hcN : ContinuousAt N r := continuousAt_id.sub (hdiff.continuousAt.div hcder hd.ne')
    have hNlim : Tendsto (fun k => N (x k)) atTop (𝓝 r) := hfix ▸ hcN.tendsto.comp hxlim
    obtain ⟨j, hj, hjN⟩ := ((hxlim.eventually (eventually_gt_nhds hr)).and
      (hNlim.eventually (eventually_gt_nhds hr))).exists
    have hxr : r < x j := lt_of_not_ge fun hx => hnever j ⟨hj, hx⟩
    exact hjN.not_ge (hfail j hxr)
  obtain ⟨k, hk⟩ := hentry
  let y := fun j : ℕ => N^[j] (x k)
  have hy : (∀ j, -leftmost hH < y j ∧ phi g H Δ (y j) ≤ 0) ∧
      ConvergesWithOrder y r 2 := by
    rcases hk.2.lt_or_eq with hlt | heq
    · have hneg : phi g H Δ (x k) < 0 := hφ ▸ hmono hk.1 hr hlt
      have h := lemma_7_3_2 hg hΔ hr hroot hk.1 hneg
      exact ⟨h.1, h.2.2.2.2⟩
    · have hconst (j : ℕ) : y j = r := by
        simp [y, heq, Function.iterate_fixed hfix]
      refine ⟨fun j => by rw [hconst j, hφ]; exact ⟨hr, le_rfl⟩, ?_⟩
      rw [show y = fun _ => r from funext hconst]
      exact ⟨tendsto_const_nhds, 1, one_pos, Eventually.of_forall fun _ => by simp⟩
  have htail (j : ℕ) : x (j + k) = y j := by
    induction j with
    | zero => simp [y]
    | succ j ih =>
      have hs := congrArg (fun t : ℝ × ℝ × ℝ => t.2.2) (hrec (j + k))
      rw [ih] at hs
      have hup : x (j + k + 1) = N (y j) := by
        simpa only [N, moreSorensenSafeguardedStep, moreSorensenSafeguardedStepBy,
          ite_eq_left (hy.1 j).1, ite_eq_right (norm_ne_zero_iff.mpr hg),
          ite_eq_right (not_lt.mpr (hy.1 j).2)] using hs
      rw [show j + 1 + k = j + k + 1 by omega, hup]
      exact (Function.iterate_succ_apply' N j (x k)).symm
  have hxlim : Tendsto x atTop (𝓝 r) :=
    (tendsto_add_atTop_iff_nat k).mp (by simpa only [htail] using hy.2.1)
  have horder : ConvergesWithOrder x r 2 := by
    obtain ⟨C, hC, hCev⟩ := hy.2.2
    obtain ⟨m, hm⟩ := eventually_atTop.mp hCev
    refine ⟨hxlim, C, hC, eventually_atTop.mpr ⟨m + k, fun i hi => ?_⟩⟩
    have he := hm (i - k) (by omega)
    rw [← htail, ← htail, show i - k + 1 + k = i + 1 by omega,
      show i - k + k = i by omega] at he
    exact he
  have hfun : stepDeriv g H 0 = shiftedStep g H := funext stepDeriv_zero
  have hcont : ContinuousAt (shiftedStep g H) r := by
    rw [← hfun]
    exact (hasDerivAt_stepDeriv (g := g) hr 0).continuousAt
  exact ⟨horder, hcont.tendsto.comp hxlim, hmul.isMinOn hH, k, hk, htail⟩

/-- **Theorem 7.3.4** of [conn2000trust], finite interior convergence. If $H$ is positive definite
($-\lambda_1 < 0$) and $\|s(0)\| \le \Delta$, then $s(0)$ lies in the ball of radius $\Delta$
and is a global minimizer of $q$ there. -/
theorem moreSorensen_interior_solution {Δ : ℝ} (hHpos : -leftmost hH < 0)
    (hs : ‖shiftedStep g H 0‖ ≤ Δ) :
    shiftedStep g H 0 ∈ Metric.closedBall 0 Δ ∧
      IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) (shiftedStep g H 0) := by
  have hmul : IsTrustRegionMultiplier g H Δ (shiftedStep g H 0) 0 :=
    ⟨le_rfl, (step_spec hHpos).1, isPositive_add_smul_of_le hHpos.le, zero_mul _⟩
  exact hmul.isMinOn_of_norm_le hH hs

/-- **Algorithm 7.3.4** of [conn2000trust], Step 1a, interior stopping for a positive semidefinite
Hessian. If $H$ is positive semidefinite ($-\lambda_1 \le 0$), $H s = -g$ and
$\|s\| \le \Delta$, then $s$ lies in the ball of radius $\Delta$ and is a global minimizer of
$q$ there.

The Hessian may be singular. -/
theorem moreSorensen_interior_solution_of_unshifted_solve {Δ : ℝ} {s : E}
    (hHpos : -leftmost hH ≤ 0) (hsolve : H s = -g) (hs : ‖s‖ ≤ Δ) :
    s ∈ Metric.closedBall 0 Δ ∧ IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) s := by
  have hmul : IsTrustRegionMultiplier g H Δ s 0 :=
    ⟨le_rfl, by simpa using hsolve, isPositive_add_smul_of_le hHpos, zero_mul _⟩
  exact hmul.isMinOn_of_norm_le hH hs

/-- **Theorem 7.3.4** of [conn2000trust], zero-gradient solution and multiplier. Let $g = 0$ and
$\Delta \ge 0$. Then there is $s$ with $\|s\| \le \Delta$ for which
$\lambda_s = \max\{0, -\lambda_1\}$ is an optimal multiplier.

If $H$ is positive semidefinite, $s = 0$. If $\lambda_1 < 0$, $s$ is $\Delta$ times a unit
eigenvector for $\lambda_1$, a boundary solution with multiplier equal to the pole. -/
theorem moreSorensen_zero_gradient_solution {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ∃ s : E, ‖s‖ ≤ Δ ∧ IsTrustRegionMultiplier (0 : E) H Δ s (shiftThreshold hH) := by
  by_cases hp : -leftmost hH ≤ 0
  · have ht : shiftThreshold hH = 0 := max_eq_left hp
    rw [ht]
    exact ⟨0, by simpa using hΔ, le_rfl, by simp, isPositive_add_smul_of_le hp, zero_mul _⟩
  · have hp' : 0 < -leftmost hH := lt_of_not_ge hp
    have ht : shiftThreshold hH = -leftmost hH := max_eq_right hp'.le
    rw [ht]
    rcases subsingleton_or_nontrivial E with hE | hE
    · rw [leftmost_eq_zero_of_subsingleton (hH := hH), neg_zero] at hp'
      exact (lt_irrefl _ hp').elim
    obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hH)
    let u : E := hH.eigenvectorBasis rfl i
    have hu : ‖u‖ = 1 := (hH.eigenvectorBasis rfl).orthonormal.norm_eq_one i
    have heig : H u = leftmost hH • u := by
      rw [← hi]
      exact hH.apply_eigenvectorBasis rfl i
    have hnorm : ‖Δ • u‖ = Δ := by simp [norm_smul, abs_of_nonneg hΔ, hu]
    have hsolve : (H + (-leftmost hH) • (1 : E →L[ℝ] E)) (Δ • u) = -(0 : E) := by
      simp [add_apply, smul_apply, one_apply_eq_self, map_smul, heig, neg_smul]
    exact ⟨Δ • u, hnorm.le, hp'.le, hsolve, isPositive_add_smul_of_le le_rfl, by simp [hnorm]⟩

/-- **Equation (7.3.16)** of [conn2000trust], with an exact leftmost eigenvector. Let $u$ be a unit
eigenvector of $H$ for $\lambda_1$, and let $\lambda_k \to -\lambda_1$. Then
$$\langle u, (H + \lambda_k I) u \rangle \to 0.$$

So an eigensolver gives directions with the vanishing shifted curvature of (7.3.16), as an
alternative to that property of the LINPACK heuristic. -/
theorem moreSorensen_exact_leftmost_curvature_tendsto {u : E} (hu : ‖u‖ = 1)
    (heig : H u = leftmost hH • u) {lam : ℕ → ℝ}
    (hlam : Tendsto lam atTop (𝓝 (-leftmost hH))) :
    Tendsto (fun k => ⟪u, (H + lam k • (1 : E →L[ℝ] E)) u⟫) atTop (𝓝 0) := by
  have heq (k : ℕ) : ⟪u, (H + lam k • (1 : E →L[ℝ] E)) u⟫ = lam k + leftmost hH := by
    simp only [add_apply, smul_apply, one_apply_eq_self, heig, inner_add_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow, mul_one]
    exact add_comm _ _
  simpa only [heq, neg_add_cancel] using hlam.add_const (leftmost hH)

/-- **Equation (7.3.16)** of [conn2000trust] and Theorem 7.3.4, boundary corrections. Let
$\lambda_k > -\lambda_1$ with $\|s(\lambda_k)\| \le \Delta$, let $u_k$ be unit vectors and
$\alpha_k$ numbers with $\|s(\lambda_k) + \alpha_k u_k\| = \Delta$, and suppose that $\langle
u_k, (H + \lambda_k I) u_k \rangle \to 0$. Then
$$\langle \alpha_k u_k, (H + \lambda_k I)(\alpha_k u_k) \rangle \to 0.$$

The coefficients satisfy $|\alpha_k| \le 2 \Delta$, because both the raw and the corrected steps
lie in the ball. -/
theorem moreSorensen_hard_correction_curvature_tendsto {Δ : ℝ}
    (lam α : ℕ → ℝ) (u : ℕ → E) (hlam : ∀ k, -leftmost hH < lam k)
    (hraw : ∀ k, ‖shiftedStep g H (lam k)‖ ≤ Δ) (hunit : ∀ k, ‖u k‖ = 1)
    (hboundary : ∀ k, ‖shiftedStep g H (lam k) + α k • u k‖ = Δ)
    (hcurv : Tendsto (fun k => ⟪u k, (H + lam k • (1 : E →L[ℝ] E)) (u k)⟫) atTop (𝓝 0)) :
    Tendsto (fun k => ⟪α k • u k, (H + lam k • (1 : E →L[ℝ] E)) (α k • u k)⟫)
      atTop (𝓝 0) := by
  let A := fun k => H + lam k • (1 : E →L[ℝ] E)
  have hpos (k : ℕ) (w : E) : 0 ≤ ⟪w, A k w⟫ :=
    ContinuousLinearMap.inner_apply_nonneg_of_isPositive
      (isPositive_add_smul_of_le (hlam k).le) w
  have halpha (k : ℕ) : |α k| ≤ 2 * Δ := calc
    _ = ‖α k • u k‖ := by rw [norm_smul, hunit, mul_one, Real.norm_eq_abs]
    _ = ‖(shiftedStep g H (lam k) + α k • u k) - shiftedStep g H (lam k)‖ := by
      rw [add_sub_cancel_left]
    _ ≤ _ := by
      have hn := norm_sub_le (shiftedStep g H (lam k) + α k • u k)
        (shiftedStep g H (lam k))
      rw [hboundary] at hn
      linarith [hraw k]
  have hbound (k : ℕ) : ⟪α k • u k, A k (α k • u k)⟫ ≤ (2 * Δ) ^ 2 * ⟪u k, A k (u k)⟫ := by
    rw [map_smul, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← sq]
    apply mul_le_mul_of_nonneg_right _ (hpos k _)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (halpha k) 2
  exact squeeze_zero (fun k => hpos k _) hbound
    (by simpa only [mul_zero] using hcurv.const_mul ((2 * Δ) ^ 2))

/-- **Theorem 7.3.4** of [conn2000trust], hard-case model values and cluster points. Let $s_M$ be a
global minimizer of $q$ on the ball of radius $\Delta$, with $\|s_M\| \le \Delta$. Let
$\lambda_k \ge 0$ with $\lambda_k > -\lambda_1$, and let $v_k$ satisfy
$\|s(\lambda_k) + v_k\| = \Delta$ and $\langle v_k, (H + \lambda_k I) v_k \rangle \to 0$. Let
$s_k = s(\lambda_k) + v_k$. Then:

* $q(s_k) \to q(s_M)$;
* every limit of a subsequence of $(s_k)$ lies in the ball and is a global minimizer of $q$
  there;
* if $s_M$ is the only global minimizer, then $s_k \to s_M$.

In the hard case, a single vector limit needs more control of the correction directions or a
unique minimizer. -/
theorem moreSorensen_hard_model_convergence {Δ : ℝ} {sM : E} (hsM : ‖sM‖ ≤ Δ)
    (hmin : IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) sM)
    (lam : ℕ → ℝ) (v : ℕ → E) (hlam₀ : ∀ k, 0 ≤ lam k)
    (hlam : ∀ k, -leftmost hH < lam k)
    (hboundary : ∀ k, ‖shiftedStep g H (lam k) + v k‖ = Δ)
    (hcurv : Tendsto (fun k => ⟪v k, (H + lam k • (1 : E →L[ℝ] E)) (v k)⟫) atTop (𝓝 0)) :
    let s := fun k => shiftedStep g H (lam k) + v k
    Tendsto (fun k => quadModel g H (s k)) atTop (𝓝 (quadModel g H sM)) ∧
      (∀ (j : ℕ → ℕ) (u : E), Tendsto j atTop atTop →
        Tendsto (s ∘ j) atTop (𝓝 u) →
        u ∈ Metric.closedBall 0 Δ ∧ IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) u) ∧
      ((∀ u ∈ Metric.closedBall 0 Δ,
        IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) u → u = sM) →
        Tendsto s atTop (𝓝 sM)) := by
  let s := fun k => shiftedStep g H (lam k) + v k
  have hfeas (k : ℕ) : s k ∈ Metric.closedBall 0 Δ :=
    mem_closedBall_zero_iff.mpr (hboundary k).le
  have hgap (k : ℕ) : quadModel g H (s k) - quadModel g H sM ≤
      (1 / 2) * ⟪v k, (H + lam k • (1 : E →L[ℝ] E)) (v k)⟫ := by
    have hs := (step_spec (g := g) (hlam k)).1
    have hlow := quadModel_lower_bound_of_shifted (hH := hH) (hlam₀ k) (hlam k) hs hsM
    have heq := quadModel_eq_of_shifted_comparison hH hs (s k)
    have hdiff : s k - shiftedStep g H (lam k) = v k := by dsimp [s]; abel
    rw [show step g H (lam k) = shiftedStep g H (lam k) from rfl, hdiff, hboundary k] at heq
    linarith only [hlow, heq]
  have ht : Tendsto (fun k => quadModel g H (s k) - quadModel g H sM) atTop (𝓝 0) :=
    squeeze_zero (fun k => sub_nonneg.mpr ((isMinOn_iff.mp hmin) _ (hfeas k))) hgap
      (by simpa only [mul_zero] using hcurv.const_mul (1 / 2))
  have hval : Tendsto (fun k => quadModel g H (s k)) atTop (𝓝 (quadModel g H sM)) := by
    simpa only [sub_add_cancel, zero_add] using ht.add_const (quadModel g H sM)
  have hcluster (j : ℕ → ℕ) (u : E) (hj : Tendsto j atTop atTop)
      (hu : Tendsto (s ∘ j) atTop (𝓝 u)) :
      u ∈ Metric.closedBall 0 Δ ∧ IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) u := by
    refine ⟨Metric.isClosed_closedBall.mem_of_tendsto hu
      (Eventually.of_forall fun k => hfeas (j k)), ?_⟩
    have hq : quadModel g H u = quadModel g H sM :=
      tendsto_nhds_unique ((continuous_quadModel g H).continuousAt.tendsto.comp hu) (hval.comp hj)
    rw [isMinOn_iff]
    intro x hx
    rw [hq]
    exact (isMinOn_iff.mp hmin) x hx
  refine ⟨hval, hcluster, fun hunique => ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  by_contra hbad
  have hfreq : ∃ᶠ k in atTop, ¬ dist (s k) sM < ε := by
    simpa only [Filter.Frequently, not_not] using hbad
  have hin : ∃ᶠ k in atTop, s k ∈ Metric.closedBall 0 Δ ∩ (Metric.ball sM ε)ᶜ :=
    hfreq.mono fun k hk => ⟨hfeas k, hk⟩
  obtain ⟨u, hu, j, hj, hju⟩ :=
    ((isCompact_closedBall (0 : E) Δ).inter_right
      Metric.isOpen_ball.isClosed_compl).tendsto_subseq' hin
  obtain ⟨huf, hum⟩ := hcluster j u hj.tendsto_atTop hju
  have heq : u = sM := hunique u huf hum
  exact hu.2 (by simpa [heq, Metric.mem_ball] using hε)

/-- **Theorem 7.3.4** of [conn2000trust], positive definite subsequence. Let $\theta \in (0, 1)$. If
$(\lambda^L_k, \lambda^U_k, \lambda_k)$ is a bracketing run with pole and target $-\lambda_1$
and $\lambda^U_0 > -\lambda_1$, then $\lambda_k > -\lambda_1$ for infinitely many $k$: there is
a sequence $k_j \to \infty$ with $\lambda_{k_j} > -\lambda_1$. -/
theorem moreSorensen_hard_bracketing_subsequence {θ : ℝ} {lo hi lam : ℕ → ℝ}
    (hθ : θ ∈ Ioo 0 1) (hrun : IsBracketRun (-leftmost hH) (-leftmost hH) θ θ lo hi lam)
    (hhi : -leftmost hH < hi 0) :
    ∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧ ∀ k, -leftmost hH < lam (j k) :=
  exists_seq_forall_of_frequently (hrun.frequently_gt_of_eq rfl hhi hθ.1 hθ.2)

/-- **Theorem 7.3.4** of [conn2000trust], the actual recurrence in the hard case. Let $g \neq 0$,
$\Delta > 0$, $\theta \in (0, 1)$, and suppose that $-\lambda_1$ is an optimal multiplier for a
global minimizer $s_M$ with $\|s_M\| \le \Delta$. Let $0 \le \lambda^L_0 \le -\lambda_1 \le
\lambda^U_0$, $\lambda_0 \in [\lambda^L_0, \lambda^U_0]$, and $b_k \le -\lambda_1$ for all $k$,
and let the triples follow the update with the pole $-\lambda_1$. Then they form a bracketing
run with pole and target $-\lambda_1$, and $\lambda_k \to -\lambda_1$.

Every trial above the pole has a positive secular value and a Newton candidate that fails the
factorization test, so the recurrence stays in the bracketing phase. -/
theorem moreSorensen_hard_safeguarded_run (hg : g ≠ 0)
    {Δ θ : ℝ} {sM : E} {lo hi x b : ℕ → ℝ} (hΔ : 0 < Δ) (hθ : θ ∈ Ioo 0 1)
    (hsM : ‖sM‖ ≤ Δ) (hmul : IsTrustRegionMultiplier g H Δ sM (-leftmost hH))
    (hlo : 0 ≤ lo 0) (hlr : lo 0 ≤ -leftmost hH) (hrh : -leftmost hH ≤ hi 0)
    (hx0 : x 0 ∈ Icc (lo 0) (hi 0)) (hb : ∀ k, b k ≤ -leftmost hH)
    (hrec : ∀ k, (lo (k + 1), hi (k + 1), x (k + 1)) =
      moreSorensenSafeguardedStep g H (-leftmost hH) Δ θ (lo k) (hi k) (x k) (b k)) :
    IsBracketRun (-leftmost hH) (-leftmost hH) θ θ lo hi x ∧
      Tendsto x atTop (𝓝 (-leftmost hH)) := by
  have hpos (y : ℝ) (hy : -leftmost hH < y) : 0 < phi g H Δ y := by
    have hsq := (secular_lt_norm_sq_of_shifted (hH := hH) hg le_rfl hmul.shifted hy).trans_le
      (pow_le_pow_left₀ (norm_nonneg sM) hsM 2)
    have hnorm : ‖shiftedStep g H y‖ < Δ :=
      (pow_lt_pow_iff_left₀ (norm_nonneg _) hΔ.le two_ne_zero).mp hsq
    have hnpos : 0 < ‖shiftedStep g H y‖ := by
      have hp := secular_pos (hH := hH) hg hy
      rw [secular] at hp
      exact norm_pos_iff.2 fun h => by simp [h] at hp
    rw [phi_eq_inv_norm_sub_inv]
    exact sub_pos.mpr (one_div_lt_one_div_of_lt hnpos hnorm)
  have hnever (k : ℕ) : x k ∉ Ioc (-leftmost hH) (-leftmost hH) := fun hk => hk.1.not_ge hk.2
  obtain ⟨hrun, -⟩ := moreSorensen_nonzero_bracket_run hg hΔ hθ hsM hmul hlo hlr hrh hx0
    hb hpos hnever hrec
  exact ⟨hrun, (hrun.tendsto_bracket_of_never_mem le_rfl hθ.1 hθ.2 hnever).2.2⟩

/-- **Theorem 7.3.4** of [conn2000trust], multiplier alternatives for a nonzero gradient. Let
$g \neq 0$, $\Delta > 0$, $\theta \in (0, 1)$, and let $r$ be an optimal multiplier for a global
minimizer $s_M$ with $\|s_M\| \le \Delta$. Let $0 \le \lambda^L_0 \le r \le \lambda^U_0$,
$\lambda_0 \in [\lambda^L_0, \lambda^U_0]$, and $b_k \le -\lambda_1$ for all $k$, and let the
triples follow the update with the pole $-\lambda_1$. Then one of the following holds:

* $r = 0$, and the minimum-norm solution $s_0$ of $H s = -g$ lies in the ball and is a global
  minimizer of $q$ there;
* $r > 0$, $r > -\lambda_1$ (the easy case), $\lambda_k \to r$ with order $2$, and
  $s(\lambda_k) \to s_M$;
* $r > 0$ and $r = -\lambda_1$ (the hard case), the triples form a bracketing run with pole and
  target $r$, and $\lambda_k \to r$.

The first case includes a singular positive semidefinite $H$, and the solution there is
`Subproblem.particular hH g 0`. The vector conclusions in the hard case are in
`ConnGouldToint.Chapter07.moreSorensen_hard_safeguarded_corrections`. -/
theorem theorem_7_3_4_nonzero_gradient (hg : g ≠ 0)
    {Δ r θ : ℝ} {sM : E} {lo hi x b : ℕ → ℝ} (hΔ : 0 < Δ) (hθ : θ ∈ Ioo 0 1)
    (hsM : ‖sM‖ ≤ Δ) (hmul : IsTrustRegionMultiplier g H Δ sM r)
    (hlo : 0 ≤ lo 0) (hlr : lo 0 ≤ r) (hrh : r ≤ hi 0)
    (hx0 : x 0 ∈ Icc (lo 0) (hi 0)) (hb : ∀ k, b k ≤ -leftmost hH)
    (hrec : ∀ k, (lo (k + 1), hi (k + 1), x (k + 1)) =
      moreSorensenSafeguardedStep g H (-leftmost hH) Δ θ (lo k) (hi k) (x k) (b k)) :
    (r = 0 ∧ H (particular hH g 0) = -g ∧
      particular hH g 0 ∈ Metric.closedBall 0 Δ ∧
      IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) (particular hH g 0)) ∨
    (0 < r ∧ -leftmost hH < r ∧ ConvergesWithOrder x r 2 ∧
      Tendsto (fun k => shiftedStep g H (x k)) atTop (𝓝 sM)) ∨
    (0 < r ∧ r = -leftmost hH ∧ IsBracketRun r r θ θ lo hi x ∧ Tendsto x atTop (𝓝 r)) := by
  have hpr : -leftmost hH ≤ r := neg_leftmost_le_shiftThreshold.trans
    (shiftThreshold_le_of_isPositive (hH := hH) hmul.nonneg hmul.isPositive)
  rcases hmul.nonneg.eq_or_lt with hz | hr
  · subst r
    obtain ⟨hgker, -, -, hn, -⟩ := particular_add_of_shifted (hH := hH) hmul.shifted
    have hsolve : H (particular hH g 0) = -g := by
      simpa using ((particular_spec (hH := hH) (g := g) 0).2.1 hgker).1
    exact Or.inl ⟨rfl, hsolve, moreSorensen_interior_solution_of_unshifted_solve
      hpr hsolve (hn.trans hsM)⟩
  rcases hpr.lt_or_eq with hp | hp
  · have hstep : sM = shiftedStep g H r := (step_spec hp).2 sM hmul.shifted
    have hn := hmul.eq_zero_or_norm_eq.resolve_left hr.ne'
    have hroot : secular g H r = Δ ^ 2 := by
      change ‖shiftedStep g H r‖ ^ 2 = Δ ^ 2
      rw [← hstep, hn]
    obtain ⟨horder, ht, -, -⟩ := moreSorensen_easy_safeguarded_run hg hΔ hθ hp hroot hlo hlr
      hrh hx0 hb hrec
    exact Or.inr (Or.inl ⟨hr, hp, horder, by simpa only [hstep] using ht⟩)
  · subst r
    exact Or.inr (Or.inr ⟨hr, rfl,
      moreSorensen_hard_safeguarded_run hg hΔ hθ hsM hmul hlo hlr hrh hx0 hb hrec⟩)

/-- **Theorem 7.3.4** of [conn2000trust], corrected hard-case steps for varying directions. Let the
hypotheses of `ConnGouldToint.Chapter07.moreSorensen_hard_safeguarded_run` hold with
$\lambda^U_0 > -\lambda_1$. For each $k$ with $\lambda_k > -\lambda_1$, let $u_k$ be a unit
vector and $\alpha_k$ a number with $\|s(\lambda_k) + \alpha_k u_k\| = \Delta$, and suppose that
$\langle u_k, (H + \lambda_k I) u_k \rangle \to 0$ along these $k$. Then
$\lambda_k \to -\lambda_1$, there are infinitely many $k$ with $\lambda_k > -\lambda_1$, and
along every sequence $k_j \to \infty$ of such indices the corrected steps
$s_j = s(\lambda_{k_j}) + \alpha_{k_j} u_{k_j}$ satisfy:

* $q(s_j) \to q(s_M)$;
* every limit of a subsequence of $(s_j)$ lies in the ball and is a global minimizer of $q$
  there;
* if $s_M$ is the only global minimizer, then $s_j \to s_M$.

The indices with $\lambda_k > -\lambda_1$ are the successful factorizations. Both roots of the
boundary equation are allowed for $\alpha_k$. -/
theorem moreSorensen_hard_safeguarded_corrections (hg : g ≠ 0)
    {Δ θ : ℝ} {sM : E} {lo hi x b α : ℕ → ℝ} {u : ℕ → E}
    (hΔ : 0 < Δ) (hθ : θ ∈ Ioo 0 1)
    (hsM : ‖sM‖ ≤ Δ) (hmul : IsTrustRegionMultiplier g H Δ sM (-leftmost hH))
    (hlo : 0 ≤ lo 0) (hlr : lo 0 ≤ -leftmost hH) (hhi : -leftmost hH < hi 0)
    (hx0 : x 0 ∈ Icc (lo 0) (hi 0)) (hb : ∀ k, b k ≤ -leftmost hH)
    (hrec : ∀ k, (lo (k + 1), hi (k + 1), x (k + 1)) =
      moreSorensenSafeguardedStep g H (-leftmost hH) Δ θ (lo k) (hi k) (x k) (b k))
    (hu : ∀ k, -leftmost hH < x k → ‖u k‖ = 1)
    (hboundary : ∀ k, -leftmost hH < x k → ‖shiftedStep g H (x k) + α k • u k‖ = Δ)
    (hcurv : Tendsto (fun k => ⟪u k, (H + x k • (1 : E →L[ℝ] E)) (u k)⟫)
      (atTop ⊓ 𝓟 {k | -leftmost hH < x k}) (𝓝 0)) :
    Tendsto x atTop (𝓝 (-leftmost hH)) ∧
      (∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧ ∀ k, -leftmost hH < x (j k)) ∧
      ∀ (j : ℕ → ℕ), Tendsto j atTop atTop → (∀ k, -leftmost hH < x (j k)) →
        let s := fun k => shiftedStep g H (x (j k)) + α (j k) • u (j k)
        Tendsto (fun k => quadModel g H (s k)) atTop (𝓝 (quadModel g H sM)) ∧
          (∀ (l : ℕ → ℕ) (w : E), Tendsto l atTop atTop → Tendsto (s ∘ l) atTop (𝓝 w) →
            w ∈ Metric.closedBall 0 Δ ∧ IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) w) ∧
          ((∀ w ∈ Metric.closedBall 0 Δ,
            IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) w → w = sM) →
            Tendsto s atTop (𝓝 sM)) := by
  obtain ⟨hrun, hxlim⟩ := moreSorensen_hard_safeguarded_run hg hΔ hθ hsM hmul hlo hlr hhi.le
    hx0 hb hrec
  refine ⟨hxlim, moreSorensen_hard_bracketing_subsequence hθ hrun hhi, fun j hj hjp => ?_⟩
  have hraw (k : ℕ) : ‖shiftedStep g H (x (j k))‖ ≤ Δ := by
    have hs := (secular_lt_norm_sq_of_shifted (hH := hH) hg le_rfl hmul.shifted (hjp k)).le
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hΔ.le two_ne_zero).mp
      (hs.trans (pow_le_pow_left₀ (norm_nonneg sM) hsM 2))
  have hj' : Tendsto j atTop (atTop ⊓ 𝓟 {k | -leftmost hH < x k}) :=
    tendsto_inf.2 ⟨hj, tendsto_principal.mpr (Eventually.of_forall hjp)⟩
  have hvc := moreSorensen_hard_correction_curvature_tendsto (x ∘ j) (α ∘ j) (u ∘ j)
    hjp hraw (fun k => hu (j k) (hjp k)) (fun k => hboundary (j k) (hjp k)) (hcurv.comp hj')
  have hmodel := moreSorensen_hard_model_convergence (hH := hH) hsM (hmul.isMinOn hH)
    (x ∘ j) (fun k => α (j k) • u (j k)) (fun k => hmul.nonneg.trans (hjp k).le)
    hjp (fun k => hboundary (j k) (hjp k)) hvc
  exact hmodel

/-- **Algorithm 7.3.4** of [conn2000trust], Step 3b(iii), the boundary equation. For
$\Delta \in \mathbb{R}$, a step $s$ and a unit direction $u$, the **boundary coefficient** is
the root
$$\alpha = \sqrt{\Delta^2 - \|s\|^2 + \langle s, u \rangle^2} - \langle s, u \rangle$$
of $\|s + \alpha u\| = \Delta$.

The real square root is $0$ for a negative argument. Fixing this root makes the correction
depend continuously on $s$ and $u$. -/
noncomputable def moreSorensenBoundaryCoefficient (Δ : ℝ) (s u : E) : ℝ :=
  √(Δ ^ 2 - ‖s‖ ^ 2 + ⟪s, u⟫ ^ 2) - ⟪s, u⟫

omit [FiniteDimensional ℝ E] in
/-- **Algorithm 7.3.4** of [conn2000trust], Step 3b(iii). If $\|s\| \le \Delta$ and $\|u\| = 1$,
then the boundary coefficient $\alpha$ satisfies $\|s + \alpha u\| = \Delta$. -/
theorem norm_add_boundaryCorrection {Δ : ℝ} {s u : E} (hs : ‖s‖ ≤ Δ) (hu : ‖u‖ = 1) :
    ‖s + moreSorensenBoundaryCoefficient Δ s u • u‖ = Δ := by
  let c := ⟪s, u⟫
  let d := √(Δ ^ 2 - ‖s‖ ^ 2 + c ^ 2)
  have hsq := pow_le_pow_left₀ (norm_nonneg s) hs 2
  have hd : d ^ 2 = Δ ^ 2 - ‖s‖ ^ 2 + c ^ 2 :=
    Real.sq_sqrt (add_nonneg (sub_nonneg.mpr hsq) (sq_nonneg _))
  change ‖s + (d - c) • u‖ = Δ
  have heq : ‖s + (d - c) • u‖ ^ 2 = Δ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs]
    change ‖s‖ ^ 2 + 2 * ((d - c) * c) + (d - c) ^ 2 = Δ ^ 2
    nlinarith only [hd]
  have hΔ := (norm_nonneg s).trans hs
  simpa only [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hΔ] using
    (sq_eq_sq_iff_abs_eq_abs _ _).mp heq

omit [FiniteDimensional ℝ E] in
/-- **Algorithm 7.3.4** of [conn2000trust], Step 3b(iii), the two boundary roots can tie. Let $H$ be
symmetric, $(H + \mu I) s = -g$ with $\|s\| < \Delta$, and let $u$ be a unit vector with
$\langle s, u \rangle = 0$. Then there is $\alpha > 0$ with
$$\|s + \alpha u\| = \|s - \alpha u\| = \Delta, \qquad s + \alpha u \neq s - \alpha u, \qquad
  q(s + \alpha u) = q(s - \alpha u).$$

So the rule to choose the root with the smaller model value needs a tie convention to select a
single step. -/
theorem moreSorensen_boundary_correction_tie {Δ μ : ℝ} {s u : E}
    (hH' : (H : E →ₗ[ℝ] E).IsSymmetric)
    (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) (hraw : ‖s‖ < Δ)
    (hu : ‖u‖ = 1) (hortho : ⟪s, u⟫ = 0) :
    ∃ α : ℝ, 0 < α ∧ ‖s + α • u‖ = Δ ∧ ‖s - α • u‖ = Δ ∧
      s + α • u ≠ s - α • u ∧ quadModel g H (s + α • u) = quadModel g H (s - α • u) := by
  let α := √(Δ ^ 2 - ‖s‖ ^ 2)
  have hα : 0 < α :=
    Real.sqrt_pos.2 (sub_pos.mpr (pow_lt_pow_left₀ hraw (norm_nonneg s) two_ne_zero))
  have hp : ‖s + α • u‖ = Δ := by
    simpa [moreSorensenBoundaryCoefficient, hortho, α] using norm_add_boundaryCorrection hraw.le hu
  have hm : ‖s - α • u‖ = Δ := by
    simpa [moreSorensenBoundaryCoefficient, hortho, α, sub_eq_add_neg, smul_neg] using
      norm_add_boundaryCorrection (u := -u) hraw.le (by simpa using hu)
  have hne : s + α • u ≠ s - α • u := by
    intro he
    have hu' : u ≠ 0 := by intro hz; simp [hz] at hu
    have hh := congrArg (fun v => v - s) he
    simp only [add_sub_cancel_left, show ∀ v : E, s - v - s = -v by intro v; abel] at hh
    have hzero : (2 * α) • u = 0 := by
      rw [two_mul, add_smul]
      exact eq_neg_iff_add_eq_zero.mp hh
    exact hu' ((smul_eq_zero.mp hzero).resolve_left (mul_pos two_pos hα).ne')
  have heqp := quadModel_eq_of_shifted_comparison hH' hs (s + α • u)
  have heqm := quadModel_eq_of_shifted_comparison hH' hs (s - α • u)
  rw [add_sub_cancel_left, hp] at heqp
  rw [show s - α • u - s = -(α • u) by abel, hm, map_neg, inner_neg_neg] at heqm
  exact ⟨α, hα, hp, hm, hne, heqp.trans heqm.symm⟩

/-- **Theorem 7.3.4** of [conn2000trust], corrected hard phase with an exact leftmost eigenvector.
Let $g \neq 0$, $\theta \in (0, 1)$, and suppose that $-\lambda_1$ is an optimal multiplier for
a global minimizer $s_M$ with $\|s_M\| \le \Delta$. Let $(\lambda^L_k, \lambda^U_k, \lambda_k)$
be a bracketing run with pole and target $-\lambda_1$ and $\lambda^U_0 > -\lambda_1$, and let
$u$ be a unit eigenvector of $H$ for $\lambda_1$. Then $\lambda_k \to -\lambda_1$, and there is
a sequence $k_j \to \infty$ with $\lambda_{k_j} > -\lambda_1$ such that the corrected steps
$s_j = s(\lambda_{k_j}) + \alpha_j u$, with $\alpha_j$ the boundary coefficient of
$s(\lambda_{k_j})$ and $u$, satisfy:

* $\|s_j\| = \Delta$ for all $j$;
* $q(s_j) \to q(s_M)$;
* $s_j \to w$ for some $w$ in the ball that is a global minimizer of $q$ there.

**Correction.** In the hard case the corrected steps of Algorithm 7.3.4 need not converge to a
single vector: the directions may vary, and the two roots of the boundary equation can tie. The
statement uses a fixed unit leftmost eigenvector and the fixed root
`ConnGouldToint.Chapter07.moreSorensenBoundaryCoefficient`, which give a vector limit.

The correction uses exact spectral data in place of the LINPACK direction heuristic of Section
7.3.7. -/
theorem moreSorensen_hard_bracket_then_exact_correction (hg : g ≠ 0)
    {Δ θ : ℝ} {sM : E} {lo hi lam : ℕ → ℝ} (hθ : θ ∈ Ioo 0 1)
    (hrun : IsBracketRun (-leftmost hH) (-leftmost hH) θ θ lo hi lam)
    (hsM : ‖sM‖ ≤ Δ) (hmul : IsTrustRegionMultiplier g H Δ sM (-leftmost hH))
    (hhi : -leftmost hH < hi 0) {u : E} (hu : ‖u‖ = 1) (heig : H u = leftmost hH • u) :
    Tendsto lam atTop (𝓝 (-leftmost hH)) ∧
    ∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧
      (∀ k, -leftmost hH < lam (j k)) ∧
      let α := fun k => moreSorensenBoundaryCoefficient Δ (shiftedStep g H (lam (j k))) u
      let s := fun k => shiftedStep g H (lam (j k)) + α k • u
      (∀ k, ‖s k‖ = Δ) ∧
      Tendsto (fun k => quadModel g H (s k)) atTop (𝓝 (quadModel g H sM)) ∧
      ∃ w : E, Tendsto s atTop (𝓝 w) ∧ w ∈ Metric.closedBall 0 Δ ∧
        IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) w := by
  have hlim := (hrun.tendsto_bracket_of_never_mem le_rfl hθ.1 hθ.2 (fun k => by simp)).2.2
  obtain ⟨j, hj, hpos⟩ := moreSorensen_hard_bracketing_subsequence hθ hrun hhi
  have hraw (k : ℕ) : ‖shiftedStep g H (lam (j k))‖ ≤ Δ := by
    have hs := (secular_lt_norm_sq_of_shifted (hH := hH) hg le_rfl hmul.shifted (hpos k)).le
    have hΔ : 0 ≤ Δ := (norm_nonneg sM).trans hsM
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hΔ two_ne_zero).mp
      (hs.trans (pow_le_pow_left₀ (norm_nonneg sM) hsM 2))
  let α := fun k => moreSorensenBoundaryCoefficient Δ (shiftedStep g H (lam (j k))) u
  have hboundary (k : ℕ) : ‖shiftedStep g H (lam (j k)) + α k • u‖ = Δ :=
    norm_add_boundaryCorrection (hraw k) hu
  have hcurv := moreSorensen_exact_leftmost_curvature_tendsto hu heig (hlim.comp hj)
  have hvc := moreSorensen_hard_correction_curvature_tendsto
    (lam ∘ j) α (fun _ => u) hpos hraw (fun _ => hu) hboundary hcurv
  have h := moreSorensen_hard_model_convergence (hH := hH) hsM (hmul.isMinOn hH)
    (lam ∘ j) (fun k => α k • u) (fun k => hmul.nonneg.trans (hpos k).le) hpos hboundary hvc
  let p := particular hH g (-leftmost hH)
  have hgorth := (particular_add_of_shifted (hH := hH) hmul.shifted).1
  have hright : Tendsto (lam ∘ j) atTop (𝓝[>] (-leftmost hH)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim.comp hj, Eventually.of_forall hpos⟩
  have hp : Tendsto (fun k => shiftedStep g H (lam (j k))) atTop (𝓝 p) :=
    ((tendsto_step_threshold (hH := hH)).1 hgorth).1.comp hright
  have hcont : Continuous (fun s : E => moreSorensenBoundaryCoefficient Δ s u) := by
    unfold moreSorensenBoundaryCoefficient
    fun_prop
  let w := p + moreSorensenBoundaryCoefficient Δ p u • u
  have hw : Tendsto (fun k => shiftedStep g H (lam (j k)) + α k • u) atTop (𝓝 w) :=
    hp.add ((hcont.continuousAt.tendsto.comp hp).smul tendsto_const_nhds)
  refine ⟨hlim, j, hj, hpos, hboundary, h.1, w, hw, ?_⟩
  exact h.2.1 id w tendsto_id hw

end ConnGouldToint.Chapter07
