/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter14.Section02
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Numlib.Optimization.Subproblem.Secular

/-!
# Conn, Gould and Toint, Section 14.3: Quadratic penalty convergence

This module formalizes the convergence analysis of the quadratic penalty method in [conn2000trust],
Section 14.3, for the problem of minimizing $f(x)$ subject to $c(x) = 0$. Algorithm 14.3.1
approximately minimizes the penalty function $\Phi(x, y, \mu) = f(x) - \langle y, c(x) \rangle +
\|c(x)\|^2 / (2\mu)$ with a fixed $y$ for penalty parameters $\mu_k \to 0$, up to tolerances
$\omega_k \to 0$ on the gradient. Theorem 14.3.1 shows that a convergent sequence of such
approximate minimizers has a feasible stationary limit, that the first-order multiplier estimates
converge to the least-squares multiplier, and that the errors are of order $\omega_k + \mu_k$ at a
nonsingular KKT point. The proofs specialize Lemma 14.2.2 to a constant multiplier.

Lemma 14.3.2 describes the spectrum of the penalty Hessian $\nabla_{xx} \Phi = \nabla_{xx} \ell(x,
y^F(x)) + \mu^{-1} A^* A$, with $A = c'(x)$, as $\mu \to 0$: after scaling by $\mu$, its extreme
eigenvalues tend to those of $A^* A$, and its least eigenvalue tends to that of the Hessian
restricted to the kernel of $A$. Both statements need a bounded Lagrangian Hessian term, which holds
at a feasible point but can fail elsewhere.

## Main definitions

* Algorithm 14.3.1, `ConnGouldToint.Chapter14.QuadraticPenaltyRun`: a run of the quadratic penalty
  method.
* Algorithm 14.3.1, Step 1, `ConnGouldToint.Chapter14.QuadraticPenaltyRun.multiplier`: the
  multiplier estimate of the run.
* Lemma 14.3.2(i), `ConnGouldToint.Chapter14.reducedPenaltyHessian`: the compression of a Hessian to
  the kernel of the constraint derivative.

## Main results

* Theorem 14.3.1(i)–(ii), `ConnGouldToint.Chapter14.theorem_14_3_1`: the limit is a KKT point, the
  multiplier estimates converge, and the errors satisfy the bounds (14.3.3)–(14.3.4).
* Theorem 14.3.1(iii), `ConnGouldToint.Chapter14.theorem_14_3_1_iii`: the estimates
  (14.3.5)–(14.3.6) at a nonsingular KKT point.
* Equation (14.3.9), `ConnGouldToint.Chapter14.fderiv_gradient_augmentedLagrangian_eq`: the Hessian
  of the penalty function.
* Equations (14.3.13)–(14.3.14), `ConnGouldToint.Chapter14.penalty_system_iff`: the penalty Newton
  system and the equivalent augmented system.
* Equation (14.3.15), `ConnGouldToint.Chapter14.gradient_augmentedLagrangian_change_parameter`: the
  change of the gradient when the penalty parameter changes.
* Lemma 14.3.2(i), `ConnGouldToint.Chapter14.lemma_14_3_2_i` and
  `ConnGouldToint.Chapter14.lemma_14_3_2_i_of_feasible`: the least eigenvalue tends to the least
  eigenvalue of the reduced Hessian.
* Lemma 14.3.2(ii)–(iii), `ConnGouldToint.Chapter14.lemma_14_3_2_scaled_extremes`,
  `ConnGouldToint.Chapter14.lemma_14_3_2_scaled_limits` and
  `ConnGouldToint.Chapter14.lemma_14_3_2_scaled_limits_of_feasible`: the scaled extreme eigenvalues
  tend to those of $A^* A$.
* Lemma 14.3.2(ii)–(iii), `ConnGouldToint.Chapter14.lemma_14_3_2_infeasible_counterexample`: at an
  infeasible point, the scaled Hessian need not tend to $A^* A$.
* Lemma 14.3.2(iv), `ConnGouldToint.Chapter14.lemma_14_3_2_iv`: without constraints the penalty
  Hessian is the objective Hessian.

## Implementation notes

* Eigenvalues are those of symmetric operators on a finite-dimensional real inner product space:
  `Subproblem.leftmost` and `Subproblem.rightmost` are the least and the greatest eigenvalue.

## Deviations from the source

* **Equation (14.3.15)** (correction). The scaling factor of the constraint term is $\mu / \nu - 1$.
  See `ConnGouldToint.Chapter14.gradient_augmentedLagrangian_change_parameter`.
* **Lemma 14.3.2(i)** (correction). The limit is stated for a fixed Lagrangian Hessian, compressed
  to the entire kernel of the constraint derivative. At a feasible point this Hessian is the one in
  the penalty Hessian. See `ConnGouldToint.Chapter14.lemma_14_3_2_i` and
  `ConnGouldToint.Chapter14.lemma_14_3_2_i_of_feasible`.
* **Lemma 14.3.2(ii)–(iii)** (correction). At an infeasible point the Lagrangian Hessian term can
  grow like $1/\mu$, and the printed limits fail. The corrected estimates bound that term
  explicitly. See `ConnGouldToint.Chapter14.lemma_14_3_2_scaled_extremes` and
  `ConnGouldToint.Chapter14.lemma_14_3_2_infeasible_counterexample`.
-/

open Filter Topology
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter14

variable {G F : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **Algorithm 14.3.1** of [conn2000trust], (14.3.1)–(14.3.2). A run of the quadratic penalty
method with fixed multiplier $y$ consists of starting points for the inner solves, iterates
$x_k$, penalty parameters $\mu_k > 0$ with $\mu_k \to 0$ and tolerances $\omega_k \to 0$, such
that
$$\|\nabla_x \Phi(x_k, y, \mu_k)\| \le \omega_k$$
for all $k$.

The run supplies the starting points, the iterates and the tolerances; it does not model the
inner solver. -/
structure QuadraticPenaltyRun (f : G → ℝ) (c : G → F) (y : F) where
  /-- The starting points of the inner solves. -/
  start : ℕ → G
  /-- The iterates $x_k$, the approximate minimizers of the inner solves. -/
  iterate : ℕ → G
  /-- The penalty parameters $\mu_k$. -/
  parameter : ℕ → ℝ
  /-- The tolerances $\omega_k$ of the inner solves. -/
  tolerance : ℕ → ℝ
  /-- Every penalty parameter is positive. -/
  parameter_pos : ∀ k, 0 < parameter k
  /-- The penalty parameters tend to zero. -/
  parameter_tendsto : Tendsto parameter atTop (𝓝 0)
  /-- The tolerances tend to zero. -/
  tolerance_tendsto : Tendsto tolerance atTop (𝓝 0)
  /-- Each iterate satisfies $\|\nabla_x \Phi(x_k, y, \mu_k)\| \le \omega_k$. -/
  residual_le : ∀ k,
    ‖fderiv ℝ (augmentedLagrangian f c y (parameter k)) (iterate k)‖ ≤ tolerance k

/-- **Algorithm 14.3.1** of [conn2000trust], Step 1. The multiplier estimate after the inner solve
$k$ is the first-order estimate $y - c(x_k) / \mu_k$. -/
noncomputable def QuadraticPenaltyRun.multiplier {f : G → ℝ} {c : G → F} {y : F}
    (run : QuadraticPenaltyRun f c y) (k : ℕ) : F :=
  firstOrderMultiplier c y (run.parameter k) (run.iterate k)

/-- **Theorem 14.3.1(i)–(ii)** of [conn2000trust]. Let $F$ be finite-dimensional, let $f$ and $c$ be
twice continuously differentiable, and let $x_k \to x_*$ with $c'(x_*)$ surjective. Let
$y \in F$, $\mu_k > 0$ with $\mu_k \to 0$, and $\|\nabla_x \Phi(x_k, y, \mu_k)\| \le \omega_k$
with $\omega_k \to 0$. Let $y_* = y^{LS}(x_*)$ and $y^F_k = y - c(x_k) / \mu_k$. Then
$(x_*, y_*)$ satisfies the first-order conditions (14.2.3), $y^F_k \to y_*$,
$y^{LS}(x_k) \to y_*$, and there are $K_1, K_2 > 0$ such that, for all large $k$,
$$\|y^F_k - y_*\| \le K_1 \omega_k + K_2 \|x_k - x_*\|, \qquad \|y^{LS}(x_k) - y_*\| \le K_2
  \|x_k - x_*\|,$$
$$\|c(x_k)\| \le \mu_k \big(K_1 \omega_k + \|y - y_*\| + K_2 \|x_k - x_*\|\big).$$

The source considers a convergent subsequence of the iterates. Here the sequence $x_k$ is that
subsequence, reindexed. -/
theorem theorem_14_3_1 [FiniteDimensional ℝ F] {f : G → ℝ} {c : G → F}
    (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c) {xstar : G}
    (hA : Function.Surjective (fderiv ℝ c xstar)) {x : ℕ → G}
    (hx : Tendsto x atTop (𝓝 xstar)) (y : F) {μ ω : ℕ → ℝ}
    (hμ : ∀ k, 0 < μ k) (hμlim : Tendsto μ atTop (𝓝 0))
    (hres : ∀ k, ‖fderiv ℝ (augmentedLagrangian f c y (μ k)) (x k)‖ ≤ ω k)
    (hω : Tendsto ω atTop (𝓝 0)) :
    let ls := fun z ↦ leastSquaresMultiplier (fderiv ℝ c z) (gradient f z)
    let ystar := ls xstar
    IsEqualityKKT f c xstar ystar ∧
      Tendsto (fun k ↦ firstOrderMultiplier c y (μ k) (x k)) atTop (𝓝 ystar) ∧
      Tendsto (ls ∘ x) atTop (𝓝 ystar) ∧
      ∃ K₁ > 0, ∃ K₂ > 0, ∀ᶠ k in atTop,
        ‖firstOrderMultiplier c y (μ k) (x k) - ystar‖ ≤ K₁ * ω k + K₂ * ‖x k - xstar‖ ∧
        ‖ls (x k) - ystar‖ ≤ K₂ * ‖x k - xstar‖ ∧
        ‖c (x k)‖ ≤ μ k * (K₁ * ω k + ‖y - ystar‖ + K₂ * ‖x k - xstar‖) := by
  let ystar := leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar)
  have hu := multiplierGram_isUnit_of_surjective hA
  obtain ⟨K₁, hK₁, K₂, hK₂, hb⟩ := lemma_14_2_2_i (y := fun _ ↦ y) hf hc hu hx hμ hres
  obtain ⟨hy, hls, hkkt⟩ := lemma_14_2_2_ii (y := fun _ ↦ y) hf hc hu hx hμ hres hω
  have hxnorm := tendsto_iff_norm_sub_tendsto_zero.mp hx
  have hmajor : Tendsto (fun k ↦ μ k * (K₁ * ω k + ‖y - ystar‖ + K₂ * ‖x k - xstar‖))
      atTop (𝓝 0) := by
    have hsum := ((hω.const_mul K₁).add_const ‖y - ystar‖).add (hxnorm.const_mul K₂)
    simpa only [zero_mul] using hμlim.mul hsum
  have hzero : Tendsto (c ∘ x) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Function.comp_apply, sub_zero] using squeeze_zero'
      (Eventually.of_forall fun k ↦ norm_nonneg (c (x k))) (hb.mono fun _ h ↦ h.2.2) hmajor
  exact ⟨hkkt (tendsto_nhds_unique (hc.continuous.continuousAt.tendsto.comp hx) hzero),
    hy, hls, K₁, hK₁, K₂, hK₂, hb⟩

/-- **Theorem 14.3.1(iii)** of [conn2000trust], (14.3.5)–(14.3.6). Under the hypotheses of Theorem
14.3.1(i)–(ii), let also the KKT operator $K(x_*, y_*)$ of (14.2.28) be invertible. Then there
are $K_3, \dots, K_7 > 0$ such that, for all large $k$,
$$\|x_k - x_*\| \le K_3 \omega_k + K_4 \mu_k, \qquad \|y^F_k - y_*\| \le K_5 \omega_k + K_6
  \mu_k, \qquad \|y^{LS}(x_k) - y_*\| \le K_7 \omega_k + K_6 \mu_k,$$
$$\|c(x_k)\| \le K_5 \mu_k \omega_k + K_6 \mu_k^2 + \mu_k \|y - y_*\|.$$
-/
theorem theorem_14_3_1_iii [FiniteDimensional ℝ F] {f : G → ℝ} {c : G → F}
    (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c) {xstar : G}
    (hA : Function.Surjective (fderiv ℝ c xstar)) {x : ℕ → G}
    (hx : Tendsto x atTop (𝓝 xstar)) (y : F) {μ ω : ℕ → ℝ}
    (hμ : ∀ k, 0 < μ k) (hμlim : Tendsto μ atTop (𝓝 0))
    (hres : ∀ k, ‖fderiv ℝ (augmentedLagrangian f c y (μ k)) (x k)‖ ≤ ω k)
    (hω : Tendsto ω atTop (𝓝 0))
    (hK : IsUnit (penaltyKKTJacobian f c
      (xstar, leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar)))) :
    let ls := fun z ↦ leastSquaresMultiplier (fderiv ℝ c z) (gradient f z)
    let ystar := ls xstar
    ∃ K₃ > 0, ∃ K₄ > 0, ∃ K₅ > 0, ∃ K₆ > 0, ∃ K₇ > 0, ∀ᶠ k in atTop,
      ‖x k - xstar‖ ≤ K₃ * ω k + K₄ * μ k ∧
      ‖firstOrderMultiplier c y (μ k) (x k) - ystar‖ ≤ K₅ * ω k + K₆ * μ k ∧
      ‖ls (x k) - ystar‖ ≤ K₇ * ω k + K₆ * μ k ∧
      ‖c (x k)‖ ≤ K₅ * μ k * ω k + K₆ * μ k ^ 2 + μ k * ‖y - ystar‖ := by
  let ystar := leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar)
  have hfeas := (theorem_14_3_1 hf hc hA hx y hμ hμlim hres hω).1.1
  obtain ⟨μmax, hmax, K₃, h₃, K₄, h₄, K₅, h₅, K₆, h₆, K₇, h₇, hb⟩ :=
    lemma_14_2_2_iii (y := fun _ ↦ y) hf hc hfeas hx hμ hres hω hK
  let D := ‖y - ystar‖ + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨K₃, h₃, K₄ * D, mul_pos h₄ hD, K₅, h₅, K₆ * D, mul_pos h₆ hD, K₇, h₇, ?_⟩
  filter_upwards [hb, hμlim.eventually (gt_mem_nhds hmax)] with k hk hkμ
  obtain ⟨hxk, hyk, hlsk, hck⟩ := hk hkμ.le
  have hD' : ‖y - ystar‖ ≤ D := le_add_of_nonneg_right zero_le_one
  have hfour := mul_le_mul_of_nonneg_left hD' (mul_nonneg h₄.le (hμ k).le)
  have hsix := mul_le_mul_of_nonneg_left hD' (mul_nonneg h₆.le (hμ k).le)
  have hsq := mul_le_mul_of_nonneg_left hD' (mul_nonneg h₆.le (sq_nonneg (μ k)))
  refine ⟨hxk.trans ?_, hyk.trans ?_, hlsk.trans ?_, hck.trans ?_⟩ <;>
    nlinarith only [hfour, hsix, hsq]

open scoped InnerProduct

private theorem gradient_augmentedLagrangian_eq {f : G → ℝ} {c : G → F} {x : G}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x) (y : F) (μ : ℝ) :
    gradient (augmentedLagrangian f c y μ) x =
      gradient f x - (fderiv ℝ c x).adjoint (firstOrderMultiplier c y μ x) := by
  rw [gradient, fderiv_augmentedLagrangian_eq hf hc]
  exact gradient_lagrangian_eq hf hc _

/-- **Equation (14.3.9)** of [conn2000trust]. Let $f$ and $c$ be twice continuously differentiable.
Then
$$\nabla_{xx} \Phi(x, y, \mu) = \nabla_{xx} \ell\big(x, y^F(x)\big) + \frac1\mu c'(x)^* c'(x),$$
where the first-order estimate $y^F(x) = y - c(x) / \mu$ is held fixed in the Hessian of the
Lagrangian. -/
theorem fderiv_gradient_augmentedLagrangian_eq {f : G → ℝ} {c : G → F}
    (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c) (x : G) (y : F) (μ : ℝ) :
    fderiv ℝ (gradient (augmentedLagrangian f c y μ)) x =
      fderiv ℝ (gradient (lagrangian f c (firstOrderMultiplier c y μ x))) x +
        μ⁻¹ • (fderiv ℝ c x).adjoint.comp (fderiv ℝ c x) := by
  let A := fderiv ℝ c
  let Adj : (G →L[ℝ] F) →L[ℝ] (F →L[ℝ] G) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ)).toContinuousLinearEquiv.toContinuousLinearMap
  let yF := firstOrderMultiplier c y μ
  have hA : ContDiff ℝ 1 A := hc.fderiv_right (by norm_num)
  have hAdj : ContDiff ℝ 1 (fun z ↦ (A z).adjoint) := Adj.contDiff.comp hA
  have hg : ContDiff ℝ 1 (gradient f) :=
    (InnerProductSpace.toDual ℝ G).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (by norm_num))
  have hA' := (hAdj.differentiable one_ne_zero x).hasFDerivAt
  have hg' := (hg.differentiable one_ne_zero x).hasFDerivAt
  have hyF : HasFDerivAt yF (0 - μ⁻¹ • A x) x :=
    (hasFDerivAt_const y x).sub ((hc.differentiable (by norm_num) x).hasFDerivAt.const_smul μ⁻¹)
  have hp := (hg'.sub (hA'.clm_apply hyF)).congr_of_eventuallyEq
    (f₁ := gradient (augmentedLagrangian f c y μ)) (Eventually.of_forall fun z ↦
      gradient_augmentedLagrangian_eq (hf.differentiable (by norm_num) z)
        (hc.differentiable (by norm_num) z) y μ)
  have hL := (hg'.sub (hA'.clm_apply (hasFDerivAt_const (yF x) x))).congr_of_eventuallyEq
    (f₁ := gradient (lagrangian f c (yF x))) (Eventually.of_forall fun z ↦
      gradient_lagrangian_eq (hf.differentiable (by norm_num) z)
        (hc.differentiable (by norm_num) z) (yF x))
  rw [hp.fderiv, hL.fderiv]
  ext d
  simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, zero_apply,
    ContinuousLinearMap.flip_apply, smul_apply, zero_sub, neg_apply, map_neg,
    map_zero, zero_add, map_smul, A]
  abel

/-- Counterexample to the printed Lemma 14.3.2(ii)–(iii) of [conn2000trust] at an infeasible point.
Let $f = 0$ and $c(x) = 1 + x + x^2$ on $\mathbb{R}$. For every $\mu > 0$, the quadratic penalty
function $\Phi(x) = c(x)^2 / (2\mu)$ satisfies
$$\mu\, \Phi''(0) = 3 \quad\text{and}\quad c'(0)^2 = 1.$$

So the scaled Hessian does not tend to $c'(0)^2$ as $\mu \to 0$: the Lagrangian Hessian term
$-y^F c''(0) = c(0) c''(0) / \mu$ has order $1/\mu$. -/
theorem lemma_14_3_2_infeasible_counterexample {μ : ℝ} (hμ : 0 < μ) :
    let c : ℝ → ℝ := fun x ↦ 1 + x + x ^ 2
    μ * deriv (deriv (quadraticPenalty (fun _ ↦ 0) c μ)) 0 = 3 ∧
      (deriv c 0) ^ 2 = 1 := by
  let c : ℝ → ℝ := fun x ↦ 1 + x + x ^ 2
  have hc (x : ℝ) : HasDerivAt c (1 + 2 * x) x := by
    have h := ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).add
      ((hasDerivAt_id x).pow 2)
    convert h using 1
    · rfl
    · simp [id]
  have hfirst : deriv (quadraticPenalty (fun _ ↦ 0) c μ) =
      fun x ↦ μ⁻¹ * (c x * (1 + 2 * x)) := by
    funext x
    have h := ((hc x).pow 2).const_mul ((2 * μ)⁻¹)
    have h' : HasDerivAt (quadraticPenalty (fun _ ↦ 0) c μ)
        (μ⁻¹ * (c x * (1 + 2 * x))) x := by
      convert h using 1
      · funext t
        simp [quadraticPenalty, Real.norm_eq_abs, sq_abs]
      · simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_inv_rev]
        ring
    exact h'.deriv
  have hd : HasDerivAt (fun x : ℝ ↦ 1 + 2 * x) 2 0 := by
    simpa [id] using ((hasDerivAt_id (0 : ℝ)).const_mul 2).const_add 1
  have hsecond := ((hc 0).mul hd).const_mul μ⁻¹
  change μ * deriv (deriv (quadraticPenalty (fun _ ↦ 0) c μ)) 0 = 3 ∧
    (deriv c 0) ^ 2 = 1
  change HasDerivAt (fun x ↦ μ⁻¹ * (c x * (1 + 2 * x))) _ 0 at hsecond
  rw [hfirst, hsecond.deriv, (hc 0).deriv]
  simp [c]
  field_simp [hμ.ne']; norm_num

/-- **Equations (14.3.13)–(14.3.14)** of [conn2000trust]. Let $M : G \to G$ and $A : G \to F$ be
bounded linear maps, $b, s \in G$, $c \in F$ and $\mu \neq 0$. Then
$$\Big(M + \frac1\mu A^* A\Big) s = b + \frac1\mu A^* c$$
if and only if there is $t \in F$ with
$$M s + A^* t = b \quad\text{and}\quad A s - \mu t = c.$$
The second block equation determines the auxiliary variable $t$ uniquely. -/
theorem penalty_system_iff (M : G →L[ℝ] G) (A : G →L[ℝ] F)
    (b s : G) (c : F) {μ : ℝ} (hμ : μ ≠ 0) :
    M s + μ⁻¹ • A.adjoint (A s) = b + μ⁻¹ • A.adjoint c ↔
      ∃ t : F, M s + A.adjoint t = b ∧ A s - μ • t = c := by
  have hsolve (t : F) (ht : A s - μ • t = c) : t = μ⁻¹ • (A s - c) := by
    have he : μ • t = A s - c := by rw [← ht, sub_sub_cancel]
    rw [← he, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  have hc : A s - μ • (μ⁻¹ • (A s - c)) = c := by
    rw [smul_smul, mul_inv_cancel₀ hμ, one_smul, sub_sub_cancel]
  constructor
  · intro h
    refine ⟨μ⁻¹ • (A s - c), ?_, hc⟩
    rw [map_smul, map_sub, smul_sub, ← add_sub_assoc, h, add_sub_cancel_right]
  · rintro ⟨t, h, ht⟩
    rw [hsolve t ht, map_smul, map_sub, smul_sub, ← add_sub_assoc] at h
    exact sub_eq_iff_eq_add.mp h

/-- **Equation (14.3.15)** of [conn2000trust]. Let $f$ and $c$ be differentiable at $x$, and let
$\mu \neq 0$. Then for every $\nu$
$$\nabla_x \Phi(x, y, \nu) = \nabla_x \Phi(x, y, \mu) + \Big(\frac\mu\nu - 1\Big) c'(x)^*
  \big(y - y^F(x)\big),$$
where $y^F(x) = y - c(x) / \mu$ is the first-order estimate for $\mu$.

**Correction.** The scaling factor is $\mu / \nu - 1$. Since $y - y^F(x) = c(x) / \mu$, the
constraint term is $(1/\nu - 1/\mu)\, c'(x)^* c(x)$; the factor in the printed formula differs. -/
theorem gradient_augmentedLagrangian_change_parameter
    {f : G → ℝ} {c : G → F} {x : G} (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) (y : F) {μ ν : ℝ} (hμ : μ ≠ 0) :
    gradient (augmentedLagrangian f c y ν) x =
      gradient (augmentedLagrangian f c y μ) x +
        (μ / ν - 1) • (fderiv ℝ c x).adjoint (y - firstOrderMultiplier c y μ x) := by
  rw [gradient_augmentedLagrangian_eq hf hc, gradient_augmentedLagrangian_eq hf hc]
  have hscalar : (μ / ν - 1) * μ⁻¹ = ν⁻¹ - μ⁻¹ := by
    calc
      _ = (μ * μ⁻¹) * ν⁻¹ - μ⁻¹ := by rw [div_eq_mul_inv]; ring
      _ = _ := by rw [mul_inv_cancel₀ hμ, one_mul]
  simp only [firstOrderMultiplier, sub_sub_cancel, map_sub, map_smul, smul_smul]
  rw [hscalar, sub_smul]
  abel

open Subproblem in
omit [CompleteSpace G] in
/-- **Lemma 14.3.2(ii)–(iii)** of [conn2000trust], corrected eigenvalue estimates. Let $G$ be a
nontrivial finite-dimensional real inner product space, let $P$, $B$ and $H$ be operators on $G$
with $P$ and $B$ symmetric, let $\mu > 0$, and let $P = H + \mu^{-1} B$. Then
$$|\mu \lambda_{\min}(P) - \lambda_{\min}(B)| \le \mu \|H\| \quad\text{and}\quad |\mu
  \lambda_{\max}(P) - \lambda_{\max}(B)| \le \mu \|H\|.$$

**Correction.** The source states the limits of the scaled extreme eigenvalues without a bound
on the Lagrangian Hessian term $H$. At an infeasible point $H$ can grow like $1/\mu$, and the
limits fail; see `ConnGouldToint.Chapter14.lemma_14_3_2_infeasible_counterexample`. Here the
error is bounded by $\mu \|H\|$.

For the penalty Hessian (14.3.9), $H = \nabla_{xx} \ell(x, y^F(x))$ and $B = c'(x)^* c'(x)$. -/
theorem lemma_14_3_2_scaled_extremes [FiniteDimensional ℝ G] [Nontrivial G]
    {P B H : G →L[ℝ] G} (hP : P.toLinearMap.IsSymmetric) (hB : B.toLinearMap.IsSymmetric)
    {μ : ℝ} (hμ : 0 < μ) (hmodel : P = H + μ⁻¹ • B) :
    |μ * leftmost hP - leftmost hB| ≤ μ * ‖H‖ ∧
      |μ * rightmost hP - rightmost hB| ≤ μ * ‖H‖ := by
  have hunit (v : G) (hv : ‖v‖ = 1) : |μ * ⟪v, P v⟫ - ⟪v, B v⟫| ≤ μ * ‖H‖ := by
    have hb : |⟪v, H v⟫| ≤ ‖H‖ := by
      have h₁ := abs_real_inner_le_norm v (H v)
      have h₂ := H.le_opNorm v
      rw [hv, one_mul] at h₁
      rw [hv, mul_one] at h₂
      exact h₁.trans h₂
    have hmul : μ * (μ⁻¹ * ⟪v, B v⟫) = ⟪v, B v⟫ := by
      rw [← mul_assoc, mul_inv_cancel₀ hμ.ne', one_mul]
    have he : μ * ⟪v, P v⟫ - ⟪v, B v⟫ = μ * ⟪v, H v⟫ := by
      rw [hmodel, add_apply, smul_apply, inner_add_right, real_inner_smul_right]
      linarith only [hmul, mul_add μ ⟪v, H v⟫ (μ⁻¹ * ⟪v, B v⟫)]
    rw [he, abs_mul, abs_of_pos hμ]
    exact mul_le_mul_of_nonneg_left hb hμ.le
  have hleft (T : G →L[ℝ] G) (hT : T.toLinearMap.IsSymmetric) :
      ∃ v : G, ‖v‖ = 1 ∧ ⟪v, T v⟫ = leftmost hT := by
    obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hT)
    refine ⟨hT.eigenvectorBasis rfl i, (hT.eigenvectorBasis rfl).norm_eq_one i, ?_⟩
    rw [apply_eigenvectorBasis' (hH := hT), hi, real_inner_smul_right,
      real_inner_self_eq_norm_sq, (hT.eigenvectorBasis rfl).norm_eq_one, one_pow, mul_one]
  have hright (T : G →L[ℝ] G) (hT : T.toLinearMap.IsSymmetric) :
      ∃ v : G, ‖v‖ = 1 ∧ ⟪v, T v⟫ = rightmost hT := by
    obtain ⟨i, hi⟩ := exists_eigenvalues_eq_rightmost (hH := hT)
    refine ⟨hT.eigenvectorBasis rfl i, (hT.eigenvectorBasis rfl).norm_eq_one i, ?_⟩
    rw [apply_eigenvectorBasis' (hH := hT), hi, real_inner_smul_right,
      real_inner_self_eq_norm_sq, (hT.eigenvectorBasis rfl).norm_eq_one, one_pow, mul_one]
  obtain ⟨p, hp, hpl⟩ := hleft P hP
  obtain ⟨b, hb, hbl⟩ := hleft B hB
  obtain ⟨p', hp', hpr⟩ := hright P hP
  obtain ⟨b', hb', hbr⟩ := hright B hB
  constructor <;> apply abs_le.mpr
  · have h₁ := (abs_le.mp (hunit p hp)).1
    have h₂ := (abs_le.mp (hunit b hb)).2
    have hpB : leftmost hB ≤ ⟪p, B p⟫ := by
      simpa only [hp, one_pow, mul_one] using leftmost_mul_norm_sq_le (hH := hB) p
    have hbP : leftmost hP ≤ ⟪b, P b⟫ := by
      simpa only [hb, one_pow, mul_one] using leftmost_mul_norm_sq_le (hH := hP) b
    rw [hpl] at h₁
    rw [hbl] at h₂
    exact ⟨by linarith only [h₁, hpB],
      by linarith only [h₂, mul_le_mul_of_nonneg_left hbP hμ.le]⟩
  · have h₁ := (abs_le.mp (hunit b' hb')).1
    have h₂ := (abs_le.mp (hunit p' hp')).2
    have hbP : ⟪b', P b'⟫ ≤ rightmost hP := by
      simpa only [hb', one_pow, mul_one] using inner_le_rightmost_mul_norm_sq (hH := hP) b'
    have hpB : ⟪p', B p'⟫ ≤ rightmost hB := by
      simpa only [hp', one_pow, mul_one] using inner_le_rightmost_mul_norm_sq (hH := hB) p'
    rw [hbr] at h₁
    rw [hpr] at h₂
    exact ⟨by linarith only [h₁, mul_le_mul_of_nonneg_left hbP hμ.le],
      by linarith only [h₂, hpB]⟩

open Subproblem in
omit [CompleteSpace G] in
/-- **Lemma 14.3.2(ii)–(iii)** of [conn2000trust], limit form. Let $G$ be a nontrivial
finite-dimensional real inner product space, let $B$ be symmetric, and let $P_i$ be symmetric
operators indexed along a filter $l$. Suppose that $\mu_i \to 0$, and that eventually
$\mu_i > 0$, $\|H_i\| \le C$ and $P_i = H_i + \mu_i^{-1} B$. Then
$$\mu_i \lambda_{\min}(P_i) \to \lambda_{\min}(B) \quad\text{and}\quad \mu_i \lambda_{\max}(P_i)
  \to \lambda_{\max}(B).$$

**Correction.** As in `ConnGouldToint.Chapter14.lemma_14_3_2_scaled_extremes`, the operators
$H_i$ are assumed to be uniformly bounded. -/
theorem lemma_14_3_2_scaled_limits [FiniteDimensional ℝ G] [Nontrivial G]
    {ι : Type*} {l : Filter ι} {μ : ι → ℝ} {P H : ι → G →L[ℝ] G}
    {B : G →L[ℝ] G} (hP : ∀ i, (P i).toLinearMap.IsSymmetric)
    (hB : B.toLinearMap.IsSymmetric) (hμ : Tendsto μ l (𝓝 0))
    (hpos : ∀ᶠ i in l, 0 < μ i) (C : ℝ) (hbound : ∀ᶠ i in l, ‖H i‖ ≤ C)
    (hmodel : ∀ᶠ i in l, P i = H i + (μ i)⁻¹ • B) :
    Tendsto (fun i ↦ μ i * leftmost (hP i)) l (𝓝 (leftmost hB)) ∧
      Tendsto (fun i ↦ μ i * rightmost (hP i)) l (𝓝 (rightmost hB)) := by
  have hb := hμ.mul_const C
  rw [zero_mul] at hb
  have he := hpos.and (hbound.and hmodel)
  constructor
  · refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall
      fun _ ↦ norm_nonneg _) ?_ hb)
    filter_upwards [he] with i hi
    rw [Real.norm_eq_abs]
    exact (lemma_14_3_2_scaled_extremes (hP i) hB hi.1 hi.2.2).1.trans
      (mul_le_mul_of_nonneg_left hi.2.1 hi.1.le)
  · refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall
      fun _ ↦ norm_nonneg _) ?_ hb)
    filter_upwards [he] with i hi
    rw [Real.norm_eq_abs]
    exact (lemma_14_3_2_scaled_extremes (hP i) hB hi.1 hi.2.2).2.trans
      (mul_le_mul_of_nonneg_left hi.2.1 hi.1.le)

omit [CompleteSpace F] in
/-- **Lemma 14.3.2(iv)** of [conn2000trust]. If the constraint space $F$ is zero-dimensional, the
Hessian of the penalty function is the Hessian of the objective:
$$\nabla_{xx} \Phi(x, y, \mu) = \nabla^2 f(x).$$
-/
theorem lemma_14_3_2_iv [Subsingleton F] (f : G → ℝ) (c : G → F)
    (x : G) (y : F) (μ : ℝ) :
    fderiv ℝ (gradient (augmentedLagrangian f c y μ)) x = fderiv ℝ (gradient f) x := by
  congr 2
  funext z
  simp [augmentedLagrangian, lagrangian, Subsingleton.elim (c z) 0]

section ReducedHessian

variable [FiniteDimensional ℝ G] (A : G →L[ℝ] F)

/-- **Lemma 14.3.2(i)** of [conn2000trust], the reduced Hessian. Let $A : G \to F$ and
$H : G \to G$, and let $N : \ker A \to G$ be the inclusion. The **reduced Hessian** is the
operator $N^* H N$ on $\ker A$, which represents the restriction of the quadratic form of $H$ to
$\ker A$. -/
noncomputable def reducedPenaltyHessian (H : G →L[ℝ] G) :
    A.toLinearMap.ker →L[ℝ] A.toLinearMap.ker :=
  let N := A.toLinearMap.ker.subtypeL
  N.adjoint.comp (H.comp N)

omit [CompleteSpace F] [FiniteDimensional ℝ G] in
/-- If $H$ is symmetric, the reduced Hessian $N^* H N$ on $\ker A$ is symmetric. -/
theorem reducedPenaltyHessian_symmetric {H : G →L[ℝ] G} (hH : H.toLinearMap.IsSymmetric) :
    (reducedPenaltyHessian A H).toLinearMap.IsSymmetric := by
  intro v w
  change ⟪(A.toLinearMap.ker.subtypeL.adjoint) (H v), w⟫ =
    ⟪v, (A.toLinearMap.ker.subtypeL.adjoint) (H w)⟫
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  exact hH v w

open Subproblem in
/-- **Lemma 14.3.2(i)** of [conn2000trust], for a fixed Hessian. Let $G$ be a nontrivial
finite-dimensional real inner product space, let $A : G \to F$ have a nontrivial kernel, and let
$H$ be symmetric. Then, as $\mu \to 0^+$,
$$\lambda_{\min}\Big(H + \frac1\mu A^* A\Big) \to \lambda_{\min}(N^* H N),$$
where $N^* H N$ is the reduced Hessian on $\ker A$.

**Correction.** The source states the limit for the penalty Hessian, whose Lagrangian term
depends on $\mu$ through $y^F(x)$. Here the Lagrangian Hessian $H$ is fixed, and the compression
is to the entire kernel of $A$. At a feasible point the two Hessians agree; see
`ConnGouldToint.Chapter14.lemma_14_3_2_i_of_feasible`.

The penalty term forces the directions of least Rayleigh quotient into $\ker A$ in the limit. -/
theorem lemma_14_3_2_i [Nontrivial G] [Nontrivial A.toLinearMap.ker]
    {H : G →L[ℝ] G} (hH : H.toLinearMap.IsSymmetric)
    (hP : ∀ μ : ℝ, (H + μ⁻¹ • A.adjoint.comp A).toLinearMap.IsSymmetric) :
    Tendsto (fun μ ↦ leftmost (hP μ)) (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝 (leftmost (reducedPenaltyHessian_symmetric A hH))) := by
  let R := reducedPenaltyHessian A H
  let hR := reducedPenaltyHessian_symmetric A hH
  let lamMin := leftmost hR
  let q : G → ℝ := fun v ↦ ⟪v, H v⟫
  have hq : Continuous q := continuous_id.inner H.continuous
  have hkernel (v : A.toLinearMap.ker) : ⟪v, R v⟫ = q v := by
    exact ContinuousLinearMap.adjoint_inner_right A.toLinearMap.ker.subtypeL v (H v)
  have hquad (μ : ℝ) (v : G) :
      ⟪v, (H + μ⁻¹ • A.adjoint.comp A) v⟫ = q v + μ⁻¹ * ‖A v‖ ^ 2 := by
    rw [add_apply, smul_apply, inner_add_right, real_inner_smul_right,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      real_inner_self_eq_norm_sq]
  have hmin (v : G) (hv : A v = 0) (hunit : ‖v‖ = 1) : lamMin ≤ q v := by
    let v' : A.toLinearMap.ker := ⟨v, hv⟩
    have h := leftmost_mul_norm_sq_le (hH := hR) v'
    rw [hkernel, show ‖v'‖ = 1 from hunit, one_pow, mul_one] at h
    exact h
  have hupper (μ : ℝ) : leftmost (hP μ) ≤ lamMin := by
    obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hR)
    let v := hR.eigenvectorBasis rfl i
    have hv : ‖(v : G)‖ = 1 := (hR.eigenvectorBasis rfl).norm_eq_one i
    have hker : A (v : G) = 0 := v.property
    have hvalue : q v = lamMin := by
      rw [← hkernel, show R v = lamMin • v from (apply_eigenvectorBasis' (hH := hR) i).trans
        (congrArg (fun t : ℝ ↦ t • v) hi), real_inner_smul_right, real_inner_self_eq_norm_sq,
        show ‖v‖ = 1 from hv, one_pow, mul_one]
    have h := leftmost_mul_norm_sq_le (hH := hP μ) (v : G)
    rw [hv, one_pow, mul_one, hquad, hker, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero, hvalue] at h
    exact h
  have hlarge (ε : ℝ) (hε : 0 < ε) :
      ∃ δ > 0, ∀ μ ∈ Set.Ioo 0 δ, lamMin - ε ≤ leftmost (hP μ) := by
    let S := Metric.sphere (0 : G) 1 ∩ {v | q v ≤ lamMin - ε}
    have hS : IsCompact S := (isCompact_sphere _ _).inter_right
      (isClosed_le hq continuous_const)
    have hSunit (v : G) (hv : v ∈ S) : ‖v‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hv.1
    have hbound (μ : ℝ) (hμ : 0 < μ) (v : G) (hv : ‖v‖ = 1)
        (h : v ∉ S) : lamMin - ε ≤ ⟪v, (H + μ⁻¹ • A.adjoint.comp A) v⟫ := by
      have hqv : lamMin - ε ≤ q v := by
        by_contra! hn
        exact h ⟨by simpa [Metric.mem_sphere, dist_zero_right] using hv, hn.le⟩
      rw [hquad]
      exact hqv.trans (le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr hμ.le) (sq_nonneg _)))
    have hRayleigh (μ : ℝ) (h :
        ∀ v : G, ‖v‖ = 1 → lamMin - ε ≤ ⟪v, (H + μ⁻¹ • A.adjoint.comp A) v⟫) :
        lamMin - ε ≤ leftmost (hP μ) := by
      obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hP μ)
      let v := (hP μ).eigenvectorBasis rfl i
      have hv : ‖v‖ = 1 := ((hP μ).eigenvectorBasis rfl).norm_eq_one i
      have hv' := h v hv
      rw [show (H + μ⁻¹ • A.adjoint.comp A) v = leftmost (hP μ) • v from
        (apply_eigenvectorBasis' (hH := hP μ) i).trans (congrArg (fun t : ℝ ↦ t • v) hi),
        real_inner_smul_right, real_inner_self_eq_norm_sq, hv, one_pow, mul_one] at hv'
      exact hv'
    by_cases hne : S.Nonempty
    · obtain ⟨w, hw, hwmin⟩ := hS.exists_isMinOn hne
        ((A.continuous.norm.pow 2).continuousOn)
      let d := ‖A w‖ ^ 2
      have hd : 0 < d := by
        have hAw : A w ≠ 0 := fun he ↦ by
          have h₁ := hmin w he (hSunit w hw)
          have h₂ : q w ≤ lamMin - ε := hw.2
          linarith
        exact sq_pos_of_pos (norm_pos_iff.mpr hAw)
      let C := |lamMin - ε| + ‖H‖ + 1
      have hC : 0 < C := by dsimp [C]; positivity
      refine ⟨d / C, div_pos hd hC, fun μ hμ ↦ hRayleigh μ ?_⟩
      intro v hv
      by_cases hvs : v ∈ S
      · have hlow : -‖H‖ ≤ q v := by
          have hi := (abs_le.mp (abs_real_inner_le_norm v (H v))).1
          have hop := H.le_opNorm v
          rw [hv, one_mul] at hi
          rw [hv, mul_one] at hop
          change -‖H‖ ≤ ⟪v, H v⟫
          linarith
        have hprod : C * μ ≤ d := by
          have := (lt_div_iff₀ hC).mp hμ.2
          linarith
        have hdC : C ≤ μ⁻¹ * ‖A v‖ ^ 2 := by
          rw [inv_mul_eq_div, le_div_iff₀ hμ.1]
          exact hprod.trans (hwmin hvs)
        rw [hquad]
        dsimp [C] at hdC
        linarith only [hlow, hdC, le_abs_self (lamMin - ε)]
      · exact hbound μ hμ.1 v hv hvs
    · exact ⟨1, zero_lt_one, fun μ hμ ↦
        hRayleigh μ fun v hv ↦ hbound μ hμ.1 v hv (fun h ↦ hne ⟨v, h⟩)⟩
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hδbound⟩ := hlarge (ε / 2) (half_pos hε)
  have hev : ∀ᶠ μ : ℝ in 𝓝[Set.Ioi (0 : ℝ)] 0, μ ∈ Set.Ioo 0 δ := by
    have hup := (eventually_lt_nhds hδ).filter_mono
      (nhdsWithin_le_nhds : 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝 0)
    filter_upwards [self_mem_nhdsWithin, hup] with μ hlo hhi
    exact ⟨hlo, hhi⟩
  filter_upwards [hev] with μ hμ
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hupper μ, hδbound μ hμ]

end ReducedHessian

private theorem symmetric_fderiv_gradient {f : G → ℝ} (hf : ContDiff ℝ 2 f) (x : G) :
    (fderiv ℝ (gradient f) x).toLinearMap.IsSymmetric := by
  let J := (InnerProductSpace.toDual ℝ G).symm.toContinuousLinearEquiv
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (by norm_num) : ContDiff ℝ 1 (fderiv ℝ f)).differentiable one_ne_zero x
  have h := J.hasFDerivAt.comp x hd.hasFDerivAt
  change HasFDerivAt (gradient f) _ _ at h
  have hs := hf.contDiffAt.isSymmSndFDerivAt (x := x) (by simp)
  intro v w
  change ⟪fderiv ℝ (gradient f) x v, w⟫ = ⟪v, fderiv ℝ (gradient f) x w⟫
  rw [h.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← real_inner_comm v]
  change ⟪(InnerProductSpace.toDual ℝ G).symm (fderiv ℝ (fderiv ℝ f) x v), w⟫ =
    ⟪(InnerProductSpace.toDual ℝ G).symm (fderiv ℝ (fderiv ℝ f) x w), v⟫
  simpa only [InnerProductSpace.toDual_symm_apply] using hs.eq v w

private theorem symmetric_penalty_gram (A : G →L[ℝ] F) :
    (A.adjoint.comp A).toLinearMap.IsSymmetric := by
  intro v w
  change ⟪A.adjoint (A v), w⟫ = ⟪v, A.adjoint (A w)⟫
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

open Subproblem in
omit [CompleteSpace G] in
private theorem leftmost_congr [FiniteDimensional ℝ G] {P M : G →L[ℝ] G}
    (he : P = M) (hP : P.toLinearMap.IsSymmetric) (hM : M.toLinearMap.IsSymmetric) :
    leftmost hP = leftmost hM := by
  subst M
  rfl

open Subproblem in
/-- **Lemma 14.3.2(i)** of [conn2000trust] at a feasible point. Let $G$ be a nontrivial
finite-dimensional real inner product space, let $f$ and $c$ be twice continuously
differentiable, let $c(x) = 0$, and let $\ker c'(x)$ be nontrivial. Let
$H = \nabla_{xx} \ell(x, y)$. Then $H$ and the penalty Hessians $\nabla_{xx} \Phi(x, y, \mu)$
are symmetric, and as $\mu \to 0^+$
$$\lambda_{\min}\big(\nabla_{xx} \Phi(x, y, \mu)\big) \to \lambda_{\min}(N^* H N),$$
where $N^* H N$ is the reduced Hessian on $\ker c'(x)$.

At a feasible point $y^F(x) = y$, so the penalty Hessian is $H + \mu^{-1} c'(x)^* c'(x)$ and
`ConnGouldToint.Chapter14.lemma_14_3_2_i` applies. -/
theorem lemma_14_3_2_i_of_feasible [FiniteDimensional ℝ G] [Nontrivial G]
    {f : G → ℝ} {c : G → F} (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c)
    {x : G} (hcx : c x = 0) (y : F) [Nontrivial (fderiv ℝ c x).toLinearMap.ker] :
    let A := fderiv ℝ c x
    let H := fderiv ℝ (gradient (lagrangian f c y)) x
    ∃ (hH : H.toLinearMap.IsSymmetric)
      (hP : ∀ μ : ℝ, (fderiv ℝ (gradient (augmentedLagrangian f c y μ)) x).toLinearMap.IsSymmetric),
      Tendsto (fun μ ↦ leftmost (hP μ)) (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 (leftmost (reducedPenaltyHessian_symmetric A hH))) := by
  let A := fderiv ℝ c x
  let H := fderiv ℝ (gradient (lagrangian f c y)) x
  have hL : ContDiff ℝ 2 (lagrangian f c y) := hf.sub (contDiff_const.inner ℝ hc)
  have hH : H.toLinearMap.IsSymmetric := symmetric_fderiv_gradient hL x
  have hM (μ : ℝ) : (H + μ⁻¹ • A.adjoint.comp A).toLinearMap.IsSymmetric :=
    hH.add ((symmetric_penalty_gram A).smul rfl)
  have he (μ : ℝ) :
      fderiv ℝ (gradient (augmentedLagrangian f c y μ)) x = H + μ⁻¹ • A.adjoint.comp A := by
    simpa [firstOrderMultiplier, hcx, H, A] using
      fderiv_gradient_augmentedLagrangian_eq hf hc x y μ
  have hP (μ : ℝ) :
      (fderiv ℝ (gradient (augmentedLagrangian f c y μ)) x).toLinearMap.IsSymmetric :=
    he μ ▸ hM μ
  refine ⟨hH, hP, ?_⟩
  have hfun : (fun μ ↦ leftmost (hP μ)) = fun μ ↦ leftmost (hM μ) := by
    funext μ
    exact leftmost_congr (he μ) (hP μ) (hM μ)
  rw [hfun]
  exact lemma_14_3_2_i A hH hM

open Subproblem in
/-- **Lemma 14.3.2(ii)–(iii)** of [conn2000trust] at a feasible point. Let $G$ be a nontrivial
finite-dimensional real inner product space, let $f$ and $c$ be twice continuously
differentiable, let $c(x) = 0$, and let $A = c'(x)$. Then $A^* A$ and the penalty Hessians
$\nabla_{xx} \Phi(x, y, \mu)$ are symmetric, and as $\mu \to 0^+$
$$\mu \lambda_{\min}\big(\nabla_{xx} \Phi(x, y, \mu)\big) \to \lambda_{\min}(A^* A)
  \quad\text{and}\quad \mu \lambda_{\max}\big(\nabla_{xx} \Phi(x, y, \mu)\big) \to
  \lambda_{\max}(A^* A).$$

At a feasible point the correction $y^F(x) - y$ vanishes for every $\mu$, so the Lagrangian
Hessian term is fixed. -/
theorem lemma_14_3_2_scaled_limits_of_feasible [FiniteDimensional ℝ G] [Nontrivial G]
    {f : G → ℝ} {c : G → F} (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c)
    {x : G} (hcx : c x = 0) (y : F) :
    let A := fderiv ℝ c x
    ∃ (hB : (A.adjoint.comp A).toLinearMap.IsSymmetric)
      (hP : ∀ μ : ℝ, (fderiv ℝ (gradient (augmentedLagrangian f c y μ)) x).toLinearMap.IsSymmetric),
      Tendsto (fun μ ↦ μ * leftmost (hP μ)) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (leftmost hB)) ∧
        Tendsto (fun μ ↦ μ * rightmost (hP μ)) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (rightmost hB)) := by
  let A := fderiv ℝ c x
  let H := fderiv ℝ (gradient (lagrangian f c y)) x
  have hB := symmetric_penalty_gram A
  have hL : ContDiff ℝ 2 (lagrangian f c y) := hf.sub (contDiff_const.inner ℝ hc)
  have hH : H.toLinearMap.IsSymmetric := symmetric_fderiv_gradient hL x
  have he (μ : ℝ) :
      fderiv ℝ (gradient (augmentedLagrangian f c y μ)) x = H + μ⁻¹ • A.adjoint.comp A := by
    simpa [firstOrderMultiplier, hcx, H, A] using
      fderiv_gradient_augmentedLagrangian_eq hf hc x y μ
  have hP (μ : ℝ) :
      (fderiv ℝ (gradient (augmentedLagrangian f c y μ)) x).toLinearMap.IsSymmetric :=
    he μ ▸ hH.add (hB.smul rfl)
  refine ⟨hB, hP, lemma_14_3_2_scaled_limits hP hB (Filter.tendsto_id'.mpr nhdsWithin_le_nhds)
    self_mem_nhdsWithin ‖H‖ (Eventually.of_forall fun _ ↦ le_rfl)
    (Eventually.of_forall he)⟩

end ConnGouldToint.Chapter14
