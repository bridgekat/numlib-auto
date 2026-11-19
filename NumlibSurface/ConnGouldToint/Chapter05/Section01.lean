/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Preconditioned
import Numlib.Krylov.Singular
import Numlib.Optimization.Subproblem.TrustRegion

/-!
# Conn, Gould and Toint, Section 5.1: Conjugate gradients

This module formalizes Section 5.1 of [conn2000trust]. On a real inner product space $E$, the
conjugate gradient method minimizes the quadratic
$$q(x) = \langle c, x \rangle + \tfrac{1}{2} \langle x, Hx \rangle$$
of (5.1.1), whose gradient is $g(x) = Hx + c$. Lemmas 5.1.1–5.1.5 describe minimizers on affine
subspaces, exact line steps along conjugate directions, and the orthogonality of the gradients to
the directions. Algorithm 5.1.1 generates conjugate directions by the recurrences (5.1.23)–(5.1.26),
and Algorithm 5.1.2 is the conjugate gradient method. If $H$ is symmetric positive definite, the
method terminates after at most as many steps as $H$ has distinct eigenvalues (Theorem 5.1.6), and
its error in the $H$-norm satisfies the Chebyshev bound
$$\|x_k - x_*\|_H \le 2 \left( \frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1} \right)^k \|x_0 -
  x_*\|_H$$
with $\kappa = \lambda_{\max} / \lambda_{\min}$ (Theorem 5.1.7). Preconditioning, by a change of
variables (Algorithm 5.1.3) or by an inverse preconditioner (Algorithm 5.1.4), gives the same
results with the eigenvalues of the pair $(H, M)$ (Corollaries 5.1.8 and 5.1.9).

The proofs specialize the CG and PCG methods of the backbone modules `Numlib.Krylov.CG`,
`Numlib.Krylov.Preconditioned` and `Numlib.Krylov.Singular`.

## Main definitions

* Equation (5.1.1), `ConnGouldToint.Chapter05.quadraticObjective`: the quadratic $q(x) = \langle c,
  x \rangle + \frac{1}{2} \langle x, Hx \rangle$.
* Equations (5.1.14)–(5.1.15), `ConnGouldToint.Chapter05.residualLineStep`: the gradient after an
  exact line step.
* Algorithm 5.1.1, `ConnGouldToint.Chapter05.conjugateDirectionStep`: one pass of the recurrences
  (5.1.23)–(5.1.26).
* Algorithm 5.1.1, `ConnGouldToint.Chapter05.algorithm_5_1_1`: the conjugate directions from an
  initial gradient.
* Algorithm 5.1.1, `ConnGouldToint.Chapter05.ConjugateDirectionStepDefined`: the two divisions of a
  step have nonzero denominators.
* Algorithm 5.1.2, `ConnGouldToint.Chapter05.algorithm_5_1_2`: the conjugate gradient method.
* Algorithm 5.1.3, `ConnGouldToint.Chapter05.algorithm_5_1_3`: conjugate gradients on the
  transformed quadratic.
* Equation (5.1.53), `ConnGouldToint.Chapter05.transformedCGPreconditioner`: the preconditioner
  $M = R^* R$.
* Algorithm 5.1.4, `ConnGouldToint.Chapter05.algorithm_5_1_4`: the preconditioned conjugate gradient
  method.

## Main results

* Algorithm 5.1.1, `ConnGouldToint.Chapter05.algorithm_5_1_1_zero` and
  `ConnGouldToint.Chapter05.algorithm_5_1_1_succ`: the initialization and the recurrences
  (5.1.23)–(5.1.26).
* Algorithm 5.1.1, `ConnGouldToint.Chapter05.algorithm_5_1_1_eq_projectedCG`: the gradients and
  directions are those of the conjugate gradient method.
* Algorithm 5.1.1, `ConnGouldToint.Chapter05.conjugateDirectionStepDefined_iff`: the step is defined
  if and only if both denominators are nonzero.
* Algorithm 5.1.1, `ConnGouldToint.Chapter05.algorithm_5_1_1_conjugate`: for symmetric positive
  definite $H$, distinct directions are conjugate.
* Algorithm 5.1.1, `ConnGouldToint.Chapter05.algorithm_5_1_1_stepDefined_iff`: for symmetric
  positive definite $H$, the step is defined if and only if the gradient is nonzero.
* Algorithm 5.1.3, `ConnGouldToint.Chapter05.algorithm_5_1_3_zero` and
  `ConnGouldToint.Chapter05.algorithm_5_1_3_succ`: the initialization and the recurrences
  (5.1.46)–(5.1.50).
* Equation (5.1.53), `ConnGouldToint.Chapter05.transformedCGPreconditioner_apply_inverse`:
  $M^{-1} = R^{-1} R^{-*}$.
* Lemma 5.1.1, `ConnGouldToint.Chapter05.lemma_5_1_1`: the stationary point of $q$ on an affine
  subspace, and its minimality.
* Lemma 5.1.2, `ConnGouldToint.Chapter05.lemma_5_1_2`: a new conjugate direction updates the
  subspace minimizer by one exact line step.
* Lemma 5.1.3, `ConnGouldToint.Chapter05.lemma_5_1_3`: a vector orthogonal to the generated
  directions is orthogonal to the input vectors.
* Lemma 5.1.4, `ConnGouldToint.Chapter05.lemma_5_1_4`: exact line steps make the gradient orthogonal
  to the directions already used.
* Lemma 5.1.5, `ConnGouldToint.Chapter05.lemma_5_1_5`: orthogonality to the earlier gradients
  reduces the conjugacy update to the last direction.
* Lemma 5.1.5, `ConnGouldToint.Chapter05.counterexample_5_1_5`: Lemma 5.1.5 fails without nonzero
  earlier gradient pairings.
* Theorem 5.1.6, `ConnGouldToint.Chapter05.theorem_5_1_6`: the conjugate gradient method terminates
  after at most the number of distinct eigenvalues.
* Theorem 5.1.7, `ConnGouldToint.Chapter05.theorem_5_1_7`: the Chebyshev bound on the error in the
  $H$-norm.
* Corollary 5.1.8, `ConnGouldToint.Chapter05.corollary_5_1_8`: the same bound for preconditioned
  conjugate gradients.
* Corollary 5.1.9, `ConnGouldToint.Chapter05.corollary_5_1_9`: preconditioned conjugate gradients
  terminate after at most the number of distinct eigenvalues of $M^{-1} H$.

## Conventions

* The gradient is $g_k = H x_k + c$. The backbone CG and PCG states for $Hx = -c$ carry the residual
  $-c - Hx_k = -g_k$, the negative of the gradient.
* "Symmetric positive definite" is `LinearMap.IsSymmetricCoercive`: symmetric with
  $\langle Hx, x \rangle \ge \mu \|x\|^2$ for some $\mu > 0$.
* Sequences start at index $0$.
* The divisions in the recurrences use Lean's convention $a / 0 = 0$.

## Deviations from the source

* **Algorithms 5.1.1–5.1.4** (reading). The recurrences are indexed by every natural number,
  with scalar division totalized at zero. The defined-step predicate identifies the two
  nonzero denominators of Algorithm 5.1.1. The transformed and preconditioned forms use
  Hilbert-space operators in place of matrices.
* **Lemmas 5.1.1 and 5.1.2** (generalization). Subspace minimization uses linear maps and
  adjoints. The line update assumes a previous minimizer, nonnegative curvature on the
  enlarged span and nonzero curvature in the added direction.
* **Lemma 5.1.5** (correction). The gradient pairings $\langle p_j, r_j \rangle$ must be nonzero at
  all earlier directions, not only at the last. See `ConnGouldToint.Chapter05.lemma_5_1_5` and
  `ConnGouldToint.Chapter05.counterexample_5_1_5`.
* **Theorem 5.1.7 and Corollary 5.1.8** (reading). The error bounds are stated as products, not as
  ratios of errors, so that they also hold when $x_0 = x_*$. See
  `ConnGouldToint.Chapter05.theorem_5_1_7` and `ConnGouldToint.Chapter05.corollary_5_1_8`.
-/

namespace ConnGouldToint.Chapter05

open Krylov
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Equation (5.1.1)** of [conn2000trust]. For $c \in E$ and a bounded linear operator $H$ on $E$,
the **quadratic objective** is
$$q(x) = \langle c, x \rangle + \tfrac{1}{2} \langle x, Hx \rangle.$$

It is `Subproblem.quadModel c H`.

**Reading.** Quadratic with a bounded operator on a real inner-product space.
-/
noncomputable abbrev quadraticObjective (c : E) (H : E →L[ℝ] E) : E → ℝ :=
  Subproblem.quadModel c H

/-- **Algorithm 5.1.1** of [conn2000trust], one pass of (5.1.23)–(5.1.26). For a linear operator $H$
on $E$ and a state $(r, p)$ of a gradient $r$ and a direction $p$, the **conjugate direction
step** returns $(r', p')$ with
$$\alpha = \frac{\|r\|^2}{\langle p, Hp \rangle}, \qquad r' = r + \alpha Hp, \qquad \beta =
  \frac{\|r'\|^2}{\|r\|^2}, \qquad p' = -r' + \beta p.$$

The state does not contain the iterate. The divisions use Lean's convention $a / 0 = 0$.

**Reading.** Printed conjugate direction update with totalized scalar divisions.
-/
noncomputable def conjugateDirectionStep (H : E →ₗ[ℝ] E) (state : E × E) : E × E :=
  let Hp := H state.2
  let α := ‖state.1‖ ^ 2 / ⟪state.2, Hp⟫
  let r' := state.1 + α • Hp
  let β := ‖r'‖ ^ 2 / ‖state.1‖ ^ 2
  (r', -r' + β • state.2)

/-- **Algorithm 5.1.1** of [conn2000trust]. For a linear operator $H$ on $E$ and an initial gradient
$r_0 \in E$, the $k$-th state $(r_k, p_k)$ is obtained from $(r_0, -r_0)$ by $k$ conjugate
direction steps.

The algorithm generates conjugate directions without computing the iterates of Algorithm 5.1.2.

**Reading.** Returns an iterate at every index, including past termination or division breakdown.
-/
noncomputable def algorithm_5_1_1 (H : E →ₗ[ℝ] E) (r₀ : E) (k : ℕ) : E × E :=
  (conjugateDirectionStep H)^[k] (r₀, -r₀)

/-- **Algorithm 5.1.1** of [conn2000trust], initialization. The initial state is
$(r_0, p_0) = (r_0, -r_0)$. -/
theorem algorithm_5_1_1_zero (H : E →ₗ[ℝ] E) (r₀ : E) :
    algorithm_5_1_1 H r₀ 0 = (r₀, -r₀) := rfl

/-- **Algorithm 5.1.1** of [conn2000trust], equations (5.1.23)–(5.1.26). The state $(r_k, p_k)$
satisfies
$$\alpha_k = \frac{\|r_k\|^2}{\langle p_k, H p_k \rangle}, \quad r_{k+1} = r_k + \alpha_k H p_k,
  \quad \beta_k = \frac{\|r_{k+1}\|^2}{\|r_k\|^2}, \quad p_{k+1} = -r_{k+1} + \beta_k p_k.$$

The divisions use Lean's convention $a / 0 = 0$, so a step of the algorithm in exact arithmetic
also needs both denominators to be nonzero; see
`ConnGouldToint.Chapter05.ConjugateDirectionStepDefined`.

**Reading.** The totalized recurrence also yields values when a denominator vanishes.
-/
theorem algorithm_5_1_1_succ (H : E →ₗ[ℝ] E) (r₀ : E) (k : ℕ) :
    let current := algorithm_5_1_1 H r₀ k
    let α := ‖current.1‖ ^ 2 / ⟪current.2, H current.2⟫
    let r' := current.1 + α • H current.2
    let β := ‖r'‖ ^ 2 / ‖current.1‖ ^ 2
    algorithm_5_1_1 H r₀ (k + 1) = (r', -r' + β • current.2) :=
  Function.iterate_succ_apply' _ _ _

private theorem conjugateDirectionStep_eq_CG_step (H : E →ₗ[ℝ] E) (state : CG.State E) :
    conjugateDirectionStep H (-state.r, state.p) = (-(CG.step H state).r, (CG.step H state).p) := by
  let α : ℝ := ‖-state.r‖ ^ 2 / ⟪state.p, H state.p⟫
  let r' := -state.r + α • H state.p
  let β : ℝ := ‖r'‖ ^ 2 / ‖-state.r‖ ^ 2
  have hα : CG.alpha H state = α := by
    rw [CG.alpha, real_inner_self_eq_norm_sq, ← real_inner_comm (H state.p) state.p]
    simp only [α, norm_neg]
  have hr : -(CG.step H state).r = r' := by
    rw [CG.step_r, hα, neg_sub, sub_eq_add_neg, add_comm]
  have hβ : CG.beta H state = β := by
    rw [CG.beta, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    simp only [β, ← hr, norm_neg]
  change (r', -r' + β • state.p) = (-(CG.step H state).r, (CG.step H state).p)
  rw [CG.step_p, hβ, ← hr, neg_neg]

/-- **Algorithm 5.1.1** of [conn2000trust], relation to conjugate gradients. For a linear operator
$H$ on $E$ and $r_0 \in E$, the state $(r_k, p_k)$ of Algorithm 5.1.1 is $(-\rho_k, d_k)$, where
$\rho_k$ and $d_k$ are the residual and the direction of the conjugate gradient method for
$Hx = -r_0$ from $x_0 = 0$.

The conjugate gradient states are `Krylov.CG.iterate`; their residual has the opposite sign to
the gradient.

**Reading.** State-by-state relation in inner-product spaces and at all indices.
-/
theorem algorithm_5_1_1_eq_projectedCG (H : E →ₗ[ℝ] E) (r₀ : E) (k : ℕ) :
    algorithm_5_1_1 H r₀ k =
      (-(CG.iterate H (-r₀) 0 k).r, (CG.iterate H (-r₀) 0 k).p) := by
  induction k with
  | zero => simp [algorithm_5_1_1_zero]
  | succ k ih =>
    change (conjugateDirectionStep H)^[k + 1] (r₀, -r₀) = _
    rw [Function.iterate_succ_apply', ← algorithm_5_1_1, ih, CG.iterate_succ]
    exact conjugateDirectionStep_eq_CG_step _ _

/-- **Algorithm 5.1.1** of [conn2000trust], division conditions. A state $(r, p)$ **admits a defined
step** if $r \neq 0$ and $\langle p, Hp \rangle \neq 0$, so that both divisions of the conjugate
direction step are divisions by nonzero numbers. -/
def ConjugateDirectionStepDefined (H : E →ₗ[ℝ] E) (state : E × E) : Prop :=
  state.1 ≠ 0 ∧ ⟪state.2, H state.2⟫ ≠ 0

/-- **Algorithm 5.1.1** of [conn2000trust], division conditions. A state $(r, p)$ admits a defined
step if and only if the denominators of (5.1.23) and (5.1.25) are nonzero:
$\langle p, Hp \rangle \neq 0$ and $\|r\|^2 \neq 0$. -/
theorem conjugateDirectionStepDefined_iff (H : E →ₗ[ℝ] E) (state : E × E) :
    ConjugateDirectionStepDefined H state ↔
      ⟪state.2, H state.2⟫ ≠ 0 ∧ ‖state.1‖ ^ 2 ≠ 0 := by
  rw [ConjugateDirectionStepDefined, pow_ne_zero_iff two_ne_zero, norm_ne_zero_iff, and_comm]

/-- **Algorithm 5.1.1** of [conn2000trust], conjugacy. Let $H$ be symmetric positive definite, and
let $r_0 \in E$. Then the directions of Algorithm 5.1.1 are conjugate:
$\langle p_i, H p_j \rangle = 0$ for all $i \neq j$.

**Reading.** Conjugacy in a real inner-product space under symmetric coercivity.
-/
theorem algorithm_5_1_1_conjugate {H : E →ₗ[ℝ] E} (hH : H.IsSymmetricCoercive)
    (r₀ : E) {i j : ℕ} (hij : i ≠ j) :
    ⟪(algorithm_5_1_1 H r₀ i).2, H (algorithm_5_1_1 H r₀ j).2⟫ = 0 := by
  rw [algorithm_5_1_1_eq_projectedCG, algorithm_5_1_1_eq_projectedCG, real_inner_comm]
  exact CG.inner_apply_direction_eq_zero (-r₀) 0 hH hij.symm

/-- **Algorithm 5.1.1** of [conn2000trust], positive-curvature case. Let $H$ be symmetric positive
definite, and let $r_0 \in E$. Then the state $(r_k, p_k)$ admits a defined step if and only if
$r_k \neq 0$.

**Reading.** Coercivity means a nonzero residual is exactly the condition for another defined step.
-/
theorem algorithm_5_1_1_stepDefined_iff {H : E →ₗ[ℝ] E} (hH : H.IsSymmetricCoercive)
    (r₀ : E) (k : ℕ) :
    ConjugateDirectionStepDefined H (algorithm_5_1_1 H r₀ k) ↔
      (algorithm_5_1_1 H r₀ k).1 ≠ 0 := by
  refine ⟨fun h ↦ h.1, fun hr ↦ ⟨hr, ?_⟩⟩
  rw [algorithm_5_1_1_eq_projectedCG] at hr ⊢
  have hr' : (CG.iterate H (-r₀) 0 k).r ≠ 0 := by simpa only [Prod.fst, neg_ne_zero] using hr
  have hpos := CG.re_inner_apply_direction_pos (-r₀) 0 hH hr'
  rw [real_inner_comm]
  exact ne_of_gt hpos

/-- **Algorithm 5.1.2** of [conn2000trust] (conjugate gradient method). For a linear operator $H$ on
$E$, $c \in E$ and a starting point $x_0$, the $k$-th state consists of the iterate $x_k$, the
residual $-g_k = -(Hx_k + c)$ and the search direction $p_k$ of the conjugate gradient method
for $Hx = -c$.

The state is `Krylov.CG.iterate H (-c) x₀ k`. It stores the residual $-g_k$ in place of the
gradient $g_k$ of the source.

**Reading.** Totalized CG state with reversed residual sign.
-/
noncomputable abbrev algorithm_5_1_2 (H : E →ₗ[ℝ] E) (c x₀ : E) (k : ℕ) : CG.State E :=
  CG.iterate H (-c) x₀ k

/-- **Algorithm 5.1.3** of [conn2000trust]. Let $E$ and $F$ be real Hilbert spaces, let
$R : E \to F$ be an isomorphism with inverse $S = R^{-1}$, and let $H$ be a linear operator on
$E$ and $c \in E$. Algorithm 5.1.3 applies the conjugate gradient method (Algorithm 5.1.2) from
$\bar{x}_0 \in F$ to the transformed quadratic
$$\bar{q}(\bar{x}) = \langle S^* c, \bar{x} \rangle + \tfrac{1}{2} \langle \bar{x}, S^* H S
  \bar{x} \rangle,$$
which is $q(S \bar{x})$.

**Reading.** Transformation by a continuous linear equivalence between Hilbert spaces.
-/
noncomputable abbrev algorithm_5_1_3 {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (R : E ≃L[ℝ] F) (H : E →ₗ[ℝ] E) (c : E) (xbar₀ : F) (k : ℕ) : CG.State F :=
  let S := R.symm.toContinuousLinearMap
  algorithm_5_1_2 (S.adjoint.toLinearMap ∘ₗ H ∘ₗ S.toLinearMap) (S.adjoint c) xbar₀ k

/-- **Algorithm 5.1.3** of [conn2000trust], initialization. With $S = R^{-1}$ and the transformed
gradient $\bar{g}_0 = S^*(H S \bar{x}_0 + c)$, the initial state is
$(\bar{x}_0, -\bar{g}_0, -\bar{g}_0)$: the iterate, the residual and the direction.

**Reading.** Uses the inverse map and its adjoint for transformed initialization.
-/
theorem algorithm_5_1_3_zero {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (R : E ≃L[ℝ] F) (H : E →ₗ[ℝ] E) (c : E) (xbar₀ : F) :
    let S := R.symm.toContinuousLinearMap
    let gbar₀ := S.adjoint (H (S xbar₀) + c)
    algorithm_5_1_3 R H c xbar₀ 0 = ⟨xbar₀, -gbar₀, -gbar₀⟩ := by
  simp [algorithm_5_1_3, CG.init, map_add, sub_eq_add_neg, add_comm]

/-- **Algorithm 5.1.3** of [conn2000trust], equations (5.1.46)–(5.1.50). With $S = R^{-1}$,
$\bar{H} = S^* H S$ and the state $(\bar{x}_k, -\bar{g}_k, \bar{p}_k)$, the next state is
$(\bar{x}_k + \alpha_k \bar{p}_k, -\bar{g}_{k+1}, -\bar{g}_{k+1} + \beta_k \bar{p}_k)$, where
$$\alpha_k = \frac{\|\bar{g}_k\|^2}{\langle \bar{p}_k, \bar{H} \bar{p}_k \rangle}, \qquad
  \bar{g}_{k+1} = \bar{g}_k + \alpha_k \bar{H} \bar{p}_k, \qquad \beta_k =
  \frac{\|\bar{g}_{k+1}\|^2}{\|\bar{g}_k\|^2}.$$

The gradients $\bar{g}_k$ have the sign of the source; the state stores $-\bar{g}_k$.

**Reading.** Transformed update via adjoints and totalized denominators.
-/
theorem algorithm_5_1_3_succ {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (R : E ≃L[ℝ] F) (H : E →ₗ[ℝ] E) (c : E) (xbar₀ : F) (k : ℕ) :
    let S := R.symm.toContinuousLinearMap
    let A := S.adjoint.toLinearMap ∘ₗ H ∘ₗ S.toLinearMap
    let s := algorithm_5_1_3 R H c xbar₀ k
    let g := -s.r
    let α := ‖g‖ ^ 2 / ⟪s.p, A s.p⟫
    let g' := g + α • A s.p
    let β := ‖g'‖ ^ 2 / ‖g‖ ^ 2
    algorithm_5_1_3 R H c xbar₀ (k + 1) = ⟨s.x + α • s.p, -g', -g' + β • s.p⟩ := by
  intro S A s g α g' β
  change CG.iterate A (-(S.adjoint c)) xbar₀ (k + 1) = _
  rw [CG.iterate_succ]
  change CG.step A s = _
  have hα : CG.alpha A s = α := by
    rw [CG.alpha, real_inner_self_eq_norm_sq, real_inner_comm s.p (A s.p)]
    simp only [α, g, norm_neg]
  have hr : (CG.step A s).r = -g' := by
    rw [CG.step_r, hα]
    change s.r - α • A s.p = -(-s.r + α • A s.p)
    abel
  have hβ : CG.beta A s = β := by
    rw [CG.beta, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hr]
    simp [β, g]
  cases he : CG.step A s with
  | mk x r p =>
    have hx := CG.step_x A s
    have hp := CG.step_p A s
    rw [he, hα] at hx
    rw [hβ, hr, he] at hp
    rw [he] at hr
    simp only at hx hr hp
    rw [hx, hr, hp]

/-- **Equation (5.1.53)** of [conn2000trust]. For an isomorphism $R : E \to F$ of real Hilbert
spaces, the **preconditioner induced by the transformation** is $M = R^* R$.

**Reading.** Uses the Hilbert-space adjoint factorization R*R.
-/
noncomputable def transformedCGPreconditioner {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (R : E ≃L[ℝ] F) : E →L[ℝ] E :=
  R.toContinuousLinearMap.adjoint.comp R.toContinuousLinearMap

/-- **Equation (5.1.53)** of [conn2000trust], inverse. For an isomorphism $R : E \to F$ of real
Hilbert spaces with $S = R^{-1}$, the operator $S S^* = R^{-1} R^{-*}$ inverts $M = R^* R$:
$M(S S^* x) = x$ for all $x \in E$.

Transformed conjugate gradients apply $M^{-1}$ in this form.

**Reading.** Uses the inverse map and adjoint in the two-sided inverse identity.
-/
theorem transformedCGPreconditioner_apply_inverse {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (R : E ≃L[ℝ] F) (x : E) :
    let S := R.symm.toContinuousLinearMap
    transformedCGPreconditioner R (S (S.adjoint x)) = x := by
  let S := R.symm.toContinuousLinearMap
  let L := R.toContinuousLinearMap
  have hSL : S.comp L = ContinuousLinearMap.id ℝ E :=
    ContinuousLinearMap.ext R.symm_apply_apply
  have h := congrArg ContinuousLinearMap.adjoint hSL
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at h
  change L.adjoint (R (R.symm (S.adjoint x))) = x
  rw [R.apply_symm_apply]
  exact congrArg (fun T : E →L[ℝ] E => T x) h

/-- **Algorithm 5.1.4** of [conn2000trust] (preconditioned conjugate gradient method). For linear
operators $H$ and $M^{-1}$ on $E$, $c \in E$ and a starting point $x_0$, the $k$-th state
consists of the iterate $x_k$, the residual $-g_k = -(Hx_k + c)$ and the search direction $p_k$
of the preconditioned conjugate gradient method for $Hx = -c$ with the inverse preconditioner
$M^{-1}$.

The state is `Krylov.PCG.iterate H Minv (-c) x₀ k`. It stores $-g_k$ in place of $g_k$, and it
applies $M^{-1}$ to the residual when the preconditioned gradient is needed.

**Reading.** Total PCG state over arbitrary inner-product space with explicit inverse map.
-/
noncomputable abbrev algorithm_5_1_4 (H Minv : E →ₗ[ℝ] E) (c x₀ : E) (k : ℕ) : PCG.State E :=
  PCG.iterate H Minv (-c) x₀ k

/-- **Lemma 5.1.1** of [conn2000trust]. Let $E$ and $F$ be real Hilbert spaces, let $H$ be a bounded
symmetric operator on $E$, let $S : F \to E$ be bounded linear, and suppose that $S^* H S$ is
invertible. Let $c, x \in E$ and
$$x_S = x - S (S^* H S)^{-1} S^* (Hx + c).$$
Then

* $x_S$ lies in the affine subspace $x + \operatorname{range} S$,
* $S^* (H x_S + c) = 0$,
* $x_S$ is the only point $x + Sz$ with $S^* (H(x + Sz) + c) = 0$, and
* if $\langle z, S^* H S z \rangle > 0$ for every $z \neq 0$, then $x_S$ minimizes $q$ over
  $x + \operatorname{range} S$.

The invertible operator $S^* H S$ is a continuous linear equivalence `B` with
`B z = S.adjoint (H (S z))`.

**Reading.** Reduced critical point and minimum use Hilbert-space maps and an explicit inverse.
-/
theorem lemma_5_1_1 [CompleteSpace E] {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (H : E →L[ℝ] E) (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (S : F →L[ℝ] E) (B : F ≃L[ℝ] F) (hB : ∀ z, B z = S.adjoint (H (S z)))
    (c x : E) :
    let xS := x - S (B.symm (S.adjoint (H x + c)))
    xS ∈ Set.range (fun z : F => x + S z) ∧
      S.adjoint (H xS + c) = 0 ∧
      (∀ z : F, S.adjoint (H (x + S z) + c) = 0 → x + S z = xS) ∧
      ((∀ z : F, z ≠ 0 → 0 < ⟪z, B z⟫) →
        IsMinOn (quadraticObjective c H) (Set.range (fun z : F => x + S z)) xS) := by
  let t := B.symm (S.adjoint (H x + c))
  let xS := x - S t
  have hxS : xS = x + S (-t) := by simp [xS, sub_eq_add_neg]
  have hcoord (z : F) : S.adjoint (H (x + S z) + c) = B z + S.adjoint (H x + c) := by
    simp only [map_add, hB]
    abel
  have ht : B t = S.adjoint (H x + c) := B.apply_symm_apply _
  have hcrit : S.adjoint (H xS + c) = 0 := by
    rw [hxS, hcoord, map_neg, ht, neg_add_cancel]
  refine ⟨⟨-t, hxS.symm⟩, hcrit, ?_, ?_⟩
  · intro z hz
    rw [hcoord] at hz
    have heq : z = -t := B.injective (by rw [map_neg, ht]; exact eq_neg_iff_add_eq_zero.mpr hz)
    rw [heq, ← hxS]
  · intro hpos
    rw [isMinOn_iff]
    rintro _ ⟨z, rfl⟩
    have heq : x + S z = xS + S (z + t) := by
      dsimp [xS]
      rw [map_add]
      abel
    have hlin : ⟪c + H xS, S (z + t)⟫ = 0 := by
      rw [add_comm c, ← S.adjoint_inner_left, hcrit, inner_zero_left]
    have hquad : 0 ≤ ⟪S (z + t), H (S (z + t))⟫ := by
      rw [← S.adjoint_inner_right, ← hB]
      by_cases hz : z + t = 0
      · simp [hz]
      · exact (hpos _ hz).le
    change Subproblem.quadModel c H xS ≤ Subproblem.quadModel c H (x + S z)
    rw [heq, Subproblem.quadModel_add hH xS (S (z + t)), hlin, add_zero]
    exact le_add_of_nonneg_right (mul_nonneg (by norm_num) hquad)

/-- **Lemma 5.1.2** of [conn2000trust]. Let $H$ be a bounded symmetric operator on $E$, let
$c, x_0, x_k \in E$, and let $p_0, p_1, \dots$ be vectors in $E$. Let $V_k =
\operatorname{span}\{p_0, \dots, p_{k-1}\}$, and suppose that

* $x_k$ minimizes $q$ over $x_0 + V_k$, and $x_k \in x_0 + V_k$,
* $\langle p_i, H p_k \rangle = 0$ for $i < k$ and $\langle p_k, H p_k \rangle \neq 0$, and
* $\langle v, Hv \rangle \ge 0$ for every $v \in V_{k+1}$.

Let $\sigma = -\langle p_k, H x_k + c \rangle / \langle p_k, H p_k \rangle$ and
$x' = x_k + \sigma p_k$. Then $x' \in x_0 + V_{k+1}$, $Hx' + c = Hx_k + c + \sigma H p_k$,
$\langle p_i, Hx' + c \rangle = 0$ for all $i \le k$, and $x'$ minimizes $q$ over
$x_0 + V_{k+1}$.

The quadratic form need only be nonnegative on $V_{k+1}$, with nonzero curvature in the new
direction $p_k$.

**Reading.** General line update assumes previous minimizer and positive curvature in the added
direction, allowing semidefinite enlarged span.
-/
theorem lemma_5_1_2 (H : E →L[ℝ] E) (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (c x₀ xk : E) (p : ℕ → E) (k : ℕ)
    (hxk : xk - x₀ ∈ Submodule.span ℝ (p '' Set.Iio k))
    (hmin : IsMinOn (quadraticObjective c H)
      {x | x - x₀ ∈ Submodule.span ℝ (p '' Set.Iio k)} xk)
    (hconj : ∀ i < k, ⟪p i, H (p k)⟫ = 0)
    (hcurv : ⟪p k, H (p k)⟫ ≠ 0)
    (hpos : ∀ v ∈ Submodule.span ℝ (p '' Set.Iio (k + 1)), 0 ≤ ⟪v, H v⟫) :
    let σ := -⟪p k, H xk + c⟫ / ⟪p k, H (p k)⟫
    let x' := xk + σ • p k
    x' - x₀ ∈ Submodule.span ℝ (p '' Set.Iio (k + 1)) ∧
      H x' + c = H xk + c + σ • H (p k) ∧
      (∀ i ≤ k, ⟪p i, H x' + c⟫ = 0) ∧
      IsMinOn (quadraticObjective c H)
        {x | x - x₀ ∈ Submodule.span ℝ (p '' Set.Iio (k + 1))} x' := by
  let K := Submodule.span ℝ (p '' Set.Iio k)
  let K' := Submodule.span ℝ (p '' Set.Iio (k + 1))
  let σ := -⟪p k, H xk + c⟫ / ⟪p k, H (p k)⟫
  let x' := xk + σ • p k
  have hp (i : ℕ) (hi : i < k) : p i ∈ K :=
    Submodule.subset_span ⟨i, hi, rfl⟩
  have hnonneg (v : E) (hv : v ∈ K) : 0 ≤ ⟪c + H xk, v⟫ := by
    refine Subproblem.inner_add_apply_nonneg_of_isMinOn hH hmin
      (Filter.Eventually.of_forall fun t => ?_)
    change xk + t • v - x₀ ∈ K
    rw [show xk + t • v - x₀ = (xk - x₀) + t • v by abel]
    exact K.add_mem hxk (K.smul_mem t hv)
  have hgrad (i : ℕ) (hi : i < k) : ⟪p i, H xk + c⟫ = 0 := by
    have hn := hnonneg (-p i) (K.neg_mem (hp i hi))
    rw [inner_neg_right] at hn
    rw [real_inner_comm, add_comm (H xk)]
    exact le_antisymm (neg_nonneg.mp hn) (hnonneg _ (hp i hi))
  have hformula : H x' + c = H xk + c + σ • H (p k) := by
    simp only [x', map_add, map_smul]
    abel
  have horth (i : ℕ) (hi : i ≤ k) : ⟪p i, H x' + c⟫ = 0 := by
    rw [hformula, inner_add_right, real_inner_smul_right]
    rcases hi.lt_or_eq with hik | rfl
    · rw [hgrad i hik, hconj i hik, mul_zero, add_zero]
    · dsimp [σ]
      rw [div_mul_cancel₀ _ hcurv, add_neg_cancel]
  have hsub : K ≤ K' := Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (Nat.le_succ k)))
  have hnew : x' - x₀ ∈ K' := by
    rw [show x' - x₀ = (xk - x₀) + σ • p k by dsimp [x']; abel]
    exact K'.add_mem (hsub hxk) (K'.smul_mem _ (Submodule.subset_span ⟨k, Nat.lt_succ_self k, rfl⟩))
  refine ⟨hnew, hformula, horth, ?_⟩
  have hker : K' ≤ LinearMap.ker ((innerSL ℝ (H x' + c)).toLinearMap) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, hi, rfl⟩
    apply LinearMap.mem_ker.mpr
    change ⟪H x' + c, p i⟫ = 0
    rw [real_inner_comm]
    exact horth i (Nat.le_of_lt_succ hi)
  rw [isMinOn_iff]
  intro y hy
  let d := y - x'
  have hd : d ∈ K' := by
    rw [show d = (y - x₀) - (x' - x₀) by dsimp [d]; abel]
    exact K'.sub_mem hy hnew
  have hlin := hker hd
  change ⟪H x' + c, d⟫ = 0 at hlin
  have heq : y = x' + d := by dsimp [d]; abel
  have hquad := hpos d hd
  change Subproblem.quadModel c H x' ≤ Subproblem.quadModel c H y
  rw [heq, Subproblem.quadModel_add hH x' d, add_comm c, hlin, add_zero]
  exact le_add_of_nonneg_right (mul_nonneg (by norm_num) hquad)

/-- **Lemma 5.1.3** of [conn2000trust]. Let $y_0, y_1, \dots$ and $p_0, p_1, \dots$ be vectors in
$E$, and let $\beta_{j,i} \in \mathbb{R}$. Suppose that $p_0 = y_0$ and
$$p_{j+1} = y_{j+1} + \sum_{i=0}^{j} \beta_{j,i} p_i \quad \text{for } j < k.$$
If $r \in E$ satisfies $\langle p_i, r \rangle = 0$ for all $i \le k$, then
$\langle y_i, r \rangle = 0$ for all $i \le k$.

**Reading.** Same orthogonality implication in an arbitrary real inner-product space.
-/
theorem lemma_5_1_3 (y p : ℕ → E) (β : ℕ → ℕ → ℝ) (k : ℕ) (r : E)
    (h₀ : p 0 = y 0)
    (hrec : ∀ j < k, p (j + 1) = y (j + 1) + ∑ i ∈ Finset.range (j + 1), β j i • p i)
    (horth : ∀ i ≤ k, ⟪p i, r⟫ = 0) :
    ∀ i ≤ k, ⟪y i, r⟫ = 0 := by
  intro i hi
  cases i with
  | zero => rw [← h₀]; exact horth 0 hi
  | succ j =>
    have hsum : ⟪∑ i ∈ Finset.range (j + 1), β j i • p i, r⟫ = 0 := by
      rw [sum_inner]
      apply Finset.sum_eq_zero
      intro i hi'
      have hij := Finset.mem_range.mp hi'
      rw [real_inner_smul_left, horth i (by omega), mul_zero]
    have h := horth (j + 1) hi
    rw [hrec j (by omega), inner_add_left, hsum, add_zero] at h
    exact h

/-- **Equations (5.1.14)–(5.1.15)** of [conn2000trust]. For a linear operator $H$ on $E$, a
direction $p$ and a gradient $r$, the **gradient after an exact line step** is
$$r - \frac{\langle p, r \rangle}{\langle p, Hp \rangle} Hp.$$

It is the gradient of $q$ at $x + \alpha p$ when $r$ is the gradient at $x$ and $\alpha =
-\langle p, r \rangle / \langle p, Hp \rangle$ is the exact step. The division uses Lean's
convention $a / 0 = 0$.

**Reading.** Residual line update totalized at zero curvature.
-/
noncomputable def residualLineStep (H : E →ₗ[ℝ] E) (p r : E) : E :=
  r + (-⟪p, r⟫ / ⟪p, H p⟫) • H p

/-- **Lemma 5.1.4** of [conn2000trust]. Let $H$ be a linear operator on $E$, and let
$p_0, \dots, p_k$ and $r_0, \dots, r_{k+1}$ be vectors in $E$ such that

* $\langle p_i, H p_j \rangle = 0$ for $i < j \le k$,
* $\langle p_j, H p_j \rangle \neq 0$ for $j \le k$, and
* $r_{j+1}$ is the gradient after an exact line step from $r_j$ along $p_j$, for $j \le k$.

Then $\langle p_i, r_{k+1} \rangle = 0$ for all $i \le k$.

The curvatures $\langle p_j, H p_j \rangle$ must be nonzero for the quotients in (5.1.14).

**Reading.** Uses inner-product space and assumes explicitly nonvanishing direction curvatures.
-/
theorem lemma_5_1_4 (H : E →ₗ[ℝ] E) (p r : ℕ → E) (k : ℕ)
    (hconj : ∀ i j, i < j → j ≤ k → ⟪p i, H (p j)⟫ = 0)
    (hnz : ∀ j ≤ k, ⟪p j, H (p j)⟫ ≠ 0)
    (hrec : ∀ j ≤ k, r (j + 1) = residualLineStep H (p j) (r j)) :
    ∀ i ≤ k, ⟪p i, r (k + 1)⟫ = 0 := by
  have horth (j : ℕ) (hj : j ≤ k + 1) : ∀ i < j, ⟪p i, r j⟫ = 0 := by
    induction j with
    | zero => intro i hi; omega
    | succ j ih =>
      intro i hi
      have hj' : j ≤ k := by omega
      rw [hrec j hj', residualLineStep, inner_add_right, real_inner_smul_right]
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hij | heq
      · rw [ih (by omega) i hij, hconj i j hij hj', mul_zero, add_zero]
      · subst i
        rw [div_mul_cancel₀ _ (hnz j hj'), add_neg_cancel]
  intro i hi
  exact horth (k + 1) le_rfl i (Nat.lt_succ_of_le hi)

/-- **Lemma 5.1.5** of [conn2000trust]. Let $H$ be a linear operator on $E$, let $p_0, \dots, p_k$,
$r_0, \dots, r_{k+1}$ and $y$ be vectors in $E$, and suppose that

* $\langle p_k, H p_j \rangle = 0$ for $j < k$,
* $\langle p_j, H p_j \rangle \neq 0$ and $\langle p_j, r_j \rangle \neq 0$ for $j \le k$,
* $r_{j+1}$ is the gradient after an exact line step from $r_j$ along $p_j$, for $j \le k$, and
* $\langle y, r_j \rangle = 0$ for $j \le k$.

Then the vector $y + (\langle y, r_{k+1} \rangle / \langle p_k, r_k \rangle) p_k$ is conjugate
to all directions: for every $j \le k$,
$$\left\langle y + \frac{\langle y, r_{k+1} \rangle}{\langle p_k, r_k \rangle} p_k, H p_j
  \right\rangle = 0.$$

**Correction.** The hypothesis that the pairings $\langle p_j, r_j \rangle$ in (5.1.17) are
nonzero is needed at every $j \le k$, not only at $j = k$. These pairings recover the individual
conjugacy coefficients from the gradient differences.
`ConnGouldToint.Chapter05.counterexample_5_1_5` shows that the lemma fails without them. -/
theorem lemma_5_1_5 (H : E →ₗ[ℝ] E) (p r : ℕ → E) (k : ℕ) (y : E)
    (hconj : ∀ j < k, ⟪p k, H (p j)⟫ = 0)
    (hcurv : ∀ j ≤ k, ⟪p j, H (p j)⟫ ≠ 0)
    (hpair : ∀ j ≤ k, ⟪p j, r j⟫ ≠ 0)
    (hrec : ∀ j ≤ k, r (j + 1) = residualLineStep H (p j) (r j))
    (hy : ∀ j ≤ k, ⟪y, r j⟫ = 0) :
    ∀ j ≤ k, ⟪y + (⟪y, r (k + 1)⟫ / ⟪p k, r k⟫) • p k, H (p j)⟫ = 0 := by
  have hid (j : ℕ) (hj : j ≤ k) :
      ⟪y, r (j + 1)⟫ = (-⟪p j, r j⟫ / ⟪p j, H (p j)⟫) * ⟪y, H (p j)⟫ := by
    rw [hrec j hj, residualLineStep, inner_add_right, real_inner_smul_right, hy j hj, zero_add]
  intro j hj
  rw [inner_add_left, real_inner_smul_left]
  rcases hj.lt_or_eq with hjk | heq
  · have hz := hid j hj
    rw [hy _ (by omega)] at hz
    have hcoef := div_ne_zero (neg_ne_zero.mpr (hpair j hj)) (hcurv j hj)
    have hinner := (mul_eq_zero.mp hz.symm).resolve_left hcoef
    rw [hinner, hconj j hjk, mul_zero, add_zero]
  · subst j
    rw [hid k le_rfl]
    field_simp [hpair k le_rfl, hcurv k le_rfl]
    ring

/-- **Lemma 5.1.5** of [conn2000trust], counterexample. In $\mathbb{R}^3$ with $H = I$, there are
vectors $p_0, p_1, r_0, r_1, r_2, y$ such that $p_0$ and $p_1$ are nonzero and orthogonal, $r_1$
and $r_2$ are the gradients after exact line steps from $r_0$ along $p_0$ and from $r_1$ along
$p_1$, $\langle p_1, r_1 \rangle \neq 0$, $y \notin \operatorname{span}\{p_0, p_1\}$, $\langle
y, r_0 \rangle = \langle y, r_1 \rangle = 0$, and
$$\left\langle y + \frac{\langle y, r_2 \rangle}{\langle p_1, r_1 \rangle} p_1, p_0
  \right\rangle \neq 0.$$

Here $H$ is positive definite and the last coefficient is defined, but
$\langle p_0, r_0 \rangle = 0$. The first line step is zero, so orthogonality to the gradients
gives no information about the first direction.

**Correction.** Example with vanishing earlier pairing refutes the printed conclusion.
-/
theorem counterexample_5_1_5 :
    ∃ p₀ p₁ r₀ r₁ r₂ y : EuclideanSpace ℝ (Fin 3),
      ⟪p₀, p₁⟫ = 0 ∧ ⟪p₀, p₀⟫ ≠ 0 ∧ ⟪p₁, p₁⟫ ≠ 0 ∧
      r₁ = residualLineStep 1 p₀ r₀ ∧ r₂ = residualLineStep 1 p₁ r₁ ∧
      ⟪p₁, r₁⟫ ≠ 0 ∧ y ∉ Submodule.span ℝ {p₀, p₁} ∧
      ⟪y, r₀⟫ = 0 ∧ ⟪y, r₁⟫ = 0 ∧
      ⟪y + (⟪y, r₂⟫ / ⟪p₁, r₁⟫) • p₁, p₀⟫ ≠ 0 := by
  let e := fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)
  have he (i j : Fin 3) : ⟪e i, e j⟫ = if i = j then 1 else 0 := by
    simp [e, EuclideanSpace.inner_single_left, PiLp.single_apply]
  have hnorm (i : Fin 3) : ‖e i‖ = 1 := by simp [e, PiLp.norm_single]
  have hne (i : Fin 3) : e i ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm]; norm_num)
  have hspan : e 0 + e 2 ∉ Submodule.span ℝ {e 0, e 1} := by
    let L := (innerSL ℝ (e 2)).toLinearMap
    have hker : Submodule.span ℝ {e 0, e 1} ≤ LinearMap.ker L := by
      refine Submodule.span_le.mpr ?_
      intro z hz
      rcases Set.mem_insert_iff.mp hz with hz | hz
      · rw [hz]
        exact LinearMap.mem_ker.mpr (by change ⟪e 2, e 0⟫ = 0; norm_num [he])
      · rw [Set.mem_singleton_iff.mp hz]
        exact LinearMap.mem_ker.mpr (by change ⟪e 2, e 1⟫ = 0; norm_num [he])
    intro hy
    have h := LinearMap.mem_ker.mp (hker hy)
    change ⟪e 2, e 0 + e 2⟫ = 0 at h
    norm_num [inner_add_right, he, hne] at h
  refine ⟨e 0, e 1, e 1, e 1, 0, e 0 + e 2, ?_, ?_, ?_, ?_, ?_, ?_, hspan, ?_, ?_, ?_⟩ <;>
    norm_num [residualLineStep, inner_add_left, he, hnorm, hne]

/-- **Theorem 5.1.6** of [conn2000trust]. Let $E$ be finite-dimensional, let $H$ be symmetric
positive definite, and let $Hx_* = -c$. Let $S \subset \mathbb{R}$ be a finite set that contains
every eigenvalue of $H$. Then the conjugate gradient iterate $x_{|S|}$ from any $x_0$ equals
$x_*$.

If $S$ is the set of eigenvalues, $|S|$ is the number of distinct eigenvalues of $H$. A larger
set $S$ gives a weaker bound on the number of steps.

**Reading.** Shows the totalized iterate is exact at the size of any finite set covering the
spectrum.
-/
theorem theorem_5_1_6 [FiniteDimensional ℝ E] {H : E →ₗ[ℝ] E}
    (hH : H.IsSymmetricCoercive) {c x₀ xstar : E} (hstar : H xstar = -c)
    (S : Finset ℝ) (hS : ∀ μ, Module.End.HasEigenvalue H μ → μ ∈ S) :
    (algorithm_5_1_2 H c x₀ S.card).x = xstar := by
  have hmem : -c - H x₀ ∈ LinearMap.range H :=
    ⟨xstar - x₀, by rw [map_sub, hstar]⟩
  have hgrade := Lanczos.grade_le_card_eigenvalues_of_mem_range hH.isSymmetric
    (fun μ _ hμ => hS μ hμ) hmem
  have happly := (CG.isGalerkinIterate (-c) x₀ hH S.card).apply_eq_of_grade_le hgrade
  exact hH.isCoercive.injective (happly.trans hstar.symm)

/-- **Theorem 5.1.7** of [conn2000trust]. Let $H$ be a symmetric operator on $E$ with
$$\lambda_{\min} \|x\|^2 \le \langle Hx, x \rangle \le \lambda_{\max} \|x\|^2 \quad \text{for
  all } x,$$
where $0 < \lambda_{\min} \le \lambda_{\max}$, and let $Hx_* = -c$. Then the conjugate gradient
iterates from $x_0$ satisfy, with $\kappa = \lambda_{\max} / \lambda_{\min}$,
$$\|x_k - x_*\|_H \le 2 \left( \frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1} \right)^k \|x_0 -
  x_*\|_H.$$

**Reading.** The bound is a product, not a ratio of the two errors, so that it also covers an
exact initial iterate $x_0 = x_*$.

When $\lambda_{\min}$ and $\lambda_{\max}$ are the extreme eigenvalues, $\kappa$ is the spectral
condition number of $H$. The bounds are `LinearMap.IsSymmetricBoundedBy H lmin lmax`, and the
$H$-norm is `energyNorm H`. -/
theorem theorem_5_1_7 {H : E →ₗ[ℝ] E} {c x₀ xstar : E} (hstar : H xstar = -c)
    {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin ≤ lmax)
    (hH : H.IsSymmetricBoundedBy lmin lmax) (k : ℕ) :
    energyNorm H ((algorithm_5_1_2 H c x₀ k).x - xstar) ≤
      2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ k *
        energyNorm H (x₀ - xstar) := by
  rw [energyNorm_sub_comm H _ xstar, energyNorm_sub_comm H x₀ xstar]
  exact IsGalerkinIterate.energyNorm_error_le hl hll hH
    (CG.isGalerkinIterate (-c) x₀ (hH.isSymmetricCoercive hl) k) hstar

/-- **Corollary 5.1.8** of [conn2000trust]. Let $M$ be symmetric positive definite with inverse
$M^{-1}$, let $H$ be symmetric, and let $Hx_* = -c$. Let $0 < \lambda_{\min} \le \lambda_{\max}$
with
$$\lambda_{\min} \langle Mx, x \rangle \le \langle Hx, x \rangle \le \lambda_{\max} \langle Mx,
  x \rangle \quad \text{for all } x.$$
Then the preconditioned conjugate gradient iterates from $x_0$ satisfy, with
$\kappa = \lambda_{\max} / \lambda_{\min}$,
$$\|x_k - x_*\|_H \le 2 \left( \frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1} \right)^k \|x_0 -
  x_*\|_H.$$

**Reading.** The bound is a product, not a ratio of the two errors, so that it also covers an
exact initial iterate $x_0 = x_*$.

When $\lambda_{\min}$ and $\lambda_{\max}$ are the extreme generalized eigenvalues of the pair
$(H, M)$, $\kappa$ is the spectral condition number of $M^{-1} H$. The preconditioner is
`Krylov.IsPreconditioner M Minv`. -/
theorem corollary_5_1_8 {H M Minv : E →ₗ[ℝ] E} (hM : IsPreconditioner M Minv)
    (hH : H.IsSymmetric) {c x₀ xstar : E} (hstar : H xstar = -c)
    {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin ≤ lmax)
    (hmin : ∀ x : E, lmin * ⟪M x, x⟫ ≤ ⟪H x, x⟫)
    (hmax : ∀ x : E, ⟪H x, x⟫ ≤ lmax * ⟪M x, x⟫) (k : ℕ) :
    energyNorm H ((algorithm_5_1_4 H Minv c x₀ k).x - xstar) ≤
      2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ k *
        energyNorm H (x₀ - xstar) := by
  rw [energyNorm_sub_comm H _ xstar, energyNorm_sub_comm H x₀ xstar]
  exact PCG.energyNorm_error_le hM hH hl hll hmin hmax hstar k

/-- **Corollary 5.1.9** of [conn2000trust]. Let $E$ be finite-dimensional, let $M$ be symmetric
positive definite with inverse $M^{-1}$, let $H$ be symmetric with $l \langle Mx, x \rangle \le
\langle Hx, x \rangle$ for all $x$ and some $l > 0$, and let $Hx_* = -c$. Let
$S \subset \mathbb{R}$ be a finite set that contains every eigenvalue of $M^{-1} H$. Then the
preconditioned conjugate gradient iterate $x_{|S|}$ from any $x_0$ equals $x_*$.

**Reading.** Exact totalized iterate at the size of a set covering the preconditioned spectrum.
-/
theorem corollary_5_1_9 [FiniteDimensional ℝ E] {H M Minv : E →ₗ[ℝ] E}
    (hM : IsPreconditioner M Minv) (hH : H.IsSymmetric)
    {l : ℝ} (hl : 0 < l) (hlo : ∀ x : E, l * ⟪M x, x⟫ ≤ ⟪H x, x⟫)
    {c x₀ xstar : E} (hstar : H xstar = -c)
    (S : Finset ℝ) (hS : ∀ μ, Module.End.HasEigenvalue (Minv ∘ₗ H) μ → μ ∈ S) :
    (algorithm_5_1_4 H Minv c x₀ S.card).x = xstar := by
  let B := hM.energyEnd (Minv ∘ₗ H)
  have hB : B.IsSymmetricCoercive := hM.isSymmetricCoercive_energyEnd H hH hl hlo
  have hS' (μ : ℝ) (hμ : Module.End.HasEigenvalue B μ) : μ ∈ S := by
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    obtain ⟨u, rfl⟩ := hM.toEnergy.surjective v
    have hu : u ≠ 0 := by
      intro hu
      exact (Module.End.hasEigenvector_iff.mp hv).2 (by simp [hu])
    have heq := hv.apply_eq_smul
    change hM.energyEnd (Minv ∘ₗ H) (hM.toEnergy u) = μ • hM.toEnergy u at heq
    rw [IsPreconditioner.energyEnd_apply, ← map_smul] at heq
    have huv : Module.End.HasEigenvector (Minv ∘ₗ H) μ u :=
      Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr (hM.toEnergy.injective heq), hu⟩
    exact hS μ (Module.End.hasEigenvalue_of_hasEigenvector huv)
  have hstar' : B (hM.toEnergy xstar) = -hM.toEnergy (Minv c) := by
    simp [B, LinearMap.comp_apply, hstar]
  have h := theorem_5_1_6 hB hstar' S hS' (x₀ := hM.toEnergy x₀)
  apply hM.toEnergy.injective
  rw [PCG.toEnergy_iterate_x H Minv (-c) x₀ hM S.card]
  simpa only [B, map_neg] using h

end ConnGouldToint.Chapter05
