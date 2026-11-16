/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Complexity.Basic
import Numlib.Optimization.Complexity.SlowExample.SeparatedJets
import Numlib.Optimization.ModelBased.QuadraticModel
import NumlibSurface.CartisGouldToint.Chapter01.Section01
import NumlibSurface.CartisGouldToint.Chapter02.Section01

/-!
# Cartis, Gould and Toint, Section 3.1: Slow convergence of Newton's method

This module formalizes §3.1 of [cartis2022evaluation] for functions
$f : \mathbb{R}^n \to \mathbb{R}$. It states the assumptions f.C2 ($f$ is twice continuously
differentiable) and f.HL ($f$ has a Lipschitz continuous Hessian) that the second-order methods of
Chapter 3 use. It then defines Newton's method (Algorithm 3.1.1), whose step solves the Newton
equation (3.1.1)
$$\nabla^2 f(x_k) s_k = -\nabla f(x_k).$$
When $\nabla^2 f(x_k)$ is positive definite, this step is the unique minimizer of the quadratic
Taylor model $T_{f,2}(x_k, \cdot)$ (3.1.2).

Theorem 3.1.1 shows that Newton's method can be slow: there is a function
$f : \mathbb{R}^2 \to \mathbb{R}$ that satisfies f.Bb, f.gL and f.HL with constants independent of
$\epsilon_1$, on which every Newton run from the origin has positive definite Hessians and stops
only at iteration $\lceil \epsilon_1^{-2} \rceil$. So the method needs
$\lceil \epsilon_1^{-2} \rceil + 1$ evaluations of $f$, $\nabla f$ and $\nabla^2 f$. The function
interpolates the data (3.1.4)–(3.1.6) with the smooth gluing construction of
`Numlib.Optimization.Complexity.SlowExample.SeparatedJets`.

## Main definitions

* Assumption f.C2, `CartisGouldToint.Chapter03.AssumptionC2`: $f$ is twice continuously
  differentiable.
* Assumption f.HL, `CartisGouldToint.Chapter03.AssumptionHL`: $f$ is $C^2$ with an $L$-Lipschitz
  Hessian (3.1.3), $L = L_{f,2} \ge 1$.
* (3.1.1), `CartisGouldToint.Chapter03.IsNewtonStep`: the Newton equation
  $\nabla^2 f(x) s = -\nabla f(x)$.
* Algorithm 3.1.1, `CartisGouldToint.Chapter03.algorithm_3_1_1`: Newton's method as a predicate on
  the sequences of a run.

## Main results

* (3.1.2), `CartisGouldToint.Chapter03.isNewtonStep_iff_isMinOn`: when $\nabla^2 f(x)$ is positive
  definite, the Newton step is unique and is the unique global minimizer of $T_{f,2}(x, \cdot)$.
* (3.1.4)–(3.1.7), `CartisGouldToint.Chapter03.NewtonSlow.exists_example`: a smooth function on
  $\mathbb{R}^2$ with bounded derivatives interpolates the data of the slow example.
* Theorem 3.1.1, `CartisGouldToint.Chapter03.theorem_3_1_1`: every Newton run from the origin on
  this function stops exactly at iteration $\lceil \epsilon_1^{-2} \rceil$.

## Conventions

* $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`. The Hessian $\nabla^2 f(x)$ is the bilinear form
  `iteratedFDeriv ℝ 2 f x`, or the operator `Optimization.hessianOperator f x`, and its norm is the
  operator norm of bilinear forms.
* $\lambda_{\min}[\nabla^2 f(x)]$ is `CartisGouldToint.Chapter01.hessianMinEig f x`.

## Implementation notes

* f.HL is the anchored smoothness assumption `LipschitzDerivsAnchored` of order $2$ on the whole
  space, together with $L \ge 1$.
* The example $f_{SN}$ of (3.1.7) is built from the data (3.1.4)–(3.1.6) with the smooth gluing
  `Optimization.exists_contDiff_interpolating_separated_jets` in place of the book's
  piecewise-polynomial bump. The data are interpolated at $x_0, \dots, x_{k_\epsilon}$ with
  $k_\epsilon = \lceil \epsilon_1^{-2} \rceil$. The construction
  `CartisGouldToint.Chapter03.NewtonSlow.exists_example` is reused for Theorem 3.2.2.

## Deviations from the source

* **Theorem 3.1.1** (correction). For the data (3.1.4) the claim $\|\nabla f(x_k)\| > \epsilon_1$
  can fail at $k = k_\epsilon$. The example prescribes $\nabla f(x_{k_\epsilon}) = 0$, so that every
  Newton run from the origin stops exactly at $k_\epsilon = \lceil \epsilon_1^{-2} \rceil$. See
  `CartisGouldToint.Chapter03.theorem_3_1_1`.
-/

open Set Finset Optimization
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter03

variable {n : ℕ}

/-! ### Assumptions f.C2 and f.HL -/

/-- **Assumption f.C2** of [cartis2022evaluation] (§3.1). A function
$f : \mathbb{R}^n \to \mathbb{R}$ satisfies f.C2 if it is twice continuously differentiable. -/
def AssumptionC2 (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ContDiff ℝ 2 f

/-- A function satisfies f.C2 if and only if it is twice continuously differentiable. -/
theorem assumptionC2_iff {f : EuclideanSpace ℝ (Fin n) → ℝ} : AssumptionC2 f ↔ ContDiff ℝ 2 f :=
  Iff.rfl

/-- **Assumption f.HL** of [cartis2022evaluation] (§3.1). A function
$f : \mathbb{R}^n \to \mathbb{R}$ satisfies f.HL with constant $L = L_{f,2}$ if $f$ is twice
continuously differentiable, $L \ge 1$, and the Hessian is Lipschitz continuous with constant
$L$ (3.1.3):
$$\|\nabla^2 f(x) - \nabla^2 f(y)\| \le L \|x - y\| \quad \text{for all } x, y \in
  \mathbb{R}^n.$$

The norm is the operator norm of bilinear forms. The definition is the anchored smoothness
assumption `LipschitzDerivsAnchored` of order $2$ on the whole space, together with $L \ge 1$.
The form (3.1.3) is `CartisGouldToint.Chapter03.AssumptionHL.lipschitz`, and its converse is
`CartisGouldToint.Chapter03.AssumptionHL.of_lipschitz`. -/
abbrev AssumptionHL (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) : Prop :=
  LipschitzDerivsAnchored f univ univ 2 2 (fun _ => L) ∧ 1 ≤ L

namespace AssumptionHL

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}

/-- Under f.HL, $f$ is twice continuously differentiable. -/
theorem contDiff (h : AssumptionHL f L) : ContDiff ℝ 2 f :=
  h.1.contDiff

/-- The constant of f.HL satisfies $L_{f,2} \ge 1$. -/
theorem one_le (h : AssumptionHL f L) : 1 ≤ L :=
  h.2

/-- Under f.HL with constant $L$, the second derivative of $f$ is $L$-Lipschitz on $\mathbb{R}^n$ in
the sense of `IteratedFDerivLipschitzOn`. -/
theorem iteratedFDerivLipschitzOn (h : AssumptionHL f L) :
    IteratedFDerivLipschitzOn f 2 L univ :=
  (lipschitzDerivsAnchored_univ_top_iff.1 h.1).2

/-- Under f.HL with constant $L$, the Hessian is $L$-Lipschitz (3.1.3): $\|\nabla^2 f(x) - \nabla^2
f(y)\| \le L \|x - y\|$ for all $x, y$. -/
theorem lipschitz (h : AssumptionHL f L) (x y : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ L * ‖x - y‖ :=
  iteratedFDerivLipschitzOn_iff.1 h.iteratedFDerivLipschitzOn x (mem_univ _) y (mem_univ _)

/-- A twice continuously differentiable $f$ whose second derivative is $L$-Lipschitz on
$\mathbb{R}^n$ in the sense of `IteratedFDerivLipschitzOn`, with $L \ge 1$, satisfies f.HL with
constant $L$. -/
theorem of_iteratedFDerivLipschitzOn (hf : ContDiff ℝ 2 f) (hL1 : 1 ≤ L)
    (hL : IteratedFDerivLipschitzOn f 2 L univ) : AssumptionHL f L :=
  ⟨lipschitzDerivsAnchored_univ_top_iff.2 ⟨hf, hL⟩, hL1⟩

/-- A twice continuously differentiable $f$ with $\|\nabla^2 f(x) - \nabla^2 f(y)\| \le L \|x - y\|$
for all $x, y$ and $L \ge 1$ satisfies f.HL with constant $L$. -/
theorem of_lipschitz (hf : ContDiff ℝ 2 f) (hL1 : 1 ≤ L)
    (hL : ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ L * ‖x - y‖) :
    AssumptionHL f L :=
  of_iteratedFDerivLipschitzOn hf hL1 (iteratedFDerivLipschitzOn_iff.2 fun x _ y _ => hL x y)

/-- Assumption f.HL implies f.C2. -/
theorem assumptionC2 (h : AssumptionHL f L) : AssumptionC2 f :=
  h.contDiff

/-- The constant of f.HL is nonnegative. -/
theorem nonneg (h : AssumptionHL f L) : 0 ≤ L :=
  zero_le_one.trans h.one_le

/-- The constant of f.HL is positive. -/
theorem pos (h : AssumptionHL f L) : 0 < L :=
  zero_lt_one.trans_le h.one_le

/-- Under f.HL, $f$ is twice continuously differentiable at every point. -/
theorem contDiffAt (h : AssumptionHL f L) (x : EuclideanSpace ℝ (Fin n)) :
    ContDiffAt ℝ 2 f x :=
  h.contDiff.contDiffAt

/-- If $f$ satisfies f.HL with constant $L$ and $L \le L'$, then $f$ satisfies f.HL with constant
$L'$. -/
theorem mono (h : AssumptionHL f L) {L' : ℝ} (hL : L ≤ L') : AssumptionHL f L' :=
  ⟨h.1.mono_const fun _ _ => hL, h.2.trans hL⟩

end AssumptionHL

/-- A three times continuously differentiable $f$ with $\|\nabla^3 f(x)\| \le L$ for all $x$ and
$L \ge 1$ satisfies f.HL with constant $L$. This is the remark after (3.1.3) of
[cartis2022evaluation]. -/
theorem AssumptionHL.of_norm_iteratedFDeriv_three_le {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    (hf : ContDiff ℝ 3 f) (hL : 1 ≤ L) (hb : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ L) :
    AssumptionHL f L :=
  .of_iteratedFDerivLipschitzOn (hf.of_le (by norm_num)) hL
    (iteratedFDerivLipschitzOn_of_norm_le convex_univ (fun y _ => hf.contDiffAt) fun x _ => hb x)

/-- Let $f$ be three times continuously differentiable, and let $|f(y)| \le B$ and
$\|\nabla^j f(y)\| \le B$ for all $y$ and all $j \le 3$. Then $f$ satisfies f.Bb with
$f_{\mathrm{low}} = -B$, and f.gL and f.HL with the constant $\max(B, 1)$. -/
theorem assumptions_of_bounded {f : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ}
    (hf : ContDiff ℝ 3 f) (hb : ∀ y, |f y| ≤ B ∧ ∀ j ≤ 3, ‖iteratedFDeriv ℝ j f y‖ ≤ B) :
    Chapter02.AssumptionBb f (-B) ∧ Chapter02.AssumptionGL f (max B 1) ∧
      AssumptionHL f (max B 1) :=
  ⟨fun y => by linarith [neg_abs_le (f y), (hb y).1],
    .of_iteratedFDerivLipschitzOn (hf.of_le (by norm_num)) (le_max_right _ _)
      (iteratedFDerivLipschitzOn_of_norm_le convex_univ
        (fun y _ => (hf.of_le (by norm_num)).contDiffAt)
        fun x _ => ((hb x).2 2 (by norm_num)).trans (le_max_left _ _)),
    AssumptionHL.of_norm_iteratedFDeriv_three_le hf (le_max_right _ _)
      fun x => ((hb x).2 3 le_rfl).trans (le_max_left _ _)⟩

/-! ### Newton's method -/

/-- The **Newton equation** (3.1.1) of [cartis2022evaluation]. A step $s \in \mathbb{R}^n$ solves it
at $x$ if $\nabla^2 f(x) s = -\nabla f(x)$, written with the Hessian as a bilinear form:
$$\nabla^2 f(x)[s, v] = -\langle \nabla f(x), v \rangle \quad \text{for all } v \in
  \mathbb{R}^n.$$
-/
def IsNewtonStep (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ v, iteratedFDeriv ℝ 2 f x ![s, v] = -⟪gradient f x, v⟫

section NewtonStep

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x s : EuclideanSpace ℝ (Fin n)}

/-- If $f$ is twice continuously differentiable at $x$, a step $s$ solves the Newton equation if and
only if $\nabla^2 f(x) s = -\nabla f(x)$ for the Hessian operator
`Optimization.hessianOperator f x`. -/
theorem isNewtonStep_iff (hf : ContDiffAt ℝ 2 f x) :
    IsNewtonStep f x s ↔ hessianOperator f x s = -gradient f x := by
  have hsym : ∀ v, iteratedFDeriv ℝ 2 f x ![s, v] = ⟪hessianOperator f x s, v⟫ := fun v => by
    rw [← inner_hessianOperator_apply hf]
    exact (hessianOperator_isSymmetric hf s v).symm
  simp only [IsNewtonStep, hsym]
  constructor
  · intro h
    refine ext_inner_right ℝ fun v => ?_
    rw [h v, inner_neg_left]
  · intro h v
    rw [h, inner_neg_left]

/-- If $f$ is twice continuously differentiable at $x$ and $s$ solves the Newton equation, then
$T_{f,2}(x, s + d) - T_{f,2}(x, s) = \frac12 \nabla^2 f(x)[d, d]$ for every $d$. -/
theorem taylorPolynomial_two_add_sub (hf : ContDiffAt ℝ 2 f x) (hs : IsNewtonStep f x s)
    (d : EuclideanSpace ℝ (Fin n)) :
    taylorPolynomial f 2 x (s + d) - taylorPolynomial f 2 x s =
      1 / 2 * iteratedFDeriv ℝ 2 f x (fun _ => d) := by
  rw [taylorPolynomial_two_eq_quadModel hf, taylorPolynomial_two_eq_quadModel hf,
    Subproblem.quadModel_def, Subproblem.quadModel_def, apply_diag_eq_vec,
    ← inner_hessianOperator_apply hf]
  have hH := (isNewtonStep_iff hf).1 hs
  have h1 : ⟪s, hessianOperator f x d⟫ = -⟪gradient f x, d⟫ := by
    have hsym := hessianOperator_isSymmetric hf s d
    change ⟪hessianOperator f x s, d⟫ = ⟪s, hessianOperator f x d⟫ at hsym
    rw [← hsym, hH, inner_neg_left]
  have h2 : ⟪d, hessianOperator f x s⟫ = -⟪gradient f x, d⟫ := by
    rw [hH, inner_neg_right, real_inner_comm]
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, inner_add_right, h1, h2]
  ring

/-- **Equation (3.1.2)** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$ be twice
continuously differentiable at $x$ with positive definite Hessian,
$\lambda_{\min}[\nabla^2 f(x)] > 0$, and let $s$ solve the Newton equation (3.1.1) at $x$. Then
for every $s' \in \mathbb{R}^n$:

* $s'$ solves the Newton equation at $x$ if and only if $s' = s$;
* $s'$ is a global minimizer of the quadratic Taylor model $T_{f,2}(x, \cdot)$ if and only if
  $s' = s$.

The Taylor model is `taylorPolynomial f 2 x`, and $\lambda_{\min}$ is
`CartisGouldToint.Chapter01.hessianMinEig`. -/
theorem isNewtonStep_iff_isMinOn (hf : ContDiffAt ℝ 2 f x)
    (hpd : 0 < Chapter01.hessianMinEig f x) (hs : IsNewtonStep f x s)
    (s' : EuclideanSpace ℝ (Fin n)) :
    (IsNewtonStep f x s' ↔ s' = s) ∧
      (IsMinOn (taylorPolynomial f 2 x) univ s' ↔ s' = s) := by
  have hpos : ∀ d, d ≠ 0 → 0 < iteratedFDeriv ℝ 2 f x (fun _ => d) := fun d hd =>
    lt_of_lt_of_le (mul_pos hpd (pow_pos (norm_pos_iff.2 hd) 2))
      (minCurvature_mul_norm_sq_le (iteratedFDeriv ℝ 2 f x) d)
  have hdiff := taylorPolynomial_two_add_sub hf hs
  refine ⟨⟨fun hs' => ?_, fun h => h ▸ hs⟩, ⟨fun hmin => ?_, fun h => h ▸ fun y _ => ?_⟩⟩
  · by_contra hne
    have h1 := (isNewtonStep_iff hf).1 hs
    have h2 := (isNewtonStep_iff hf).1 hs'
    have hd := hpos (s' - s) (sub_ne_zero.2 hne)
    rw [apply_diag_eq_vec, ← inner_hessianOperator_apply hf, map_sub, h1, h2, sub_self,
      inner_zero_right] at hd
    exact lt_irrefl _ hd
  · by_contra hne
    have h1 := hmin (mem_univ s)
    have h2 := hdiff (s' - s)
    rw [add_sub_cancel] at h2
    have := hpos (s' - s) (sub_ne_zero.2 hne)
    simp only [mem_ofPred_eq] at h1
    linarith
  · have := hdiff (y - s)
    rw [add_sub_cancel] at this
    have h0 : 0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => y - s) :=
      (mul_nonneg hpd.le (sq_nonneg _)).trans (minCurvature_mul_norm_sq_le _ _)
    simp only [mem_ofPred_eq]
    linarith

end NewtonStep

/-- **Algorithm 3.1.1** of [cartis2022evaluation] (Newton's method for unconstrained minimization).
Let $f : \mathbb{R}^n \to \mathbb{R}$ and $\epsilon \in \mathbb{R}$. Sequences of iterates $x_k$
and steps $s_k$ form a **Newton run** if $\epsilon > 0$ and, at every iteration $k$ at which the
test $\|\nabla f(x_j)\| \le \epsilon$ has failed for all $j \le k$, the step $s_k$ solves the
Newton equation (3.1.1) at $x_k$ and $x_{k+1} = x_k + s_k$.

The source presumes that the Hessians are positive definite; then $s_k$ is the unique minimizer
of $T_{f,2}(x_k, \cdot)$ (`CartisGouldToint.Chapter03.isNewtonStep_iff_isMinOn`). The run
predicate does not require positive definiteness. -/
structure algorithm_3_1_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) : Prop where
  /-- The accuracy level satisfies $\epsilon > 0$. -/
  ε_pos : 0 < ε
  /-- Step 2: before termination, $s_k$ solves the Newton equation (3.1.1) at $x_k$. -/
  step : UntilHit (fun k => ‖gradient f (x k)‖ ≤ ε) fun k => IsNewtonStep f (x k) (s k)
  /-- Step 3: before termination, the new iterate is $x_{k+1} = x_k + s_k$. -/
  next : UntilHit (fun k => ‖gradient f (x k)‖ ≤ ε) fun k => x (k + 1) = x k + s k

/-! ### The example of Theorem 3.1.1 -/

namespace NewtonSlow

/-- The first unit vector $e_1$ of $\mathbb{R}^2$. -/
noncomputable abbrev e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

/-- The second unit vector $e_2$ of $\mathbb{R}^2$. -/
noncomputable abbrev e₂ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1

/-- The vector $e_1$ has norm $1$. -/
theorem norm_e₁ : ‖e₁‖ = 1 := by simp [e₁]

/-- The vector $e_2$ has norm $1$. -/
theorem norm_e₂ : ‖e₂‖ = 1 := by simp [e₂]

/-- The inner product $\langle e_1, e_1 \rangle$ is $1$. -/
theorem inner_e₁_e₁ : ⟪e₁, e₁⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_e₁, one_pow]

/-- The inner product $\langle e_2, e_2 \rangle$ is $1$. -/
theorem inner_e₂_e₂ : ⟪e₂, e₂⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_e₂, one_pow]

/-- The inner product $\langle e_1, e_2 \rangle$ is $0$. -/
theorem inner_e₁_e₂ : ⟪e₁, e₂⟫ = 0 := by
  simp [e₁, e₂, EuclideanSpace.inner_single_left]

/-- The inner product $\langle e_2, e_1 \rangle$ is $0$. -/
theorem inner_e₂_e₁ : ⟪e₂, e₁⟫ = 0 := by
  rw [real_inner_comm, inner_e₁_e₂]

/-- Every $d \in \mathbb{R}^2$ satisfies $\|d\|^2 = \langle e_1, d \rangle^2 + \langle e_2, d
\rangle^2$. -/
theorem norm_sq_eq (d : EuclideanSpace ℝ (Fin 2)) : ‖d‖ ^ 2 = ⟪e₁, d⟫ ^ 2 + ⟪e₂, d⟫ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp [e₁, e₂, EuclideanSpace.inner_single_left]

/-- Every $d \in \mathbb{R}^2$ satisfies $|\langle e_1, d \rangle| \le \|d\|$. -/
theorem abs_inner_e₁_le (d : EuclideanSpace ℝ (Fin 2)) : |⟪e₁, d⟫| ≤ ‖d‖ :=
  (abs_real_inner_le_norm _ _).trans (by rw [norm_e₁, one_mul])

/-- The rank-one bilinear form $(v, w) \mapsto \langle e, v \rangle \langle e, w \rangle$ on
$\mathbb{R}^2$. -/
noncomputable def rankOne (e : EuclideanSpace ℝ (Fin 2)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin 2)) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
    fun _ => innerSL ℝ e

/-- The rank-one bilinear form of $e$ takes the value
$\langle e, v_0 \rangle \langle e, v_1 \rangle$ at $(v_0, v_1)$. -/
theorem rankOne_apply (e : EuclideanSpace ℝ (Fin 2)) (v : Fin 2 → EuclideanSpace ℝ (Fin 2)) :
    rankOne e v = ⟪e, v 0⟫ * ⟪e, v 1⟫ := by
  simp [rankOne, Fin.prod_univ_two]

/-- If $\|e\| = 1$, the rank-one bilinear form of $e$ has norm at most $1$. -/
theorem norm_rankOne_le {e : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1) : ‖rankOne e‖ ≤ 1 := by
  refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one fun v => ?_
  rw [rankOne_apply, Real.norm_eq_abs, abs_mul, Fin.prod_univ_two, one_mul]
  have h0 := abs_real_inner_le_norm e (v 0)
  have h1 := abs_real_inner_le_norm e (v 1)
  rw [he, one_mul] at h0 h1
  exact mul_le_mul h0 h1 (abs_nonneg _) (norm_nonneg _)

/-- The termination index $k_\epsilon = \lceil \epsilon^{-2} \rceil$ of the example. -/
noncomputable def kε (ε : ℝ) : ℕ := ⌈(ε ^ 2)⁻¹⌉₊

/-- The function values $f_k = 2 - k \epsilon^2$ of (3.1.4). -/
noncomputable def fval (ε : ℝ) (k : ℕ) : ℝ := 2 - k * ε ^ 2

/-- The Newton steps $s_k = f_k^{-1} (1, \epsilon)$ of (3.1.5) for $k < k_\epsilon$, and $s_k = 0$
for $k \ge k_\epsilon$. -/
noncomputable def step (ε : ℝ) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  if k < kε ε then (fval ε k)⁻¹ • (e₁ + ε • e₂) else 0

/-- The iterates $x_k = \sum_{j < k} s_j$ of (3.1.6). -/
noncomputable def iter (ε : ℝ) (k : ℕ) : EuclideanSpace ℝ (Fin 2) := ∑ j ∈ range k, step ε j

/-- The gradients $g_k = -(\epsilon^2 f_k, \epsilon f_k)$ of (3.1.4) for $k < k_\epsilon$, and
$g_k = 0$ for $k \ge k_\epsilon$. -/
noncomputable def grad (ε : ℝ) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  if k < kε ε then -((ε ^ 2 * fval ε k) • e₁) - (ε * fval ε k) • e₂ else 0

/-- The Hessians $H_k = \operatorname{diag}(\epsilon^2 f_k^2, f_k^2)$ of (3.1.4), as bilinear forms.
-/
noncomputable def hess (ε : ℝ) (k : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin 2)) ℝ :=
  (ε ^ 2 * fval ε k ^ 2) • rankOne e₁ + fval ε k ^ 2 • rankOne e₂

/-- The first iterate of the example is $x_0 = 0$. -/
theorem iter_zero (ε : ℝ) : iter ε 0 = 0 := by simp [iter]

/-- The iterates of the example satisfy $x_{k+1} = x_k + s_k$. -/
theorem iter_succ (ε : ℝ) (k : ℕ) : iter ε (k + 1) = iter ε k + step ε k := by
  simp [iter, sum_range_succ]

/-- The Hessian $H_k$ takes the value $\epsilon^2 f_k^2 \langle e_1, v_0 \rangle \langle e_1, v_1
\rangle + f_k^2 \langle e_2, v_0 \rangle \langle e_2, v_1 \rangle$ at $(v_0, v_1)$. -/
theorem hess_apply (ε : ℝ) (k : ℕ) (v : Fin 2 → EuclideanSpace ℝ (Fin 2)) :
    hess ε k v = ε ^ 2 * fval ε k ^ 2 * (⟪e₁, v 0⟫ * ⟪e₁, v 1⟫) +
      fval ε k ^ 2 * (⟪e₂, v 0⟫ * ⟪e₂, v 1⟫) := by
  simp [hess, rankOne_apply]

section Bounds

variable {ε : ℝ}

/-- For $0 < \epsilon < 1$, the termination index satisfies $k_\epsilon \epsilon^2 < 2$. -/
theorem kε_mul_lt (hε : 0 < ε) (hε1 : ε < 1) : (kε ε : ℝ) * ε ^ 2 < 2 := by
  have h2 : 0 < ε ^ 2 := by positivity
  have := Nat.ceil_lt_add_one (inv_nonneg.2 h2.le)
  have h3 : (kε ε : ℝ) * ε ^ 2 < ((ε ^ 2)⁻¹ + 1) * ε ^ 2 :=
    mul_lt_mul_of_pos_right this h2
  rw [add_mul, inv_mul_cancel₀ h2.ne'] at h3
  have : ε ^ 2 < 1 := by nlinarith
  linarith

/-- For $0 < \epsilon < 1$ and $k \le k_\epsilon$, the function value satisfies $f_k > 0$. -/
theorem fval_pos (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ} (hk : k ≤ kε ε) : 0 < fval ε k := by
  have h := kε_mul_lt hε hε1
  have : (k : ℝ) * ε ^ 2 ≤ kε ε * ε ^ 2 :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)
  unfold fval; linarith

/-- For $\epsilon > 0$ and $k < k_\epsilon$, the function value satisfies $f_k > 1$. -/
theorem one_lt_fval (hε : 0 < ε) {k : ℕ} (hk : k < kε ε) : 1 < fval ε k := by
  have h2 : 0 < ε ^ 2 := by positivity
  have : (k : ℝ) < (ε ^ 2)⁻¹ := Nat.lt_ceil.1 hk
  have : (k : ℝ) * ε ^ 2 < 1 := by
    have := mul_lt_mul_of_pos_right this h2
    rwa [inv_mul_cancel₀ h2.ne'] at this
  unfold fval; linarith

/-- The function values satisfy $f_k \le 2$. -/
theorem fval_le_two (ε : ℝ) (k : ℕ) : fval ε k ≤ 2 := by
  unfold fval
  have : 0 ≤ (k : ℝ) * ε ^ 2 := by positivity
  linarith

/-- For $k < k_\epsilon$, the first coordinate of the step is $\langle e_1, s_k \rangle = f_k^{-1}$.
-/
theorem inner_e₁_step {k : ℕ} (hk : k < kε ε) : ⟪e₁, step ε k⟫ = (fval ε k)⁻¹ := by
  rw [step, ite_eq_left hk, inner_smul_right, inner_add_right, inner_smul_right, inner_e₁_e₁,
    inner_e₁_e₂]
  ring

/-- For $k < k_\epsilon$, the second coordinate of the step is
$\langle e_2, s_k \rangle = \epsilon f_k^{-1}$. -/
theorem inner_e₂_step {k : ℕ} (hk : k < kε ε) : ⟪e₂, step ε k⟫ = ε * (fval ε k)⁻¹ := by
  rw [step, ite_eq_left hk, inner_smul_right, inner_add_right, inner_smul_right, inner_e₂_e₂,
    inner_e₂_e₁]
  ring

/-- For $0 < \epsilon < 1$ and $i < j \le k_\epsilon$, the iterates satisfy $\|x_j - x_i\| \ge 1/2$,
because their first coordinates increase by $1/f_k \ge 1/2$ at each step. -/
theorem half_le_norm_iter_sub (hε : 0 < ε) (hε1 : ε < 1) {i j : ℕ} (hij : i < j) (hj : j ≤ kε ε) :
    1 / 2 ≤ ‖iter ε j - iter ε i‖ := by
  have hsum : iter ε j - iter ε i = ∑ l ∈ Finset.Ico i j, step ε l := by
    rw [iter, iter, sum_Ico_eq_sub _ hij.le]
  have hin : ⟪e₁, iter ε j - iter ε i⟫ = ∑ l ∈ Finset.Ico i j, (fval ε l)⁻¹ := by
    rw [hsum, inner_sum]
    refine sum_congr rfl fun l hl => inner_e₁_step ?_
    exact (Finset.mem_Ico.1 hl).2.trans_le hj
  have hge : 1 / 2 ≤ ⟪e₁, iter ε j - iter ε i⟫ := by
    rw [hin]
    have hi : i ∈ Finset.Ico i j := Finset.mem_Ico.2 ⟨le_rfl, hij⟩
    have hnn : ∀ l ∈ Finset.Ico i j, 0 ≤ (fval ε l)⁻¹ := fun l hl =>
      (inv_pos.2 (fval_pos hε hε1 ((Finset.mem_Ico.1 hl).2.le.trans hj))).le
    calc (1 : ℝ) / 2 ≤ (fval ε i)⁻¹ := by
          rw [one_div]
          exact inv_anti₀ (fval_pos hε hε1 (hij.le.trans hj)) (fval_le_two ε i)
      _ ≤ ∑ l ∈ Finset.Ico i j, (fval ε l)⁻¹ :=
          single_le_sum (f := fun l => (fval ε l)⁻¹) hnn hi
  exact hge.trans ((le_abs_self _).trans (abs_inner_e₁_le _))

/-- For $0 < \epsilon < 1$, the gradients satisfy $\|g_k\| \le 8$ for all $k$. -/
theorem norm_grad_le (hε : 0 < ε) (hε1 : ε < 1) (k : ℕ) : ‖grad ε k‖ ≤ 8 := by
  unfold grad
  split_ifs with hk
  · have hf := fval_pos hε hε1 hk.le
    have hf2 := fval_le_two ε k
    calc ‖-((ε ^ 2 * fval ε k) • e₁) - (ε * fval ε k) • e₂‖
        ≤ ‖(ε ^ 2 * fval ε k) • e₁‖ + ‖(ε * fval ε k) • e₂‖ := by
          rw [sub_eq_add_neg]
          exact (norm_add_le _ _).trans (by rw [norm_neg, norm_neg])
      _ = ε ^ 2 * fval ε k + ε * fval ε k := by
          rw [norm_smul, norm_smul, norm_e₁, norm_e₂, Real.norm_of_nonneg (by positivity),
            Real.norm_of_nonneg (by positivity)]
          ring
      _ ≤ 8 := by nlinarith
  · simp

/-- For $0 < \epsilon < 1$ and $k \le k_\epsilon$, the Hessians satisfy $\|H_k\| \le 8$. -/
theorem norm_hess_le (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ} (hk : k ≤ kε ε) : ‖hess ε k‖ ≤ 8 := by
  have hf := fval_pos hε hε1 hk
  have hf2 := fval_le_two ε k
  calc ‖hess ε k‖ ≤ ‖(ε ^ 2 * fval ε k ^ 2) • rankOne e₁‖ + ‖fval ε k ^ 2 • rankOne e₂‖ :=
        norm_add_le _ _
    _ ≤ ε ^ 2 * fval ε k ^ 2 * 1 + fval ε k ^ 2 * 1 := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
          Real.norm_of_nonneg (by positivity)]
        gcongr
        · exact norm_rankOne_le norm_e₁
        · exact norm_rankOne_le norm_e₂
    _ ≤ 8 := by
        have h4 : fval ε k ^ 2 ≤ 4 := by nlinarith
        have h1 : ε ^ 2 ≤ 1 := by nlinarith
        have : ε ^ 2 * fval ε k ^ 2 ≤ 1 * fval ε k ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        linarith

/-- For $0 < \epsilon < 1$, the Hessians are uniformly positive definite:
$H_k[d, d] \ge \epsilon^2 f_k^2 \|d\|^2$ for every $d \in \mathbb{R}^2$. -/
theorem le_hess_apply (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ} (d : EuclideanSpace ℝ (Fin 2)) :
    ε ^ 2 * fval ε k ^ 2 * ‖d‖ ^ 2 ≤ hess ε k (fun _ => d) := by
  rw [hess_apply, norm_sq_eq]
  have : ε ^ 2 ≤ 1 := by nlinarith
  have h0 : 0 ≤ fval ε k ^ 2 * ⟪e₂, d⟫ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right this h0]

/-- For $0 < \epsilon < 1$ and $k < k_\epsilon$, the data satisfy the Newton equation
$H_k s_k = -g_k$, in the form $H_k[s_k, v] = -\langle g_k, v \rangle$ for all $v$. -/
theorem hess_step_apply (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ} (hk : k < kε ε)
    (v : EuclideanSpace ℝ (Fin 2)) :
    hess ε k ![step ε k, v] = -⟪grad ε k, v⟫ := by
  have hf := (fval_pos hε hε1 hk.le).ne'
  rw [hess_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [inner_e₁_step hk, inner_e₂_step hk, grad, ite_eq_left hk, inner_sub_left,
    inner_neg_left, inner_smul_left, inner_smul_left]
  simp only [conj_trivial]
  field_simp
  ring

/-- For $0 < \epsilon < 1$ and $k < k_\epsilon$, the gradients satisfy $\|g_k\| > \epsilon$. -/
theorem lt_norm_grad (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ} (hk : k < kε ε) : ε < ‖grad ε k‖ := by
  have hf := one_lt_fval hε hk
  have hsq : ‖grad ε k‖ ^ 2 = ε ^ 2 * fval ε k ^ 2 * (ε ^ 2 + 1) := by
    rw [norm_sq_eq, grad, ite_eq_left hk, inner_sub_right, inner_neg_right, inner_smul_right,
      inner_smul_right, inner_sub_right, inner_neg_right, inner_smul_right, inner_smul_right,
      inner_e₁_e₁, inner_e₁_e₂, inner_e₂_e₁, inner_e₂_e₂]
    ring
  have : ε ^ 2 < ‖grad ε k‖ ^ 2 := by
    rw [hsq]
    have : 1 < fval ε k ^ 2 * (ε ^ 2 + 1) := by nlinarith
    have := mul_lt_mul_of_pos_left this (pow_pos hε 2)
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this

end Bounds

/-- The Hessians $H_k$ are symmetric bilinear forms: $H_k[v, w] = H_k[w, v]$. -/
theorem hess_symm (ε : ℝ) (k : ℕ) (v w : EuclideanSpace ℝ (Fin 2)) :
    hess ε k ![v, w] = hess ε k ![w, v] := by
  simp only [hess_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Let $0 < \epsilon < 1$ and $k \le k_\epsilon$. If $f : \mathbb{R}^2 \to \mathbb{R}$ has the
Hessian $\nabla^2 f(x_k) = H_k$, then $\lambda_{\min}[\nabla^2 f(x_k)] > 0$. -/
theorem hessianMinEig_pos {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ} (hk : k ≤ kε ε)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (h2 : iteratedFDeriv ℝ 2 f (iter ε k) = hess ε k) :
    0 < Chapter01.hessianMinEig f (iter ε k) := by
  have hfk := fval_pos hε hε1 hk
  refine lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * fval ε k ^ 2) ?_
  rw [Chapter01.hessianMinEig_def, h2]
  exact le_minCurvature_iff.2 fun d => le_hess_apply hε hε1 d

/-- Let $0 < \epsilon < 1$ and $k < k_\epsilon$. If $f : \mathbb{R}^2 \to \mathbb{R}$ has
$\nabla f(x_k) = g_k$ and $\nabla^2 f(x_k) = H_k$, then $s_k$ solves the Newton equation (3.1.1)
for $f$ at $x_k$. -/
theorem isNewtonStep_of_jet {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ} (hk : k < kε ε)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hg : gradient f (iter ε k) = grad ε k)
    (h2 : iteratedFDeriv ℝ 2 f (iter ε k) = hess ε k) :
    IsNewtonStep f (iter ε k) (step ε k) := fun v => by
  rw [h2, hg]
  exact hess_step_apply hε hε1 hk v

/-- **Equations (3.1.4)–(3.1.7)** of [cartis2022evaluation], the example of Theorem 3.1.1. There is
$B \ge 0$ with the following property. For every $\epsilon \in (0, 1)$ there is a three times
continuously differentiable $f : \mathbb{R}^2 \to \mathbb{R}$ with $|f(y)| \le B$ and
$\|\nabla^j f(y)\| \le B$ for all $y$ and all $j \le 3$, that interpolates the data at the
iterates:
$$f(x_k) = f_k, \quad \nabla f(x_k) = g_k, \quad \nabla^2 f(x_k) = H_k \quad \text{for all } k
  \le k_\epsilon.$$

The data are those of (3.1.4)–(3.1.6), except that $g_{k_\epsilon} = 0$. The function replaces
the book's piecewise-polynomial $f_{SN}$ of (3.1.7); it comes from
`Optimization.exists_contDiff_interpolating_separated_jets`. -/
theorem exists_example :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ 3 f ∧ (∀ y, |f y| ≤ B ∧ ∀ j ≤ 3, ‖iteratedFDeriv ℝ j f y‖ ≤ B) ∧
      ∀ k ≤ kε ε, f (iter ε k) = fval ε k ∧ gradient f (iter ε k) = grad ε k ∧
        iteratedFDeriv ℝ 2 f (iter ε k) = hess ε k := by
  obtain ⟨B, hB, H⟩ := exists_contDiff_interpolating_separated_jets
    (E := EuclideanSpace ℝ (Fin 2)) (r := 1 / 2) (κ := 8) (by norm_num) (by norm_num)
  refine ⟨B, hB, fun ε hε hε1 => ?_⟩
  obtain ⟨f, hf, hjet, hbd⟩ := H (kε ε) (iter ε) (fval ε) (grad ε) (hess ε)
    (fun i hi j hj hij => by
      rcases lt_or_gt_of_ne hij with h | h
      · rw [norm_sub_rev]; exact half_le_norm_iter_sub hε hε1 h hj
      · exact half_le_norm_iter_sub hε hε1 h hi)
    (fun k _ => hess_symm ε k)
    (fun k hk => ⟨by
      rw [abs_of_pos (fval_pos hε hε1 hk)]; linarith [fval_le_two ε k],
      norm_grad_le hε hε1 k, norm_hess_le hε hε1 hk⟩)
  exact ⟨f, hf.of_le (by norm_cast), hbd, hjet⟩

end NewtonSlow

open NewtonSlow in
/-- **Theorem 3.1.1** of [cartis2022evaluation] (slow convergence of Newton's method). There are
$f_{\mathrm{low}}$, $L_1 \ge 1$ and $L_2 \ge 1$ with the following property. For every
$\epsilon_1 \in (0, 1)$ there is a function $f : \mathbb{R}^2 \to \mathbb{R}$ that satisfies
f.Bb with $f_{\mathrm{low}}$, f.gL with $L_1$ and f.HL with $L_2$, such that a Newton run
(Algorithm 3.1.1) from $x_0 = 0$ exists, and every Newton run from $x_0 = 0$ satisfies:

* $\lambda_{\min}[\nabla^2 f(x_k)] > 0$ for all $k \le k_\epsilon = \lceil \epsilon_1^{-2}
  \rceil$;
* the first iteration with $\|\nabla f(x_k)\| \le \epsilon_1$ is $k_\epsilon$.

So the method evaluates $f$, $\nabla f$ and $\nabla^2 f$ at the $k_\epsilon + 1$ iterates
$x_0, \dots, x_{k_\epsilon}$.

**Correction.** For the data (3.1.4) the source claims $\|\nabla f(x_k)\| > \epsilon_1$ for all
$k \le k_\epsilon$. For $\epsilon_1$ not small, $f_{k_\epsilon} = 2 - \lceil \epsilon_1^{-2}
\rceil \epsilon_1^2$ can be smaller than $1$, and the claim fails at $k = k_\epsilon$. The
example prescribes $\nabla f(x_{k_\epsilon}) = 0$ instead, so the method stops exactly at
$k_\epsilon$.

The function is `CartisGouldToint.Chapter03.NewtonSlow.exists_example`. Every Newton run from
the origin follows the iterates of (3.1.6), because the Newton equation has a unique solution at
each of them. -/
theorem theorem_3_1_1 :
    ∃ flow L₁ L₂ : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ, Chapter02.AssumptionBb f flow ∧
        Chapter02.AssumptionGL f L₁ ∧ AssumptionHL f L₂ ∧
        (∃ x s, x 0 = 0 ∧ algorithm_3_1_1 f ε x s) ∧
        ∀ x s, x 0 = 0 → algorithm_3_1_1 f ε x s →
          (∀ k ≤ ⌈(ε ^ 2)⁻¹⌉₊, 0 < Chapter01.hessianMinEig f (x k)) ∧
          IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) ⌈(ε ^ 2)⁻¹⌉₊ := by
  obtain ⟨B, -, H⟩ := exists_example
  refine ⟨-B, max B 1, max B 1, le_max_right _ _, le_max_right _ _, fun ε hε hε1 => ?_⟩
  obtain ⟨f, hf, hbd, hjet⟩ := H ε hε hε1
  obtain ⟨hb, hgl, hhl⟩ := assumptions_of_bounded hf hbd
  set K := kε ε
  have hgrad : ∀ k ≤ K, ‖gradient f (iter ε k)‖ ≤ ε ↔ K ≤ k := fun k hk => by
    rw [(hjet k hk).2.1]
    constructor
    · intro h
      by_contra hlt
      exact absurd h (not_le.2 (lt_norm_grad hε hε1 (not_le.1 hlt)))
    · intro h
      rw [grad, ite_eq_right (not_lt.2 h), norm_zero]; exact hε.le
  have hhit : IsFirstHit (fun k => ‖gradient f (iter ε k)‖ ≤ ε) K :=
    ⟨(hgrad K le_rfl).2 le_rfl, fun j hj h => absurd ((hgrad j hj.le).1 h) (not_le.2 hj)⟩
  have hpd : ∀ k ≤ K, 0 < Chapter01.hessianMinEig f (iter ε k) := fun k hk =>
    hessianMinEig_pos hε hε1 hk (hjet k hk).2.2
  have hnewton : ∀ k < K, IsNewtonStep f (iter ε k) (step ε k) := fun k hk =>
    isNewtonStep_of_jet hε hε1 hk (hjet k hk.le).2.1 (hjet k hk.le).2.2
  refine ⟨f, hb, hgl, hhl, ⟨iter ε, step ε, iter_zero ε, hε, fun k hk => hnewton k ?_,
    fun k _ => iter_succ ε k⟩, fun x s hx0 h => ?_⟩
  · exact not_le.1 fun hle => hk K hle hhit.test
  -- every run follows the data
  have heq : ∀ k ≤ K, ∀ j ≤ k, x j = iter ε j := by
    intro k
    induction k with
    | zero => exact fun _ j hj => by rw [Nat.le_zero.1 hj, hx0, iter_zero]
    | succ k ih =>
      intro hk j hj
      have hx := ih (Nat.le_of_succ_le hk)
      rcases Nat.lt_or_eq_of_le hj with hj | rfl
      · exact hx j (Nat.lt_succ_iff.1 hj)
      have hkK : k < K := hk
      have hstop : ∀ i ≤ k, ¬ ‖gradient f (x i)‖ ≤ ε := fun i hi => by
        rw [hx i hi]; exact hhit.not_test_of_lt (hi.trans_lt hkK)
      have hs : IsNewtonStep f (iter ε k) (s k) := hx k le_rfl ▸ h.step k hstop
      have hsk := ((isNewtonStep_iff_isMinOn (hhl.contDiffAt _) (hpd k hkK.le)
        (hnewton k hkK) (s k)).1).1 hs
      rw [h.next k hstop, hx k le_rfl, hsk, iter_succ]
  rw [show ⌈(ε ^ 2)⁻¹⌉₊ = K from rfl]
  refine ⟨fun k hk => by rw [heq K le_rfl k hk]; exact hpd k hk,
    ⟨by simp only; rw [heq K le_rfl K le_rfl]; exact hhit.test, fun j hj => ?_⟩⟩
  simp only
  rw [heq K le_rfl j hj.le]
  exact hhit.not_test_of_lt hj

end CartisGouldToint.Chapter03
