/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Subproblem.Matrix

/-!
# Cartis, Gould and Toint, Section 8.1: The context of the step computation

This module formalizes Section 8.1 of [cartis2022evaluation]. Let $g \in \mathbb{R}^n$, let
$H \in \mathbb{R}^{n \times n}$ be symmetric, and let $M \in \mathbb{R}^{n \times n}$ be symmetric
positive definite. The section introduces the quadratic model $m(s) = \langle g, s \rangle +
\frac{1}{2} \langle s, H s \rangle$ (8.1.1), the scaled norm
$\|s\|_M = \sqrt{\langle s, M s \rangle}$, the regularized model $m^R(s, \sigma, r) = m(s) +
\frac{1}{r} \sigma \|s\|_M^r$ (8.1.4), and the two subproblems of the step computation: the
trust-region subproblem (8.1.2), which minimizes $m(s)$ subject to $\|s\|_M \le \Delta$, and the
regularization subproblem (8.1.3), which minimizes $m^R(s, \sigma, r)$ over all $s$.

The module also connects these objects to the operator backbone `Numlib.Optimization.Subproblem`. In
the space $\mathbb{R}^n$ with the inner product $\langle x, y \rangle_M = \langle M x, y \rangle$,
which is `Subproblem.ScaledSpace`, the norm is $\|\cdot\|_M$, the models are the operator models of
$M^{-1} g$ and $M^{-1} H$, and the two subproblems are the operator subproblems.

## Main definitions

* Equation (8.1.1), `CartisGouldToint.Chapter08.model`: the quadratic model $m(s)$.
* Equation (8.1.2), `CartisGouldToint.Chapter08.IsTrustRegionSolution`: $s$ is a global minimizer of
  the trust-region subproblem.
* Equation (8.1.3), `CartisGouldToint.Chapter08.IsRegularizationSolution`: $s$ is a global minimizer
  of the regularization subproblem.
* Equation (8.1.4), `CartisGouldToint.Chapter08.regModel`: the regularized model
  $m^R(s, \sigma, r)$.
* Section 8.1, `CartisGouldToint.Chapter08.mNorm`: the scaled norm $\|v\|_M$.

## Main results

* `CartisGouldToint.Chapter08.mNorm_eq_norm_toScaled`: $\|v\|_M$ is the norm of $v$ in the $M$-inner
  product space.
* `CartisGouldToint.Chapter08.model_eq_quadModel` and
  `CartisGouldToint.Chapter08.regModel_eq_regModel`: the two models are the operator models of
  $M^{-1} g$ and $M^{-1} H$ in the $M$-inner product space.
* `CartisGouldToint.Chapter08.isTrustRegionSolution_iff_scaled`: $s$ solves (8.1.2) if and only if
  it minimizes the operator model on the closed ball of radius $\Delta$ of the $M$-inner product
  space.
* `CartisGouldToint.Chapter08.isRegularizationSolution_iff_scaled`: $s$ solves (8.1.3) if and only
  if it minimizes the operator regularized model.

## Conventions

* $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`, and a matrix $A$ acts on vectors through
  `Matrix.toEuclideanLin A`.
* The dual norm $\|v\|_{M^{-1}}$ is `CartisGouldToint.Chapter08.mNorm M⁻¹ v`.

## Implementation notes

* The solution predicates describe the exact subproblems. The source studies exact
  solutions in this chapter to justify tests for approximate steps.

## Deviations from the source

* The definitions take arbitrary square matrices $H$ and $M$. The hypotheses "$H$ symmetric" and
  "$M$ positive definite" appear in the theorems that need them. The source also discusses
  uniform definiteness of the sequence of weights $M_k$, while the declarations here take
  a single matrix.
* The power $\|s\|_M^r$ in (8.1.4) is the real power `Real.rpow`, and $r$ is any real number. The
  source takes $r \ge 2$, $\Delta>0$ and $\sigma>0$, and the Lean solution predicates accept
  arbitrary real radii, powers and regularization weights.
-/

open Matrix Set Metric
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter08

open Subproblem

variable {n : ℕ}

/-- **Section 8.1** of [cartis2022evaluation], the scaled norm. Let $M \in \mathbb{R}^{n \times n}$.
The **scaled norm** of $v \in \mathbb{R}^n$ is
$$\|v\|_M = \sqrt{\langle v, M v \rangle}.$$

The source defines it after (8.1.4) for a symmetric positive definite $M$. The definition
accepts every square matrix; where $\langle v, M v \rangle < 0$, the real square root gives $0$.
For a positive definite $M$ it is the norm of the $M$-inner product space
(`CartisGouldToint.Chapter08.mNorm_eq_norm_toScaled`). The dual norm $\|v\|_{M^{-1}}$ is
`CartisGouldToint.Chapter08.mNorm M⁻¹ v`.

**Reading.** The printed square root matches on positive definite weights; arbitrary matrices are
admitted with square root totalized.
-/
noncomputable def mNorm (M : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  √⟪v, toEuclideanLin M v⟫

/-- **Equation (8.1.1)** of [cartis2022evaluation]. Let $g \in \mathbb{R}^n$ and
$H \in \mathbb{R}^{n \times n}$. The **quadratic model** is
$$m(s) = \langle g, s \rangle + \tfrac{1}{2} \langle s, H s \rangle.$$

The source assumes $H$ symmetric. The scalar model also accepts nonsymmetric matrices.

**Reading.** Same quadratic model with the symmetry of H left to downstream theorems.
-/
noncomputable def model (g : EuclideanSpace ℝ (Fin n)) (H : Matrix (Fin n) (Fin n) ℝ)
    (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⟪g, s⟫ + (1 / 2) * ⟪s, toEuclideanLin H s⟫

/-- **Equation (8.1.4)** of [cartis2022evaluation]. Let $g \in \mathbb{R}^n$,
$H, M \in \mathbb{R}^{n \times n}$ and $\sigma, r \in \mathbb{R}$. The **regularized model** is
$$m^R(s, \sigma, r) = m(s) + \frac{1}{r} \sigma \|s\|_M^r,$$
with $m$ the quadratic model (8.1.1) and $\|\cdot\|_M$ the scaled norm.

The factor $1/r$ is the normalization of footnote 59 of the source. The power is the real power
`Real.rpow`. The definition accepts any real $r,\sigma$, while the source takes
$r\ge2$ and $\sigma>0$. At $r=0$ the regularization term vanishes by total division.

**Generalization.** The same factor 1/r and scaled norm power extend to arbitrary regularization
weights and real exponents including zero.
-/
noncomputable def regModel (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (σ r : ℝ) (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  model g H s + (1 / r) * σ * mNorm M s ^ r

/-- **Equation (8.1.2)** of [cartis2022evaluation]. Let $g \in \mathbb{R}^n$,
$H, M \in \mathbb{R}^{n \times n}$ and $\Delta \in \mathbb{R}$. A vector $s$ is a **global
minimizer of the trust-region subproblem** if $\|s\|_M \le \Delta$ and $m(s) \le m(u)$ for every
$u$ with $\|u\|_M \le \Delta$. The predicate accepts all real radii. The source uses
$\Delta>0$.

**Reading.** Same exact global trust-region solution condition, with arbitrary real radii and matrix
inputs.
-/
def IsTrustRegionSolution (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (Δ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  mNorm M s ≤ Δ ∧ ∀ u, mNorm M u ≤ Δ → model g H s ≤ model g H u

/-- **Equation (8.1.3)** of [cartis2022evaluation]. Let $g \in \mathbb{R}^n$,
$H, M \in \mathbb{R}^{n \times n}$ and $\sigma, r \in \mathbb{R}$. A vector $s$ is a **global
minimizer of the regularization subproblem** if $m^R(s, \sigma, r) \le m^R(u, \sigma, r)$ for
every $u \in \mathbb{R}^n$. The model parameters have the generalized domain of
`CartisGouldToint.Chapter08.regModel`.

**Generalization.** Same exact unconstrained global minimizer condition for the extended model
parameter domain.
-/
def IsRegularizationSolution (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (σ r : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ u, regModel g H M σ r s ≤ regModel g H M σ r u

variable {g s : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}

/-- The definition of a global minimizer of (8.1.2), unfolded: $\|s\|_M \le \Delta$, and
$m(s) \le m(u)$ for every $u$ with $\|u\|_M \le \Delta$.

**Generalization.** Unfolds the exact trust-region solution predicate over its generalized parameter
domain.
-/
theorem isTrustRegionSolution_iff {Δ : ℝ} :
    IsTrustRegionSolution g H M Δ s ↔
      mNorm M s ≤ Δ ∧ ∀ u, mNorm M u ≤ Δ → model g H s ≤ model g H u :=
  Iff.rfl

/-- The definition of a global minimizer of (8.1.3), unfolded:
$m^R(s, \sigma, r) \le m^R(u, \sigma, r)$ for every $u$.

**Generalization.** Unfolds the same exact global minimization for generalized parameters.
-/
theorem isRegularizationSolution_iff {σ r : ℝ} :
    IsRegularizationSolution g H M σ r s ↔ ∀ u, regModel g H M σ r s ≤ regModel g H M σ r u :=
  Iff.rfl

/-- The definition of the scaled norm, unfolded: $\|v\|_M = \sqrt{\langle v, M v \rangle}$.

**Reading.** The formula is unconditional, including non-positive-definite weights.
-/
theorem mNorm_def (M : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    mNorm M v = √⟪v, toEuclideanLin M v⟫ := rfl

/-- The definition of the quadratic model, unfolded: $m(s) = \langle g, s \rangle + \frac{1}{2}
\langle s, H s \rangle$.

**Reading.** Unfolds the model without a Hessian symmetry premise.
-/
theorem model_def (g : EuclideanSpace ℝ (Fin n)) (H : Matrix (Fin n) (Fin n) ℝ)
    (s : EuclideanSpace ℝ (Fin n)) : model g H s = ⟪g, s⟫ + (1 / 2) * ⟪s, toEuclideanLin H s⟫ :=
  rfl

/-- The definition of the regularized model, unfolded: $m^R(s, \sigma, r) = m(s) + \frac{1}{r}
\sigma \|s\|_M^r$.

**Reading.** Unfolds the regularized model for all real weights and powers.
-/
theorem regModel_def (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ) (σ r : ℝ)
    (s : EuclideanSpace ℝ (Fin n)) :
    regModel g H M σ r s = model g H s + (1 / r) * σ * mNorm M s ^ r :=
  rfl

/-- The scaled norm of the zero vector is $0$: $\|0\|_M = 0$.

**Reading.** The zero vector identity continues to hold for arbitrary matrices.
-/
@[simp]
theorem mNorm_zero (M : Matrix (Fin n) (Fin n) ℝ) : mNorm M 0 = 0 := by
  rw [mNorm_def, inner_zero_left, Real.sqrt_zero]

/-- The scaled norm is nonnegative: $\|v\|_M \ge 0$ for every matrix $M$ and every $v$.

**Reading.** Nonnegativity follows from totalized square root even outside the positive definite
source domain.
-/
theorem mNorm_nonneg (M : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    0 ≤ mNorm M v :=
  Real.sqrt_nonneg _

/-! ### The bridge to the $M$-inner product space -/

/-- Let $M$ be positive definite. For every $v \in \mathbb{R}^n$, the scaled norm $\|v\|_M$ is the
norm of $v$ in the $M$-inner product space `Subproblem.ScaledSpace`. -/
theorem mNorm_eq_norm_toScaled (hM : M.PosDef) (v : EuclideanSpace ℝ (Fin n)) :
    mNorm M v = ‖toScaled hM v‖ := by
  rw [mNorm, norm_toScaled, real_inner_comm]

/-- Let $M$ be positive definite. For every $v \in \mathbb{R}^n$,
$\|v\|_M^2 = \langle v, M v \rangle$. -/
theorem mNorm_sq (hM : M.PosDef) (v : EuclideanSpace ℝ (Fin n)) :
    mNorm M v ^ 2 = ⟪v, toEuclideanLin M v⟫ := by
  rw [mNorm_eq_norm_toScaled hM, norm_toScaled_sq, real_inner_comm]

/-- Let $M$ be positive definite. For every $v \in \mathbb{R}^n$, the dual norm $\|v\|_{M^{-1}}$ is
the norm of the scaled gradient $M^{-1} v$ in the $M$-inner product space. -/
theorem mNorm_inv_eq_norm_scaledGrad (hM : M.PosDef) (v : EuclideanSpace ℝ (Fin n)) :
    mNorm M⁻¹ v = ‖scaledGrad hM v‖ := by
  rw [mNorm, ← norm_scaledGrad_sq, Real.sqrt_sq (norm_nonneg _)]

/-- Let $M$ be positive definite. The quadratic model satisfies $m(s) = \langle M^{-1} g, s
\rangle_M + \frac{1}{2} \langle s, M^{-1} H s \rangle_M$: it is the operator model
`Subproblem.quadModel` of $M^{-1} g$ and $M^{-1} H$ in the $M$-inner product space.

**Reading.** The same model is expressed using inverse-scaled operators, also for nonsymmetric H.
-/
theorem model_eq_quadModel (hM : M.PosDef) (s : EuclideanSpace ℝ (Fin n)) :
    model g H s = quadModel (scaledGrad hM g) (scaledOp H hM) (toScaled hM s) :=
  quadModel_scaled g s

/-- Let $M$ be positive definite and $\sigma, r \in \mathbb{R}$. The regularized model
$m^R(s, \sigma, r)$ is the operator regularized model `Subproblem.regModel` of $M^{-1} g$ and
$M^{-1} H$ in the $M$-inner product space, with weight $\sigma$ and exponent $r$.

**Reading.** Reexpresses the regularized model in the scaled space while allowing arbitrary real
weight and exponent.
-/
theorem regModel_eq_regModel (hM : M.PosDef) (σ r : ℝ) (s : EuclideanSpace ℝ (Fin n)) :
    regModel g H M σ r s =
      Subproblem.regModel (scaledGrad hM g) (scaledOp H hM) σ r (toScaled hM s) := by
  rw [Subproblem.regModel_def, ← model_eq_quadModel hM, ← mNorm_eq_norm_toScaled hM, regModel]
  ring

/-- Let $g \in \mathbb{R}^n$, $H \in \mathbb{R}^{n \times n}$, let $M$ be positive definite, and let
$\Delta \in \mathbb{R}$. Then $s$ is a global minimizer of the trust-region subproblem (8.1.2)
if and only if, in the $M$-inner product space, $\|s\|_M \le \Delta$ and $s$ minimizes the
operator model of $M^{-1} g$ and $M^{-1} H$ on the closed ball of radius $\Delta$ about $0$.

This is the bridge from (8.1.2) to the operator backbone. The vector $s$ is carried into the
$M$-inner product space by `Subproblem.toScaled`, the identity map of $\mathbb{R}^n$.

**Generalization.** Reexpresses the exact problem on a closed ball with generalized real radius.
-/
theorem isTrustRegionSolution_iff_scaled (hM : M.PosDef) {Δ : ℝ} :
    IsTrustRegionSolution g H M Δ s ↔
      ‖toScaled hM s‖ ≤ Δ ∧
        IsMinOn (quadModel (scaledGrad hM g) (scaledOp H hM)) (closedBall 0 Δ) (toScaled hM s) := by
  simp only [IsTrustRegionSolution, isMinOn_iff, mem_closedBall_zero_iff,
    mNorm_eq_norm_toScaled hM, model_eq_quadModel hM]
  refine and_congr_right fun _ => ⟨fun h x hx => ?_, fun h u hu => h _ hu⟩
  obtain ⟨u, rfl⟩ := (toScaled hM).surjective x
  exact h u hx

/-- Let $g \in \mathbb{R}^n$, $H \in \mathbb{R}^{n \times n}$, let $M$ be positive definite, and let
$\sigma, r \in \mathbb{R}$. Then $s$ is a global minimizer of the regularization subproblem
(8.1.3) if and only if, in the $M$-inner product space, $s$ minimizes the operator regularized
model of $M^{-1} g$ and $M^{-1} H$ over the whole space.

This is the bridge from (8.1.3) to the operator backbone. The vector $s$ is carried into the
$M$-inner product space by `Subproblem.toScaled`, the identity map of $\mathbb{R}^n$.

**Generalization.** Reexpresses exact global minimization in the scaled space with generalized real
parameters.
-/
theorem isRegularizationSolution_iff_scaled (hM : M.PosDef) {σ r : ℝ} :
    IsRegularizationSolution g H M σ r s ↔
      IsMinOn (Subproblem.regModel (scaledGrad hM g) (scaledOp H hM) σ r) univ
        (toScaled hM s) := by
  simp only [IsRegularizationSolution, isMinOn_univ_iff, regModel_eq_regModel hM]
  refine ⟨fun h x => ?_, fun h u => h _⟩
  obtain ⟨u, rfl⟩ := (toScaled hM).surjective x
  exact h u

/-- For $M = I$ the scaled norm is the Euclidean norm: $\|x\|_I = \|x\|$. -/
@[simp]
theorem mNorm_one (x : EuclideanSpace ℝ (Fin n)) : mNorm 1 x = ‖x‖ := by
  rw [mNorm, toEuclideanLin_one, LinearMap.id_apply, real_inner_self_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg _)]

end CartisGouldToint.Chapter08
