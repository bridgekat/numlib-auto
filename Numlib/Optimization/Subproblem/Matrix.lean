/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.SymmetricPencil
import Numlib.Krylov.Preconditioned
import Numlib.Optimization.Subproblem.Stopping

/-!
# Matrix subproblems in the operator setting

Chapters 8–10 of [cartis2022evaluation] state the trust-region and regularization subproblems for
real matrices: a symmetric matrix $H \in \mathbb{R}^{n \times n}$, a symmetric positive definite
scaling matrix $M$, the norm $\|v\|_M = \sqrt{\langle M v, v \rangle}$ and its dual norm
$\|v\|_{M^{-1}} = \sqrt{\langle v, M^{-1} v \rangle}$. The backbone, from
`Numlib.Optimization.Subproblem.Model` on, works with one symmetric operator on a real inner product
space. This file connects the two settings. The space $E_M$ is $\mathbb{R}^n$ with the inner product
$\langle x, y \rangle_M = \langle M x, y \rangle$, whose norm is $\|\cdot\|_M$. On $E_M$ the matrix
problem becomes the operator problem for the operator $M^{-1} H$, which is symmetric in
$\langle \cdot, \cdot \rangle_M$, and the vector $M^{-1} g$.

Every object of the matrix setting is the corresponding object of the operator setting: the
quadratic and regularized models, the norms $\|\cdot\|_M$ and $\|\cdot\|_{M^{-1}}$, the gradient
$g + H s + \lambda M s$, positive (semi)definiteness of $H + \lambda M$, solves with
$H + \lambda M$, the step $(H + \lambda M)^{-1}(-g)$ and the secular function, the eigenvalues and
eigenvectors of the pencil $(H, M)$, the kernels of $H + \lambda M$, the minimum-$M$-norm solution
of $(H + \lambda M) x = -g$, the Hessian of the regularized model, and the stopping rules (9.3.14).

## Main definitions

* `Subproblem.ScaledSpace`: the space $E_M$, that is, $\mathbb{R}^n$ with the inner product $\langle
  x, y \rangle_M = \langle M x, y \rangle$.
* `Subproblem.scaledOp`: the operator $M^{-1} H$ on $E_M$.
* `Subproblem.scaledGrad`: the vector $M^{-1} g$ in $E_M$.

## Main results

* `Subproblem.norm_toScaled` and `Subproblem.norm_scaledGrad_sq`: the norm of $E_M$ is $\|x\|_M$,
  and $\|M^{-1} g\|_M = \|g\|_{M^{-1}}$.
* `Subproblem.isSymmetric_scaledOp`: if $H$ is symmetric, then $M^{-1} H$ is symmetric in
  $\langle \cdot, \cdot \rangle_M$.
* `Subproblem.quadModel_scaled` and `Subproblem.regModel_scaled`: the matrix models (8.1.1) and
  (8.1.4) are the operator models of $M^{-1} g$ and $M^{-1} H$.
* `Subproblem.scaledGrad_gradient`: $M^{-1}(g + H s + \lambda M s) = M^{-1} g + (M^{-1} H + \lambda
  I) s$.
* `Subproblem.posSemidef_add_smul_iff_isPositive`: $H + \lambda M$ is positive semidefinite if and
  only if $M^{-1} H + \lambda I$ is positive on $E_M$.
* `Subproblem.posDef_add_smul_iff_scaled`: $H + \lambda M$ is positive semidefinite if and only if
  $\lambda \ge -\lambda_1$, and positive definite if and only if $\lambda > -\lambda_1$, where
  $\lambda_1$ is the least eigenvalue of the pencil.
* `Subproblem.isUnit_add_smul_scaledOp` and `Subproblem.isUnit_of_isUnit_add_smul_scaledOp`:
  $H + \lambda M$ is invertible if and only if $M^{-1} H + \lambda I$ is invertible.
* `Subproblem.toScaled_inv_apply` and `Subproblem.toScaled_inv_mul_apply`: solves with
  $H + \lambda M$ are solves with $M^{-1} H + \lambda I$.
* `Subproblem.toScaled_step` and `Subproblem.secular_scaled`: the matrix step
  $(H + \lambda M)^{-1}(-g)$ and the secular function $\|s\|_M^2$ are the operator step and secular
  function, for every $\lambda$.
* `Subproblem.toScaled_mem_ker_iff` and `Subproblem.scaledGrad_mem_orthogonal_iff`: the kernels of
  $H + \lambda M$ and the consistency condition of $(H + \lambda M) x = -g$ correspond.
* `Subproblem.toScaled_eq_particular_iff` and `Subproblem.particular_scaled_spec`: the minimum-norm
  solution of the operator problem is the minimum-$M$-norm solution of $(H + \lambda M) x = -g$.
* `Subproblem.inner_regModelHessian_scaled`: the Hessian (8.2.34) of the regularized model in the
  matrix setting.
* `Subproblem.regStoppingRules_scaled_iff`: the stopping rules (9.3.14) in the matrix setting.
* `Subproblem.eigenvalues_scaledOp`, `Subproblem.leftmost_scaledOp` and
  `Subproblem.rightmost_scaledOp`: the eigenvalues of $M^{-1} H$ on $E_M$ are the eigenvalues of the
  pencil $(H, M)$.
* `Subproblem.scaledOp_toScaled_of_eigen`, `Subproblem.eigen_of_scaledOp_eq`,
  `Subproblem.eigen_of_mem_ker`, `Subproblem.exists_eigen_of_eigenvalues` and
  `Subproblem.exists_scaledOp_scaledGrad_eq_iff`: eigenvectors of $M^{-1} H$ are generalized
  eigenvectors $H v = \mu M v$ of the pencil, and conversely.
* `Subproblem.norm_scaledOp_le`: the operator norm of $M^{-1} H$ on $E_M$ is at most the Euclidean
  operator norm $\|M^{-1} H\|_2$.

## Implementation notes

* The space $E_M$ is the energy space `Krylov.IsPreconditioner.EnergySpace` of $M$. The map
  `Subproblem.toScaled` is the identity map from `EuclideanSpace ℝ ι` to $E_M$.
* The index set of the matrices is a finite type `ι`, with $n$ its cardinality.
* Matrix inverses follow the Mathlib convention $A^{-1} = 0$ for a singular matrix $A$, and operator
  inverses use `Ring.inverse`, which is $0$ at a non-invertible operator. So the transport results
  for solves, the step and the secular function hold for every $\lambda$.
-/

open Matrix
open scoped RealInnerProductSpace

namespace Subproblem

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H M : Matrix ι ι ℝ}

/-! ### The scaled space, operator and gradient -/

variable (hM : M.PosDef)

/-- The **$M$-inner product space** $E_M$, for a real positive definite matrix $M$: the space
$\mathbb{R}^n$ with the inner product
$$\langle x, y \rangle_M = \langle M x, y \rangle.$$
Its norm is the norm $\|x\|_M = \sqrt{\langle M x, x \rangle}$ of Section 8.1 of
[cartis2022evaluation].

The space is the energy space `Krylov.IsPreconditioner.EnergySpace` of $M$, built from
`Matrix.PosDef.isPreconditioner_toEuclideanLin`. -/
noncomputable abbrev ScaledSpace : Type _ := hM.isPreconditioner_toEuclideanLin.EnergySpace

/-- The identity map from `EuclideanSpace ℝ ι` to the $M$-inner product space $E_M$, as a linear
equivalence. -/
noncomputable abbrev toScaled : EuclideanSpace ℝ ι ≃ₗ[ℝ] ScaledSpace hM :=
  hM.isPreconditioner_toEuclideanLin.toEnergy

variable (H) in
/-- The **scaled operator** $M^{-1} H$ on the $M$-inner product space $E_M$, for a real matrix $H$
and a real positive definite matrix $M$.

If $H$ is symmetric, then $M^{-1} H$ is symmetric in $\langle \cdot, \cdot \rangle_M$
(`Subproblem.isSymmetric_scaledOp`), and its eigenvalues are those of the pencil $(H, M)$
(`Subproblem.eigenvalues_scaledOp`). -/
noncomputable def scaledOp : ScaledSpace hM →L[ℝ] ScaledSpace hM :=
  LinearMap.toContinuousLinearMap
    (hM.isPreconditioner_toEuclideanLin.energyEnd (toEuclideanLin M⁻¹ ∘ₗ toEuclideanLin H))

/-- The **scaled gradient** $M^{-1} g$ in the $M$-inner product space $E_M$, for
$g \in \mathbb{R}^n$ and a real positive definite matrix $M$.

Its norm in $E_M$ is the dual norm $\|g\|_{M^{-1}}$ of [cartis2022evaluation]
(`Subproblem.norm_scaledGrad_sq`). -/
noncomputable def scaledGrad (g : EuclideanSpace ℝ ι) : ScaledSpace hM :=
  toScaled hM (toEuclideanLin M⁻¹ g)

variable {hM}

/-- The scaled operator acts on a vector $x \in \mathbb{R}^n$ of $E_M$ as the matrix $M^{-1} H$: it
maps $x$ to $M^{-1}(H x)$. -/
@[simp]
theorem scaledOp_toScaled (x : EuclideanSpace ℝ ι) :
    scaledOp H hM (toScaled hM x) = toScaled hM (toEuclideanLin M⁻¹ (toEuclideanLin H x)) :=
  rfl

/-- The $M$-inner product of two vectors $x, y \in \mathbb{R}^n$ is $\langle x, y \rangle_M =
\langle M x, y \rangle$. -/
theorem inner_toScaled (x y : EuclideanSpace ℝ ι) :
    ⟪toScaled hM x, toScaled hM y⟫ = ⟪toEuclideanLin M x, y⟫ :=
  WithEnergy.inner_equiv _ _ x y

/-- The squared $M$-norm of $x \in \mathbb{R}^n$ is $\|x\|_M^2 = \langle M x, x \rangle$. -/
theorem norm_toScaled_sq (x : EuclideanSpace ℝ ι) :
    ‖toScaled hM x‖ ^ 2 = ⟪toEuclideanLin M x, x⟫ := by
  rw [← real_inner_self_eq_norm_sq, inner_toScaled]

/-- Let $M$ be a real positive definite matrix. For every $x \in \mathbb{R}^n$, the norm of $x$ in
the $M$-inner product space $E_M$ is
$$\|x\|_M = \sqrt{\langle M x, x \rangle}.$$
-/
theorem norm_toScaled (x : EuclideanSpace ℝ ι) : ‖toScaled hM x‖ = √⟪toEuclideanLin M x, x⟫ := by
  rw [← norm_toScaled_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The bilinear form of the scaled operator is that of $H$: $\langle M^{-1} H x, y \rangle_M =
\langle H x, y \rangle$ for all $x, y \in \mathbb{R}^n$. -/
theorem inner_scaledOp_toScaled (x y : EuclideanSpace ℝ ι) :
    ⟪scaledOp H hM (toScaled hM x), toScaled hM y⟫ = ⟪toEuclideanLin H x, y⟫ :=
  hM.isPreconditioner_toEuclideanLin.inner_energyEnd_left _ x y

/-- For all $g, y \in \mathbb{R}^n$, $\langle M^{-1} g, y \rangle_M = \langle g, y \rangle$. -/
theorem inner_scaledGrad_toScaled (g y : EuclideanSpace ℝ ι) :
    ⟪scaledGrad hM g, toScaled hM y⟫ = ⟪g, y⟫ := by
  rw [real_inner_comm, scaledGrad, hM.isPreconditioner_toEuclideanLin.inner_toEnergy_inv,
    real_inner_comm]

/-- For all $v, g \in \mathbb{R}^n$, $\langle v, M^{-1} g \rangle_M = \langle v, g \rangle$.

So the coordinates $\gamma_i = v_i^T g$ of (8.2.6) of [cartis2022evaluation] are the $M$-inner
products of the generalized eigenvectors $v_i$ with the scaled gradient. -/
theorem inner_toScaled_scaledGrad (v g : EuclideanSpace ℝ ι) :
    ⟪toScaled hM v, scaledGrad hM g⟫ = ⟪v, g⟫ := by
  rw [real_inner_comm, inner_scaledGrad_toScaled, real_inner_comm]

/-- Let $M$ be a real positive definite matrix. For every $g \in \mathbb{R}^n$, the squared norm of
the scaled gradient in $E_M$ is
$$\|M^{-1} g\|_M^2 = \langle g, M^{-1} g \rangle = \|g\|_{M^{-1}}^2.$$
-/
theorem norm_scaledGrad_sq (g : EuclideanSpace ℝ ι) :
    ‖scaledGrad hM g‖ ^ 2 = ⟪g, toEuclideanLin M⁻¹ g⟫ :=
  hM.isPreconditioner_toEuclideanLin.norm_toEnergy_inv_sq g

/-- Let $H$ be a real symmetric matrix and $M$ a real positive definite matrix. Then the scaled
operator $M^{-1} H$ is symmetric in the $M$-inner product:
$$\langle M^{-1} H x, y \rangle_M = \langle x, M^{-1} H y \rangle_M \quad \text{for all } x, y
  \in E_M.$$
-/
theorem isSymmetric_scaledOp (hH : H.IsHermitian) :
    (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM).IsSymmetric :=
  (LinearMap.isSymmetric_iff_of_inner_map_eq (toScaled hM) fun x y => inner_scaledOp_toScaled x y).1
    (isSymmetric_toEuclideanLin_iff.2 hH)

/-! ### Models and gradients -/

/-- **The quadratic model in the scaled setting.** Let $H$ be a real matrix and $M$ a real positive
definite matrix. For all $g, s \in \mathbb{R}^n$,
$$\langle g, s \rangle + \tfrac12 \langle s, H s \rangle = m(s),$$
where $m$ is the quadratic model `Subproblem.quadModel` of $M^{-1} g$ and $M^{-1} H$ in the
$M$-inner product space $E_M$.

The left side is the model (8.1.1) of [cartis2022evaluation]. -/
theorem quadModel_scaled (g s : EuclideanSpace ℝ ι) :
    ⟪g, s⟫ + (1 / 2) * ⟪s, toEuclideanLin H s⟫ =
      quadModel (scaledGrad hM g) (scaledOp H hM) (toScaled hM s) := by
  rw [quadModel, inner_scaledGrad_toScaled,
    real_inner_comm (scaledOp H hM (toScaled hM s)) (toScaled hM s), inner_scaledOp_toScaled,
    real_inner_comm (toEuclideanLin H s) s]

/-- **The regularized model in the scaled setting.** Let $H$ be a real matrix and $M$ a real
positive definite matrix. For all $g, s \in \mathbb{R}^n$ and $\sigma, r \in \mathbb{R}$,
$$\langle g, s \rangle + \tfrac12 \langle s, H s \rangle + \frac{\sigma}{r} \|s\|_M^r =
  m^R(s),$$
where $m^R$ is the regularized model `Subproblem.regModel` of $M^{-1} g$ and $M^{-1} H$ in the
$M$-inner product space $E_M$.

The left side is the model (8.1.4) of [cartis2022evaluation], with $\|s\|_M$ written as
$\sqrt{\langle M s, s \rangle}$. -/
theorem regModel_scaled (g s : EuclideanSpace ℝ ι) (σ r : ℝ) :
    ⟪g, s⟫ + (1 / 2) * ⟪s, toEuclideanLin H s⟫ + σ / r * √⟪toEuclideanLin M s, s⟫ ^ r =
      regModel (scaledGrad hM g) (scaledOp H hM) σ r (toScaled hM s) := by
  rw [regModel, ← quadModel_scaled, norm_toScaled]

/-- For every $\lambda \in \mathbb{R}$ and $x \in \mathbb{R}^n$, $(M^{-1} H + \lambda I) x = M^{-1}
(H + \lambda M) x$. -/
theorem add_smul_scaledOp_toScaled (lam : ℝ) (x : EuclideanSpace ℝ ι) :
    (scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM)) (toScaled hM x) =
      toScaled hM (toEuclideanLin M⁻¹ (toEuclideanLin (H + lam • M) x)) := by
  simp only [_root_.add_apply, _root_.smul_apply, one_apply_eq_self,
    scaledOp_toScaled, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    toEuclideanLin_nonsing_inv_mul_apply hM.isUnit]

/-- **The gradient in the scaled setting.** Let $H$ be a real matrix and $M$ a real positive
definite matrix. For all $g, s \in \mathbb{R}^n$ and $\lambda \in \mathbb{R}$, the Euclidean
gradient $v = g + H s + \lambda M s$ satisfies
$$M^{-1} v = M^{-1} g + (M^{-1} H + \lambda I) s.$$

The vector $v$ is the gradient (8.2.34) of [cartis2022evaluation]. So its dual norm
$\|v\|_{M^{-1}} = \sqrt{\langle v, M^{-1} v \rangle}$ is the norm in $E_M$ of the gradient of
the operator model (`Subproblem.norm_scaledGrad_sq`). -/
theorem scaledGrad_gradient (g s : EuclideanSpace ℝ ι) (lam : ℝ) :
    scaledGrad hM (g + toEuclideanLin H s + lam • toEuclideanLin M s) =
      scaledGrad hM g + (scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM))
        (toScaled hM s) := by
  have h : toEuclideanLin (H + lam • M) s = toEuclideanLin H s + lam • toEuclideanLin M s := by
    rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [add_smul_scaledOp_toScaled, scaledGrad, scaledGrad, ← map_add, ← map_add, h, add_assoc]

/-! ### Definiteness, the step and the secular function -/

/-- The bilinear form of $M^{-1} H + \lambda I$ in the $M$-inner product is that of $H + \lambda M$:
$\langle (M^{-1} H + \lambda I) x, y \rangle_M = \langle (H + \lambda M) x, y \rangle$ for all
$x, y \in \mathbb{R}^n$. -/
theorem inner_add_smul_scaledOp_toScaled (lam : ℝ) (x y : EuclideanSpace ℝ ι) :
    ⟪(scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM)) (toScaled hM x),
      toScaled hM y⟫ = ⟪toEuclideanLin (H + lam • M) x, y⟫ := by
  simp only [_root_.add_apply, _root_.smul_apply, one_apply_eq_self,
    inner_add_left, inner_smul_left, inner_scaledOp_toScaled, inner_toScaled, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, conj_trivial]

/-- For every $\lambda \in \mathbb{R}$, the matrix $H + \lambda M$ is positive semidefinite if and
only if the operator $M^{-1} H + \lambda I$ on $E_M$ is positive, that is, symmetric with
$\langle (M^{-1} H + \lambda I) x, x \rangle_M \ge 0$ for all $x$. -/
theorem posSemidef_add_smul_iff_isPositive (lam : ℝ) :
    (H + lam • M).PosSemidef ↔
      ((scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM) : _ →L[ℝ] _) :
        ScaledSpace hM →ₗ[ℝ] ScaledSpace hM).IsPositive := by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  exact LinearMap.isPositive_iff_of_inner_map_eq (toScaled hM) fun x y =>
    inner_add_smul_scaledOp_toScaled lam x y

/-- For every $\lambda \in \mathbb{R}$, the matrix $H + \lambda M$ is positive definite if and only
if the operator $M^{-1} H + \lambda I$ on $E_M$ is symmetric and coercive in the $M$-inner
product. -/
theorem posDef_add_smul_iff_isSymmetricCoercive (lam : ℝ) :
    (H + lam • M).PosDef ↔
      ((scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM) : _ →L[ℝ] _) :
        ScaledSpace hM →ₗ[ℝ] ScaledSpace hM).IsSymmetricCoercive := by
  rw [Matrix.posDef_iff_isSymmetricCoercive]
  exact LinearMap.isSymmetricCoercive_iff_of_inner_map_eq (toScaled hM) fun x y =>
    inner_add_smul_scaledOp_toScaled lam x y

/-- The $M$-inner product space is nontrivial when the index type is nonempty, that is, when
$n \ge 1$. -/
instance instNontrivialScaledSpace [Nonempty ι] : Nontrivial (ScaledSpace hM) :=
  (toScaled hM).injective.nontrivial

/-- **Definiteness of $H + \lambda M$ and the leftmost eigenvalue.** Let $H$ be a real symmetric
matrix and $M$ a real positive definite matrix, with $n \ge 1$. Let $\lambda_1$ be the leftmost
eigenvalue of the scaled operator $M^{-1} H$ on $E_M$, which is the least eigenvalue of the
pencil $(H, M)$ (`Subproblem.leftmost_scaledOp`). Then for every $\lambda \in \mathbb{R}$:
* $H + \lambda M$ is positive semidefinite if and only if $\lambda \ge -\lambda_1$;
* $H + \lambda M$ is positive definite if and only if $\lambda > -\lambda_1$.

This is the matrix form of the facts of Section 8.2 of [cartis2022evaluation]. The number
$\lambda_1$ is `Subproblem.leftmost` of `Subproblem.isSymmetric_scaledOp`. -/
theorem posDef_add_smul_iff_scaled [Nonempty ι] (hH : H.IsHermitian) (lam : ℝ) :
    ((H + lam • M).PosSemidef ↔ -leftmost (isSymmetric_scaledOp (hM := hM) hH) ≤ lam) ∧
      ((H + lam • M).PosDef ↔ -leftmost (isSymmetric_scaledOp (hM := hM) hH) < lam) :=
  ⟨(posSemidef_add_smul_iff_isPositive lam).trans (isPositive_add_smul_iff lam),
    (posDef_add_smul_iff_isSymmetricCoercive lam).trans (isSymmetricCoercive_add_smul_iff lam)⟩

/-- For $\lambda \in \mathbb{R}$, if the matrix $H + \lambda M$ is invertible, then the operator
$M^{-1} H + \lambda I$ on $E_M$ is invertible. -/
theorem isUnit_add_smul_scaledOp {lam : ℝ} (hu : IsUnit (H + lam • M)) :
    IsUnit (scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM)) := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot']
  intro u hu0
  obtain ⟨x, rfl⟩ := (toScaled hM).surjective u
  rw [ContinuousLinearMap.coe_coe, add_smul_scaledOp_toScaled, LinearEquiv.map_eq_zero_iff] at hu0
  have h1 : toEuclideanLin (H + lam • M) x = 0 := by
    rw [← toEuclideanLin_mul_nonsing_inv_apply hM.isUnit (toEuclideanLin (H + lam • M) x), hu0,
      map_zero]
  rw [← toEuclideanLin_nonsing_inv_mul_apply hu x, h1, map_zero, map_zero]

/-- Let $H$ be a real matrix, $M$ a real positive definite matrix, and $\lambda \in \mathbb{R}$. If
the operator $M^{-1} H + \lambda I$ on $E_M$ is invertible, then the matrix $H + \lambda M$ is
invertible.

This is the converse of `Subproblem.isUnit_add_smul_scaledOp`. -/
theorem isUnit_of_isUnit_add_smul_scaledOp {lam : ℝ}
    (hu : IsUnit (scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM))) :
    IsUnit (H + lam • M) := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot] at hu
  have hinj := LinearMap.ker_eq_bot.1 hu
  rw [← mulVec_injective_iff_isUnit]
  intro x y hxy
  have h : toScaled hM (WithLp.toLp 2 x) = toScaled hM (WithLp.toLp 2 y) := by
    apply hinj
    simp only [ContinuousLinearMap.coe_coe, add_smul_scaledOp_toScaled, toEuclideanLin_toLp, hxy]
  simpa using h

/-- **Solves with $H + \lambda M$ in the scaled setting.** Let $H$ be a real matrix and $M$ a real
positive definite matrix. For every $\lambda \in \mathbb{R}$ and $v \in \mathbb{R}^n$,
$$(H + \lambda M)^{-1} v = (M^{-1} H + \lambda I)^{-1} (M^{-1} v)$$
as vectors of $E_M$.

The matrix inverse is $0$ at a singular matrix, and the operator inverse is `Ring.inverse`,
which is $0$ at a non-invertible operator. So both sides are $0$ when $H + \lambda M$ is
singular, and the identity holds for every $\lambda$. -/
theorem toScaled_inv_apply (lam : ℝ) (v : EuclideanSpace ℝ ι) :
    toScaled hM (toEuclideanLin (H + lam • M)⁻¹ v) =
      Ring.inverse (scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM))
        (toScaled hM (toEuclideanLin M⁻¹ v)) := by
  set T := scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM) with hTdef
  by_cases hu : IsUnit (H + lam • M)
  · have hinv := congrArg (fun S : ScaledSpace hM →L[ℝ] ScaledSpace hM =>
      S (toScaled hM (toEuclideanLin (H + lam • M)⁻¹ v)))
      (Ring.inverse_mul_cancel _ (isUnit_add_smul_scaledOp (hM := hM) hu))
    change Ring.inverse T (T _) = _ at hinv
    rw [one_apply_eq_self, hTdef, add_smul_scaledOp_toScaled,
      toEuclideanLin_mul_nonsing_inv_apply hu] at hinv
    exact hinv.symm
  · have h1 : (H + lam • M)⁻¹ = 0 :=
      nonsing_inv_apply_not_isUnit _ (by rwa [← isUnit_iff_isUnit_det])
    have h2 : ¬ IsUnit T := fun h => hu (isUnit_of_isUnit_add_smul_scaledOp h)
    rw [h1, Ring.inverse_non_unit _ h2]
    simp

/-- Let $H$ be a real matrix and $M$ a real positive definite matrix. For every
$\lambda \in \mathbb{R}$ and $w \in \mathbb{R}^n$,
$$(H + \lambda M)^{-1} M w = (M^{-1} H + \lambda I)^{-1} w$$
as vectors of $E_M$, with the inverses of `Subproblem.toScaled_inv_apply`. -/
theorem toScaled_inv_mul_apply (lam : ℝ) (w : EuclideanSpace ℝ ι) :
    toScaled hM (toEuclideanLin (H + lam • M)⁻¹ (toEuclideanLin M w)) =
      Ring.inverse (scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM))
        (toScaled hM w) := by
  rw [toScaled_inv_apply, toEuclideanLin_nonsing_inv_mul_apply hM.isUnit]

/-- **The step in the scaled setting.** Let $H$ be a real matrix and $M$ a real positive definite
matrix. For every $g \in \mathbb{R}^n$ and $\lambda \in \mathbb{R}$, the vector
$(H + \lambda M)^{-1}(-g)$, as a vector of $E_M$, is the step $s(\lambda) = -(M^{-1} H + \lambda
I)^{-1} M^{-1} g$ of the operator problem.

The step is (8.2.2) of [cartis2022evaluation] and is `Subproblem.step`. Both sides are $0$ when
$H + \lambda M$ is singular. -/
theorem toScaled_step (g : EuclideanSpace ℝ ι) (lam : ℝ) :
    toScaled hM (toEuclideanLin (H + lam • M)⁻¹ (-g)) =
      step (scaledGrad hM g) (scaledOp H hM) lam := by
  rw [toScaled_inv_apply, step, map_neg, map_neg, map_neg, scaledGrad]

/-- **The secular function in the scaled setting.** Let $H$ be a real matrix and $M$ a real positive
definite matrix. For every $g \in \mathbb{R}^n$ and $\lambda \in \mathbb{R}$, let
$s = (H + \lambda M)^{-1}(-g)$. Then the secular function of $M^{-1} g$ and $M^{-1} H$ at
$\lambda$ is
$$\pi(\lambda) = \|s\|_M^2 = \langle M s, s \rangle.$$

The secular function is (8.2.4) of [cartis2022evaluation] and is `Subproblem.secular`. -/
theorem secular_scaled (g : EuclideanSpace ℝ ι) (lam : ℝ) :
    secular (scaledGrad hM g) (scaledOp H hM) lam =
      ⟪toEuclideanLin M (toEuclideanLin (H + lam • M)⁻¹ (-g)),
        toEuclideanLin (H + lam • M)⁻¹ (-g)⟫ := by
  rw [secular, ← toScaled_step g lam, norm_toScaled_sq]

/-! ### Kernels and the minimum-$M$-norm solution -/

/-- Let $H$ be a real matrix and $M$ a real positive definite matrix. For every
$\lambda \in \mathbb{R}$ and $x \in \mathbb{R}^n$, $x$ lies in the kernel of the operator
$M^{-1} H + \lambda I$ on $E_M$ if and only if $x$ lies in the kernel of the matrix
$H + \lambda M$. -/
theorem toScaled_mem_ker_iff (lam : ℝ) (x : EuclideanSpace ℝ ι) :
    toScaled hM x ∈ LinearMap.ker ((scaledOp H hM + lam • 1 : ScaledSpace hM →L[ℝ] ScaledSpace hM) :
      ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) ↔ x ∈ LinearMap.ker (toEuclideanLin (H + lam • M)) := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    add_smul_scaledOp_toScaled, LinearEquiv.map_eq_zero_iff]
  constructor
  · intro h
    rw [← toEuclideanLin_mul_nonsing_inv_apply hM.isUnit (toEuclideanLin (H + lam • M) x), h,
      map_zero]
  · intro h; rw [h, map_zero]

/-- Let $H$ be a real matrix and $M$ a real positive definite matrix. For every
$\lambda \in \mathbb{R}$ and $g \in \mathbb{R}^n$, the vector $M^{-1} g$ is $M$-orthogonal to
the kernel of $M^{-1} H + \lambda I$ if and only if $g$ is orthogonal to the kernel of
$H + \lambda M$.

So the consistency condition of the shifted system $(H + \lambda M) x = -g$ is the same in both
settings. -/
theorem scaledGrad_mem_orthogonal_iff (lam : ℝ) (g : EuclideanSpace ℝ ι) :
    scaledGrad hM g ∈ (LinearMap.ker ((scaledOp H hM + lam • 1 : ScaledSpace hM →L[ℝ]
      ScaledSpace hM) : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM))ᗮ ↔
      g ∈ (LinearMap.ker (toEuclideanLin (H + lam • M)))ᗮ := by
  rw [Submodule.mem_orthogonal', Submodule.mem_orthogonal']
  constructor
  · intro h y hy
    rw [← inner_scaledGrad_toScaled]
    exact h _ ((toScaled_mem_ker_iff lam y).2 hy)
  · intro h u hu
    obtain ⟨y, rfl⟩ := (toScaled hM).surjective u
    rw [inner_scaledGrad_toScaled]
    exact h y ((toScaled_mem_ker_iff lam y).1 hu)

/-- For all $\lambda \in \mathbb{R}$ and $g, x \in \mathbb{R}^n$,
$(M^{-1} H + \lambda I) x = -M^{-1} g$ if and only if $(H + \lambda M) x = -g$. -/
theorem add_smul_scaledOp_toScaled_eq_neg_iff (lam : ℝ) (g x : EuclideanSpace ℝ ι) :
    (scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM)) (toScaled hM x) =
      -scaledGrad hM g ↔ toEuclideanLin (H + lam • M) x = -g := by
  rw [add_smul_scaledOp_toScaled, scaledGrad, ← map_neg, ← map_neg,
    (toScaled hM).injective.eq_iff]
  constructor
  · intro h
    have := congrArg (toEuclideanLin M) h
    rwa [toEuclideanLin_mul_nonsing_inv_apply hM.isUnit,
      toEuclideanLin_mul_nonsing_inv_apply hM.isUnit] at this
  · intro h; rw [h]

/-- For every $\lambda \in \mathbb{R}$ and $y \in \mathbb{R}^n$, the vector $y$ of $E_M$ is
$M$-orthogonal to the kernel of $M^{-1} H + \lambda I$ if and only if
$\langle M y, v \rangle = 0$ for every $v$ in the kernel of $H + \lambda M$. -/
theorem toScaled_mem_orthogonal_ker_iff (lam : ℝ) (y : EuclideanSpace ℝ ι) :
    toScaled hM y ∈ (LinearMap.ker ((scaledOp H hM + lam • 1 : ScaledSpace hM →L[ℝ]
      ScaledSpace hM) : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM))ᗮ ↔
      ∀ v ∈ LinearMap.ker (toEuclideanLin (H + lam • M)), ⟪toEuclideanLin M y, v⟫ = 0 := by
  rw [Submodule.mem_orthogonal']
  constructor
  · intro h v hv
    rw [← inner_toScaled]
    exact h _ ((toScaled_mem_ker_iff lam v).2 hv)
  · intro h u hu
    obtain ⟨v, rfl⟩ := (toScaled hM).surjective u
    rw [inner_toScaled]
    exact h v ((toScaled_mem_ker_iff lam v).1 hu)

/-- **The minimum-$M$-norm solution is `Subproblem.particular`.** Let $H$ be a real symmetric
matrix, $M$ a real positive definite matrix, $\lambda \in \mathbb{R}$, and $g \in \mathbb{R}^n$
orthogonal to the kernel of $H + \lambda M$. Then a vector $x \in \mathbb{R}^n$ equals the
minimum-norm solution `Subproblem.particular` of the scaled problem for $M^{-1} g$, $M^{-1} H$
and $\lambda$ if and only if
$$(H + \lambda M) x = -g \quad \text{and} \quad \langle M x, v \rangle = 0 \text{ for every } v
  \in \ker (H + \lambda M).$$

This is the solution of (8.3.2) of [cartis2022evaluation] of least $M$-norm. -/
theorem toScaled_eq_particular_iff (hH : H.IsHermitian) {lam : ℝ} {g : EuclideanSpace ℝ ι}
    (hg : g ∈ (LinearMap.ker (toEuclideanLin (H + lam • M)))ᗮ) (x : EuclideanSpace ℝ ι) :
    toScaled hM x = particular (isSymmetric_scaledOp hH) (scaledGrad hM g) lam ↔
      toEuclideanLin (H + lam • M) x = -g ∧
        ∀ v ∈ LinearMap.ker (toEuclideanLin (H + lam • M)), ⟪toEuclideanLin M x, v⟫ = 0 := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hg' := (scaledGrad_mem_orthogonal_iff (H := H) (hM := hM) lam g).2 hg
  obtain ⟨hsol, hiff, -, -⟩ := (particular_spec (hH := hT) (g := scaledGrad hM g) lam).2.1 hg'
  have hperp := (particular_spec (hH := hT) (g := scaledGrad hM g) lam).1
  constructor
  · intro h
    rw [← h] at hsol hperp
    exact ⟨(add_smul_scaledOp_toScaled_eq_neg_iff lam g x).1 hsol,
      (toScaled_mem_orthogonal_ker_iff lam x).1 hperp⟩
  · rintro ⟨h1, h2⟩
    have hk := (hiff _).1 ((add_smul_scaledOp_toScaled_eq_neg_iff lam g x).2 h1)
    have hp := Submodule.sub_mem _ ((toScaled_mem_orthogonal_ker_iff lam x).2 h2) hperp
    exact sub_eq_zero.1 (inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal hk hp))

/-- **`Subproblem.particular` of the scaled problem is the minimum-$M$-norm solution.** Let $H$ be a
real symmetric matrix, $M$ a real positive definite matrix, $\lambda \in \mathbb{R}$, and
$g \in \mathbb{R}^n$ orthogonal to the kernel of $H + \lambda M$. Let $x_*$ be
`Subproblem.particular` of the scaled problem for $M^{-1} g$, $M^{-1} H$ and $\lambda$, as a
vector of $\mathbb{R}^n$. Then $(H + \lambda M) x_* = -g$, and every $y \in \mathbb{R}^n$ with
$(H + \lambda M) y = -g$ satisfies
$$\langle M x_*, x_* \rangle \le \langle M y, y \rangle.$$

The system is (8.3.2) of [cartis2022evaluation]. -/
theorem particular_scaled_spec (hH : H.IsHermitian) {lam : ℝ} {g : EuclideanSpace ℝ ι}
    (hg : g ∈ (LinearMap.ker (toEuclideanLin (H + lam • M)))ᗮ) :
    toEuclideanLin (H + lam • M)
        ((toScaled hM).symm (particular (isSymmetric_scaledOp hH) (scaledGrad hM g) lam)) = -g ∧
      ∀ y, toEuclideanLin (H + lam • M) y = -g →
        ⟪toEuclideanLin M ((toScaled hM).symm
            (particular (isSymmetric_scaledOp hH) (scaledGrad hM g) lam)),
          (toScaled hM).symm (particular (isSymmetric_scaledOp hH) (scaledGrad hM g) lam)⟫ ≤
          ⟪toEuclideanLin M y, y⟫ := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hg' := (scaledGrad_mem_orthogonal_iff (H := H) (hM := hM) lam g).2 hg
  obtain ⟨hsol, -, hmin, -⟩ := (particular_spec (hH := hT) (g := scaledGrad hM g) lam).2.1 hg'
  set p := particular hT (scaledGrad hM g) lam
  have hp : toScaled hM ((toScaled hM).symm p) = p := (toScaled hM).apply_symm_apply p
  refine ⟨(add_smul_scaledOp_toScaled_eq_neg_iff lam g _).1 (by rw [hp]; exact hsol),
    fun y hy => ?_⟩
  rw [← norm_toScaled_sq, ← norm_toScaled_sq, hp]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (hmin _ ((add_smul_scaledOp_toScaled_eq_neg_iff lam g y).2 hy)) 2

/-! ### The Hessian and the stopping rules -/

/-- **The Hessian of the regularized model in the scaled setting.** Let $H$ be a real matrix and $M$
a real positive definite matrix, and let $\sigma, r \in \mathbb{R}$ and
$s, v, w \in \mathbb{R}^n$. Put $\nu = \|s\|_M$. Then the Hessian $\nabla^2 m^R(s)$ of the
operator regularized model of $M^{-1} g$ and $M^{-1} H$ satisfies
$$\langle v, \nabla^2 m^R(s) w \rangle_M = v^T \left(H + \sigma \nu^{r-2} M + (r - 2) \sigma
  \nu^{r-4} (M s)(M s)^T\right) w.$$

The right side is the Hessian (8.2.34) of [cartis2022evaluation] in the matrix setting. The
Hessian on the left is `Subproblem.regModelHessian`, and $\nu$ is given by
`Subproblem.norm_toScaled`. -/
theorem inner_regModelHessian_scaled (σ r : ℝ) (s v w : EuclideanSpace ℝ ι) :
    ⟪toScaled hM v, regModelHessian (scaledOp H hM) σ r (toScaled hM s) (toScaled hM w)⟫ =
      ⟪v, toEuclideanLin H w⟫ + σ * ‖toScaled hM s‖ ^ (r - 2) * ⟪v, toEuclideanLin M w⟫ +
        (r - 2) * σ * ‖toScaled hM s‖ ^ (r - 4) *
          (⟪toEuclideanLin M s, v⟫ * ⟪toEuclideanLin M s, w⟫) := by
  have hMs := isSymmetric_toEuclideanLin_iff.2 hM.isHermitian
  have e1 : ⟪toScaled hM v, scaledOp H hM (toScaled hM w)⟫ = ⟪v, toEuclideanLin H w⟫ := by
    rw [real_inner_comm, inner_scaledOp_toScaled, real_inner_comm]
  have e2 : ⟪toScaled hM v, toScaled hM w⟫ = ⟪v, toEuclideanLin M w⟫ := by
    rw [inner_toScaled]; exact hMs v w
  have e3 : ⟪toScaled hM v, toScaled hM s⟫ = ⟪toEuclideanLin M s, v⟫ := by
    rw [real_inner_comm, inner_toScaled]
  have e4 : ⟪toScaled hM s, toScaled hM w⟫ = ⟪toEuclideanLin M s, w⟫ := inner_toScaled s w
  rw [regModelHessian_apply]
  simp only [inner_add_right, inner_smul_right, e1, e2, e3, e4]
  ring

/-- **The stopping rules (9.3.14) in the scaled setting.** Let $H$ be a real matrix and $M$ a real
positive definite matrix, let $\sigma, \theta_1, \theta_2 \in \mathbb{R}$ and $r \neq 0$, and
let $g, s \in \mathbb{R}^n$. Put $\nu = \|s\|_M$. Then the operator stopping rules
`Subproblem.RegStoppingRules` for $M^{-1} g$ and $M^{-1} H$ hold at $s$ if and only if the
following three conditions hold:
* (9.3.14a) $\langle g, s \rangle + \frac12 \langle s, H s \rangle + \frac{\sigma}{r} \nu^r \le
  0$;
* (9.3.14b) $\|g + H s + \sigma \nu^{r-2} M s\|_{M^{-1}} \le \frac12 \theta_1 \nu^2$, where
  $\|v\|_{M^{-1}} = \sqrt{\langle v, M^{-1} v \rangle}$;
* (9.3.14c) for every $w \in \mathbb{R}^n$, $-\theta_2 \nu \langle M w, w \rangle \le w^T
  \left(H + \sigma \nu^{r-2} M + (r - 2) \sigma \nu^{r-4} (M s)(M s)^T\right) w$.

The rules are (9.3.14) of [cartis2022evaluation]. Rule (9.3.14c) uses the Hessian (8.2.34)
(`Subproblem.inner_regModelHessian_scaled`). It says that the least eigenvalue of the pencil
$(\nabla^2 m^R(s), M)$ is at least $-\theta_2 \nu$. The condition $r \neq 0$ makes the model
vanish at $s = 0$, so that rule (9.3.14a) takes the form above. -/
theorem regStoppingRules_scaled_iff {σ r θ₁ θ₂ : ℝ} (hr : r ≠ 0) (g s : EuclideanSpace ℝ ι) :
    RegStoppingRules (scaledGrad hM g) (scaledOp H hM) σ r θ₁ θ₂ (toScaled hM s) ↔
      ⟪g, s⟫ + (1 / 2) * ⟪s, toEuclideanLin H s⟫ + σ / r * ‖toScaled hM s‖ ^ r ≤ 0 ∧
      √⟪g + toEuclideanLin H s + (σ * ‖toScaled hM s‖ ^ (r - 2)) • toEuclideanLin M s,
          toEuclideanLin M⁻¹
            (g + toEuclideanLin H s + (σ * ‖toScaled hM s‖ ^ (r - 2)) • toEuclideanLin M s)⟫ ≤
        (1 / 2) * θ₁ * ‖toScaled hM s‖ ^ 2 ∧
      ∀ w, -(θ₂ * ‖toScaled hM s‖) * ⟪toEuclideanLin M w, w⟫ ≤
        ⟪w, toEuclideanLin H w⟫ + σ * ‖toScaled hM s‖ ^ (r - 2) * ⟪w, toEuclideanLin M w⟫ +
          (r - 2) * σ * ‖toScaled hM s‖ ^ (r - 4) *
            (⟪toEuclideanLin M s, w⟫ * ⟪toEuclideanLin M s, w⟫) := by
  set lam := σ * ‖toScaled hM s‖ ^ (r - 2)
  have hdec : regModel (scaledGrad hM g) (scaledOp H hM) σ r (toScaled hM s) =
      ⟪g, s⟫ + (1 / 2) * ⟪s, toEuclideanLin H s⟫ + σ / r * ‖toScaled hM s‖ ^ r := by
    rw [regModel_def, ← quadModel_scaled]
  have hgrad : scaledGrad hM g + scaledOp H hM (toScaled hM s) + lam • toScaled hM s =
      scaledGrad hM (g + toEuclideanLin H s + lam • toEuclideanLin M s) := by
    rw [scaledGrad_gradient, _root_.add_apply, _root_.smul_apply, one_apply_eq_self, add_assoc]
  have hnorm : ∀ u : ScaledSpace hM, ‖u‖ = √(‖u‖ ^ 2) := fun u =>
    (Real.sqrt_sq (norm_nonneg u)).symm
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, fun w => ?_⟩
    · rwa [hdec, regModel_zero _ _ _ hr] at h1
    · rwa [hgrad, hnorm, norm_scaledGrad_sq] at h2
    · have := h3 (toScaled hM w)
      rwa [inner_regModelHessian_scaled, norm_toScaled_sq] at this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, fun u => ?_⟩
    · rwa [hdec, regModel_zero _ _ _ hr]
    · rwa [hgrad, hnorm, norm_scaledGrad_sq]
    · obtain ⟨w, rfl⟩ := (toScaled hM).surjective u
      rw [inner_regModelHessian_scaled, norm_toScaled_sq]
      exact h3 w

/-! ### Eigenvalues and eigenvectors -/

/-- The $M$-inner product space has dimension $n$, the cardinality of the index type. -/
theorem finrank_scaledSpace : Module.finrank ℝ (ScaledSpace hM) = Fintype.card ι := by
  rw [← (toScaled hM).finrank_eq, finrank_euclideanSpace]

/-- Let $H$ be a real matrix and $M$ a real positive definite matrix. If $v \in \mathbb{R}^n$ and
$\mu \in \mathbb{R}$ satisfy the generalized eigenvalue equation $H v = \mu M v$ of the pencil
$(H, M)$, then
$$M^{-1} H v = \mu v$$
in $E_M$.

With `Subproblem.inner_toScaled`, generalized eigenvectors that are $M$-orthonormal,
$V^T M V = I$ as in (8.2.5) of [cartis2022evaluation], are orthonormal eigenvectors of the
scaled operator. `Subproblem.inner_toScaled_scaledGrad` gives their coordinates
$\gamma_i = v_i^T g$. -/
theorem scaledOp_toScaled_of_eigen {v : EuclideanSpace ℝ ι} {μ : ℝ}
    (hv : toEuclideanLin H v = μ • toEuclideanLin M v) :
    scaledOp H hM (toScaled hM v) = μ • toScaled hM v := by
  rw [scaledOp_toScaled, hv, map_smul, toEuclideanLin_nonsing_inv_mul_apply hM.isUnit, map_smul]

/-- The real quadratic form of a matrix $A$ in coordinates: $\langle A y, y \rangle = y^T A y$. -/
private theorem inner_toEuclideanLin_toLp (A : Matrix ι ι ℝ) (y : ι → ℝ) :
    ⟪toEuclideanLin A (WithLp.toLp 2 y), WithLp.toLp 2 y⟫ = star y ⬝ᵥ A *ᵥ y := by
  rw [toEuclideanLin_toLp, EuclideanSpace.inner_toLp_toLp_real, star_trivial, dotProduct_comm]

/-- **The eigenvalues of the scaled operator are the pencil eigenvalues.** Let $H$ be a real
symmetric matrix and $M$ a real positive definite matrix. Then the eigenvalues of the symmetric
operator $M^{-1} H$ on $E_M$, in decreasing order, are the eigenvalues
`Matrix.pencilEigenvalues` of the pencil $(H, M)$, in decreasing order.

Both families are characterized by the Courant–Fischer max–min principle for the Rayleigh
quotient $\langle H x, x \rangle / \langle M x, x \rangle$. -/
theorem eigenvalues_scaledOp (hH : H.IsHermitian) :
    (isSymmetric_scaledOp (hM := hM) hH).eigenvalues finrank_scaledSpace =
      pencilEigenvalues hH hM := by
  funext i
  set Φ : (ι → ℝ) ≃ₗ[ℝ] ScaledSpace hM := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.trans (toScaled hM)
  have hΦ : ∀ y, (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM).rayleighQuotient (Φ y) =
      RCLike.re (star y ⬝ᵥ H *ᵥ y) / RCLike.re (star y ⬝ᵥ M *ᵥ y) := fun y => by
    simp only [LinearMap.rayleighQuotient, RCLike.re_to_real, ContinuousLinearMap.coe_coe]
    rw [norm_sq_eq_re_inner (𝕜 := ℝ), RCLike.re_to_real]
    change ⟪scaledOp H hM (toScaled hM (WithLp.toLp 2 y)), toScaled hM (WithLp.toLp 2 y)⟫ /
      ⟪toScaled hM (WithLp.toLp 2 y), toScaled hM (WithLp.toLp 2 y)⟫ = _
    rw [inner_scaledOp_toScaled, inner_toScaled, inner_toEuclideanLin_toLp,
      inner_toEuclideanLin_toLp]
  have h1 := (isSymmetric_scaledOp (hM := hM) hH).isGreatest_eigenvalues finrank_scaledSpace i
  rw [Matrix.setOf_exists_submodule_eq Φ hΦ _ (· ≤ ·)] at h1
  exact h1.unique (isGreatest_pencilEigenvalues hH hM i)

/-- **The leftmost eigenvalue of the scaled operator is the least pencil eigenvalue.** Let $H$ be a
real symmetric matrix and $M$ a real positive definite matrix. Then the leftmost eigenvalue of
$M^{-1} H$ on $E_M$ is the least eigenvalue $\lambda_1$ of the pencil $(H, M)$:
$$\lambda_1(M^{-1} H) = \min_i \lambda_i(H, M).$$

The pencil eigenvalues are those of (8.2.5) of [cartis2022evaluation]. So
`Subproblem.shiftThreshold` of the scaled operator is the number
$\lambda_s = \max\{0, -\lambda_1\}$ of the source. The minimum is written as an infimum over
`Matrix.pencilEigenvalues`. For $n = 0$ both sides are $0$. -/
theorem leftmost_scaledOp (hH : H.IsHermitian) :
    leftmost (isSymmetric_scaledOp (hM := hM) hH) = ⨅ i, pencilEigenvalues hH hM i := by
  rw [← eigenvalues_scaledOp hH, leftmost]
  simp_rw [LinearMap.IsSymmetric.eigenvalues_eq_cast _ finrank_scaledSpace]
  exact ((finCongr finrank_scaledSpace.symm).iInf_comp
    (g := fun j => (isSymmetric_scaledOp (hM := hM) hH).eigenvalues rfl j)).symm

/-- **The norm of the scaled operator.** Let $H$ be a real symmetric matrix and $M$ a real positive
definite matrix. Then the operator norm of $M^{-1} H$ on $E_M$ is at most the Euclidean operator
norm of the matrix $M^{-1} H$:
$$\|M^{-1} H\|_{E_M} \le \|M^{-1} H\|_2.$$

The operator norm of a symmetric operator is its largest absolute eigenvalue, and each
eigenvalue $\mu$ of $M^{-1} H$ satisfies $|\mu| \le \|M^{-1} H\|_2$. The right side is the norm
of `toEuclideanLin (M⁻¹ * H)` as a continuous linear map, which is the matrix $\ell^2$ operator
norm by `Matrix.l2_opNorm_eq_norm_toEuclideanLin`. -/
theorem norm_scaledOp_le (hH : H.IsHermitian) :
    ‖scaledOp H hM‖ ≤ ‖LinearMap.toContinuousLinearMap (toEuclideanLin (M⁻¹ * H))‖ := by
  set C := ‖LinearMap.toContinuousLinearMap (toEuclideanLin (M⁻¹ * H))‖
  have hT := isSymmetric_scaledOp (hM := hM) hH
  set b := hT.eigenvectorBasis rfl
  set μ := hT.eigenvalues rfl
  -- every eigenvalue is bounded by `C`
  have hμ : ∀ i, |μ i| ≤ C := fun i => by
    obtain ⟨x, hx⟩ := (toScaled hM).surjective (b i)
    have hx0 : x ≠ 0 := by
      rintro rfl; exact (b.orthonormal.ne_zero i) (by rw [← hx, map_zero])
    have heig : scaledOp H hM (b i) = μ i • b i := apply_eigenvectorBasis' (hH := hT) i
    rw [← hx, scaledOp_toScaled, ← map_smul] at heig
    have hMH : toEuclideanLin (M⁻¹ * H) x = μ i • x := by
      rw [toEuclideanLin_mul_apply]; exact (toScaled hM).injective heig
    have hle := (LinearMap.toContinuousLinearMap (toEuclideanLin (M⁻¹ * H))).le_opNorm x
    rw [LinearMap.coe_toContinuousLinearMap', hMH, norm_smul, Real.norm_eq_abs] at hle
    exact le_of_mul_le_mul_right hle (norm_pos_iff.2 hx0)
  have hC : 0 ≤ C := norm_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun u => ?_
  have hcoord : ∀ i, ⟪b i, scaledOp H hM u⟫ = μ i * ⟪b i, u⟫ := fun i => by
    rw [← ContinuousLinearMap.coe_coe, ← hT, ContinuousLinearMap.coe_coe,
      apply_eigenvectorBasis' (hH := hT) i, real_inner_smul_left]
  have hsq : ‖scaledOp H hM u‖ ^ 2 ≤ (C * ‖u‖) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_sum_eigenvectorBasis (hH := hT), mul_pow,
      ← real_inner_self_eq_norm_sq u, inner_eq_sum_eigenvectorBasis (hH := hT), Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hcoord]
    have : (μ i) ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hμ i) 2
    nlinarith [sq_nonneg ⟪b i, u⟫]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-! ### Generalized eigenvectors and the scaled gradient -/

/-- Let $M$ be a real positive definite matrix. If $g \in \mathbb{R}^n$ is nonzero, then the scaled
gradient $M^{-1} g$ is nonzero. -/
theorem scaledGrad_ne_zero {g : EuclideanSpace ℝ ι} (hg : g ≠ 0) : scaledGrad hM g ≠ 0 := by
  intro h
  apply hg
  have h2 : toEuclideanLin M⁻¹ g = 0 := by
    rw [scaledGrad, LinearEquiv.map_eq_zero_iff] at h; exact h
  rw [← toEuclideanLin_mul_nonsing_inv_apply hM.isUnit g, h2, map_zero]

/-- The scaled gradient of $g = 0$ is $0$. -/
@[simp]
theorem scaledGrad_zero : scaledGrad hM (0 : EuclideanSpace ℝ ι) = 0 := by
  simp [scaledGrad]

/-- Let $H$ be a real matrix and $M$ a real positive definite matrix. If $u \in \mathbb{R}^n$ and
$c \in \mathbb{R}$ satisfy $M^{-1} H u = c u$ in $E_M$, then $u$ satisfies the generalized
eigenvalue equation
$$H u = c M u.$$

This is the converse of `Subproblem.scaledOp_toScaled_of_eigen`. -/
theorem eigen_of_scaledOp_eq {u : EuclideanSpace ℝ ι} {c : ℝ}
    (h : scaledOp H hM (toScaled hM u) = c • toScaled hM u) :
    toEuclideanLin H u = c • toEuclideanLin M u := by
  rw [scaledOp_toScaled, ← map_smul, (toScaled hM).injective.eq_iff] at h
  have := congrArg (toEuclideanLin M) h
  rwa [toEuclideanLin_mul_nonsing_inv_apply hM.isUnit, map_smul] at this

/-- Let $H$ be a real matrix, $M$ a real positive definite matrix, and $\mu \in \mathbb{R}$. If
$w \in E_M$ lies in the kernel of $M^{-1} H + \mu I$, then $w$, as a vector of $\mathbb{R}^n$,
satisfies the generalized eigenvalue equation
$$H w = -\mu M w.$$
-/
theorem eigen_of_mem_ker {μ : ℝ} {w : ScaledSpace hM}
    (hw : w ∈ LinearMap.ker ((scaledOp H hM + μ • 1 : ScaledSpace hM →L[ℝ] ScaledSpace hM) :
      ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)) :
    toEuclideanLin H ((toScaled hM).symm w) = (-μ) • toEuclideanLin M ((toScaled hM).symm w) := by
  rw [← (toScaled hM).apply_symm_apply w, toScaled_mem_ker_iff, LinearMap.mem_ker, map_add,
    map_smul, LinearMap.add_apply, LinearMap.smul_apply] at hw
  rw [neg_smul, eq_neg_iff_add_eq_zero]
  exact hw

/-- Let $H$ be a real matrix and $M$ a real positive definite matrix, and let $g \in \mathbb{R}^n$.
Then $M^{-1} H (M^{-1} g) = c M^{-1} g$ for some $c \in \mathbb{R}$ if and only if there are
$v \in \mathbb{R}^n$ and $c \in \mathbb{R}$ with
$$M v = g \quad \text{and} \quad H v = c M v.$$
That is, $M^{-1} g$ is an eigenvector of $M^{-1} H$ or zero if and only if $g = M v$ for a
generalized eigenvector $v$ of the pencil $(H, M)$ or for $v = 0$. -/
theorem exists_scaledOp_scaledGrad_eq_iff {g : EuclideanSpace ℝ ι} :
    (∃ c : ℝ, scaledOp H hM (scaledGrad hM g) = c • scaledGrad hM g) ↔
      ∃ (v : EuclideanSpace ℝ ι) (c : ℝ), toEuclideanLin M v = g ∧
        toEuclideanLin H v = c • toEuclideanLin M v := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨toEuclideanLin M⁻¹ g, c, toEuclideanLin_mul_nonsing_inv_apply hM.isUnit g, ?_⟩
    exact eigen_of_scaledOp_eq hc
  · rintro ⟨v, c, rfl, hv⟩
    refine ⟨c, ?_⟩
    rw [scaledGrad, toEuclideanLin_nonsing_inv_mul_apply hM.isUnit]
    exact scaledOp_toScaled_of_eigen hv

/-- Let $H$ be a real symmetric matrix and $M$ a real positive definite matrix. Then every
eigenvalue $\mu$ of the scaled operator $M^{-1} H$ on $E_M$ is a generalized eigenvalue of the
pencil $(H, M)$: there is $u \in \mathbb{R}^n$ with $u \neq 0$ and
$$H u = \mu M u.$$

The eigenvalue $\mu$ is the $i$-th entry of the eigenvalue list of
`Subproblem.isSymmetric_scaledOp`, for any index $i$. -/
theorem exists_eigen_of_eigenvalues (hH : H.IsHermitian)
    (i : Fin (Module.finrank ℝ (ScaledSpace hM))) :
    ∃ u : EuclideanSpace ℝ ι, u ≠ 0 ∧ toEuclideanLin H u =
      (isSymmetric_scaledOp (hM := hM) hH).eigenvalues rfl i • toEuclideanLin M u := by
  set hT := isSymmetric_scaledOp (hM := hM) hH
  refine ⟨(toScaled hM).symm (hT.eigenvectorBasis rfl i), ?_, eigen_of_scaledOp_eq (hM := hM) ?_⟩
  · simpa using (hT.eigenvectorBasis rfl).orthonormal.ne_zero i
  · rw [LinearEquiv.apply_symm_apply]; exact apply_eigenvectorBasis' (hH := hT) i

/-- **The rightmost eigenvalue of the scaled operator is the largest pencil eigenvalue.** Let $H$ be
a real symmetric matrix and $M$ a real positive definite matrix. Then the rightmost eigenvalue
of $M^{-1} H$ on $E_M$ is the largest eigenvalue $\lambda_n$ of the pencil $(H, M)$:
$$\lambda_n(M^{-1} H) = \max_i \lambda_i(H, M).$$

The maximum is written as a supremum over `Matrix.pencilEigenvalues`. For $n = 0$ both sides are
$0$. -/
theorem rightmost_scaledOp (hH : H.IsHermitian) :
    rightmost (isSymmetric_scaledOp (hM := hM) hH) = ⨆ i, pencilEigenvalues hH hM i := by
  rw [← eigenvalues_scaledOp hH, rightmost]
  simp_rw [LinearMap.IsSymmetric.eigenvalues_eq_cast _ finrank_scaledSpace]
  exact ((finCongr finrank_scaledSpace.symm).iSup_comp
    (g := fun j => (isSymmetric_scaledOp (hM := hM) hH).eigenvalues rfl j)).symm

end Subproblem
