/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Numlib.Eigen.Pencil
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz
import Numlib.Variational.Evolution

/-!
# The θ-method for the system $M u' + A u = f$

This module studies the linear system of ordinary differential equations $M u' + A u = f$, where the
mass matrix $M$ is symmetric positive definite and $A$ is the stiffness matrix. The system is the
semi-discretization in space of a parabolic problem, by finite differences ($M = 1$ and $A = \nu
h^{-2} \operatorname{tridiag}(-1, 2, -1)$) or by finite elements (the Galerkin method in a basis).
The θ-method advances it in time by
$$(M + \theta \Delta t A) u^{k+1} = (M - (1 - \theta) \Delta t A) u^k + \Delta t (\theta f^{k+1} +
  (1 - \theta) f^k).$$
The presentation follows [quarteroni2000numerical], §13.2–13.3, equations (13.8)–(13.11) and
(13.14)–(13.16). With the $M$-inner product $\langle x, y \rangle_M = x^T M y$, the module is the
matrix form of `Numlib.Variational.Evolution`: the semi-discrete system is the Galerkin equation for
the form $(x, y) \mapsto (Ax) \cdot y$, and the θ-step is the form-level θ-step for that form. The
stability in the $M$-norm is therefore unconditional for $\theta \ge 1/2$, and for $\theta < 1/2$ it
holds under $(1 - 2\theta) \lambda_{\max} \Delta t \le 2$, where $\lambda_{\max}$ bounds the
generalized eigenvalues of the pencil $(A, M)$. A Galerkin semi-discretization in a basis $\varphi$
is this system with $M$ and $A$ the Gram matrices of the inner product and of the form ((13.13) is
equivalent to (13.14)), and the same holds for the θ-step ((13.17) is equivalent to (13.16)).

The exact threshold for asymptotic stability needs the generalized eigenvalues $\lambda_i$
themselves. The iterates of the source-free θ-method tend to $0$ from every initial value if and
only if every amplification factor
$$r_\theta(\lambda_i \Delta t) = \frac{1 - (1 - \theta) \lambda_i \Delta t}{1 + \theta \lambda_i
  \Delta t}$$
has modulus less than $1$. For $M = 1$ and the finite difference Laplacian $A = (\nu / h^2)
\operatorname{tridiag}(-1, 2, -1)$ of order $m$, the eigenvalues are
$(4\nu / h^2) \sin^2((k+1)\pi / (2(m+1)))$, and the forward Euler method is asymptotically stable if
and only if $\Delta t (4\nu / h^2) \sin^2(m\pi / (2(m+1))) < 2$. The classical condition
$\Delta t \le h^2 / (2\nu)$ of [quarteroni2000numerical], (13.11), is sufficient for this, but it is
not necessary, although the source states it as an equivalence. The backward Euler method is
unconditionally asymptotically stable.

## Main definitions

* `FiniteDifference.IsSemidiscrete`: $u$ solves $M u' + A u = f$ on $[0, T]$ with $u(0) = u_0$.
* `FiniteDifference.thetaStep`: one step $u \mapsto (M + \theta \Delta t A)^{-1} ((M - (1 - \theta)
  \Delta t A) u + \Delta t (\theta f_1 + (1 - \theta) f_0))$ of the θ-method.
* `FiniteDifference.thetaAmplification`: the amplification matrix $(M + \theta \Delta t A)^{-1} (M -
  (1 - \theta) \Delta t A)$.
* `FiniteDifference.thetaFactor`: the amplification factor $r_\theta(\lambda \Delta t)$.
* `FiniteDifference.MassSpace`: $\mathbb{R}^n$ with the $M$-inner product.
* `FiniteDifference.massForm`: the bilinear form $(x, y) \mapsto (Ax) \cdot y$ on the $M$-space.

## Main results

* `FiniteDifference.IsSemidiscrete.iff_normalForm`: for invertible $M$, the system is
  $u' = -M^{-1} A u + M^{-1} f$.
* `FiniteDifference.isSemidiscreteGalerkin_iff_isSemidiscrete`: a semi-discrete Galerkin problem in
  a basis is the system $M \xi' + A \xi = f$ for the coordinates.
* `Variational.IsThetaStep.iff_thetaStep`: the form-level θ-step in a basis is the matrix θ-step for
  the coordinates.
* `FiniteDifference.isThetaStep_toMass_iff`: the matrix θ-step is the form-level θ-step in the
  $M$-space.
* `FiniteDifference.thetaStep_dotProduct_mulVec_le`: for $\theta \ge 1/2$ the θ-method does not
  increase the $M$-norm.
* `FiniteDifference.thetaStep_dotProduct_mulVec_le_of_le`: for $\theta \ge 0$ and
  $(1 - 2\theta) \lambda_{\max} \Delta t \le 2$ the θ-method does not increase the $M$-norm.
* `FiniteDifference.thetaAmplification_eq_conj`: the amplification matrix is $W
  \operatorname{diag}(r_\theta(d_i \Delta t)) W^{-1}$.
* `FiniteDifference.forall_tendsto_thetaStep_iff`: asymptotic stability holds if and only if $|1 -
  (1 - \theta) \lambda \Delta t| < 1 + \theta \lambda \Delta t$ for every generalized eigenvalue
  $\lambda$.
* `FiniteDifference.backwardEuler_tendsto`: the backward Euler method is unconditionally
  asymptotically stable.
* `FiniteDifference.forwardEuler_heat_tendsto_iff`: the exact threshold for the forward Euler method
  on the finite difference heat equation.
* `FiniteDifference.forwardEuler_heat_tendsto_of_le`: the condition $\Delta t \le h^2 / (2\nu)$ is
  sufficient.

## Proof outline

The stability results in the $M$-norm are the form-level theorems of `Numlib.Variational.Evolution`,
read in the $M$-space. For asymptotic stability, the simultaneous diagonalization of the
symmetric-definite pencil $(A, M)$ (`Matrix.exists_simultaneous_diagonalization`) gives $W$ with
$W^T M W = 1$ and $W^T A W = \operatorname{diag}(d)$. The amplification matrix is then similar to
$\operatorname{diag}(r_\theta(d_i \Delta t))$, which gives its characteristic polynomial and its
real and complex spectra. Its powers tend to $0$ if and only if its spectral radius is less than
$1$.

## Implementation notes

* Matrices are real and indexed by a finite type with decidable equality. Vectors are functions
  `n → ℝ`, and $x^T M x$ is `x ⬝ᵥ (M *ᵥ x)`.
* The θ-step is defined with the inverse `Matrix.inv` of $M + \theta \Delta t A$, which is $0$ when
  that matrix is singular. `FiniteDifference.mulVec_thetaStep` says that the step solves its linear
  system when the matrix is invertible. `FiniteDifference.isUnit_add_smul_of_posDef` gives
  invertibility when $M$ is positive definite, the quadratic form of $A$ is positive semidefinite,
  and $\theta \Delta t \ge 0$. No symmetry of $A$ is needed there, so nonsymmetric transport
  matrices are included.
* The $M$-space `FiniteDifference.MassSpace` is the energy space `WithEnergy` of the Euclidean
  operator of $M$.
* The generalized eigenvalues of the pencil $(A, M)$ form the set `Matrix.pencilSpectrum A M` of the
  $\lambda$ with $\det(A - \lambda M) = 0$. In the conditional stability theorem the bound
  $\lambda_{\max}$ is given as the quadratic-form bound $x^T A x \le \lambda_{\max} x^T M x$.
-/

open Set Filter Topology Matrix
open scoped RealInnerProductSpace

noncomputable section

namespace FiniteDifference

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The semi-discrete system -/

/-- **The semi-discrete system** ([quarteroni2000numerical], (13.8) with $M = 1$, and (13.14) in
general). Let $M, A \in \mathbb{R}^{n \times n}$, $f \colon \mathbb{R} \to \mathbb{R}^n$,
$u_0 \in \mathbb{R}^n$ and $T \in \mathbb{R}$. A function $u \colon \mathbb{R} \to \mathbb{R}^n$
**solves the semi-discrete system** $M u' + A u = f$ on $[0, T]$ with initial value $u_0$ if
$u(0) = u_0$ and there is $u' \colon \mathbb{R} \to \mathbb{R}^n$ such that, for every
$t \in [0, T]$, $u'(t)$ is the derivative of $u$ at $t$ within $[0, T]$ and
$$M u'(t) + A u(t) = f(t).$$

The form of the definition is the same as that of `Variational.IsSemidiscreteGalerkin`. -/
def IsSemidiscrete (M A : Matrix n n ℝ) (f : ℝ → n → ℝ) (u₀ : n → ℝ) (T : ℝ)
    (u : ℝ → n → ℝ) : Prop :=
  u 0 = u₀ ∧ ∃ u' : ℝ → n → ℝ, ∀ t ∈ Icc 0 T,
    HasDerivWithinAt u (u' t) (Icc 0 T) t ∧ M *ᵥ u' t + A *ᵥ u t = f t

/-- **The normal form** ([quarteroni2000numerical], (13.15)). Let $M \in \mathbb{R}^{n \times n}$ be
invertible and let $A \in \mathbb{R}^{n \times n}$. Then $u$ solves $M u' + A u = f$ on $[0, T]$
with initial value $u_0$ if and only if $u$ solves
$$u' + M^{-1} A u = M^{-1} f$$
on $[0, T]$ with the same initial value, that is, the system with mass matrix $1$, stiffness
matrix $M^{-1} A$ and source $M^{-1} f$. -/
theorem IsSemidiscrete.iff_normalForm {M : Matrix n n ℝ} (hM : IsUnit M) (A : Matrix n n ℝ)
    (f : ℝ → n → ℝ) (u₀ : n → ℝ) (T : ℝ) (u : ℝ → n → ℝ) :
    IsSemidiscrete M A f u₀ T u ↔
      IsSemidiscrete 1 (M⁻¹ * A) (fun t => M⁻¹ *ᵥ f t) u₀ T u := by
  have hdet := (isUnit_iff_isUnit_det M).1 hM
  have key : ∀ v w g : n → ℝ, M *ᵥ v + A *ᵥ w = g ↔ 1 *ᵥ v + (M⁻¹ * A) *ᵥ w = M⁻¹ *ᵥ g := by
    intro v w g
    constructor
    · rintro rfl
      rw [one_mulVec, mulVec_add, mulVec_mulVec, mulVec_mulVec, nonsing_inv_mul _ hdet,
        one_mulVec]
    · intro h
      have := congrArg (M *ᵥ ·) h
      simpa only [one_mulVec, mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc,
        mul_nonsing_inv _ hdet, Matrix.one_mul] using this
  simp only [IsSemidiscrete, key]

/-! ### The coordinate bridge -/

section Bridge

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] {ι : Type*} [Fintype ι]

/-- The coordinate form of one Galerkin equation. Let $K$ be a real inner product space with a basis
$(\varphi_i)_{i \in \iota}$ indexed by a finite type, let $a$ be a bounded bilinear form on $K$,
let $F$ be a continuous linear functional on $K$, and let $w, z \in K$. Then
$\langle w, v \rangle + a(z, v) = F(v)$ for every $v \in K$ if and only if
$$M \xi_w + A \xi_z = (F(\varphi_i))_i,$$
where $\xi_w$ and $\xi_z$ are the coordinates of $w$ and $z$ in the basis,
$M_{ij} = \langle \varphi_j, \varphi_i \rangle$ is the mass matrix and
$A_{ij} = a(\varphi_j, \varphi_i)$ is the stiffness matrix.

Testing on the basis suffices because both sides are linear in $v$. The matrices are
`SesqForm.gramMatrix` of `innerSL ℝ` and of $a$. -/
theorem forall_inner_add_eq_iff (φ : Module.Basis ι ℝ K) (a : SesqForm ℝ K) (F : K →L[ℝ] ℝ)
    (w z : K) :
    (∀ v, ⟪w, v⟫ + a z v = F v) ↔
      SesqForm.gramMatrix (innerSL ℝ) φ *ᵥ φ.equivFun w + a.gramMatrix φ *ᵥ φ.equivFun z
        = fun i => F (φ i) := by
  have hM : ∀ i, (SesqForm.gramMatrix (innerSL ℝ) φ *ᵥ φ.equivFun w) i = ⟪w, φ i⟫ := fun i => by
    rw [SesqForm.gramMatrix_mulVec_apply, φ.sum_equivFun, innerSL_apply_apply]
  have hA : ∀ i, (a.gramMatrix φ *ᵥ φ.equivFun z) i = a z (φ i) := fun i => by
    rw [SesqForm.gramMatrix_mulVec_apply, φ.sum_equivFun]
  constructor
  · intro h
    funext i
    rw [Pi.add_apply, hM, hA, h]
  · intro h v
    have hL : ((innerSL ℝ w + a z - F : K →L[ℝ] ℝ) : K →ₗ[ℝ] ℝ) = 0 := by
      refine φ.ext fun i => ?_
      have := congrFun h i
      rw [Pi.add_apply, hM, hA] at this
      simp only [ContinuousLinearMap.coe_coe, _root_.sub_apply, _root_.add_apply,
        innerSL_apply_apply, LinearMap.zero_apply, this, sub_self]
    have := LinearMap.congr_fun hL v
    simp only [ContinuousLinearMap.coe_coe, _root_.sub_apply, _root_.add_apply,
      innerSL_apply_apply, LinearMap.zero_apply] at this
    linarith

variable [FiniteDimensional ℝ K]

-- the linter does not see the `Fintype` inside the sup norm of `ι → ℝ`
set_option linter.unusedFintypeInType false in
/-- Derivatives transfer along the coordinate map of a basis. Let $K$ be a finite-dimensional real
inner product space with a basis $\varphi$ indexed by a finite type, let
$u \colon \mathbb{R} \to K$, $u' \in K$, $s \subseteq \mathbb{R}$ and $t \in \mathbb{R}$. Then
the coordinates of $u$ have the derivative the coordinates of $u'$ at $t$ within $s$ if and only
if $u$ has the derivative $u'$ at $t$ within $s$. -/
theorem hasDerivWithinAt_equivFun_iff (φ : Module.Basis ι ℝ K) (u : ℝ → K) (u' : K) (s : Set ℝ)
    (t : ℝ) :
    HasDerivWithinAt (fun t => φ.equivFun (u t)) (φ.equivFun u') s t ↔
      HasDerivWithinAt u u' s t := by
  set e : K ≃L[ℝ] (ι → ℝ) := φ.equivFun.toContinuousLinearEquiv
  constructor
  · intro h
    have := (e.symm.hasFDerivAt.comp_hasDerivWithinAt t h).congr_deriv (e.symm_apply_apply u')
    refine this.congr (fun x _ => ?_) ?_
    · exact (e.symm_apply_apply (u x)).symm
    · exact (e.symm_apply_apply (u t)).symm
  · intro h
    exact e.hasFDerivAt.comp_hasDerivWithinAt t h

/-- **The coordinate form of the semi-discrete Galerkin problem** ([quarteroni2000numerical], the
equivalence of (13.13) and (13.14)). Let $K$ be a finite-dimensional real inner product space
with a basis $(\varphi_i)_{i \in \iota}$ indexed by a finite type, let $a$ be a bounded bilinear
form on $K$ that does not depend on time, let $F(t)$ be continuous linear functionals on $K$,
and let $u_0 \in K$ and $T \in \mathbb{R}$. Then $u \colon \mathbb{R} \to K$ solves the
semi-discrete Galerkin problem for $a$, $F$ and $u_0$ on $[0, T]$ if and only if its coordinates
$\xi(t)$ in the basis solve
$$M \xi' + A \xi = f$$
on $[0, T]$ with the initial value the coordinates of $u_0$, where
$M_{ij} = \langle \varphi_j, \varphi_i \rangle$, $A_{ij} = a(\varphi_j, \varphi_i)$ and
$f_i(t) = F(t)(\varphi_i)$.

The Galerkin problem is `Variational.IsSemidiscreteGalerkin` with the constant family of forms
$t \mapsto a$. -/
theorem isSemidiscreteGalerkin_iff_isSemidiscrete (φ : Module.Basis ι ℝ K) (a : SesqForm ℝ K)
    (F : ℝ → K →L[ℝ] ℝ) (u₀ : K) (T : ℝ) (u : ℝ → K) :
    Variational.IsSemidiscreteGalerkin (fun _ => a) F u₀ T u ↔
      IsSemidiscrete (SesqForm.gramMatrix (innerSL ℝ) φ) (a.gramMatrix φ)
        (fun t i => F t (φ i)) (φ.equivFun u₀) T (fun t => φ.equivFun (u t)) := by
  simp only [Variational.IsSemidiscreteGalerkin, IsSemidiscrete, φ.equivFun.injective.eq_iff]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨u', hu'⟩
    refine ⟨fun t => φ.equivFun (u' t), fun t ht => ?_⟩
    rw [hasDerivWithinAt_equivFun_iff, ← forall_inner_add_eq_iff φ]
    exact hu' t ht
  · rintro ⟨ξ', hξ'⟩
    refine ⟨fun t => φ.equivFun.symm (ξ' t), fun t ht => ?_⟩
    have h := hξ' t ht
    simp only
    rw [← hasDerivWithinAt_equivFun_iff φ, forall_inner_add_eq_iff φ,
      LinearEquiv.apply_symm_apply]
    exact h

-- the linter does not see the `Fintype` inside `Matrix.PosDef`
set_option linter.unusedFintypeInType false in
omit [FiniteDimensional ℝ K] in
/-- **The mass matrix is positive definite** ([quarteroni2000numerical], §13.3, after (13.14)). Let
$K$ be a real inner product space and let $(\varphi_i)_{i \in \iota}$ be a linearly independent
family in $K$, indexed by a finite type. Then the Gram matrix
$M_{ij} = \langle \varphi_j, \varphi_i \rangle$ is positive definite. -/
theorem massMatrix_posDef {φ : ι → K} (hφ : LinearIndependent ℝ φ) :
    (SesqForm.gramMatrix (innerSL ℝ) φ).PosDef :=
  SesqForm.gramMatrix_posDef one_pos SesqForm.innerSL_isHermitian SesqForm.innerSL_isCoerciveWith hφ

end Bridge

/-! ### The θ-method in matrix form -/

section ThetaStep

variable (M A : Matrix n n ℝ) (θ Δt : ℝ)

/-- **One step of the θ-method** ([quarteroni2000numerical], (13.10) and (13.16)). Let
$M, A \in \mathbb{R}^{n \times n}$ and $\theta, \Delta t \in \mathbb{R}$. The step takes the old
iterate $u$ and the sources $f_0$ at the old time and $f_1$ at the new time to
$$(M + \theta \Delta t A)^{-1} \bigl( (M - (1 - \theta) \Delta t A) u + \Delta t (\theta f_1 +
  (1 - \theta) f_0) \bigr).$$

The inverse is `Matrix.inv`, which is $0$ when $M + \theta \Delta t A$ is singular.
`FiniteDifference.mulVec_thetaStep` says that the step solves its linear system when the matrix
is invertible. -/
def thetaStep (f₀ f₁ u : n → ℝ) : n → ℝ :=
  (M + (θ * Δt) • A)⁻¹ *ᵥ ((M - ((1 - θ) * Δt) • A) *ᵥ u + Δt • (θ • f₁ + (1 - θ) • f₀))

/-- **The amplification matrix** of the θ-method: for $M, A \in \mathbb{R}^{n \times n}$ and
$\theta, \Delta t \in \mathbb{R}$, it is
$$(M + \theta \Delta t A)^{-1} (M - (1 - \theta) \Delta t A),$$
the homogeneous part of the step. The inverse is `Matrix.inv`, which is $0$ for a singular
matrix. -/
def thetaAmplification : Matrix n n ℝ :=
  (M + (θ * Δt) • A)⁻¹ * (M - ((1 - θ) * Δt) • A)

/-- **The amplification factor** of the θ-method on a mode with generalized eigenvalue $\lambda$
([quarteroni2000numerical], §13.3.1): for $\theta, \Delta t, \lambda \in \mathbb{R}$,
$$r_\theta(\lambda \Delta t) = \frac{1 - (1 - \theta) \lambda \Delta t}{1 + \theta \lambda
  \Delta t}.$$
It is $0$ when the denominator is $0$. -/
def thetaFactor (lam : ℝ) : ℝ := (1 - (1 - θ) * lam * Δt) / (1 + θ * lam * Δt)

/-- The θ-step is the amplification matrix applied to the old iterate, plus the source term:
$$u \mapsto (M + \theta \Delta t A)^{-1} (M - (1 - \theta) \Delta t A) u + (M + \theta \Delta t
  A)^{-1} \Delta t (\theta f_1 + (1 - \theta) f_0).$$
-/
theorem thetaStep_eq_mulVec_add (f₀ f₁ u : n → ℝ) :
    thetaStep M A θ Δt f₀ f₁ u = thetaAmplification M A θ Δt *ᵥ u
      + (M + (θ * Δt) • A)⁻¹ *ᵥ (Δt • (θ • f₁ + (1 - θ) • f₀)) := by
  simp only [thetaStep, thetaAmplification, mulVec_add, mulVec_mulVec]

/-- The θ-step with zero sources is the amplification matrix applied to the old iterate. -/
theorem thetaStep_zero_zero (u : n → ℝ) :
    thetaStep M A θ Δt 0 0 u = thetaAmplification M A θ Δt *ᵥ u := by
  simp [thetaStep_eq_mulVec_add]

variable {M A θ Δt}

/-- **The matrix of the θ-method is invertible** ([quarteroni2000numerical], §13.3, after (13.16)).
Let $M \in \mathbb{R}^{n \times n}$ be positive definite, let $A \in \mathbb{R}^{n \times n}$
satisfy $x^T A x \ge 0$ for every $x$, and let $c \ge 0$. Then $M + cA$ is invertible. With
$c = \theta \Delta t$ this is the matrix $K = M + \theta \Delta t A$ of the linear system of the
θ-method.

No symmetry of $A$ is needed: $x^T (M + cA) x > 0$ for $x \neq 0$ gives injectivity. -/
theorem isUnit_add_smul_of_posDef (hM : M.PosDef) (hA : ∀ x, 0 ≤ x ⬝ᵥ (A *ᵥ x)) {c : ℝ}
    (hc : 0 ≤ c) : IsUnit (M + c • A) := by
  rw [← mulVec_injective_iff_isUnit]
  intro x y hxy
  by_contra hne
  have hne' : x - y ≠ 0 := sub_ne_zero.2 hne
  have h0 : (M + c • A) *ᵥ (x - y) = 0 := by rw [mulVec_sub, hxy, sub_self]
  have h1 : 0 < (x - y) ⬝ᵥ (M *ᵥ (x - y)) := by simpa using hM.dotProduct_mulVec_pos hne'
  have h2 : 0 ≤ (x - y) ⬝ᵥ (A *ᵥ (x - y)) := hA _
  have h3 : (x - y) ⬝ᵥ ((M + c • A) *ᵥ (x - y)) = 0 := by rw [h0, dotProduct_zero]
  rw [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul] at h3
  nlinarith

/-- The θ-step solves its linear system. If $M + \theta \Delta t A$ is invertible, then the θ-step
$u'$ of $u$ with the sources $f_0, f_1$ satisfies
$$(M + \theta \Delta t A) u' = (M - (1 - \theta) \Delta t A) u + \Delta t (\theta f_1 + (1 -
  \theta) f_0).$$
-/
theorem mulVec_thetaStep (hK : IsUnit (M + (θ * Δt) • A)) (f₀ f₁ u : n → ℝ) :
    (M + (θ * Δt) • A) *ᵥ thetaStep M A θ Δt f₀ f₁ u
      = (M - ((1 - θ) * Δt) • A) *ᵥ u + Δt • (θ • f₁ + (1 - θ) • f₀) := by
  rw [thetaStep, mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hK), one_mulVec]

/-- The θ-step is the unique solution of its linear system. If $M + \theta \Delta t A$ is
invertible, then $u'$ is the θ-step of $u$ with the sources $f_0, f_1$ if and only if
$$(M + \theta \Delta t A) u' = (M - (1 - \theta) \Delta t A) u + \Delta t (\theta f_1 + (1 -
  \theta) f_0).$$
-/
theorem eq_thetaStep_iff (hK : IsUnit (M + (θ * Δt) • A)) (f₀ f₁ u u' : n → ℝ) :
    u' = thetaStep M A θ Δt f₀ f₁ u ↔
      (M + (θ * Δt) • A) *ᵥ u' = (M - ((1 - θ) * Δt) • A) *ᵥ u + Δt • (θ • f₁ + (1 - θ) • f₀) := by
  constructor
  · rintro rfl
    exact mulVec_thetaStep hK f₀ f₁ u
  · intro h
    rw [thetaStep, ← h, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hK),
      one_mulVec]

omit [DecidableEq n] in
/-- The divided form of the θ-method ([quarteroni2000numerical], (13.16) as printed) is equivalent
to the linear system. For $\Delta t \neq 0$ and $u, u', f_0, f_1 \in \mathbb{R}^n$,
$$M \frac{u' - u}{\Delta t} + A (\theta u' + (1 - \theta) u) = \theta f_1 + (1 - \theta) f_0$$
holds if and only if $(M + \theta \Delta t A) u' = (M - (1 - \theta) \Delta t A) u + \Delta t
(\theta f_1 + (1 - \theta) f_0)$. -/
theorem divided_iff (hΔt : Δt ≠ 0) (f₀ f₁ u u' : n → ℝ) :
    M *ᵥ (Δt⁻¹ • (u' - u)) + A *ᵥ (θ • u' + (1 - θ) • u) = θ • f₁ + (1 - θ) • f₀ ↔
      (M + (θ * Δt) • A) *ᵥ u' = (M - ((1 - θ) * Δt) • A) *ᵥ u + Δt • (θ • f₁ + (1 - θ) • f₀) := by
  have key : (M + (θ * Δt) • A) *ᵥ u'
      - ((M - ((1 - θ) * Δt) • A) *ᵥ u + Δt • (θ • f₁ + (1 - θ) • f₀))
      = Δt • (M *ᵥ (Δt⁻¹ • (u' - u)) + A *ᵥ (θ • u' + (1 - θ) • u)
        - (θ • f₁ + (1 - θ) • f₀)) := by
    simp only [add_mulVec, sub_mulVec, smul_mulVec, mulVec_add, mulVec_sub, mulVec_smul, smul_add,
      smul_sub, smul_smul, mul_inv_cancel₀ hΔt, one_smul]
    module
  rw [← sub_eq_zero (a := (M + (θ * Δt) • A) *ᵥ u'), key, smul_eq_zero, or_iff_right hΔt,
    sub_eq_zero]

/-- The θ-step is characterized by the divided form. If $M + \theta \Delta t A$ is invertible and
$\Delta t \neq 0$, then $u'$ is the θ-step of $u$ with the sources $f_0, f_1$ if and only if
$$M \frac{u' - u}{\Delta t} + A (\theta u' + (1 - \theta) u) = \theta f_1 + (1 - \theta) f_0.$$
-/
theorem eq_thetaStep_iff_divided (hK : IsUnit (M + (θ * Δt) • A)) (hΔt : Δt ≠ 0)
    (f₀ f₁ u u' : n → ℝ) :
    u' = thetaStep M A θ Δt f₀ f₁ u ↔
      M *ᵥ (Δt⁻¹ • (u' - u)) + A *ᵥ (θ • u' + (1 - θ) • u) = θ • f₁ + (1 - θ) • f₀ := by
  rw [eq_thetaStep_iff hK, divided_iff hΔt]

end ThetaStep

/-- **The coordinates of the form-level θ-step** ([quarteroni2000numerical], the equivalence of
(13.17) and (13.16)). Let $K$ be a real inner product space with a basis
$(\varphi_i)_{i \in \iota}$ indexed by a finite type, let $a$ be a bounded bilinear form on $K$
with $a(v, v) \ge 0$ for every $v$, let $\theta \ge 0$ and $\Delta t > 0$, and let
$\ell_0, \ell_1$ be continuous linear functionals on $K$. Then $u' \in K$ is the θ-step of
$u \in K$ for $a$ and the sources $\ell_0, \ell_1$ (`Variational.IsThetaStep`) if and only if
the coordinates of $u'$ are the matrix θ-step of the coordinates of $u$, for the mass matrix
$M_{ij} = \langle \varphi_j, \varphi_i \rangle$, the stiffness matrix
$A_{ij} = a(\varphi_j, \varphi_i)$ and the source vectors $(\ell_0(\varphi_i))_i$ and
$(\ell_1(\varphi_i))_i$. -/
theorem _root_.Variational.IsThetaStep.iff_thetaStep {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : Module.Basis ι ℝ K) (a : SesqForm ℝ K) {θ Δt : ℝ} (hθ : 0 ≤ θ) (hΔt : 0 < Δt)
    (hpos : a.IsCoerciveWith 0) (ℓ₀ ℓ₁ : K →L[ℝ] ℝ) (u u' : K) :
    Variational.IsThetaStep a θ Δt ℓ₀ ℓ₁ u u' ↔
      φ.equivFun u' = thetaStep (SesqForm.gramMatrix (innerSL ℝ) φ) (a.gramMatrix φ) θ Δt
        (fun i => ℓ₀ (φ i)) (fun i => ℓ₁ (φ i)) (φ.equivFun u) := by
  have hA : ∀ x, 0 ≤ x ⬝ᵥ (a.gramMatrix φ *ᵥ x) := fun x => by
    rw [SesqForm.dotProduct_gramMatrix_mulVec_real]
    simpa using hpos (∑ j, x j • φ j)
  have hK := isUnit_add_smul_of_posDef (massMatrix_posDef φ.linearIndependent) hA
    (mul_nonneg hθ hΔt.le)
  rw [eq_thetaStep_iff_divided hK hΔt.ne', ← map_sub, ← map_smul, ← map_smul, ← map_smul,
    ← map_add]
  have hF : ((θ • fun i => ℓ₁ (φ i)) + (1 - θ) • fun i => ℓ₀ (φ i) : ι → ℝ)
      = fun i => (θ • ℓ₁ + (1 - θ) • ℓ₀) (φ i) := by
    funext i
    simp
  rw [hF, ← forall_inner_add_eq_iff φ a]
  simp only [Variational.IsThetaStep, _root_.add_apply, _root_.smul_apply, smul_eq_mul]

/-! ### The $M$-inner product -/

section MassSpace

variable {M : Matrix n n ℝ} (hM : M.PosDef)

/-- **$\mathbb{R}^n$ with the $M$-inner product.** For a positive definite
$M \in \mathbb{R}^{n \times n}$, this is $\mathbb{R}^n$ with the inner product
$\langle x, y \rangle_M = (Mx) \cdot y$. In this space the θ-method for $M u' + A u = f$ is the
form-level θ-method of `Numlib.Variational.Evolution`.

It is the energy space `WithEnergy` of the Euclidean operator of $M$. -/
abbrev MassSpace : Type _ := WithEnergy (toEuclideanLin M) hM.isSymmetricCoercive_toEuclideanLin

/-- The identity map of $\mathbb{R}^n$ onto the $M$-space, as a linear equivalence. The form-level
theorems are read in coordinates along it. -/
def toMass : (n → ℝ) ≃ₗ[ℝ] MassSpace hM :=
  (WithLp.linearEquiv 2 ℝ (n → ℝ)).symm.trans (WithEnergy.equiv _ _)

instance : FiniteDimensional ℝ (MassSpace hM) := LinearEquiv.finiteDimensional (toMass hM)

instance : CompleteSpace (MassSpace hM) := FiniteDimensional.complete ℝ _

/-- The $M$-inner product is $\langle x, y \rangle_M = (Mx) \cdot y$. -/
theorem inner_toMass (x y : n → ℝ) : ⟪toMass hM x, toMass hM y⟫ = (M *ᵥ x) ⬝ᵥ y := by
  change energyInner (toEuclideanLin M) (WithLp.toLp 2 x) (WithLp.toLp 2 y) = _
  rw [energyInner, toEuclideanLin_toLp, EuclideanSpace.inner_toLp_toLp, star_trivial,
    dotProduct_comm]

/-- The squared $M$-norm is the quadratic form: $\|x\|_M^2 = x^T M x$. This is $\|u\|_M^2$ of
[quarteroni2000numerical]. -/
theorem norm_toMass_sq (x : n → ℝ) : ‖toMass hM x‖ ^ 2 = x ⬝ᵥ (M *ᵥ x) := by
  rw [← real_inner_self_eq_norm_sq, inner_toMass, dotProduct_comm]

/-- The bilinear form $(x, y) \mapsto (Ax) \cdot y$ on the $M$-space, for
$A \in \mathbb{R}^{n \times n}$.

It is the coordinate form $a(\sum_j \xi_j \varphi_j, \sum_i \eta_i \varphi_i) = \eta \cdot A
\xi$ of a bilinear form with stiffness matrix $A$
(`SesqForm.dotProduct_gramMatrix_mulVec_real`). It is also the form
$\langle M^{-1} A x, y \rangle_M$ of the operator $M^{-1} A$, which is $M$-symmetric when $A$ is
symmetric. -/
def massForm (A : Matrix n n ℝ) : SesqForm ℝ (MassSpace hM) :=
  SesqForm.ofBilin (LinearMap.mk₂ ℝ (fun p q => (A *ᵥ (toMass hM).symm p) ⬝ᵥ (toMass hM).symm q)
    (fun p p' q => by simp [mulVec_add, add_dotProduct])
    (fun c p q => by simp [mulVec_smul, smul_dotProduct])
    (fun p q q' => by simp [dotProduct_add])
    (fun c p q => by simp [dotProduct_smul]))

/-- The bilinear form `FiniteDifference.massForm` in coordinates: its value at $(x, y)$ is
$(Ax) \cdot y$. -/
@[simp]
theorem massForm_apply (A : Matrix n n ℝ) (x y : n → ℝ) :
    massForm hM A (toMass hM x) (toMass hM y) = (A *ᵥ x) ⬝ᵥ y := by
  simp [massForm]

/-- The linear functional $y \mapsto f \cdot y$ on the $M$-space, for $f \in \mathbb{R}^n$. It is
the coordinate form of a source functional $F$ with load vector $f_i = F(\varphi_i)$. -/
def massFunctional (f : n → ℝ) : MassSpace hM →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => f ⬝ᵥ (toMass hM).symm p
      map_add' := fun p q => by simp [dotProduct_add]
      map_smul' := fun c p => by simp [dotProduct_smul] }

/-- The functional `FiniteDifference.massFunctional` in coordinates: its value at $y$ is
$f \cdot y$. -/
@[simp]
theorem massFunctional_apply (f y : n → ℝ) : massFunctional hM f (toMass hM y) = f ⬝ᵥ y := by
  simp [massFunctional]

/-- The functional of the zero load vector is the zero functional. -/
@[simp]
theorem massFunctional_zero : massFunctional hM (0 : n → ℝ) = 0 := by
  ext p
  simp [massFunctional]

/-- If $x^T A x \ge 0$ for every $x \in \mathbb{R}^n$, then the bilinear form
$(x, y) \mapsto (Ax) \cdot y$ on the $M$-space is positive: its value at $(x, x)$ is
nonnegative. -/
theorem massForm_isCoerciveWith_zero {A : Matrix n n ℝ} (hA : ∀ x, 0 ≤ x ⬝ᵥ (A *ᵥ x)) :
    (massForm hM A).IsCoerciveWith 0 := by
  intro p
  obtain ⟨x, rfl⟩ := (toMass hM).surjective p
  rw [massForm_apply, RCLike.re_to_real, zero_mul, dotProduct_comm]
  exact hA x

/-- If $A$ is symmetric, then the bilinear form $(x, y) \mapsto (Ax) \cdot y$ on the $M$-space is
symmetric. -/
theorem massForm_isHermitian {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (massForm hM A).IsHermitian := by
  intro p q
  obtain ⟨x, rfl⟩ := (toMass hM).surjective p
  obtain ⟨y, rfl⟩ := (toMass hM).surjective q
  rw [massForm_apply, massForm_apply, RCLike.conj_to_real, dotProduct_comm, dotProduct_mulVec,
    ← mulVec_transpose, ← conjTranspose_eq_transpose_of_trivial, hA.eq]

/-- **The θ-step in the $M$-space.** Let $M \in \mathbb{R}^{n \times n}$ be positive definite, let
$A \in \mathbb{R}^{n \times n}$, let $\theta, \Delta t \in \mathbb{R}$, and let
$f_0, f_1, u, u' \in \mathbb{R}^n$. Then $u'$ is the form-level θ-step
(`Variational.IsThetaStep`) of $u$ for the form $(x, y) \mapsto (Ax) \cdot y$ and the
functionals $y \mapsto f_0 \cdot y$, $y \mapsto f_1 \cdot y$ on the $M$-space if and only if
$$M \Delta t^{-1} (u' - u) + A (\theta u' + (1 - \theta) u) = \theta f_1 + (1 - \theta) f_0,$$
the divided form of the matrix θ-step. Here $\Delta t^{-1} = 0$ when $\Delta t = 0$. -/
theorem isThetaStep_toMass_iff (A : Matrix n n ℝ) {θ Δt : ℝ} (f₀ f₁ u u' : n → ℝ) :
    Variational.IsThetaStep (massForm hM A) θ Δt (massFunctional hM f₀) (massFunctional hM f₁)
        (toMass hM u) (toMass hM u') ↔
      M *ᵥ (Δt⁻¹ • (u' - u)) + A *ᵥ (θ • u' + (1 - θ) • u) = θ • f₁ + (1 - θ) • f₀ := by
  rw [Variational.IsThetaStep, (toMass hM).surjective.forall,
    ← sub_eq_zero (a := M *ᵥ (Δt⁻¹ • (u' - u)) + A *ᵥ (θ • u' + (1 - θ) • u)),
    ← dotProduct_eq_zero_iff]
  refine forall_congr' fun y => ?_
  rw [← map_sub, ← map_smul, ← map_smul, ← map_smul, ← map_add, inner_toMass, massForm_apply,
    massFunctional_apply, massFunctional_apply, sub_dotProduct, add_dotProduct, add_dotProduct,
    smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul, sub_eq_zero]

end MassSpace

/-! ### Stability in the $M$-norm -/

section Stability

variable {M A : Matrix n n ℝ} {θ Δt : ℝ}

/-- The matrix θ-step with zero sources is the form-level θ-step in the $M$-space, with the
functionals of the zero load vector. The hypotheses are that $M$ is positive definite,
$M + \theta \Delta t A$ is invertible, and $\Delta t \neq 0$. -/
theorem isThetaStep_toMass_thetaStep' (hM : M.PosDef) (hK : IsUnit (M + (θ * Δt) • A))
    (hΔt : Δt ≠ 0) (u : n → ℝ) :
    Variational.IsThetaStep (massForm hM A) θ Δt (massFunctional hM 0) (massFunctional hM 0)
      (toMass hM u) (toMass hM (thetaStep M A θ Δt 0 0 u)) := by
  rw [isThetaStep_toMass_iff]
  exact (eq_thetaStep_iff_divided hK hΔt 0 0 u _).1 rfl

/-- The matrix θ-step with zero sources is the form-level θ-step in the $M$-space with zero sources.
The hypotheses are that $M$ is positive definite, $M + \theta \Delta t A$ is invertible, and
$\Delta t \neq 0$. -/
theorem isThetaStep_toMass_thetaStep (hM : M.PosDef) (hK : IsUnit (M + (θ * Δt) • A))
    (hΔt : Δt ≠ 0) (u : n → ℝ) :
    Variational.IsThetaStep (massForm hM A) θ Δt 0 0 (toMass hM u)
      (toMass hM (thetaStep M A θ Δt 0 0 u)) := by
  have h := isThetaStep_toMass_thetaStep' hM hK hΔt u
  rwa [massFunctional_zero] at h

/-- **Unconditional stability of the θ-method in the $M$-norm for $\theta \ge 1/2$**
([quarteroni2000numerical], §13.3.1, first conclusion). Let $M \in \mathbb{R}^{n \times n}$ be
positive definite, let $A \in \mathbb{R}^{n \times n}$ satisfy $x^T A x \ge 0$ for every $x$,
let $\theta \ge 1/2$ and $\Delta t > 0$. Then the θ-step $u'$ of $u$ with zero sources satisfies
$\|u'\|_M \le \|u\|_M$, that is,
$$u'^T M u' \le u^T M u.$$

This is `Variational.IsThetaStep.norm_le_of_half_le` read in the $M$-space. No symmetry of $A$
is needed. -/
theorem thetaStep_dotProduct_mulVec_le (hM : M.PosDef) (hA : ∀ x, 0 ≤ x ⬝ᵥ (A *ᵥ x))
    (hθ : 1 / 2 ≤ θ) (hΔt : 0 < Δt) (u : n → ℝ) :
    thetaStep M A θ Δt 0 0 u ⬝ᵥ (M *ᵥ thetaStep M A θ Δt 0 0 u) ≤ u ⬝ᵥ (M *ᵥ u) := by
  have hK : IsUnit (M + (θ * Δt) • A) :=
    isUnit_add_smul_of_posDef hM hA (mul_nonneg (by linarith) hΔt.le)
  have h := (isThetaStep_toMass_thetaStep hM hK hΔt.ne' u).norm_le_of_half_le hθ hΔt
    (massForm_isCoerciveWith_zero hM hA)
  rw [← norm_toMass_sq, ← norm_toMass_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- **Conditional stability of the θ-method in the $M$-norm** ([quarteroni2000numerical], §13.3.1,
the condition $\Delta t \le 2 / ((1 - 2\theta) \lambda_h^{N_h})$). Let
$M \in \mathbb{R}^{n \times n}$ be positive definite, let $A \in \mathbb{R}^{n \times n}$ be
symmetric with $x^T A x \ge 0$ for every $x$, let $\theta \ge 0$ and $\Delta t > 0$. Let
$\lambda_{\max} \in \mathbb{R}$ satisfy $w^T A w \le \lambda_{\max} w^T M w$ for every $w$, and
assume $(1 - 2\theta) \lambda_{\max} \Delta t \le 2$. Then the θ-step $u'$ of $u$ with zero
sources satisfies
$$u'^T M u' \le u^T M u.$$

The bound on $w^T A w$ says that every generalized eigenvalue of the pencil $(A, M)$ is at most
$\lambda_{\max}$. This is `Variational.IsThetaStep.norm_le_of_le_of_lt_half` read in the
$M$-space. -/
theorem thetaStep_dotProduct_mulVec_le_of_le (hM : M.PosDef) (hA : A.IsHermitian)
    (hA0 : ∀ x, 0 ≤ x ⬝ᵥ (A *ᵥ x)) (hθ : 0 ≤ θ) (hΔt : 0 < Δt) {lmax : ℝ}
    (hl : ∀ w, w ⬝ᵥ (A *ᵥ w) ≤ lmax * (w ⬝ᵥ (M *ᵥ w))) (hcfl : (1 - 2 * θ) * lmax * Δt ≤ 2)
    (u : n → ℝ) :
    thetaStep M A θ Δt 0 0 u ⬝ᵥ (M *ᵥ thetaStep M A θ Δt 0 0 u) ≤ u ⬝ᵥ (M *ᵥ u) := by
  have hK : IsUnit (M + (θ * Δt) • A) := isUnit_add_smul_of_posDef hM hA0 (mul_nonneg hθ hΔt.le)
  have hle : ∀ v : MassSpace hM, massForm hM A v v ≤ lmax * ‖v‖ ^ 2 := by
    intro v
    obtain ⟨x, rfl⟩ := (toMass hM).surjective v
    rw [massForm_apply, norm_toMass_sq, dotProduct_comm]
    exact hl x
  have h := (isThetaStep_toMass_thetaStep hM hK hΔt.ne' u).norm_le_of_le_of_lt_half
    (massForm_isHermitian hM hA) (massForm_isCoerciveWith_zero hM hA0) hle hΔt hcfl
  rw [← norm_toMass_sq, ← norm_toMass_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

end Stability

/-! ### The spectrum of the amplification matrix -/

section Spectrum

variable {M A : Matrix n n ℝ} {θ Δt : ℝ}

/-- Simultaneous diagonalization of a symmetric-definite pencil, in real form. Let
$M \in \mathbb{R}^{n \times n}$ be positive definite and let $A \in \mathbb{R}^{n \times n}$ be
symmetric. Then there are an invertible $W \in \mathbb{R}^{n \times n}$ and $d \in \mathbb{R}^n$
with
$$W^T M W = 1, \qquad W^T A W = \operatorname{diag}(d),$$
and the set of generalized eigenvalues of the pencil $(A, M)$ is $\{d_i\}$.

This is `Matrix.exists_simultaneous_diagonalization` for real matrices. -/
theorem exists_conj_eq_diagonal (hM : M.PosDef) (hA : A.IsHermitian) :
    ∃ (W : Matrix n n ℝ) (d : n → ℝ), IsUnit W ∧ star W * M * W = 1 ∧
      star W * A * W = diagonal d ∧ pencilSpectrum A M = Set.range d := by
  obtain ⟨W, d, hW, hWM, hWA, hspec⟩ := exists_simultaneous_diagonalization hA hM
  refine ⟨W, d, hW, hWM, ?_, ?_⟩
  · simpa [RCLike.ofReal_real_eq_id] using hWA
  · simpa [RCLike.ofReal_real_eq_id] using hspec

/-- **The pencil eigenvectors diagonalize the amplification matrix** ([quarteroni2000numerical],
§13.3.1, the θ-method in the eigenbasis, in matrix form). Let $W \in \mathbb{R}^{n \times n}$ be
invertible with $W^T M W = 1$ and $W^T A W = \operatorname{diag}(d)$, and assume
$1 + \theta d_i \Delta t \neq 0$ for every $i$. Then
$$(M + \theta \Delta t A)^{-1} (M - (1 - \theta) \Delta t A) = W
  \operatorname{diag}(r_\theta(d_i \Delta t)) W^{-1}.$$
-/
theorem thetaAmplification_eq_conj {W : Matrix n n ℝ} {d : n → ℝ} (hW : IsUnit W)
    (hWM : star W * M * W = 1) (hWA : star W * A * W = diagonal d)
    (hden : ∀ i, 1 + θ * d i * Δt ≠ 0) :
    thetaAmplification M A θ Δt = W * diagonal (fun i => thetaFactor θ Δt (d i)) * W⁻¹ := by
  have hWd := (isUnit_iff_isUnit_det W).1 hW
  have hWs : IsUnit (star W).det := (isUnit_iff_isUnit_det _).1 hW.star
  have hconj : ∀ c : ℝ, star W * (M + c • A) * W = diagonal (fun i => 1 + c * d i) := by
    intro c
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hWM, hWA,
      ← diagonal_one, ← diagonal_smul, ← diagonal_add]
    rfl
  have hK := hconj (θ * Δt)
  have hN : star W * (M - ((1 - θ) * Δt) • A) * W
      = diagonal (fun i => 1 + -((1 - θ) * Δt) * d i) := by
    rw [sub_eq_add_neg, ← neg_smul]
    exact hconj _
  have hexp : ∀ (X : Matrix n n ℝ) (D : Matrix n n ℝ), star W * X * W = D →
      X = (star W)⁻¹ * D * W⁻¹ := by
    intro X D hX
    rw [← hX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hWs, Matrix.one_mul,
      Matrix.mul_assoc, mul_nonsing_inv _ hWd, Matrix.mul_one]
  have hK' := hexp _ _ hK
  have hN' := hexp _ _ hN
  have hKunit : IsUnit (M + (θ * Δt) • A) := by
    rw [hK']
    refine ((Matrix.isUnit_nonsing_inv_iff.2 hW.star).mul ?_).mul
      (Matrix.isUnit_nonsing_inv_iff.2 hW)
    rw [isUnit_diagonal, Pi.isUnit_iff]
    intro i
    rw [isUnit_iff_ne_zero]
    have := hden i
    intro h0
    apply this
    linear_combination h0
  have hprod : (M + (θ * Δt) • A) * (W * diagonal (fun i => thetaFactor θ Δt (d i)) * W⁻¹)
      = M - ((1 - θ) * Δt) • A := by
    rw [hK', hN']
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hWd, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
    congr 3
    funext i
    have hne : 1 + θ * Δt * d i ≠ 0 := by
      rw [show θ * Δt * d i = θ * d i * Δt by ring]
      exact hden i
    rw [thetaFactor, show 1 + θ * d i * Δt = 1 + θ * Δt * d i by ring, mul_div_cancel₀ _ hne]
    ring
  rw [thetaAmplification, ← hprod, ← Matrix.mul_assoc,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hKunit), Matrix.one_mul]

/-- Under the hypotheses of `FiniteDifference.thetaAmplification_eq_conj`, the characteristic
polynomial of the amplification matrix is $\prod_i (X - r_\theta(d_i \Delta t))$. -/
theorem charpoly_thetaAmplification {W : Matrix n n ℝ} {d : n → ℝ} (hW : IsUnit W)
    (hWM : star W * M * W = 1) (hWA : star W * A * W = diagonal d)
    (hden : ∀ i, 1 + θ * d i * Δt ≠ 0) :
    (thetaAmplification M A θ Δt).charpoly
      = ∏ i, (Polynomial.X - Polynomial.C (thetaFactor θ Δt (d i))) := by
  rw [thetaAmplification_eq_conj hW hWM hWA hden]
  have := Matrix.charpoly_units_conj hW.unit (diagonal (fun i => thetaFactor θ Δt (d i)))
  rw [IsUnit.unit_spec] at this
  rw [this, charpoly_diagonal]

/-- Under the hypotheses of `FiniteDifference.thetaAmplification_eq_conj`, a real number $\mu$ is in
the real spectrum of the amplification matrix if and only if $\mu = r_\theta(d_i \Delta t)$ for
some $i$. -/
theorem mem_spectrum_thetaAmplification_iff {W : Matrix n n ℝ} {d : n → ℝ} (hW : IsUnit W)
    (hWM : star W * M * W = 1) (hWA : star W * A * W = diagonal d)
    (hden : ∀ i, 1 + θ * d i * Δt ≠ 0) (μ : ℝ) :
    μ ∈ spectrum ℝ (thetaAmplification M A θ Δt) ↔ ∃ i, μ = thetaFactor θ Δt (d i) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, charpoly_thetaAmplification hW hWM hWA hden,
    Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

/-- Under the hypotheses of `FiniteDifference.thetaAmplification_eq_conj`, a complex number $\mu$ is
in the complex spectrum of the amplification matrix if and only if
$\mu = r_\theta(d_i \Delta t)$ for some $i$. In particular, no nonreal eigenvalue appears. -/
theorem mem_spectrum_complexify_thetaAmplification_iff {W : Matrix n n ℝ} {d : n → ℝ}
    (hW : IsUnit W) (hWM : star W * M * W = 1) (hWA : star W * A * W = diagonal d)
    (hden : ∀ i, 1 + θ * d i * Δt ≠ 0) (μ : ℂ) :
    μ ∈ spectrum ℂ (complexify (thetaAmplification M A θ Δt)) ↔
      ∃ i, μ = (thetaFactor θ Δt (d i) : ℂ) := by
  rw [Matrix.mem_spectrum_complexify_iff, charpoly_thetaAmplification hW hWM hWA hden,
    Polynomial.map_prod, Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

/-- Let $M, A \in \mathbb{R}^{n \times n}$ be positive definite, let $\theta \ge 0$ and
$\Delta t \ge 0$, and let $\lambda$ be a generalized eigenvalue of the pencil $(A, M)$. Then the
denominator of the amplification factor is positive: $1 + \theta \lambda \Delta t > 0$.

The reason is that the generalized eigenvalues are positive. -/
theorem one_add_mul_pos_of_posDef (hM : M.PosDef) (hA : A.PosDef) (hθ : 0 ≤ θ) (hΔt : 0 ≤ Δt)
    {lam : ℝ} (hlam : lam ∈ pencilSpectrum A M) : 0 < 1 + θ * lam * Δt := by
  have hpos : 0 < lam := by simpa using re_pos_of_mem_pencilSpectrum_of_posDef hA hM hlam
  have := mul_nonneg (mul_nonneg hθ hpos.le) hΔt
  linarith

/-- **The eigenvalues of the θ-step** ([quarteroni2000numerical], §13.3.1). Let
$M, A \in \mathbb{R}^{n \times n}$ be positive definite, let $\theta \ge 0$ and
$\Delta t \ge 0$. Then $\mu \in \mathbb{R}$ is an eigenvalue of the amplification matrix if and
only if
$$\mu = r_\theta(\lambda \Delta t) = \frac{1 - (1 - \theta) \lambda \Delta t}{1 + \theta \lambda
  \Delta t}$$
for a generalized eigenvalue $\lambda$ of the pencil $(A, M)$, that is, a root of
$\det(A - \lambda M)$. -/
theorem thetaAmplification_hasEigenvalue_iff (hM : M.PosDef) (hA : A.PosDef) (hθ : 0 ≤ θ)
    (hΔt : 0 ≤ Δt) (μ : ℝ) :
    Module.End.HasEigenvalue (toLin' (thetaAmplification M A θ Δt)) μ ↔
      ∃ lam ∈ pencilSpectrum A M, μ = thetaFactor θ Δt lam := by
  obtain ⟨W, d, hW, hWM, hWA, hspec⟩ := exists_conj_eq_diagonal hM hA.1
  have hden : ∀ i, 1 + θ * d i * Δt ≠ 0 := fun i =>
    (one_add_mul_pos_of_posDef hM hA hθ hΔt (hspec ▸ Set.mem_range_self i)).ne'
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin',
    mem_spectrum_thetaAmplification_iff hW hWM hWA hden, hspec]
  simp

/-- Let $M, A \in \mathbb{R}^{n \times n}$ be positive definite, let $\theta \ge 0$ and
$\Delta t \ge 0$. Then the spectral radius of the amplification matrix, computed over
$\mathbb{C}$, is less than $1$ if and only if
$$|1 - (1 - \theta) \lambda \Delta t| < 1 + \theta \lambda \Delta t$$
for every generalized eigenvalue $\lambda$ of the pencil $(A, M)$, that is, every amplification
factor has modulus less than $1$. -/
theorem complexSpectralRadius_thetaAmplification_lt_one_iff (hM : M.PosDef) (hA : A.PosDef)
    (hθ : 0 ≤ θ) (hΔt : 0 ≤ Δt) :
    complexSpectralRadius (thetaAmplification M A θ Δt) < 1 ↔
      ∀ lam ∈ pencilSpectrum A M, |1 - (1 - θ) * lam * Δt| < 1 + θ * lam * Δt := by
  obtain ⟨W, d, hW, hWM, hWA, hspec⟩ := exists_conj_eq_diagonal hM hA.1
  have hden' : ∀ i, 0 < 1 + θ * d i * Δt := fun i =>
    one_add_mul_pos_of_posDef hM hA hθ hΔt (hspec ▸ Set.mem_range_self i)
  have hspecC : spectrum ℂ (complexify (thetaAmplification M A θ Δt))
      = Set.range (fun i => (thetaFactor θ Δt (d i) : ℂ)) := by
    ext μ
    rw [mem_spectrum_complexify_thetaAmplification_iff hW hWM hWA fun i => (hden' i).ne']
    simp [eq_comm]
  rw [complexSpectralRadius_eq_iSup, hspecC, iSup_range, ← Finset.sup_univ_eq_iSup,
    Finset.sup_lt_iff (by simp), hspec]
  simp only [Finset.mem_univ, true_implies, Set.forall_mem_range]
  refine forall_congr' fun i => ?_
  rw [Complex.nnnorm_real, ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_coe, coe_nnnorm,
    NNReal.coe_one, Real.norm_eq_abs, thetaFactor, abs_div, abs_of_pos (hden' i),
    div_lt_one (hden' i)]

/-- **Asymptotic stability of the θ-method** ([quarteroni2000numerical], §13.2, "asymptotically
stable", and (13.11)). Let $M, A \in \mathbb{R}^{n \times n}$ be positive definite, let
$\theta \ge 0$ and $\Delta t \ge 0$, and let $G$ be the amplification matrix. Then
$G^k u_0 \to 0$ as $k \to \infty$ for every $u_0 \in \mathbb{R}^n$ if and only if
$$|1 - (1 - \theta) \lambda \Delta t| < 1 + \theta \lambda \Delta t$$
for every generalized eigenvalue $\lambda$ of the pencil $(A, M)$.

Since $\lambda > 0$, for $\Delta t > 0$ the condition holds for every $\lambda$ when
$\theta \ge 1/2$, and for $\theta < 1/2$ it is $(1 - 2\theta) \lambda \Delta t < 2$. For
$\Delta t = 0$ the condition fails when $n \ge 1$, because $G$ is then the identity. The proof
combines `Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one` with the spectrum of the
amplification matrix. -/
theorem forall_tendsto_thetaStep_iff (hM : M.PosDef) (hA : A.PosDef) (hθ : 0 ≤ θ)
    (hΔt : 0 ≤ Δt) :
    (∀ u₀, Tendsto (fun k => (thetaAmplification M A θ Δt ^ k) *ᵥ u₀) atTop (𝓝 0)) ↔
      ∀ lam ∈ pencilSpectrum A M, |1 - (1 - θ) * lam * Δt| < 1 + θ * lam * Δt := by
  rw [← Matrix.tendsto_pow_zero_iff_forall_mulVec, tendsto_pow_iff_complexSpectralRadius_lt_one,
    complexSpectralRadius_thetaAmplification_lt_one_iff hM hA hθ hΔt]

/-- **The backward Euler method is unconditionally asymptotically stable**
([quarteroni2000numerical], §13.2, after (13.11)). Let $M, A \in \mathbb{R}^{n \times n}$ be
positive definite and let $\Delta t > 0$. Then for every $u_0 \in \mathbb{R}^n$,
$$((M + \Delta t A)^{-1} M)^k u_0 \to 0 \quad (k \to \infty).$$

The amplification matrix is the one of the θ-method with $\theta = 1$, and its eigenvalues
$1 / (1 + \lambda \Delta t)$ lie in $(0, 1)$. -/
theorem backwardEuler_tendsto (hM : M.PosDef) (hA : A.PosDef) (hΔt : 0 < Δt) (u₀ : n → ℝ) :
    Tendsto (fun k => (thetaAmplification M A 1 Δt ^ k) *ᵥ u₀) atTop (𝓝 0) := by
  refine (forall_tendsto_thetaStep_iff hM hA zero_le_one hΔt.le).2 (fun lam hlam => ?_) u₀
  have hpos : 0 < lam := by simpa using re_pos_of_mem_pencilSpectrum_of_posDef hA hM hlam
  rw [sub_self, zero_mul, zero_mul, sub_zero, abs_one, one_mul]
  nlinarith

end Spectrum

/-! ### The forward Euler scheme for the heat equation -/

/-- Let $m \in \mathbb{N}$ and $c > 0$. A real number $\lambda$ is an eigenvalue of
$c \operatorname{tridiag}(-1, 2, -1)$ of order $m$ if and only if
$$\lambda = 4c \sin^2 \frac{(k+1)\pi}{2(m+1)}$$
for some $k \in \{0, \dots, m-1\}$. These are the eigenvalues $\mu_i$ of $A_{fd}$ in
[quarteroni2000numerical], §13.2.

The proof is `Matrix.symmTridiagonalToeplitz_hasEigenvalue_iff` with the half-angle formula. -/
theorem mem_spectrum_smul_symmTridiagonalToeplitz_iff {m : ℕ} {c : ℝ} (hc : 0 < c) (lam : ℝ) :
    lam ∈ spectrum ℝ (c • symmTridiagonalToeplitz m (-1) 2) ↔
      ∃ k : Fin m, lam
        = c * (4 * Real.sin ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m : ℝ) + 1))) ^ 2) := by
  have h1 : lam ∈ spectrum ℝ (c • symmTridiagonalToeplitz m (-1) 2) ↔
      c⁻¹ * lam ∈ spectrum ℝ (symmTridiagonalToeplitz m (-1) 2) := by
    have := spectrum.smul_mem_smul_iff (a := symmTridiagonalToeplitz m (-1) 2) (s := c⁻¹ * lam)
      (r := Units.mk0 c hc.ne')
    rw [Units.smul_def, Units.smul_def, Units.val_mk0, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hc.ne', one_mul] at this
    exact this
  rw [h1, ← hasEigenvalue_toEuclideanLin_iff, symmTridiagonalToeplitz_hasEigenvalue_iff]
  refine exists_congr fun k => ?_
  have hang : (((k : ℕ) : ℝ) + 1) * Real.pi / ((m : ℝ) + 1)
      = 2 * ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m : ℝ) + 1))) := by
    field_simp
  rw [hang, mul_neg_one, neg_mul, ← sub_eq_add_neg, Real.two_sub_two_mul_cos_two_mul,
    inv_mul_eq_iff_eq_mul₀ hc.ne']

/-- **The forward Euler method for the finite difference heat equation** ([quarteroni2000numerical],
(13.11) and the display after it). Let $m \in \mathbb{N}$, let $\nu, h, \Delta t > 0$, and let
$A = (\nu / h^2) \operatorname{tridiag}(-1, 2, -1)$ of order $m$. Then
$(1 - \Delta t A)^k u_0 \to 0$ as $k \to \infty$ for every $u_0 \in \mathbb{R}^m$ if and only if
$$\Delta t \cdot \frac{4\nu}{h^2} \sin^2 \frac{m\pi}{2(m+1)} < 2.$$
This is the exact threshold $\Delta t \lambda_{\max}(A) < 2$.

Since $\sin^2 < 1$, the condition $\Delta t \le h^2 / (2\nu)$ of the source is sufficient. The
source states it as an equivalence, but the true threshold
$h^2 / (2\nu \sin^2(m\pi / (2(m+1))))$ is slightly larger. This theorem is the case $M = 1$ of
`FiniteDifference.forall_tendsto_thetaStep_iff`, where the pencil spectrum is the spectrum of
$A$. -/
theorem forwardEuler_heat_tendsto_iff (m : ℕ) {ν h Δt : ℝ} (hν : 0 < ν) (hh : 0 < h)
    (hΔt : 0 < Δt) :
    (∀ u₀ : Fin m → ℝ, Tendsto (fun k : ℕ =>
        ((1 - Δt • ((ν / h ^ 2) • symmTridiagonalToeplitz m (-1) 2)) ^ k) *ᵥ u₀) atTop (𝓝 0)) ↔
      Δt * (4 * ν / h ^ 2 * Real.sin ((m : ℝ) * Real.pi / (2 * ((m : ℝ) + 1))) ^ 2) < 2 := by
  set c : ℝ := ν / h ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hA : (c • symmTridiagonalToeplitz m (-1) 2).PosDef :=
    (posDef_symmTridiagonalToeplitz_neg_one_two m).smul hc0
  have hamp : thetaAmplification 1 (c • symmTridiagonalToeplitz m (-1) 2) 0 Δt
      = 1 - Δt • (c • symmTridiagonalToeplitz m (-1) 2) := by
    simp [thetaAmplification]
  have hspecset : spectrum ℝ (c • symmTridiagonalToeplitz m (-1) 2) = Set.range fun k : Fin m =>
      c * (4 * Real.sin ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m : ℝ) + 1))) ^ 2) := by
    ext lam
    rw [mem_spectrum_smul_symmTridiagonalToeplitz_iff hc0]
    simp [eq_comm]
  rw [← hamp, forall_tendsto_thetaStep_iff Matrix.PosDef.one hA le_rfl hΔt.le, pencilSpectrum_one,
    hspecset, Set.forall_mem_range]
  simp only [sub_zero, one_mul, zero_mul, add_zero]
  have hS : ∀ k : Fin m, 0 < Real.sin ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m : ℝ) + 1))) := by
    intro k
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    rw [div_lt_iff₀ (by positivity)]
    have hk : ((k : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast k.isLt
    nlinarith [Real.pi_pos]
  have hmono : ∀ k : Fin m, Real.sin ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m : ℝ) + 1)))
      ≤ Real.sin ((m : ℝ) * Real.pi / (2 * ((m : ℝ) + 1))) := by
    intro k
    have hk : ((k : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast k.isLt
    have h0 : (0 : ℝ) ≤ (((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m : ℝ) + 1)) := by positivity
    refine Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) ?_ ?_
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hk Real.pi_pos.le)
        (by positivity)
  have hfac : 4 * ν / h ^ 2 = 4 * c := by rw [hc]; ring
  rw [hfac]
  constructor
  · intro hall
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp
    · have := hall ⟨m - 1, Nat.sub_lt hm one_pos⟩
      have hcast : (((m - 1 : ℕ) : ℝ) + 1) = (m : ℝ) := by
        rw [Nat.cast_sub hm, Nat.cast_one]
        ring
      rw [hcast, abs_lt] at this
      linarith [this.1]
  · intro hlt k
    have hsq : Real.sin ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m : ℝ) + 1))) ^ 2
        ≤ Real.sin ((m : ℝ) * Real.pi / (2 * ((m : ℝ) + 1))) ^ 2 :=
      pow_le_pow_left₀ (hS k).le (hmono k) 2
    have hpos := hS k
    have hx : 0 < c * (4 * Real.sin ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m : ℝ) + 1))) ^ 2)
        * Δt := by positivity
    have hle : c * (4 * Real.sin ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m : ℝ) + 1))) ^ 2) * Δt
        ≤ Δt * (4 * c * Real.sin ((m : ℝ) * Real.pi / (2 * ((m : ℝ) + 1))) ^ 2) := by
      have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ c * 4 * Δt)
      linarith
    rw [abs_lt]
    constructor <;> linarith

/-- **The condition $\Delta t \le h^2 / (2\nu)$ is sufficient** ([quarteroni2000numerical], (13.11)
and the display after it). Let $m \in \mathbb{N}$, let $\nu, h, \Delta t > 0$ with
$\Delta t \le h^2 / (2\nu)$, and let $A = (\nu / h^2) \operatorname{tridiag}(-1, 2, -1)$ of
order $m$. Then for every $u_0 \in \mathbb{R}^m$, the forward Euler iterates satisfy
$$(1 - \Delta t A)^k u_0 \to 0 \quad (k \to \infty).$$

The threshold of `FiniteDifference.forwardEuler_heat_tendsto_iff` carries the extra factor
$\sin^2(m\pi / (2(m+1))) < 1$. So the condition is sufficient but not necessary, although the
source states it as an equivalence. -/
theorem forwardEuler_heat_tendsto_of_le (m : ℕ) {ν h Δt : ℝ} (hν : 0 < ν) (hh : 0 < h)
    (hΔt : 0 < Δt) (hle : Δt ≤ h ^ 2 / (2 * ν)) (u₀ : Fin m → ℝ) :
    Tendsto (fun k : ℕ =>
        ((1 - Δt • ((ν / h ^ 2) • symmTridiagonalToeplitz m (-1) 2)) ^ k) *ᵥ u₀) atTop (𝓝 0) := by
  refine (forwardEuler_heat_tendsto_iff m hν hh hΔt).2 ?_ u₀
  set x : ℝ := (m : ℝ) * Real.pi / (2 * ((m : ℝ) + 1)) with hx
  have hx0 : 0 ≤ x := by positivity
  have hxlt : x < Real.pi / 2 := by
    rw [hx, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) m]
  have hcos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxlt⟩
  have hsq : Real.sin x ^ 2 < 1 := by nlinarith [Real.sin_sq_add_cos_sq x]
  have h1 : Δt * (4 * ν / h ^ 2 * Real.sin x ^ 2)
      ≤ h ^ 2 / (2 * ν) * (4 * ν / h ^ 2 * Real.sin x ^ 2) :=
    mul_le_mul_of_nonneg_right hle (by positivity)
  have h2 : h ^ 2 / (2 * ν) * (4 * ν / h ^ 2 * Real.sin x ^ 2) = 2 * Real.sin x ^ 2 := by
    field_simp
    ring
  linarith

end FiniteDifference

end
