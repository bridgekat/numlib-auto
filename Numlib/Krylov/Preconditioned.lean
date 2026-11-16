/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Krylov.CG
import Numlib.Krylov.Convergence.CG
import Numlib.Krylov.QuasiMinRes
import Numlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Preconditioned Krylov methods

Preconditioning is a change of inner product, not a new algorithm. Let $M$ be a symmetric coercive
operator on an inner product space $E$ with a linear inverse $M^{-1}$. Then $E$ carries the
$M$-inner product $\langle x, y \rangle_M = \langle M x, y \rangle$, and in this inner product the
preconditioned operator $M^{-1} A$ satisfies $\langle M^{-1} A x, y \rangle_M = \langle A x, y
\rangle$. So $M^{-1} A$ is symmetric whenever $A$ is, and its quadratic form is the quadratic form
of $A$. Everything that the theory without preconditioning proves therefore transports. In
particular, the preconditioned conjugate gradient method (PCG, Algorithm 9.1 of [saad2003iterative])
is the conjugate gradient method for $M^{-1} A$ in the $M$-inner product, and its error obeys the
Chebyshev bound with the condition number of the generalized eigenvalue problem $A x = \lambda M x$.

The module also proves that left and right preconditioning search the same affine space
$x_0 + \mathcal{K}_m(M^{-1} A, M^{-1} r_0)$ and differ only in the norm that they minimize over it
([saad2003iterative], Proposition 9.1). For flexible GMRES, whose search space is not a Krylov
space, it proves the optimality and the exactness criterion of Propositions 9.2 and 9.3 of
[saad2003iterative].

## Main definitions

* `Krylov.IsPreconditioner`: a symmetric coercive $M$ together with a linear inverse $M^{-1}$.
* `Krylov.IsPreconditioner.EnergySpace`, `Krylov.IsPreconditioner.toEnergy`,
  `Krylov.IsPreconditioner.energySubmodule` and `Krylov.IsPreconditioner.energyEnd`: the $M$-inner
  product space, and the transport of vectors, subspaces and operators into it.
* `Krylov.PCG.State`, `Krylov.PCG.alpha`, `Krylov.PCG.beta`, `Krylov.PCG.step`, `Krylov.PCG.init`
  and `Krylov.PCG.iterate`: the preconditioned conjugate gradient iteration ([saad2003iterative],
  Algorithm 9.1).

## Main results

* `Krylov.IsPreconditioner.isGalerkin_energyEnd_iff`: the Galerkin condition for
  $M^{-1} A x = M^{-1} b$ in the $M$-inner product is the Galerkin condition for $A x = b$ in the
  original inner product.
* `Krylov.IsPreconditioner.isMinResidual_energyEnd_iff`: the minimal-residual condition for
  $M^{-1} A x = M^{-1} b$ in the $M$-inner product is the minimality of $\|b - A x\|_{M^{-1}}$.
* `Krylov.PCG.iterate_eq_CG_iterate_withEnergy`: the PCG iteration is `CG.iterate` for $M^{-1} A$ in
  the $M$-inner product.
* `Krylov.PCG.isGalerkinIterate`: the PCG iterate is the Galerkin iterate of $A x = b$ over
  $x_0 + \mathcal{K}_k(M^{-1} A, M^{-1} r_0)$, so it minimizes the $A$-norm of the error there.
* `Krylov.PCG.energyNorm_error_le`: $\|x^* - x_k\|_A \le 2 \big( (\sqrt\kappa - 1)/(\sqrt\kappa + 1)
  \big)^k \|x^* - x_0\|_A$, with $\kappa$ the condition number of $A x = \lambda M x$.
* `Krylov.PCG.inner_inv_residual_eq_zero` and `Krylov.PCG.inner_apply_direction_eq_zero`: the PCG
  residuals are $M^{-1}$-orthogonal and the directions are $A$-conjugate ([golub2013matrix],
  (11.5.2); [saad2003iterative], §9.2.1).
* `Krylov.IsPreconditioner.energyNorm_steepestDescentStep_le`: the preconditioned steepest descent
  step contracts the $A$-norm of the error by $(\lambda_{\max} - \lambda_{\min})/(\lambda_{\max} +
  \lambda_{\min})$.
* `Krylov.exists_aeval_of_isMinResidualIterate_preconditioned` and
  `Krylov.isMinResidual_of_isMinResidualIterate_rightPreconditioned`: left and right preconditioning
  search the same affine space; the left one minimizes $\|M^{-1}(b - A x)\|$ and the right one
  $\|b - A x\|$ ([saad2003iterative], Proposition 9.1).
* `Krylov.FGMRES.isMinResidual`: the flexible GMRES iterate minimizes the residual norm over $x_0 +
  \operatorname{span}\{z_0, \dots, z_{m-1}\}$ ([saad2003iterative], Proposition 9.2).
* `Krylov.FGMRES.apply_eq_iff_coeff_eq_zero`: the flexible GMRES iterate is exact if and only if the
  last subdiagonal entry of the Hessenberg matrix vanishes ([saad2003iterative], Proposition 9.3).
  `Krylov.FGMRES.apply_eq_of_coeff_eq_zero` is the half of it that needs no orthonormal residual
  basis, so it also holds at the breakdown step.

## Notation

* $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$. The $M$-inner product is $\langle x, y \rangle_M =
  \langle M x, y \rangle$, and $\|u\|_{M^{-1}} = (\operatorname{Re} \langle u, M^{-1} u
  \rangle)^{1/2}$.
* $\|x\|_A = (\operatorname{Re} \langle A x, x \rangle)^{1/2}$ is the energy norm `energyNorm A x`.
* $\lambda_{\min}$ and $\lambda_{\max}$ are bounds $\lambda_{\min} \langle M x, x \rangle \le
  \langle A x, x \rangle \le \lambda_{\max} \langle M x, x \rangle$ for all $x$, that is, bounds on
  the generalized eigenvalues of $A x = \lambda M x$. Each inequality is stated for the real parts.

## Implementation notes

* The inverse $M^{-1}$ is carried as data and not deduced from the surjectivity of $M$. This is what
  a preconditioner is in practice, a routine that solves $M z = r$, and it keeps the module free of
  hypotheses of completeness and finite dimension.
* The $M$-inner product space is the type synonym `WithEnergy` of
  `Numlib.Analysis.InnerProductSpace.Energy`, in the style of Mathlib.
* The step lengths of PCG are quotients, and Lean divides by $0$ to give $0$.
-/

open Polynomial Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Krylov

/-- Let $E$ be an inner product space over $\mathbb{K}$. A pair of linear operators $M$, $M^{-1}$ on
$E$ is a **preconditioner** if $M$ is symmetric coercive and $M M^{-1} x = x$ for all $x \in E$.

The right inverse $M^{-1}$ is then a two-sided inverse (`Krylov.IsPreconditioner.inv_apply`),
and it is symmetric (`Krylov.IsPreconditioner.isSymmetric_inv`). -/
structure IsPreconditioner (M Minv : E →ₗ[𝕜] E) : Prop where
  /-- The operator $M$ is symmetric coercive, so $\langle M x, y \rangle$ is an inner product. -/
  isSymmetricCoercive : M.IsSymmetricCoercive
  /-- The operator $M^{-1}$ is a right inverse of $M$: $M M^{-1} x = x$ for all $x$. -/
  apply_inv : ∀ x, M (Minv x) = x

namespace IsPreconditioner

variable {M Minv : E →ₗ[𝕜] E} (hM : IsPreconditioner M Minv)
include hM

/-- For a preconditioner $(M, M^{-1})$, the right inverse is also a left inverse: $M^{-1} M x = x$
for all $x$. -/
theorem inv_apply (x : E) : Minv (M x) = x :=
  hM.isSymmetricCoercive.isCoercive.injective (by rw [hM.apply_inv])

/-- For a preconditioner $(M, M^{-1})$, the inverse $M^{-1}$ is symmetric. -/
theorem isSymmetric_inv : Minv.IsSymmetric := fun x y => by
  conv_lhs => rw [← hM.apply_inv y]
  rw [← hM.isSymmetricCoercive.isSymmetric, hM.apply_inv]

/-- For a preconditioner $(M, M^{-1})$, the **$M$-inner product space** is $E$ with the inner
product $\langle x, y \rangle_M = \langle M x, y \rangle$. In this space the preconditioned
operator $M^{-1} A$ is symmetric whenever $A$ is. -/
noncomputable abbrev EnergySpace : Type _ := WithEnergy M hM.isSymmetricCoercive

/-- The identity map from $E$ to the $M$-inner product space, as a linear equivalence. -/
noncomputable abbrev toEnergy : E ≃ₗ[𝕜] hM.EnergySpace :=
  WithEnergy.equiv M hM.isSymmetricCoercive

/-- A subspace $K$ of $E$, seen as a subspace of the $M$-inner product space. -/
noncomputable abbrev energySubmodule (K : Submodule 𝕜 E) : Submodule 𝕜 hM.EnergySpace :=
  WithEnergy.submoduleMap M hM.isSymmetricCoercive K

/-- A linear operator $B$ on $E$, seen as a linear operator on the $M$-inner product space. -/
noncomputable def energyEnd (B : E →ₗ[𝕜] E) : hM.EnergySpace →ₗ[𝕜] hM.EnergySpace :=
  (hM.toEnergy).toLinearMap ∘ₗ B ∘ₗ (hM.toEnergy).symm.toLinearMap

/-- The transported operator acts on a transported vector as the original operator does. -/
@[simp]
theorem energyEnd_apply (B : E →ₗ[𝕜] E) (x : E) :
    hM.energyEnd B (hM.toEnergy x) = hM.toEnergy (B x) := rfl

/-- The squared norm of $x$ in the $M$-inner product is the quadratic form of $M$: $\|x\|_M^2 =
\operatorname{Re} \langle M x, x \rangle$. -/
theorem norm_toEnergy_sq (x : E) : ‖hM.toEnergy x‖ ^ 2 = RCLike.re (inner 𝕜 (M x) x) :=
  norm_sq_eq_re_inner (𝕜 := 𝕜) (hM.toEnergy x)

/-- For all $w, u \in E$, the $M$-inner product of $w$ with a preconditioned vector is the original
inner product:
$$\langle w, M^{-1} u \rangle_M = \langle w, u \rangle.$$
This identity makes preconditioning a change of inner product and nothing more. -/
theorem inner_toEnergy_inv (w u : E) :
    inner 𝕜 (hM.toEnergy w) (hM.toEnergy (Minv u)) = inner 𝕜 w u := by
  rw [WithEnergy.inner_equiv, energyInner, ← hM.isSymmetric_inv, hM.inv_apply]

variable (A : E →ₗ[𝕜] E)

/-- For a linear operator $A$ on $E$ and all $x, y \in E$,
$$\langle M^{-1} A x, y \rangle_M = \langle A x, y \rangle.$$
In particular the quadratic form of $M^{-1} A$ in the $M$-inner product is the quadratic form of
$A$. -/
theorem inner_energyEnd_left (x y : E) :
    inner 𝕜 (hM.energyEnd (Minv ∘ₗ A) (hM.toEnergy x)) (hM.toEnergy y) = inner 𝕜 (A x) y := by
  rw [energyEnd_apply, WithEnergy.inner_equiv, energyInner, LinearMap.comp_apply, hM.apply_inv]

/-- For a linear operator $A$ on $E$ and all $x, y \in E$, $\langle x, M^{-1} A y \rangle_M =
\langle x, A y \rangle$. This is the other side of
`Krylov.IsPreconditioner.inner_energyEnd_left`. -/
theorem inner_energyEnd_right (x y : E) :
    inner 𝕜 (hM.toEnergy x) (hM.energyEnd (Minv ∘ₗ A) (hM.toEnergy y)) = inner 𝕜 x (A y) := by
  rw [energyEnd_apply, WithEnergy.inner_equiv, energyInner, LinearMap.comp_apply,
    ← hM.isSymmetric_inv, hM.inv_apply]

/-- For a linear operator $A$ on $E$ and every $x \in E$, the energy norm of $x$ for $M^{-1} A$ in
the $M$-inner product is the energy norm $\|x\|_A$ in the original inner product. So the
Chebyshev bounds proved for $M^{-1} A$ in the $M$-inner product are bounds on $\|x^* - x_k\|_A$. -/
theorem energyNorm_energyEnd (x : E) :
    energyNorm (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy x) = energyNorm A x := by
  rw [energyNorm, energyNorm, hM.inner_energyEnd_left A x x]

/-- Powers of a transported operator are the transports of the powers:
$\tilde B^i \tilde x = \widetilde{B^i x}$. -/
theorem pow_energyEnd (B : E →ₗ[𝕜] E) (i : ℕ) (x : E) :
    ((hM.energyEnd B) ^ i) (hM.toEnergy x) = hM.toEnergy ((B ^ i) x) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, energyEnd_apply,
      ← Module.End.mul_apply, ← pow_succ']

/-- For a linear operator $B$ on $E$, $v \in E$ and $m \in \mathbb{N}$, the Krylov space
$\mathcal{K}_m(B, v)$ computed in the $M$-inner product space is the transport of
$\mathcal{K}_m(B, v)$ computed in $E$. So preconditioning does not move the search space; it
changes only the geometry on it. -/
theorem subspace_energyEnd (B : E →ₗ[𝕜] E) (v : E) (m : ℕ) :
    subspace (hM.energyEnd B) (hM.toEnergy v) m = hM.energySubmodule (subspace B v m) := by
  have hsub : hM.energySubmodule (subspace B v m)
      = (subspace B v m).map (hM.toEnergy).toLinearMap := rfl
  rw [hsub, subspace, subspace, Submodule.map_span]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(B ^ (i : ℕ)) v, ⟨i, rfl⟩, (hM.pow_energyEnd B i v).symm⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, hM.pow_energyEnd B i v⟩

/-- **The Galerkin condition is invariant under preconditioning.** Let $A$ be a linear operator on
$E$, let $b, x_0, x \in E$, and let $K$ be a subspace of $E$. Then $x$ is a Galerkin iterate
over $x_0 + K$ for the preconditioned system $M^{-1} A x = M^{-1} b$ in the $M$-inner product if
and only if $x$ is a Galerkin iterate over $x_0 + K$ for $A x = b$ in the original inner
product.

So every optimality statement of `Numlib.Krylov.Iterate` applies to a preconditioned method with
no new proof. The statement needs no hypothesis on $A$. -/
theorem isGalerkin_energyEnd_iff (b x₀ : E) (K : Submodule 𝕜 E) (x : E) :
    IsGalerkin (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀)
        (hM.energySubmodule K) (hM.toEnergy x) ↔ IsGalerkin A b x₀ K x := by
  have hres : hM.toEnergy (Minv b) - hM.energyEnd (Minv ∘ₗ A) (hM.toEnergy x) =
      hM.toEnergy (Minv (b - A x)) := by
    rw [energyEnd_apply, LinearMap.comp_apply, ← map_sub, ← map_sub]
  constructor
  · rintro ⟨hmem, horth⟩
    rw [← map_sub, WithEnergy.equiv_mem_submoduleMap_iff M hM.isSymmetricCoercive] at hmem
    refine ⟨hmem, (Submodule.mem_orthogonal _ _).2 fun w hw => ?_⟩
    have h := (Submodule.mem_orthogonal _ _).1 horth (hM.toEnergy w)
      ((WithEnergy.equiv_mem_submoduleMap_iff M hM.isSymmetricCoercive).2 hw)
    rwa [hres, hM.inner_toEnergy_inv] at h
  · rintro ⟨hmem, horth⟩
    refine ⟨by
        rw [← map_sub]
        exact (WithEnergy.equiv_mem_submoduleMap_iff M hM.isSymmetricCoercive).2 hmem,
      (Submodule.mem_orthogonal _ _).2 fun w hw => ?_⟩
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
    rw [show (hM.toEnergy).toLinearMap v = hM.toEnergy v from rfl, hres, hM.inner_toEnergy_inv]
    exact (Submodule.mem_orthogonal _ _).1 horth v hv

/-- For every $u \in E$, the $M$-norm of the preconditioned vector $M^{-1} u$ is the $M^{-1}$-norm
of $u$:
$$\|M^{-1} u\|_M^2 = \operatorname{Re} \langle u, M^{-1} u \rangle.$$
So the residual norm that a left-preconditioned minimal-residual method minimizes is
$\|b - A x\|_{M^{-1}}$. -/
theorem norm_toEnergy_inv_sq (u : E) :
    ‖hM.toEnergy (Minv u)‖ ^ 2 = RCLike.re (inner 𝕜 u (Minv u)) := by
  rw [hM.norm_toEnergy_sq, hM.apply_inv]

/-- **The minimal-residual condition is invariant under preconditioning.** Let $A$ be a linear
operator on $E$, let $b, x_0, x \in E$, and let $K$ be a subspace of $E$. Then $x$ minimizes the
residual of the preconditioned system $M^{-1} A x = M^{-1} b$ over $x_0 + K$ in the $M$-inner
product if and only if $x - x_0 \in K$ and
$$\|M^{-1}(b - A x)\|_M \le \|M^{-1}(b - A y)\|_M \qquad \text{for all } y \in x_0 + K.$$
By `Krylov.IsPreconditioner.norm_toEnergy_inv_sq`, this is the minimization of the $M^{-1}$-norm
$\|b - A x\|_{M^{-1}}$ of the true residual, which is what left-preconditioned GMRES and MINRES
do ([saad2003iterative], §9.3.1).

The norm $\|M^{-1} u\|_M$ is `energyNorm M (Minv u)`. -/
theorem isMinResidual_energyEnd_iff (b x₀ : E) (K : Submodule 𝕜 E) (x : E) :
    IsMinResidual (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀)
        (hM.energySubmodule K) (hM.toEnergy x) ↔
      (x - x₀ ∈ K ∧ ∀ y, y - x₀ ∈ K →
        energyNorm M (Minv (b - A x)) ≤ energyNorm M (Minv (b - A y))) := by
  have hres : ∀ y : E, hM.toEnergy (Minv b) - hM.energyEnd (Minv ∘ₗ A) (hM.toEnergy y)
      = hM.toEnergy (Minv (b - A y)) := fun y => by
    rw [energyEnd_apply, LinearMap.comp_apply, ← map_sub, ← map_sub]
  have hnorm : ∀ y : E, ‖hM.toEnergy (Minv (b - A y))‖ = energyNorm M (Minv (b - A y)) :=
    fun y => WithEnergy.norm_equiv M hM.isSymmetricCoercive _
  constructor
  · rintro ⟨hmem, hmin⟩
    rw [← map_sub, WithEnergy.equiv_mem_submoduleMap_iff M hM.isSymmetricCoercive] at hmem
    refine ⟨hmem, fun y hy => ?_⟩
    have h := hmin (hM.toEnergy y) (by
      rw [← map_sub]
      exact (WithEnergy.equiv_mem_submoduleMap_iff M hM.isSymmetricCoercive).2 hy)
    rwa [hres, hres, hnorm, hnorm] at h
  · rintro ⟨hmem, hmin⟩
    refine ⟨by
        rw [← map_sub]
        exact (WithEnergy.equiv_mem_submoduleMap_iff M hM.isSymmetricCoercive).2 hmem,
      fun z hz => ?_⟩
    obtain ⟨y, rfl⟩ := (hM.toEnergy).surjective z
    rw [← map_sub, WithEnergy.equiv_mem_submoduleMap_iff M hM.isSymmetricCoercive] at hz
    rw [hres, hres, hnorm, hnorm]
    exact hmin y hz

/-- Let $A$ be symmetric, and let $\lambda_{\min}, \lambda_{\max} \in \mathbb{R}$ with
$$\lambda_{\min} \operatorname{Re} \langle M x, x \rangle \le \operatorname{Re} \langle A x, x
  \rangle \le \lambda_{\max} \operatorname{Re} \langle M x, x \rangle \qquad (x \in E).$$
Then $M^{-1} A$ is symmetric in the $M$-inner product, with $\lambda_{\min} \|x\|_M^2 \le
\operatorname{Re} \langle M^{-1} A x, x \rangle_M \le \lambda_{\max} \|x\|_M^2$ for all $x$.

So bounds on the generalized eigenvalues of $A x = \lambda M x$ are bounds on the quadratic form
of $M^{-1} A$ in the $M$-inner product, in the form `LinearMap.IsSymmetricBoundedBy` that the
Chebyshev convergence theory uses. The ratio $\lambda_{\max} / \lambda_{\min}$ is the condition
number of $M^{-1} A$, which preconditioning is meant to reduce. -/
theorem isSymmetricBoundedBy_energyEnd (hA : A.IsSymmetric) {lmin lmax : ℝ}
    (hmin : ∀ x : E, lmin * RCLike.re (inner 𝕜 (M x) x) ≤ RCLike.re (inner 𝕜 (A x) x))
    (hmax : ∀ x : E, RCLike.re (inner 𝕜 (A x) x) ≤ lmax * RCLike.re (inner 𝕜 (M x) x)) :
    (hM.energyEnd (Minv ∘ₗ A)).IsSymmetricBoundedBy lmin lmax where
  isSymmetric := by
    intro u v
    obtain ⟨x, rfl⟩ := (hM.toEnergy).surjective u
    obtain ⟨y, rfl⟩ := (hM.toEnergy).surjective v
    rw [hM.inner_energyEnd_left A, hM.inner_energyEnd_right A, hA]
  le_re_inner := by
    intro u
    obtain ⟨x, rfl⟩ := (hM.toEnergy).surjective u
    rw [hM.inner_energyEnd_left A, hM.norm_toEnergy_sq]
    exact hmin x
  re_inner_le := by
    intro u
    obtain ⟨x, rfl⟩ := (hM.toEnergy).surjective u
    rw [hM.inner_energyEnd_left A, hM.norm_toEnergy_sq]
    exact hmax x

/-- Let $A$ be symmetric, and let $c > 0$ with $c \operatorname{Re} \langle M x, x \rangle \le
\operatorname{Re} \langle A x, x \rangle$ for all $x \in E$. Then $M^{-1} A$ is symmetric
coercive in the $M$-inner product. This makes PCG well defined. -/
theorem isSymmetricCoercive_energyEnd (hA : A.IsSymmetric) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x : E, c * RCLike.re (inner 𝕜 (M x) x) ≤ RCLike.re (inner 𝕜 (A x) x)) :
    (hM.energyEnd (Minv ∘ₗ A)).IsSymmetricCoercive where
  isSymmetric := by
    intro u v
    obtain ⟨x, rfl⟩ := (hM.toEnergy).surjective u
    obtain ⟨y, rfl⟩ := (hM.toEnergy).surjective v
    rw [hM.inner_energyEnd_left A, hM.inner_energyEnd_right A, hA]
  isCoercive := ⟨c, hc, by
    intro u
    obtain ⟨x, rfl⟩ := (hM.toEnergy).surjective u
    rw [hM.inner_energyEnd_left A, hM.norm_toEnergy_sq]
    exact hcoer x⟩

/-- One step of the preconditioned gradient (steepest descent) method ([quarteroni2000numerical],
§4.3.3, Program 19 with $P \neq I$). For $b, x \in E$ let $r = b - A x$ and $z = M^{-1} r$. The
step
$$x \mapsto x + \frac{\langle z, r \rangle}{\langle z, A z \rangle} \, z,$$
which is `Projection.step1 A b z z x`, is the steepest descent step
`Projection.steepestDescentStep` of `Numlib.Projection.OneDimensional` for the operator
$M^{-1} A$ and the right-hand side $M^{-1} b$ in the $M$-inner product, read back in $E$. -/
theorem toEnergy_step1_inv_residual (b x : E) :
    hM.toEnergy (Projection.step1 A b (Minv (b - A x)) (Minv (b - A x)) x)
      = Projection.steepestDescentStep (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b))
          (hM.toEnergy x) := by
  have hres : hM.toEnergy (Minv b) - hM.energyEnd (Minv ∘ₗ A) (hM.toEnergy x)
      = hM.toEnergy (Minv (b - A x)) := by
    rw [energyEnd_apply, LinearMap.comp_apply, ← map_sub, ← map_sub]
  rw [Projection.steepestDescentStep, Projection.step1, Projection.step1, hres, map_add, map_smul,
    hM.inner_toEnergy_inv, hM.inner_energyEnd_right]

/-- Let $A$ be symmetric, let $0 < \lambda_{\min}$ and $\lambda_{\max}$ satisfy
$$\lambda_{\min} \operatorname{Re} \langle M x, x \rangle \le \operatorname{Re} \langle A x, x
  \rangle \le \lambda_{\max} \operatorname{Re} \langle M x, x \rangle \qquad (x \in E),$$
and let $A x^* = b$. For $x \in E$ let $r = b - A x$, $z = M^{-1} r$ and $x' = x + (\langle z, r
\rangle / \langle z, A z \rangle) z$. Then
$$\|x^* - x'\|_A \le \frac{\lambda_{\max} - \lambda_{\min}}{\lambda_{\max} + \lambda_{\min}} \,
  \|x^* - x\|_A.$$
So the preconditioned gradient method contracts the $A$-norm of the error. This is §4.3.3 of
[quarteroni2000numerical] with Corollary 4.1 read for $P^{-1} A$; the source prints the method
as Program 19 and states no numbered result for it.

The proof is `Projection.energyNorm_steepestDescentStep_le` for $M^{-1} A$ in the $M$-inner
product (`Krylov.IsPreconditioner.isSymmetricBoundedBy_energyEnd`), read back through
`Krylov.IsPreconditioner.energyNorm_energyEnd`, in the same way as
`Krylov.PCG.energyNorm_error_le` transports the conjugate gradient bound. -/
theorem energyNorm_steepestDescentStep_le (hA : A.IsSymmetric) {lmin lmax : ℝ} (hl : 0 < lmin)
    (hmin : ∀ x : E, lmin * RCLike.re (inner 𝕜 (M x) x) ≤ RCLike.re (inner 𝕜 (A x) x))
    (hmax : ∀ x : E, RCLike.re (inner 𝕜 (A x) x) ≤ lmax * RCLike.re (inner 𝕜 (M x) x))
    {b xstar : E} (hstar : A xstar = b) (x : E) :
    energyNorm A (xstar - Projection.step1 A b (Minv (b - A x)) (Minv (b - A x)) x) ≤
      (lmax - lmin) / (lmax + lmin) * energyNorm A (xstar - x) := by
  have hB := hM.isSymmetricBoundedBy_energyEnd A hA hmin hmax
  have hstar' : hM.energyEnd (Minv ∘ₗ A) (hM.toEnergy xstar) = hM.toEnergy (Minv b) := by
    rw [energyEnd_apply, LinearMap.comp_apply, hstar]
  have h := Projection.energyNorm_steepestDescentStep_le hl hB hstar' (hM.toEnergy x)
  rw [← hM.toEnergy_step1_inv_residual A b x, ← map_sub, ← map_sub, hM.energyNorm_energyEnd,
    hM.energyNorm_energyEnd] at h
  exact h

end IsPreconditioner

/-! ### Left and right preconditioning search the same space ([saad2003iterative], Proposition 9.1)
-/

variable {M Minv A : E →ₗ[𝕜] E}

/-- **Proposition 9.1** of [saad2003iterative], left preconditioning. Let $M^{-1}$ and $A$ be linear
operators on $E$, let $b, x_0 \in E$ and $r_0 = b - A x_0$. If $x$ is a minimal-residual iterate
at step $m$ for the system $M^{-1} A x = M^{-1} b$, that is, $x$ minimizes $\|M^{-1}(b - A x)\|$
over $x_0 + \mathcal{K}_m(M^{-1} A, M^{-1} r_0)$, then
$$x = x_0 + s(M^{-1} A) \, M^{-1} r_0$$
for a polynomial $s$ of degree less than $m$. -/
theorem exists_aeval_of_isMinResidualIterate_preconditioned
    {b x₀ : E} {m : ℕ} {x : E} (hx : IsMinResidualIterate (Minv ∘ₗ A) (Minv b) x₀ m x) :
    ∃ s : 𝕜[X], s.degree < m ∧ x = x₀ + aeval (Minv ∘ₗ A) s (Minv (b - A x₀)) := by
  have hr : Minv b - (Minv ∘ₗ A) x₀ = Minv (b - A x₀) := by
    rw [LinearMap.comp_apply, ← map_sub]
  have hmem := hx.mem
  rw [hr] at hmem
  obtain ⟨s, hs, hsx⟩ := (mem_subspace_iff_exists_aeval _ _).1 hmem
  exact ⟨s, hs, by rw [hsx]; abel⟩

/-- **Proposition 9.1** of [saad2003iterative], right preconditioning. Let $M^{-1}$ and $A$ be
linear operators on $E$, let $b, u_0 \in E$, and let $x_0 = M^{-1} u_0$ and $r_0 = b - A x_0$.
If $u$ is a minimal-residual iterate at step $m$ for the system $A M^{-1} u = b$ started at
$u_0$, then $x = M^{-1} u$ lies in the affine space $x_0 + \mathcal{K}_m(M^{-1} A, M^{-1} r_0)$
of the left-preconditioned method, and $x$ minimizes the true residual norm $\|b - A x\|$ over
this space.

So left and right preconditioning search the same space, and only the minimized norm differs. -/
theorem isMinResidual_of_isMinResidualIterate_rightPreconditioned {b x₀ : E} {m : ℕ} {u₀ u : E}
    (hx₀ : x₀ = Minv u₀) (hu : IsMinResidualIterate (A ∘ₗ Minv) b u₀ m u) :
    IsMinResidual A b x₀ (subspace (Minv ∘ₗ A) (Minv (b - A x₀)) m) (Minv u) := by
  have hr : b - (A ∘ₗ Minv) u₀ = b - A x₀ := by rw [LinearMap.comp_apply, hx₀]
  have hmap := map_subspace_comp A Minv (b - A x₀) m
  have hmem := hu.mem
  rw [hr] at hmem
  refine ⟨?_, fun y hy => ?_⟩
  · have hsub : Minv u - x₀ = Minv (u - u₀) := by rw [hx₀, map_sub]
    rw [hsub, ← hmap]
    exact Submodule.mem_map_of_mem hmem
  · rw [← hmap] at hy
    obtain ⟨w, hw, hwy⟩ := Submodule.mem_map.1 hy
    have hyu : y = Minv (u₀ + w) := by rw [map_add, ← hx₀, hwy]; abel
    have h := hu.min (u₀ + w) (by rw [hr, add_sub_cancel_left]; exact hw)
    rwa [hyu, ← LinearMap.comp_apply, ← LinearMap.comp_apply (f := A)]

/-! ### The preconditioned conjugate gradient iteration ([saad2003iterative], Algorithm 9.1) -/

namespace PCG

/-- The state of the preconditioned conjugate gradient iteration: the iterate $x$, the residual
$r = b - A x$ and the search direction $p$. The preconditioned residual $z = M^{-1} r$ is
computed again at each step and not stored. -/
structure State (E : Type*) where
  /-- The current iterate $x$. -/
  x : E
  /-- The residual $r = b - A x$. -/
  r : E
  /-- The search direction $p$. -/
  p : E

/-- The PCG step length $\alpha = \langle r, M^{-1} r \rangle / \langle A p, p \rangle$, with
$\alpha = 0$ if the denominator is $0$. -/
noncomputable def alpha (A Minv : E →ₗ[𝕜] E) (s : State E) : 𝕜 :=
  inner 𝕜 s.r (Minv s.r) / inner 𝕜 (A s.p) s.p

/-- One PCG step ([saad2003iterative], Algorithm 9.1). With $\alpha = \langle r, M^{-1} r \rangle /
\langle A p, p \rangle$, the new state is
$$x' = x + \alpha p, \qquad r' = r - \alpha A p, \qquad p' = M^{-1} r' + \beta p,$$
where $\beta = \langle r', M^{-1} r' \rangle / \langle r, M^{-1} r \rangle$. A quotient with
denominator $0$ is $0$. -/
noncomputable def step (A Minv : E →ₗ[𝕜] E) (s : State E) : State E :=
  let α := alpha A Minv s
  let r' := s.r - α • A s.p
  let β : 𝕜 := inner 𝕜 r' (Minv r') / inner 𝕜 s.r (Minv s.r)
  { x := s.x + α • s.p, r := r', p := Minv r' + β • s.p }

/-- The PCG direction update coefficient $\beta = \langle r', M^{-1} r' \rangle / \langle r, M^{-1}
r \rangle$, where $r'$ is the residual after the step, with $\beta = 0$ if the denominator is
$0$. -/
noncomputable def beta (A Minv : E →ₗ[𝕜] E) (s : State E) : 𝕜 :=
  inner 𝕜 (step A Minv s).r (Minv (step A Minv s).r) / inner 𝕜 s.r (Minv s.r)

/-- The starting state of PCG for $A x = b$ at $x_0$: the iterate $x_0$, the residual
$r_0 = b - A x_0$ and the direction $p_0 = M^{-1} r_0$. -/
def init (A Minv : E →ₗ[𝕜] E) (b x₀ : E) : State E :=
  { x := x₀, r := b - A x₀, p := Minv (b - A x₀) }

/-- The PCG state after $k$ steps for $A x = b$, started at $x_0$, with the preconditioner inverse
$M^{-1}$: the $k$-fold application of `Krylov.PCG.step` to `Krylov.PCG.init`. -/
noncomputable def iterate (A Minv : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : State E :=
  (step A Minv)^[k] (init A Minv b x₀)

variable (A Minv : E →ₗ[𝕜] E) (b x₀ : E)

/-- The state after $k + 1$ steps is one `Krylov.PCG.step` applied to the state after $k$ steps. -/
theorem iterate_succ (k : ℕ) :
    iterate A Minv b x₀ (k + 1) = step A Minv (iterate A Minv b x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The iterate update $x' = x + \alpha p$ of one PCG step. -/
theorem step_x (s : State E) : (step A Minv s).x = s.x + alpha A Minv s • s.p := rfl

/-- The residual update $r' = r - \alpha A p$ of one PCG step. -/
theorem step_r (s : State E) : (step A Minv s).r = s.r - alpha A Minv s • A s.p := rfl

/-- The direction update $p' = M^{-1} r' + \beta p$ of one PCG step. -/
theorem step_p (s : State E) :
    (step A Minv s).p = Minv (step A Minv s).r + beta A Minv s • s.p := rfl

/-- **PCG is CG on the preconditioned system.** Let $(M, M^{-1})$ be a preconditioner and $A$ a
linear operator on $E$, and let $b, x_0 \in E$. Let $x_k$, $r_k$, $p_k$ be the PCG iterate,
residual and direction after $k$ steps, and let $\tilde x_k$, $\tilde r_k$, $\tilde p_k$ be
those of the conjugate gradient iteration for $M^{-1} A$ with right-hand side $M^{-1} b$,
started at $x_0$ in the $M$-inner product. Then
$$x_k = \tilde x_k, \qquad M^{-1} r_k = \tilde r_k, \qquad p_k = \tilde p_k, \qquad r_k = b - A
  x_k.$$
This is §9.2.1 of [saad2003iterative]: everything proved of `CG.iterate` holds for PCG.

The statement needs no hypothesis on $A$. The vectors of $E$ are transported to the $M$-inner
product space by `Krylov.IsPreconditioner.toEnergy`. -/
theorem iterate_eq_CG_iterate_withEnergy {M : E →ₗ[𝕜] E} (hM : IsPreconditioner M Minv) (k : ℕ) :
    hM.toEnergy (iterate A Minv b x₀ k).x
        = (CG.iterate (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀) k).x ∧
      hM.toEnergy (Minv (iterate A Minv b x₀ k).r)
        = (CG.iterate (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀) k).r ∧
      hM.toEnergy (iterate A Minv b x₀ k).p
        = (CG.iterate (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀) k).p ∧
      (iterate A Minv b x₀ k).r = b - A (iterate A Minv b x₀ k).x := by
  have hinit : hM.toEnergy (Minv (b - A x₀))
      = hM.toEnergy (Minv b) - hM.energyEnd (Minv ∘ₗ A) (hM.toEnergy x₀) := by
    rw [IsPreconditioner.energyEnd_apply, LinearMap.comp_apply, ← map_sub, ← map_sub]
  induction k with
  | zero => exact ⟨rfl, hinit, hinit, rfl⟩
  | succ k ih =>
    obtain ⟨hx, hr, hp, hres⟩ := ih
    have hnum : inner 𝕜 (hM.toEnergy (Minv (iterate A Minv b x₀ k).r))
          (hM.toEnergy (Minv (iterate A Minv b x₀ k).r))
        = inner 𝕜 (iterate A Minv b x₀ k).r (Minv (iterate A Minv b x₀ k).r) := by
      rw [WithEnergy.inner_equiv, energyInner, hM.apply_inv]
    have halpha : alpha A Minv (iterate A Minv b x₀ k)
        = CG.alpha (hM.energyEnd (Minv ∘ₗ A))
          (CG.iterate (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀) k) := by
      rw [alpha, CG.alpha, ← hr, ← hp, hnum, hM.inner_energyEnd_left A]
    have hr' : hM.toEnergy (Minv (iterate A Minv b x₀ (k + 1)).r)
        = (CG.iterate (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b))
            (hM.toEnergy x₀) (k + 1)).r := by
      rw [iterate_succ, step_r, CG.iterate_succ_r, map_sub, map_sub, map_smul, map_smul, hr,
        ← hp, halpha, IsPreconditioner.energyEnd_apply, LinearMap.comp_apply]
    have hbeta : beta A Minv (iterate A Minv b x₀ k)
        = CG.beta (hM.energyEnd (Minv ∘ₗ A))
          (CG.iterate (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀) k) := by
      rw [beta, CG.beta_iterate, ← iterate_succ, ← hr', ← hr, hnum]
      congr 1
      rw [WithEnergy.inner_equiv, energyInner, hM.apply_inv]
    refine ⟨?_, hr', ?_, ?_⟩
    · rw [iterate_succ, step_x, CG.iterate_succ_x, map_add, map_smul, hx, hp, halpha]
    · rw [iterate_succ, step_p, ← iterate_succ, CG.iterate_succ_p, map_add, map_smul, hr', hp,
        hbeta]
    · rw [iterate_succ, step_r, step_x, hres, map_add, map_smul, sub_sub]

/-- The PCG iterate after $k$ steps is the conjugate gradient iterate for $M^{-1} A$ and $M^{-1} b$
in the $M$-inner product. -/
theorem toEnergy_iterate_x {M : E →ₗ[𝕜] E} (hM : IsPreconditioner M Minv) (k : ℕ) :
    hM.toEnergy (iterate A Minv b x₀ k).x
      = (CG.iterate (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀) k).x :=
  (iterate_eq_CG_iterate_withEnergy A Minv b x₀ hM k).1

/-- The residual field of the PCG state after $k$ steps is the true residual: $r_k = b - A x_k$. -/
theorem residual_eq {M : E →ₗ[𝕜] E} (hM : IsPreconditioner M Minv) (k : ℕ) :
    (iterate A Minv b x₀ k).r = b - A (iterate A Minv b x₀ k).x :=
  (iterate_eq_CG_iterate_withEnergy A Minv b x₀ hM k).2.2.2

variable {A Minv b x₀}

/-- Let $(M, M^{-1})$ be a preconditioner, let $A$ be symmetric, and let $c > 0$ with $c
\operatorname{Re} \langle M x, x \rangle \le \operatorname{Re} \langle A x, x \rangle$ for all
$x \in E$. Then for every $k$ the PCG iterate $x_k$ is the Galerkin iterate of $A x = b$ over
the preconditioned Krylov space
$$x_0 + \mathcal{K}_k(M^{-1} A, M^{-1} r_0),$$
in the original inner product. In particular it minimizes the $A$-norm of the error over this
space (`IsGalerkin.energyNorm_le`). -/
theorem isGalerkinIterate {M : E →ₗ[𝕜] E} (hM : IsPreconditioner M Minv) (hA : A.IsSymmetric)
    {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x : E, c * RCLike.re (inner 𝕜 (M x) x) ≤ RCLike.re (inner 𝕜 (A x) x)) (k : ℕ) :
    IsGalerkin A b x₀ (subspace (Minv ∘ₗ A) (Minv (b - A x₀)) k)
      (iterate A Minv b x₀ k).x := by
  have hgal : IsGalerkin (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀)
      (subspace (hM.energyEnd (Minv ∘ₗ A))
        (hM.toEnergy (Minv b) - hM.energyEnd (Minv ∘ₗ A) (hM.toEnergy x₀)) k)
      (CG.iterate (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀) k).x :=
    CG.isGalerkinIterate (hM.toEnergy (Minv b)) (hM.toEnergy x₀)
      (hM.isSymmetricCoercive_energyEnd A hA hc hcoer) k
  rw [show hM.toEnergy (Minv b) - hM.energyEnd (Minv ∘ₗ A) (hM.toEnergy x₀)
        = hM.toEnergy (Minv (b - A x₀)) by
      rw [IsPreconditioner.energyEnd_apply, LinearMap.comp_apply, ← map_sub, ← map_sub],
    hM.subspace_energyEnd, ← toEnergy_iterate_x A Minv b x₀ hM k] at hgal
  exact (hM.isGalerkin_energyEnd_iff A b x₀ _ _).1 hgal

/-- **The PCG residuals are $M^{-1}$-orthogonal** ([saad2003iterative], Algorithm 9.1;
[golub2013matrix], (11.5.2)). Let $(M, M^{-1})$ be a preconditioner, let $A$ be symmetric, and
let $c > 0$ with $c \operatorname{Re} \langle M x, x \rangle \le \operatorname{Re} \langle A x,
x \rangle$ for all $x$. Then the PCG residuals satisfy
$$\langle M^{-1} r_i, r_j \rangle = 0 \qquad (i \neq j).$$

In the $M$-inner product the preconditioned residuals $z = M^{-1} r$ are the CG residuals of
$M^{-1} A$, which are orthogonal, and $\langle z_i, z_j \rangle_M = \langle M^{-1} r_i, r_j
\rangle$. The hypotheses on $A$ are those of `Krylov.PCG.isGalerkinIterate`. -/
theorem inner_inv_residual_eq_zero {M : E →ₗ[𝕜] E} (hM : IsPreconditioner M Minv)
    (hA : A.IsSymmetric) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x : E, c * RCLike.re (inner 𝕜 (M x) x) ≤ RCLike.re (inner 𝕜 (A x) x))
    {i j : ℕ} (hij : i ≠ j) :
    inner 𝕜 (Minv (iterate A Minv b x₀ i).r) (iterate A Minv b x₀ j).r = 0 := by
  have h := CG.inner_residual_eq_zero (hM.toEnergy (Minv b)) (hM.toEnergy x₀)
    (hM.isSymmetricCoercive_energyEnd A hA hc hcoer) hij
  rwa [← (iterate_eq_CG_iterate_withEnergy A Minv b x₀ hM i).2.1,
    ← (iterate_eq_CG_iterate_withEnergy A Minv b x₀ hM j).2.1, hM.inner_toEnergy_inv] at h

/-- **The PCG directions are $A$-conjugate** ([saad2003iterative], Algorithm 9.1; [golub2013matrix],
(11.5.2)). Let $(M, M^{-1})$ be a preconditioner, let $A$ be symmetric, and let $c > 0$ with $c
\operatorname{Re} \langle M x, x \rangle \le \operatorname{Re} \langle A x, x \rangle$ for all
$x$. Then the PCG directions satisfy
$$\langle A p_i, p_j \rangle = 0 \qquad (i \neq j).$$

The reason is that $\langle M^{-1} A p_i, p_j \rangle_M = \langle A p_i, p_j \rangle$, and the
PCG directions are the CG directions of $M^{-1} A$ in the $M$-inner product. -/
theorem inner_apply_direction_eq_zero {M : E →ₗ[𝕜] E} (hM : IsPreconditioner M Minv)
    (hA : A.IsSymmetric) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x : E, c * RCLike.re (inner 𝕜 (M x) x) ≤ RCLike.re (inner 𝕜 (A x) x))
    {i j : ℕ} (hij : i ≠ j) :
    inner 𝕜 (A (iterate A Minv b x₀ i).p) (iterate A Minv b x₀ j).p = 0 := by
  have h := CG.inner_apply_direction_eq_zero (hM.toEnergy (Minv b)) (hM.toEnergy x₀)
    (hM.isSymmetricCoercive_energyEnd A hA hc hcoer) hij
  rwa [← (iterate_eq_CG_iterate_withEnergy A Minv b x₀ hM i).2.2.1,
    ← (iterate_eq_CG_iterate_withEnergy A Minv b x₀ hM j).2.2.1,
    hM.inner_energyEnd_left A] at h

/-- The Chebyshev bound for PCG ([saad2003iterative], §9.2). Let $(M, M^{-1})$ be a preconditioner,
let $A$ be symmetric, let $0 < \lambda_{\min} \le \lambda_{\max}$ satisfy
$$\lambda_{\min} \operatorname{Re} \langle M x, x \rangle \le \operatorname{Re} \langle A x, x
  \rangle \le \lambda_{\max} \operatorname{Re} \langle M x, x \rangle \qquad (x \in E),$$
and let $A x^* = b$. With $\kappa = \lambda_{\max} / \lambda_{\min}$, the PCG iterate $x_k$
satisfies for every $k$
$$\|x^* - x_k\|_A \le 2 \left( \frac{\sqrt\kappa - 1}{\sqrt\kappa + 1} \right)^k \|x^* -
  x_0\|_A.$$

The bound is the bound without preconditioning, transported: the energy norm of $M^{-1} A$ in
the $M$-inner product is the $A$-norm, so preconditioning changes only which condition number
appears. -/
theorem energyNorm_error_le {M : E →ₗ[𝕜] E} (hM : IsPreconditioner M Minv) (hA : A.IsSymmetric)
    {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin ≤ lmax)
    (hmin : ∀ x : E, lmin * RCLike.re (inner 𝕜 (M x) x) ≤ RCLike.re (inner 𝕜 (A x) x))
    (hmax : ∀ x : E, RCLike.re (inner 𝕜 (A x) x) ≤ lmax * RCLike.re (inner 𝕜 (M x) x))
    {xstar : E} (hstar : A xstar = b) (k : ℕ) :
    energyNorm A (xstar - (iterate A Minv b x₀ k).x) ≤
      2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ k *
        energyNorm A (xstar - x₀) := by
  have hB := hM.isSymmetricBoundedBy_energyEnd A hA hmin hmax
  have hgal := CG.isGalerkinIterate (hM.toEnergy (Minv b)) (hM.toEnergy x₀)
    (hB.isSymmetricCoercive hl) k
  have hstar' : hM.energyEnd (Minv ∘ₗ A) (hM.toEnergy xstar) = hM.toEnergy (Minv b) := by
    rw [IsPreconditioner.energyEnd_apply, LinearMap.comp_apply, hstar]
  have h := IsGalerkinIterate.energyNorm_error_le hl hll hB hgal hstar'
  rw [← toEnergy_iterate_x A Minv b x₀ hM k, ← map_sub, ← map_sub,
    hM.energyNorm_energyEnd, hM.energyNorm_energyEnd] at h
  exact h

end PCG

/-! ### Flexible GMRES -/

namespace FGMRES

/-- **Proposition 9.2** of [saad2003iterative]: the flexible GMRES iterate minimizes the residual
norm over $x_0 + \operatorname{span}\{z_0, \dots, z_{m-1}\}$. Let $A$, $z$, $v$ and $h$ satisfy
the two-family Hessenberg relation $A z_j = \sum_{i \le j+1} h_{ij} v_i$, let
$b - A x_0 = \beta v_0$, and let $v_0, \dots, v_m$ be orthonormal. If $y \in \mathbb{K}^m$
minimizes the quasi-residual $\|\beta e_1 - \bar H_m y\|_2$, then $x_0 + \sum_{j<m} y_j z_j$
minimizes $\|b - A x\|$ over $x_0 + \operatorname{span}\{z_0, \dots, z_{m-1}\}$.

Flexible GMRES expands the iterate in arbitrary preconditioned directions $z_j = M_j^{-1} v_j$,
and it expands the residual in the orthonormal Arnoldi basis $v_i$, so its search space is not a
Krylov space. The minimization needs only the two-family relation $A Z_m = V_{m+1} \bar H_m$ of
(9.22) in [saad2003iterative] and the orthonormality of $V_{m+1}$. This is
`Krylov.IsQuasiMinResidualIterate.isMinOn_norm_residual` with the minimizer given explicitly. -/
theorem isMinResidual {A : E →ₗ[𝕜] E} {z v : ℕ → E} {h : ℕ → ℕ → 𝕜} {b x₀ : E} {β : 𝕜}
    (hv : HessenbergRelation₂ A z v h) (hr : b - A x₀ = β • v 0) {m : ℕ}
    (hon : Orthonormal 𝕜 fun i : Fin (m + 1) => v (i : ℕ)) {y : Fin m → 𝕜}
    (hy : IsMinOn (quasiResidual h β m) Set.univ y) :
    IsMinResidual A b x₀ (Submodule.span 𝕜 (Set.range fun j : Fin m => z (j : ℕ)))
      (x₀ + ∑ j, y j • z j) :=
  IsQuasiMinResidualIterate.isMinOn_norm_residual hv hr hon ⟨y, hy, rfl⟩

/-- For upper Hessenberg $h$ and $m \ge 1$, the last entry of $\bar H_m y$ is $h_{m, m-1} y_{m-1}$.
-/
private theorem mulVec_hessenbergOf_last {h : ℕ → ℕ → 𝕜} (hH : Matrix.IsUpperHessenberg (n := ℕ) h)
    {m : ℕ} (hm : 0 < m) (y : Fin m → 𝕜) :
    (hessenbergOf h m).mulVec y ⟨m, Nat.lt_succ_self m⟩
      = h m (m - 1) * y ⟨m - 1, by omega⟩ := by
  simp only [Matrix.mulVec, dotProduct, hessenbergOf, Matrix.of_apply]
  refine Finset.sum_eq_single (⟨m - 1, by omega⟩ : Fin m) (fun k _ hk => ?_)
    (fun hc => absurd (Finset.mem_univ _) hc)
  have hklt := k.isLt
  have hk' : (k : ℕ) ≠ m - 1 := fun hcc => hk (Fin.ext hcc)
  rw [hH.eq_zero_of_add_one_lt m (k : ℕ) (by omega), zero_mul]

/-- Back substitution in a Hessenberg system: if $h$ is upper Hessenberg with nonzero subdiagonal
entries $h_{i+1,i}$ for $i + 1 < m$, $\beta \neq 0$ and $H_m y = \beta e_1$, then the last
coordinate $y_{m-1}$ is nonzero. -/
private theorem last_ne_zero_of_mulVec_eq {h : ℕ → ℕ → 𝕜} {β : 𝕜} (hβ : β ≠ 0) {m : ℕ}
    (hm : 0 < m) (hH : Matrix.IsUpperHessenberg (n := ℕ) h)
    (hsub : ∀ i, i + 1 < m → h (i + 1) i ≠ 0) {y : Fin m → 𝕜}
    (hyeq : (hessenbergSqOf h m).mulVec y = firstVec β m) :
    y ⟨m - 1, by omega⟩ ≠ 0 := by
  intro hlast
  have hrow : ∀ (r : ℕ) (hr : r < m),
      ∑ k : Fin m, h r (k : ℕ) * y k = firstVec β m ⟨r, hr⟩ := by
    intro r hr
    have hcong := congrFun hyeq ⟨r, hr⟩
    simpa only [Matrix.mulVec, dotProduct, hessenbergSqOf, Matrix.of_apply] using hcong
  have hall : ∀ t : ℕ, ∀ i : Fin m, m - 1 - t ≤ (i : ℕ) → y i = 0 := by
    intro t
    induction t with
    | zero =>
      intro i hi
      have hval : (i : ℕ) = m - 1 := by omega
      have : i = (⟨m - 1, by omega⟩ : Fin m) := Fin.ext hval
      rw [this]
      exact hlast
    | succ t ih =>
      intro i hi
      by_cases hcase : m - 1 - t ≤ (i : ℕ)
      · exact ih i hcase
      have hij : (i : ℕ) + 1 < m := by omega
      have hz := hrow ((i : ℕ) + 1) hij
      have hfv : firstVec β m ⟨(i : ℕ) + 1, hij⟩ = 0 := by simp [firstVec]
      rw [hfv] at hz
      have hsum : ∑ k : Fin m, h ((i : ℕ) + 1) (k : ℕ) * y k
          = h ((i : ℕ) + 1) (i : ℕ) * y i := by
        refine Finset.sum_eq_single i (fun k _ hk => ?_)
          (fun hc => absurd (Finset.mem_univ _) hc)
        have hkne : (k : ℕ) ≠ (i : ℕ) := fun hcc => hk (Fin.ext hcc)
        rcases lt_or_gt_of_ne hkne with hlt | hgt
        · rw [hH.eq_zero_of_add_one_lt ((i : ℕ) + 1) (k : ℕ) (by omega), zero_mul]
        · rw [ih k (by omega), mul_zero]
      rw [hsum] at hz
      exact (mul_eq_zero.1 hz).resolve_left (hsub (i : ℕ) hij)
  have hy0 : ∀ i : Fin m, y i = 0 := fun i => hall (m - 1) i (by omega)
  have h0 := hrow 0 hm
  rw [show firstVec β m ⟨0, hm⟩ = β from by simp [firstVec]] at h0
  rw [Finset.sum_congr rfl fun k _ => by rw [hy0 k, mul_zero]] at h0
  exact hβ (by simpa using h0.symm)

/-- A row of $\bar H_j$ above the last one is the corresponding row of the square matrix $H_j$. -/
private theorem mulVec_hessenbergOf_of_lt {h : ℕ → ℕ → 𝕜} {j : ℕ} (w : Fin j → 𝕜) (r : ℕ)
    (hr : r < j) :
    (hessenbergOf h j).mulVec w ⟨r, by omega⟩ = (hessenbergSqOf h j).mulVec w ⟨r, hr⟩ := by
  simp only [Matrix.mulVec, dotProduct, hessenbergOf, hessenbergSqOf, Matrix.of_apply]

/-- The vector $\beta e_1$ of length $j + 1$ agrees with $\beta e_1$ of length $j$ in the first $j$
entries. -/
private theorem firstVec_succ_of_lt {β : 𝕜} {j : ℕ} (r : ℕ) (hr : r < j) :
    firstVec β (j + 1) ⟨r, by omega⟩ = firstVec β j ⟨r, hr⟩ := by
  simp [firstVec]

/-- The quasi-residual of $w$ is $0$ if and only if $\beta e_1 - \bar H_j w = 0$. -/
private theorem quasiResidual_eq_zero_iff (h : ℕ → ℕ → 𝕜) (β : 𝕜) (j : ℕ) :
    ∀ w : Fin j → 𝕜, quasiResidual h β j w = 0 ↔
      ∀ i : Fin (j + 1), (firstVec β (j + 1) - (hessenbergOf h j).mulVec w) i = 0 := by
  intro w
  rw [quasiResidual_def, norm_eq_zero]
  constructor
  · intro hw i
    have := congrArg (WithLp.ofLp (p := 2)) hw
    simpa using congrFun this i
  · intro hw
    have : (firstVec β (j + 1) - (hessenbergOf h j).mulVec w) = 0 := funext hw
    rw [this]
    simp

/-- **A vanishing subdiagonal entry makes the flexible GMRES iterate exact**, with no orthonormality
hypothesis on the residual basis. Let $A$, $z$, $v$ and $h$ satisfy the two-family Hessenberg
relation $A z_j = \sum_{i \le j+1} h_{ij} v_i$, let $b - A x_0 = \beta v_0$, and let $m \ge 1$.
If the square Hessenberg matrix $H_m$ is nonsingular and $h_{m, m-1} = 0$, then every minimizer
$y$ of the quasi-residual $\|\beta e_1 - \bar H_m y\|_2$ gives
$$A \Big( x_0 + \sum_{i<m} y_i z_i \Big) = b.$$

This is the half of `Krylov.FGMRES.apply_eq_iff_coeff_eq_zero` that survives a breakdown at step
$m - 1$, where the residual basis stops one vector short and $v_0, \dots, v_m$ cannot be
orthonormal. It is what §9.4.1 of [saad2003iterative] needs: an exact inner solve $A z_j = v_j$
empties the orthogonalization, and the outer iteration is finished. -/
theorem apply_eq_of_coeff_eq_zero {A : E →ₗ[𝕜] E} {z v : ℕ → E} {h : ℕ → ℕ → 𝕜} {b x₀ : E}
    {β : 𝕜} (hv : HessenbergRelation₂ A z v h) (hr : b - A x₀ = β • v 0) {m : ℕ} (hm : 0 < m)
    (hH : IsUnit (hessenbergSqOf h m).det) (hzero : h m (m - 1) = 0) {y : Fin m → 𝕜}
    (hy : IsMinOn (quasiResidual h β m) Set.univ y) :
    A (x₀ + ∑ i, y i • z i) = b := by
  set y' : Fin m → 𝕜 := (hessenbergSqOf h m)⁻¹.mulVec (firstVec β m) with hy'
  have hy'eq : (hessenbergSqOf h m).mulVec y' = firstVec β m := by
    rw [hy']
    exact Matrix.mulVec_nonsing_inv_mulVec ((Matrix.isUnit_iff_isUnit_det _).2 hH) _
  have hq' : quasiResidual h β m y' = 0 := by
    refine (quasiResidual_eq_zero_iff h β m y').2 fun i => ?_
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 i.isLt) with heq | hlt
    · have hi : i = (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := Fin.ext heq
      rw [hi, Pi.sub_apply, mulVec_hessenbergOf_last hv.isUpperHessenberg hm y', hzero, zero_mul,
        show firstVec β (m + 1) ⟨m, Nat.lt_succ_self m⟩ = 0 from by simp [firstVec]; omega,
        sub_zero]
    · rw [Pi.sub_apply, mulVec_hessenbergOf_of_lt y' (i : ℕ) hlt, hy'eq,
        firstVec_succ_of_lt (i : ℕ) hlt, sub_self]
  have hq : quasiResidual h β m y = 0 :=
    le_antisymm (hq' ▸ isMinOn_iff.1 hy y' (Set.mem_univ y')) (quasiResidual_nonneg h β m y)
  have hc0 := (quasiResidual_eq_zero_iff h β m y).1 hq
  have h0 : b - A (x₀ + ∑ i, y i • z i) = 0 := by
    rw [hv.residual_eq hr m y]
    exact Finset.sum_eq_zero fun i _ => by rw [hc0 i, zero_smul]
  exact (sub_eq_zero.1 h0).symm

/-- **Proposition 9.3** of [saad2003iterative]. Let $A$, $z$, $v$ and $h$ satisfy the two-family
Hessenberg relation $A z_j = \sum_{i \le j+1} h_{ij} v_i$, let $b - A x_0 = \beta v_0$ with
$\beta \neq 0$, and let $j \ge 1$. Assume that the earlier steps have not broken down, that is,
$h_{i+1, i} \neq 0$ for $i + 1 < j$, that the square Hessenberg matrix $H_j$ is nonsingular, and
that $v_0, \dots, v_j$ are orthonormal. If $y \in \mathbb{K}^j$ minimizes the quasi-residual
$\|\beta e_1 - \bar H_j y\|_2$, then
$$A \Big( x_0 + \sum_{i<j} y_i z_i \Big) = b \iff h_{j, j-1} = 0.$$
So the flexible GMRES iterate at step $j$ is exact if and only if the last subdiagonal entry of
$\bar H_j$ vanishes.

The nonsingularity of $H_j$ is a real extra hypothesis in the flexible case. In GMRES,
$A Z_j = A V_j$, and the nonsingularity of $A$ transfers; here the $z_j$ are arbitrary. The
forward direction is back substitution in $H_j y = \beta e_1$. The reverse direction builds the
exact solution from $H_j^{-1} (\beta e_1)$ and uses the minimality. Indices start at $0$, so the
entry $h_{j, j-1}$ is the entry $h_{j+1, j}$ in the indexing from $1$ of the source. -/
theorem apply_eq_iff_coeff_eq_zero {A : E →ₗ[𝕜] E} {z v : ℕ → E} {h : ℕ → ℕ → 𝕜} {b x₀ : E}
    {β : 𝕜} (hv : HessenbergRelation₂ A z v h) (hr : b - A x₀ = β • v 0) (hβ : β ≠ 0)
    {j : ℕ} (hj : 0 < j) (hsub : ∀ i, i + 1 < j → h (i + 1) i ≠ 0)
    (hH : IsUnit (hessenbergSqOf h j).det)
    (hon : Orthonormal 𝕜 fun i : Fin (j + 1) => v (i : ℕ))
    {y : Fin j → 𝕜} (hy : IsMinOn (quasiResidual h β j) Set.univ y) :
    A (x₀ + ∑ i, y i • z i) = b ↔ h j (j - 1) = 0 := by
  classical
  -- the coefficients of the residual in the basis `v`
  have hrowj : ∀ (w : Fin j → 𝕜) (r : ℕ) (hr : r < j),
      (hessenbergOf h j).mulVec w ⟨r, by omega⟩ = (hessenbergSqOf h j).mulVec w ⟨r, hr⟩ :=
    fun w r hr => mulVec_hessenbergOf_of_lt w r hr
  have hfirst : ∀ (r : ℕ) (hr : r < j),
      firstVec β (j + 1) ⟨r, by omega⟩ = firstVec β j ⟨r, hr⟩ :=
    fun r hr => firstVec_succ_of_lt r hr
  -- `quasiResidual` vanishes exactly when the coefficient vector does
  have hqz := quasiResidual_eq_zero_iff h β j
  -- exactness is vanishing of the coefficient vector
  have hexact : A (x₀ + ∑ i, y i • z i) = b ↔ quasiResidual h β j y = 0 := by
    rw [hqz]
    constructor
    · intro hax
      have h0 : ∑ i : Fin (j + 1),
          (firstVec β (j + 1) - (hessenbergOf h j).mulVec y) i • v (i : ℕ) = 0 := by
        rw [← hv.residual_eq hr j y, hax, sub_self]
      exact fun i => Fintype.linearIndependent_iff.1 hon.linearIndependent _ h0 i
    · intro hc0
      have h0 : b - A (x₀ + ∑ i, y i • z i) = 0 := by
        rw [hv.residual_eq hr j y]
        exact Finset.sum_eq_zero fun i _ => by rw [hc0 i, zero_smul]
      exact (sub_eq_zero.1 h0).symm
  rw [hexact]
  constructor
  · intro hq
    have hc0 := (hqz y).1 hq
    have hlast := hc0 ⟨j, Nat.lt_succ_self j⟩
    rw [Pi.sub_apply, sub_eq_zero, mulVec_hessenbergOf_last hv.isUpperHessenberg hj y,
      show firstVec β (j + 1) ⟨j, Nat.lt_succ_self j⟩ = 0 from by simp [firstVec]; omega] at hlast
    have hyeq : (hessenbergSqOf h j).mulVec y = firstVec β j := by
      funext r
      have := hc0 ⟨(r : ℕ), by omega⟩
      rw [Pi.sub_apply, sub_eq_zero, hfirst (r : ℕ) r.isLt, hrowj y (r : ℕ) r.isLt] at this
      exact this.symm
    exact (mul_eq_zero.1 hlast.symm).resolve_right
      (last_ne_zero_of_mulVec_eq hβ hj hv.isUpperHessenberg hsub hyeq)
  · intro hzero
    set y' : Fin j → 𝕜 := (hessenbergSqOf h j)⁻¹.mulVec (firstVec β j) with hy'
    have hy'eq : (hessenbergSqOf h j).mulVec y' = firstVec β j := by
      rw [hy']
      exact Matrix.mulVec_nonsing_inv_mulVec ((Matrix.isUnit_iff_isUnit_det _).2 hH) _
    have hq' : quasiResidual h β j y' = 0 := by
      refine (hqz y').2 fun i => ?_
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 i.isLt) with heq | hlt
      · have hi : i = (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1)) := Fin.ext heq
        rw [hi, Pi.sub_apply, mulVec_hessenbergOf_last hv.isUpperHessenberg hj y', hzero, zero_mul,
          show firstVec β (j + 1) ⟨j, Nat.lt_succ_self j⟩ = 0 from by simp [firstVec]; omega,
          sub_zero]
      · rw [Pi.sub_apply, hrowj y' (i : ℕ) hlt, hy'eq, hfirst (i : ℕ) hlt, sub_self]
    have hle := isMinOn_iff.1 hy y' (Set.mem_univ y')
    exact le_antisymm (hq' ▸ hle) (quasiResidual_nonneg h β j y)

end FGMRES

end Krylov

open scoped ComplexOrder in
/-- Let $M$ be a positive definite $n \times n$ matrix over $\mathbb{K}$. Then $M$ and its inverse
$M^{-1}$, acting on the Euclidean space $\mathbb{K}^n$, form a preconditioner:
`Matrix.toEuclideanLin M` is symmetric coercive, and `Matrix.toEuclideanLin M⁻¹` inverts it. -/
theorem Matrix.PosDef.isPreconditioner_toEuclideanLin {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n 𝕜} (hM : M.PosDef) :
    Krylov.IsPreconditioner (Matrix.toEuclideanLin M) (Matrix.toEuclideanLin M⁻¹) :=
  ⟨hM.isSymmetricCoercive_toEuclideanLin, Matrix.toEuclideanLin_mul_nonsing_inv_apply hM.isUnit⟩
